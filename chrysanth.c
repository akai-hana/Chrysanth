/* ~>[^=-| chrysanth.c >-***<> */ 
/* X11 shader render wallpaper */

/* build: make   (links -lX11 -lXrandr -lXext -lXss -lGL -lm)
 * usage: chrysanth -f shader.frag [options]; (-h, --help)
 *
 * The shader is rendered directly into X11's root background's GLX pixmap.
 * Rendering pauses while an opaque window covering the whole root is fullscreen,
 * while the X screensaver is on, and while DPMS has the monitor blanked.
 */

#define _GNU_SOURCE
#define GL_GLEXT_PROTOTYPES 1
#include <ctype.h>
#include <errno.h>
#include <fnmatch.h>
#include <math.h>
#include <signal.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <time.h>

#include <dirent.h>
#include <getopt.h>
#include <poll.h>
#include <sys/inotify.h>
#include <sys/signalfd.h>
#include <sys/stat.h>
#include <unistd.h>

#include <X11/Xatom.h>
#include <X11/Xlib.h>
#include <X11/Xmd.h>
#include <X11/Xutil.h>
#include <X11/extensions/Xrandr.h>
#include <X11/extensions/dpms.h>
#include <X11/extensions/scrnsaver.h>

#include <GL/gl.h>
#include <GL/glx.h>

/* messages go to stderr with a "chrysanth: " prefix: warn() is for what went wrong, info() for what is merely going on (-q silences it); both have the printf format check.
   die() also exits with status 1 (exit() is noreturn). */
static bool quiet; /* -q */
static void __attribute__((format(printf, 1, 0))) vmsg(const char *fmt, va_list ap) {
    fputs("chrysanth: ", stderr);
    vfprintf(stderr, fmt, ap);
    fputc('\n', stderr);
}
static void __attribute__((format(printf, 1, 2))) warn(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vmsg(fmt, ap);
    va_end(ap);
}
static void __attribute__((format(printf, 1, 2))) info(const char *fmt, ...) {
    va_list ap;
    if (quiet) return;
    va_start(ap, fmt);
    vmsg(fmt, ap);
    va_end(ap);
}
#define die(...) (warn(__VA_ARGS__), exit(1))

#define MIN(a, b) ((a) < (b) ? (a) : (b))
#define ARRAY_LEN(a) ((int)(sizeof(a) / sizeof *(a)))
#define MAX_PROP_ITEMS 32  /* items read from a 32-bit window property (see getProp) */
#define COMM_LEN 15        /* longest process name in /proc/<pid>/stat (the kernel's comm) */
#define EXE_PATH_MAX 4096  /* buffer for this binary's path */
#define MAX_XERRORS_SHOWN 8        /* X protocol errors printed (all are counted) */
#define DPMS_POLL_SEC 1.0          /* how often the DPMS state is looked at: Xlib has no event for it */
#define COMP_EXIT_TRIES 50         /* after SIGTERM, the compositor's exit is awaited this many times... */
#define COMP_EXIT_POLL_MS 20       /* ...this many milliseconds apart */
#define STALL_MIN_SEC 0.25         /* after a stall a frame's dt is capped at max(this, STALL_PERIODS frame periods) */
#define STALL_PERIODS 4.0
#define OPACITY_OPAQUE 0xffffffffUL /* _NET_WM_WINDOW_OPACITY of a fully opaque window */
#define FPS_MIN 0.01               /* the accepted frame rates (-F): the period 1/fps must stay a sane number of seconds... */
#define FPS_MAX 1000.0
#define SPEED_MAX 1e6              /* ...and |speed| (-s) small enough that shader time and the float uniform made from it never overflow */

typedef struct { const char **v; int n; } StrList;
static void listAdd(StrList *l, const char *item) {
    if (!(l->v = realloc(l->v, (l->n + 1) * sizeof *l->v))) die("out of memory");
    l->v[l->n++] = item;
}

/* state */
static bool quitFlag, reloadFlag; /* set in the main loop (signalfd, file watch): no signal handlers */
static int sfd = -1;             /* signalfd for SIGINT/SIGTERM/SIGHUP/SIGUSR1, which are blocked */
static sigset_t origMask;        /* the signal mask we started with: children get it back */
static int xerrors;              /* X protocol errors seen so far (counted, never fatal) */
static bool xerrQuiet;           /* they are expected right now (context probing): counted, not printed */

static const char *shaderPath, *compositor, *wrapCmd; /* shaderPath: -f, a shader file or a directory of them; wrapCmd: -W, chrysanth re-executes itself under it */
static const char *fragFile; /* the shader file actually loaded: the candidate that compiled (see resolveShader), reloaded and watched */
static double speed = 1.0, scale = 1.0, fps = 30.0; /* doubles, so that no setting can overflow a float on its way in (see checkSettings for the ranges) */
static double wrapSec; /* -T: shader time goes back to 0 after this many seconds; 0: it never does */
static StrList pauseExempt; /* -k fullscreen_pause_exceptions: WM_CLASS names whose fullscreen windows are see-through */
static StrList killComp; /* -K fullscreen_kill_compositor: WM_CLASS names; while one is fullscreen, the compositor is stopped */
static const char *compProc; /* -N: the compositor's process name, when it cannot be guessed from -C */
static char compName[64] = "picom"; /* the process name -K stops and the already-running check looks for: -N, else guessed from -C (see initCompName); empty: unknown, both are off */
static bool compAbsent, compKilled; /* -K window up but no compositor running (nothing to restart) / we stopped it and owe it a restart */

static Display *d;
static Window root, watched; /* watched: the active window whose state changes wake us up */
static XWindowAttributes wa;
/* the atoms we use: A[] is filled from atomNames[] (_XROOTPMAP_ID, ESETROOT_PMAP_ID: what picom reads) */
enum { A_ACTIVE, A_STATE, A_FULLSCREEN, A_OPACITY, A_ROOTPMAP, A_ESETPMAP, A_NETNAME, A_UTF8, A_COUNT };
static char *atomNames[A_COUNT] = {
    [A_ACTIVE] = "_NET_ACTIVE_WINDOW", [A_STATE] = "_NET_WM_STATE", [A_FULLSCREEN] = "_NET_WM_STATE_FULLSCREEN", [A_OPACITY] = "_NET_WM_WINDOW_OPACITY",
    [A_ROOTPMAP] = "_XROOTPMAP_ID", [A_ESETPMAP] = "ESETROOT_PMAP_ID", [A_NETNAME] = "_NET_WM_NAME", [A_UTF8] = "UTF8_STRING",
};
static Atom A[A_COUNT];
static GLXContext ctx;
static GLXFBConfig fbcfg; /* the config of `ctx` and of the GLX pixmap */
static bool fbDbl;        /* it is double-buffered: frames are drawn to the front buffer */
static int rrEvBase;         /* the first event number of the XRandR extension */
static bool hasRandr, dirtyFs = true, dirtyScreen, fsPaused;
static bool hasDpms, blanked; /* DPMS is usable / the monitor is blanked (standby, suspend, off) */
static int ssEvBase;          /* the first event number of the MIT-SCREEN-SAVER extension */
static bool hasSaver, saverOn; /* it is usable / the X screensaver is on: the idle timeout (xset s) has struck, which is also what xss-lock hears and locks the screen on */
static double nextDpmsT, nextT; /* monoSec() time of the next DPMS check / at which the next frame is due */
static unsigned prog;    /* the current shader program */
static StrList cands;    /* shader files to try, in order */
static int ino = -1;          /* inotify fd watching the shader's directory (-1: no reload on save) */
static const char *watchName; /* the shader's file name, without its directory */

/* everything whose size depends on the screen resolution */
static struct {
    int w, h, rw, rh; /* root size, render size (root * scale) */
    bool announced;   /* the root properties already point at pm (see publish) */
    Pixmap pm;
    GLXPixmap gp;     /* the GLX pixmap wrapping pm */
    unsigned fbo, rb; /* offscreen target when rendering below full size; 0: the shader renders straight into the pixmap */
} S;

static double monoSec(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec / 1e9; }

/* run a shell command in the background, never waited for (SIGCHLD is ignored) */
static void spawn(const char *cmd) {
    if (fork()) return;
    sigprocmask(SIG_SETMASK, &origMask, NULL); /* a blocked mask and an ignored SIGCHLD both survive exec */
    signal(SIGCHLD, SIG_DFL);
    setsid(); /* a session and process group of its own: a Ctrl-C or terminal hangup meant for us must not take the compositor down too */
    execl("/bin/sh", "sh", "-c", cmd, (char *)NULL);
    _exit(127);
}

/* X errors are never fatal (windows vanish mid-query, GLX probing may fail): they are counted for the surface and context setup to compare, and the first MAX_XERRORS_SHOWN are printed.
   The exception is BadWindow, the everyday result of asking about a window that has just closed: it is neither counted nor printed. */
static int onXError(Display *dpy, XErrorEvent *e) {
    static int shown;
    char text[128];
    if (e->error_code == BadWindow) return 0; /* a window we were asking about has just closed (the active window, mostly): routine, and not worth one of the MAX_XERRORS_SHOWN, which would leave real errors unprinted */
    xerrors++;
    if (xerrQuiet || shown >= MAX_XERRORS_SHOWN) return 0;
    shown++;
    XGetErrorText(dpy, e->error_code, text, sizeof text);
    warn("X error: %s (request %d.%d, resource 0x%lx)", text, e->request_code, e->minor_code, e->resourceid);
    return 0;
}

static void drainSignals(void) {
    struct signalfd_siginfo si;
    while (read(sfd, &si, sizeof si) == (ssize_t)sizeof si) {
        if (si.ssi_signo == SIGUSR1) reloadFlag = true;
        else quitFlag = true; /* SIGINT, SIGTERM, SIGHUP */
    }
}

/* The signals are blocked and read from a signalfd, so one arriving between a flag check and the poll cannot be missed: it just makes the fd readable. */
static void setupSignals(void) {
    static const int sigs[] = {SIGINT, SIGTERM, SIGHUP, SIGUSR1};
    sigset_t blocked; sigemptyset(&blocked);
    for (int i = 0; i < ARRAY_LEN(sigs); i++) sigaddset(&blocked, sigs[i]);
    sigprocmask(SIG_BLOCK, &blocked, &origMask);
    if ((sfd = signalfd(-1, &blocked, SFD_NONBLOCK | SFD_CLOEXEC)) < 0) die("cannot create signalfd");
    signal(SIGCHLD, SIG_IGN); /* spawned children are never waited for; don't leave zombies */
}

static void openDisplay(void) {
    if (!(d = XOpenDisplay(NULL))) die("cannot open display");
    XSetErrorHandler(onXError); /* windows vanish mid-query, GLX probing may fail: none of it is fatal */
    root = DefaultRootWindow(d);
    XInternAtoms(d, atomNames, A_COUNT, False, A);
}

/* copies the items of a 32-bit window property (at most MAX_PROP_ITEMS) into out[]; returns how many, 0 if absent */
static int getProp(Window w, Atom a, Atom type, unsigned long out[MAX_PROP_ITEMS]) {
    Atom t; int fmt; unsigned long n = 0, left; unsigned char *p = NULL;
    if (XGetWindowProperty(d, w, a, 0, MAX_PROP_ITEMS, False, type, &t, &fmt, &n, &left, &p) != Success) return 0;
    if (fmt == 32 && n) memcpy(out, p, n * sizeof *out); else n = 0;
    if (p) XFree(p);
    return (int)n;
}

/* shaders */
static char *readFile(const char *path) {
    FILE *f = fopen(path, "rb"); struct stat st; char *s = NULL;
    if (!f) { warn("%s: %s", path, strerror(errno)); return NULL; }
    if (fstat(fileno(f), &st) || !S_ISREG(st.st_mode) || !(s = calloc(st.st_size + 1, 1)) || fread(s, 1, st.st_size, f) != (size_t)st.st_size) {
        warn("read failed: %s", path);
        free(s); s = NULL;
    }
    fclose(f);
    return s;
}

/* One oversized triangle from gl_VertexID, no vertex buffers: (-1,-1), (3,-1), (-1,3). It covers the viewport and is clipped, so no pixel is shaded twice along a quad's seam. */
static const char *fullscreenVert =
    "#version 330 core\n"
    "void main() {\n"
    "    gl_Position = vec4(float((gl_VertexID & 1) << 2) - 1.0, float((gl_VertexID & 2) << 1) - 1.0, 0.0, 1.0);\n"
    "}\n";

/* The uniforms we know about. `name`: the Shadertoy name (declared for Shadertoy shaders that lack it); `alias`: the name plain shaders use instead (looked up first). */
enum { U_TIME, U_RES, U_DELTA, U_FRAME, U_DATE, U_MOUSE, U_COUNT };
static const struct { const char *name, *alias, *type; } uniDefs[U_COUNT] = {
    [U_TIME]  = {"iTime",       "time",       "float"},
    [U_RES]   = {"iResolution", "resolution", "vec3"},
    [U_DELTA] = {"iTimeDelta",  NULL,         "float"},
    [U_FRAME] = {"iFrame",      NULL,         "int"},
    [U_DATE]  = {"iDate",       NULL,         "vec4"},
    [U_MOUSE] = {"iMouse",      NULL,         "vec4"},
};
static struct { GLint loc; GLenum type; } U[U_COUNT]; /* location (-1: unused) and GLSL type in the current program */

static bool isIdent(char c) { return isalnum((unsigned char)c) || c == '_'; }

/* the first occurrence of `word` at or after `p` that is a whole identifier (not part of a longer one), or NULL; `src` is the start of the text */
static const char *findWord(const char *src, const char *p, const char *word) {
    for (p = strstr(p, word); p; p = strstr(p + 1, word))
        if (!(p > src && isIdent(p[-1])) && !isIdent(p[strlen(word)])) return p;
    return NULL;
}

/* blanks the comments of `s` in place: their characters become spaces, newlines stay. What is left can be searched for keywords without matching commented-out
   code, and every offset and line number is unchanged. */
static void blankComments(char *s) {
    for (char *p = s; *p;) {
        if (p[0] == '/' && p[1] == '/') {
            while (*p && *p != '\n') *p++ = ' ';
        } else if (p[0] == '/' && p[1] == '*') {
            p[0] = p[1] = ' ';
            p += 2;
            while (*p && !(p[0] == '*' && p[1] == '/')) {
                if (*p != '\n') *p = ' ';
                p++;
            }
            if (*p) { p[0] = p[1] = ' '; p += 2; }
        } else {
            p++;
        }
    }
}

/* does `src` (comments blanked) define `void main`? (`void mainImage(` must not count: it contains "void main") */
static bool definesMain(const char *src) {
    for (const char *p = findWord(src, src, "void"); p; p = findWord(src, p + 1, "void")) {
        const char *q = p + 4;
        if (!isspace((unsigned char)*q)) continue;
        while (isspace((unsigned char)*q)) q++;
        if (!strncmp(q, "main", 4) && !isIdent(q[4])) return true;
    }
    return false;
}

/* does `src` (comments blanked) already declare `name` as a uniform? The statement the identifier sits in, back to the previous ; { or } (or the start of the text), must
   contain the word `uniform`. That covers a declaration split over several lines, and one sharing its line with other code (`uniform float a; float b = iTime;` declares
   no iTime). `name` must be a whole identifier: `uniform float iTimeDelta;` does not declare iTime. */
static bool declares(const char *src, const char *name) {
    for (const char *p = findWord(src, src, name); p; p = findWord(src, p + 1, name)) {
        const char *st = p, *u;
        while (st > src && !strchr(";{}", st[-1])) st--;
        u = findWord(st, st, "uniform");
        if (u && u < p) return true;
    }
    return false;
}

/* does `src` (comments blanked) mention iChannel0..3, iChannelTime or iChannelResolution? Shadertoy's texture, buffer and audio inputs are not supported */
static bool usesChannels(const char *src) {
    for (const char *p = strstr(src, "iChannel"); p; p = strstr(p + 1, "iChannel"))
        if (p == src || !isIdent(p[-1])) return true;
    return false;
}

/* plain shaders pass through unchanged; Shadertoy shaders (mainImage, no main) get the Shadertoy uniforms and a main() wrapper. *channels: iChannel inputs are used.
   Everything is looked for in a copy of the source with its comments blanked, so that commented-out code (`// uniform float iTime;`, `// void main`) counts for nothing. */
static char *prepareFrag(const char *src, bool *toy, bool *channels) {
    char *scan = strdup(src);
    if (!scan) die("out of memory");
    blankComments(scan);
    *channels = usesChannels(scan);
    *toy = findWord(scan, scan, "mainImage") && !definesMain(scan);
    if (!*toy) { free(scan); return strdup(src); }

    static const char *tail =
        "\nout vec4 wsFragColor;\n"
        "void main() {\n"
        "    vec4 c = vec4(0.0, 0.0, 0.0, 1.0);\n"
        "    mainImage(c, gl_FragCoord.xy);\n"
        "    wsFragColor = vec4(c.rgb, 1.0);\n"
        "}\n";

    char *body = strdup(src), version[128] = "#version 330 core", *v = strstr(scan, "#version"); /* not one inside a comment */
    if (v) { /* keep the author's version line; blank it in the body so line numbers still match */
        v = body + (v - scan);
        char *e = strchr(v, '\n');
        size_t n = e ? (size_t)(e - v) : strlen(v);
        snprintf(version, sizeof version, "%.*s", (int)MIN(n, sizeof version - 1), v);
        memset(v, ' ', n);
    }
    char *out = NULL; size_t outLen = 0;
    FILE *m = open_memstream(&out, &outLen);
    if (!m) die("out of memory");
    fprintf(m, "%s\n", version);
    for (int i = 0; i < U_COUNT; i++)
        if (!declares(scan, uniDefs[i].name)) fprintf(m, "uniform %s %s;\n", uniDefs[i].type, uniDefs[i].name);
    fprintf(m, "#line 1\n%s%s", body, tail);
    fclose(m); /* `out` is valid from here on */
    free(body);
    free(scan);
    return out;
}

/* true if shader (or, with isProg, program) `obj` compiled (linked); otherwise prints its log */
static bool buildOk(unsigned obj, bool isProg, const char *what) {
    int ok; char msg[4096];
    (isProg ? glGetProgramiv : glGetShaderiv)(obj, isProg ? GL_LINK_STATUS : GL_COMPILE_STATUS, &ok);
    if (!ok) {
        (isProg ? glGetProgramInfoLog : glGetShaderInfoLog)(obj, sizeof msg, NULL, msg);
        warn("%s failed to %s:\n%s", what, isProg ? "link" : "compile", msg);
    }
    return ok;
}

/* returns 0 (after printing the log) instead of exiting, so a reload can fail safely */
static unsigned compile(const char *src, GLenum type, const char *what) {
    unsigned sh = glCreateShader(type);
    glShaderSource(sh, 1, &src, NULL);
    glCompileShader(sh);
    if (buildOk(sh, false, what)) return sh;
    glDeleteShader(sh);
    return 0;
}

static unsigned buildProgram(const char *path) {
    char *raw = readFile(path);
    if (!raw) return 0;
    bool toy, channels;
    char *src = prepareFrag(raw, &toy, &channels);
    free(raw);
    info("%s: %s shader", path, toy ? "Shadertoy" : "plain");
    if (channels) warn("%s uses iChannel inputs (textures, buffers, audio), which are not supported: expect a build error, or black where they are sampled", path);

    unsigned vs = compile(fullscreenVert, GL_VERTEX_SHADER, "vertex shader"), fs = compile(src, GL_FRAGMENT_SHADER, path), p = 0;
    free(src);
    if (vs && fs) {
        p = glCreateProgram();
        glAttachShader(p, vs);
        glAttachShader(p, fs);
        glLinkProgram(p);
        if (!buildOk(p, true, path)) { glDeleteProgram(p); p = 0; }
    }
    if (vs) glDeleteShader(vs);
    if (fs) glDeleteShader(fs);
    return p;
}

static void setResolution(void) {
    if (U[U_RES].loc < 0) return;
    if (U[U_RES].type == GL_FLOAT_VEC3) glUniform3f(U[U_RES].loc, S.rw, S.rh, 1.0f);
    else if (U[U_RES].type == GL_INT_VEC2) glUniform2i(U[U_RES].loc, S.rw, S.rh);
    else glUniform2f(U[U_RES].loc, S.rw, S.rh);
}

/* look up the (current) program's uniforms in one pass over its active ones, and set the constant ones */
static void bindUniforms(void) {
    bool viaAlias[U_COUNT] = {false};
    GLint count = 0;
    for (int k = 0; k < U_COUNT; k++) U[k].loc = -1;
    glGetProgramiv(prog, GL_ACTIVE_UNIFORMS, &count);
    for (GLint i = 0; i < count; i++) {
        char nm[128]; GLint len, size; GLenum ty;
        glGetActiveUniform(prog, i, sizeof nm, &len, &size, &ty, nm);
        for (int k = 0; k < U_COUNT; k++) {
            bool isAlias = uniDefs[k].alias && !strcmp(nm, uniDefs[k].alias);
            if (!isAlias && (strcmp(nm, uniDefs[k].name) || viaAlias[k])) continue; /* the alias wins over the Shadertoy name */
            U[k].loc = glGetUniformLocation(prog, nm);
            U[k].type = ty;
            viaAlias[k] |= isAlias;
        }
    }
    setResolution();
    if (U[U_MOUSE].loc >= 0) glUniform4f(U[U_MOUSE].loc, 0, 0, 0, 0);
}

static void setUniforms(double t, double dt, unsigned long frame) {
    if (U[U_TIME].loc >= 0) glUniform1f(U[U_TIME].loc, (float)t);
    if (U[U_DELTA].loc >= 0) glUniform1f(U[U_DELTA].loc, (float)(dt * speed));
    if (U[U_FRAME].loc >= 0) {
        if (U[U_FRAME].type == GL_INT) glUniform1i(U[U_FRAME].loc, (int)(frame & 0x7fffffff));
        else glUniform1f(U[U_FRAME].loc, (float)(frame & 0xffffff)); /* a float counts exactly up to 2^24 */
    }
    if (U[U_DATE].loc >= 0) { /* the broken-down time only changes once a second */
        static time_t cachedSec; static float date[4];
        time_t tt = time(NULL);
        if (tt != cachedSec) {
            struct tm lt;
            localtime_r(&tt, &lt);
            cachedSec = tt;
            date[0] = lt.tm_year + 1900;
            date[1] = lt.tm_mon;
            date[2] = lt.tm_mday;
            date[3] = lt.tm_hour * 3600 + lt.tm_min * 60 + lt.tm_sec;
        }
        glUniform4f(U[U_DATE].loc, date[0], date[1], date[2], date[3]);
    }
}

/* makes np the running program; the old one is deleted (at startup there is none: glDeleteProgram ignores 0) */
static void useProgram(unsigned np) {
    glDeleteProgram(prog);
    prog = np;
    glUseProgram(prog);
    bindUniforms();
}

static void reloadShader(void) {
    unsigned np = buildProgram(fragFile);
    if (!np) { warn("reload failed, keeping the previous shader"); return; }
    useProgram(np);
    info("shader reloaded");
}

/* shader file watch */
static void setupWatch(const char *path) {
    char *dir = strdup(path), *slash = strrchr(dir, '/'); /* kept for good: watchName points into it */
    watchName = slash ? slash + 1 : dir;
    if (slash) *slash = 0;
    ino = inotify_init1(IN_NONBLOCK | IN_CLOEXEC);
    /* watch the directory: editors usually replace the file instead of rewriting it */
    if (ino < 0 || inotify_add_watch(ino, !slash ? "." : *dir ? dir : "/", IN_CLOSE_WRITE | IN_MOVED_TO) < 0) {
        warn("inotify (reload on save disabled, SIGUSR1 still works): %s", strerror(errno));
        if (ino >= 0) close(ino);
        ino = -1;
    }
}

static void drainWatch(void) {
    char buf[4096] __attribute__((aligned(8))); ssize_t n;
    while (ino >= 0 && (n = read(ino, buf, sizeof buf)) > 0)
        for (char *p = buf; p < buf + n;) {
            struct inotify_event *e = (struct inotify_event *)p;
            if (e->len && !strcmp(e->name, watchName)) reloadFlag = true;
            p += sizeof *e + e->len;
        }
}

/* surface */
/* the root-sized pixmap, wrapped as a GLX pixmap that GL renders into (made current here) */
static void surfaceCreate(int w, int h) {
    S = (typeof(S)){.w = w, .h = h};
    S.rw = (int)fmax(w * scale + 0.5, 1); /* a render size of at least 1 pixel */
    S.rh = (int)fmax(h * scale + 0.5, 1);
    S.pm = XCreatePixmap(d, root, w, h, wa.depth);
    int before = xerrors;
    S.gp = glXCreatePixmap(d, fbcfg, S.pm, NULL);
    XSync(d, False);
    if (!S.gp || xerrors != before || !glXMakeCurrent(d, S.gp, ctx)) die("cannot render into the GLX pixmap");
    if (S.rw != w || S.rh != h) { /* below full size: render offscreen, upscale into the pixmap */
        /* RGB8 is enough (the shader's alpha is always 1.0) and cheaper in memory bandwidth, but GL does not promise that it can be rendered to; RGBA8 it does */
        static const GLenum formats[] = {GL_RGB8, GL_RGBA8};
        GLenum status = 0;
        glGenRenderbuffers(1, &S.rb);
        glGenFramebuffers(1, &S.fbo);
        glBindFramebuffer(GL_FRAMEBUFFER, S.fbo);
        for (int i = 0; i < ARRAY_LEN(formats) && status != GL_FRAMEBUFFER_COMPLETE; i++) {
            glBindRenderbuffer(GL_RENDERBUFFER, S.rb);
            glRenderbufferStorage(GL_RENDERBUFFER, formats[i], S.rw, S.rh);
            glFramebufferRenderbuffer(GL_FRAMEBUFFER, GL_COLOR_ATTACHMENT0, GL_RENDERBUFFER, S.rb);
            status = glCheckFramebufferStatus(GL_FRAMEBUFFER);
        }
        if (status != GL_FRAMEBUFFER_COMPLETE) die("framebuffer incomplete (status 0x%x)", status);
    }
    glBindFramebuffer(GL_FRAMEBUFFER, 0);
    if (fbDbl) glDrawBuffer(GL_FRONT); /* the default framebuffer's draw buffer sticks across binds */
    glViewport(0, 0, S.rw, S.rh); /* viewport state is the context's, not the framebuffer's: it needs setting once per surface */
    info("%dx%d, rendering at %dx%d%s", w, h, S.rw, S.rh, S.fbo ? "" : " (no intermediate buffer)");
}

static void surfaceDestroy(void) {
    glFinish();
    if (S.fbo) { glDeleteFramebuffers(1, &S.fbo); glDeleteRenderbuffers(1, &S.rb); }
    glXMakeCurrent(d, None, NULL); /* the new GLX pixmap gets bound by surfaceCreate */
    glXDestroyPixmap(d, S.gp);
    XFreePixmap(d, S.pm);
    memset(&S, 0, sizeof S);
}

/* `run` is the running shader time, `dt` the real seconds since the previous frame */
static void renderFrame(double run, double dt, unsigned long frame) {
    glBindFramebuffer(GL_FRAMEBUFFER, S.fbo);
    setUniforms(run, dt, frame);
    glDrawArrays(GL_TRIANGLES, 0, 3);
    if (S.fbo) { /* a GLX pixmap has the same orientation as a window (row 0 at the bottom): no flip needed */
        glBindFramebuffer(GL_READ_FRAMEBUFFER, S.fbo);
        glBindFramebuffer(GL_DRAW_FRAMEBUFFER, 0);
        glBlitFramebuffer(0, 0, S.rw, S.rh, 0, 0, S.w, S.h, GL_COLOR_BUFFER_BIT, GL_LINEAR);
    }
    glXWaitGL(); /* make what GL drew visible to the X server (it waits for GL to finish, no glFinish needed) */
}

/* wallpaper */
/* sets a root pixmap property (_XROOTPMAP_ID or ESETROOT_PMAP_ID) to `pm` */
static void setPmapProp(Atom prop, Pixmap pm) {
    XChangeProperty(d, root, prop, XA_PIXMAP, 32, PropModeReplace, (unsigned char *)&pm, 1);
}

/* Make the frame visible. _XROOTPMAP_ID is rewritten every frame on purpose: GL rendering raises no damage event for picom, but a PropertyNotify on it
   makes picom repaint the root, even when the value is identical. ESETROOT_PMAP_ID only has to exist and match (takeOverRoot checks it), so it is written
   once per surface, with the background pixmap, which also only changes when the surface is recreated. */
static void publish(void) {
    if (!S.announced) { XSetWindowBackgroundPixmap(d, root, S.pm); setPmapProp(A[A_ESETPMAP], S.pm); S.announced = true; }
    setPmapProp(A[A_ROOTPMAP], S.pm);
    XClearWindow(d, root);
    XFlush(d);
}

/* On a clean exit, copy the last frame into a pixmap that outlives us (RetainPermanent, like Esetroot and feh) and point the root properties at it; the live pixmap
   dies with our connection. The next wallpaper setter, or our next start (takeOverRoot), frees it with XKillClient. */
static void leaveStill(void) {
    if (!S.pm || !S.announced) return; /* nothing was drawn on this surface yet (quit before the first frame, or right after a resize): a new pixmap's contents are undefined, so the wallpaper stays as it is */
    glFinish(); glXWaitGL();
    Pixmap still = XCreatePixmap(d, root, S.w, S.h, wa.depth);
    GC gc = XCreateGC(d, still, 0, NULL);
    XCopyArea(d, S.pm, still, gc, 0, 0, S.w, S.h, 0, 0);
    XFreeGC(d, gc);
    XSetWindowBackgroundPixmap(d, root, still);
    setPmapProp(A[A_ROOTPMAP], still);
    setPmapProp(A[A_ESETPMAP], still);
    XClearWindow(d, root);
    XSetCloseDownMode(d, RetainPermanent);
    XSync(d, False);
}

/* Single instance: kill the client that owns the current root pixmap (a previous run, or a wallpaper setter that left one behind), then clear the stale properties.
   Only when _XROOTPMAP_ID and ESETROOT_PMAP_ID agree (the Esetroot convention): a lone _XROOTPMAP_ID may point at something else. */
static void takeOverRoot(void) {
    unsigned long v[MAX_PROP_ITEMS], e[MAX_PROP_ITEMS];
    if (getProp(root, A[A_ROOTPMAP], XA_PIXMAP, v) == 1 && getProp(root, A[A_ESETPMAP], XA_PIXMAP, e) == 1 && v[0] && v[0] == e[0]) {
        xerrQuiet = true; /* a stale id (owner already gone) answers BadValue: expected, not worth printing */
        XKillClient(d, v[0]);
        XSync(d, False);
        xerrQuiet = false;
    }
    XDeleteProperty(d, root, A[A_ROOTPMAP]);
    XDeleteProperty(d, root, A[A_ESETPMAP]);
    XSync(d, False);
}

/* window rules */
/* is `s` one of the items of `l`? An item with a * or ? in it is a glob pattern (fnmatch, so `\` quotes: `\[x\]*` matches "[x] ..."); any other item must match exactly.
   Patterns are for the names that vary: Steam's WM_CLASS steam_app_*, or a title that carries a document name or a score. */
static bool inList(const StrList *l, const char *s) {
    for (int k = 0; s && k < l->n; k++) {
        const char *item = l->v[k];
        if (strpbrk(item, "*?") ? !fnmatch(item, s, 0) : !strcmp(item, s)) return true;
    }
    return false;
}

/* does the window's WM_CLASS (instance or class name) or, with `withTitle`, its title (_NET_WM_NAME, or the legacy WM_NAME) match one of the items of `l` (see inList)? */
static bool matches(Window win, const StrList *l, bool withTitle) {
    if (!l->n) return false;
    bool hit = false;
    XClassHint h = {0};
    if (XGetClassHint(d, win, &h)) { hit = inList(l, h.res_name) || inList(l, h.res_class); XFree(h.res_name); XFree(h.res_class); }
    if (hit || !withTitle) return hit;
    Atom t; int fmt; unsigned long n = 0, left; unsigned char *p = NULL; /* the UTF-8 title, _NET_WM_NAME */
    if (XGetWindowProperty(d, win, A[A_NETNAME], 0, 1024, False, A[A_UTF8], &t, &fmt, &n, &left, &p) == Success && p && fmt == 8 && n && strlen((char *)p) == n)
        hit = inList(l, (char *)p); /* the property is NUL-terminated by Xlib; an embedded NUL must not truncate the match */
    if (p) XFree(p);
    char *legacy = NULL; /* the old WM_NAME */
    if (!hit && XFetchName(d, win, &legacy) && legacy) { hit = inList(l, legacy); XFree(legacy); }
    return hit;
}

enum { FS_NO, FS_PAUSE, FS_KILL }; /* what a window asks of us: nothing, pausing the shader, or pausing it and stopping the compositor */

/* FS_NO unless the window is fullscreen, opaque, covers the whole root (a fullscreen window on one monitor leaves the wallpaper visible on the others) and is
   not on the -k list: then FS_PAUSE, or FS_KILL when, on top of that, the window is on the -K list, matched by WM_CLASS or by window title (-K wins over -k). */
static int fullscreenState(Window win) {
    unsigned long v[MAX_PROP_ITEMS];
    bool fs = false;
    if (!win || win == root) return FS_NO;

    /* the checks are ordered by cost in X round trips: most windows stop at the first, the -k/-K matching and the geometry come last */
    for (int i = 0, n = getProp(win, A[A_STATE], XA_ATOM, v); i < n; i++) fs |= v[i] == A[A_FULLSCREEN];
    if (!fs) return FS_NO;
    if (getProp(win, A[A_OPACITY], XA_CARDINAL, v) == 1 && v[0] < OPACITY_OPAQUE) return FS_NO; /* reduced opacity: see-through */
    bool onKillList = matches(win, &killComp, true);
    if (!onKillList && matches(win, &pauseExempt, false)) return FS_NO;

    Window r, child;
    int x, y, rx, ry;
    unsigned ww, hh, bw, depth;
    bool covers = XGetGeometry(d, win, &r, &x, &y, &ww, &hh, &bw, &depth) && XTranslateCoordinates(d, win, root, 0, 0, &rx, &ry, &child) &&
                 rx <= 0 && ry <= 0 && rx + (int)ww >= S.w && ry + (int)hh >= S.h;
    return !covers ? FS_NO : onKillList ? FS_KILL : FS_PAUSE;
}

/* compositor */
/* up to `max` pids of this user's live processes whose name is `name`, from /proc/<pid>/stat ("pid (comm) S ..."):
   zombies don't count. Done here instead of pgrep/pkill, so that we know synchronously what was running. */
static int findProcs(const char *name, pid_t *pids, int max) {
    DIR *dir = opendir("/proc"); int n = 0;
    for (struct dirent *e; dir && n < max && (e = readdir(dir));) {
        char path[320], line[256], *lp, *rp; struct stat st;
        if (!isdigit((unsigned char)e->d_name[0])) continue;
        snprintf(path, sizeof path, "/proc/%s", e->d_name);
        if (stat(path, &st) || st.st_uid != getuid()) continue;
        snprintf(path, sizeof path, "/proc/%s/stat", e->d_name);
        FILE *f = fopen(path, "r");
        if (f && fgets(line, sizeof line, f) && (lp = strchr(line, '(')) && (rp = strrchr(lp, ')')) && rp[1] == ' ' && rp[2] != 'Z' &&
            (size_t)(rp - lp - 1) == strlen(name) && !memcmp(lp + 1, name, strlen(name)))
            pids[n++] = (pid_t)atoi(e->d_name);
        if (f) fclose(f);
    }
    if (dir) closedir(dir);
    return n;
}

/* Commands that may precede the real one, with their single-letter options that take a value as the next word (env: `-u NAME`, nice: a bare `-n N`, systemd-run: `-p PROP`;
   `-i`, `-N`, `--adjustment=N`, `--user` etc. take none). A long option with a separate value (`--unit foo`) is not understood: that is what -N is for. */
static const struct { const char *name, *valOpts; } wrappers[] = {
    {"env", "uCS"}, {"nice", "n"}, {"setsid", ""}, {"nohup", ""}, {"prime-run", ""}, {"systemd-run", "HMuEp"},
};

/* Shells are never a compositor's process name: `-C "sh -c '...'"` says nothing about the real one, and -K would stop every shell of the user's. */
static bool isShell(const char *name) {
    static const char *const shells[] = {"sh", "bash", "dash", "ash", "ksh", "mksh", "zsh", "fish", "csh", "tcsh"};
    for (int i = 0; i < ARRAY_LEN(shells); i++)
        if (!strcmp(name, shells[i])) return true;
    return false;
}

/* The process that -K stops (and that the already-running check looks for) is the one -N names or, failing that, the one the -C command starts: its first word
   (after leading VAR=value words and the wrappers above, exec included), without the directory and cut to the COMM_LEN characters of a /proc comm name.
   With neither, picom. A shell is refused (see isShell): the name is then empty, which switches -K and the check off. */
/* the word at or after p (blanks skipped): its length goes to *n */
static const char *nextWord(const char *p, size_t *n) { p += strspn(p, " \t"); *n = strcspn(p, " \t"); return p; }

static void initCompName(void) {
    size_t n = 0;
    const char *p = compositor && !compProc ? nextWord(compositor, &n) : NULL;
    if (compProc) { /* -N may be a path, too: the process name is its last part */
        const char *slash = strrchr(compProc, '/');
        snprintf(compName, sizeof compName, "%.*s", COMM_LEN, slash ? slash + 1 : compProc);
    }
    while (p && n) {
        const char *slash = memrchr(p, '/', n), *base = slash ? slash + 1 : p, *vals = NULL; /* /usr/bin/env is env */
        size_t bn = (size_t)(p + n - base);
        bool skip = p[strcspn(p, "= \t")] == '=' || (bn == 4 && !strncmp(base, "exec", 4)); /* VAR=value, exec */
        for (int i = 0; i < ARRAY_LEN(wrappers); i++) {
            if (bn != strlen(wrappers[i].name) || strncmp(base, wrappers[i].name, bn)) continue;
            skip = true;
            vals = wrappers[i].valOpts;
        }
        if (!skip) { /* the command itself */
            snprintf(compName, sizeof compName, "%.*s", (int)MIN(COMM_LEN, bn), base);
            break;
        }
        p = nextWord(p + n, &n);
        while (vals && n && *p == '-') { /* a wrapper's options (VAR=value words are skipped by the next rounds) */
            bool takesArg = n == 2 && strchr(vals, p[1]);
            p = nextWord(p + n, &n);
            if (takesArg) p = nextWord(p + n, &n);
        }
    }
    if (isShell(compName)) {
        warn("'%s' is a shell, not the compositor: its process name is unknown, so -K and the already-running check are off (name it with -N, e.g. -N picom)", compName);
        compName[0] = 0;
    }
}

/* stop the compositor while a -K window is fullscreen, restart it afterwards: only one that was really running, and not if one is running again by then. */
static void setCompositor(bool stop) {
    static bool told; /* the "nothing to stop" notice is given once, not at every -K window */
    pid_t pids[16];
    if (!stop) compAbsent = false;
    if (stop && !compKilled && !compAbsent) {
        int n = compName[0] ? findProcs(compName, pids, ARRAY_LEN(pids)) : 0;
        if (!n) {
            compAbsent = true;
            if (!told && compName[0]) warn("-K window is fullscreen, but no process named '%s' of yours is running: nothing to stop (is that the compositor's name? see -N)", compName);
            if (!told && !compName[0]) warn("-K window is fullscreen, but the compositor's process name is unknown: nothing to stop (see -N)");
            told = true;
            return;
        }
        for (int i = 0; i < n; i++) kill(pids[i], SIGTERM);
        for (int i = 0; i < COMP_EXIT_TRIES && findProcs(compName, pids, 1); i++) poll(NULL, 0, COMP_EXIT_POLL_MS); /* a restart must not race its shutdown */
        compKilled = true;
        info("-K window is fullscreen, stopped %s", compName);
    } else if (!stop && compKilled) {
        compKilled = false;
        if (findProcs(compName, pids, 1)) { info("%s is running again, not restarting it", compName); return; }
        const char *cmd = compositor ? compositor : compProc ? compProc : "picom"; /* with no -C: the process -N names, else picom */
        spawn(cmd);
        info("restarting %s: %s", compName, cmd);
    }
}

/* The -C command starts once the first shader has built and the stale root pixmap is gone (see main): the compositor cannot latch onto a dead pixmap, and a broken
   shader never costs the running instance its wallpaper; publish() later makes the compositor pick the new one up. One that is already running (a re-exec,
   say) is left alone, when its name is known. */
static void startCompositor(void) {
    pid_t running;
    if (!compositor) return;
    if (compName[0] && findProcs(compName, &running, 1)) info("%s is already running, not starting it", compName);
    else spawn(compositor);
}

/* events */
static void updateFullscreen(void) {
    unsigned long v[MAX_PROP_ITEMS];
    Window win = getProp(root, A[A_ACTIVE], XA_WINDOW, v) == 1 ? v[0] : 0;
    if (win == root) win = 0; /* a window manager may name the root when nothing has focus: XSelectInput on it would replace our PropertyChangeMask from initEvents, and clear it again when the focus moves on */
    if (win != watched) { /* follow the active window so its state changes wake us up */
        if (watched) XSelectInput(d, watched, 0);
        if ((watched = win)) XSelectInput(d, win, PropertyChangeMask | StructureNotifyMask);
    }
    int state = fullscreenState(win);
    fsPaused = state != FS_NO;
    setCompositor(state == FS_KILL);
}

/* the screen changed (XRandR): the surface is rebuilt if the root's size did */
static void updateScreen(void) {
    XGetWindowAttributes(d, root, &wa);
    if (wa.width == S.w && wa.height == S.h) return;
    surfaceDestroy();
    surfaceCreate(wa.width, wa.height);
    setResolution();
    dirtyFs = true;
}

/* is the monitor blanked by DPMS? There is no event for it in Xlib, so it is polled. */
static bool screenBlanked(void) { CARD16 level; BOOL on; return hasDpms && DPMSInfo(d, &level, &on) && on && level != DPMSModeOn; }

/* a blank monitor needs no frames: looked at once per DPMS_POLL_SEC, and not while a fullscreen window or the screensaver pauses us anyway */
static void updateBlanked(double now) {
    if (fsPaused || saverOn || now < nextDpmsT) return;
    nextDpmsT = now + DPMS_POLL_SEC;
    bool off = screenBlanked();
    if (off != blanked) info("monitor %s", off ? "blanked, pausing" : "on again");
    blanked = off;
}

static void pumpEvents(void) {
    while (XPending(d)) {
        XEvent ev;
        XNextEvent(d, &ev);
        if (ev.type == PropertyNotify) {
            Atom a = ev.xproperty.atom;
            if (ev.xproperty.window == root ? a == A[A_ACTIVE] : (a == A[A_STATE] || a == A[A_OPACITY] || a == XA_WM_CLASS || a == XA_WM_NAME || a == A[A_NETNAME])) dirtyFs = true;
        } else if (ev.type == ConfigureNotify || ev.type == DestroyNotify) dirtyFs = true; /* the active window moved, resized or went away */
        else if (hasRandr && ev.type == rrEvBase + RRScreenChangeNotify) { XRRUpdateConfiguration(&ev); dirtyScreen = true; }
        else if (hasSaver && ev.type == ssEvBase + ScreenSaverNotify) {
            int st = ((XScreenSaverNotifyEvent *)&ev)->state;
            bool on = st == ScreenSaverOn || st == ScreenSaverCycle;
            if (on != saverOn) info("screensaver %s", on ? "on, pausing" : "off");
            saverOn = on;
        }
    }
}

/* subscribe to what wakes us up (root properties for the active window, XRandR changes, the screensaver, edits of the shader file) and probe DPMS.
   The screensaver extension reports the server's idle timeout (and a saver client's window), which is also what xss-lock locks on; a locker started by hand
   (i3lock from a key binding) is neither: its override-redirect window never becomes the active window, and only DPMS blanking ends the rendering behind it. */
static void initEvents(void) {
    int rrErr, dpmsEv, dpmsErr, ssErr;
    XSelectInput(d, root, PropertyChangeMask);
    if ((hasRandr = XRRQueryExtension(d, &rrEvBase, &rrErr))) XRRSelectInput(d, root, RRScreenChangeNotifyMask);
    if ((hasSaver = XScreenSaverQueryExtension(d, &ssEvBase, &ssErr))) {
        XScreenSaverInfo *si = XScreenSaverAllocInfo();
        XScreenSaverSelectInput(d, root, ScreenSaverNotifyMask);
        saverOn = si && XScreenSaverQueryInfo(d, root, si) && si->state == ScreenSaverOn; /* it may already be on when we start */
        if (si) XFree(si);
    }
    setupWatch(fragFile);
    hasDpms = DPMSQueryExtension(d, &dpmsEv, &dpmsErr) && DPMSCapable(d);
}

/* waiting */
/* The one place the program sleeps: until an X event, a shader file change, a signal or (unless `until` is negative) that monoSec() time. Frame pacing and pausing use it. */
static void waitEvents(double until) {
    struct pollfd pf[3] = {{ConnectionNumber(d), POLLIN, 0}, {ino, POLLIN, 0}, {sfd, POLLIN, 0}}; /* a negative fd is ignored */
    struct timespec ts = {0}, *timeout = NULL; /* NULL: no deadline */
    /* events may already sit in Xlib's queue (read by a round trip): the fd won't wake us for them */
    if (XPending(d)) return;
    if (until >= 0) {
        double dt = until - monoSec();
        if (dt <= 0) return;
        ts = (struct timespec){.tv_sec = (time_t)dt, .tv_nsec = (long)((dt - (time_t)dt) * 1e9)}; timeout = &ts; /* ppoll, not poll: no rounding to milliseconds */
    }
    ppoll(pf, 3, timeout, NULL);
}

/* context */
typedef GLXContext (*CreateContextAttribsFn)(Display *, GLXFBConfig, GLXContext, Bool, const int *);

/* a 3.3 core context for `cfg` if the driver offers one, else whatever it gives us; NULL on failure */
static GLXContext makeContext(GLXFBConfig cfg) {
    GLXContext c = NULL;
    CreateContextAttribsFn make = (CreateContextAttribsFn)glXGetProcAddress((const GLubyte *)"glXCreateContextAttribsARB");
    if (make) {
        int attrs[] = {GLX_CONTEXT_MAJOR_VERSION_ARB, 3, GLX_CONTEXT_MINOR_VERSION_ARB, 3, GLX_CONTEXT_PROFILE_MASK_ARB, GLX_CONTEXT_CORE_PROFILE_BIT_ARB, None};
        int before = xerrors;
        xerrQuiet = true; /* a driver without 3.3 core fails here, and that is fine: we fall back below */
        c = make(d, cfg, NULL, True, attrs);
        XSync(d, False);
        xerrQuiet = false;
        if (xerrors != before) c = NULL;
    }
    if (!c) c = glXCreateNewContext(d, cfg, GLX_RGBA_TYPE, NULL, True);
    return c;
}

/* GLX config choice */
static int cfgAttr(GLXFBConfig c, int attr) { int v = 0; glXGetFBConfigAttrib(d, c, attr, &v); return v; }

/* Picks the pixmap-capable, non-multisampled config of the root's depth with the best score: 4 * single-buffered + 2 * no depth/stencil + (same visual as the root).
   Double-buffered configs are drawn to the front buffer. Fills fbcfg and fbDbl; dies if there is none. */
static void pickConfig(VisualID rootVisual) {
    int n = 0, best = -1;
    GLXFBConfig *all = glXGetFBConfigs(d, DefaultScreen(d), &n);
    for (int i = 0; all && i < n; i++) {
        GLXFBConfig c = all[i];
        if (!(cfgAttr(c, GLX_DRAWABLE_TYPE) & GLX_PIXMAP_BIT) || !(cfgAttr(c, GLX_RENDER_TYPE) & GLX_RGBA_BIT) || cfgAttr(c, GLX_SAMPLE_BUFFERS)) continue;
        XVisualInfo *vi = glXGetVisualFromFBConfig(d, c);
        bool fits = vi && vi->depth == wa.depth, isRoot = fits && vi->visualid == rootVisual;
        if (vi) XFree(vi);
        int score = 4 * !cfgAttr(c, GLX_DOUBLEBUFFER) + 2 * (!cfgAttr(c, GLX_DEPTH_SIZE) && !cfgAttr(c, GLX_STENCIL_SIZE)) + isRoot;
        if (fits && score > best) { best = score; fbcfg = c; }
    }
    if (all) XFree(all);
    if (!fbcfg) die("no GLX framebuffer config can render into a pixmap of the root's depth");
    fbDbl = cfgAttr(fbcfg, GLX_DOUBLEBUFFER);
    info("GLX config 0x%x (%s)", cfgAttr(fbcfg, GLX_FBCONFIG_ID), fbDbl ? "double-buffered, front buffer" : "single-buffered");
}

/* GL up: config, context, surface, the first shader that builds (a broken file in a shader directory just moves on to the next), vertex array, uniforms */
static void initGL(void) {
    XGetWindowAttributes(d, root, &wa);
    pickConfig(XVisualIDFromVisual(wa.visual));
    if (!(ctx = makeContext(fbcfg))) die("cannot create GL context");
    surfaceCreate(wa.width, wa.height); /* makes the context current */
    unsigned np = 0;
    for (int i = 0; i < cands.n && !np; i++) {
        fragFile = cands.v[i];
        np = buildProgram(fragFile);
    }
    if (!np) exit(1); /* buildProgram said why */
    glDisable(GL_DITHER); /* on by default; pointless for a wallpaper that writes final 8-bit colors */
    unsigned vao; glGenVertexArrays(1, &vao); glBindVertexArray(vao);
    useProgram(np);
}

/* options */
/* Every setting, once: its letter (0: a section heading, `help` is the heading), config key (NULL: command line only), argument name and help text.
   The getopt string, the config keys and the usage text all come from this table; setOption() interprets the letters. */
static const struct { char opt; const char *key, *arg, *help; } options[] = {
    {'f', "shader", "path", "Fragment shader (plain or Shadertoy syntax). Passing a directory randomizes .frags inside on exec"},
    {0, NULL, NULL, "Shader config"},
    {'s', "speed", "x", "Animation speed multiplier (default 1)"},
    {'r', "scale", "x", "Render scale [0.N - 1] (default 1)."},
    {'F', "fps", "n", "Target fps, 0.01 - 1000 (default 30)"},
    {'T', "time_wrap", "n", "Wrap shader time back to 0 every n seconds (default: never). A float uniform gets coarse as time grows (steps of 15 ms after 1.5 days, 60 ms after 6); wrapping avoids that, but jumps unless the shader is periodic in n"},
    {0, NULL, NULL, "Window rules"},
    {'k', "fullscreen_pause_exceptions", "class", "Fullscreen pause exceptions: these windows don't pause the shader (comma-separated; * and ? are wildcards)"},
    {'K', "fullscreen_kill_compositor", "name", "Fullscreen kill compositor: windows whose WM_CLASS or title (WM_NAME) matches; while one is fullscreen the compositor is stopped, and restarted after (comma-separated; * and ? are wildcards)"},
    {'C', "compositor", "cmd", "Compositor command: run at startup and after -K; its first word is the process -K stops, unless -N says otherwise (default: picom)"},
    {'N', "compositor_process", "name", "Compositor process name: what -K stops and the already-running check looks for. Needed when -C starts a shell or a wrapper chrysanth does not know"},
    {0, NULL, NULL, "Program options"},
    {'W', "wrapper", "cmd", "Run chrysanth itself under `env cmd`, e.g. \"DRI_PRIME=1\" or \"prime-run\" (config key: wrapper)"},
    {'c', NULL, "file", "Config file specified (default: ~/.config/chrysanth/chrysanth.conf, else next to binary)"},
    {'q', NULL, "", "Quiet: print only warnings and errors"},
    {'h', NULL, "", "What you're just reading right now... (also --help)"},
};

/* config file */
static char *settingSrc[128]; /* by option letter: where the setting's value came from ("-r", or "scale in chrysanth.conf"), for the range errors of checkSettings */
static const char *srcOf(char opt) { return settingSrc[(int)opt] ? settingSrc[(int)opt] : "setting"; }

static double parseNum(const char *s, const char *opt) {
    char *end;
    double v = strtod(s, &end);
    if (end == s || *end || !isfinite(v)) die("bad number for %s: %s", opt, s); /* "nan" and "inf" parse as numbers, too: they would freeze time or make the frame period 0 */
    return v;
}
static char *trim(char *s) { /* in place: drops blanks at both ends */
    while (*s == ' ' || *s == '\t') s++;
    char *e = s + strlen(s);
    while (e > s && strchr(" \t\r\n", e[-1])) *--e = 0;
    return s;
}

/* Cleans up a value in place: trims it, with `comment` drops a trailing `# comment` (a # after a blank or a leading quoted part), then drops one pair of matching "" or ''. */
static char *clean(char *s, bool comment) {
    s = trim(s);
    if (comment) {
        char *p = s, *q = (*s == '"' || *s == '\'') ? strchr(s + 1, *s) : NULL;
        if (q) p = q + 1;
        for (; *p; p++)
            if (*p == '#' && (q || p == s || p[-1] == ' ' || p[-1] == '\t')) { *p = 0; break; }
        s = trim(s);
    }
    size_t n = strlen(s);
    if (n >= 2 && (s[0] == '"' || s[0] == '\'') && s[n - 1] == s[0]) { s[n - 1] = 0; s++; }
    return s;
}
static char *expandHome(const char *p) { /* ~ and ~/... in the shader path */
    const char *home = getenv("HOME");
    char *out = NULL;
    return p[0] == '~' && (p[1] == '/' || !p[1]) && home && asprintf(&out, "%s%s", home, p + 1) >= 0 ? out : strdup(p);
}

/* adds every non-empty item of the comma-separated list `val` (modified in place) to `l` */
static void addCsv(StrList *l, char *val) {
    for (char *tok = strtok(val, ","); tok; tok = strtok(NULL, ","))
        if (*(tok = clean(tok, false))) listAdd(l, strdup(tok));
}

/* The only place settings are interpreted, from the config file or the command line (`opt` is the option letter). `val` may be modified; `what` names the setting in errors. */
static void setOption(int opt, char *val, const char *what) {
    free(settingSrc[opt]);
    settingSrc[opt] = strdup(what);
    switch (opt) {
    case 'f': shaderPath = expandHome(val); break;
    case 's': speed = parseNum(val, what); break;
    case 'r': scale = parseNum(val, what); break;
    case 'F': fps = parseNum(val, what); break;
    case 'T': wrapSec = parseNum(val, what); break;
    case 'q': quiet = true; break;
    case 'k': addCsv(&pauseExempt, val); break;
    case 'K': addCsv(&killComp, val); break;
    case 'C': compositor = strdup(val); break;
    case 'N': compProc = strdup(val); break;
    case 'W': wrapCmd = strdup(val); break;
    }
}

/* The ranges are checked once everything is read, so that a bad value in the config file can still be overridden on the command line; the messages name where the
   value came from. (A number that is not one at all, or not finite, is refused at once by parseNum.) */
static void checkSettings(void) {
    if (!(scale > 0 && scale <= 1)) die("%s must be in (0, 1], not %g", srcOf('r'), scale);
    if (!(fps >= FPS_MIN && fps <= FPS_MAX)) die("%s must be in [%g, %g], not %g", srcOf('F'), FPS_MIN, FPS_MAX, fps);
    if (!(fabs(speed) <= SPEED_MAX)) die("%s must be in [-%g, %g], not %g", srcOf('s'), SPEED_MAX, SPEED_MAX, speed);
    if (!(wrapSec >= 0)) die("%s must not be negative, not %g", srcOf('T'), wrapSec);
}

/* Config file: `key = value` per line (see chrysanth.conf, README.md). Read before the command line, which overrides single values and adds to the lists. A NULL path does nothing. */
static void loadConfig(const char *path, bool mustExist) {
    FILE *f = path ? fopen(path, "r") : NULL;
    if (!f && path && mustExist) die("%s: %s", path, strerror(errno));
    if (!f) return;
    info("config: %s", path);
    const char *base = strrchr(path, '/'); /* the file's own name is what the messages quote: the start of a long path says nothing */
    base = base ? base + 1 : path;
    char *line = NULL; size_t cap = 0;
    for (int ln = 1; getline(&line, &cap, f) > 0; ln++) {
        char *s = trim(line), *eq = strchr(s, '=');
        if (!*s || *s == '#' || *s == ';') continue;
        if (!eq) { warn("%s:%d: expected key = value", path, ln); continue; }
        *eq = 0;
        char *key = trim(s), *val = clean(eq + 1, true), what[64];
        if (!*val) { warn("%s:%d: empty value for '%s'", path, ln, key); continue; }
        int opt = 0;
        for (int i = 0; i < ARRAY_LEN(options); i++)
            if (options[i].key && !strcmp(key, options[i].key)) opt = options[i].opt;
        if (!opt) { warn("%s:%d: unknown key '%s'", path, ln, key); continue; }
        snprintf(what, sizeof what, "%.40s in %.15s", key, base);
        setOption(opt, val, what);
    }
    free(line);
    fclose(f);
}

static ssize_t exePath(char *buf, size_t size) { /* this binary's path, NUL-terminated in buf; <= 0 on failure */
    ssize_t n = readlink("/proc/self/exe", buf, size - 1);
    if (n > 0) buf[n] = 0;
    return n;
}

/* Default config: $XDG_CONFIG_HOME/chrysanth/chrysanth.conf (else ~/.config/chrysanth/chrysanth.conf), then
   chrysanth.conf next to the running binary (so a checkout works as it is); NULL if neither exists. */
static char *defaultConfigPath(void) {
    const char *xdg = getenv("XDG_CONFIG_HOME"), *exeDir = NULL;
    char exe[EXE_PATH_MAX], *slash, *found = NULL;
    if (exePath(exe, sizeof exe) > 0 && (slash = strrchr(exe, '/'))) {
        *slash = 0;
        exeDir = exe;
    }
    struct { const char *fmt, *dir; } cand[] = {{"%s/chrysanth/chrysanth.conf", xdg}, {"%s/chrysanth.conf", exeDir}}; /* in order of preference */
    if (!(xdg && *xdg)) {
        cand[0].fmt = "%s/.config/chrysanth/chrysanth.conf";
        cand[0].dir = getenv("HOME");
    }
    for (int i = 0; i < ARRAY_LEN(cand) && !found; i++) {
        char *p = NULL;
        if (cand[i].dir && *cand[i].dir && asprintf(&p, cand[i].fmt, cand[i].dir) >= 0) {
            if (access(p, R_OK)) free(p);
            else found = p;
        }
    }
    return found;
}

/* shader choice */
/* The shader setting may name a directory: its .frag files (not hidden, regular after symlinks) are the candidates, random one first; main() uses the first that compiles. */
static void resolveShader(void) {
    struct stat st;
    if (stat(shaderPath, &st) || !S_ISDIR(st.st_mode)) { listAdd(&cands, shaderPath); return; }

    DIR *dir = opendir(shaderPath);
    if (!dir) die("%s: %s", shaderPath, strerror(errno));
    for (struct dirent *e; (e = readdir(dir));) {
        size_t n = strlen(e->d_name); char *path;
        if (e->d_name[0] == '.' || n <= 5 || strcasecmp(e->d_name + n - 5, ".frag")) continue;
        if (asprintf(&path, "%s/%s", shaderPath, e->d_name) < 0) die("out of memory");
        if (stat(path, &st) || !S_ISREG(st.st_mode)) { free(path); continue; }
        listAdd(&cands, path);
    }
    closedir(dir);
    if (!cands.n) die("no .frag files in %s", shaderPath);

    srandom((unsigned)time(NULL) ^ ((unsigned)getpid() << 16));
    int j = (int)(random() % cands.n);
    const char *tmp = cands.v[0]; cands.v[0] = cands.v[j]; cands.v[j] = tmp;
    info("%s: %d shader%s, starting with %s", shaderPath, cands.n, cands.n == 1 ? "" : "s", cands.v[0]);
}

/* The wrapper setting: re-execute ourselves as `env <wrapper> <this binary> <same args>`, so things like DRI_PRIME=1 (or prime-run, nice -n 10, ...) are in place
   before any GL/X work happens. CHRYSANTH_WRAPPED marks the second run, which skips this (it reads the same config and would otherwise loop). */
static void applyWrapper(int argc, char **argv) {
    if (getenv("CHRYSANTH_WRAPPED")) { unsetenv("CHRYSANTH_WRAPPED"); return; } /* not inherited by the compositor or anything else we start */
    if (!wrapCmd) return;
    char exe[EXE_PATH_MAX], *script = NULL;
    if (exePath(exe, sizeof exe) <= 0 || asprintf(&script, "exec env %s \"$@\"", wrapCmd) < 0) die("cannot apply wrapper");
    argv[0] = exe;
    info("wrapper: env %s", wrapCmd);
    setenv("CHRYSANTH_WRAPPED", "1", 1);
    /* sh -c script sh exe args...: "$@" is exe plus the original arguments */
    char *nv[argc + 5];
    nv[0] = "sh"; nv[1] = "-c"; nv[2] = script; nv[3] = "sh";
    memcpy(nv + 4, argv, (size_t)(argc + 1) * sizeof *nv); /* the original arguments, NULL included */
    execv("/bin/sh", nv);
    die("/bin/sh: %s", strerror(errno));
}

/* command line */
static const struct option longOpts[] = {{"help", no_argument, NULL, 'h'}, {NULL, 0, NULL, 0}};

static void usage(FILE *f, bool full) {
    bool color = isatty(fileno(f));
    const char *green = color ? "\033[1;32m" : "", *cyan = color ? "\033[1;36m" : "";
    const char *yellow = color ? "\033[33m" : "", *reset = color ? "\033[0m" : "";
    fprintf(f, "%suse:%s chrysanth %s-f%s %sshader.frag|dir/%s %s[options]%s\n", green, reset, cyan, reset, yellow, reset, yellow, reset);
    if (!full) { fprintf(f, "See 'chrysanth -h' (or --help) for options.\n"); return; }
    for (int i = 0; i < ARRAY_LEN(options); i++) {
        if (options[i].opt) fprintf(f, "  %s-%c%s %s%-5s%s %s\n", cyan, options[i].opt, reset, yellow, options[i].arg, reset, options[i].help);
        else fprintf(f, "\n%s\n", options[i].help);
    }
    fprintf(f, "\nSee README.md for more details\n");
}

/* Reads the config file, then the command line on top of it. Exits for -h, for a bad option and for a missing shader. */
static void readSettings(int argc, char **argv) {
    char optString[2 * ARRAY_LEN(options) + 1] = "", *o = optString; /* the getopt string: each letter, then ':' if it takes an argument */
    for (int i = 0; i < ARRAY_LEN(options); i++)
        if (options[i].opt) o += sprintf(o, "%c%s", options[i].opt, *options[i].arg ? ":" : "");

    /* the config file is read first so the command line can override it, so -c has to be found before the real option pass. -h and -q are acted on here too: the
       "config:" notice must obey -q, and a broken config file must not get in the way of the help. */
    const char *cfgPath = NULL;
    opterr = 0;
    for (int c; (c = getopt_long(argc, argv, optString, longOpts, NULL)) != -1;) {
        if (c == 'c') cfgPath = optarg;
        else if (c == 'q') quiet = true;
        else if (c == 'h') { usage(stdout, true); exit(0); }
    }
    opterr = 1;
    optind = 0; /* 0, not 1: makes glibc and musl start over, including their argv reordering state */
    char *defPath = cfgPath ? NULL : defaultConfigPath();
    loadConfig(cfgPath ? cfgPath : defPath, cfgPath != NULL);
    free(defPath);

    for (int c; (c = getopt_long(argc, argv, optString, longOpts, NULL)) != -1;) {
        switch (c) {
        case 'c': case 'h': break; /* handled above */
        case '?': usage(stderr, false); exit(1);
        default: setOption(c, optarg, (char[]){'-', (char)c, 0}); /* every other option is a setting */
        }
    }
    if (!shaderPath) { usage(stderr, false); exit(1); }
}

/* main */
int main(int argc, char **argv) {
    readSettings(argc, argv);
    applyWrapper(argc, argv);
    initCompName(); /* after the wrapper's re-exec, so that its notice is printed once */
    resolveShader();
    checkSettings();

    setupSignals();
    openDisplay();
    takeOverRoot();
    // VVV possibly outdated comment now? swapped initGL with takeOverRoot to fix a bug
    /* Whatever a bad shader can make fail comes before the running instance is touched: a typo or a compile error exits here, and the wallpaper it was showing stays.
       Only then does the stale root pixmap go (takeOverRoot) and the compositor start, so that it cannot latch onto a dead one; the first publish() makes it pick
       up the new wallpaper. The price: the compositor starts one GL setup and shader build later than it used to. */
    initGL();
    startCompositor();
    initEvents();

    /* running shader time is accumulated frame by frame, so a pause simply adds nothing */
    double shaderT = 0, lastNow = -1; unsigned long frameNo = 0;

    while (!quitFlag) {
        pumpEvents();
        drainWatch();
        drainSignals();
        if (quitFlag) break;
        if (dirtyScreen) { dirtyScreen = false; updateScreen(); }
        if (reloadFlag) { reloadFlag = false; reloadShader(); }
        if (dirtyFs) { dirtyFs = false; updateFullscreen(); }

        double now = monoSec();
        updateBlanked(now);
        /* paused: block until an X event, a file change or a signal (blank: also the next DPMS check); the first frame after is due at once */
        if (fsPaused || saverOn || blanked) { lastNow = -1; nextT = 0; waitEvents(fsPaused || saverOn ? -1 : nextDpmsT); continue; }
        /* not due yet: sleep, but wake for events and reloads */
        if (now < nextT) { waitEvents(nextT); continue; }

        double period = 1.0 / fps, dt = lastNow < 0 ? period : now - lastNow;
        dt = fmin(dt, fmax(STALL_MIN_SEC, STALL_PERIODS * period)); /* after a stall the animation goes on, it doesn't jump */
        shaderT += dt * speed;
        if (wrapSec > 0 && fabs(shaderT) >= wrapSec) shaderT = fmod(shaderT, wrapSec); /* -T: keeps the float uniform fine-grained on a wallpaper that runs for weeks */
        lastNow = now;
        renderFrame(shaderT, dt, frameNo++);
        publish();
        /* absolute deadlines keep the rate steady; more than a frame behind (or the first frame after a pause): resync to one frame from now, no catch-up burst */
        nextT += period;
        double after = monoSec();
        if (after - nextT > period) nextT = after + period;
    }

    /* clean shutdown: the live pixmap dies with us, so leave a still of the last frame as the wallpaper */
    leaveStill();
    setCompositor(false); /* after leaveStill, so a restarted picom finds the wallpaper; exiting while a -K window is fullscreen must not leave the desktop without picom */
    surfaceDestroy();
    glXDestroyContext(d, ctx);
    XCloseDisplay(d);
    return 0;
}
