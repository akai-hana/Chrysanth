<div align="center">

# Chrysanth【菊】

###### The fastest X11 wallpaper shader renderer.

![](https://github.com/akai-hana/assets/blob/main/chrysanth-example.gif)

</div>

### Quick anchors

- [About 菊](#about-菊)
- [Build](#build)
- [Usage](#usage)
- [Config](#config)
- [Benchmarks](#benchmarks) _<-- TODO!_

## About 菊

Chrysanth is a shader renderer for X11 desktop wallpapers.

It renders GLSL fragment shaders to your background wallpaper (X11's root window pixmap), allowing to have a live shader render as your desktop's wallpaper.

It offers several QoL features, such as fullscreen detection to smartly pause/resume the shader, as well as a config file to manage exceptions, rendering settings, shader-picking randomization on launch, and command wrapping/appending to tie a compositor to Chrysanth's lifecycle.

Chrysanth is compatible with regular .frag files, or Shadertoy-downloaded shaders.

---

This shader renderer is extremely fast because it works entirely on the GPU.

Some alternative X11-root shader renderers draw to an offscreen buffer, and do a GPU -> CPU readback, plus an upload over the X socket.

Chrysanth optimizes the rendering pipeline by completely skipping any sort of buffering, and rendering straight to the X root background itself (binding to the pixmap as a GLX drawable). This way, the shader is rendered entirely by the GPU, without any kind of copy, CPU readback processing, shared memory upload or X socket handling.

Also thanks to this, Chrysanth is compatible with any compositing done, since picom already composites windows against the same pixmap Chrysanth renders into, so it'll composite like it would with any regular wallpaper.

## Build

```
# Download
git clone https://github.com/akai-hana/Chrysanth
cd Chrysanth

# Install
make
make install # optional. installs the binary to /usr/local/bin

# optional: put the config file where Chrysanth looks for it (see Config)
mkdir -p ~/.config/chrysanth && cp chrysanth.conf ~/.config/chrysanth/
```

#TODO: make `make install` mkdir ~/.config/chrysanth and install the config file there.

## Usage

```
chrysanth -f shader.frag [options]
```

.frag file and additional options can be configured on Chrysanth's config (`~/.config/chrysanth/chrysanth.conf`), or passed directly on the CLI.

See `chrysanth --help` (or `-h`) for more info.

---

Re-running Chrysanth replaces the launched instance. If any compositor is running, it keeps it alive too.

This makes re-exec-ing a safe way to switch shaders.

## Config

An example config file is provided with all options commented.

Chrysanth looks for `chrysanth.conf` in `~/.config/chrysanth/`, or next to the binary, so a cloned repo can be self-contained.

You can also specify one through CLI (`chrysanth -c file.conf`).

---

Tip: to get the `WM_CLASS`/`WM_NAME` of a window (to configure exceptions), run the following command and left-click the window:

```
xprop | grep -E "WM_CLASS|WM_NAME"
```

`fullscreen_pause_exceptions` (`-k`) matches a window's `WM_CLASS` (either of its two strings), while `fullscreen_kill_compositor` (`-K`) matches either its `WM_CLASS` or its title (`WM_NAME`).
TODO: make it so that both accept wm_class and wm_name, no need for behavior distinction

## Benchmarks

TODO!

<!--
Every renderer was measured on the same machine, with the same shader, resolution and frame rate, over a fixed window of time. A renderer's cost isn't confined to its own process, since per-frame work also lands in the X server and the compositor, so all three are reported.

| Renderer | Client CPU | Xorg CPU (delta) | Compositor CPU (delta) | RSS | Startup |
|---|---|---|---|---|---|
| Chrysanth (direct) | | | | | |
| shadow, `-m root` | | | | | |
| shadow, `-m background` | | | | | |
-->

---

<div align="center">

</> with <3 by [akai_hana](https://github.com/akai-hana)

</div>
