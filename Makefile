CC = clang
CFLAGS = -O3 -flto -Wall -Wextra
LDLIBS = -lX11 -lXrandr -lXext -lGL -lm
PREFIX ?= /usr/local

.PHONY: clean install uninstall

chrysanth: chrysanth.c
	$(CC) $(CFLAGS) -o $@ $< $(LDLIBS)

clean:
	rm -f chrysanth

install: chrysanth
	install -Dm755 chrysanth "$(PREFIX)/bin/chrysanth"

uninstall:
	rm -f "$(PREFIX)/bin/chrysanth"
