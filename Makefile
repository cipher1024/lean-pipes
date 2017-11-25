
.PHONY: all clean lines

LEAN_OPT =

all:
	leanpkg build

clean:
	/usr/bin/find . -name "*.olean" -delete
	rm -rf _target

lines:
	wc `git ls-files | grep .lean`
