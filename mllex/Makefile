# Makefile for ML-Lex
# $Id: Makefile.in,v 1.1 2007/11/16 04:36:19 kiyoshiy Exp $

srcdir = .
builddir = .
top_srcdir = .
top_builddir = .

include ./commonrule

VPATH = .

TARGETS = smllex

SOURCES = lexgen.sml main.sml call-main.sml

all: $(TARGETS)

install: $(TARGETS)
	$(INSTALL) -d -m 755 '$(DESTDIR)$(bindir)'
	$(MAKESML) -B '$(DESTDIR)$(bindir)' -H '$(DESTDIR)$(heapdir)' \
	           -i -o smllex

clean:
	-rm -rf $(srcdir)/.cm $(srcdir)/CM
	$(MAKESML) -r -o smllex

smllex: sources.cm $(SOURCES)
	$(MAKESML) -o $@ $(srcdir)/sources.cm

# Makefile.in ends here.
