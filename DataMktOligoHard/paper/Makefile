# This file must be run with GNU make
# Example invocations:
# make
# make VENUE=ijcai once

INAME = main
ONAME = data-mkt-oligo-hard
OUT_DIR = build
TEX_OPTIONS = -cnf-line "max_print_line = 10000" -halt-on-error
ZIP_EXCLUDES = -x '.*' -x '*.db' -x '__MACOSX'

VENUE_SUFFIX = $(if $(VENUE),-$(VENUE))
BUILD_PREFIX = $(if $(OUT_DIR),$(OUT_DIR)/)
AUX_BASE = $(BUILD_PREFIX)$(ONAME)$(VENUE_SUFFIX)
INTERACTION = $(if $(SILENT),batchmode,nonstopmode)
ISPEC = $(if $(COLOR),"\def\colorscheme{$(COLOR)}\input{$(INAME)$(VENUE_SUFFIX).tex}",$(INAME)$(VENUE_SUFFIX).tex)
TEX_RUN = pdflatex $(TEX_OPTIONS) -jobname=$(ONAME)$(VENUE_SUFFIX) -interaction=$(INTERACTION) $(if $(OUT_DIR),-output-directory=$(OUT_DIR) )$(ISPEC)
BIB_RUN = bibtex $(if $(SILENT),-terse )$(AUX_BASE).aux

default:
	$(if $(OUT_DIR),mkdir -p $(OUT_DIR))
	# $(TEX_RUN)
	# $(BIB_RUN)
	$(TEX_RUN)
	$(TEX_RUN)
	# $(TEX_RUN)
once:
	$(if $(OUT_DIR),mkdir -p $(OUT_DIR))
	$(TEX_RUN)
bib:
	$(BIB_RUN)

clean:
	rm -f $(BUILD_PREFIX)*.{aux,bbl,blg,log,out,toc,vtc,cut}
