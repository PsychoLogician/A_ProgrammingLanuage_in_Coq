# Define the Coq source files
# COQ_FILES = BasicDefinitions.v Computation.v Macro.v
COQ_FILES = BasicDefinitions.v Computation.v Macro.v

# Define the LaTeX file that will be generated
LATEX_FILE = output.tex

# Define the PDF file that will be generated
PDF_FILE = output.pdf

# latex packages
LaTeX_PACKAGE1 = \usepackage{mathrsfs}
LaTeX_PACKAGE2 = \usepackage{cite}
LaTeX_PACKAGE3 = \usepackage{xcolor} # not use yet


# Rule to generate the LaTeX file from the Coq source files
$(LATEX_FILE): $(COQ_FILES)
	coqdoc --toc -s --latex $(COQ_FILES) -o $(LATEX_FILE) -p $(LaTeX_PACKAGE1) -p $(LaTeX_PACKAGE2) --no-lib-name


# Rule to generate the PDF file from the LaTeX file
$(PDF_FILE): $(LATEX_FILE)
	pdflatex $(LATEX_FILE)

# Default rule to build the PDF file
all: $(PDF_FILE)

# Clean rule to remove generated files
clean:
	rm -f $(LATEX_FILE) $(PDF_FILE) *.aux *.log *.glob

.PHONY: all clean
