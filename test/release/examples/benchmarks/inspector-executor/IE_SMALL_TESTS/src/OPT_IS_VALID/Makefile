CHPL_FLAGS += --fast --optimize-irregular-array-accesses --report-irregular-array-access

INPUT = $(wildcard ./*.chpl)
OUTPUT = $(patsubst ./%.chpl,%.exe_valid,$(INPUT))

all: ${OUTPUT}

%.exe_valid: ./%.chpl
	mkdir -p ../../bin
	mkdir -p ../../bin/OPT_IS_VALID
	mkdir -p ../../compiler_log
	mkdir -p ../../compiler_log/OPT_IS_VALID
	chpl ${CHPL_FLAGS} $< -o ../../bin/OPT_IS_VALID/$@ &> ../../compiler_log/OPT_IS_VALID/$@.log
	chpl --fast $< -o ../../bin/OPT_IS_VALID/noOpt_$@
