#!/bin/bash

#SBATCH -N 2

# Color codes for printing
RED='\033[0;31m'
BLUE='\033[0;34m'
GREEN='\033[0;32m'
CYAN='\033[0;36m'
YELLOW='\033[1;33m'
NOCOLOR='\033[0m'


# What nodes are available to use?
temp=`scontrol show hostname | paste -d, -s`
IFS=',' read -ra nodes <<< "$temp"

printf "${GREEN}\nRunning on nodes:\n\t+${NOCOLOR}"
for node in "${nodes[@]}"
do
    printf "${CYAN} ${node}${NOCOLOR}"
done
printf "\n\n"

INSPECTOR_ON=$1

RESDIR=temp_results

mkdir -p ${RESDIR}
mkdir -p ${RESDIR}/OPT_IS_VALID
mkdir -p ${RESDIR}/OPT_IS_NOT_VALID

valid_test_exes=( $(ls -d bin/OPT_IS_VALID/noOpt_*.exe_valid) )
declare -a VALID_EXES
for i in "${valid_test_exes[@]}"
do
    test_name=`basename "$i" .exe_valid`
    test_name=$(echo ${test_name#*_})
    VALID_EXES=("${VALID_EXES[@]}" ${test_name})
done
invalid_test_exes=( $(ls -d bin/OPT_IS_NOT_VALID/noOpt_*.exe_not_valid) )
declare -a INVALID_EXES
for i in "${invalid_test_exes[@]}"
do
    test_name=`basename "$i" .exe_not_valid`
    test_name=$(echo ${test_name#*_})
    INVALID_EXES=("${INVALID_EXES[@]}" ${test_name})
done

printf "\n${CYAN}####################################################################\n${NOCOLOR}"
printf "\n${CYAN}Checking compiler output for all tests in bin/OPT_IS_VALID\n${NOCOLOR}"
for exe in "${VALID_EXES[@]}"
do
    DIFF=""
    DIFF=$(diff compiler_log/OPT_IS_VALID/${exe}.exe* latest_good_results/compiler_log_sherlock/OPT_IS_VALID/${exe}.exe*)
    if [ "$DIFF" != "" ]
    then
        printf "${RED} ${exe}: FAILED${NOCOLOR}\n"
    else
        printf "${GREEN} ${exe}: PASSED${NOCOLOR}\n"
    fi
done

FAIL=0
printf "\n${CYAN}Running all tests in bin/OPT_IS_VALID\n${NOCOLOR}"
for exe in "${VALID_EXES[@]}"
do
    printf "\n${YELLOW}############## ${exe} ##############${NOCOLOR}\n"
    ./bin/OPT_IS_VALID/${exe}.exe_valid -nl 2 > ${RESDIR}/OPT_IS_VALID/${exe}.output
    ./bin/OPT_IS_VALID/noOpt_${exe}.exe_valid -nl 2 > ${RESDIR}/OPT_IS_VALID/noOpt_${exe}.output
    DIFF=""
    if [ -z "${INSPECTOR_ON}" ]
    then
        DIFF=$(diff ${RESDIR}/OPT_IS_VALID/${exe}.output ${RESDIR}/OPT_IS_VALID/noOpt_${exe}.output)
    else
        DIFF=$(diff ${RESDIR}/OPT_IS_VALID/${exe}.output latest_good_results/OPT_WITH_INSPECTOR-ON_PRINTS/${exe}.output)
    fi
    if [ "$DIFF" != "" ]
    then
        FAIL=1
        if [ -z "${INSPECTOR_ON}" ]
        then
            printf "${RED} FAILED: ${RESDIR}/OPT_IS_VALID/${exe}.output differs from ${RESDIR}/OPT_IS_VALID/noOpt_${exe}.output${NOCOLOR}\n"
        else
            printf "${RED} FAILED: ${RESDIR}/OPT_IS_VALID/${exe}.output differs from latest_good_results/OPT_WITH_INSPECTOR-ON_PRINTS/${exe}.output\n"
        fi
    else
        printf "${GREEN} PASSED${NOCOLOR}\n"
    fi
done

printf "\n${CYAN}####################################################################\n${NOCOLOR}"
printf "\n${CYAN}Checking compiler output for all tests in bin/OPT_IS_NOT_VALID\n${NOCOLOR}"
for exe in "${INVALID_EXES[@]}"
do
    DIFF=""
    DIFF=$(diff compiler_log/OPT_IS_NOT_VALID/${exe}.exe* latest_good_results/compiler_log_sherlock/OPT_IS_NOT_VALID/${exe}.exe*)
    if [ "$DIFF" != "" ]
    then
        printf "${RED} ${exe}: FAILED${NOCOLOR}\n"
    else
        printf "${GREEN} ${exe}: PASSED${NOCOLOR}\n"
    fi
done

printf "\n${CYAN}Running all tests in bin/OPT_IS_NOT_VALID\n${NOCOLOR}"
for exe in "${INVALID_EXES[@]}"
do
    printf "\n${YELLOW}############## ${exe} ##############${NOCOLOR}\n"
    ./bin/OPT_IS_NOT_VALID/${exe}.exe_not_valid -nl 2 > ${RESDIR}/OPT_IS_NOT_VALID/${exe}.output
    ./bin/OPT_IS_NOT_VALID/noOpt_${exe}.exe_not_valid -nl 2 > ${RESDIR}/OPT_IS_NOT_VALID/noOpt_${exe}.output
    DIFF=$(diff ${RESDIR}/OPT_IS_NOT_VALID/${exe}.output ${RESDIR}/OPT_IS_NOT_VALID/noOpt_${exe}.output)
    if [ "$DIFF" != "" ]
    then
        FAIL=1
        printf "${RED} FAILED: ${RESDIR}/OPT_IS_NOT_VALID/${exe}.output differs from ${RESDIR}/OPT_IS_NOT_VALID/noOpt_${exe}.output${NOCOLOR}\n"
    else
        printf "${GREEN} PASSED${NOCOLOR}\n"
    fi
done

if [ "$FAIL" == 1 ]
then
    printf "\n${RED} Some tests failed. Not removing ${RESDIR}${NOCOLOR}\n"
else
    printf "\n${GREEN} All tests passed. Removing ${RESDIR}${NOCOLOR}\n"
    #rm -rf ${RESDIR}
fi

echo ""
printf "${YELLOW}###############################################################\n${NOCOLOR}"
echo ""
