#!/bin/bash

echo -e ""
echo "  Building Compiler"
echo "====================================="
echo -e -n ""

make -C JOOSA-src
rm -f PeepholeBenchmarks/bench*/*.*dump

COUNT=0
COUNT_COMPILED=0

for BENCH_DIR in PeepholeBenchmarks/*/
do
	((COUNT++))

	BENCH=$(basename $BENCH_DIR)
	echo -e ""
	echo "  Generating Bytecode for '$BENCH'"
	echo "====================================="
	echo -e -n ""

	echo -e -n ""
	echo "  Normal"
	echo "----------------"
	echo -e -n ""

	PEEPDIR=`pwd` make -s --no-print-directory -C $BENCH_DIR clean

	PEEPDIR=`pwd` make -s --no-print-directory -C $BENCH_DIR

	if [ $? != 0 ]
	then
		echo
		echo -e "Error: Unable to compile benchmark '$BENCH'"
		continue
	fi

	echo -e ""
	echo "  Optimized"
	echo "----------------"
	echo -e -n ""

	PEEPDIR=`pwd` make -s --no-print-directory -C $BENCH_DIR opt

	if [ $? != 0 ]
	then
		echo
		echo -e "Error: Unable to optimize benchmark '$BENCH'"
		continue
	fi

	echo -e ""
	echo "  Execution"
	echo "----------------"
	echo -e -n ""

	RESULT=$(PEEPDIR=`pwd` make -s --no-print-directory -C $BENCH_DIR run)
	EXPECTED=$(cat $BENCH_DIR/out1)

	if [[ "$RESULT" == "$EXPECTED" ]]
	then
		echo -e "Execution Successful"
	else
		echo $EXPECTED
		echo
		echo $RESULT
		echo -e "Execution Failed"
		continue
	fi

	echo -e ""
	echo "  Bytecode Size"
	echo "----------------"
	echo -e -n ""

	NORMAL=$(grep -a code_length $BENCH_DIR*.dump | awk '{sum += $3} END {print sum}')
	OPT=$(grep -a code_length $BENCH_DIR*.optdump | awk '{sum += $3} END {print sum}')

	if [[ -z "$NORMAL" || -z "$OPT" ]]
	then
		echo -e "Error: Unable to load bytecode statistics"
		continue
	fi

	((COUNT_COMPILED++))

	echo -e "Normal: $NORMAL"
	echo -e "Optimized: $OPT"
done

echo -e ""
echo "  Overall Bytecode Size"
echo "====================================="
echo -e -n ""

if [ $COUNT == $COUNT_COMPILED ]
then
	echo -e "Successfully compiled all benchmarks"
else
	echo -e "Error: Compiled $COUNT_COMPILED/$COUNT benchmarks"
	exit 1
fi
echo

NORMAL=$(grep -a code_length PeepholeBenchmarks/bench*/*.dump | awk '{sum += $3} END {print sum}')
OPT=$(grep -a code_length PeepholeBenchmarks/bench*/*.optdump | awk '{sum += $3} END {print sum}')

if [[ -z "$NORMAL" || -z "$OPT" ]]
then
	echo -e "Error: Unable to load bytecode statistics"
	exit
fi

echo -e "Normal: $NORMAL"
echo -e "Optimized: $OPT"
