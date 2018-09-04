#!/usr/bin/env bash
make clean; make

if ! [ -x ./test.d.byte ]
then
    echo 'test not found!'
    echo 'Run `make Test.d.byte` first.'
    exit 1
fi

lsof -ti:9001 | xargs kill
lsof -ti:9002 | xargs kill
lsof -ti:9003 | xargs kill

(./test.d.byte -nodes 127.0.0.1 9001 127.0.0.1 9002 & ) >node1.log 2>&1

(./test.d.byte -nodes 127.0.0.1 9002 127.0.0.1 9003 & ) >node2.log 2>&1

./test.d.byte -nodes 127.0.0.1 9003| tee node3.log 2>&1