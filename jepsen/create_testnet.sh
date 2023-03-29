#!/bin/bash

TENDERMINT=/home/surya/Downloads/tendermint
NODES=$1

rm -rf ./nodedirs
mkdir -p ./nodedirs
eval $TENDERMINT testnet --dir "./nodedirs" --n $NODES
for i in ./nodedirs/*; do cp ./config.toml $i; done
