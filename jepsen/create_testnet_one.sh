#!/bin/bash

TENDERMINT=/home/surya/Downloads/tendermint
NODES=$1

rm -rf ./nodedirs
mkdir -p ./nodedirs
eval $TENDERMINT testnet --dir "./nodedirs" --n 1


for (( i=1; i<$NODES; i++ ))
do
	mkdir ./nodedirs/mach$i
	cp ./nodedirs/mach0/genesis.json ./nodedirs/mach$i/genesis.json
done

for i in ./nodedirs/*; do cp config.toml $i/config.toml; done

mv ./nodedirs/mach0/priv_validator.json $i/priv_validator.json
