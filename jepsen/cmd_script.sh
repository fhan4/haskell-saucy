#!/bin/bash

DBNAME=$1
#DIR=$2
SEED=$2

# start merkleeyes
./merkleeyes/build/pkg/linux_amd64/merkleeyes start --address "unix:///root/data.sock" --dbName $DBNAME 2>&1 | tee /root/.tendermint/merkleeyes.log &

if [ $SEED != "" ] ; then
	# start tendermint with pex 
	echo "Starting tendermint seed node (" $DBNAME ")\n" > /root/.tendermint/tendermint.log
	echo "/bin/tendermint node --proxy_app 'unix:///root/data.sock' --p2p.pex --p2p.seeds '$SEED' --log_level='*:debug' 2>&1 | tee /root/.tendermint/tendermint.log &\n" > /root/.tendermint/tendermint.log
	/bin/tendermint node --proxy_app "unix:///root/data.sock" --p2p.pex --p2p.seeds "$SEED" --log_level="*:debug" 2>&1 | tee /root/.tendermint/tendermint.log &
    tail -f /root/.tendermint/tendermint.log
else
	# this node gets some peers
	echo "Starting regular tendermint node with a seed (" $DBNAME ")" > /root/.tendermint/tendermint.log
	echo "/bin/tendermint node --proxy_app 'unix:///root/data.sock' --p2p.pex --log_level='*:debug'  2>&1 | tee /root/.tendermint/tendermint.log &" > /root/.tendermint/tendermint.log
	/bin/tendermint node --proxy_app "unix:///root/data.sock" --p2p.pex --log_level="*:debug"  2>&1 | tee /root/.tendermint/tendermint.log &
    tail -f /root/.tendermint/tendermint.log
fi	

