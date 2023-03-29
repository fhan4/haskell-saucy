#!/bin/bash

#DBNAME=$1
#DIR=$2
PEXORSEED=$1

# start merkleeyes
#./merkleeyes/build/pkg/linux_amd64/merkleeyes start --address "unix:///root/data.sock" --dbName $DBNAME 2>&1 | tee /root/.tendermint/merkleeyes.log & 

#if [ $PEXORSEED == "pex" ] ; then
#	# start tendermint with pex 
#	echo "Starting tendermint seed node (" $DBNAME ")"
#	/bin/tendermint node --proxy_app "unix:///root/data.sock" --log_level="*:debug" 2>&1 | tee /root/.tendermint/tendermint.log &
#    tail -f /root/.tendermint/tendermint.log
if [ $PEXORSEED != "" ] ; then
	# this node gets some peers
	/bin/tendermint node --proxy_app "unix:///root/data.sock" --p2p.seeds "$PEXORSEED" --log_level="*:debug"  2>&1 | tee /root/.tendermint/tendermint.log &
    tail -f /root/.tendermint/tendermint.log
else 
	# this node gets some peers
	/bin/tendermint node --proxy_app "unix:///root/data.sock" --log_level="*:debug" 2>&1 | tee /root/.tendermint/tendermint.log &
    tail -f /root/.tendermint/tendermint.log
fi	

