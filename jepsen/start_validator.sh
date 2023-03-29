#!/bin/bash

TENDERMINT=/home/surya/Downloads/tendermint
NODES=$1


# This script starts the docker containers and starts all the services in them and connects them together

#mkdir -p ./nodedirs
## create the testnet genesis files here 
#eval $TENDERMINT testnet --dir "./nodedirs" -n $1

# spawn pex container
#echo 'docker run --rm -d --network=jepsen --ip="172.19.0.2" --name="tendermint0" -v "./nodedirs/mach0:/root/.tendermint" tendermint/merkleeyes:latest "jepsen2" "pex"'
#docker run --rm -d --network=jepsen --ip="172.19.0.2" --name="tendermint0" -v "./nodedirs/mach0:/root/.tendermint" tendermint/merkleeyes:latest "jepsen2" "pex"

# spawn the containers 
#for (( i=3; i<=($NODES+1); i++))
#do
#  docker run --rm -d --network=jepsen --ip="172.19.0.$i" --name="tendermint$i" -v "./nodedirs/mach$(($i-2)):/root/.tendermint" tendermint/merkleeyes:latest "jepsen$(($i-2))" "172.19.0.2:46656"
#done


#SEED="172.19.0.2"
#PEERS="$SEED:46656"

for (( i=1; i<$NODES; i++ ))
do
	PEERS+=("172.19.0.$(($i+2)):46656")
	#PEERS="$PEERS,172.19.0$(($i+2)):46656"
done

echo "Peers:" ${PEERS[@]}
printf -v PEERS "%s," "${PEERS[@]}"
PEERS=${PEERS%,}
echo "Peers:" $PEERS

VALNUM=$(($NODES-1))
IP="172.19.0.$(($VALNUM+2))"
CONTAINER="tendermint$VALNUM"
JEPSEN="jepsen$VALNUM"

echo "docker run --rm -d --network=jepsen --ip=$IP --name=$CONTAINER -v './nodedirs/mach$VALNUM:/root/.tendermint/' tendermint/merkleeyes:latest $JEPSEN '$PEERS'"
docker run --rm -d --network=jepsen --ip=$IP --name=$CONTAINER -v "./nodedirs/mach$VALNUM:/root/.tendermint/" tendermint/merkleeyes:latest $JEPSEN "$PEERS"

#sleep 5
#
#for (( i=1; i<$NODES; i++))
#do
#  # nodes need to start at ip address 172.19.0.2
#  echo "docker run --rm -d --network=jepsen --ip='172.19.0.$(($i+2))' --name='tendermint$i' -v './nodedirs/mach$i:/root/.tendermint' tendermint/merkleeyes:latest 'jepsen$i' '$SEED:46656'"
#  docker run --rm -d --network=jepsen --ip="172.19.0.$(($i+2))" --name="tendermint$i" -v "./nodedirs/mach$i:/root/.tendermint" tendermint/merkleeyes:latest "jepsen$i" "$SEED:46656"
#done 	

#docker run --rm -d --network=jepsen --ip=$VALIDATOR --name="tendermint0" -v "./nodedirs/mach0:/root/.tendermint" tendermint/merkleeyes:latest "jepsen0" "$PEERS"
#
#
#for (( i=1; i<$NODES; i++))
#do
#  # nodes need to start at ip address 172.19.0.3
#  docker run --rm -d --network=jepsen --ip="172.19.0.$(($i+2))" --name="tendermint$i" -v "./nodedirs/mach$i:/root/.tendermint" tendermint/merkleeyes:latest "jepsen$i" "$VALIDATOR:46656"
#done 	

