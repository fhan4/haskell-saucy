#!/usr/bin/env bash
DOCKER_BUILDKIT=0
if [ ! -f ./secret/authorized_keys ]; then
	mkdir -p secret 
	cp ~/.ssh/id_rsa.pub ./secret/authorized_keys
fi

docker build -t tendermint/merkleeyes .

