#!/bin/bash
TX=$1
curl "http://127.0.0.1:46657/tx?hash=$TX"
