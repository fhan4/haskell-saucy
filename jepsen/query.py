import requests
import enc
import sys
import json

base_url = 'http://172.19.0.{}:46657/'
cast_sync = 'broadcast_tx_sync?tx={}'
cast_async = 'broadcast_tx_async?tx={}'
tx_template = "tx?hash={}"

def set_tx(k,v,node):
    s = enc.create_set(k,v)
    get_url = (base_url.format(node)) + (cast_async.format('0x'+s))
    r = requests.get(get_url)
    print(r)
    return r

def get_tx(k,node):
    s = enc.create_get(k)
    get_url = (base_url.format(node)) + (cast_async.format('0x'+s))
    return requests.get(get_url)

def cas_tx(k,c,v,node):
    s = enc.create_cas(k,c,v)
    get_url = (base_url.format(node)) + (cast_async.format('0x'+s))
    return requests.get(get_url)

def tx_hash(resp):
    d = json.loads(resp.text)
    return d["result"]["hash"]

def txinfo(h,node):
    get_url = (base_url.format(node)) + (tx_template.format('0x'+h))
    print(get_url)
    return requests.get(get_url)

if __name__ == "__main__":
    cmd = sys.argv[1]
    node = sys.argv[2]
    if cmd == 'get':
        k = sys.argv[3]
        print(tx_hash(get_tx(k,node)))
    elif cmd == 'set':
        k = sys.argv[3]
        v = sys.argv[4]
        print(tx_hash(set_tx(k,v,node)))
    elif cmd == 'cas':
        k = sys.argv[3]
        c = sys.argv[4]
        v = sys.argv[5] 
        print(tx_hash(cas_tx(k,c,v,node)))
    elif cmd == 'txinfo':
        h = sys.argv[3]
        print(txinfo(h,node).text)
