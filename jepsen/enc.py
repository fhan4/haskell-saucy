import os

def l(b):
    s = len(b)
    return s.to_bytes((s.bit_length() + 7)//8, 'big')
def encode(b):
    return (l(l(b)) + l(b) + b.encode('utf-8'))
def hex_encode(b):
    return encode(b).hex()

def new_nonce():
    return os.urandom(12) 

def _create_set(n,k,v):
    return n + b'\x01' + encode(k) + encode(v)
def _create_set_hex(n,k,v):
    return _create_set(n,k,v).hex()
def test_create_set():
    expect = 'F4FCDC5BF26E227B66A1BA90010104657269630107636C6170746F6E'
    nonce =  'F4FCDC5BF26E227B66A1BA90'
    assert len(nonce) == 24
    got = _create_set_hex(bytes.fromhex(nonce), 'eric', 'clapton').upper() 
    return got == expect

def _create_get(n,k):
    return n + b'\x03' + encode(k)
def _create_get_hex(n,k):
    return _create_get(n,k).hex()
def test_create_get():
    expect = 'B980403FF73E79A3A2D90A1E03010465726963'.upper()
    nonce = 'B980403FF73E79A3A2D90A1E'.upper()
    assert len(nonce) == 24
    got = _create_get_hex(bytes.fromhex(nonce), 'eric').upper()
    return got == expect

def _create_cas(n,k,c,v):
    return n + b'\x04' + encode(k) + encode(c) + encode(v)
def _create_cas_hex(n,k,c,v):
    return _create_cas(n,k,c,v).hex()
def test_create_cas():
    expect = '18D892B6D62773E6AA8804CF040104657269630107636C6170746F6E010765726963736f6e'.upper()
    nonce = '18D892B6D62773E6AA8804CF'.upper()
    assert len(nonce) == 24
    got = _create_cas_hex(bytes.fromhex(nonce), 'eric', 'clapton', 'ericson').upper()
    return got == expect

def create_set(k,v):
    return _create_set_hex(new_nonce(), k, v)
def create_get(k):
    return _create_get_hex(new_nonce(), k)
def create_cas(k,c,v):
    return _create_cas_hex(new_nonce(), k, c, v)

