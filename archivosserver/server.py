import random
from Crypto.Hash import SHA512
from Crypto.Protocol.KDF import PBKDF2
from Crypto.Hash import SHA512
from Crypto.Random import get_random_bytes
import math
from Crypto.Hash import SHAKE256
from Crypto.Hash import HMAC, SHA256
from Crypto.Cipher import AES
import json
import socket


server=socket.socket()

server.bind(('localhost',8000))
server.listen(5)

ID_q='Usuario2'

f = open("archivoprotegidoserver.txt", "r")
BD=json.loads(f.read())
print(BD)
def recuperarpi(id):
    if id in BD.keys():
       return BD[id][0]
    else:
       raise ValueError('Error con id')

def recuperarU1(id):
    if id in BD.keys():
       return BD[id][1]
    else:
       raise ValueError('Error con id')


while True:
    (conexion,addr)=server.accept()
    print( "Nueva conexion establecida")
    print(addr)
    conexion.send(b"Bienvenido al server")
    conexion.close()
