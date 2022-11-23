import random
from Crypto.Hash import SHA512
from Crypto.Protocol.KDF import PBKDF2
from Crypto.Hash import SHA512
from Crypto.Random import get_random_bytes
import math
from Crypto.Hash import SHAKE256
from Crypto.Hash import HMAC, SHA256
from Crypto.Cipher import AES
import socket
import json
server=socket.socket()
server1=socket.socket()
server2=socket.socket()
server3=socket.socket()

class FP:

   def __init__(self,rep, p):
          self.p=p
          self.rep=(rep %p)

   def __add__(self, b):
          rep=(self.rep + b.rep)%self.p
          return FP(rep,self.p)

   def __sub__(self, b):
          rep=(self.rep - b.rep)%self.p
          return FP(rep,self.p)

   def get_random_element(self):
           rep=int(random.randint(0,self.p-1))
           return FP(rep,self.p)

   def get_zero(self):
           return FP(0,self.p)

   def get_one(self):
           return FP(1,self.p)

   def get_minus_one(self):
           return FP(self.p-1,self.p)
        
   def get_random_nonzero_element(self):
           element=random.randint(1,self.p-1)
           return FP(element,self.p)
  
   def __pow__(self, n):  
          return FP(pow(self.rep,n,self.p), self.p)
   
   def get_square(self):
        g=self.get_random_nonzero_element()
        one=self.get_one()
        output=g**((self.p-1)//2)
        while not output.equals(one):
            g=self.get_random_nonzero_element()
            output=g**((self.p-1)//2)

        return g

   def get_nonsquare(self):
        g=self.get_random_nonzero_element()
        one=self.get_one()
        output=g**((self.p-1)//2)
        while  output.equals(one):
            g=self.get_random_nonzero_element()
            output=g**((self.p-1)//2)
        return g
   def __truediv__(self,y):
        return self*y.m_inverse()
       
   def get_order(self):
          return self.p    
   
   def get_primitive_root(self):
          
          if self.p==17:
             g=self.get_random_nonzero_element()
            
             g8=g**8
             
             while g8.rep ==1 : 
               g=self.get_random_nonzero_element()
               g8=g**8
             gi=g**15
          
             return g,gi
   def a_inverse(self):
       zero=self.get_zero() 
       return zero-self

   def m_inverse(self):

       def egcd( a, b):
          if a == 0:
             return (b, 0, 1)
          g, y, x = egcd(b%a,a)
          return (g, x - (b//a) * y, y)
  
       def modinv(a, m):
          g, x, y = egcd(a, m)
          if g != 1:
             raise Exception('No modular inverse')
          return x%m

       return FP(modinv(self.rep, self.p),self.p)
        
   def __mul__(self, b):
          rep=(self.rep*b.rep)%self.p
          
          return FP(rep,self.p)
      
   def equals(self,a):
        if isinstance(a, self.__class__): 
            return self.rep==a.rep and  self.p==a.p
        return False
   def __eq__(self, other):
         return self.equals(other)

   def __str__(self):        
         return str(self.rep)

   def is_one(self):
           return self.rep==1

   def is_nonzero(self):
           return self.rep!=0


p=41
a=FP(30,p)
b=FP(20,p)

print(a==b)


class ECPoint:

    def __init__(self,a,b,x=None,y=None):
        self.x=x
        self.y=y
        self.a=a
        self.b=b

    def is_identity(self):
        return  self.x==None and self.y==None

    def equals(self, Q):
        
        if isinstance(Q, self.__class__):
           if self.is_identity() and Q.is_identity():
              return True
           else:
              if self.is_identity():
                 return False
              else:
                 if Q.is_identity():
                   return False
                 else:
                   return self.x==Q.x and self.y == Q.y and self.a==Q.a and self.b==Q.b
        return False

    def __eq__(self, other):
         return self.equals(other)

    def __add__(self, Q):
        if Q.is_identity(): 
           return self;
        

        if self.is_identity():
           return Q;
        

        if not self.x==Q.x:
           s = self.y-Q.y
           s =s/ (self.x-Q.x);
           x =(s*s-self.x)-Q.x     
           y = s*(self.x-x)-self.y
           return ECPoint(self.a,self.b,x, y)

            
        else:
           if self.y==Q.y:
              if P.y.rep == 0:
                return ECPoint(self.a,self.b)
              
              three = FP(3,self.a.p)
              two = FP(2,self.a.p)
              s = three * (self.x ** 2)
              s = s+ self.a
              s = s/(two*self.y)
              x =(s*s-self.x)-Q.x 
              y = s*(self.x-x)-self.y
              return ECPoint(self.a,self.b,x, y)
            
           else:
              return ECPoint(self.a,self.b)
                 
    def inverse(self):
        if self.is_identity():
          return ECPoint(self.a,self.b)
        else:
          return ECPoint(self.a,self.b,self.x,self.y.a_inverse())
       
        
    def double(self):

        if  self.is_identity():
            return ECPoint(self.a,self.b)
        
        if  self.y.rep==0:
            return ECPoint(self.a,self.b)
        
      
        three = FP(3,self.a.p);
        two = FP(2,self.a.p);
        s = three * (self.x ** 2);
        s = s+self.a
        s = s/ (two *self.y)

        x =(s*s-self.x)-self.x 
        y = s *(self.x-x)-self.y

        return ECPoint(self.a,self.b,x, y)
  
    def __sub__(self, P):
          
          return self+P.inverse()


    def point_multiplication(self, n):
        
        if n<0:
          n1=-n
          P=self.inverse()
        else:
          n1=n
          P=self
        
        T = ECPoint(self.a,self.b) ;
        
        for k in range(n1.bit_length() - 1,-1,-1):
            T = T.double()

            if (n1>>k)&1:
                T = T + P
            
        return T
    def to_bytes(self):
        pp=self.x.p
        cx=self.x.rep
        cy=self.y.rep
        lt=(pp.bit_length()+7)//8
        return cx.to_bytes(lt, byteorder='big')+cy.to_bytes(lt, byteorder='big')
    
    @staticmethod
    def point_from_bytes(a,b,f_array):
      
        lt=(a.p.bit_length()+7)//8
        if len(f_array)==2*lt:
            x=FP(int.from_bytes( f_array[:lt], byteorder='big'),a.p)
            y=FP(int.from_bytes( f_array[lt:], byteorder='big'),a.p)
            return ECPoint(a,b,x=x,y=y)
        else:
           raise RuntimeError("Array length is not expected")

    def __str__(self): 
         if self.is_identity():
            return "I"       
         return '('+str(self.x.rep)+','+str(self.y.rep)+')'


      
    

p=29
a=FP(4,p)
b=FP(20,p)

#c=FP(5,p)

#print(c.a_inverse())


#(1,24)
#(1,5)
## y^2=x^3+4x+20=1+4+20=25 
##5*5=25
##

## F29={0,1,2,..., 28}


I=ECPoint(a,b)

P=ECPoint(a,b,FP(1,p),FP(5,p)) 

print(P)

#print(P+P)
#print(P-P)



R=I+P
i=1
points=[]
points.append(R)
print(i,R)
while not R.is_identity():
   R=R+P 
   i=i+1
   print(i,R)
   points.append(R)
   

#j=random.randint(0,i)

#QQ=P.point_multiplication(j)



#print(QQ.equals(points[j-1]))
#<G> <= E(Fp)


p= 2**256 - 2**224 + 2**192 + 2**96 - 1

#Fp



a=FP(-3,p)



b=FP(41058363725152142129326129780047268409114441015993725554835256314039467401291,p)



x=FP(48439561293906451759052585252797914202762949526041747995844080717082404635286,p)


y=FP(36134250956749795798585127919587881956611106672985015071877198253568414405109,p)

#2^256 - 2^224 + 2^192 - 89188191075325690597107910205041859247

q=2**256 - 2**224 + 2**192 - 89188191075325690597107910205041859247 

print('p',p)
print('a',a)
print('b',b)

G=ECPoint(a,b, x,y)

print(G)
#print(G+G)
print(G.point_multiplication(q)) # qG=G+G+G+....+G



n=math.log(q, 2)






f = open("aexp.txt", "r")
aexp=int(f.read())
print("aexp: ",aexp)

A=G.point_multiplication(aexp)
f = open("bexp.txt", "r")
bexp=int(f.read())
print("bexp: ",bexp)
B=G.point_multiplication(bexp)



def H1(pi0, U, V, W,d, n=32):
    
    h_256 = SHAKE256.new()
    p0="funcion1"
    rep= bytes(p0, 'utf-8')
    h_256.update(rep)
    
    h_256.update(pi0.to_bytes(32,'big'))

    h_256.update(U.to_bytes())
    h_256.update(V.to_bytes())
    h_256.update(W.to_bytes())
    h_256.update(d.to_bytes())

    return h_256.read(n)

def H2(k, n=32):
    
    h_256 = SHAKE256.new()
    p0="funcion2"
    
    h_256.update(k)

    return h_256.read(n)

def H3(k, n=32):
    
    h_256 = SHAKE256.new()
    p0="funcion3"
    
    h_256.update(k)

    return h_256.read(n)

def H4(k, n=44):
    
    h_256 = SHAKE256.new()
    p0="funcion4"
    
    h_256.update(k)

    return h_256.read(n)

def H5(ida, idb, ra, rb,k, n=76):
    
    h_256 = SHAKE256.new()
    p0="funcion5"
    rep= bytes(p0, 'utf-8')
    h_256.update(rep)
    
    h_256.update(ida)

    h_256.update(idb)
    h_256.update(ra)
    h_256.update(rb)
    h_256.update(k)

    return h_256.read(n)

f = open("archivoprotegidocliente.txt", "r")
BD=json.loads(f.read())
BD=json.loads((BD.replace("'",'"')))

def recuperarpi(id):
    if id in BD.keys():
       return int(BD[id].split("(")[1].split(",")[0])
    else:
       raise ValueError('Error con id')
def recuperarU1(id):
    if id in BD.keys():
       return int(BD[id].replace("'","").replace("(","").replace(")","").split(",")[2])
    else:
       raise ValueError('Error con id')

ID_p='Usuario1'

password='mypassword'
f = open("salt.txt", "r")
salt=bytes(f.read(), 'utf-8')
print("salt: ",salt)

ID_q='Usuario2'
h= PBKDF2(password+ID_p+ID_q, salt,2*math.ceil(n/8) , count=100000, hmac_hash_module=SHA512)
print(h)


print(len(h))
"""
h1 = h[:32]
h2= h[32:] 
print(h1)
print(h2)
pi0=int.from_bytes(h1,'big')% q
pi1=int.from_bytes(h2,'big')% q
print("pi0: ",pi0)
print("pi1: ",pi1)
"""
pi0=recuperarpi(ID_p)
print("G: ",G)
pi1=recuperarU1(ID_p)
U1=G.point_multiplication(pi1) ##pi1⋅𝐺

print("U1: ",U1)


alpha=random.randint(2,q-1)
U=A.point_multiplication(pi0)+G.point_multiplication(alpha)

def rec_V_IDq():
    server.bind(('localhost',8001))
    server.listen(5)
    
    contV=False
    contID=False
    while (contV == False & contID == False):
        try:
            (client,addr)=server.accept()
            res = client.recv(1024)       
            print("res: ",res)    
            if (res!=b'Usuario2'): 
                print("diferente Usuario2")
                Vx=res[0]
                Vy=res[1]
                print("VX",(Vx))
                print("VY: ",(Vy))
                v=ECPoint(Vx,Vy)
                V=v.point_from_bytes(a,b,res)
                print("V: ",V)

                contV=True
                client.close()
            else:
                print("Usuario2")
                ID_q=res.decode('UTF-8')
                contID=True
        except:

            print("Except")

    return [V,ID_q]
"""
def sendCtoActualizationOfIP(ce):
    contador=0
    while (contador<5):
        try:
            contador+=1 
            print("sending c to server for actualization of IP, please wait")
            clienteCIP = socket.socket()       
            print("connect")   
            clienteCIP.connect(('localhost',9005))
            print("post connect")
            conter=0
            
            while(conter<20):
                try:      
                    print("Send pre")
                    clienteCIP.send(ce)
                    print("Send post")
                    conter=conter+1
                    clienteCIP.close()
                    print("try padre")
                except (EnvironmentError): 
                    print("expect hijo")          
                    conter=conter+1
        except:
            print("expect padre")
            contador+=1 
            continue
"""
def sendCtoserver(c):
    con=0
    while (con<5):
        try:
            con+=1 
            print("sending c to server, please wait")
            clienteC = socket.socket()          
            clienteC.connect(('localhost',9001))
            cont=0
            
            while (cont<5):
                    try:      
                        clienteC.send(c)
                        cont=cont+1
                        clienteC.close()
                    except (EnvironmentError):           
                       cont=cont+1
        except:
            con+=1 
            continue
def send_U_ID(U,ID_p):
    cont=0
    while (cont<2): 
        try:
            cont=cont+1
            print("cont: ",cont)
            clienteU = socket.socket()
         
            clienteIDP=socket.socket()
          
            clienteIDP.connect(('localhost',8000))
         
            clienteU.connect(('localhost',8000))
         
            envio=(ID_p,U.to_bytes,str(U))
            
            clienteU.send(U.to_bytes())
            
            clienteIDP.send(bytes(ID_p,'UTF-8'))
         
            #cliente.send(bytes(str(envio), 'utf-8'))
            clienteU.close()
          
            clienteIDP.close()
          
            
        except (EnvironmentError):
            print(EnvironmentError)
            cont=cont+1

def recT2atoserver():
    server1.bind(('localhost',9000))  
    server1.listen(5)
    
    conT2a=False
    while (conT2a == False ):
        try:
            (client,addr)=server1.accept()
            res = client.recv(1024)       
            print("res: ",res)    
            t2a=res
            conT2a=True
            client.close()
           
        except:

            print("Except")

    return res
       
def recRtoserver():
    server2.bind(('localhost',9002))  
    server2.listen(5)
    
    conR=False
    while (conR == False ):
        try:
            (clientR,add)=server2.accept()
            res = clientR.recv(1024)    
            r=res
            conR=True
            clientR.close()
           
        except:

            print("Except")

    return res
       
send_U_ID(U,ID_p)
print("Apunto")
r=rec_V_IDq()
print("ya fue")
V=r[0]
ID_q=r[1]

print("V:", V)
print("ID_q:", ID_q)

y_r= V.y**2
mtres=FP(-3,p)
x_r= V.x**3 + mtres*V.x + b
#if V.is_identity() or !(y_r == x_r): abort

Wc= (V-B.point_multiplication(pi0)).point_multiplication(alpha)
dc= (V-B.point_multiplication(pi0)).point_multiplication(pi1)
print("pi0:",pi0)
print("U:", U)
print("V: ",V)
print("Wc: ",Wc)
print("dc: ",dc)

keycliente=H1(pi0, U, V, Wc,dc, 32)
print(keycliente.hex())

t2a=recT2atoserver()
print("t2a: ",t2a)

t1a=H2(keycliente)
t1b=H3(keycliente)

key=keycliente
f=open('keycliente.txt','w')
f.write('%s'%str(key))
f.close()
print("key: ",type(key))
ñ=H4(key)
sk=ñ[:32]
N=ñ[32:]
print("Ñ: ",ñ)
print(len(ñ))
print("SK: ",sk)
print(len(sk))
print("N: ",N)

cipher = AES.new(sk, AES.MODE_GCM, nonce=N)
data=b"Ipdeprueba"
m= b"registrar:"+data
c=cipher.encrypt(m)

print("sendtoserver")

sendCtoserver(c)
print("c: ",c)
r=recRtoserver()
print("r: ",r)

## Operacion actualizar IP d
cipher = AES.new(sk, AES.MODE_GCM, nonce=N)
data= b"NuevoIPdecliente"
m= b"obtenerIP:"+data
c=cipher.encrypt(m)

#envio de c por parte de cliente al servidor
#sendCtoActualizationOfIP(c)
#print("CIP: ",c)