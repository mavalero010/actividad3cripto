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






aexp=random.randint(2,q-1)
A=G.point_multiplication(aexp)
bexp=random.randint(2,q-1)
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


ID_p='Usuario1'

password='mypassword'
salt=get_random_bytes(16)
ID_q='Usuario2'
h= PBKDF2(password+ID_p+ID_q, salt,2*math.ceil(n/8) , count=100000, hmac_hash_module=SHA512)
print(h)


print(len(h))

h1 = h[:32]
h2= h[32:] 
print(h1)
print(h2)
pi0=int.from_bytes(h1,'big')% q
pi1=int.from_bytes(h2,'big')% q
print("pi0: ",pi0)
print("pi1: ",pi1)



U1=G.point_multiplication(pi1) ##pi1⋅𝐺


#Enviando U1, ID_p y pi0

## recibiendo U , ID_p y pi0

BD={ID_p:(pi0,U1)}
print(type(BD))
f =  open("archivoprotegidocliente.txt", "w")
f.write('"%s"' % str(BD))
f.close()

f1=open("../archivosserver/archivoprotegidoserver.txt","w")
f1.write('"%s"' % str(BD))
f1.close()


alpha=random.randint(2,q-1)
U=A.point_multiplication(pi0)+G.point_multiplication(alpha)

cliente = socket.socket()
cliente.connect(('localhost',8000))
print("U: ",U)
cliente.send(b(ID_p))

res = cliente.recv(1024)
print(res)
cliente.close()
