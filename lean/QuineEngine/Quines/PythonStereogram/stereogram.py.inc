# a stereogram quine: stereogram.pdf hides this source, 3 x 8 raised characters a page,
# after a title page
import random,zlib
k='abcdefghijklmnopqrstuvwxyz0123456789 ' + chr(10) + '()[]{}<>=+-*/%&^.,:;' + chr(39) + chr(34) + '#!'
g={k[i]:int('03cf03f800f30c3f01f301c302fb03cc0c33007ca1c000f030cc90cc00ff03c780ff83c7123b0c0300fc0078c0ccf0003800603360ff200c0377023f038c03bb03fb000f03ff03bf0000ffffa000500000d1002e0d220e11a100520003300f000300ff00600060a99551c0000020400002204200040004800f0c0024'[4*i:4*i+4],16)for i in range(len(k))}
def u(s):p=s.split('^');return p[0]+''.join(q[:1].upper()+q[1:]for q in p[1:])
def m(t,o):
 z=[bytearray(1660)for y in range(900)];a=0,26,57,70,83,114,140;e=0,26,97,123,194,220
 for j,h in enumerate(t):
  i=o+j;x=36+j%8*200+i*37%49;y=28+j//8*300+i*23%25
  for b in range(16):
   if g[h]>>b&1:
    d=[int(v)for v in '0031306150635265043534650215001302333263204322451100510014005400'[4*b:4*b+4]]
    if b<12:
     for w in range(y+e[d[1]],y+e[d[3]]):z[w][x+a[d[0]]:x+a[d[2]]]=bytes([1])*(a[d[2]]-a[d[0]])
    else:
     p,q=a[d[0]]-70,e[d[1]]-110
     for w in range(-110,110):
      for v in range(-70,70):
       f=max(0,min(1,(v*p+w*q)/(p*p+q*q)))
       if(v-f*p)**2+(w-f*q)**2<170:z[y+110+w][x+70+v]=1
 return z
def s(z,o):
 c={};n=bytearray();random.seed(o)
 for y in range(1000):
  r=bytes(120)+(z[y-50]if 49<y<950 else bytes(1660))+bytes(120)
  if r not in c:
   l=list(range(1900))
   for x in range(1900):
    a=x-70+14*r[x];b=a+140-28*r[x]
    if a<0 or b>1899 or r[x]<1 and 1 in r[x-15:x+16]:continue
    k=l[a]
    while k!=a and k!=b:
     if k>b:l[a]=b;a,b=b,k
     else:a=k
     k=l[a]
    l[a]=b
   c[r]=l
  l=c[r];w=bytearray(random.randbytes(1900))
  for x in range(1899,-1,-1):w[x]=w[l[x]]
  if 14<y<36:
   for x in range(1900):w[x]*=min((x-880)**2,(x-1020)**2)+(y-25)**2>100
  n+=w
 return n
def draw(t):
 j=chr(10);random.seed(0);d=u('^b^t/f 120 ^tf 369 332 ^td(^i am a ^quine)^tj ^e^t');o=[u('<</^type/^catalog/^pages 2 0 ^r>>'),'',u('[/^indexed/^device^r^g^b 255<')+(bytes(3)+random.randbytes(765)).hex()+'>]',u('<</^type/^font/^subtype/^type1/^base^font/^helvetica>>'),u('<</^type/^page/^parent 2 0 ^r/^media^box[0 0 1425 750]/^resources<</^font<</f 4 0 ^r>>>>/^contents 6 0 ^r>>'),u('<</^length %d>>stream')%len(d)+j+d+j+'endstream'];q=[u('5 0 ^r')]
 for p in range(0,len(t),24):
  i=zlib.compress(s(m(t[p:p+24],p),p));n=len(o)+1;q+=[str(n)+u(' 0 ^r')];d='q 1425 0 0 750 0 0 cm/i '+u('^do ^q')
  o+=[u('<</^type/^page/^parent 2 0 ^r/^media^box[0 0 1425 750]/^resources<</^x^object<</i %d 0 ^r>>>>/^contents %d 0 ^r>>')%(n+2,n+1),u('<</^length %d>>stream')%len(d)+j+d+j+'endstream',u('<</^type/^x^object/^subtype/^image/^width 1900/^height 1000/^color^space 3 0 ^r/^bits^per^component 8/^filter/^flate^decode/^length %d>>stream')%len(i)+j+i.decode('latin1')+j+'endstream']
 o[1]=u('<</^type/^pages/^kids[%s]/^count %d>>')%(' '.join(q),len(q));f=u('%^p^d^f-1.4')+j;a=[]
 for i,x in enumerate(o):a+=[len(f)];f+='%d 0 obj'%(i+1)+j+x+j+'endobj'+j
 f+='xref'+j+'0 %d'%(len(o)+1)+j+'0000000000 65535 f '+j+''.join('%010d 00000 n '%x+j for x in a)+u('trailer<</^size %d/^root 1 0 ^r>>')%(len(o)+1)+j+'startxref'+j+str(len(f))+j+u('%%^e^o^f')+j
 open('stereogram.pdf','wb').write(f.encode('latin1'))

