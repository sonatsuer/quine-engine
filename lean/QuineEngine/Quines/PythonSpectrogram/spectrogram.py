v="""# the spectrogram of the sound of this program is its qr code; it plays it, or with -w writes a wav
import array,math,sys
def qr(t):
 # version 40, level l, byte mode, mask 0; 1 is dark
 n=177;m=[[0]*n for _ in range(n)];f=[[0]*n for _ in range(n)]
 def p(y,x,c):
  if 0<=y<n and 0<=x<n:m[y][x]=c;f[y][x]=1
 def q(y,x,h,w):
  for i in range(-h,h+1):
   for j in range(-h,h+1):p(y+i,x+j,w>>max(abs(i),abs(j))&1)
 for y,x in(3,3),(3,n-4),(n-4,3):q(y,x,4,11)
 a=6,30,58,86,114,142,170
 for y in a:
  for x in a:
   if not f[y][x]:q(y,x,2,5)
 for i in range(8,n-8):p(6,i,~i&1);p(i,6,~i&1)
 p(n-8,8,1)
 for i in range(15):c=30660>>i&1;p(i+(i>5)if i<8 else 8,8 if i<8 else 7 if i==8 else 14-i,c);p(8 if i<8 else n-15+i,n-1-i if i<8 else 8,c)
 for i in range(18):c=167017>>i&1;p(i//3,n-11+i%3,c);p(n-11+i%3,i//3,c)
 # mode 4, a 16-bit count, the bytes, a terminator, pad bytes
 d=list(bytes.fromhex('4%04x'%len(t)+t.encode().hex()+'0'))
 if len(d)>2956:raise ValueError('too long')
 d+=[236,17]*1478
 # reed-solomon: 30 codewords for each of 19 blocks of 118 bytes and 6 of 119
 e=[1]*512
 for i in range(1,512):e[i]=e[i-1]*2^(e[i-1]>127)*285
 l={e[i]:i for i in range(255)};u=lambda a,b:a and b and e[l[a]+l[b]];g=[1]
 for i in range(30):g=[a^u(b,e[i])for a,b in zip(g+[0],[0]+g)]
 b=[];k=0
 for i in range(25):
  s=d[k:k+118+(i>18)];k+=len(s);r=[0]*30
  for c in s:r=[a^u(h,c^r[0])for a,h in zip(r[1:]+[0],g[1:])]
  b+=(s,r),
 o=[s[i]for i in range(119)for s,r in b if i<len(s)]+[r[i]for i in range(30)for s,r in b];k=0
 for z in[*range(n-1,6,-2),5,3,1]:
  for v in range(n):
   y=v if(z+1)%4>1 else n-1-v
   for x in z,z-1:
    if not f[y][x]:m[y][x]=o[k>>3]>>7-k%8&1^(x+y+1)%2;k+=1
 return m
def play(t):
 # 185 x 185 modules with the quiet zone; a light one sounds: column x is 0.2 s, row y is
 # 9700-50*y-5 and +5 hz, with 20 ms ramps where a row turns on and off
 m=qr(t);g=lambda y,x:0<=x<185 and not(3<x<181 and 3<y<181 and m[y-4][x-4]);u=[math.sin(math.pi/2*min(1,i/960))**2 for i in range(9600)];e=[0,u,u[::-1],[a*b for a,b in zip(u,u[::-1])]];s=[]
 w=[array.array('d',[math.sin(math.pi*((9695-y*50)*i/24000+y*y/185))+math.sin(math.pi*((9705-y*50)*i/24000+y*y/92))for i in range(9600)])for y in range(185)]
 for x in range(185):s+=map(sum,zip(*[map(float.__mul__,w[y],e[k])if(k:=(not g(y,x-1))+2*(not g(y,x+1)))else w[y]for y in range(185)if g(y,x)]))
 k=16000/max(map(abs,s));a=array.array('h',[round(v*k)for v in s]).tobytes()
 if sys.argv[1:]==['-w']:
  import wave
  with wave.open(sys.stdout.buffer,'wb')as f:f.setnchannels(1);f.setsampwidth(2);f.setframerate(48000);f.writeframes(a)
 else:
  import miniaudio,time
  def f(b):
   n=yield b''
   while 1:n=yield b[:2*n];b=b[2*n:]
  with miniaudio.PlaybackDevice(nchannels=1,sample_rate=48000)as o:s=f(memoryview(a));next(s);o.start(s);time.sleep(len(a)/96000+.5)
play('v='+chr(34)+chr(34)+chr(34)+v+chr(34)+chr(34)+chr(34)+';exec(v)'+chr(10))""";exec(v)
