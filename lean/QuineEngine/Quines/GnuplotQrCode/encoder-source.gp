n=177
l=strlen(s)
T=""
do for [i=32:126] {T=T.sprintf("%c",i)}
X(a)=(a*2)^((a>>7)*285)
G(a,b)=b==0?0:((b&1)*a)^G(X(a),b>>1)
array m[n*n]
array f[n*n]
do for [i=1:n*n] {m[i]=0;f[i]=0}
S="if(y>=0&&y<n&&x>=0&&x<n){m[y*n+x+1]=c;f[y*n+x+1]=1}"
F="do for [i=-h:h] {do for [j=-h:h] {y=Y+i;x=Z+j;c=(w>>(abs(i)>abs(j)?abs(i):abs(j)))&1;eval S}}"
h=4;w=11;Y=3;Z=3;eval F;Z=n-4;eval F;Y=n-4;Z=3;eval F
array A[7]=[6,30,58,86,114,142,170]
h=2;w=5
do for [p=1:7] {do for [q=1:7] {Y=A[p];Z=A[q];if(f[Y*n+Z+1]==0){eval F}}}
do for [i=8:n-9] {c=(i+1)%2;y=6;x=i;eval S;y=i;x=6;eval S}
y=n-8;x=8;c=1;eval S
do for [i=0:14] {c=(30660>>i)&1;y=i<8?(i>5?i+1:i):8;x=i<8?8:(i==8?7:14-i);eval S;y=i<8?8:n-15+i;x=i<8?n-1-i:8;eval S}
do for [i=0:17] {c=(167017>>i)&1;y=int(i/3);x=n-11+i%3;eval S;x=int(i/3);y=n-11+i%3;eval S}
D=2956
if(l>D-3){exit status 1}
N(k)=k==0?4:k<=4?(l>>(16-4*k))&15:k<=4+2*l?((strstrt(T,s[int((k-5)/2)+1:int((k-5)/2)+1])+31)>>(((k-5)%2)==0?4:0))&15:0
array d[D]
do for [i=0:l+2] {d[i+1]=N(2*i)*16+N(2*i+1)}
c=236
do for [i=l+3:D-1] {d[i+1]=c;c=c^253}
E=30
array R[E]
do for [j=1:E] {R[j]=j==E?1:0}
r=1
do for [i=1:E] {do for [j=1:E] {R[j]=G(R[j],r)^(j<E?R[j+1]:0)};r=G(r,2)}
array K[25*149]
k=0
do for [i=0:24] {g=i<19?118:119;array e[E];do for [u=1:E] {e[u]=0};do for [t=0:g-1] {K[i*149+t+1]=d[k+t+1];q=e[1]^d[k+t+1];do for [u=1:E-1] {e[u]=e[u+1]};e[E]=0;do for [u=1:E] {e[u]=e[u]^G(R[u],q)}};if(g==118){K[i*149+119]=0};do for [u=1:E] {K[i*149+119+u]=e[u]};k=k+g}
array o[3706]
k=0
do for [i=0:148] {do for [j=0:24] {if(i!=118||j>=19){k=k+1;o[k]=K[j*149+i+1]}}}
k=0
C="do for [v0=0:n-1] {do for [c0=0:1] {x=x0-c0;y=((x0+1)%4>1)?v0:n-1-v0;if(f[y*n+x+1]==0){m[y*n+x+1]=(k<29648?(o[int(k/8)+1]>>(7-k%8))&1:0)^((x+y+1)%2);k=k+1}}}"
do for [x0=n-1:7:-2] {eval C}
do for [x0=5:1:-2] {eval C}
set print $M
do for [y=0:n-1] {r="";do for [x=1:n] {r=r.sprintf(" %d",1-m[y*n+x])};print r}
unset print
unset key;unset tics;unset border;unset colorbox
set palette gray
set size ratio -1
set lmargin at screen 0;set rmargin at screen 1;set tmargin at screen 1;set bmargin at screen 0
set xrange [-4.5:n+3.5];set yrange [n+3.5:-4.5]
plot $M matrix with image pixels
