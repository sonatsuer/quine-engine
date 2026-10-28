v="""'this program blinks its own source in morse code, in a window'
import tkinter

k='abcdefghijklmnopqrstuvwxyz0123456789.,?!/()&:;=+-_$@'+chr(34)+chr(39)+chr(10)+' '
c='.- -... -.-. -.. . ..-. --. .... .. .--- -.- .-.. -- -. --- .--. --.- .-. ... - ..- ...- .-- -..- -.-- --.. ----- .---- ..--- ...-- ....- ..... -.... --... ---.. ----. .-.-.- --..-- ..--.. -.-.-- -..-. -.--. -.--.- .-... ---... -.-.-. -...- .-.-. -....- ..--.- ...-..- .--.-. .-..-. .----. .-.-'
m=dict(zip(k,c.split()+''.split(',')))

def blink(t):
    'a dot is 60 ms of light; the gaps are 60 ms in a letter, 180 ms between letters, 420 ms'
    'between words; the message starts with ka and ends with sk'
    e=list()
    for w in ('-.-.-',)+tuple(map(m.get,t))+('...-.-',):
        for x in w:
            e.append((1,60 if x=='.' else 180))
            e.append((0,60))
        e.append((0,120 if w else 240))
    r=getattr(tkinter,'tk'.capitalize())()
    r.title('morse')
    r.geometry('300x300')
    r.configure(bg='black')
    i=iter(e)
    def step():
        x=next(i,0)
        if not x:
            r.destroy()
            return
        a,b=x
        r.configure(bg='white' if a else 'black')
        r.after(b,step)
    r.after(2000,step)
    r.mainloop()

blink('v='+chr(34)+chr(34)+chr(34)+v+chr(34)+chr(34)+chr(34)+';exec(v)'+chr(10))""";exec(v)
