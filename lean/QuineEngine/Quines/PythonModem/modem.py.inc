# this program plays its own source as a 300-baud modem (bell 103), with miniaudio
import array, math, miniaudio, time

def feed(b):
    # the device asks for n frames (of 2 bytes) at a time; after the end, it gets silence
    n = yield b''
    while True:
        n = yield b[:2 * n]
        b = b[2 * n:]

def play(t):
    # 8n1 frames, least significant bit first, after 1 s of mark tone and before 0.5 s of it;
    # a mark (1) is 1270 hz and a space (0) is 1070 hz, 160 samples a bit at 48000 samples/s
    bits = [1] * 300
    for c in t.encode():
        bits += [0] + [c >> i & 1 for i in range(8)] + [1]
    bits += [1] * 150
    s = array.array('h')
    p = 0.0
    for b in bits:
        w = 2 * math.pi * (1270 if b else 1070) / 48000
        for i in range(160):
            s.append(int(12000 * math.sin(p)))
            p = (p + w) % (2 * math.pi)
    with miniaudio.PlaybackDevice(nchannels=1, sample_rate=48000) as out:
        f = feed(memoryview(s.tobytes()))
        next(f)
        out.start(f)
        time.sleep(len(s) / 48000 + 0.5)

