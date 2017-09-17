 #!/usr/bin/python

import time
import os
import sys
import re
import json
from collections import namedtuple, defaultdict

import pyaig
from pyaig import AIG

from pyabc import split


class archive(object):

    def __init__(self):

        self.data = bytearray()
        self.space = ''

        self.put('serialization::archive')
        self.put(5)
        self.put(0)
        self.put(0)


    def put(self, x):

        if type(x) == int:
            self.data.extend('%s%d'%(self.space, x))
            self.space = ' '

        elif type(x) == str:
            self.data.extend('%s%d '%(self.space, len(x)))
            self.data.extend(x)
            self.space = ''
        
        else:
            assert False, 'bad boost::serialize type'


class message(object):

    ABORT = 5
    TEXT = 999996
    START = 999999
    PARAMETERS = 2
    
    SEND_NETLIST = 1
    RECV_NETLIST = 106

    ABC_RESULT = 101
    ABC_PROGRESS = 3
    
    BIP_RESULT = 111
    BIP_PROGRESS = 6

    JSON = 123456

    def __init__(self):
        self.data = bytearray()

    def putu32(self, x):
        self.data.append( x & 0xFF )
        self.data.append( (x >> 8) & 0xFF )
        self.data.append( (x >> 16) & 0xFF )
        self.data.append( (x >> 24) & 0xFF )

    def putu(self, x):
        while x >= 0x80:
            self.data.append( x&0x7F | 0x80 )
            x >>= 7
        self.data.append(x)

    def put_str(self, s):
        self.data.extend(s)

    def put_archive(self, x):
        self.data.extend(x.data)

    def put_aig(self, aig):
        self.data.extend(pyaig.marshal_aiger(aig))

class received_message(object):

    def __init__(self, data):
        self.data = bytearray(data)
        self.pos = 0

    def get_next(self):
        if self.pos >= len(self.data):
            raise RuntimeError("error parsing message")
        c = self.data[self.pos]
        self.pos += 1
        return c

    def getc(self):
        return int(self.get_next())

    def consume(self, c):
        assert self.getc() == c

    def get_remaining(self):
        return str(self.data[self.pos:])

    def getu32(self):
        x = 0
        for i in xrange(4):
            x |= self.get_next() << (i * 8)
        return x

    def get_vec_bool(self):
        n = self.getu()
        values = [ self.getc() for i in xrange(n) ]
        return values

    def get_vec_bool_as_cex(self):
        V = {0: '0', 1:'0', 2:'0', 3:'1'}
        return "".join( V[v] for v in self.get_vec_bool() )

    def get_cex(self):

        cex = [ None ]

        concrete = self.getu()
        frames = self.getu()

        for i in xrange(frames):
            cex.append( self.get_vec_bool_as_cex() )
        
        self.consume(1)
        cex[0] = self.get_vec_bool_as_cex()

        return cex

    def getu(self):
        x = 0
        shift = 0
        while True:
            c = self.get_next()
            x |= ( c & 0x7F ) << shift
            shift += 7
            if c < 0x80:
                return x


class par_client_handler(split.base_redirect_handler):

    HEADER_TYPE_LEN = 6
    HEADER_SIZE_LEN = 16
    HEADER_LEN = HEADER_TYPE_LEN + 1 +HEADER_SIZE_LEN + 1

    HEADER_REGEX = re.compile(r'^(\d{%d}) (\d{%d}) $'%(HEADER_TYPE_LEN, HEADER_SIZE_LEN))

    def __init__(self, loop, f):

        super(par_client_handler, self).__init__(loop, f)
        
        self.header = ""
        self.type = None
        self.size = None
        self.content = ""
        self.buffer = ""

    def on_start(self):
        print "ENGINE STARTED"

    def on_message(self, ptype, pcontent):
        print 'RECEIVED MESSAGE type: ', ptype, ', content: "%s"'%pcontent.replace('\n', '\\n')

    def send_message(self, ptype, pcontent):

        self.write_stdin("%06u %016u "%(ptype, len(pcontent)))
        self.write_stdin(pcontent)

    def on_data(self, fd, data):
        self.buffer += data
        while self.buffer:
            self.parse_messages()

    def parse_messages(self):

        if len(self.header) < par_client_handler.HEADER_LEN:

            n = par_client_handler.HEADER_LEN - len(self.header)
            
            self.header += self.buffer[ : n ]
            assert len(self.header) <= par_client_handler.HEADER_LEN
            self.buffer = self.buffer[ n : ]
                
            if len(self.header) == par_client_handler.HEADER_LEN:
                m = par_client_handler.HEADER_REGEX.match(self.header)
                if not m:
                    raise RuntimeError("Message Error")
                    self.kill()
                self.type = int(m.group(1))
                self.size = int(m.group(2))

        if self.buffer and ( self.size is None or self.type is None):
            raise RuntimeError('message error %s - %s - %s'%(str(self.buffer), str(self.size), str(self.type)))

        if self.buffer and len(self.content) <= self.size:

            n = self.size - len(self.content)

            self.content += self.buffer[ : n ]
            assert len(self.content) <= self.size

            self.buffer = self.buffer[ n : ]

            if len(self.content) == self.size:

                self.on_message(self.type, self.content)
                self.header = ""
                self.type = None
                self.size =  None
                self.content = ''


class par_engine(par_client_handler):

    ABC_PROGRESS_REGEX = re.compile(r'^property: (safe)<(\d+)>$')
    BUF_FREE_DEPTH_REGEX = re.compile(r'^bug-free-depth: (\d+)$')

    bug_free_depth = namedtuple("bug_free_depth", ["engine", "prop_no", "depth"])
    property_result = namedtuple("property_result", ["engine", "prop_no", "result", "depth", "cex"])
    json_result = namedtuple("json_result", ["engine", "json"])

    start_result = namedtuple("start_result", ["engine"])
    abort_result = namedtuple("abort_result", ["engine", "reason"])

    def __init__(self, loop, name, f):
        super(par_engine, self).__init__(loop, f)
        self.name = name

    def on_message(self, ptype, pcontent):

        if ptype == message.TEXT:
            return

        m = received_message(pcontent)

        if ptype == message.ABORT:
            self.on_abort( m.get_remaining() )

        elif ptype == message.BIP_PROGRESS:
          
            prop_no = m.getu32()
            prop_type = m.getu32()
            text = m.get_remaining()
            self.on_progress(prop_no, prop_type, text)

        elif ptype == message.ABC_PROGRESS:
          
            lines = m.get_remaining().split('\n')
            m = par_engine.ABC_PROGRESS_REGEX.match(lines[0])
            if m:
                prop_no = int(m.group(2))
                prop_type = 1 if m.group(1) == 'safe' else -1
                self.on_progress(prop_no, prop_type, '\n'.join(lines[1:]))

        elif ptype == message.ABC_RESULT:

            result = m.getc()
            m.consume(1)
            prop_no = m.getu()

            if result == 0:
                self.on_result_unknown(prop_no);

            elif result == 2:
                cex = [ None ]
                m.consume(1)
                depth = m.getu()
                cex = m.get_cex()
                self.on_result_cex(prop_no, depth, cex);

            elif result == 3:
                assert m.getc() == 0
                self.on_result_holds(prop_no);

        elif ptype == message.BIP_RESULT:

            result = m.getc()
            prop_no = m.getu32()
            prop_type = m.getu32()
            loop_frame = m.getu32()

            if result == 0:
                self.on_result_unknown(prop_no);

            elif result == 2:
                cex = m.get_cex()
                self.on_result_cex(prop_no, len(cex)-2, cex);

            elif result == 3:
                self.on_result_holds(prop_no);

        elif ptype == message.JSON:

            self.on_result_json( json.loads( m.get_remaining() ) )

    def on_start(self):
        # print "STARTED(%s)"%(self.name)
        self.loop.add_result( (self.token, False, par_engine.start_result(self.name)) )

    def on_abort(self, reason):
        # print "ABORT(%s): %s"%(self.name, reason)
        self.loop.add_result( (self.token, False, par_engine.abort_result(self.name, reason)) )

    def on_result_json(self, data):
        # print 'RESULT(%s): JSON ", data
        self.loop.add_result( (self.token, False, par_engine.json_result(self.name, data)) )

    def on_result_cex(self, prop_no, depth, cex):
        # print 'RESULT(%s): CEX prop=%d, depth=%d'%(self.name, prop_no, depth), cex
        self.loop.add_result( (self.token, False, par_engine.property_result(self.name, prop_no, "failed", depth, cex)) )

    def on_result_unknown(self, prop_no):
        # print 'RESULT(%s): prop=%d, UNKNOWN'%(self.name, prop_no)
        self.loop.add_result( (self.token, False, par_engine.property_result(self.name, prop_no, "unknown", None, None)) )

    def on_result_holds(self, prop_no):
        # print 'RESULT(%s): prop=%d, HOLDS'%(self.name, prop_no)
        self.loop.add_result( (self.token, False, par_engine.property_result(self.name, prop_no, "proved", None, None)) )

    def on_bug_free_depth(self, prop_no, depth):
        # print 'PROGRESS(%s): prop=%d, bug-free-depth=%d'%(self.name, prop_no, depth)
        self.loop.add_result( (self.token, False, par_engine.bug_free_depth(self.name, prop_no, depth)) )

    def on_progress(self, prop_no, prop_type, progress):
        # print 'PROGRESS(%s): prop=%d, type=%d, progress="%s"'%(self.name, prop_no, prop_type, progress.replace('\n', r'\n'))
        for line in progress.split('\n'):
            m = par_engine.BUF_FREE_DEPTH_REGEX.match(line)
            if m:
                self.on_bug_free_depth( prop_no, int(m.group(1)) )

    def send_message(self, ptype, m):
        super(par_engine, self).send_message(ptype, m.data)

    def send_start_message(self, log_path="", replay_path="", verbosity=0, capture_stderr=False):

        m = message()

        a = archive()

        a.put(1)
        a.put(log_path)
        a.put(replay_path)
        a.put(int(verbosity))
        a.put(int(capture_stderr))

        m.put_archive(a)

        self.send_message(999999, m)

    def send_netlist_message(self, aig):

        m = message()
        m.put_aig(aig)
        self.send_message(message.SEND_NETLIST, m)

    def send_param_message(self, s=''):

        m = message()
        m.put_str(s)
        self.send_message(message.PARAMETERS, m)


class executable_engine(par_engine):

    def __init__(self, loop, N, name, args):

        def exec_callback():
            os.execvp(args[0], args)
            return -1

        super(executable_engine, self).__init__(loop, name, exec_callback)
        self.N = N

    def on_start(self):
        super(executable_engine, self).on_start()

        self.send_start_message()
        self.send_netlist_message(self.N)
        self.send_param_message()


class forked_engine(par_engine):

    def __init__(self, loop, name, f):
        super(forked_engine, self).__init__(loop, name, f)


def send_message(ptype, pcontent, fout=sys.stdout):
    fout.write("%06u %016u "%(ptype, len(pcontent)))
    fout.write(pcontent)
    fout.flush()


def send_progress(prop_no, prop_type, depth, fout=sys.stdout):

    m = message()

    m.putu32(prop_no)
    m.putu32(prop_type)
    m.put_str('bug-free-depth: %d\n'%depth)

    send_message(message.BIP_PROGRESS, m.data, fout)


def send_json(data, fout=sys.stdout):

    m = message()
    m.put_str(json.dumps(data) )
    m.put_str( '\n' )

    send_message(message.JSON, m.data, fout)


make_splitter = split.make_splitter


if __name__=='__main__' :

    def f():

        try:

            for i in xrange(3):
                time.sleep(0.1)
                send_progress(0, 1, i)

            send_json( { "abc" : 3333 } )

            time.sleep(0.1)

        except:
            import traceback
            traceback.print_exc(file=sys.stderr)
            raise

        return 10


    def build(n):

        aig = AIG()
        w = aig.create_pi()

        for i in xrange(n):
            w = aig.create_latch(next=w)

        po = aig.create_po(w, po_type=AIG.BAD_STATES)

        return aig


    def run_par(engines, aig):

        bug_free_depth = defaultdict(lambda : -1)

        with make_splitter() as s:

            timer_uid = s.add_timer(1)

            for name, args in engines:
                s.fork_handler( executable_engine(s.loop, aig, name, args) )
            s.fork_handler( forked_engine(s.loop, "xxx", f) )

            for uid, res in s:
                
                print uid, res

                if uid == timer_uid:
                    print "TIMEOUT"
                    break

                if type(res) == par_engine.bug_free_depth:
                    print res
                    if bug_free_depth[res.prop_no] < res.depth:
                        print 'u%d'%res.depth
                        bug_free_depth[res.prop_no] = res.depth

                if type(res) == par_engine.property_result:
                    print res
                    break

                if type(res) == int:
                    print "RES: ", res
                    print os.WIFEXITED(res), os.WIFSIGNALED(res), os.WEXITSTATUS(res)


    engines = [
        ( 'pdr', ['abc', '-b', '-c', '&st; &put; pdr ; send_status'] ),
        ( 'bmc3', ['abc', '-b', '-c', '&st; &put; bmc3 -a'] ),
        ( ',bmc', ['bip', ',bmc', '-no-logo', '@@'] ),
        ( ',treb', ['bip', '-no-logo', ',treb', '@@'] ),
        ( ',treb -abs', ['bip', '-no-logo', ',treb', '-abs', '@@'] ),
    ]

    aig = build(150)
    # aig.write_aiger('xxx.aig')
    # aig = pyzz.netlist.read_aiger('../../build/single/prodcellp2neg.aig')
    # aig = pyzz.netlist.read_aiger('../../build/single/ndista128.aig')

    run_par(engines, aig)
