# Copyright (C) 2010  David Hugh Malcolm
#
# This library is free software; you can redistribute it and/or
# modify it under the terms of the GNU Lesser General Public
# License as published by the Free Software Foundation; either
# version 2.1 of the License, or (at your option) any later version.
#
# This library is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# Lesser General Public License for more details.
#
# You should have received a copy of the GNU Lesser General Public
# License along with this library; if not, write to the Free Software
# Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

import gdb
import re
import sys
import datetime
from collections import namedtuple
import sqlite3
import ply.lex as lex
import ply.yacc as yacc
import tempfile

__type_cache = {}

#from glib import read_global_var, g_quark_to_string

class OldStyle:
    def __init__(self, x, y):
        self.x = x
        self.y = y

class NewStyle(object):
    def __init__(self, x, y):
        self.x = x
        self.y = y

class NewStyleWithSlots(object):
    __slots__ = ('x', 'y')
    def __init__(self, x, y):
        self.x = x
        self.y = y


reserved = ['AND', 'OR', 'NOT']
tokens = [
    'ID','LITERAL_NUMBER', 'LITERAL_STRING',
    'LPAREN','RPAREN',
    'COMPARISON'
    ] + reserved
        
t_LPAREN  = r'\('
t_RPAREN  = r'\)'

def t_ID(t):
    r'[a-zA-Z_][a-zA-Z_0-9]*'
    # Check for reserved words (case insensitive):
    if t.value.upper() in reserved:
        t.type = t.value.upper()
    else:
        t.type = 'ID'
    return t

def t_COMPARISON(t):
    r'<=|<|==|=|!=|>=|>'
    return t

def t_LITERAL_NUMBER(t):
    r'(0x[0-9a-fA-F]+|\d+)'
    try:
        if t.value.startswith('0x'):
            t.value = int(t.value, 16)
        else:
            t.value = int(t.value)
    except(ValueError):
        raise ParserError(t.value)
    return t

def t_LITERAL_STRING(t):
    r'"([^"]*)"'
    # Drop the quotes:
    t.value = t.value[1:-1]
    return t

# Ignored characters
t_ignore = " \t"

def python_categorization(usage_set):
    # special-cased categorization for CPython

    # The Objects/stringobject.c:interned dictionary is typically large,
    # with its PyDictEntry table occuping 200k on a 64-bit build of python 2.6
    # Identify it:
    try:
        val_interned = gdb.parse_and_eval('interned')
        pyop = PyDictObjectPtr.from_pyobject_ptr(val_interned)
        ma_table = int(pyop.field('ma_table'))
        usage_set.set_addr_category(ma_table,
                                    Category('cpython', 'PyDictEntry table', 'interned'),
                                    level=1)
    except(RuntimeError):
        pass

    # Various kinds of per-type optimized allocator
    # See Modules/gcmodule.c:clear_freelists

    # The Objects/intobject.c: block_list
    try:
        val_block_list = gdb.parse_and_eval('block_list')
        if str(val_block_list.type.target()) != 'PyIntBlock':
            raise RuntimeError
        while int(val_block_list) != 0:
            usage_set.set_addr_category(int(val_block_list),
                                        Category('cpython', '_intblock', ''),
                                        level=0)
            val_block_list = val_block_list['next']

    except(RuntimeError):
        pass

    # The Objects/floatobject.c: block_list
    # TODO: how to get at this? multiple vars named "block_list"

    # Objects/methodobject.c: PyCFunction_ClearFreeList
    #   "free_list" of up to 256 PyCFunctionObject, but they're still of
    #   that type

    # Objects/classobject.c: PyMethod_ClearFreeList
    #   "free_list" of up to 256 PyMethodObject, but they're still of that type

    # Objects/frameobject.c: PyFrame_ClearFreeList
    #   "free_list" of up to 300 PyFrameObject, but they're still of that type

    # Objects/tupleobject.c: array of free_list: up to 2000 free tuples of each
    # size from 1-20 (using ob_item[0] to chain up); singleton for size 0; they
    # are still tuples when deallocated, though

    # Objects/unicodeobject.c:
    #   "free_list" of up to 1024 PyUnicodeObject, with the "str" buffer
    #   optionally preserved also for lengths up to 9
    #   They're all still of type "unicode" when free
    #   Singletons for the empty unicode string, and for the first 256 code
    #   points (Latin-1)

# New gdb commands, specific to CPython


def t_newline(t):
    r'\n+'
    t.lexer.lineno += t.value.count("\n")
    
def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)

lexer = lex.lex()


############################################################################
# Grammar:
############################################################################

precedence = (
    ('left', 'AND', 'OR'),
    ('left', 'NOT'),
    ('left', 'COMPARISON'),
)

class Expression(object):
    def eval_(self, u):
        raise NotImplementedError

    def __eq__(self, other):
        return (self.__class__ == other.__class__
                and self.__dict__ == other.__dict__)

class Constant(Expression):
    def __init__(self, value):
        self.value = value

    def __repr__(self):
        return 'Constant(%r)' % (self.value,)

    def eval_(self, u):
        return self.value

class GetAttr(Expression):
    def __init__(self, attrname):
        self.attrname = attrname

    def __repr__(self):
        return 'GetAttr(%r)' % (self.attrname,)

    def eval_(self, u):
        if self.attrname in ('domain', 'kind', 'detail'):
            if u.category == None:
                u.ensure_category()
            return getattr(u.category, self.attrname)
        return getattr(u, self.attrname)

class BinaryOp(Expression):
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

class Comparison(BinaryOp):
    def __init__(self, lhs, rhs):
        BinaryOp.__init__(self, lhs, rhs)

    def __repr__(self):
        return '%s(%r, %r)' % (self.__class__.__name__, self.lhs, self.rhs)

    def eval_(self, u):
        lhs_val = self.lhs.eval_(u)
        rhs_val = self.rhs.eval_(u)
        return self.cmp_(lhs_val, rhs_val)

    def cmp_(self, lhs, rhs):
        raise NotImplementedError

class Comparison__le__(Comparison):
    def cmp_(self, lhs, rhs):
        return lhs <= rhs

class Comparison__lt__(Comparison):
    def cmp_(self, lhs, rhs):
        return lhs <  rhs

class Comparison__eq__(Comparison):
    def cmp_(self, lhs, rhs):
        return lhs == rhs

class Comparison__ne__(Comparison):
    def cmp_(self, lhs, rhs):
        return lhs != rhs

class Comparison__ge__(Comparison):
    def cmp_(self, lhs, rhs):
        return lhs >= rhs

class Comparison__gt__(Comparison):
    def cmp_(self, lhs, rhs):
        return lhs >  rhs


class And(BinaryOp):
    def __repr__(self):
        return 'And(%r, %r)' % (self.lhs, self.rhs)

    def eval_(self, u):
        # Short-circuit evaluation:
        if not self.lhs.eval_(u):
            return False
        return self.rhs.eval_(u)

class Or(BinaryOp):
    def __repr__(self):
        return 'Or(%r, %r)' % (self.lhs, self.rhs)

    def eval_(self, u):
        # Short-circuit evaluation:
        if self.lhs.eval_(u):
            return True
        return self.rhs.eval_(u)

class Not(Expression):
    def __init__(self, inner):
        self.inner = inner
    def __repr__(self):
        return 'Not(%r)' % (self.inner, )
    def eval_(self, u):
        return not self.inner.eval_(u)



class Column(object):
    def __init__(self, name, getter, formatter):
        self.name = name
        self.getter = getter
        self.formatter = formatter


class Query(object):
    def __init__(self, filter_):
        self.filter_ = filter_

    def __iter__(self):

        if True:
            # 2-pass, but the expensive first pass may be cached
            usage_list = lazily_get_usage_list()
            for u in usage_list:
                if self.filter_.eval_(u):
                    yield u
        else:
            # 1-pass:
            # This may miss blocks that are only categorized w.r.t. to other
            # blocks:
            for u in iter_usage_with_progress():
                if self.filter_.eval_(u):
                    yield u

def do_query(args):

    if args == '':
        # if no query supplied, select everything:
        filter_ = Constant(True)
    else:
        filter_ = parse_query(args)

    if False:
        print(args)
        print(filter_)

    columns = [Column('Start',
                      lambda u: u.start,
                      fmt_addr),
               Column('End',
                      lambda u: u.start + u.size - 1,
                      fmt_addr
                      ),
               Column('Domain',
                      lambda u: u.category.domain,
                      None),
               Column('Kind',
                      lambda u: u.category.kind,
                      None),
               Column('Detail',
                      lambda u: u.category.detail,
                      None),
               Column('Hexdump',
                      lambda u: u.hexdump,
                      None),
               ]
               
    t = Table([col.name for col in columns])

    for u in Query(filter_):
        u.ensure_hexdump()
        u.ensure_category()

        if u.category:
            domain = u.category.domain
            kind = u.category.kind
            detail = u.category.detail
            if not detail:
                detail = ''        
        else:
            domain = ''
            kind = ''
            detail = ''

        t.add_row([fmt_addr(u.start),
                   fmt_addr(u.start + u.size - 1),
                   domain,
                   kind,
                   detail,
                   u.hd])

    t.write(sys.stdout)
    print()
 

def p_expression_number(t):
    'expression : LITERAL_NUMBER'
    t[0] = Constant(t[1])

def p_expression_string(t):
    'expression : LITERAL_STRING'
    t[0] = Constant(t[1])

def p_comparison(t):
    'expression : expression COMPARISON expression'
    classes = { '<=' : Comparison__le__,
                '<'  : Comparison__lt__,
                '==' : Comparison__eq__,
                '='  : Comparison__eq__,
                '!=' : Comparison__ne__,
                '>=' : Comparison__ge__,
                '>'  : Comparison__gt__ }
    cls = classes[t[2]]

    t[0] = cls(t[1], t[3])

def p_and(t):
    'expression : expression AND expression'
    t[0] = And(t[1], t[3])

def p_or(t):
    'expression : expression OR expression'
    t[0] = Or(t[1], t[3])

def p_not(t):
    'expression : NOT expression'
    t[0] = Not(t[2])

def p_expression_group(t):
    'expression : LPAREN expression RPAREN'
    t[0] = t[2]

def p_expression_name(t):
    'expression : ID'
    attrname = t[1]
    attrnames = ('domain', 'kind', 'detail', 'addr', 'start', 'size')
    if attrname not in attrnames:
        raise ParserError.from_production(t, attrname,
                                          ('Unknown attribute "%s" (supported are %s)'
                                           % (attrname, ','.join(attrnames))))
    t[0] = GetAttr(attrname)
 
class ParserError(Exception):
    @classmethod
    def from_production(cls, p, val, msg):
        return ParserError(p.lexer.lexdata,
                           p.lexer.lexpos - len(val),
                           val,
                           msg)

    @classmethod
    def from_token(cls, t, msg="Parse error"):
        return ParserError(t.lexer.lexdata,
                           t.lexer.lexpos - len(t.value),
                           t.value,
                           msg)

    def __init__(self, input_, pos, value, msg):
        self.input_ = input_
        self.pos = pos
        self.value = value
        self.msg = msg
    
    def __str__(self):
        return ('%s at "%s":\n%s\n%s'
                % (self.msg, self.value,
                   self.input_,
                   ' '*self.pos + '^'*len(self.value)))

def p_error(t):
    raise ParserError.from_token(t)


############################################################################
# Interface:
############################################################################

# Entry point:
def parse_query(s):
    #try:
    parser = yacc.yacc(debug=0, write_tables=0)
    return parser.parse(s)#, debug=1)
    #except ParserError, e:
    #    print 'foo', e

def test_lexer(s):
    lexer.input(s)
    while True:
        tok = lexer.token()
        if not tok: break
        print(tok)



# Test creating an object with more than 8 attributes, so that the __dict__
# has an external PyDictEntry buffer.
# We will test to see if this detectable in the selftest.
class OldStyleManyAttribs:
    def __init__(self, **kwargs):
        self.__dict__ = kwargs

class NewStyleManyAttribs(object):
    def __init__(self, **kwargs):
        self.__dict__ = kwargs


#typemap = {
#    'GdkColormap':GdkColormapPtr,
#    'GdkImage':GdkImagePtr,
#    'GdkPixbuf':GdkPixbufPtr,
#    'PangoCairoFcFontMap':PangoCairoFcFontMapPtr,
#}

def need_debuginfo(f):
    def g(self, args, from_tty):
        try:
            return f(self, args, from_tty)
        except MissingDebuginfo as e:
            print('Missing debuginfo for %s' % e.module)
            print('Suggested fix:')
            print('    debuginfo-install %s' % e.module)
    return g




class MissingDebuginfo(RuntimeError):
    def __init__(self, module):
        self.module = module

class Usage(object):
    # Information about an in-use area of memory
    slots = ('start', 'size', 'category', 'level', 'hd', 'obj')

    def __init__(self, start, size, category=None, level=None, hd=None, obj=None):
        assert isinstance(start, int)
        assert isinstance(size, int)
        if category:
            assert isinstance(category, Category)
        self.start = start
        self.size = size
        self.category = category
        self.level = level
        self.hd = hd
        self.obj = obj

    def __repr__(self):
        result = 'Usage(%s, %s' % (hex(self.start), hex(self.size))
        if self.category:
            result += ', %r' % (self.category, )
        if self.hd:
            result += ', hd=%r' % self.hd
        if self.obj:
            result += ', obj=%r' % self.obj
        return result + ')'

    def ensure_category(self, usage_set=None):
        if self.category is None:
            self.category = categorize(self, usage_set)

    def ensure_hexdump(self):
        if self.hd is None:
            self.hd = hexdump_as_bytes(self.start, NUM_HEXDUMP_BYTES)

class WrappedValue(object):
    """
    Base class, wrapping an underlying gdb.Value adding various useful methods,
    and allowing subclassing
    """
    def __init__(self, gdbval):
        self._gdbval = gdbval

    # __getattr__ just made it too confusing
    #def __getattr__(self, attr):
    #    return WrappedValue(self.val[attr])

    def field(self, attr):
        return self._gdbval[attr]

    def __str__(self):
        return str(self._gdbval)

    # See http://sourceware.org/gdb/onlinedocs/gdb/Values-From-Inferior.html#Values-From-Inferior
    @property
    def address(self):
        return self._gdbval.address

    @property
    def is_optimized_out(self):
        return self._gdbval.is_optimized_out

    @property
    def type(self):
        return self._gdbval.type

    @property
    def dynamic_type(self):
        return self._gdbval.dynamic_type

    @property
    def is_lazy(self):
        return self._gdbval.is_lazy

    def dereference(self):
        return WrappedValue(self._gdbval.dereference())

#    def address(self):
#        return int(self._gdbval.cast(type_void_ptr))

    def is_null(self):
        return int(self._gdbval) == 0


class WrappedPointer(WrappedValue):
    def as_address(self):
        return int(self._gdbval.cast(type_void_ptr))

    def __str__(self):
        return ('<%s for inferior 0x%x>'
                % (self.__class__.__name__,
                   self.as_address()
                   )
                )

    def cast(self, type_):
        return WrappedPointer(self._gdbval.cast(type_))

    def categorize_refs(self, usage_set, level=0, detail=None):
        '''Hook for categorizing references known by the type this points to'''
        # do nothing by default:
        pass


class Heap(gdb.Command):
    'Print a report on memory usage, by category'
    def __init__(self):
        gdb.Command.__init__ (self,
                              "heap",
                              gdb.COMMAND_DATA,
                              prefix=True)

    @need_debuginfo
    def invoke(self, args, from_tty):
        total_by_category = {}
        count_by_category = {}
        total_size = 0
        total_count = 0
        try:
            usage_list = list(lazily_get_usage_list())
            for u in usage_list:
                u.ensure_category()
                total_size += u.size
                if u.category in total_by_category:
                    total_by_category[u.category] += u.size
                else:
                    total_by_category[u.category] = u.size

                total_count += 1
                if u.category in count_by_category:
                    count_by_category[u.category] += 1
                else:
                    count_by_category[u.category] = 1

        except(KeyboardInterrupt):
            pass # FIXME

        t = Table(['Domain', 'Kind', 'Detail', 'Count', 'Allocated size'])
        for category in sorted(total_by_category.keys(),
                               lambda s1, s2: cmp(total_by_category[s2],
                                                  total_by_category[s1])
                               ):
            detail = category.detail
            if not detail:
                detail = ''
            t.add_row([category.domain,
                       category.kind,
                       detail,
                       fmt_size(count_by_category[category]),
                       fmt_size(total_by_category[category]),
                       ])
        t.add_row(['', '', 'TOTAL', fmt_size(total_count), fmt_size(total_size)])
        t.write(sys.stdout)
        print()

class HeapSizes(gdb.Command):
    'Print a report on memory usage, by sizes'
    def __init__(self):
        gdb.Command.__init__ (self,
                              "heap sizes",
                              gdb.COMMAND_DATA)
    @need_debuginfo
    def invoke(self, args, from_tty):
        ms = glibc_arenas.get_ms()
        chunks_by_size = {}
        num_chunks = 0
        total_size = 0
        try:
            for chunk in ms.iter_chunks():
                if not chunk.is_inuse():
                    continue
                size = int(chunk.chunksize())
                num_chunks += 1
                total_size += size
                if size in chunks_by_size:
                    chunks_by_size[size] += 1
                else:
                    chunks_by_size[size] = 1
        except(KeyboardInterrupt):
            pass # FIXME
        t = Table(['Chunk size', 'Num chunks', 'Allocated size'])
        for size in sorted(chunks_by_size.keys(),
                           lambda s1, s2: chunks_by_size[s2] * s2 - chunks_by_size[s1] * s1):
            t.add_row([fmt_size(size),
                       chunks_by_size[size],
                       fmt_size(chunks_by_size[size] * size)])
        t.add_row(['TOTALS', num_chunks, fmt_size(total_size)])
        t.write(sys.stdout)
        print()


class HeapUsed(gdb.Command):
    'Print used heap chunks'
    def __init__(self):
        gdb.Command.__init__ (self,
                              "heap used",
                              gdb.COMMAND_DATA)

    @need_debuginfo
    def invoke(self, args, from_tty):
        print('Used chunks of memory on heap')
        print('-----------------------------')
        ms = glibc_arenas.get_ms()
        for i, chunk in enumerate(ms.iter_chunks()):
            if not chunk.is_inuse():
                continue
            size = chunk.chunksize()
            mem = chunk.as_mem()
            u = Usage(mem, size)
            category = categorize(u, None)
            hd = hexdump_as_bytes(mem, 32)
            print ('%6i: %s -> %s %8i bytes %20s |%s'
                   % (i,
                      fmt_addr(chunk.as_mem()),
                      fmt_addr(chunk.as_mem()+size-1),
                      size, category, hd))
        print()

class HeapFree(gdb.Command):
    'Print free heap chunks'
    def __init__(self):
        gdb.Command.__init__ (self,
                              "heap free",
                              gdb.COMMAND_DATA)

    @need_debuginfo
    def invoke(self, args, from_tty):
        print('Free chunks of memory on heap')
        print('-----------------------------')
        ms = glibc_arenas.get_ms()
        total_size = 0
        for i, chunk in enumerate(ms.iter_free_chunks()):
            size = chunk.chunksize()
            total_size += size
            mem = chunk.as_mem()
            u = Usage(mem, size)
            category = categorize(u, None)
            hd = hexdump_as_bytes(mem, 32)

            print ('%6i: %s -> %s %8i bytes %20s |%s'
                   % (i,
                      fmt_addr(chunk.as_mem()),
                      fmt_addr(chunk.as_mem()+size-1),
                      size, category, hd))

        print("Total size: %s" % total_size)


class HeapAll(gdb.Command):
    'Print all heap chunks'
    def __init__(self):
        gdb.Command.__init__ (self,
                              "heap all",
                              gdb.COMMAND_DATA)

    @need_debuginfo
    def invoke(self, args, from_tty):

        print('All chunks of memory on heap (both used and free)')
        print('-------------------------------------------------')
        arenas = glibc_arenas.arenas #get_arenas()
        # print arenas
        # gdb.parse_and_eval("&main_arena")
        for arena in arenas:
            if arena.address == gdb.parse_and_eval("&main_arena"):
                print(arena.address)
                ms = arena
                for i, chunk in enumerate(ms.iter_chunks()):
                    size = chunk.chunksize()
                    if chunk.is_inuse():
                        kind = ' inuse'
                    else:
                        kind = ' free'

                    print ('%i: %s -> %s %s: %i bytes (%s)'
                          % (i,
                             fmt_addr(chunk.as_address()),
                             fmt_addr(chunk.as_address()+size-1),
                             kind, size, chunk))

            else:
                print(arena.address)
                ms = arena
                for i, chunk in enumerate(ms.iter_sbrk_chunks_not_main()):
                    size = chunk.chunksize()
                    if chunk.is_inuse():
                        kind = ' inuse'
                    else:
                        kind = ' free'

                    print ('%i: %s -> %s %s: %i bytes (%s)'
                          % (i,
                             fmt_addr(chunk.as_address()),
                             fmt_addr(chunk.as_address()+size-1),
                             kind, size, chunk))
#                    print
#        ms = glibc_arenas.get_ms()
#        for i, chunk in enumerate(ms.iter_chunks()):
#            size = chunk.chunksize()
#            if chunk.is_inuse():
#                kind = ' inuse'
#            else:
#                kind = ' free'
#
#            print ('%i: %s -> %s %s: %i bytes (%s)'
#                   % (i,
#                      fmt_addr(chunk.as_address()),
#                      fmt_addr(chunk.as_address()+size-1),
#                      kind, size, chunk))
#        print

class HeapLog(gdb.Command):
    'Print a log of recorded heap states'
    def __init__(self):
        gdb.Command.__init__ (self,
                              "heap log",
                              gdb.COMMAND_DATA)

    @need_debuginfo
    def invoke(self, args, from_tty):
        h = history
        if len(h.snapshots) == 0:
            print('(no history)')
            return
        for i in range(len(h.snapshots), 0, -1):
            s = h.snapshots[i-1]
            print('Label %i "%s" at %s' % (i, s.name, s.time))
            print('    ', s.summary())
            if i > 1:
                prev = h.snapshots[i-2]
                d = Diff(prev, s)
                print()
                print('    ', d.stats())
            print()

class HeapLabel(gdb.Command):
    'Record the current state of the heap for later comparison'
    def __init__(self):
        gdb.Command.__init__ (self,
                              "heap label",
                              gdb.COMMAND_DATA)

    @need_debuginfo
    def invoke(self, args, from_tty):
        s = history.add(args)
        print(s.summary())


class HeapDiff(gdb.Command):
    'Compare two states of the heap'
    def __init__(self):
        gdb.Command.__init__ (self,
                              "heap diff",
                              gdb.COMMAND_DATA)

    @need_debuginfo
    def invoke(self, args, from_tty):
        h = history
        if len(h.snapshots) == 0:
            print('(no history)')
            return
        prev = h.snapshots[-1]
        curr = Snapshot.current('current')
        d = Diff(prev, curr)
        print('Changes from %s to %s' % (prev.name, curr.name))
        print('  ', d.stats())
        print()
        print('\n'.join(['  ' + line for line in d.as_changes().splitlines()]))

class HeapSelect(gdb.Command):
    'Query used heap chunks'
    def __init__(self):
        gdb.Command.__init__ (self,
                              "heap select",
                              gdb.COMMAND_DATA)

    @need_debuginfo
    def invoke(self, args, from_tty):
#        from heap.query import do_query
#        from heap.parser import ParserError
        try:
            do_query(args)
        except ParserError as e:
            print(e)

class Hexdump(gdb.Command):
    'Print a hexdump, starting at the specific region of memory'
    def __init__(self):
        gdb.Command.__init__ (self,
                              "hexdump",
                              gdb.COMMAND_DATA)

    def invoke(self, args, from_tty):
        print(repr(args))
        arg_list = gdb.string_to_argv(args)

        chars_only = True

        if len(arg_list) == 2:
            addr_arg = arg_list[0]
            chars_only = True if args[1] == '-c' else False
        else:
            addr_arg = args

        if addr_arg.startswith('0x'):
            addr = int(addr_arg, 16)
        else:
            addr = int(addr_arg)

        # assume that paging will cut in and the user will quit at some point:
        size = 32
        while True:
            hd = hexdump_as_bytes(addr, size, chars_only=chars_only)
            print ('%s -> %s %s' % (fmt_addr(addr), fmt_addr(addr + size -1), hd))
            addr += size

class HeapArenas(gdb.Command):
    'Display heap arenas available'
    def __init__(self):
        gdb.Command.__init__ (self,
                              "heap arenas",
                              gdb.COMMAND_DATA)

    @need_debuginfo
    def invoke(self, args, from_tty):
        for n, arena in enumerate(glibc_arenas.arenas):
            print("Arena #%d: %s" % (n, arena.address))

class HeapArenaSelect(gdb.Command):
    'Select heap arena'
    def __init__(self):
        gdb.Command.__init__ (self,
                              "heap arena",
                              gdb.COMMAND_DATA)

    @need_debuginfo
    def invoke(self, args, from_tty):
        arena_num = int(args)

        glibc_arenas.cur_arena = glibc_arenas.arenas[arena_num]
        print("Arena set to %s" % glibc_arenas.cur_arena.address)

class HeapActivate(gdb.Command):
    'Activate heap pluggin'
    def __init__(self):
        gdb.Command.__init__(self,
                             "heap activate",
                             gdb.COMMAND_DATA)

    @need_debuginfo
    def invoke(self, args, from_tty):
        global type_void_ptr, type_char_ptr, type_unsigned_char_ptr, sizeof_ptr, format_string
        glibc_arenas.activate()
        type_void_ptr = gdb.lookup_type('void').pointer()
        type_char_ptr = gdb.lookup_type('char').pointer()
        type_unsigned_char_ptr = gdb.lookup_type('unsigned char').pointer()
        sizeof_ptr = type_void_ptr.sizeof

        if sizeof_ptr == 4:
            format_string = '0x%08x'
        else:
            format_string = '0x%016x'


class Snapshot(object):
    '''Snapshot of the state of the heap'''
    def __init__(self, name, time):
        self.name = name
        self.time = time
        self._all_usage = set()
        self._totalsize = 0
        self._num_usage = 0

    def _add_usage(self, u):
        self._all_usage.add(u)
        self._totalsize += u.size
        self._num_usage += 1
        return u

    @classmethod
    def current(cls, name):
        result = cls(name, datetime.datetime.now())
        for i, u in enumerate(iter_usage_with_progress()):
            u.ensure_category()
            u.ensure_hexdump()
            result._add_usage(u)
        return result

    def total_size(self):
        '''Get total allocated size, in bytes'''
        return self._totalsize

    def summary(self):
        return '%s allocated, in %i blocks' % (fmt_size(self.total_size()), 
                                               self._num_usage)

    def size_by_address(self, address):
        return self._chunk_by_address[address].size

class History(object):
    '''History of snapshots of the state of the heap'''
    def __init__(self):
        self.snapshots = []

    def add(self, name):
        s = Snapshot.current(name)
        self.snapshots.append(s)
        return s

class Diff(object):
    '''Differences between two states of the heap'''
    def __init__(self, old, new):
        self.old = old
        self.new = new

        self.new_minus_old = self.new._all_usage - self.old._all_usage
        self.old_minus_new = self.old._all_usage - self.new._all_usage

    def stats(self):
        size_change = self.new.total_size() - self.old.total_size()
        count_change = self.new._num_usage - self.old._num_usage
        return "%s%s bytes, %s%s blocks" % (sign(size_change),
                                      fmt_size(size_change),
                                      sign(count_change),
                                      fmt_size(count_change))
        
    def as_changes(self):
        result = self.chunk_report('Free-d blocks', self.old, self.old_minus_new)
        result += self.chunk_report('New blocks', self.new, self.new_minus_old)
        # FIXME: add changed chunks
        return result

    def chunk_report(self, title, snapshot, set_of_usage):
        result = '%s:\n' % title
        if len(set_of_usage) == 0:
            result += '  (none)\n'
            return result
        for usage in sorted(set_of_usage,
                            lambda u1, u2: cmp(u1.start, u2.start)):
            result += ('  %s -> %s %8i bytes %20s |%s\n'
                       % (fmt_addr(usage.start),
                          fmt_addr(usage.start + usage.size-1),
                          usage.size, usage.category, usage.hd))
        return result
 


class GTypeInstancePtr(WrappedPointer):
    @classmethod
    def from_gtypeinstance_ptr(cls, addr, typenode):
        typename = cls.get_type_name(typenode)
        if typename:
            cls = cls.get_class_for_typename(typename)
            return cls(addr, typenode, typename)

    @classmethod
    def get_class_for_typename(cls, typename):
        '''Get the GTypeInstance subclass for the given type name'''
        if typename in typemap:
            return typemap[typename]
        return GTypeInstancePtr

    def __init__(self, addr, typenode, typename):
        # Try to cast the ptr to the named type:
        addr = gdb.Value(addr)
        try:
            if is_typename_castable(typename):
                # This requires, say, gtk2-debuginfo:
                ptr_type = caching_lookup_type(typename).pointer()
                addr = addr.cast(ptr_type)
                #print typename, addr.dereference()
                #if typename == 'GdkPixbuf':
                #    print 'GOT PIXELS', addr['pixels']
        except RuntimeError as e:
            pass
            #print addr, e

        WrappedPointer.__init__(self, addr)
        self.typenode = typenode
        self.typename = typename
        """
        try:
            print 'self', self
            print 'self.typename', self.typename
            print 'typenode', typenode
            print 'typenode.type', typenode.type
            print 'typenode.dereference()', typenode.dereference()
            print
        except:
            print 'got here'
            raise
        """

    def categorize(self):
        return Category('GType', self.typename, '')

    @classmethod
    def get_type_name(cls, typenode):
        return g_quark_to_string(typenode["qname"])


class GdkColormapPtr(GTypeInstancePtr):
    def categorize_refs(self, usage_set, level=0, detail=None):
        # print 'got here 46'
        pass
        # GdkRgbInfo is stored as qdata on a GdkColormap

class GdkImagePtr(GTypeInstancePtr):
    def categorize_refs(self, usage_set, level=0, detail=None):
        priv_type = caching_lookup_type('GdkImagePrivateX11').pointer()
        priv_data = WrappedPointer(self._gdbval['windowing_data'].cast(priv_type))

        usage_set.set_addr_category(priv_data.as_address(),
                                    Category('GType', 'GdkImagePrivateX11', ''),
                                    level=level+1, debug=True)

        ximage = WrappedPointer(priv_data.field('ximage'))
        dims = '%sw x %sh x %sbpp' % (ximage.field('width'),
                                      ximage.field('height'),
                                      ximage.field('depth'))
        usage_set.set_addr_category(ximage.as_address(),
                                    Category('X11', 'Image', dims),
                                    level=level+2, debug=True)

        usage_set.set_addr_category(int(ximage.field('data')),
                                    Category('X11', 'Image data', dims),
                                    level=level+2, debug=True)

class GdkPixbufPtr(GTypeInstancePtr):
    def categorize_refs(self, usage_set, level=0, detail=None):
        dims = '%sw x %sh' % (self._gdbval['width'],
                              self._gdbval['height'])
        usage_set.set_addr_category(int(self._gdbval['pixels']),
                                    Category('GType', 'GdkPixbuf pixels', dims),
                                    level=level+1, debug=True)

class PangoCairoFcFontMapPtr(GTypeInstancePtr):
    def categorize_refs(self, usage_set, level=0, detail=None):
        # This gives us access to the freetype library:
        FT_Library = WrappedPointer(self._gdbval['library'])

        # This is actually a "struct  FT_LibraryRec_", in FreeType's
        #   include/freetype/internal/ftobjs.h
        # print FT_Library._gdbval.dereference()

        usage_set.set_addr_category(FT_Library.as_address(),
                                    Category('FreeType', 'Library', ''),
                                    level=level+1, debug=True)

        usage_set.set_addr_category(int(FT_Library.field('raster_pool')),
                                    Category('FreeType', 'raster_pool', ''),
                                    level=level+2, debug=True)
        # potentially we could look at FT_Library['memory']


class Category(namedtuple('Category', ('domain', 'kind', 'detail'))):
    '''
    Categorization of an in-use area of memory

      domain: high-level grouping e.g. "python", "C++", etc

      kind: type information, appropriate to the domain e.g. a class/type

        Domain     Meaning of 'kind'
        ------     -----------------
        'C++'      the C++ class
        'python'   the python class
        'cpython'  C structure/type (implementation detail within Python)
        'pyarena'  Python memory allocator

      detail: additional detail
    '''

    def __new__(_cls, domain, kind, detail=None):
        return tuple.__new__(_cls, (domain, kind, detail))

    def __str__(self):
        return '%s:%s:%s' % (self.domain, self.kind, self.detail)



class Table(object):
    '''A table of text/numbers that knows how to print itself'''
    def __init__(self, columnheadings=None, rows=[]):
        self.numcolumns = len(columnheadings)
        self.columnheadings = columnheadings
        self.rows = []
        self._colsep = '  '

    def add_row(self, row):
        assert len(row) == self.numcolumns
        self.rows.append(row)

    def write(self, out):
        colwidths = self._calc_col_widths()

        self._write_row(out, colwidths, self.columnheadings)

        self._write_separator(out, colwidths)

        for row in self.rows:
            self._write_row(out, colwidths, row)

    def _calc_col_widths(self):
        result = []
        for colIndex in range(self.numcolumns):
            result.append(self._calc_col_width(colIndex))
        return result

    def _calc_col_width(self, idx):
        cells = [str(row[idx]) for row in self.rows]
        heading = self.columnheadings[idx]
        return max([len(c) for c in (cells + [heading])])

    def _write_row(self, out, colwidths, values):
        for i, (value, width) in enumerate(zip(values, colwidths)):
            if i > 0:
                out.write(self._colsep)
            formatString = "%%%ds" % width # to generate e.g. "%20s"
            out.write(formatString % value)
        out.write('\n')

    def _write_separator(self, out, colwidths):
        for i, width in enumerate(colwidths):
            if i > 0:
                out.write(self._colsep)
            out.write('-' * width)
        out.write('\n')

class UsageSet(object):
    def __init__(self, usage_list):
        self.usage_list = usage_list

        # Ensure we can do fast lookups:
        self.usage_by_address = dict([(int(u.start), u) for u in usage_list])

    def set_addr_category(self, addr, category, level=0, visited=None, debug=False):
        '''Attempt to mark the given address as being of the given category,
        whilst maintaining a set of address already visited, to try to stop
        infinite graph traveral'''
        if visited:
            if addr in visited:
                if debug:
                    print('addr 0x%x already visited (for category %r)' % (addr, category))
                return False
            visited.add(addr)

        if addr in self.usage_by_address:
            if debug:
                print('addr 0x%x found (for category %r, level=%i)' % (addr, category, level))
            u = self.usage_by_address[addr]
            # Bail if we already have a more detailed categorization for the
            # address:
            if level <= u.level:
                if debug:
                    print ('addr 0x%x already has category %r (level %r)'
                           % (addr, u.category, u.level))
                return False
            u.category = category
            u.level = level
            return True
        else:
            if debug:
                print('addr 0x%x not found (for category %r)' % (addr, category))

class PythonCategorizer(object):
    '''
    Logic for categorizing buffers owned by Python objects.
    (Done as an object to capture the type-lookup state)
    '''
    def __init__(self):
        '''This will raise a TypeError if the types aren't available (e.g. not
        a python app, or debuginfo not available'''
        self._type_PyDictObject_ptr = caching_lookup_type('PyDictObject').pointer()
        self._type_PyListObject_ptr = caching_lookup_type('PyListObject').pointer()
        self._type_PySetObject_ptr = caching_lookup_type('PySetObject').pointer()
        self._type_PyUnicodeObject_ptr = caching_lookup_type('PyUnicodeObject').pointer()
        self._type_PyCodeObject_ptr = caching_lookup_type('PyCodeObject').pointer()
        self._type_PyGC_Head = caching_lookup_type('PyGC_Head')

    @classmethod
    def make(cls):
        '''Try to make a PythonCategorizer, if debuginfo is available; otherwise return None'''
        try:
            return cls()
        except RuntimeError:
            return None

    def categorize(self, u, usage_set):
        '''Try to categorize a Usage instance within an UsageSet (which could
        lead to further categorization)'''
        c = u.category
        if c.domain != 'python':
            return False
        if u.obj:
            if u.obj.categorize_refs(usage_set):
                return True

        if c.kind == 'list':
            list_ptr = gdb.Value(u.start + self._type_PyGC_Head.sizeof).cast(self._type_PyListObject_ptr)
            ob_item = int(list_ptr['ob_item'])
            usage_set.set_addr_category(ob_item,
                                        Category('cpython', 'PyListObject ob_item table', None))
            return True

        elif c.kind == 'set':
            set_ptr = gdb.Value(u.start + self._type_PyGC_Head.sizeof).cast(self._type_PySetObject_ptr)
            table = int(set_ptr['table'])
            usage_set.set_addr_category(table,
                                        Category('cpython', 'PySetObject setentry table', None))
            return True

        if c.kind == 'code':
            # Python 2.6's PyCode_Type doesn't have Py_TPFLAGS_HAVE_GC:
            code_ptr = gdb.Value(u.start).cast(self._type_PyCodeObject_ptr)
            co_code =  int(code_ptr['co_code'])
            usage_set.set_addr_category(co_code,
                                        Category('python', 'str', 'bytecode'), # FIXME: on py3k this should be bytes
                                        level=1)
            return True
        elif c.kind == 'sqlite3.Statement':
            ptr_type = caching_lookup_type('pysqlite_Statement').pointer()
            obj_ptr = gdb.Value(u.start).cast(ptr_type)
            #print obj_ptr.dereference()
#            from heap.sqlite import categorize_sqlite3
            for fieldname, catname, fn in (('db', 'sqlite3', categorize_sqlite3),
                                           ('st', 'sqlite3_stmt', None)):
                field_ptr = int(obj_ptr[fieldname])

                # sqlite's src/mem1.c adds a a sqlite3_int64 (size) to the front
                # of the allocation, so we need to look 8 bytes earlier to find
                # the malloc-ed region:
                malloc_ptr = field_ptr - 8

                # print u, fieldname, category, field_ptr
                if usage_set.set_addr_category(malloc_ptr, Category('sqlite3', catname)):
                    if fn:
                        fn(field_ptr, usage_set, set())
            return True

        elif c.kind == 'rpm.hdr':
            ptr_type = caching_lookup_type('struct hdrObject_s').pointer()
            if ptr_type:
                obj_ptr = gdb.Value(u.start).cast(ptr_type)
                # print obj_ptr.dereference()
                h = obj_ptr['h']
                if usage_set.set_addr_category(int(h), Category('rpm', 'Header', None)):
                    blob = h['blob']
                    usage_set.set_addr_category(int(blob), Category('rpm', 'Header blob', None))

        elif c.kind == 'rpm.mi':
            ptr_type = caching_lookup_type('struct rpmmiObject_s').pointer()
            if ptr_type:
                obj_ptr = gdb.Value(u.start).cast(ptr_type)
                print(obj_ptr.dereference())
                mi = obj_ptr['mi']
                if usage_set.set_addr_category(int(mi),
                                               Category('rpm', 'rpmdbMatchIterator', None)):
                    pass
                    #blob = h['blob']
                    #usage_set.set_addr_category(int(blob), 'rpm Header blob')

        # Not categorized:
        return False


class PyArenaPtr(WrappedPointer):
    # Wrapper around a (void*) that's a Python arena's buffer (the
    # arena->address, as opposed to the (struct arena_object*) itself)
    @classmethod
    def from_addr(cls, p, arenaobj):
        ptr = gdb.Value(p)
        ptr = ptr.cast(type_void_ptr)
        return cls(ptr, arenaobj)

    def __init__(self, gdbval, arenaobj):
        WrappedPointer.__init__(self, gdbval)

        assert(isinstance(arenaobj, ArenaObject))
        self.arenaobj = arenaobj

        # obmalloc.c sets up arenaobj->pool_address to the first pool
        # address, aligning it to POOL_SIZE_MASK:
        self.initial_pool_addr = self.as_address()
        self.num_pools = ARENA_SIZE / POOL_SIZE
        self.excess = self.initial_pool_addr & POOL_SIZE_MASK
        if self.excess != 0:
            self.num_pools -= 1
            self.initial_pool_addr += POOL_SIZE - self.excess

    def __str__(self):
        return ('PyArenaPtr([%s->%s], %i pools [%s->%s], excess: %i tracked by %s)'
                % (fmt_addr(self.as_address()),
                   fmt_addr(self.as_address() + ARENA_SIZE - 1),
                   self.num_pools,
                   fmt_addr(self.initial_pool_addr),
                   fmt_addr(self.initial_pool_addr
                            + (self.num_pools * POOL_SIZE) - 1),
                   self.excess,
                   self.arenaobj
                   )
                )

    def iter_pools(self):
        '''Yield a sequence of PyPoolPtr, representing all of the pools within
        this arena'''
        # print 'num_pools:', num_pools
        pool_addr = self.initial_pool_addr
        for idx in range(self.num_pools):

            # "pool_address" is a high-water-mark for activity within the arena;
            # pools at this location or beyond haven't been initialized yet:
            if pool_addr >= self.arenaobj.pool_address:
                return

            pool = PyPoolPtr.from_addr(pool_addr)
            yield pool
            pool_addr += POOL_SIZE

    def iter_usage(self):
        '''Yield a series of Usage instances'''
        if self.excess != 0:
            # FIXME: this size is wrong
            yield Usage(self.as_address(), self.excess, Category('pyarena', 'alignment wastage'))

        for pool in self.iter_pools():
            # print 'pool:', pool
            for u in pool.iter_usage():
                yield u

        # FIXME: unused space (if any) between pool_address and the alignment top

        # if self.excess != 0:
        #    # FIXME: this address is wrong
        #    yield Usage(self.as_address(), self.excess, Category('pyarena', 'alignment wastage'))


class PyPoolPtr(WrappedPointer):
    # Wrapper around Python's obmalloc.c: poolp: (struct pool_header *)

    @classmethod
    def from_addr(cls, p):
        ptr = gdb.Value(p)
        ptr = ptr.cast(cls.gdb_type())
        return cls(ptr)

    def __str__(self):
        return ('PyPoolPtr([%s->%s: %d blocks of size %i bytes))'
                % (fmt_addr(self.as_address()), fmt_addr(self.as_address() + POOL_SIZE - 1),
                   self.num_blocks(), self.block_size()))

    @classmethod
    def gdb_type(cls):
        # Deferred lookup of the "poolp" type:
        return caching_lookup_type('poolp')

    def block_size(self):
        return INDEX2SIZE(self.field('szidx'))

    def num_blocks(self):
        firstoffset = self._firstoffset()
        maxnextoffset = self._maxnextoffset()
        offsetrange = maxnextoffset - firstoffset
        return offsetrange / self.block_size() # FIXME: not exactly correctly

    def _firstoffset(self):
        return POOL_OVERHEAD()

    def _maxnextoffset(self):
        return POOL_SIZE - self.block_size()

    def iter_blocks(self):
        '''Yield all blocks within this pool, whether free or in use'''
        size = self.block_size()
        maxnextoffset = self._maxnextoffset()
        # print initnextoffset, maxnextoffset
        offset = self._firstoffset()
        base_addr = self.as_address()
        while offset <= maxnextoffset:
            yield (base_addr + offset, size)
            offset += size

    def iter_usage(self):
        # The struct pool_header at the front:
        yield Usage(self.as_address(),
                    POOL_OVERHEAD(),
                    Category('pyarena', 'pool_header overhead'))

        fb = list(self.iter_free_blocks())
        for (start, size) in fb:
            yield Usage(start, size, Category('pyarena', 'freed pool chunk'))

        for (start, size) in self.iter_used_blocks():
            if (start, size) not in fb:
                yield Usage(start, size) #, 'python pool: ' + categorize(start, size, None))

        # FIXME: yield any wastage at the end

    def iter_free_blocks(self):
        '''Yield the sequence of free blocks within this pool.  Doesn't include
        the areas after nextoffset that have never been allocated'''
        # print self._gdbval.dereference()
        size = self.block_size()
        freeblock = self.field('freeblock')
        _type_block_ptr_ptr = caching_lookup_type('unsigned char').pointer().pointer()
        # Walk the singly-linked list of free blocks for this chunk
        while int(freeblock) != 0:
            # print 'freeblock:', (fmt_addr(int(freeblock)), int(size))
            yield (int(freeblock), int(size))
            freeblock = freeblock.cast(_type_block_ptr_ptr).dereference()

    def _free_blocks(self):
        # Get the set of addresses of free blocks
        return set([addr for addr, size in self.iter_free_blocks()])

    def iter_used_blocks(self):
        '''Yield the sequence of currently in-use blocks within this pool'''
        # We'll filter out the free blocks from the list:
        free_block_addresses = self._free_blocks()

        size = self.block_size()
        initnextoffset = self._firstoffset()
        nextoffset = self.field('nextoffset')
        #print initnextoffset, nextoffset
        offset = initnextoffset
        base_addr = self.as_address()
        # Iterate upwards until you reach "pool->nextoffset": blocks beyond
        # that point have never been allocated:
        while offset < nextoffset:
            addr = base_addr + offset
            # Filter out those within this pool's linked list of free blocks:
            if int(addr) not in free_block_addresses:
                yield (int(addr), int(size))
            offset += size

class PyObjectPtr(WrappedPointer):
    @classmethod
    def from_pyobject_ptr(cls, addr):
        ob_type = addr['ob_type']
        tp_flags = ob_type['tp_flags']
        if tp_flags & Py_TPFLAGS_HEAPTYPE:
            return HeapTypeObjectPtr(addr)

        if tp_flags & Py_TPFLAGS_UNICODE_SUBCLASS:
            return PyUnicodeObjectPtr(addr.cast(caching_lookup_type('PyUnicodeObject').pointer()))

        if tp_flags & Py_TPFLAGS_DICT_SUBCLASS:
            return PyDictObjectPtr(addr.cast(caching_lookup_type('PyDictObject').pointer()))

        tp_name = ob_type['tp_name'].string()
        if tp_name == 'instance':
            __type_PyInstanceObjectPtr = caching_lookup_type('PyInstanceObject').pointer()
            return PyInstanceObjectPtr(addr.cast(__type_PyInstanceObjectPtr))

        return PyObjectPtr(addr)

    def type(self):
        return PyTypeObjectPtr(self.field('ob_type'))

    def safe_tp_name(self):
        try:
            return self.type().field('tp_name').string()
        except(RuntimeError, UnicodeDecodeError):
            # Can't even read the object at all?
            return 'unknown'

    def categorize(self):
        # Python objects will be categorized as ("python", tp_name), but
        # old-style classes have to do more work
        return Category('python', self.safe_tp_name())

    def as_malloc_addr(self):
        ob_type = addr['ob_type']
        tp_flags = ob_type['tp_flags']
        addr = int(self._gdbval)
        if tp_flags & Py_TPFLAGS_: # FIXME
            return obj_addr_to_gc_addr(addr)
        else:
            return addr

class ProgressNotifier(object):
    '''Wrap an iterable with progress notification to stdout'''
    def __init__(self, inner, msg):
        self.inner = inner
        self.count = 0
        self.msg = msg

    def __iter__(self):
        return self

    def next(self):
        self.count += 1
        if 0 == self.count % 10000:
            print(self.msg, self.count)
        return self.inner.next()

class CachedInferiorState(object):
    """
    Cached state containing information scraped from the inferior process
    """
    def __init__(self):
        self._arena_detectors = []

    def add_arena_detector(self, detector):
        self._arena_detectors.append(detector)

    def detect_arena(self, ptr, chunksize):
        '''Detect if this ptr returned by malloc is in use by any of the
        layered allocation schemes, returning arena object if it is, None
        if not'''
        for detector in self._arena_detectors:
            arena = detector.as_arena(ptr, chunksize)
            if arena:
                return arena

        # Not found:
        return None


class PyUnicodeObjectPtr(PyObjectPtr):
    """
    Class wrapping a gdb.Value that's a PyUnicodeObject* within the process
    being debugged.
    """
    _typename = 'PyUnicodeObject'

    def categorize_refs(self, usage_set, level=0, detail=None):
        m_str = int(self.field('str'))
        usage_set.set_addr_category(m_str,
                                    Category('cpython', 'PyUnicodeObject buffer', detail),
                                    level)
        return True

class PyDictObjectPtr(PyObjectPtr):
    """
    Class wrapping a gdb.Value that's a PyDictObject* i.e. a dict instance
    within the process being debugged.
    """
    _typename = 'PyDictObject'

    def categorize_refs(self, usage_set, level=0, detail=None):
        ma_table = int(self.field('ma_table'))
        usage_set.set_addr_category(ma_table,
                                    Category('cpython', 'PyDictEntry table', detail),
                                    level)
        return True

class PyInstanceObjectPtr(PyObjectPtr):
    _typename = 'PyInstanceObject'

    def cl_name(self):
        in_class = self.field('in_class')
        # cl_name is a python string, not a char*; rely on
        # prettyprinters for now:
        cl_name = str(in_class['cl_name'])[1:-1]
        return cl_name

    def categorize(self):
        return Category('python', self.cl_name(), 'old-style')

    def categorize_refs(self, usage_set, level=0, detail=None):
        cl_name = self.cl_name()
        # print 'cl_name', cl_name

        # Visit the in_dict:
        in_dict = self.field('in_dict')
        # print 'in_dict', in_dict

        dict_detail = '%s.__dict__' % cl_name

        # Mark the ptr as being a dictionary, adding detail
        usage_set.set_addr_category(obj_addr_to_gc_addr(in_dict),
                                    Category('cpython', 'PyDictObject', dict_detail),
                                    level=1)

        # Visit ma_table:
        _type_PyDictObject_ptr = caching_lookup_type('PyDictObject').pointer()
        in_dict = in_dict.cast(_type_PyDictObject_ptr)

        ma_table = int(in_dict['ma_table'])

        # Record details:
        usage_set.set_addr_category(ma_table,
                                    Category('cpython', 'PyDictEntry table', dict_detail),
                                    level=2)
        return True

class PyTypeObjectPtr(PyObjectPtr):
    _typename = 'PyTypeObject'

def pypy_categorizer(addr, size):
    return None

class ArenaCollection(WrappedPointer):

    # Corresponds to pypy/rpython/memory/gc/minimarkpage.py:ArenaCollection

    def get_arenas(self):
        # Yield a sequence of (struct pypy_ArenaReference0*) gdb.Value instances
        # representing the arenas
        current_arena = self.field('ac_inst_current_arena')
        # print "self.field('ac_inst_current_arena'): %s" % self.field('ac_inst_current_arena')
        if current_arena:
            yield ArenaReference(current_arena)
        # print "self.field('ac_inst_arenas_lists'):%s" % self.field('ac_inst_arenas_lists')
        #for arena in :
        arena = self.field('ac_inst_arenas_lists')
        #while arena:
        #    yield ArenaReference(arena)
        #    arena = arena.dereference()['ac_inst_nextarena']
        
class ArenaReference(WrappedPointer):
    def iter_usage(self):
        # print 'got PyPy arena within allocations'
        return [] # FIXME
    
class PyPyArenaDetection(object):
    '''Detection of PyPy arenas, done as an object so that we can cache state'''
    def __init__(self):
        try:
            ac_global = gdb.parse_and_eval('pypy_g_pypy_rpython_memory_gc_minimarkpage_ArenaCollect')
        except RuntimeError:
            # Not PyPy?
            raise WrongInferiorProcess('pypy')
        self._ac = ArenaCollection(ac_global.address)
        self._arena_refs = []
        self._malloc_ptrs = {}
        for ar in self._ac.get_arenas():
            print(ar)
            print(ar._gdbval.dereference())
            self._arena_refs.append(ar)
            # ar_base : address as returned by malloc
            self._malloc_ptrs[int(ar.field('ar_base'))] = ar
        print(self._malloc_ptrs)

    def as_arena(self, ptr, chunksize):
        if ptr in self._malloc_ptrs:
            return self._malloc_ptrs[ptr]
        return None

class HeapTypeObjectPtr(PyObjectPtr):
    _typename = 'PyObject'

    def categorize_refs(self, usage_set, level=0, detail=None):
        attr_dict = self.get_attr_dict()
        if attr_dict:
            # Mark the dictionary's "detail" with our typename
            # gdb.execute('print (PyObject*)0x%x' % int(attr_dict._gdbval))
            usage_set.set_addr_category(obj_addr_to_gc_addr(attr_dict._gdbval),
                                        Category('python', 'dict', '%s.__dict__' % self.safe_tp_name()),
                                        level=level+1)

            # and mark the dict's PyDictEntry with our typename:
            attr_dict.categorize_refs(usage_set, level=level+1,
                                      detail='%s.__dict__' % self.safe_tp_name())
        return True

    def get_attr_dict(self):
        '''
        Get the PyDictObject ptr representing the attribute dictionary
        (or None if there's a problem)
        '''
#        from heap import type_char_ptr
        try:
            typeobj = self.type()
            dictoffset = int_from_int(typeobj.field('tp_dictoffset'))
            if dictoffset != 0:
                if dictoffset < 0:
                    type_PyVarObject_ptr = caching_lookup_type('PyVarObject').pointer()
                    tsize = int_from_int(self._gdbval.cast(type_PyVarObject_ptr)['ob_size'])
                    if tsize < 0:
                        tsize = -tsize
                    size = _PyObject_VAR_SIZE(typeobj, tsize)
                    dictoffset += size
                    assert dictoffset > 0
                    if dictoffset % SIZEOF_VOID_P != 0:
                        # Corrupt somehow?
                        return None

                dictptr = self._gdbval.cast(type_char_ptr) + dictoffset
                PyObjectPtrPtr = caching_lookup_type('PyObject').pointer().pointer()
                dictptr = dictptr.cast(PyObjectPtrPtr)
                return PyObjectPtr.from_pyobject_ptr(dictptr.dereference())
        except RuntimeError:
            # Corrupt data somewhere; fail safe
            pass

        # Not found, or some kind of error:
        return None

class ArenaObject(WrappedPointer):
    '''
    Wrapper around Python's struct arena_object*
    Note that this is record-keeping for an arena, not the
    memory itself
    '''
    @classmethod
    def iter_arenas(cls):
        try:
            val_arenas = gdb.parse_and_eval('arenas')
            val_maxarenas = gdb.parse_and_eval('maxarenas')
        except RuntimeError:
            # Not linked against python, or no debug information:
            raise WrongInferiorProcess('cpython')

        try:
            for i in range(val_maxarenas):
                # Look up "&arenas[i]":
                obj = ArenaObject(val_arenas[i].address)

                # obj->address == 0 indicates an unused entry within the "arenas" array:
                if obj.address != 0:
                    yield obj
        except RuntimeError:
            # pypy also has a symbol named "arenas", of type "long unsigned int * volatile"
            # For now, ignore it:
            return

    @property  # need to override the base property
    def address(self):
        return self.field('address')

    def __init__(self, gdbval):
        WrappedPointer.__init__(self, gdbval)

        # Cache some values:
        # This is the high-water mark: at this point and beyond, the bytes of
        # memory are untouched since malloc:
        self.pool_address = self.field('pool_address')


class CPythonArenaDetection(object):
    '''Detection of CPython arenas, done as an object so that we can cache state'''
    def __init__(self):
        self.arenaobjs = list(ArenaObject.iter_arenas())

    def as_arena(self, ptr, chunksize):
        '''Detect if this ptr returned by malloc is in use as a Python arena,
        returning PyArenaPtr if it is, None if not'''
        # Fast rejection of too-small chunks:
        if chunksize < (256 * 1024):
            return None

        for arenaobj in self.arenaobjs:
            if ptr == arenaobj.address:
                # Found it:
                return PyArenaPtr.from_addr(ptr, arenaobj)

        # Not found:
        return None

class HeapCPythonAllocators(gdb.Command):
    "For CPython: display information on the allocators"
    def __init__(self):
        gdb.Command.__init__ (self,
                              "heap cpython-allocators",
                              gdb.COMMAND_DATA)

    @need_debuginfo
    def invoke(self, args, from_tty):
        t = Table(columnheadings=('struct arena_object*', '256KB buffer location', 'Free pools'))
        for arena in ArenaObject.iter_arenas():
            t.add_row([fmt_addr(arena.as_address()),
                       fmt_addr(arena.address),
                       '%i / %i ' % (arena.field('nfreepools'),
                                     arena.field('ntotalpools'))
                       ])
        print('Objects/obmalloc.c: %i arenas' % len(t.rows))
        t.write(sys.stdout)
        print()



class MChunkPtr(WrappedPointer):
    '''Wrapper around glibc's mchunkptr

    Note:
      as_address() gives the address of the chunk as seen by the malloc implementation
      as_mem() gives the address as seen by the user of malloc'''

    # size field is or'ed with PREV_INUSE when previous adjacent chunk in use
    PREV_INUSE = 0x1

    # /* extract inuse bit of previous chunk */
    # #define prev_inuse(p)       ((p)->size & PREV_INUSE)


    # size field is or'ed with IS_MMAPPED if the chunk was obtained with mmap()
    IS_MMAPPED = 0x2

    # /* check for mmap()'ed chunk */
    # #define chunk_is_mmapped(p) ((p)->size & IS_MMAPPED)


    # size field is or'ed with NON_MAIN_ARENA if the chunk was obtained
    # from a non-main arena.  This is only set immediately before handing
    # the chunk to the user, if necessary.
    NON_MAIN_ARENA = 0x4

    # /* check for chunk from non-main arena */
    # #define chunk_non_main_arena(p) ((p)->size & NON_MAIN_ARENA)

    SIZE_BITS = (PREV_INUSE|IS_MMAPPED|NON_MAIN_ARENA)

    @classmethod
    def gdb_type(cls):
        # Deferred lookup of the "mchunkptr" type:
        return caching_lookup_type('mchunkptr')

    def size(self):
        if not(hasattr(self, '_cached_size')):
            self._cached_size = int(self.field('size'))
        return self._cached_size

    def chunksize(self):
        return self.size() & ~(self.SIZE_BITS)

    def has_flag(self, flag):
        return self.size() & flag

    def has_PREV_INUSE(self):
        return self.has_flag(self.PREV_INUSE)

    def has_IS_MMAPPED(self):
        return self.has_flag(self.IS_MMAPPED)

    def has_NON_MAIN_ARENA(self):
        return self.has_flag(self.NON_MAIN_ARENA)

    def __str__(self):
        result = ('<%s chunk=0x%x mem=0x%x'
                  % (self.__class__.__name__,
                     self.as_address(),
                     self.as_mem()))
        if self.has_PREV_INUSE():
            result += ' PREV_INUSE'
        else:
            result += ' prev_size=%i' % self.field('prev_size')
        if self.has_NON_MAIN_ARENA():
            result += ' NON_MAIN_ARENA'
        if self.has_IS_MMAPPED():
            result += ' IS_MMAPPED'
        else:
            if self.is_inuse():
                result += ' inuse'
            else:
                result += ' free'
        SIZE_SZ = caching_lookup_type('size_t').sizeof
        result += ' chunksize=%i memsize=%i>' % (self.chunksize(),
                                                 self.chunksize() - (2 * SIZE_SZ))
        return result

    def as_mem(self):
        # Analog of chunk2mem: the address as seen by the program (e.g. malloc)
        SIZE_SZ = caching_lookup_type('size_t').sizeof
        return self.as_address() + (2 * SIZE_SZ)

    def is_inuse(self):
        # Is this chunk is use?
        if self.has_IS_MMAPPED():
            return True
        # Analog of #define inuse(p)
        #   ((((mchunkptr)(((char*)(p))+((p)->size & ~SIZE_BITS)))->size) & PREV_INUSE)
        nc = self.next_chunk()
        return nc.has_PREV_INUSE()

    def next_chunk(self):
        # Analog of:
        #   #define next_chunk(p) ((mchunkptr)( ((char*)(p)) + ((p)->size & ~SIZE_BITS) ))
        ptr = self._gdbval.cast(type_char_ptr)
        cs = self.chunksize()
        ptr += cs
        ptr = ptr.cast(MChunkPtr.gdb_type())
        #print 'next_chunk returning: 0x%x' % ptr
        return MChunkPtr(ptr)

    def prev_chunk(self):
        # Analog of:
        #   #define prev_chunk(p) ((mchunkptr)( ((char*)(p)) - ((p)->prev_size) ))
        ptr = self._gdbval.cast(type_char_ptr)
        ptr -= self.field('prev_size')
        ptr = ptr.cast(MChunkPtr.gdb_type())
        return MChunkPtr(ptr)

class MBinPtr(MChunkPtr):
    # Wrapper around an "mbinptr"

    @classmethod
    def gdb_type(cls):
        # Deferred lookup of the "mbinptr" type:
        return caching_lookup_type('mbinptr')

    def first(self):
        return MChunkPtr(self.field('fd'))

    def last(self):
        return MChunkPtr(self.field('bk'))

class MFastBinPtr(MChunkPtr):
    # Wrapped around a mfastbinptr
    pass

class MallocState(WrappedValue):
    # Wrapper around struct malloc_state, as defined in malloc.c

    def fastbin(self, idx):
        return MFastBinPtr(self.field('fastbinsY')[idx])

    def bin_at(self, i):
        # addressing -- note that bin_at(0) does not exist
        #  (mbinptr) (((char *) &((m)->bins[((i) - 1) * 2]))
        #	     - offsetof (struct malloc_chunk, fd))

        ptr = self.field('bins')[(i-1)*2]
        #print '001', ptr
        ptr = ptr.address
        #print '002', ptr
        ptr = ptr.cast(type_char_ptr)
        #print '003', ptr
        ptr -= offsetof('struct malloc_chunk', 'fd')
        #print '004', ptr
        ptr = ptr.cast(MBinPtr.gdb_type())
        #print '005', ptr
        return MBinPtr(ptr)

    def iter_chunks(self):
        '''Yield a sequence of MChunkPtr corresponding to all chunks of memory
        in the heap (both used and free), in order of ascending address'''

        for c in self.iter_mmap_chunks():
            yield c

        for c in self.iter_sbrk_chunks():
            yield c

    def iter_mmap_chunks(self):
        for inf in gdb.inferiors():
            thread  = gdb.selected_thread()
            (pid, lwpid, tid) = thread.ptid
            for (start, end) in iter_mmap_heap_chunks(pid):

                # print "Trying 0x%x-0x%x" % (start, end)
                try:
                    chunk = MChunkPtr(gdb.Value(start).cast(MChunkPtr.gdb_type()))
                    # Does this look like the first chunk within a range of
                    # mmap address space?
                    #print ('0x%x' % chunk.as_address() + chunk.chunksize())
                    if (not chunk.has_NON_MAIN_ARENA() and chunk.has_IS_MMAPPED()
                        and chunk.as_address() + chunk.chunksize() <= end):

                        # Iterate upwards until you reach "end" of mmap space:
                        while chunk.as_address() < end and chunk.has_IS_MMAPPED():
                            yield chunk
                            # print '0x%x' % chunk.as_address(), chunk
                            chunk = chunk.next_chunk()
                except RuntimeError:
                    pass

    def iter_sbrk_chunks(self):
        '''Yield a sequence of MChunkPtr corresponding to all chunks of memory
        in the heap (both used and free), in order of ascending address, for those
        from sbrk_base upwards'''
        # FIXME: this is currently a hack; I need to verify my logic here

        # As I understand it, it's only possible to navigate the following ways:
        #
        # For a chunk with PREV_INUSE:0, then prev_size is valid, and can be used
        # to substract down to the start of that chunk
        # For a chunk with PREV_INUSE:1, then prev_size is not readable (reading it
        # could lead to SIGSEGV), and it's not possible to get at the size of the
        # previous chunk.

        # For a free chunk, we have next/prev pointers to a doubly-linked list
        # of other free chunks.

        # For a chunk, we have the size, and that size gives us the address of the next chunk in RAM
        # So if we know the address of the first chunk, then we can use this to iterate upwards through RAM,
        # and thus iterate over all of the chunks

        # Start at "mp_.sbrk_base"
        chunk = MChunkPtr(gdb.Value(sbrk_base()).cast(MChunkPtr.gdb_type()))
        # sbrk_base is NULL when no small allocations have happened:

        if chunk.as_address() > 0:
            # Iterate upwards until you reach "top":
            top = int(self.field('top'))
            while chunk.as_address() != top:
                yield chunk
                # print '0x%x' % chunk.as_address(), chunk
                try:
                    chunk = chunk.next_chunk()
                except RuntimeError:
                    break


    def iter_sbrk_chunks_not_main(self):

	# sizeof(struct malloc_state) = 0x450 (i386)
	# sizeof(struct malloc_state) = 0xxxx (x86_64)

        if sizeof_ptr == 4:
            chunk = int('%ld' % self.address) + 0x450
        else:
            chunk = int('%ld' % self.address) + 0x890

        chunk = gdb.Value(chunk).cast(type_char_ptr)

        chunk = MChunkPtr(chunk.cast(MChunkPtr.gdb_type()))

        if chunk.as_address() > 0:
            top = int(self.field('top'))
            while chunk.as_address() != top:
                yield chunk
                try:
                    chunk = chunk.next_chunk()
                except RuntimeError:
                    break



    def iter_free_chunks(self):
        '''Yield a sequence of MChunkPtr (some of which may be MFastBinPtr),
        corresponding to the free chunks of memory'''
        # Account for top:
        print('top')
        yield MChunkPtr(self.field('top'))

        NFASTBINS = int(self.NFASTBINS())
        # Traverse fastbins:
        for i in range(0, NFASTBINS):

            print('fastbin %i' % i)
            p = self.fastbin(i)
            while not p.is_null():
                yield p
                p = MFastBinPtr(p.field('fd'))

        #   for (p = fastbin (av, i); p != 0; p = p->fd) {
        #     ++nfastblocks;
        #     fastavail += chunksize(p);
        #   }
        # }

        # Must keep this in-sync with malloc.c:
        # FIXME: can we determine this dynamically from within gdb?
        NBINS = 128

        # Traverse regular bins:
        for i in range(1, NBINS):
            print('regular bin %i' % i)
            b = self.bin_at(i)
            #print 'b: %s' % b
            p = b.last()
            n = 0
            #print 'p:', p
            while p.as_address() != b.as_address():
                #print 'n:', n
                #print 'b:', b
                #print 'p:', p
                n+=1
                yield p
                p = MChunkPtr(p.field('bk'))
        #    for (p = last(b); p != b; p = p->bk) {
        #        ++nblocks;
        #          avail += chunksize(p);
        #    }
        # }

    def NFASTBINS(self):
        fastbinsY = self.field('fastbinsY')
        return array_length(fastbinsY)

class MallocPar(WrappedValue):
    # Wrapper around static struct malloc_par mp_
    @classmethod
    def get(cls):
        # It's a singleton:
        gdbval = gdb.parse_and_eval('mp_')
        return MallocPar(gdbval)


class GlibcArenas(object):
    def __init__(self):
        self.main_arena = ''
        self.cur_arena = ''
        self.activate()
#        self.activate = False
#       self.main_arena = self.get_main_arena()
#        self.get_main_arena()
#        if self.main_arena:
#            self.cur_arena = self.get_ms(self.main_arena)
#            self.get_arenas()


    def activate(self):
        try:
            self.main_arena = self.get_main_arena()
#            self.main_arena = gdb.parse_and_eval("main_arena")
        except:
            print("GDB-Heap didnt activate!")
            return

        type_void_ptr = gdb.lookup_type('void').pointer()
        type_char_ptr = gdb.lookup_type('char').pointer()
        type_unsigned_char_ptr = gdb.lookup_type('unsigned char').pointer()
        sizeof_ptr = type_void_ptr.sizeof
        void_ptr_ptr = caching_lookup_type('void').pointer().pointer()

        if sizeof_ptr == 4:
            format_string = '0x%08x'
        else:
            format_string = '0x%016x'


        self.cur_arena = self.get_ms(self.main_arena)
        self.get_arenas()

    def get_main_arena(self):
        return gdb.parse_and_eval("main_arena")

    def get_ms(self, arena_dereference=None):
        if arena_dereference:
            ms = MallocState(arena_dereference)
        else:
            ms = self.cur_arena

        return ms

    def get_arenas(self):
        ar_ptr = self.get_ms(self.main_arena)

        self.arenas = []
        while True:
            self.arenas.append(ar_ptr)

            if ar_ptr.address != ar_ptr.field('next'):
                ar_ptr = self.get_ms(ar_ptr.field('next').dereference())

            if ar_ptr.address == self.main_arena.address:
                return


def is_pyobject_ptr(addr):
    try:
        _type_pyop = caching_lookup_type('PyObject').pointer()
        _type_pyvarop = caching_lookup_type('PyVarObject').pointer()
    except RuntimeError:
        # not linked against python
        return None

    pyop = gdb.Value(addr).cast(_type_pyop)
    try:
        ob_refcnt = pyop['ob_refcnt']
        if ob_refcnt >=0 and ob_refcnt < 0xffff:
            obtype = pyop['ob_type']
            if obtype != 0:
                type_refcnt = obtype.cast(_type_pyop)['ob_refcnt']
                if type_refcnt > 0 and type_refcnt < 0xffff:
                    type_ob_size = obtype.cast(_type_pyvarop)['ob_size']

                    if type_ob_size > 0xffff:
                        return 0

                    for fieldname in ('tp_del', 'tp_mro', 'tp_init', 'tp_getset'):
                        if not looks_like_ptr(obtype[fieldname]):
                            return 0

                    # Then this looks like a Python object:
                    return PyObjectPtr.from_pyobject_ptr(pyop)

    except (RuntimeError, UnicodeDecodeError):
        pass # Not a python object (or corrupt)

def execute(command):
    '''Equivalent to gdb.execute(to_string=True), returning the output as
    a string rather than logging it to stdout.

    On gdb versions lacking this capability, it uses redirection and temporary
    files to achieve the same result'''
    if has_gdb_execute_to_string:
        return gdb.execute(command, to_string = True)
    else:
        f = tempfile.NamedTemporaryFile('r', delete=True)
        gdb.execute("set logging off")
        gdb.execute("set logging redirect off")
        gdb.execute("set logging file %s" % f.name)
        gdb.execute("set logging redirect on")
        gdb.execute("set logging on")
        gdb.execute(command)
        gdb.execute("set logging off")
        gdb.execute("set logging redirect off")
        result = f.read()
        f.close()
        return result


#try:
#    # This will either capture the result, or fail before executing,
#    # so in neither case should we get noise on stdout:
#    gdb.execute('info registers', to_string=True)
#except TypeError:
#    has_gdb_execute_to_string = False

def dump():
    print ('Does gdb.execute have an "to_string" keyword argument? : %s' 
           % has_gdb_execute_to_string)







# This was adapted from glib's gobject.py:g_type_to_name
def get_typenode_for_gtype(gtype):
    def lookup_fundamental_type(typenode):
        if typenode == 0:
            return None
        val = read_global_var("static_fundamental_type_nodes")
        if val == None:
            return None

        # glib has an address() call here on the end, which looks wrong
        # (i) it's an attribute, not a method
        # (ii) it converts a TypeNode* to a TypeNode**
        return val[typenode >> 2]

    gtype = int(gtype)
    typenode = gtype - gtype % 4
    if typenode > (255 << 2):
        return gdb.Value(typenode).cast (gdb.lookup_type("TypeNode").pointer())
    else:
        return lookup_fundamental_type (typenode)

def is_typename_castable(typename):
    if typename.startswith('Gtk'):
        return True
    if typename.startswith('Gdk'):
        return True
    if typename.startswith('GType'):
        return True
    if typename.startswith('Pango'):
        return True
    if typename.startswith('GVfs'):
        return True
    return False





def as_gtype_instance(addr, size):
    #type_GObject_ptr = caching_lookup_type('GObject').pointer()
    try:
        type_GTypeInstance_ptr = caching_lookup_type('GTypeInstance').pointer()
    except RuntimeError:
        # Not linked against GLib?
        return None

    gobj = gdb.Value(addr).cast(type_GTypeInstance_ptr)
    try:
        gtype = gobj['g_class']['g_type']
        #print 'gtype', gtype
        typenode = get_typenode_for_gtype(gtype)
        # If I remove the next line, we get errors like:
        #   Cannot access memory at address 0xd1a712caa5b6e5c0
        # Does this line give us an early chance to raise an exception?
        #print 'typenode', typenode
        # It appears to be in the coercion to boolean here:
        # if typenode:
        if typenode is not None:
            #print 'typenode.dereference()', typenode.dereference()
            return GTypeInstancePtr.from_gtypeinstance_ptr(addr, typenode)
    except RuntimeError:
        # Any random buffer that we point this at that isn't a GTypeInstance (or
        # GObject) is likely to raise a RuntimeError at some point in the above
        pass
    return None

# FIXME: currently this ignores G_SLICE
# e.g. use
#    G_SLICE=always-malloc
# to override this


def get_class_name(addr, size):
    # Try to detect a vtable ptr at the top of this object:
    vtable = gdb.Value(addr).cast(void_ptr_ptr).dereference()
    if not looks_like_ptr(vtable):
        return None

    info = execute('info sym (void *)0x%x' % int(vtable))
    # "vtable for Foo + 8 in section .rodata of /home/david/heap/test_cplusplus"
    m = re.match('vtable for (.*) \+ (.*)', info)
    if m:
        return m.group(1)
    # Not matched:
    return None
    

def as_cplusplus_object(addr, size):
    print(get_class_name(addr))
    pass

def fmt_addr(addr):
    return format_string % addr

class WrongInferiorProcess(RuntimeError):
    def __init__(self, hint):
        self.hint = hint


def caching_lookup_type(typename):
    '''Adds caching to gdb.lookup_type(), whilst still raising RuntimeError if
    the type isn't found.'''
    if typename in __type_cache:
        gdbtype = __type_cache[typename]
        if gdbtype:
            return gdbtype
        raise RuntimeError('(cached) Could not find type "%s"' % typename)
    try:
        if 0:
            print('type cache miss: %r' % typename)
        gdbtype = gdb.lookup_type(typename).strip_typedefs()
    except RuntimeError as e:
        # did not find the type: add a None to the cache
        gdbtype = None
    __type_cache[typename] = gdbtype
    if gdbtype:
        return gdbtype
    raise RuntimeError('Could not find type "%s"' % typename)

def array_length(_gdbval):
    '''Given a gdb.Value that's an array, determine the number of elements in
    the array'''
    arr_size = _gdbval.type.sizeof
    elem_size = _gdbval[0].type.sizeof
    return arr_size/elem_size

def offsetof(typename, fieldname):
    '''Get the offset (in bytes) from the start of the given type to the given
    field'''

    # This is a transliteration to gdb's python API of:
    #    (int)(void*)&((#typename*)NULL)->#fieldname)

    t = caching_lookup_type(typename).pointer()
    v = gdb.Value(0)
    v = v.cast(t)
    field = v[fieldname].cast(type_void_ptr)
    return int(field.address)


def check_missing_debuginfo(err, module):
    assert(isinstance(err, RuntimeError))
    if err.args[0] == 'Attempt to extract a component of a value that is not a (null).':
        # Then we likely are trying to extract a field from a struct but don't
        # have the DWARF description of the fields of the struct loaded:
        raise MissingDebuginfo(module)


def fmt_size(size):
    '''
    Pretty-formatting of numeric values: return a string, subdividing the
    digits into groups of three, using commas
    '''
    s = str(size)
    result = ''
    while len(s)>3:
        result = ',' + s[-3:] + result
        s = s[0:-3]
    result = s + result
    return result

def as_hexdump_char(b):
    '''Given a byte, return a string for use by hexdump, converting
    non-printable/non-ASCII values as a period'''
    if b>=0x20 and b < 0x80:
        return chr(b)
    else:
        return '.'

def sign(amt):
    if amt >= 0:
        return '+'
    else:
        return '' # the '-' sign will come from the numeric repr



def hexdump_as_bytes(addr, size, chars_only=True):
    addr = gdb.Value(addr).cast(type_unsigned_char_ptr)
    bytebuf = []
    for j in range(size):
        ptr = addr + j
        b = int(ptr.dereference())
        bytebuf.append(b)

    result = ''
    if not chars_only:
        result += ' '.join(['%02x' % b for b in bytebuf]) + ' |'
    result += ''.join([as_hexdump_char(b) for b in bytebuf])
    result += '|'

    return (result)

def hexdump_as_int(addr, count):
    addr = gdb.Value(addr).cast(caching_lookup_type('unsigned long').pointer())
    bytebuf = []
    longbuf = []
    for j in range(count):
        ptr = addr + j
        long = ptr.dereference()
        longbuf.append(long)
        bptr = gdb.Value(ptr).cast(type_unsigned_char_ptr)
        for i in range(sizeof_ptr):
            bytebuf.append(int((bptr + i).dereference()))
    return (' '.join([fmt_addr(long) for long in longbuf])
            + ' |'
            + ''.join([as_hexdump_char(b) for b in bytebuf])
            + '|')


def _get_register_state():
#    from heap.compat import execute
    return execute('thread apply all info registers')

def lazily_get_usage_list():
    '''Lazily do a full-graph categorization, getting a list of Usage instances'''
    global __cached_usage_list
    global __cached_reg_state

    reg_state = _get_register_state()
    # print 'reg_state', reg_state
    if __cached_usage_list and __cached_reg_state:
        # Verify that the inferior process hasn't changed state since the cache
        # was populated.
        # Something of a hack: verify that all registers have the same values:
        if reg_state == __cached_reg_state:
            # We can use the cache:
            # print 'USING THE CACHE'
            return __cached_usage_list

    # print 'REGENERATING THE CACHE'

    # Do the work:
    usage_list = list(iter_usage_with_progress())
    categorize_usage_list(usage_list)

    # Update the cache:
    __cached_usage_list = usage_list
    __cached_reg_state = reg_state

    return __cached_usage_list

def categorize_usage_list(usage_list):
    '''Do a "full-graph" categorization of the given list of Usage instances
    For example, if p is a (PyDictObject*), then mark p->ma_table and p->ma_mask
    accordingly
    '''
    usage_set = UsageSet(usage_list)
    visited = set()

    # Precompute some types, if available:
    pycategorizer = PythonCategorizer.make()

    for u in ProgressNotifier(iter(usage_list), 'Blocks analyzed'):
        # Cover the simple cases, where the category can be figured out directly:
        u.ensure_category(usage_set)

        # Cross-references:
        if u.obj:
            if u.obj.categorize_refs(usage_set):
                continue

        # Try to categorize buffers used by python objects:
        if pycategorizer:
            if pycategorizer.categorize(u, usage_set):
                continue

    python_categorization(usage_set)


def categorize(u, usage_set):
    '''Given an in-use block, try to guess what it's being used for
    If usage_set is provided, this categorization may lead to further
    categorizations'''
#    from heap.cpython import as_python_object, obj_addr_to_gc_addr
    addr, size = u.start, u.size
    pyop = as_python_object(addr)
    if pyop:
        u.obj = pyop
        try:
            return pyop.categorize()
        except (RuntimeError, UnicodeEncodeError, UnicodeDecodeError):
            # If something went wrong, assume that this wasn't really a python
            # object, and fall through:
            print("couldn't categorize pyop:", pyop)
            pass

    # PyPy detection:
#    from heap.pypy import pypy_categorizer
    cat = pypy_categorizer(addr, size)
    if cat:
        return cat

    # C++ detection: only enabled if we can capture "execute"; there seems to
    # be a bad interaction between pagination and redirection: all output from
    # "heap" disappears in the fallback form of execute, unless we "set pagination off"
#    from heap.compat import has_gdb_execute_to_string
    #  Disable for now, see https://bugzilla.redhat.com/show_bug.cgi?id=620930
    if False: # has_gdb_execute_to_string:
#        from heap.cplusplus import get_class_name
        cpp_cls = get_class_name(addr, size)
        if cpp_cls:
            return Category('C++', cpp_cls)

    # GObject detection:
#    from gobject import as_gtype_instance
    ginst = as_gtype_instance(addr, size)
    if ginst:
        u.obj = ginst
        return ginst.categorize()

    s = as_nul_terminated_string(addr, size)
    if s and len(s) > 2:
        return Category('C', 'string data')

    # Uncategorized:
    return Category('uncategorized', '', '%s bytes' % size)

def as_nul_terminated_string(addr, size):
    # Does this look like a NUL-terminated string?
    ptr = gdb.Value(addr).cast(type_char_ptr)
    try:
        s = ptr.string(encoding='ascii')
        return s
    except (RuntimeError, UnicodeDecodeError):
        # Probably not string data:
        return None

def iter_usage_with_progress():
    return ProgressNotifier(iter_usage(), 'Blocks retrieved')



def iter_usage():
    # Iterate through glibc, and within that, within Python arena blocks, as appropriate
#    from heap.glibc import glibc_arenas
    ms = glibc_arenas.get_ms()

    cached_state = CachedInferiorState()

#    from heap.cpython import ArenaDetection as CPythonArenaDetection, PyArenaPtr, ArenaObject
    try:
        cpython_arenas = CPythonArenaDetection()
        cached_state.add_arena_detector(cpython_arenas)
    except(WrongInferiorProcess):
        pass

#    from heap.pypy import ArenaDetection as PyPyArenaDetection
    try:
        pypy_arenas = PyPyArenaDetection()
        cached_state.add_arena_detector(pypy_arenas)
    except(WrongInferiorProcess):
        pass

    for i, chunk in enumerate(ms.iter_mmap_chunks()):
        mem_ptr = chunk.as_mem()
        chunksize = chunk.chunksize()

        arena = cached_state.detect_arena(mem_ptr, chunksize)
        if arena:
            for u in arena.iter_usage():
                yield u
        else:
            yield Usage(int(mem_ptr), chunksize)

    for chunk in ms.iter_sbrk_chunks():
        mem_ptr = chunk.as_mem()
        chunksize = chunk.chunksize()

        if chunk.is_inuse():
            arena = cached_state.detect_arena(mem_ptr, chunksize)
            if arena:
                for u in arena.iter_usage():
                    yield u
            else:
                yield Usage(int(mem_ptr), chunksize)



def looks_like_ptr(value):
    '''Does this gdb.Value pointer's value looks reasonable?

    For use when casting a block of memory to a structure on pointer fields
    within that block of memory.
    '''

    # NULL is acceptable; assume that it's 0 on every arch we care about
    if value == 0:
        return True

    # Assume that pointers aren't allocated in the bottom 1MB of a process'
    # address space:
    if value < (1024 * 1024):
        return False

    # Assume that if it got this far, that it's valid:
    return True





# Return the number of bytes in size class I:
def INDEX2SIZE(I):
    return (I + 1) << ALIGNMENT_SHIFT

def ROUNDUP(x):
    return (x + ALIGNMENT_MASK) & ~ALIGNMENT_MASK

def POOL_OVERHEAD():
    return ROUNDUP(caching_lookup_type('struct pool_header').sizeof)

# Taken from my libpython.py code in python's Tools/gdb/libpython.py
# FIXME: ideally should share code somehow
def _PyObject_VAR_SIZE(typeobj, nitems):
    type_size_t = caching_lookup_type('size_t')
    return ( ( typeobj.field('tp_basicsize') +
               nitems * typeobj.field('tp_itemsize') +
               (SIZEOF_VOID_P - 1)
             ) & ~(SIZEOF_VOID_P - 1)
           ).cast(type_size_t)
def int_from_int(gdbval):
    return int(gdbval)

    # Doesn't look like a python object, implicit return None

def obj_addr_to_gc_addr(addr):
    '''Given a PyObject* address, convert to a PyGC_Head* address
    (i.e. the allocator's view of the same)'''
    #print 'obj_addr_to_gc_addr(%s)' % fmt_addr(int(addr))
    _type_PyGC_Head = caching_lookup_type('PyGC_Head')
    return int(addr) - _type_PyGC_Head.sizeof

def as_python_object(addr):
    '''Given an address of an allocation, determine if it holds a PyObject,
    or a PyGC_Head

    Return a WrappedPointer for the PyObject* if it does (which might have a
    different location c.f. when PyGC_Head was allocated)

    Return None if it doesn't look like a PyObject*'''
    # Try casting to PyObject* ?
    # FIXME: what about the debug allocator?
    try:
        _type_pyop = caching_lookup_type('PyObject').pointer()
        _type_PyGC_Head = caching_lookup_type('PyGC_Head')
    except(RuntimeError):
        # not linked against python
        return None
    pyop = is_pyobject_ptr(addr)
    if pyop:
        return pyop
    else:
        # maybe a GC type:
        _type_PyGC_Head_ptr = _type_PyGC_Head.pointer()
        gc_ptr = gdb.Value(addr).cast(_type_PyGC_Head_ptr)
        # print gc_ptr.dereference()

        PYGC_REFS_REACHABLE = -3

        if gc_ptr['gc']['gc_refs'] == PYGC_REFS_REACHABLE:  # FIXME: need to cover other values
            pyop = is_pyobject_ptr(gdb.Value(addr + _type_PyGC_Head.sizeof))
            if pyop:
                return pyop
    # Doesn't look like a python object, implicit return None



def sbrk_base():
    mp_ = MallocPar.get()
    try:
        return int(mp_.field('sbrk_base'))
    except RuntimeError as e:
        check_missing_debuginfo(e, 'glibc')
        raise e

"""
"""


# See malloc.c:
#    struct mallinfo mALLINFo(mstate av)
#    {
#      struct mallinfo mi;
#      size_t i;
#      mbinptr b;
#      mchunkptr p;
#      INTERNAL_SIZE_T avail;
#      INTERNAL_SIZE_T fastavail;
#      int nblocks;
#      int nfastblocks;
#
#      /* Ensure initialization */
#      if (av->top == 0)  malloc_consolidate(av);
#
#      check_malloc_state(av);
#
#      /* Account for top */
#      avail = chunksize(av->top);
#      nblocks = 1;  /* top always exists */
#
#      /* traverse fastbins */
#      nfastblocks = 0;
#      fastavail = 0;
#
#      for (i = 0; i < NFASTBINS; ++i) {
#        for (p = fastbin (av, i); p != 0; p = p->fd) {
#          ++nfastblocks;
#          fastavail += chunksize(p);
#        }
#      }
#
#      avail += fastavail;
#
#      /* traverse regular bins */
#      for (i = 1; i < NBINS; ++i) {
#        b = bin_at(av, i);
#        for (p = last(b); p != b; p = p->bk) {
#          ++nblocks;
#          avail += chunksize(p);
#        }
#      }
#
#      mi.smblks = nfastblocks;
#      mi.ordblks = nblocks;
#      mi.fordblks = avail;
#      mi.uordblks = av->system_mem - avail;
#      mi.arena = av->system_mem;
#      mi.hblks = mp_.n_mmaps;
#      mi.hblkhd = mp_.mmapped_mem;
#      mi.fsmblks = fastavail;
#      mi.keepcost = chunksize(av->top);
#      mi.usmblks = mp_.max_total_mem;
#      return mi;
#    }
#


def iter_mmap_heap_chunks(pid):
    '''Try to locate the memory-mapped heap allocations for the given
    process (by PID) by reading /proc/PID/maps

    Yield a sequence of (start, end) pairs'''
    for line in open('/proc/%i/maps' % pid):
        # print line,
        # e.g.:
        # 38e441e000-38e441f000 rw-p 0001e000 fd:01 1087                           /lib64/ld-2.11.1.so
        # 38e441f000-38e4420000 rw-p 00000000 00:00 0
        hexd = r'[0-9a-f]'
        hexdigits = '(' + hexd + '+)'
        m = re.match(hexdigits + '-' + hexdigits
                     + r' ([r\-][w\-][x\-][ps]) ' + hexdigits
                     + r' (..:..) (\d+)\s+(.*)',
                     line)
        if m:
            # print m.groups()
            start, end, perms, offset, dev, inode, pathname = m.groups()
            # PROT_READ, PROT_WRITE, MAP_PRIVATE:
            if perms == 'rw-p':
                if offset == '00000000': # FIXME bits?
                    if dev == '00:00': # FIXME
                        if inode == '0': # FIXME
                            if pathname == '': # FIXME
                                # print 'heap line?:', line
                                # print m.groups()
                                start, end = [int(m.group(i), 16) for i in (1, 2)]
                                yield (start, end)
        else:
            print('unmatched :', line)


def register_commands():
    # Register the commands with gdb
    Heap()
    HeapSizes()
    HeapUsed()
    HeapFree()
    HeapAll()
    HeapLog()
    HeapLabel()
    HeapDiff()
    HeapSelect()
    HeapArenas()
    HeapArenaSelect()
    Hexdump()
    HeapActivate()



glibc_arenas = GlibcArenas()
# Use glib's pretty-printers:
dir_ = '/usr/share/glib-2.0/gdb'
if not dir_ in sys.path:
    sys.path.insert(0, dir_)





   
history = History()

register_commands();


has_gdb_execute_to_string = True
__cached_usage_list = None
__cached_reg_state = None
__type_cache = {}

NUM_HEXDUMP_BYTES = 20


type_void_ptr = gdb.lookup_type('void').pointer()
type_char_ptr = gdb.lookup_type('char').pointer()
type_unsigned_char_ptr = gdb.lookup_type('unsigned char').pointer()
sizeof_ptr = type_void_ptr.sizeof
void_ptr_ptr = caching_lookup_type('void').pointer().pointer()

if sizeof_ptr == 4:
    format_string = '0x%08x'
else:
    format_string = '0x%016x'


SIZEOF_VOID_P = type_void_ptr.sizeof

# Transliteration from Python's obmalloc.c:
ALIGNMENT             = 8
ALIGNMENT_SHIFT       = 3
ALIGNMENT_MASK        = (ALIGNMENT - 1)

SYSTEM_PAGE_SIZE      = (4 * 1024)
SYSTEM_PAGE_SIZE_MASK = (SYSTEM_PAGE_SIZE - 1)
ARENA_SIZE            = (256 << 10)
POOL_SIZE             = SYSTEM_PAGE_SIZE
POOL_SIZE_MASK        = SYSTEM_PAGE_SIZE_MASK

Py_TPFLAGS_HEAPTYPE = (1 << 9)

Py_TPFLAGS_INT_SUBCLASS      = (1 << 23)
Py_TPFLAGS_LONG_SUBCLASS     = (1 << 24)
Py_TPFLAGS_LIST_SUBCLASS     = (1 << 25)
Py_TPFLAGS_TUPLE_SUBCLASS    = (1 << 26)
Py_TPFLAGS_STRING_SUBCLASS   = (1 << 27)
Py_TPFLAGS_UNICODE_SUBCLASS  = (1 << 28)
Py_TPFLAGS_DICT_SUBCLASS     = (1 << 29)
Py_TPFLAGS_BASE_EXC_SUBCLASS = (1 << 30)
Py_TPFLAGS_TYPE_SUBCLASS     = (1 << 31)

NamedTuple = namedtuple('NamedTuple', ('x', 'y'))

objs = []
types = [OldStyle, NewStyle, NewStyleWithSlots]
types.append(NamedTuple)
for impl in types:
    objs.append(impl(x=3, y=4))

# Create instance with 9 attributes:
old_style_many = OldStyleManyAttribs(**dict(zip('abcdefghi', range(9))))
new_style_many = NewStyleManyAttribs(**dict(zip('abcdefghi', range(9))))



# Ensure that we have a set object that uses an externally allocated
# buffer, so that we can verify that these are detected.  To do this,
# we need a set with more than PySet_MINSIZE members (which is 8):
large_set = set(range(64))
large_frozenset = frozenset(range(64))

db = sqlite3.connect(':memory:')
c = db.cursor()

# Create table
c.execute('''CREATE TABLE dummy(foo TEXT, bar TEXT, v REAL)''')

# Insert a row of data
c.execute("INSERT INTO dummy VALUES ('ostrich', 'elephant', 42.0)")

# Save (commit) the changes
db.commit()

# Don't close "c"; we want to see the objects in memory


# Ensure that the selftest's breakpoint on builtin_id is hit:
id(42)


