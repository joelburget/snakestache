'''A pure-python implementation of Handlebars, a logic and specification-less
templating language originally implemented in javascript and tears. This
implementation works hard to adhere to the orinal implementation, even its
warts.
'''

import re
import ply.lex as lex
import ply.yacc as yacc

ipy = False
try:
    from IPython.lib import pretty
    ipy = True
except:
    pass

tokens = (
    'CONTENT',
    'COMMENT',
    'OPEN_BLOCK',
    'OPEN_ENDBLOCK',
    'OPEN_INVERSE',
    'OPEN_UNESCAPED',
    'OPEN',
    'EQUALS',
    'ID',
    'SEP',
    'CLOSE',
    'STRING',
    'DATA',
    'BOOLEAN',
    'INTEGER',
    # 'INVALID',
    'OPEN_PARTIAL',
    'PARTIAL_NAME',
    # 'EOF',
)

states = (
    ('com', 'exclusive'), # multiline comment
    ('mu',  'exclusive'), # in a mustache
    ('emu', 'exclusive'), # escaped mustache
    ('par', 'exclusive'), # partial
    )

# tokens

content_re = '[^\x00]+?(?={{)'
emu_content_re = '[^{]?(.[^{])+'

def t_CONTENT(t):
    '[^{]?(.[^{])+[^{]?' # Match as much as we can before '{{'
    # '[^\x00]+?(?={{)' # Match as much as we can before '{{'
    # '[^\x00]+?(?={{)|[^{\x00]+' # Match as much as we can before '{{'
    # TODO don't care about null/eof?

    if t.value[-1] != r'\\':
        t.lexer.push_state('mu');
    elif t.value[-1] == r'\\':
        t.value = t.value[:-1]
        t.lexer.push_state("emu")
    return t

def t_continue(t):
    '{{'
    # '(?:{{)' # Don't capture! - doesn't work?
    # print t.value
    # print t.lexer.lexdata[t.lexer.lexpos:t.lexer.lexpos+10]
    t.lexer.lexpos -= 2
    t.lexer.push_state('mu')

def t_emu_CONTENT(t):
    '[^\x00]{2,}(?={{)|[^{\x00]{2,}'
    # TODO don't care about null/eof?

    if t.value[-1] != r'\\':
        t.lexer.pop_state()
    elif t.value[-1] == r'\\':
        t.value = t.value[:-1]
    return t

def t_com_COMMENT(t):
    r'[\s\S]*?--}}'
    t.value = t.value[:-4]
    t.lexer.pop_state()
    return t

def t_mu_OPEN_PARTIAL(t):
    r'{{>'
    t.lexer.push_state("par")
    return t

# t_mu_OPEN_BLOCK = r'{{\#'
def t_mu_OPEN_BLOCK(t):
    r'{{\#'
    return t

t_mu_OPEN_INVERSE = r'{{(\^|\s*else)'
t_mu_OPEN_ENDBLOCK = r'{{/'
t_mu_OPEN_UNESCAPED = r'{{({|&)'

def t_ignore_mu_COMMENT(t):
    r'{{!--'
    t.lexer.pop_state()
    t.lexer.push_state('com')

def t_mu_COMMENT(t):
    r'{{![\s\S]*?}}'
    t.value = t.value[3:-4] # TODO(joel) -4?
    t.lexer.pop_state()

t_mu_OPEN = r'{{'
t_mu_EQUALS = r'='
t_mu_SEP = r'[\/.]'
t_mu_ignore = ' \t\n'

def t_mu_CLOSE(t):
    r'}}}?'
    t.lexer.pop_state()
    return t

def t_mu_STRING(t):
    r"""("(\\["]|[^"])*")|('(\\[']|[^'])*')"""

    # Remove quotes and unescape
    quote = t.value[0]
    t.value = t.value[1:-1]
    t.value = re.sub(r'\\' + quote, quote)
    return t

def t_mu_DATA(t):
    r'@[a-zA-Z]+'
    t.value = t.value[1:]
    return t

t_mu_BOOLEAN = r'true|false'
t_mu_INTEGER = r'\-?[0-9]+'
dotted_id = r'\.\.|\.(?=[} ])'
name_id = r'[a-zA-Z0-9_$-]+(?=[=}\s\/.])' 
bracketed_id = r'\[[^\]]*\]'
identifier = '%s|%s|%s' % (dotted_id, name_id, bracketed_id)

@lex.TOKEN(identifier)
def t_mu_ID(t):
    if t.value[0] == '[':
        t.value = t.value[1:-1]
    return t

# t_mu_INVALID = r'.'

def t_par_PARTIAL_NAME(t):
    r'[a-zA-Z0-9_$-/]+'
    t.lexer.pop_state()
    return t

t_par_ignore = ' \t\n'

# def t_EOF
def t_error(t):
    # print "Illegal character '%s'" % t.value[0]
    # Fall back to a mustach if we don't find any plain content (we should be
    # sitting on '{{')
    assert t.value[:2] == '{{' or len(t.value) == 0
    t.lexer.push_state('mu')

def t_mu_error(t):
    print "Illegal character '%s'" % t.value[0]
    t.lexer.skip(1)

t_emu_error = t_mu_error
t_par_error = t_mu_error
t_com_error = t_mu_error

class ProgramNode(object):
    '''A list of statements, essentially. Plus fucked up semantics.'''
    def __init__(self, statements, inverse=[]):
        self.statements = statements
        self.inverse = ProgramNode(inverse) if len(inverse) > 0 else None
    
    def __repr__(self):
        return 'ProgramNode(%r, %r)' % (self.statements, self.inverse)

    def _repr_pretty_(self, p, cycle):
        if cycle:
            p.text('ProgramNode(<loop!>)')
        else:
            with p.group(4, 'ProgramNode(', ')'):
                p.pretty(self.statements)
                p.text(',')
                p.breakable()
                p.pretty(self.inverse)

    def __str__(self):
        string = ''.join([str(s) for s in self.statements])

        if self.inverse is not None:
            string += '{{else}}'
            # string += ''.join([str(s) for s in self.inverse])
            string += str(self.inverse)

        return string

    def eval(self, context):
        # TODO inverse?
        return ''.join([stmt.eval(context) for stmt in self.statements])

class MustacheNode(object):
    '''A templated value, with or without params.
    
    {{moosetachio}}
    {{stache fumanchu cop pencil}}
    '''
    def __init__(self, raw_params, hash, unescaped=False, block=True,
            inverse=False):
        self.params = raw_params
        self.hash = hash
        self.escaped = not unescaped
        self.block = block
        self.inverse = inverse
    
    def __repr__(self):
        return 'MustacheNode(%r, %r, unescaped=%r, block=%r, inverse=%r)' % (
            self.params, self.hash, not self.escaped, self.block, self.inverse)

    def _repr_pretty_(self, p, cycle):
        if cycle:
            p.text('MustacheNode(<loop!>)')
        else:
            with p.group(4, 'MustacheNode(', ')'):
                p.pretty(self.params)
                p.text(',')
                p.breakable()
                p.pretty(self.hash)
                p.text(',')
                p.breakable()
                p.text('unescaped=')
                p.pretty(self.block)
                p.breakable()
                p.text('block=')
                p.pretty(self.inverse)

    def __str__(self):
        # open, close = ('{{', '}}') if self.escaped else ('{{{', '}}}')
        if self.block:
            open, close = '{{#', '}}'
        elif self.inverse:
            open, close = '{{else}}', '}}'
        elif self.unescaped:
            open, close = '{{{', '}}}'
        else:
            open, close = '[[', ']]'
        content = ' '.join([str(p) for p in self.params])
        # TODO
        # if len(self.hash) > 0:
        #     content += ' '.join([str(h) for h in self.hash])
        hash = '' if self.hash is None else ' ' + str(self.hash)
        return '%s%s%s%s' % (open, content, hash, close)

    def eval(self, context):
        return None

class PartialNode(object):
    '''Render a partial, maybe with params.

    {{> partial}}
    {{> partial p1 p2}}
    '''

    '''
    self.partial_name is a SimpleNode(partial_name)
    self.context is an IdNode or None
    '''
    def __init__(self, partial_name, context):
        self.partial_name = partial_name
        self.context = context
    
    def __repr__(self):
        return 'PartialNode(%r, %r)' % (self.partial_name, self.context)

    def _repr_pretty_(self, p, cycle):
        if cycle:
            p.text('PartialNode(<loop!>)')
        else:
            with p.group(4, 'PartialNode(', ')'):
                p.pretty(self.partial_name)
                p.text(',')
                p.breakable()
                p.pretty(self.context)

    def __str__(self):
        ctx = str(self.context) if self.context else ''
        return '{{> %s%s}}' % (self.partial_name, ctx)

class BlockNode(object):
    '''A mustachioed block.

    {{mustache_me}}
        Put mustache here -> {{this}} <-
    {{/mustache_me}}
    '''
    def __init__(self, mustache, program, inverse, close):
        # TODO check open and close
        self.mustache = mustache
        self.program = program
        self.inverse = inverse
    
    def __repr__(self):
        return 'BlockNode(%r, %r, %r)' % (self.mustache, self.program,
            self.inverse)

    def _repr_pretty_(self, p, cycle):
        if cycle:
            p.text('BlockNode(<loop!>)')
        else:
            with p.group(4, 'BlockNode(', ')'):
                p.pretty(self.mustache)
                p.text(',')
                p.breakable()
                p.pretty(self.program)
                p.text(',')
                p.breakable()
                p.pretty(self.inverse)

    def __str__(self):
        program = str(self.program) if self.program is not None else ''
        inverse = str(self.inverse) if self.inverse is not None else ''
        # return '%s{{else%s}}%s' % (program, self.mustache, inverse)
        return '%s{{%s}}%s' % (program, self.mustache, inverse)

class IdNode(object):
    '''An identifier.

    Path segments are separated by '/' or '.'. They can have hypens, 'this',
    '..', literals, or numbers.

    Examples:
    foo.foo-bar
    404/../[foo bar]
    this/text
    '''
    def __init__(self, parts):
        self.parts = parts

    @staticmethod
    def _name(part):
        if ' ' in part:
            return '[%s]' % part
        else:
            return part

    def __repr__(self):
        return '/'.join([self._name(part) for part in self.parts])
        return "IdNode(%r)" % self.parts

    def _repr_pretty_(self, p, cycle):
        if cycle:
            p.text('IdNode(<loop!>)')
        else:
            with p.group(4, 'IdNode(', ')'):
                p.pretty(self.parts)

    def __str__(self):
        return '/'.join([str(part) for part in self.parts])

content, hash, partial_name, data, integer, boolean, comment, string = range(8)

class SimpleNode(object):
    """Holds a simple item, without children - content, hash, partial name,
    data, integer, boolean, or comment."""
    def __init__(self, obj, kind):
        self.obj = obj
        self.kind = kind

    def __repr__(self):
        return "SimpleNode(%r, %r)" % (self.obj, self.kind)

    def _repr_pretty_(self, p, cycle):
        if cycle:
            p.text('SimpleNode(<loop!>)')
        else:
            with p.group(4, 'SimpleNode(', ')'):
                p.pretty(self.obj)
                p.text(',')
                p.breakable()
                p.pretty(self.kind)

    def __str__(self):
        # TODO not sure about data, comment
        if self.kind in [content, partial_name, data, integer, boolean,
                comment, string]:
            return str(self.obj)
        else: # self.kind == hash:
            return ' '.join(['%=%' for k, v in self.obj])

PARSE_COMPAT, PARSE_CORRECT = range(2)
PARSE_STYLE = PARSE_CORRECT

def p_root(p):
    'root : program'
    # 'root : program EOF'
    p[0] = p[1]

def p_program_inverse(p):
    '''program : simpleInverse statements
               | simpleInverse
    '''
    if PARSE_STYLE == PARSE_CORRECT:
        raise Exception("%s without opening block" % p[1])
    inverse = p[2] if len(p) > 2 else []
    p[0] = ProgramNode([], inverse)

def p_empty(p):
    'empty :'
    pass

def p_program_statements(p):
    '''
    program : statements simpleInverse statements
            | statements
            | empty
    '''

    # PARSE_CORRECT style
    '''
    program : statements simpleInverse statements
            | statements simpleInverse
            | statements
            | empty
    '''

    '''Return a ProgramNode, the first argument being the statements to execute
    in the if branch, and the second being the statements to execute in the
    else branch.
    '''
    if PARSE_STYLE == PARSE_CORRECT and len(p) == 3:
        raise Exception("%s without closing block" % p[2])
    if len(p) == 2: # TODO empty
        arg = []
    elif len(p) == 3:
        # not saying this makes any sense
        arg = []
    else:
        arg = p[3]
    p[0] = ProgramNode(p[1], arg)

def p_statements(p):
    '''statements : statement
                  | statements statement
    '''
    p[0] = p[1:]

def p_statement_block(p):
    '''statement : openInverse program closeBlock
                 | openBlock program closeBlock
    '''
    if p[1] == t_mu_OPEN_BLOCK:
        primary, inverse = p[2], p[2].inverse
    else:
        primary, inverse = p[2].inverse, p[2]
    p[0] = BlockNode(p[1], primary, inverse, p[3])

def p_statement_stache(p):
    '''statement : mustache
                 | partial
    '''
    p[0] = p[1]

def p_statement_token(p):
    '''statement : CONTENT
                 | COMMENT
    '''
    p[0] = SimpleNode(p[1], comment if p[1].startswith('{{!') else content)

def p_open_block_1(p):
    '''openBlock : OPEN_BLOCK inMustache CLOSE'''
    p[0] = MustacheNode(p[2][0], p[2][1])

def p_open_block_2(p):
    '''openInverse : OPEN_INVERSE inMustache CLOSE'''
    p[0] = MustacheNode(p[2][0], p[2][1], inverse=True)

def p_close_block(p):
    '''closeBlock : OPEN_ENDBLOCK path CLOSE'''
    p[0] = p[2]

def p_mustache(p):
    '''mustache : OPEN inMustache CLOSE
                | OPEN_UNESCAPED inMustache CLOSE
    '''
    p[0] = MustacheNode(p[2][0], p[2][1], False if p[1] == '{{' else True,
        block=False)

def p_partial(p):
    '''partial : OPEN_PARTIAL partialName CLOSE
               | OPEN_PARTIAL partialName path CLOSE
    '''
    p[0] = PartialNode(p[2], p[3] if len(p) == 4 else None)

def p_simple_inverse(p):
    '''simpleInverse : OPEN_INVERSE CLOSE'''
    p[0] = None

def p_in_mustache(p):
    '''inMustache : path params hash
                  | path params
                  | path hash
                  | path
                  | DATA
    '''

    '''Returns a list of two elements - a list of the the path and params, then
    the hash if there is one, or None if there isn't.'''
    # path : [IdNode]
    # params : [SimpleNode(x)]
    # hash : SimpleNode(hash)
    # DATA : SimpleNode(data)
    l = len(p)
    if l == 4: # path params hash
        # p2 is a list of params
        p[0] = [[p[1]] + p[2], p[3]]
    elif l == 3: # path params | path hash
        if not isinstance(p[2], list): # path hash
            p[0] = [[p[1]], p[2]]
        else: # path params
            # p2 is a list of params
            p[0] = [[p[1]] + p[2], None]
    elif l == 2: # path | DATA
        if isinstance(p[1], IdNode): # path
            p[0] = [[p[1]], None]
        else: # DATA
            p[0] = [[SimpleNode(p[1], data)], None]

def p_params(p):
    '''params : params param
              | param
    '''
    # TODO combine with statements?
    p[0] = p[1:]

def p_param_path(p):
    '''param : path'''
    p[0] = p[1]

def p_param_string(p):
    '''param : STRING'''
    p[0] = SimpleNode(p[1], string)

def p_param_integer(p):
    '''param : INTEGER'''
    p[0] = SimpleNode(p[1], integer)

def p_param_boolean(p):
    '''param : BOOLEAN'''
    p[0] = SimpleNode(p[1], boolean)

def p_param_data(p):
    '''param : DATA'''
    p[0] = SimpleNode(p[1], data)

def p_hash(p):
    '''hash : hashSegments'''
    '''A list of key-value parameters to a mustache.

    A value can be a path, string, integer, boolean, or data (@...). In
    addition, partial names can be used without a key.

    After pirate is the hash:
    {{pirate beard=true name=scoundrel.name eyepatches=1 pirate_partial}}
    '''
    p[0] = SimpleNode(p[1], hash)

def p_hash_segments(p):
    '''hashSegments : hashSegments hashSegment
                    | hashSegment
    '''
    p[0] = p[1:] # TODO combine with above, append p2 to p1

def p_hash_segment_path(p):
    '''hashSegment : ID EQUALS path'''
    p[0] = [p[1], p[3]]

def p_hash_segment_string(p):
    '''hashSegment : ID EQUALS STRING'''
    p[0] = [p[1], SimpleNode(p[3], string)]

def p_hash_segment_integer(p):
    '''hashSegment : ID EQUALS INTEGER'''
    p[0] = [p[1], SimpleNode(p[3], integer)]

def p_hash_segment_boolean(p):
    '''hashSegment : ID EQUALS BOOLEAN'''
    p[0] = [p[1], SimpleNode(p[3], boolean)]

def p_hash_segment_data(p):
    '''hashSegment : ID EQUALS DATA'''
    p[0] = [p[1], SimpleNode(p[3], data)]

def p_partial_name(p):
    '''partialName : PARTIAL_NAME'''
    p[0] = SimpleNode(p[1], partial_name)

def p_path(p):
    '''path : pathSegments'''
    p[0] = IdNode(p[1])

def p_path_segments(p):
    '''pathSegments : pathSegments SEP ID
                    | ID
    '''
    if len(p) == 4:
        seg = p[1]
        seg.push(p[3])
    else:
        seg = [p[1]]
    p[0] = seg

def compile(template):
    lex.lex()
    # lex.lexer.push_state('mu')
    lex.input(template)
    while 1:
        tok = lex.token()
        if not tok: break
        print tok
    yacc.yacc()
    return yacc.parse(template)

if __name__ == '__main__':
    # print compile("test")
    x = compile("{{#if nothing}}Scratchpad{{else}}{{# complicated}}{{> partial}}{{/complicated}}{{/if}}")
    # print "%s\n%r" % (x, x)
    pretty.pprint(x, max_width=60)
