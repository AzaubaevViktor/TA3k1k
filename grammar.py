import json
from copy import copy


def clear_arr(arr):
    return [x for x in arr if x]


class GrammarException(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return "Ошибка при составлении грамматики: {}".format(self.msg)


class ParserException(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return "Ошибка при разборе: {}".format(self.msg)


class Parser:
    # TODO: Дополнить
    """
    Класс парсер
    На вход подаются примитивы в виде списка:

    """

    def __init__(self, primitives: dict):
        self.primitives = primitives
        self.primitives[" "] = False
        self.raises = None
        self._tokens = []

    def parse(self, string: str) -> list:
        self._tokens = []
        if self._parse(string):
            tokens = copy(self._tokens)
            self._tokens = []
            return tokens
        else:
            raise self.raises

    def _parse(self, string: str):
        if not string:
            return True

        for k, v in self.primitives.items():
            if string.find(k) == 0:
                self._tokens.append(v)
                if self._parse(string[len(k):]):
                    return True
                else:
                    self._tokens.pop()
        self.raises = ParserException("Ошибка при разборе подстроки `{}`".format(
                string
        ))


class FirstTable:
    def __init__(self):
        self.table = {}

    def __getitem__(self, item) -> set:
        if isinstance(item, str):
            return self.table[item]

        elif isinstance(item, list):
            tokens = item
            intersect = set(self.table[tokens[0]])
            all_tokens = set()
            for token in tokens:
                intersect.intersection_update(self.table[token])
                all_tokens.update(self.table[token].difference({False}))
                if False not in self.table[token]:
                    break
            all_tokens.update(intersect)
            return all_tokens

    def __setitem__(self, key: str, value: set):
        self.table[key] = value

    def keys(self):
        return self.table.keys()

    def __str__(self) -> str:
        return str(self.table)

    def items(self):
        return self.table.items()


class Grammar:
    """
    Класс-анализатор контекстно-свободных грамматик
    """
    ARROW = 0
    OR = 1

    def __init__(self, grammar):
        """
        Формальная грамматика (англ. Formal grammar) — способ описания формального языка, представляющий собой четверку
        Γ =<Σ, N, S ∈ N, P ⊂ N⁺ × (Σ ∪ N)^*>,
        где
        Σ — алфавит, элементы которого называют терминалами (англ. terminals),
            В данном классе представлено множеством self.terminals
        N — множество, элементы которого называют нетерминалами (англ. nonterminals),
            В данном классе представлено множеством self.nonterminals
        S — начальный символ грамматики (англ. start symbol),
            В данном классе это будет нетерминал '$' (правосторонний) или первый нетерминальный символ (левосторонний)
        P — набор правил вывода (англ. production rules или productions) \alpha\rightarrow \beta.
            В данном классе представлено множеством self.rules

        :param grammar: Грамматика в виде словаря
        :return:
        """
        self.terminals = set(grammar.get('terminal', "").split(" "))
        self.nonterminals = grammar.get('nonterminal', "").split(" ")
        self.start_symbol = self.nonterminals[0]
        self.nonterminals = set(self.nonterminals)
        self.nonterminals.update(self.start_symbol)
        self.alphabet = self.terminals.union(self.nonterminals)
        self.rules = []

        self._parse_rules(grammar.get('rules', []))

        # Ограничение на длинну магазина
        self.max_mem_len = max([r.rel_len for r in self.rules]) * len(self.rules) * 10
        self.cur_max_mem = self.max_mem_len
        self._derivations = []

        self.parser = Parser({k: k for k in self.terminals})
        self.first_table = FirstTable()
        self.follow_table = {}

    def _check(self):
        term_nonterms = self.terminals.intersection(self.nonterminals)
        if term_nonterms:
            raise GrammarException("символы {} являются одновременно терминалами и нетерминалами".format(term_nonterms))

    def _parse_rules(self, rules):
        primitives = {k: k for k in self.alphabet}
        primitives["->"] = self.ARROW
        primitives["|"] = self.OR

        parser = Parser(primitives)
        for rule in rules:
            tokens = parser.parse(rule)
            try:
                arrow_index = tokens.index(self.ARROW)
            except ValueError:
                raise GrammarException("В правиле `{rule}` не найдена `->`".format(
                        rule=rule
                ))
            rule_head = tokens[:arrow_index]
            rule_body = tokens[arrow_index + 1:]

            while 1:
                try:
                    or_index = rule_body.index(self.OR)
                except ValueError:
                    break
                subrule_body = rule_body[:or_index]
                rule_body = rule_body[or_index + 1:]

                self.rules.append(Rule(self, rule_head, subrule_body))

            self.rules.append(Rule(self, rule_head, rule_body))

    def add_derivation(self, tokens, memory, cause):
        self._derivations.append((copy(tokens), copy(memory), cause))

    def _parse_string(self, string: str) -> list:
        return clear_arr(self.parser.parse(string))

    def _prepare(self, string: str) -> list:
        tokens = self._parse_string(string)
        self.cur_max_mem = self.max_mem_len * len(tokens)
        self._derivations = []
        return tokens

    def leftmost(self, string: str):
        self._leftmost(self._prepare(string), [self.start_symbol])

    def _leftmost(self, tokens, memory):
        if len(memory) > self.cur_max_mem:
            return False

        if not tokens and not memory:
            self.add_derivation(tokens, memory, "Преобразование окончено")
            return True

        if tokens \
                and memory \
                and memory[0] in self.terminals \
                and memory[0] == tokens[0]:
            if self._leftmost(tokens[1:], memory[1:]):
                self.add_derivation(tokens, memory, "Удаление токена `{}`".format(memory[0]))
                return True

        if memory:
            for rule in self.rules:
                _memory = rule.left_replace(memory)
                if _memory is not None:
                    if self._leftmost(tokens, _memory):
                        self.add_derivation(tokens, memory, str(rule))
                        return True
        return False

    def rightmost(self, string: str):
        self.used_empty_rules = False
        self._rightmost(self._prepare(string), ['$'])

    def _rightmost(self, tokens: list, memory: list):
        if len(memory) > self.cur_max_mem:
            return False

        if not tokens \
                and memory == ['$', self.start_symbol]:
            self.add_derivation(tokens, memory, 'Преобразование окончено')
            return True

        if memory:
            for rule in self.rules:
                if rule.is_empty_body:
                    continue
                _memory = rule.right_replace(memory)
                if _memory is not None:
                    if self._rightmost(tokens, _memory):
                        self.add_derivation(tokens, memory, str(rule))
                        return True

        if tokens:
            if self._rightmost(tokens[1:], memory + [tokens[0]]):
                self.add_derivation(tokens, memory, "Перенос токена `{}` в магазин".format(tokens[0]))
                return True

        # для пустых правил
        if memory:
            for rule in self.rules:
                if rule.is_empty_body and not self.used_empty_rules:
                    self.used_empty_rules = True
                    _memory = rule.right_replace(memory)
                    if _memory is not None:
                        if self._rightmost(tokens, _memory):
                            self.add_derivation(tokens, memory, str(rule))
                            self.used_empty_rules = False
                            return True
                    self.used_empty_rules = False

        return False

    def print_derivations(self):
        tok_len = 0
        mem_len = 0
        if not self._derivations:
            print("Не удалось распознать строку")

        for tok, mem, cause in self._derivations[::-1]:
            tok_str = "T: `{}`".format(" ".join(tok))
            if tok_len < len(tok_str):
                tok_len = len(tok_str)

            mem_str = "M: `{}`".format(" ".join(mem))
            if mem_len < len(mem_str):
                mem_len = len(mem_str)

            fmt = "{:" + str(tok_len) + "} | {:" + str(mem_len) + "} | {cause}"

            print(fmt.format(
                    tok_str,
                    mem_str,
                    cause=cause
            ))

    def _create_first_table(self):
        # False -- empty
        # '$' -- end
        for term in self.terminals:
            self.first_table[term] = {term}

        for nterm in self.nonterminals:
            self.first_table[nterm] = set()

        for rule in self.rules:
            if rule.head_len != 1:
                raise GrammarException("Невозможно применить FIRST FOLLOW, заоловок правила {} "
                                       "состоит больше, чем из одного токена".format(rule))
            if not rule.body:
                self.first_table[rule.head[0]].update([False])

        is_added = True
        while is_added:
            is_added = False
            for rule in self.rules:
                nterm = rule.head[0]
                # Добавляем
                for token in rule.body:
                    diff = self.first_table[token].difference(self.first_table[nterm])
                    if diff:
                        self.first_table[nterm].update(diff)
                        is_added = True

                    if False not in self.first_table[token]:
                        break

    def _check_first_follow_table(self):
        for rule1 in self.rules:
            for rule2 in self.rules:
                if rule1 != rule2 and rule1.head == rule2.head:
                    a = rule1.body
                    b = rule2.body
                    if not a or not b:
                        continue

                    fia = self.first_table[a]
                    fib = self.first_table[b]
                    foA = self.follow_table[rule1.head[0]]

                    if fia.intersection(fib):
                        print("Правила `{}` и `{}`".format(rule1, rule2))
                        return False

                    if False in fib:
                        if fia.intersection(foA):
                            print("Правила `{}` и `{}`".format(rule1, rule2))
                            return False
        return True

    def _create_follow_table(self):
        # 1 Step
        for nterm in self.nonterminals:
            self.follow_table[nterm] = set()

        self.follow_table[self.start_symbol] = set('$')

        is_added = True
        while is_added:
            is_added = False

            for rule in self.rules:
                # 3 Step 2 part
                try:
                    token = rule.body[-1]
                    if token in self.nonterminals:
                        diff = self.follow_table[rule.head[0]].difference(self.follow_table[token])
                        if diff:
                            is_added = True
                            self.follow_table[token].update(diff)
                except IndexError:
                    pass

                if rule.body_len == 0:
                    continue

                for i in range(len(rule.body) - 1):
                    nterm = rule.body[i]
                    if nterm in self.nonterminals:
                        # 2 Step
                        to_follow = self.first_table[rule.body[i+1:]]
                        if False in to_follow:
                            # 3 Step 2 part
                            diff = self.follow_table[rule.head[0]].difference(self.follow_table[nterm])
                            if diff:
                                is_added = True
                                self.follow_table[nterm].update(diff)

                        to_follow.difference_update({False})
                        diff = to_follow.difference(self.follow_table[nterm])
                        if diff:
                            is_added = True
                            self.follow_table[nterm].update(diff)

    def _create_syntax_table(self):
        M = {}
        for rule in self.rules:
            if not rule.body and '$' in self.follow_table[rule.head[0]]:
                for token in self.follow_table[rule.head[0]]:
                    M[(rule.head[0], token)] = rule
                continue

            for a in (self.first_table[rule.body] - {False}):
                M[(rule.head[0], a)] = rule

            if False in self.first_table[rule.body]:
                for term in self.follow_table[rule.head[0]]:
                    M[(rule.head[0], term)] = rule

        self.syntax_table = M

    def ll1(self, string: str):
        tokens = self._parse_string(string)
        tokens.append('$')
        stack = ['$', self.start_symbol]
        ip = 0
        while stack[-1] != '$':
            print(stack, tokens[ip:], end=" ")
            try:
                rule = self.syntax_table[(stack[-1], tokens[ip])]
            except KeyError:
                rule = None

            if stack[-1] == tokens[ip]:
                stack.pop()
                ip += 1
                print("ip++")
            elif stack[-1] in self.terminals:
                raise GrammarException("Ошибка при распознавании")
            elif not rule:
                raise GrammarException("Не найдено правило для (`{}`, `{}`)".format(stack[-1], tokens[ip]))
            else:
                print("Use {}".format(rule))
                stack.pop()
                stack.extend(rule.body[::-1])

        return True





class Rule:
    """
    Класс, реализущий правило
    """

    def __init__(self, grammar: Grammar, head: list, body: list):
        """

        :param grammar: Грамматика, частью которой является правило
        :param head: Левая часть (заголовок) правила
        :param body: Правая часть (тело) правила
        :return:
        """
        self.grammar = grammar
        self.head = head
        self.head_len = len(head)
        self.body = body
        self.body_len = len(body)
        self.is_empty_body = len(body) == 0

        # Прирост на символ при обработке правила
        self.rel_len = len(self.body) / self.head_len

        self._check(self.head)
        self._check(self.body)

    def _check(self, side):
        for symbol in side:
            if symbol not in self.grammar.alphabet:
                raise GrammarException(
                        "В правиле {rule} символ `{sym}` не является частью алфавита".format(
                                rule=str(self),
                                sym=symbol
                        )
                )

    def left_replace(self, tokens: list) -> list:
        """
        При совпадении заменяет СЛЕВА токены в соотв. с правилом и возвращает результат
        Заменяет ЗАГОЛОВОК на ТЕЛО
        :param tokens: Список входных токенов на проверку и замену
        :return: list с замененёнными первыми токенами в соответствии с правилом
        """
        if len(tokens) < self.head_len:
            return None

        for t, ts in zip(tokens, self.head):
            if t != ts:
                return None

        return self.body + tokens[self.head_len:]

    def right_replace(self, tokens: list) -> list:
        """
        При совпадении заменяет СПРАВА токены в соотв. с правилом и возвращает результат
        Заменяет ТЕЛО на ЗАГОЛОВОК
        :param tokens: Список входных токенов на проверку и замену
        :return: list с замененёнными последними токенами в соответствии с правилом
        """
        if len(tokens) < self.body_len:
            return None

        for t, ts in zip(tokens[len(tokens) - self.body_len:],
                         self.body):
            if t != ts:
                return None

        return tokens[:len(tokens) - self.body_len] + self.head

    def __str__(self):
        return "{} -> {}".format(" ".join(self.head), " ".join(self.body))

    def __repr__(self):
        return str(self)


if __name__ == "__main__":
    file = json.load(open('brackets.json', 'rt'))
    grammar = Grammar(file)
    string = input("Введите распознаваемую строку:")

    print("============ Левосторонний разбор ============")
    grammar.leftmost(string)
    grammar.print_derivations()
    print("============ Правосторонний разбор ===========")
    grammar.rightmost(string)
    grammar.print_derivations()

    print("================ FIRST FOLLOW ================")
    grammar._create_first_table()
    print("FIRST:")
    for k, v in grammar.first_table.items():
        print("{}: {}".format(k, v))
    # print("id):", grammar.first_table[['id', ')']])
    # print("E'T':", grammar.first_table[["E'", "T'"]])

    grammar._create_follow_table()
    print("FOLLOW:")
    for k, v in grammar.follow_table.items():
        print("{}: {}".format(k, v))

    if grammar._check_first_follow_table():
        print("Это LL(1) грамматика")
    else:
        print("Это не LL(1) грамматика")
        exit()

    grammar._create_syntax_table()
    print("M:")
    print(grammar.syntax_table)

    print("LL(1):")
    try:
        if grammar.ll1(string):
            print("Распознал!")
    except GrammarException as e:
        print(e)

