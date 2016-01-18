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
        self._tokens = []

    def parse(self, string: str) -> list:
        self._tokens = []
        if self._parse(string):
            tokens = copy(self._tokens)
            self._tokens = []
            return tokens
        else:
            return False

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
        raise ParserException("Ошибка при разборе подстроки `{}`".format(
                string
        ))


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

        primitives = {k: k for k in self.alphabet}
        primitives["->"] = self.ARROW
        primitives["|"] = self.OR

        parser = Parser(primitives)
        for rule in grammar.get("rules"):
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
        # Ограничение на длинну магазина
        self.max_mem_len = max([r.rel_len for r in self.rules]) * len(self.rules) * 10
        self.cur_max_mem = self.max_mem_len
        self._derivations = []

        self.parser = Parser({k: k for k in self.terminals})

    def _check(self):
        term_nonterms = self.terminals.intersection(self.nonterminals)
        if term_nonterms:
            raise GrammarException("символы {} являются одновременно терминалами и нетерминалами".format(term_nonterms))

    def add_derivation(self, tokens, memory, cause):
        self._derivations.append((copy(tokens), copy(memory), cause))

    def _prepare(self, string: str) -> list:
        tokens = self.parser.parse(string)
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


if __name__ == "__main__":
    file = json.load(open('palindrom.json', 'rt'))
    grammar = Grammar(file)
    string = input("Введите распознаваемую строку:")

    print("============ Левосторонний разбор ============")
    grammar.leftmost(string)
    grammar.print_derivations()
    print("============ Правосторонний разбор ===========")
    grammar.rightmost(string)
    grammar.print_derivations()

