# This file is part of IPPDDL Parser, available at <https://github.com/AndreMoukarzel/ippddl-parser/>.

import re

from .predicate import Predicate
from .action import Action


class DeterministicParser:

    SUPPORTED_REQUIREMENTS = [
        ':strips', ':negative-preconditions', ':typing', ':equality', ':rewards'
    ]


    def __init__(self, domain_filename=None, problem_filename=None) -> None:
        if domain_filename:
            self.scan_tokens(domain_filename)
        if problem_filename:
            self.scan_tokens(problem_filename)
        
        if domain_filename:
            self.parse_domain(domain_filename)
        if problem_filename:
            self.parse_problem(problem_filename)


    def scan_tokens(self, filename):
        with open(filename) as f:
            # Remove single line comments
            str = re.sub(r';.*$', '', f.read(), flags=re.MULTILINE).lower()
        # Tokenize
        stack = []
        list = []
        for t in re.findall(r'[()]|[^\s()]+', str):
            if t == '(':
                stack.append(list)
                list = []
            elif t == ')':
                if stack:
                    li = list
                    list = stack.pop()
                    list.append(li)
                else:
                    raise Exception('Missing open parentheses')
            else:
                list.append(t)
        if stack:
            raise Exception('Missing close parentheses')
        if len(list) != 1:
            raise Exception('Malformed expression')
        return list[0]


    def parse_domain(self, domain_filename, requirements=SUPPORTED_REQUIREMENTS):
        tokens = self.scan_tokens(domain_filename)
        if type(tokens) is list and tokens.pop(0) == 'define':
            self.domain_name = None
            self.requirements = []
            self.types = {}
            self.objects = {}
            self.actions = []
            self.predicates = []
            while tokens:
                group = tokens.pop(0)
                t = group.pop(0)
                if t == 'domain':
                    self.domain_name = group[0]
                elif t == ':requirements':
                    for req in group:
                        if req not in requirements:
                            raise Exception('Requirement ' + req + ' not supported')
                    self.requirements = group
                elif t == ':constants':
                    self.parse_objects(group, t)
                elif t == ':predicates':
                    self.parse_predicates(group)
                elif t == ':types':
                    self.parse_types(group)
                elif t == ':action':
                    self.parse_action(group)
                else: self.parse_domain_extended(t, group)
        else:
            raise Exception('File ' + domain_filename + ' does not match domain pattern')

    def parse_domain_extended(self, t, group):
        print(str(t) + ' is not recognized in domain')


    def parse_hierarchy(self, group, structure, name, redefine):
        list = []
        while group:
            if redefine and group[0] in structure:
                raise Exception('Redefined supertype of ' + group[0])
            elif group[0] == '-':
                if not list:
                    raise Exception('Unexpected hyphen in ' + name)
                group.pop(0)
                type = group.pop(0)
                if type not in structure:
                    structure[type] = []
                structure[type] += list
                list = []
            else:
                list.append(group.pop(0))
        if list:
            if 'object' not in structure:
                structure['object'] = []
            structure['object'] += list


    def parse_objects(self, group, name):
        self.parse_hierarchy(group, self.objects, name, False)


    def parse_types(self, group):
        self.parse_hierarchy(group, self.types, 'types', True)


    def parse_predicates(self, group):
        for pred in group:
            predicate_name = pred.pop(0)
            for predicate in self.predicates:
                if predicate.name == predicate_name:
                    raise Exception('Predicate ' + predicate_name + ' redefined')
            arguments = {}
            untyped_variables = []
            while pred:
                t = pred.pop(0)
                if t == '-':
                    if not untyped_variables:
                        raise Exception('Unexpected hyphen in predicates')
                    type = pred.pop(0)
                    while untyped_variables:
                        arguments[untyped_variables.pop(0)] = type
                else:
                    untyped_variables.append(t)
            while untyped_variables:
                arguments[untyped_variables.pop(0)] = 'object'
            
            predicate = Predicate(predicate_name, arguments)
            self.predicates.append(predicate)
    

    def parse_action_parameters(self, unparsed_parameters, action_name):
        parameters = []
        untyped_parameters = []
        while unparsed_parameters:
            t = unparsed_parameters.pop(0)
            if t == '-':
                if not untyped_parameters:
                    raise Exception('Unexpected hyphen in ' + action_name + ' parameters')
                ptype = unparsed_parameters.pop(0)
                while untyped_parameters:
                    parameters.append([untyped_parameters.pop(0), ptype])
            else:
                untyped_parameters.append(t)
        while untyped_parameters:
            parameters.append([untyped_parameters.pop(0), 'object'])
        
        return parameters


    def parse_action_effects(self, effects, action_name):
        """Parses the effects of an action.

        The base parser is used in deterministic problems, and therefore all
        actions are assumed to have only one possible outcome with add and del
        effects
        """
        add_effects = []
        del_effects = []

        # Since the action is deterministic, we hardset its probability of happening to 100%
        self.split_predicates(effects, add_effects, del_effects, action_name, ' effects')
        add_effects = [add_effects]
        del_effects = [del_effects]
        
        return add_effects, del_effects


    def parse_action(self, group):
        name = group.pop(0)
        if type(name) is not str:
            raise Exception('Action without name definition')
        for act in self.actions:
            if act.name == name:
                raise Exception('Action ' + name + ' redefined')
        parameters = []
        positive_preconditions = []
        negative_preconditions = []
        extensions = []
        add_effects = []
        del_effects = []
        while group:
            t = group.pop(0)
            if t == ':parameters':
                if type(group) is not list:
                    raise Exception('Error with ' + name + ' parameters')
                unparsed_parameters = group.pop(0)
                parameters = self.parse_action_parameters(unparsed_parameters, name)
            elif t == ':precondition':
                self.split_predicates(group.pop(0), positive_preconditions, negative_preconditions, name, ' preconditions')
            elif t == ':effect':
                effects: str = group.pop(0)
                add_effects, del_effects = self.parse_action_effects(effects, name)
            else:
                group.insert(0, t)
                extensions.append(group)
        
        action = Action(name, parameters, positive_preconditions, negative_preconditions, add_effects, del_effects)
        self.parse_action_extended(action, extensions)
        self.actions.append(action)


    def parse_action_extended(self, action, group):
        while group:
            t = group.pop(0)
            print(str(t) + ' is not recognized in action ' + action.name)
    

    def add_objects_equality(self, group):
        """Adds equality predicates for all objects in group and returns
        the completed group"""
        equality_preds = []
        for objs in self.objects.values():
            for obj in objs:
                equality_preds.append(['equal', obj, obj])
        return group + equality_preds


    def parse_problem(self, problem_filename):
        def frozenset_of_tuples(data):
            return frozenset([tuple(t) for t in data])
        tokens = self.scan_tokens(problem_filename)
        if type(tokens) is list and tokens.pop(0) == 'define':
            self.problem_name = None
            self.state = frozenset()
            self.positive_goals = frozenset()
            self.negative_goals = frozenset()
            while tokens:
                group = tokens.pop(0)
                t = group.pop(0)
                if t == 'problem':
                    self.problem_name = group[0]
                elif t == ':domain':
                    if self.domain_name != group[0]:
                        raise Exception('Different domain specified in problem file')
                elif t == ':requirements':
                    pass  # Ignore requirements in problem, parse them in the domain
                elif t == ':objects':
                    self.parse_objects(group, t)
                elif t == ':init':
                    if ':equality' in set(self.requirements):
                        group = self.add_objects_equality(group)
                    self.state = frozenset_of_tuples(group)
                elif t == ':goal':
                    positive_goals = []
                    negative_goals = []
                    self.split_predicates(group[0], positive_goals, negative_goals, '', 'goals')
                    self.positive_goals = frozenset_of_tuples(positive_goals)
                    self.negative_goals = frozenset_of_tuples(negative_goals)
                else: self.parse_problem_extended(t, group)
        else:
            raise Exception('File ' + problem_filename + ' does not match problem pattern')


    def parse_problem_extended(self, t, group):
        print(str(t) + ' is not recognized in problem')


    def split_predicates(self, group, positive, negative, name, part):
        if type(group) is not list:
            raise Exception('Error with ' + name + part)
        if group:
            if group[0] == 'and':
                group.pop(0)
            else:
                group = [group]
            for predicate in group:
                if predicate[0] == 'not':
                    if len(predicate) != 2:
                        raise Exception('Unexpected not in ' + name + part)
                    negative.append(predicate[-1])
                else:
                    positive.append(predicate)


if __name__ == '__main__':
    import sys, pprint
    domain = sys.argv[1]
    problem = sys.argv[2]
    parser = DeterministicParser()
    print('----------------------------')
    pprint.pprint(parser.scan_tokens(domain))
    print('----------------------------')
    pprint.pprint(parser.scan_tokens(problem))
    print('----------------------------')
    parser.parse_domain(domain)
    parser.parse_problem(problem)
    print('Domain name: ' + str(parser.domain_name))
    for act in parser.actions:
        print(act)
    print('----------------------------')
    print('Problem name: ' + str(parser.problem_name))
    print('Objects: ' + str(parser.objects))
    print('State: ' + str([list(i) for i in parser.state]))
    print('Positive goals: ' + str([list(i) for i in parser.positive_goals]))
    print('Negative goals: ' + str([list(i) for i in parser.negative_goals]))
