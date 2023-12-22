# This file is part of IPPDDL Parser, available at <https://github.com/AndreMoukarzel/ippddl-parser/>.

import random
import itertools
from typing import List, Tuple, Dict, Set
from fractions import Fraction


def frozenset_of_tuples(data):
    return frozenset([tuple(t) for t in data])


class Action:
    """Action with probabilistic effects
    """

    def __init__(
            self,
            name: str,
            parameters: List[List[str]],
            positive_preconditions: List[List[str]],
            negative_preconditions: List[List[str]],
            add_effects: List[List[List[str]]],
            del_effects: List[List[List[str]]],
            probabilities: List[Fraction]=[]
        ) -> None:
        """Instantiates an Action

        Parameters
        ----------
        name: str
            Identifier of the Action
        parameters: List[List[str]]
            List with each related object and their type in format
            [object name, object type]
        positive_preconditions: List[List[str]]
            List with positive preconditions' names and related objects in
            format [name, obj1, obj2, ...].
        negative_preconditions: List[List[str]]
            List with negative preconditions' names and related objects in
            format [name, obj1, obj2, ...].
        add_effects: List[List[List[str]]]
            List of each list of positive effects possible. More than one set of
            effects can be the result or probabilistic actions.
        del_effects: List[List[List[str]]]
            List of each list of deletion effects possible. More than one set of
            effects can be the result or probabilistic actions.
        probabilities: List[Fraction], optional
            Probability of each of the listed add_effects and del_effects pairs
            to occur. If not specified, assumes the action is deterministic and
            therefore all probabilities are 1.0
        """
        self.name = name
        self.parameters = tuple(parameters)  # Make parameters a tuple so we can hash this if need be
        self.positive_preconditions = frozenset_of_tuples(positive_preconditions)
        self.negative_preconditions = frozenset_of_tuples(negative_preconditions)
        self.add_effects = [frozenset_of_tuples(add_effs) for add_effs in add_effects]
        self.del_effects = [frozenset_of_tuples(del_effs) for del_effs in del_effects]
        self.raw_probabilities = probabilities
        self.probabilities = probabilities
        if len(probabilities) == 0: # If no probability is specified, assumes action is deterministic
            # Sets all effects to have 100% chance of occuring.
            self.raw_probabilities = [1.0 for _ in add_effects]
        # For imprecise probabilities, given as an interval of values, settles them into a usable probability
        self.settle_imprecise_probabilities()


    def __str__(self) -> str:
        return_str = 'action: ' + self.name + \
            '\n  parameters: ' + str(list(self.parameters)) + \
            '\n  positive_preconditions: ' + str([list(i) for i in self.positive_preconditions]) + \
            '\n  negative_preconditions: ' + str([list(i) for i in self.negative_preconditions]) + \
            '\n  effects:'
        for i, prob in enumerate(self.raw_probabilities):
            if isinstance(prob, tuple):
                settled_prob = float(self.probabilities[i])
                return_str += f"\n\t({', '.join([str(val) for val in prob])}) | Current Value: {round(settled_prob, 2)}"
            else:
                return_str += f'\n\t{prob}'
            
            return_str += f'\n\t  positive effects: {str([list(eff) for eff in self.add_effects[i]])}' + \
                          f'\n\t  negative effects: {str([list(eff) for eff in self.del_effects[i]])}'
        return return_str + '\n'


    def __eq__(self, other) -> bool:
        if self.name == other.name and self.parameters == other.parameters \
            and self.positive_preconditions == other.positive_preconditions \
            and self.negative_preconditions == other.negative_preconditions \
            and self.add_effects == other.add_effects and self.del_effects == other.del_effects \
            and self.raw_probabilities == other.raw_probabilities:
            return True
        return False
    

    def replace(self, group: frozenset, variables: List[str], assignment: Tuple[str]) -> List[List[str]]:
        """Replaces the variables of predicates specified in group with the
        values specified in assignment.
         
        Parameters
        ----------
        group: frozenset
            Set of predicates.
        variables: List[str]
            List of variables present in the predicates from group.
        assignment: Tuple[str]
            Tuple of values to assign to the variables.
        
        Returns
        -------
        new_group: List[List[str]]
            List with each of the predicates with its variables' values set as
            the assignments, transforming them into propositions.
        """
        new_group: List[List[str]] = []
        for pred in group:
            pred = list(pred)
            for i, p in enumerate(pred):
                if p in variables:
                    pred[i] = assignment[variables.index(p)]
            new_group.append(pred)
        return new_group


    def replace_effects(self, effects: List[frozenset], variables: List[str], assignment: Tuple[str], connections: Dict[str, Set[str]]) -> Tuple[List[List[List[str]]], List[float]]:
        """Replaces the variables of predicates specified in effects with the
        values specified in assignment.
         
        Parameters
        ----------
        effects: List[frozenset]
            List with all sets of predicates representing the effects of
            possible outcomes of this Action.
        variables: List[str]
            List of variables present in the predicates from group.
        assignment: Tuple[str]
            Tuple of values to assign to the variables.
        connections: Dict[str, Set[str]]
            Dictionary with connections between computers in a SysAdmin problem.
            Used only with Actions from a SysAdmin problem domain.
        
        Returns
        -------
        new_effects: List[List[List[str]]]
            List of lists with each of the predicates with its variables' values
            set as the assignments, transforming them into propositions.
        related_probabilities: List[float]
            List of the probabilities of each list of predicates occuring.
        """
        new_effects: List[List[List[str]]] = []
        related_probabilities: List[float] = []
        for i, eff in enumerate(effects):
            prob = self.probabilities[i]
            if ('sysadmin_forall',) in eff: # Special effect of SysAdmin domain
                replaced_eff = []
                for comp in connections[assignment[0]]:
                    replaced_eff.append(('up', comp))
            else:
                replaced_eff = self.replace(eff, variables, assignment)
            new_effects.append(replaced_eff)
            related_probabilities.append(prob)
        return new_effects, related_probabilities


    def groundify(self, objects: Dict[str, List[str]], types: Dict[str, List[str]], connections: Dict[str, Set[str]]=None):
        """Applies the given objects and their types to this action, yielding
        all possible grounded actions.

        Parameters
        ----------
        objects: Dict[str, List[str]]
            Dictionary where the keys are the arguments of the un-grounded action
            and the values are a list of all possible values of such arguments.
        types: Dict[str, List[str]]
            Dictionary where the keys are the possible object types and the
            values are the arguments that belong to such type. Honestly, I don't
            know if this even does anything.
        connections: Dict[str, Set[str]]
            Dictionary with connections between computers in a SysAdmin problem.
            Used only with Actions from a SysAdmin problem domain.
        """
        if not self.parameters:
            yield self
            return
        type_map = []
        variables = []
        for var, type in self.parameters:
            type_stack = [type]
            items = []
            while type_stack:
                t = type_stack.pop()
                if t in objects:
                    items += objects[t]
                if t in types:
                    type_stack += types[t]
            type_map.append(items)
            variables.append(var)
        for assignment in itertools.product(*type_map):
            positive_preconditions = self.replace(self.positive_preconditions, variables, assignment)
            negative_preconditions = self.replace(self.negative_preconditions, variables, assignment)
            add_effects, probs = self.replace_effects(self.add_effects, variables, assignment, connections)
            del_effects, _ = self.replace_effects(self.del_effects, variables, assignment, connections)
            yield Action(self.name, assignment, positive_preconditions, negative_preconditions, add_effects, del_effects, probs)
    

    def is_applicable(self, state: frozenset) -> bool:
        """Returns if the action is applicable in the specified state.
        
        The state is expected to be a set of predicates."""
        return self.positive_preconditions.issubset(state) and self.negative_preconditions.isdisjoint(state)


    def settle_imprecise_probabilities(self):
        """Settles imprecise probabilities into a valid value contained into the
        specified intervals. Can be re-used to change the settled probabilities.
        """
        precise_sum: float = 0.0 
        self.probabilities = [0.0] * len(self.raw_probabilities)
        for i, prob in enumerate(self.raw_probabilities):
            # Precise probabilities do not need to be settled, so they are resolved first
            if not isinstance(prob, tuple): 
                self.probabilities[i] = prob
                precise_sum += prob
        
        for i, prob in enumerate(self.raw_probabilities):
            if isinstance(prob, tuple):
                settled_prob: float = random.uniform(prob[0], prob[1])
                self.probabilities[i] = Fraction(settled_prob)


    def get_possible_resulting_states(self, state: frozenset) -> Tuple[List[frozenset], List[float]]:
        """Gets all possible resulting states of applying this action to the
        specified state, and the probability of each occuring.
        
        Parameters
        ----------
        state: frozenset
            State to which this action will be applied to.
        
        Returns
        -------
        resulting_states: List[frozenset]
            List of possible states resulting from applying this action to state.
        probabilities: List[float]
            List of probabilities of reaching each of resulting_states.
        """
        if not self.is_applicable(state):
            return [state], [1.0]

        resulting_states: List[frozenset] = []
        probabilities: List[float] = []
        for i, prob in enumerate(self.probabilities):
            add_effects = self.add_effects[i]
            del_effects = self.del_effects[i]
            new_state = state.difference(del_effects).union(add_effects)
            # Sorts propositions to avoid multiple representations of same state
            new_state = frozenset_of_tuples(sorted(new_state))

            resulting_states.append(new_state)
            probabilities.append(prob)
        return resulting_states, probabilities
    

    def apply(self, state: frozenset) -> frozenset:
        """Applies the Action to the specified state, if applicable.

        Randomly chooses, according to the probabilities of each effect
        occuring, one of the possible states reachable by executing this
        action on the received state.
        
        Parameters
        ----------
        state: frozenset
            State to which this action will be applied to.
        
        Returns
        -------
        frozenset
            Resulting state.
        """
        if not self.is_applicable(state):
            return state
        possible_states, probs = self.get_possible_resulting_states(state)
        randf: float = random.uniform(0.0, 1.0)

        # Sorts possible states from lowest to highest probability
        states_and_probs = [(poss_state, prob) for poss_state, prob in sorted(zip(possible_states, probs), key=lambda pair: pair[0])]
        for poss_state, prob in states_and_probs:
            if randf <= prob:
                return poss_state
            randf: float = random.uniform(0.0, 1.0)
        return state



if __name__ == '__main__':
    a = Action('move', [['?ag', 'agent'], ['?from', 'pos'], ['?to', 'pos']],
                       [['at', '?ag', '?from'], ['adjacent', '?from', '?to']],
                       [['at', '?ag', '?to']],
                       [[['at', '?ag', '?to']]],
                       [[['at', '?ag', '?from']]])
    print(a)

    print("\n\n---------- Groundified ----------\n")
    objects = {
        'agent': ['ana', 'bob'],
        'pos': ['p1', 'p2']
    }
    types = {'object': ['agent', 'pos']}
    for act in a.groundify(objects, types):
        print(act)
