import copy
import re
from ptree import PTree, Node


def create_sq_table(obs_seq, type_of_table):
    """
    Given an observation sequence (a list of words), creates a square table
    with cells represented as some iterable. For the cky_parser algorithm.
    """
    table = [[]]
    for o in obs_seq:
        table.append([])
    for row in table:
        row.append(copy.deepcopy(type_of_table))
        for o in obs_seq:
            row.append(copy.deepcopy(type_of_table))
    return table


def list_powerset(lst):
    output = [[]]
    for e in lst:
        output.extend([subset + [e] for subset in output])
    return output


class PRule(object):
    def __init__(self, variable, derivation, probability):
        self.variable = str(variable)
        self.derivation = tuple(derivation)
        self.probability = float(probability)

    def derivation_length(self):
        return len(self.derivation)

    def __repr__(self):
        compact_derivation = " ".join(self.derivation)
        return self.variable + ' -> ' + compact_derivation + ' (' + str(self.probability) + ')'

    def __eq__(self, other):
        try:
            return self.variable == other.variable and self.derivation == other.derivation
        except:
            return False


class PCFG(object):
    def __init__(self, start_variable='S', rules = None):
        if rules is None:
            self.rules = {}
        else:
            self.rules = copy.deepcopy(rules) # A dictionary that maps an str object to a list of PRule objects
        self.start = start_variable # Start symbol of the grammar

    def add_rule(self, rule):
        '''
        Adds a rule to dictionary of rules in grammar.
        '''
        if rule.variable not in self.rules:
            self.rules[rule.variable] = []
        self.rules[rule.variable].append(rule)

    def remove_rule(self, rule):
        '''
        Removes a rule from dictionary of rules in grammar.
        '''
        try:
            self.rules[rule.variable].remove(rule)
        except KeyError:
            pass
        except ValueError:
            pass
    
    def shorten_rule(self, rule, list_of_variables):
        """
        If the input rule has more than 2 symbols in its RHS, removes that rule 
        from the grammar and adds the requisite rules that emulate the long rule. 
        Does so recursively, so as to keep shortening rules with more than 3 symbols
        in their RHS. Uses a list of variables to keep track of new variable names.
        """
        if len(rule.derivation) > 2:
            variable_number = len(list_of_variables)
            new_variable = 'X' + str(variable_number)
            list_of_variables.append(new_variable)
            rule_for_iteration = PRule(new_variable, rule.derivation[1:], 1)
            self.add_rule(rule_for_iteration)
            self.add_rule(PRule(rule.variable, (rule.derivation[0], new_variable), rule.probability))
            self.remove_rule(rule)
            self.shorten_rule(rule_for_iteration, list_of_variables)
            
    def to_near_cnf(self):
        '''
        Returns an equivalent near-CNF grammar.
        
        Because the algorithm iterates over rule-dictionaries while at the same
        time updating them using add_rule and remove_rule, at each point wherein
        the function starts an iteration over a rule dictionary, a deepcopy of
        that that dictionary is updated instead of the dictionary that is iterated
        over. The 'original' dictionary is updated later.
        
        The first outermost 'for loop' is used to get rid of epsilon rules 
        (of the type A -> ""): to avoid the possibility of infinite loops, 
        list_of_epsilon_rules is used to remember which epsilon rules have already 
        been taken care of. New rules are added and old rules updated, 
        based on all rules in the dictionary which include the possibly 
        epsilon-valued variable (e.g., rules that have A in their derivation)
        To add new rules based on present rules, a superset (or 'superlist') of 
        index values is used: for a rule such as 'B -> A X Y A', for example,
        the superlist will allow for the addition of 3 new rules: one in which
        derivation[0] is removed; another in which derivation[3] is removed;
        and finally one in which both are removed. Of course, whenever a rule
        is removed or added, all of the variable's rules are normalized so that
        their new total probability mass equals 1.
        
        The second outermost 'for loop' is used to shorten all rules with
        derivation lengths bigger than 2. The recursive shorten_rule function
        is used.
        
        Finally, the third outermost 'for loop' checks if any of the rules
        with 2 RHS symbols include terminals; any such rules are removed and
        divided into new rules, so that all terminal derivations are unary.
        This works similarly to the shorten_rule function, but without the need for recursion.
        '''   
        changes_list = []
        near_cnf = PCFG('S0', self.rules)
        near_cnf.add_rule(PRule('S0', self.start, 1))
        near_cnf_copy_1 = copy.deepcopy(near_cnf)
        list_of_epsilon_rules = []
        for v1 in near_cnf.rules:
            for rule_1 in near_cnf.rules[v1]:
                if rule_1.derivation == ('',) and rule_1 not in list_of_epsilon_rules:
                    near_cnf_copy_1.remove_rule(rule_1)
                    list_of_epsilon_rules.append(rule_1)
                    for rule_2 in near_cnf_copy_1.rules[v1]:
                        new_probability = rule_2.probability / (1 - rule_1.probability)
                        rule_2.probability = new_probability
                    near_cnf_copy_2 = copy.deepcopy(near_cnf_copy_1)
                    for v2 in near_cnf_copy_1.rules:
                        for rule_3 in near_cnf_copy_1.rules[v2]:
                            if v1 in rule_3.derivation:
                                v1_index_list = []
                                for i in range(len(rule_3.derivation)):
                                    if rule_3.derivation[i] == v1:
                                        v1_index_list.append(i)
                                v1_index_powerlist = list_powerset(v1_index_list)
                                v1_index_powerlist.remove([])
                                for index_list in v1_index_powerlist:
                                    new_derivation_list = list(rule_3.derivation)
                                    for index in sorted(index_list, reverse = True):
                                        del new_derivation_list[index]
                                    new_probability = rule_3.probability * \
                                        (rule_1.probability ** len(index_list)) * \
                                            ((1 - rule_1.probability) ** new_derivation_list.count(v1))
                                    new_rule = PRule(v2, new_derivation_list, new_probability)
                                    if new_rule not in near_cnf_copy_1.rules[v2]:
                                        near_cnf_copy_2.add_rule(new_rule)
                                        changes_list.append(PCFGChange(new_rule, 'epsilon_rule', \
                                                                       info=(rule_3, index_list)))
                                        for rule_4 in near_cnf_copy_2.rules[v2]:
                                            updated_probability = rule_4.probability / (1 + new_probability)
                                            rule_4.probability = updated_probability
                                    else:
                                        for rule_4 in near_cnf_copy_2.rules[v2]:
                                            if new_rule == rule_4:
                                                updated_probability = rule_4.probability + new_probability
                                                rule_4.probability = updated_probability
                                                updated_probability = rule_4.probability / (1 + new_probability)
                                                rule_4.probability = updated_probability
                                            else:
                                                updated_probability = rule_4.probability / (1 + new_probability)
                                                rule_4.probability = updated_probability
                    near_cnf_copy_1.rules = near_cnf_copy_2.rules
        near_cnf.rules = near_cnf_copy_1.rules
        list_of_new_X_variables = []
        near_cnf_copy = copy.deepcopy(near_cnf)
        for v in near_cnf.rules:
            for rule in near_cnf.rules[v]:
                near_cnf_copy.shorten_rule(rule, list_of_new_X_variables)
        near_cnf.rules = near_cnf_copy.rules
        list_of_new_Y_variables = []
        near_cnf_copy = copy.deepcopy(near_cnf)
        for v in near_cnf.rules:
            for rule in near_cnf.rules[v]:
                if len(rule.derivation) == 2:
                    if rule.derivation[0] not in near_cnf.rules and rule.derivation[1] in near_cnf.rules:
                        new_variable = 'Y' + str(len(list_of_new_Y_variables))
                        list_of_new_Y_variables.append(new_variable)
                        near_cnf_copy.add_rule(PRule(new_variable, rule.derivation[0], 1))
                        near_cnf_copy.add_rule(PRule(v, (new_variable, rule.derivation[1]), rule.probability))
                        near_cnf_copy.remove_rule(rule)
                    if rule.derivation[0] in near_cnf.rules and rule.derivation[1] not in near_cnf.rules:
                        new_variable = 'Y' + str(len(list_of_new_Y_variables))
                        list_of_new_Y_variables.append(new_variable)
                        near_cnf_copy.add_rule(PRule(new_variable, rule.derivation[1], 1))
                        near_cnf_copy.add_rule(PRule(v, (rule.derivation[0], new_variable), rule.probability))
                        near_cnf_copy.remove_rule(rule)
                    if rule.derivation[0] not in near_cnf.rules and rule.derivation[1] not in near_cnf.rules:
                        new_variable_0 = 'Y' + str(len(list_of_new_Y_variables))
                        list_of_new_Y_variables.append(new_variable_0)
                        new_variable_1 = 'Y' + str(len(list_of_new_Y_variables))
                        list_of_new_Y_variables.append(new_variable_1)
                        near_cnf_copy.add_rule(PRule(new_variable_0, rule.derivation[0], 1))
                        near_cnf_copy.add_rule(PRule(new_variable_1, rule.derivation[1], 1))
                        near_cnf_copy.add_rule(PRule(v, (new_variable_0, new_variable_1), rule.probability))
                        near_cnf_copy.remove_rule(rule)
        near_cnf.rules = near_cnf_copy.rules
        return (near_cnf, changes_list)
    
    def unary_check(self, i, j, table, back, variable):
        """
        Recursively checks for rules with unary derivations and updates the cell
        of the table and backpointer appropriately. Variables reached from 
        unary derivations remain in the same cell. For cky_parser.
        """
        for v in self.rules:
            for rule in self.rules[v]:
                if len(rule.derivation) == 1:
                    if rule.derivation[0] in table[i][j]:
                        probability = rule.probability * table[i][j][rule.derivation[0]]
                        if v not in table[i][j]:
                            table[i][j][v] = probability
                            back[i][j][v] = (0, rule.derivation[0])
                            self.unary_check(i, j, table, back, v)
                        else: 
                            if table[i][j][v] < probability:
                                table[i][j][v] = probability
                                back[i][j][v] = (0, rule.derivation[0])
                                self.unary_check(i, j, table, back, v)
                                
    def tree_builder(self, i, j, back, current_node, obs_seq):
        """
        Recursively constructs a syntax tree using the Node class,
        relying on a backpointer table. The backpointer used should have
        dictionaries for cells, filled in with key-value pairs of the 
        following type: A : (0, X) or A : (k, X, Y), where A is some variable,
        X and Y are derivations from A (most often variables themselves), 
        and k is a number used to access the cells of the backpointer wherein 
        the derived nodes can be recursively constructed (when it comes to unary 
        derivations, k is 0; the variable's cell is also the derivation's). 
        The recursion is halted whenever the cell reached has no key for a 
        derived variable: when this happens, a terminal has been reached.
        """
        if current_node in back[i][j]:
            if len(back[i][j][current_node]) == 2:
                new_node = back[i][j][current_node][1]
                return Node(current_node, [self.tree_builder(i, j, back, new_node, obs_seq)])
            if len(back[i][j][current_node]) == 3:
                left_node = back[i][j][current_node][1]
                right_node = back[i][j][current_node][2]
                new_index = back[i][j][current_node][0]             
                return Node(current_node, \
                            [self.tree_builder(i, new_index, back, left_node, obs_seq), \
                             self.tree_builder(new_index, j, back, right_node, obs_seq)])
        else:
            return Node(current_node, [obs_seq[j-1]])
                        
    def cky_parser(self, string):
        '''
        Parses the input string given the grammar, using the probabilistic CKY algorithm.
        If the string has been generated by the grammar - returns a most likely parse tree for the input string.
        Otherwise - returns None.
        The CFG is given in near-CNF.
        '''
        obs_seq = string.split()
        obs_seq_length = len(obs_seq)
        table = create_sq_table(obs_seq, {})
        back = create_sq_table(obs_seq, {})
        for j in range(1, obs_seq_length+1):
            for v in self.rules:
                for rule in self.rules[v]:
                    if rule.derivation[0] == obs_seq[j-1]:
                        table[j-1][j][v] = rule.probability
                        self.unary_check(j-1, j, table, back, v)
            for i in range(j - 1, -1, -1):
                for k in range(i, j):
                    for v in self.rules:
                        for rule in self.rules[v]:
                            if len(rule.derivation) == 2:
                                if rule.derivation[0] in table[i][k] and rule.derivation[1] in table[k][j]:
                                    probability = rule.probability * table[i][k][rule.derivation[0]] \
                                        * table[k][j][rule.derivation[1]]
                                    if v not in table[i][j]:
                                        table[i][j][v] = probability
                                        back[i][j][v] = (k, rule.derivation[0], rule.derivation[1])
                                    elif table[i][j][v] < probability:
                                        table[i][j][v] = probability
                                        back[i][j][v] = (k, rule.derivation[0], rule.derivation[1])
                            self.unary_check(i, j, table, back, v)
        epsilon = 2**-50
        if self.start in table[0][obs_seq_length] and table[0][obs_seq_length][self.start] >= epsilon:
            probability = table[0][obs_seq_length][self.start]
            return PTree(self.tree_builder(0, obs_seq_length, back, self.start, obs_seq), probability)
        return None

    def is_valid_grammar(self):
        '''
        Validates that the grammar is legal (meaning - the probabilities of the rules for each variable sum to 1).
        '''
        list_of_probability_sums = []
        for v in self.rules:
            sum_of_probabilities = 0
            for rule in self.rules[v]:
                sum_of_probabilities += rule.probability
            list_of_probability_sums.append(sum_of_probabilities)
        print(list_of_probability_sums)
        epsilon = 0.00001
        for i in list_of_probability_sums:
            if i < 1 - epsilon or i > 1 + epsilon:
                return False
        return True
    
    def epsilon_tree_adjustment(self, root, changes):
        new_root = copy.deepcopy(root)
        list_of_nodes = []
        derivation = []
        if len(root.children) != 1:
            for node in root.children:
                derivation.append(node.key)
                list_of_nodes.append(node)
            derivation = tuple(derivation)
            for change in changes:
                if change.rule.derivation == derivation:
                    original_rule = change.info[0]
                    epsilon_index_list = change.info[1]
                    new_children = []
                    for i in range(len(original_rule.derivation)):
                        if i in epsilon_index_list:
                            epsilon_node = Node(original_rule.derivation[i], [])
                            list_of_nodes.insert(i, epsilon_node)
                            new_children.append(epsilon_node)
                        else:
                            recursion_node = list_of_nodes[i]
                            new_children.append(self.epsilon_tree_adjustment(recursion_node, changes))
                    new_root = Node(root.key, new_children)
        return new_root
    
    def restore_shortened_rules(self, root):
        new_root = copy.deepcopy(root)
        new_children = []
        if len(root.children) == 2:
            X_match = bool(re.match('X[0-9]+', root.children[1].key))
            if X_match:
                new_children.append(self.restore_shortened_rules(root.children[0]))
                new_children.append(self.restore_shortened_rules(root.children[1].children[0]))
                new_children.append(self.restore_shortened_rules(root.children[1].children[1]))
                new_root = Node(root.key, new_children)
        elif root.children[0] in self.rules:
            new_children.append(self.restore_shortened_rules(root.children[0]))
            new_root = Node(root.key, new_children)
        return new_root
                
    def restore_terminals_in_rules(self, root):
        new_root = copy.deepcopy(root)
        new_children = []
        if len(root.children) == 2:
            Y_match = bool(re.match('Y[0-9]+', root.children[1].key))
            if Y_match:
                new_children.append(self.restore_terminals_in_rules(root.children[0]))
                new_children.append(root.children[1].children[0])
                new_root = Node(root.key, new_children)
        elif root.children[0] in self.rules:
            new_children.append(self.restore_terminals_in_rules(root.children[0]))
            new_root = Node(root.key, new_children)
        return new_root
                
    def adjust_near_cnf_ptree(self, ptree, changes):
        '''
        THIS METHOD IS RELEVANT ONLY FOR THE BONUS QUSETION.
        Adjusts a PTree derived by a grammar converted to near-CNF, to the equivalent PTree of the original grammar.
        The only changes that this algorithm needs to have informational access to
        (represented by PCFGChange objects) are epsilon rules: S0 is easily gotten rid of,
        while Xn and Yn variables (variables that exist due to rule-shortening), 
        are easily identifiable and pruned without the need for such objects.
        '''
        new_tree = copy.deepcopy(ptree)
        new_tree.root = ptree.root.children[0]
        new_tree.root = self.epsilon_tree_adjustment(new_tree.root, changes)
        new_tree.root = self.restore_shortened_rules(new_tree.root)
        new_tree.root = self.restore_terminals_in_rules(new_tree.root)
        return new_tree


class PCFGChange(object):
    NEW_START = 'new_start'
    EPSILON_RULE = 'epsilon_rule'
    AUXILIARY = 'auxiliary'

    def __init__(self, rule, change_type, info=None):
        '''
        Documents the specific change done on a PCFG.
        '''
        assert change_type in (PCFGChange.NEW_START, PCFGChange.EPSILON_RULE, PCFGChange.AUXILIARY)
        self.rule = rule
        self.change_type = change_type
        self.info = info
