import re
import copy
import time


class Predicate:
    def __init__(self, name, ptype, arguments):
        self.predicateName = name
        self.predicateType = ptype   # Boolean
        self.arguments = arguments   # 1- 25 arguments


class Sentence:
    def __init__(self, predicates):
        self.predicates = predicates  # Sentence is a list of predicates


class KnowledgeBase:
    def __init__(self, sentences):
        self.KB = sentences


def predicate_position_list(KBobj):
    hashset_p = {}
    hashset_n = {}
    for index, sentence in enumerate(KBobj.KB):
        for p_index, predicate in enumerate(sentence.predicates):
            predicate_string = predicate.predicateName + str(predicate.arguments)
            # print(predicate_string)
            if predicate.predicateType is True:
                hashset_n[predicate_string] = (sentence, index+1, p_index+1)
            else:
                hashset_p[predicate_string] = (sentence, index+1, p_index+1)
    return hashset_p, hashset_n


def predicate_position_tuplelist(KBobj):
    hashset_p = {}
    hashset_n = {}
    for index, sentence in enumerate(KBobj.KB):
        for p_index, predicate in enumerate(sentence.predicates):
            predicate_string = predicate.predicateName
            # print(predicate_string)
            if predicate.predicateType is True:
                if predicate_string not in hashset_n:
                    hashset_n[predicate_string] = list()
                hashset_n[predicate_string].append((sentence, index+1, p_index+1))
            else:
                if predicate_string not in hashset_p:
                    hashset_p[predicate_string] = list()
                hashset_p[predicate_string].append((sentence, index+1, p_index+1))
    return hashset_p, hashset_n


def main():
    with open("input.txt", 'r') as readfile:
        nqueries = int(readfile.readline())
        queries = []
        for iquery in range(nqueries):
            query = readfile.readline().strip("\n")
            queries.append(query)
        nsentences = int(readfile.readline())
        sentences = []
        for isentence in range(nsentences):
            sentence = readfile.readline().strip("\n")
            sentences.append(sentence)
    sentences = standardize(sentences)
    # Convert to CNF
    sentence_obj_list = []
    sentences = parse(sentences)
    for s in sentences:
        s = s.split("|")
        n_predicates_in_sentence = len(s)
        predicate_obj_list = []
        # create predicate objects of each sentence
        for p in range(n_predicates_in_sentence):
            predicate = s[p].strip()
            if predicate[0] == "~":
                ptype = True   # Means Negated
                p_index = predicate.index("(")
                predicate_name = predicate[1:p_index]
            else:
                ptype = False
                p_index = predicate.index("(")
                predicate_name = predicate[:p_index]
            arguments = predicate[p_index:]
            arguments = tuple(arguments[1:-1].split(","))
            # print("Predicate Name", predicate_name,"predicate arguments", arguments)
            p_obj = Predicate(predicate_name, ptype, arguments)
            predicate_obj_list.append(p_obj)
        s_obj = Sentence(predicate_obj_list)
        sentence_obj_list.append(s_obj)
    # sentence_obj_list = factoring(sentence_obj_list)
    kbobj = KnowledgeBase(sentence_obj_list)
    # call Resolution
    result_list = []
    for i, query in enumerate(queries):
        qkbobj = copy.deepcopy(kbobj)
        query = negate_query(query)
        hashset_p, hashset_n = predicate_position_tuplelist(qkbobj)
        result = resolution(hashset_p, hashset_n, query, qkbobj, nsentences)
        if result is True:
            # print("TRUE")
            result_list.append("TRUE")
            continue
        else:
            # print("FALSE")
            result_list.append("FALSE")
            continue
        break
    output = ""
    with open("output.txt", "w+") as output_fd:
        for answer in result_list[:-1]:
            output += answer + "\n"
        output += result_list[-1]
        output_fd.write(output)


def negate_query(query):
    if query[0] == "~":
        return query[1:]
    else:
        return "~" + query


def factoring(sentence_objs):
    sentence_objs_list = []
    for sentence in sentence_objs:
        positions_to_pop = []
        already_seen = {}
        for position, predicate in enumerate(sentence.predicates):
            if (predicate.predicateName, predicate.arguments) in already_seen:
                positions_to_pop.append(position)
                sentence.predicates.pop(position)
            else:
                already_seen[(predicate.predicateName, predicate.arguments)] = (predicate, predicate.arguments, position)
        sentence_objs_list.append(sentence)
    return sentence_objs_list


def parse(sentence_list):
    cnf_sentences = []
    for sentence in sentence_list:
        if "=>" in sentence:
            index = sentence.index("=")
            left = sentence[:index]
            right = sentence[index:]
            left = left.split()
            for index, x in enumerate(left):
                if x == "&":
                    left[index] = "|"
                    continue
                if x[0].isupper() and x[0] != "~":
                    left[index] = "~" + x
                elif x[0] == "~":
                    left[index] = x[1:]
            left = " ".join(left)
            right = right.replace("=>", "|")
            c_sentence = left + right
            cnf_sentences.append(c_sentence)
        else:
            cnf_sentences.append(sentence)
    return cnf_sentences


# STANDARDIZATION

def standardize(sentences):
    sentences_list = []
    for i, sentence in enumerate(sentences):
        tuple_list = re.findall(r'\(([^)]*)\)', sentence)
        y = []    # To create an empty set later
        for x in tuple_list:
            x = x.split(",")
            y += x
        y = set(y)   # Redundant elements will be removed
        variable_list = []
        for z in y:
            if z[0].isupper():
                continue
            else:
                variable_list.append(z)
        for each_symbol in variable_list:
            each_symbol_new = each_symbol+str(i+1)
            regex = r"\b(?=\w)" + re.escape(each_symbol) + r"\b(?!\w)"
            # regex = r"\b" + re.escape(each_symbol) + r"\b"
            sentence = re.sub(regex, each_symbol_new, sentence)
            # print(sentence)
        sentences_list.append(sentence)
    return sentences_list


# UNIFICATION

def is_variable(x):
    if x.islower():
        return True
    else:
        return False


def unification(x, y, z):
    if x == y:
        return z
    if x is [] and y is []:
        return z
    if type(x) is not tuple and is_variable(x):
        # print("x:", x, "y:", y, "z:", z)
        return unify(x, y, z)
    elif type(y) is not tuple and is_variable(y):
        return unify(y, x, z)
    elif type(x) is tuple and type(y) is tuple:
        # print("Here")
        return unification(x[1:], y[1:], unification(x[0], y[0], z))
    else:
        return z


def unify(variable, b, hashset):
    # If in the form of {variable/variable}
    if variable in hashset:
        return unify(hashset[variable], b, hashset)
    else:
        # Substitution
        return substitution(hashset, variable, b)


def substitution(hashset, variable, value):
    updated_hashset = hashset.copy()
    updated_hashset[variable] = value
    if value in hashset:
        updated_hashset[variable] = hashset[value]
    return updated_hashset


# RESOLUTION


def resolution(hashset_p, hashset_n, query, kbobj, nsentences):
    # DFS or BFS
    p_index = query.index("(")
    if query[0] == "~":
        predicate_name = query[1:p_index]
        qtype = True
    else:
        predicate_name = query[:p_index]
        qtype = False
    arguments = query[p_index:]
    arguments = tuple(arguments[1:-1].split(","))
    nqueryobj = Predicate(predicate_name, qtype, arguments)
    qsentence = Sentence([nqueryobj])
    kbobj.KB.append(qsentence)
    nsentences += 1
    if qtype is True:
        if predicate_name in hashset_n:
            hashset_n[predicate_name].append((qsentence, nsentences, 1))
        else:
            hashset_n[predicate_name] = (qsentence, nsentences, 1)
    else:
        if predicate_name in hashset_p:
            hashset_p[predicate_name].append((qsentence, nsentences, 1))
        else:
            hashset_p[predicate_name] = (qsentence, nsentences, 1)
    queue = list()
    queue.append(qsentence)
    count = 0
    avoiding_cycles = {}
    delay = 40
    close_time = time.time() + delay
    while queue:
        loop_detected = 0
        sentence = queue.pop(0)
        count += 1
        if time.time() > close_time:
            return False
        # POPS sentence object from the queue
        for index, predicate in enumerate(sentence.predicates):
            # Pick the first predicate and then check if its can be used to resolve
            if predicate.predicateType is True:
                if predicate.predicateName in hashset_p:
                    sentences = hashset_p[predicate.predicateName]    # Sentences to be matched
                    for sentence_v in sentences:
                        predicate_l = sentence_v[0].predicates.copy()   # Sentence[0] is object
                        predicate_p = sentence_v[2]-1  # Position of the predicate in sentences, doesnt start with 0, hence -1
                        predicate_for_unification = predicate_l[predicate_p]
                        no_unification = 0
                        for i in range(len(predicate.arguments)):
                            if is_variable(predicate.arguments[i]) or is_variable(predicate_for_unification.arguments[i]):
                                continue
                            elif predicate.arguments[i] == predicate_for_unification.arguments[i]:
                                continue
                            elif predicate.arguments[i] != predicate_for_unification.arguments[i]:
                                no_unification = 1
                                break
                        if no_unification:
                            continue
                        theta = unification(predicate.arguments, predicate_for_unification.arguments, {})
                        predicate_l.pop(predicate_p)
                        predicate_l_s = sentence.predicates.copy()
                        predicate_l_s.pop(index)
                        sentence_obj_list = predicate_l + predicate_l_s
                        # cycle detection
                        cycle = detect_cycle(sentence_v[0].predicates.copy(), sentence_obj_list, avoiding_cycles)
                        if cycle is True:
                            loop_detected = 1
                            break
                        else:
                            predicates_k = tuple(sentence_v[0].predicates.copy())
                            avoiding_cycles[predicates_k] = sentence_obj_list
                        if not sentence_obj_list:
                            return True
                        new_sentence_obj_list = copy.deepcopy(sentence_obj_list)
                        # Actual substitution
                        for theta_k, theta_v in theta.items():
                            for substitute in new_sentence_obj_list:
                                arguments = list(substitute.arguments)
                                for i, arg in enumerate(arguments):
                                    if arg == theta_k:
                                        arguments[i] = theta_v
                                arguments = tuple(arguments)
                                substitute.arguments = arguments
                        # Done with substitution, now make a new sentence object
                        new_sentence_obj = Sentence(new_sentence_obj_list)
                        kbobj.KB.insert(0, new_sentence_obj)
                        queue.append(new_sentence_obj)
                        hashset_p, hashset_n = predicate_position_tuplelist(kbobj)
            else:
                if predicate.predicateName in hashset_n:
                    sentences = hashset_n[predicate.predicateName]    # Sentences to be matched
                    for sentence_v in sentences:
                        predicate_l = sentence_v[0].predicates.copy()   # Sentence[0] is object
                        predicate_p = sentence_v[2]-1  # Position of the predicate in sentences, doesnt start with 0, hence -1
                        predicate_for_unification = predicate_l[predicate_p]
                        theta = unification(predicate.arguments, predicate_for_unification.arguments, {})
                        predicate_l.pop(predicate_p)
                        predicate_l_s = sentence.predicates.copy()
                        predicate_l_s.pop(index)
                        sentence_obj_list = predicate_l + predicate_l_s
                        # Cycle Detection
                        cycle = detect_cycle(sentence_v[0].predicates.copy(), sentence_obj_list, avoiding_cycles)
                        if cycle is True:
                            loop_detected = 1
                            break
                        else:
                            predicates_k = tuple(sentence_v[0].predicates.copy())
                            avoiding_cycles[predicates_k] = sentence_obj_list
                        if not sentence_obj_list:
                            return True
                        new_sentence_obj_list = copy.deepcopy(sentence_obj_list)
                        for theta_k, theta_v in theta.items():
                            for substitute in new_sentence_obj_list:
                                arguments = list(substitute.arguments)
                                for i, arg in enumerate(arguments):
                                    if arg == theta_k:
                                        arguments[i] = theta_v
                                arguments = tuple(arguments)
                                substitute.arguments = arguments
                        new_sentence_obj = Sentence(new_sentence_obj_list)
                        kbobj.KB.insert(0, new_sentence_obj)
                        queue.append(new_sentence_obj)
                        hashset_p, hashset_n = predicate_position_tuplelist(kbobj)
            if loop_detected:
                break
    return False


def detect_cycle(hashed_sentence_predicate, result, avoiding_cycles):
    predicates_k = tuple(hashed_sentence_predicate)
    if predicates_k in avoiding_cycles:
        sentence_list = avoiding_cycles[predicates_k]
        if sentence_list == result:
            return True


main()
