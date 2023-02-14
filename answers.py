###########################################################################
## answers.py - Code template for Project Functional Dependencies
###########################################################################

## If you need to import library put it below

import itertools

## Change the function below with your student number.
def student_number():
    return 'A003419B'



## Q1a. Determine the closure of a given set of attribute S the schema R and functional dependency F
def closure(R, F, S):
    non_empty_F = remove_empty_functional_dependency(F)
    return get_one_set_closure(R, non_empty_F, S)

## Q1b. Determine all attribute closures excluding superkeys that are not candidate keys given the schema R and functional dependency F
def all_closures(R, F): 
    non_empty_F = remove_empty_functional_dependency(F)

    all_closure_attribute_sets = get_subsets_of_attribute_set(R)
    C = []
    for closure_attribute_set in all_closure_attribute_sets:
        C.append([sorted(list(closure_attribute_set)), get_one_set_closure(R, non_empty_F, list(closure_attribute_set))])
    
    filtered_C = remove_non_candidatekey_superkey(R, C)

    return filtered_C
    
## Q2a. Return a minimal cover of the functional dependencies of a given schema R and functional dependencies F.
def min_cover(R, FD): 
    return []

## Q2b. Return all minimal covers reachable from the functional dependencies of a given schema R and functional dependencies F.
def min_covers(R, FD):
    '''
    Explain the rationale of the algorithm here.
    '''
    return []

## Q2c. Return all minimal covers of a given schema R and functional dependencies F.
def all_min_covers(R, FD):
    '''
    Explain the rationale of the algorithm here.
    '''
    return []

## You can add additional functions below

# Let FD be X -> {A} 
# Remove functional dependencies with empty X or empty A 
def remove_empty_functional_dependency(F):
    return list(filter(lambda FD: (len(FD[0]) > 0 and len(FD[1]) > 0), F))


# Get combinations of subsets for list of attributes
# Example: get_subsets_of_attribute_set(['A', 'B']) => [{'A'}, {'B'}, {'A', 'B'}]
def get_subsets_of_attribute_set(S):
    subsets = []
    for i in range(1, len(S) + 1):
        combinations = itertools.combinations(''.join(S), i)
        subsets.extend(set(k) for k in combinations)

    return subsets


def get_one_set_closure(R, F, S):
    A_set = set(S)
    while (True):
        counter = 0

        subsets = get_subsets_of_attribute_set(list(A_set))
        for subset in subsets:
            for FD in F:
                if (set(FD[0]) == subset and len(set(FD[1]) - A_set) > 0):
                    A_set.update(set(FD[1]) - A_set)
                    counter += 1
        
        # if counter == 0, means no more FD could be inferred
        if ((len(A_set) == len(R)) or (counter == 0)):
            break;
    
    return sorted(list(A_set))


def remove_non_candidatekey_superkey(R, C):
    num_schema_attributes = len(R)
    candidate_keys = []
    filtered_C = []

    # C should be a list of closures, sorted from singletons to pairs to triplet etc 
    for closure in C:
        if (len(closure[1]) != num_schema_attributes):
            # Not superkey
            filtered_C.append(closure)

        # Is superkey
        # Check if subset is already added as candidate_key, if it is, then ignore closure to remove superkey from filtered list
        elif (len(candidate_keys) == 0 or any(True for ck in candidate_keys if not ck.issubset(set(closure[0])))):
            filtered_C.append(closure)
            candidate_keys.append(set(closure[0]))
            
    return filtered_C





# Main functions
def main():
    ### Test case from the project
    R = ['A', 'B', 'C', 'D']
    FD = [[['A', 'B'], ['C']], [['C'], ['D']]]

    print(closure(R, FD, ['A']))
    print(closure(R, FD, ['A', 'B']))
    print(all_closures(R, FD))

#     R = ['A', 'B', 'C', 'D', 'E', 'F']
#     FD = [[['A'], ['B', 'C']], [['B'], ['C','D']], [['D'], ['B']], [['A','B','E'], ['F']]]
#     print(min_cover(R, FD)) 

#     R = ['A', 'B', 'C']
#     FD = [[['A'], ['B']], [['B'], ['C']], [['C'], ['A']]] 
#     print(min_covers(R, FD))
#     print(all_min_covers(R, FD)) 

#     ### Add your own additional test cases if necessary

# def main():
#     ### Test case from the project
#     R = ['A', 'B', 'C', 'D', 'E']
#     FD = [[['A'], ['B']], [['B'], ['C']], [['C'], ['D']], [['D'], ['E']]]

#     # print(closure(R, FD, ['A']))
#     print(all_closures(R, FD))



if __name__ == '__main__':
    main()



