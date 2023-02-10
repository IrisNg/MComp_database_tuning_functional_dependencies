###########################################################################
## answers.py - Code template for Project Functional Dependencies
###########################################################################

## If you need to import library put it below

import itertools

## Change the function below with your student number.
def student_number():
    return 'A003419B'

# Get combinations of subsets for list of attributes
# Example: get_subsets_of_attribute_set(['A', 'B']) => [{'A'}, {'B'}, {'A', 'B'}]
def get_subsets_of_attribute_set(S):
    subsets = []
    for i in range(1, len(S) + 1):
        combinations = itertools.combinations(''.join(S), i)
        subsets.extend(set(k) for k in combinations)

    return subsets


#TODO: remove empty FD
def get_one_set_closure(R, F, S):
    A_set = set(S)

    while (True):
        added_counter = 0

        subsets = get_subsets_of_attribute_set(list(A_set))

        for subset in subsets:
            for FD in F:
                if (set(FD[0]) == subset and len(set(FD[1]) - A_set) > 0):
                    A_set.update(set(FD[1]) - A_set)
                    added_counter += 1
        
        # if added_counter == 0, means no more FD could be inferred
        if ((len(A_set) == len(R)) or (added_counter == 0)):
            break;
    
    return sorted(list(A_set))



## Q1a. Determine the closure of a given set of attribute S the schema R and functional dependency F
def closure(R, F, S):
    return get_one_set_closure(R, F, S)

## Q1b. Determine all attribute closures excluding superkeys that are not candidate keys given the schema R and functional dependency F
def all_closures(R, F): 
    all_closure_sets = get_subsets_of_attribute_set(R)
    all_closures_results = []
    for closure_set in all_closure_sets:
        all_closures_results.append([sorted(list(closure_set)), get_one_set_closure(R, F, list(closure_set))])
    #TODO: exclude super keys not candidate keys
    return all_closures_results
    
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



## Main functions
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
#     R = ['A', 'B', 'C', 'D']
#     FD = [[['A', 'B'], ['C']], [['C'], ['D']]]

#     # print(closure(R, FD, ['A']))
#     print(closure(R, FD, ['A', 'B']))



if __name__ == '__main__':
    main()



