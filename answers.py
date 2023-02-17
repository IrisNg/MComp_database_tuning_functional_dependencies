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
    non_empty_F = remove_empty_FD(F)
    return get_one_set_closure(R, non_empty_F, S)

## Q1b. Determine all attribute closures excluding superkeys that are not candidate keys given the schema R and functional dependency F
def all_closures(R, F): 
    non_empty_F = remove_empty_FD(F)

    all_closure_attribute_sets = get_subsets_of_attribute_set(R)
    C = [[closure_attribute_set, get_one_set_closure(
        R, non_empty_F, closure_attribute_set)] for closure_attribute_set in all_closure_attribute_sets]

    filtered_C = remove_non_candidatekey_superkey(R, C)

    return filtered_C
    
## Q2a. Return a minimal cover of the functional dependencies of a given schema R and functional dependencies F.
def min_cover(R, FD): 
    non_empty_F = remove_empty_FD(FD)

    # Returns list of min_covers, extract only one min_cover
    nested_min_covers = get_min_covers(R, non_empty_F, restrict_to_first_min_cover=True)

    return nested_min_covers[0]

## Q2b. Return all minimal covers reachable from the functional dependencies of a given schema R and functional dependencies F.
def min_covers(R, FD):
    non_empty_F = remove_empty_FD(FD)

    '''
    Explain the rationale of the algorithm here.
    '''
    # TODO: add summary of get min covers here
    return get_min_covers(R, non_empty_F, restrict_to_first_min_cover=False)

## Q2c. Return all minimal covers of a given schema R and functional dependencies F.
def all_min_covers(R, FD):
    # TODO: add summary of get min covers here
    '''
    Explain the rationale of the algorithm here.
    '''
    all_closures_as_FD = all_closures(R, FD)

    return get_min_covers(R, all_closures_as_FD, restrict_to_first_min_cover=False)

## You can add additional functions below

# Let FD be X -> {A}
# Remove functional dependencies with empty X or empty A
def remove_empty_FD(F):
    return list(filter(lambda FD: (len(FD[0]) > 0 and len(FD[1]) > 0), F))


# Get all combinations of attribute subsets for S, a list of attributes
# Example: get_subsets_of_attribute_set(['A', 'B']) => [['A'], ['B'], ['A', 'B']]
def get_subsets_of_attribute_set(S):
    subsets = []
    for i in range(1, len(S) + 1):
        combinations = itertools.combinations(''.join(S), i)
        subsets.extend(list(k) for k in combinations)

    return subsets


def get_one_set_closure(R, F, S):
    # Convert FD in list to set to use set utilities for better performance
    set_F = [convert_FD_list_to_set(FD) for FD in F.copy()]
    closure_attributes = set(S)

    while (True):
        counter = 0

        for FD in set_F:
            if(FD[0].issubset(closure_attributes) and len(FD[1] - closure_attributes) > 0):
                closure_attributes.update(FD[1] - closure_attributes)
                counter += 1

        # if counter == 0, means no more FD could be inferred
        if ((len(closure_attributes) == len(R)) or (counter == 0)):
            break

    return sorted(list(closure_attributes))


# C should be a list of closures, sorted from singletons to pairs to triplet etc,
# else algorithm will not be able to find candidate keys in earlier loops before finding superkeys that are not candidate keys in later loops
def remove_non_candidatekey_superkey(R, C):
    num_schema_attributes = len(R)
    candidate_keys = []
    filtered_C = []

    for closure in C:
        # Not superkey, add closure to filtered list
        if (len(closure[1]) != num_schema_attributes):
            filtered_C.append(closure)

        # Is superkey
        # Check if subset is already added as candidate_key, if it is, then ignore closure to remove superkey from filtered list
        # TODO: double check this logic here
        elif (len(candidate_keys) == 0 or any(True for ck in candidate_keys if not ck.issubset(set(closure[0])))):
            filtered_C.append(closure)
            candidate_keys.append(set(closure[0]))

    return filtered_C


def get_min_covers(R, F, restrict_to_first_min_cover):
    # Step 1 - get F': Minimize right hand-side of every functional dependency to attain form X -> {A}
    simplified_rhs_F = decompose_FD(F)

    simplified_rhs_F = remove_trivial_FD(
        [convert_FD_list_to_set(FD) for FD in simplified_rhs_F])

    incl_transitive_F = add_transitive_FD(simplified_rhs_F)

    many_simplified_lhs_rhs_F = simplify_lhs_FD(simplified_rhs_F, incl_transitive_F, restrict_to_first_min_cover)
    print('========')
    print('many_simplified_lhs_rhs_F', many_simplified_lhs_rhs_F)

    many_removed_duplicate_F = [remove_duplicate_FD(simplified_F) for simplified_F in many_simplified_lhs_rhs_F]
    print('========')
    print('many_removed_duplicate_F', many_removed_duplicate_F)
    # TODO: remove duplicated F sets here?
    # Nested minimal covers list
    many_min_covers_nested = [remove_transitive_FD(simplified_F) for simplified_F in many_removed_duplicate_F]
    many_min_covers = [min_cover for many_min_covers_list in many_min_covers_nested for min_cover in many_min_covers_list]
    print('========= many min covers =========', many_min_covers)

    # Remove duplicated minimal covers, and convert FD from set back into list
    many_min_covers_removed_duplicate = remove_duplicate_min_cover(many_min_covers)

    return many_min_covers_removed_duplicate



# Using Armstrong Axioms decomposition rule, decompose FD into multiple FDs if right hand-side of FD has multiple attributes
# Example {{A} -> {B,C}} => {{A} -> {B}, {A} -> {C}}
def decompose_FD(F):
    decomposed_F = []

    for FD in F:
        if (len(FD[1]) == 1):
            decomposed_F.append(FD)
        else:
            for attribute in FD[1]:
                decomposed_F.append([FD[0], [attribute]])

    return decomposed_F

# Convert [['A'], ['B', 'C']] => 'A->BC'
def convert_FD_list_to_string(FD):
    return ''.join(sorted(FD[0])) + '->' + ''.join(sorted(FD[1]))

# Convert [['A'], ['B', 'C']] => [{'A'}, {'B', 'C'}]
def convert_FD_list_to_set(FD):
    return [set(FD[0]), set(FD[1])]

# Convert and sort [{'D', 'A'}, {'C', 'B'}] => [['A', 'D'], ['B', 'C']]
def convert_FD_set_to_list(FD):
    return [sorted(list(FD[0])), sorted(list(FD[1]))]

# Find and add transitive functional dependencies to a list of original functional dependencies
def add_transitive_FD(F):
    added_F = [convert_FD_list_to_set(FD) for FD in F.copy()]

    # Maintain a set of FD strings for quick searching to check if FD is already added
    set_F = set([convert_FD_list_to_string(FD) for FD in F.copy()])
    print('set_F', set_F)

    while (True):
        counter = 0

        for FD in added_F:
            FD_lhs = FD[0]
            FD_rhs = FD[1]

            for inner_FD in added_F:
                inner_FD_lhs = inner_FD[0]
                inner_FD_rhs = inner_FD[1]

                # Check if first FD's right hand-side match with another FD's left hand-side to find transitive FD (Armstrong Axioms Transitivity Rule)
                # But ignore trivial FD
                if (inner_FD_lhs == FD_rhs and not inner_FD_rhs.issubset(FD_lhs)):
                    transitive_FD = convert_FD_set_to_list(
                        [FD_lhs, inner_FD_rhs])
                    transitive_FD_string = convert_FD_list_to_string(
                        transitive_FD)

                    # Check if transitive FD is already added previously
                    if (transitive_FD_string not in set_F):
                        # New transitive FD, add to cumulative list and set
                        added_F.append(convert_FD_list_to_set(transitive_FD))
                        set_F.add(transitive_FD_string)
                        counter += 1

        if (counter == 0):
            # No new transitive FD has been added in last round of while loop, stop finding transitive FD
            break

    return added_F


def remove_trivial_FD(F):
    return list(filter(lambda FD: not FD[1].issubset(FD[0]), F))


def simplify_lhs_FD(simplified_rhs_F, incl_transitive_F, restrict_to_first_min_cover):
    # simplified_alt is a list of simplified alternative left hand-side for each FD
    # There could be 0, or many alternatives for each FD, which will lead to different outcomes of minimal covers
    # Store simplified alternative FDs separately instead of replacing into original list directly
    # This is to find all minimal covers by choosing different alternatives later
    # Length of simplified_alt correlates to original FD list, so as to replace into original list using same index later
    # E.g. FD in simplified_alt[2] will replace into simplified_rhs_F[2] afterwards
    simplified_alt = [[] for i in range(len(simplified_rhs_F))]

    for FD_index, FD in enumerate(simplified_rhs_F):
        FD_lhs = FD[0]
        FD_rhs = FD[1]

        # If left hand-side is already simplified to 1 attribute, then skip
        if (len(FD_lhs) == 1):
            continue

        for inner_FD in incl_transitive_F:
            inner_FD_lhs = inner_FD[0]
            inner_FD_rhs = inner_FD[1]

            # We want to replace left hand-side of outer FD with smaller subset
            # If inner FD left hand-side is equal or greater than outer FD lhs in length, then skip
            if (len(inner_FD_lhs) == len(FD_lhs)):
                break

            alt = simplified_alt[FD_index]

            # Simplification scenario 1:
            # outer FD rhs = inner FD rhs, AND inner FD lhs is a smaller subset of outer FD lhs
            # AND inner FD lhs has same number of attributes as any previously added alternatives, not more, otherwise it will not be minimal
            if (FD_rhs == inner_FD_rhs and inner_FD_lhs.issubset(FD_lhs) and (len(alt) == 0 or len(inner_FD_lhs) == len(alt[0][0]))):
                simplified_alt[FD_index].append(inner_FD)
                continue

            # Simplification scenario 2:
            # Using Armstrong Axioms Transitivity Rule, inner FD implies that a subset of outer FD lhs functionally determines another subset of outer FD lhs
            # Example - outer FD = {A, B} -> {C}, and inner FD = {A} -> {B}, then outer FD can be replaced with {A} -> {C}
            # AND lhs of FD to add, has same number of attributes as any previously added alternatives, not more, otherwise it will not be minimal
            if (inner_FD_lhs.issubset(FD_lhs) and inner_FD_rhs.issubset(FD_lhs - inner_FD_lhs) and (len(alt) == 0 or len(FD_lhs - inner_FD_rhs) == len(alt[0][0]))):
                simplified_alt[FD_index].append(
                    [(FD_lhs - inner_FD_rhs), FD_rhs])


        # Remove duplicated alternatives
        print('havent cleaned', simplified_alt[FD_index])
        simplified_alt[FD_index] = remove_duplicate_FD(simplified_alt[FD_index])
        print('cleaned dups', simplified_alt[FD_index])


    print('simplify_alt', simplified_alt)
    # Get combinations of alternatives to find all minimal covers
    # To use Python's itertools.product, convert FD format alternatives (nested list) into ids (string of nested indexes)
    # Example - if simplified_alt = [[], [[{'A', 'E'}, {'F'}]]], id of alt FD [{'A', 'E'}, {'F'}] => [['1-0']]
    simplified_alt_ids = []

    for FD_index, alts in enumerate(simplified_alt):
        if (len(alts) == 0):
            continue

        ids = [(str(FD_index) + '-' + str(alt_index)) for alt_index, alt in enumerate(alts)]
        simplified_alt_ids.append(ids)

    # If all FDs have no alternatives, exit and return only original F passed in as argument
    if (len(simplified_alt_ids) == 0):
        return [simplified_rhs_F]

    print('hello', simplified_alt_ids)
    # Get combinations of alternatives' ids
    all_combination = list(itertools.product(*simplified_alt_ids))

    # If mode is set to only get one minimal cover, select only the first combination
    if (restrict_to_first_min_cover):
        all_combination = [all_combination[0]]

    print('all possibilities', all_combination)
    print('===========')
    print('original F', simplified_rhs_F)

    # Generate many sets of F based on different combinations of lhs alternatives for each FD
    # This will get all minimal covers later (will also remove duplicated outcomes at the last step of finding minimal cover later)
    many_F = []
    for combi in all_combination:
        alt_F = simplified_rhs_F.copy()

        for id in combi:
            split_id = id.split('-')
            FD_index = int(split_id[0])
            alt_index = int(split_id[1])
            alt_F[FD_index] = simplified_alt[FD_index][alt_index]
        many_F.append(alt_F)

    # TODO: remove?
    print('\n====== start many_F ======')
    # print('many_F', many_F)
    for F in many_F:
        print('\n==============\n')
        print(F)
    print('====== end many_F ======\n')
    # TODO: end remove?

    return many_F


def remove_duplicate_FD(F):
    unique_F = []
    unique_F_string = set()

    for FD in F:
        FD_string = convert_FD_list_to_string(FD)

        if (FD_string not in unique_F_string):
            unique_F.append(FD)
            unique_F_string.add(FD_string)

    return unique_F


def remove_transitive_FD(F):
    print('remove transitive FD', F)

    omittable_FD = []
    non_omittable_FD = []

    # Find FD that could be replaced by other FDs using Armstrong Axioms Transitivity Rule
    # Do not remove omittable FDs from original F yet, find permutations to remove omittable FDs in sequence later as it may affect outcome of minimal cover
    for outer_FD_index, outer_FD in enumerate(F):
        lhs_match = []
        rhs_match = []
        # TODO: if no match?

        for inner_FD_index, inner_FD in enumerate(F):
            # Skip same FD for outer and inner loop
            if (outer_FD_index == inner_FD_index):
                continue

            if (outer_FD[0] == inner_FD[0]):
                lhs_match.append(inner_FD)

            if (outer_FD[1] == inner_FD[1]):
                rhs_match.append(inner_FD)

        is_omittable = False
        for lhs_match_FD in lhs_match:
            if (is_omittable):
                break

            for rhs_match_FD in rhs_match:
                if (lhs_match_FD[1] == rhs_match_FD[0]):
                    omittable_FD.append(outer_FD)
                    is_omittable = True
                    break

        if (not is_omittable):
            non_omittable_FD.append(outer_FD)

    # TODO: If no omitable?
    print('**********')
    print('omitable', omittable_FD)
    print('non omitable', non_omittable_FD)
    print('**********')

    many_F_with_omittable_rotated = []
    omittable_ids = ''.join([str(index) for index in range(len(omittable_FD))])
    print('omittable_ids', omittable_ids)
    permutations = list(itertools.permutations(
        omittable_ids, len(omittable_FD)))
    print('permutations', permutations)

    for permutation in permutations:
        omittable_permutation = [
            omittable_FD[int(omittable_index)] for omittable_index in permutation]
        many_F_with_omittable_rotated.append(
            [*omittable_permutation, *non_omittable_FD])

    # TODO: remove?
    print('++++++++++++++++++++++++++++++')
    for L in many_F_with_omittable_rotated:
        print('\n ---------------- \n')
        print(L)
        print('\n ---------------- \n')
    print('++++++++++++++++++++++++++++++')
    # TODO: end remove?

    for rotated_F in many_F_with_omittable_rotated:
        for outer_FD_index, outer_FD in enumerate(rotated_F):
            lhs_match = []
            rhs_match = []

            for inner_FD_index, inner_FD in enumerate(rotated_F):
                # Skip if inner_FD has been removed in previous outer_FD loop
                # or skip if same FD for outer and inner loop
                if (inner_FD is None or outer_FD_index == inner_FD_index):
                    continue

                if (outer_FD[0] == inner_FD[0]):
                    lhs_match.append(inner_FD)

                if (outer_FD[1] == inner_FD[1]):
                    rhs_match.append(inner_FD)

            # If either lhs or rhs has no other FD match, this outer_FD is non omittable
            if (len(lhs_match) == 0 or len(rhs_match) == 0):
                continue

            is_outer_FD_removed = False
            for lhs_match_FD in lhs_match:
                if (is_outer_FD_removed):
                    break

                for rhs_match_FD in rhs_match:
                    if (lhs_match_FD[1] == rhs_match_FD[0]):
                        # Remove omittable FD from F
                        # So that it is not usable by the next outer_FD and inner_FD in the next loop
                        rotated_F[outer_FD_index] = None
                        is_outer_FD_removed = True
                        break

    # Remove elements that are None
    many_F_filtered_out_removed = []
    for new_F in many_F_with_omittable_rotated:
        many_F_filtered_out_removed.append(
            list(filter(lambda FD: FD is not None, new_F)))

    print('\n===========================\n')
    print('almost final!')
    print(many_F_filtered_out_removed)
    print('\n===========================\n')

    return many_F_filtered_out_removed


def remove_duplicate_min_cover(many_min_covers):
    # Covert each min_cover to a set of string format FD
    unique_min_covers = []
    unique_min_covers_set = []
    
    print('EEHHHHH')
    for k in many_min_covers:
        print('\n-------\n')
        print(k)
        print('\n-------\n')
    print('EEHHHHH')
    for one_min_cover in many_min_covers:
        min_cover_set = set(convert_FD_list_to_string(FD) for FD in one_min_cover)

        if (len(unique_min_covers_set) == 0):
            # Also convert FD from set back to list
            unique_min_covers.append([convert_FD_set_to_list(FD) for FD in one_min_cover])
            unique_min_covers_set.append(min_cover_set)
            continue

        is_duplicate = False

        for unique_min_cover_set in unique_min_covers_set:
            if (unique_min_cover_set == min_cover_set):
                is_duplicate = True
                break
        
        if (not is_duplicate):
            # Also convert FD from set back to list
            unique_min_covers.append([convert_FD_set_to_list(FD) for FD in one_min_cover])
            unique_min_covers_set.append(min_cover_set)

    print('WEEEEEEEEEEE')
    for k in unique_min_covers:
        print('\n-------\n')
        print(k)
        print('\n-------\n')
    print('WEEEEEEEEEEE')
    return unique_min_covers

    

# Main functions
def main():
    ### Test case from the project
    R = ['A', 'B', 'C', 'D']
    FD = [[['A', 'B'], ['C']], [['C'], ['D']]]

    # print(closure(R, FD, ['A']))
    # print(closure(R, FD, ['A', 'B']))
    # print(all_closures(R, FD))

    R = ['A', 'B', 'C', 'D', 'E', 'F']
    FD = [[['A'], ['B', 'C']], [['B'], ['C','D']], [['D'], ['B']], [['A','B','E'], ['F']]]
    print(min_cover(R, FD)) 

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



