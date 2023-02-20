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
    return get_one_closure(R, non_empty_F, S)

## Q1b. Determine all attribute closures excluding superkeys that are not candidate keys given the schema R and functional dependency F
def all_closures(R, F): 
    non_empty_F = remove_empty_FD(F)

    # Get all combinations of closure attribute sets
    # Should return combinations sorted from singletons to pairs to triplets
    # Else loop algorithm below will not be able to find candidate keys in earlier loops before skipping superkeys that are not candidate keys in later loops
    # Example: if R = ['A', 'B'] => the closures to find are [['A'], ['B'], ['A', 'B']]
    all_closure_attribute_sets = get_subset_combination(R)

    # Find closure of each closure_attribute_set one by one
    num_schema_attributes = len(R)
    candidate_keys = [] # Example: [{'C'}, {'A', 'B'}]
    closures_without_non_candidatekey_superkey = []

    for closure_attribute_set in all_closure_attribute_sets:
        # Skip finding closure if there is already a smaller subset of closure_attribute_set that is candidate key
        # because in that scenario, closure_attribute_set will be a superkey that is not candidate key
        # and we want to omit superkeys that are not candidate keys per the requirements
        if (len(candidate_keys) > 0) and any(True if ck.issubset(set(closure_attribute_set)) else False for ck in candidate_keys):
            continue
            
        calculated_closure = get_one_closure(R, non_empty_F, closure_attribute_set)
        closures_without_non_candidatekey_superkey.append([closure_attribute_set, calculated_closure])

        if len(calculated_closure) == num_schema_attributes:
            # Superkey AND Candidate key, as all attributes of R are functionally dependent on this closure_attribute_set
            candidate_keys.append(set(closure_attribute_set))

    return closures_without_non_candidatekey_superkey
    
## Q2a. Return a minimal cover of the functional dependencies of a given schema R and functional dependencies F.
def min_cover(R, FD): 
    non_empty_F = remove_empty_FD(FD)

    # Returns nested list of one minimal cover (to reuse get_min_covers() for min_covers and all_min_covers questions)
    # Extract only the first mininmal cover from nested list
    # restrict_to_first_min_cover=True prevents get_min_covers (and its sub functions) from finding more than one permutation, which improves performance when getting only one minimal cover
    nested_min_covers = get_min_covers(R, non_empty_F, restrict_to_first_min_cover=True)

    return nested_min_covers[0]

## Q2b. Return all minimal covers reachable from the functional dependencies of a given schema R and functional dependencies F.
def min_covers(R, FD):
    non_empty_F = remove_empty_FD(FD)

    '''
    Explain the rationale of the algorithm here.
    Ans: Sorry, please refer to comments in get_min_covers() ancillary function instead, since the logic is reused for all 3 parts of Q2
    '''

    return get_min_covers(R, non_empty_F, restrict_to_first_min_cover=False)

## Q2c. Return all minimal covers of a given schema R and functional dependencies F.
def all_min_covers(R, FD):
    '''
    Explain the rationale of the algorithm here.
    Ans: We start by finding the closures for all attribute sets, this will infer additional functional dependencies using Armstrong Axioms that are not found in the original FD list. 
    Since we infer a complete set of FDs, using the same function get_min_covers(), the function algorithm will derive a complete set of minimal covers otherwise not reachable by using original FD list itself
    Example: If the data structure returned for one closure is [['A', 'B'], ['A', 'B', 'C', 'D']], passing the same closure data into get_min_covers(), 
    it will be decomposed to derive functional dependencies AB -> A, AB -> B, AB -> C, AB -> D, before using this complete set of FDs (along with decomposed FDs from other attribute closures) to find all minimal covers
    If there are redundant functional dependencies from the closure, e.g. ABC -> D is redundant when A -> D already exists, 
    they will be simplified in simplify_lhs_FD() or removed in remove_transitive_FD() steps of get_min_covers(), leading to all minimal covers found being minimal and deriving the full set
    Please refer to comments in get_min_covers() for breakdown of logic in the algorithm, same as Q2a and Q2b
    '''
    all_closures_as_FD = all_closures(R, FD)

    return get_min_covers(R, all_closures_as_FD, restrict_to_first_min_cover=False)

## You can add additional functions below

## Data structure conversion helpers for better performance in business logic loops
# Convert [['A'], ['B', 'C']] => 'A->BC'
def convert_FD_list_to_string(FD):
    return ''.join(sorted(FD[0])) + '->' + ''.join(sorted(FD[1]))


# Convert [['A'], ['B', 'C']] => [{'A'}, {'B', 'C'}]
def convert_FD_list_to_set(FD):
    return [set(FD[0]), set(FD[1])]


# Convert and sort [{'D', 'A'}, {'C', 'B'}] => [['A', 'D'], ['B', 'C']]
def convert_FD_set_to_list(FD):
    return [sorted(list(FD[0])), sorted(list(FD[1]))]


## Other business logic functions
#TODO: empty lhs means A can be determined without using any other attribute (so can omit from closure attribute?)
# F is a list of FD
# FD is the equivalent of a functional dependency, X -> {A}, in the data structure [[X],[A]] where X and A are >= 0 attribute items
# Remove FD with empty X or empty A
# Example: remove_empty_FD([[['A', 'B'], ['C']], [['A'], []]]) => [[['A', 'B'], ['C']]] 
def remove_empty_FD(F):
    return list(filter(lambda FD: (len(FD[0]) > 0 and len(FD[1]) > 0), F))


# Get all combinations of subsets for a list of attributes
# Example: get_subset_combination(['A', 'B']) => [['A'], ['B'], ['A', 'B']]
def get_subset_combination(attribute_list):
    subsets = []
    for i in range(1, len(attribute_list) + 1):
        combinations = itertools.combinations(attribute_list, i)
        subsets.extend(sorted(list(k)) for k in combinations)
    return subsets


# Get closure for S, an attribute set represented by a list of attributes
# R is schema, also represented by a list of attributes in the schema
# F is a list of functional dependencies
# Returns a sorted list of attributes functionally determined by S
def get_one_closure(R, F, S):
    # Convert FD in list to set to use Python set utilities (e.g .issubset()) for better performance
    F_set = [convert_FD_list_to_set(FD) for FD in F.copy()]
    # By Armstrong Axioms Reflexivity Rule, each attribute in S functionally determines itself
    determined_attributes = set(S)

    while (True):
        counter = 0

        for FD in F_set:
            # With a combination of Armstrong Axioms Decomposition, Union, and Transitivity Rule
            # Any FD with left hand-side a subset of the current determined_attributes, means FD right hand-side can be determined by S
            # Example: if S = ['A', 'B'], determined_attributes = {'A', 'B', 'C'}, and FD = [['B', 'C'], ['D']]
            # Since AB -> B, AB -> C, by union rule, AB -> BC. By transitivity rule, AB -> BC and BC -> D => AB -> D
            # Thus 'D' can then be added into determined_attributes set, and other attributes (in FD with 'D' as a subset of left hand-side) can be inferred in the next loop
            if FD[0].issubset(determined_attributes) and (len(FD[1] - determined_attributes) > 0):
                determined_attributes.update(FD[1] - determined_attributes)
                counter += 1

        # if counter == 0, means no more FD could be inferred, so break out of loop to stop inferring
        if (len(determined_attributes) == len(R)) or (counter == 0):
            break

    return sorted(list(determined_attributes))


# Get a list of minimal covers, based on
# F, a list of FDs (or FDs decomposed from closure)
# restrict_to_first_min_cover, a boolean, when set to True, only find one permutation of minimal cover
def get_min_covers(R, F, restrict_to_first_min_cover):
    # Convert FDs from 'list' type to 'set' type for better performance
    converted_F_with_FD_set = [convert_FD_list_to_set(FD) for FD in F.copy()]

    # Step 1 - get F': Minimize right hand-side of every functional dependency to attain form X -> {A}
    # 1a. This is done by using Armstrong Axioms Decomposition Rule
    # Example: if one FD = [['A', 'B'], ['C', 'D']], after completing step 1 and decomposed this FD, 
    # we get => [['A', 'B'], ['C']], [['A', 'B'], ['D']] (resulting into 2 FDs)
    simplified_rhs_F = decompose_FD(converted_F_with_FD_set)

    # 1b. Also remove trivial FDs (which may have been added during 1a. decomposition)
    # Example: this will remove trivial FD = [['A', 'B'], ['A']] and [['A'], ['A']]
    simplified_rhs_F = remove_trivial_FD(simplified_rhs_F)

    # Step 2 - get F'': Minimize left hand-side of every functional dependency, 
    # such that for every functional dependency in the form X -> {A} there is no functional dependency Y -> {A} with Y being a proper subset of X
    # 2a. Infer additional transitive FDs using Armstrong Axioms Transitivity Rule
    # Found transitive FDs could be used to replace FDs with superset left hand-side later
    incl_transitive_F = add_transitive_FD(simplified_rhs_F)

    # 2b. Replace FDs having superset left hand-side with transitive FDs that is its subset on left hand-side
    # Example: original FD = [['A', 'B'], ['C']] could be replaced with simpler FD [['A'], ['C']]
    # Also remove attribute from left hand-side if there is any FD implying a subset of lhs determines another subset of lhs
    # Example: original FD = [['A', 'B'], ['C']], another FD = [['A'], ['B']], this could be simplified to [['A'], ['C']]
    # As each FD can be replaced by one or more simpler FD (resulting in different minimal cover outcome),
    # return many permutations (a list) of simplified F based on each replacement possibility, product of possibilities with other replaceable FDs
    many_simplified_lhs_rhs_F = simplify_lhs_FD(simplified_rhs_F, incl_transitive_F, restrict_to_first_min_cover)

    # Step 3 - get F''': Minimize the set, such that none of the FD can be derived from other FDs
    # 3a. Remove duplicated FDs within each simplified F
    # And remove duplicated F (with exact same FDs across more than one F), this will prevent performance issue in next step when number of permutations increase further
    many_simplified_lhs_rhs_F = [remove_duplicate_FD(simplified_F) for simplified_F in many_simplified_lhs_rhs_F]
    many_simplified_lhs_rhs_F = remove_duplicate_F(many_simplified_lhs_rhs_F, is_convert_FD_to_list = False)

    # 3b. Remove transitive FDs within each simplified F that can be derived using Armstrong Axioms Transitivity Rule from other FDs
    # As we can reach different minimal cover outcome based on which transitive FD is removed first,
    # we find permutations and rotate the order of removable transitive FD within F itself, before removing transitive FD sequentially 
    # This will result in even more sets of min_covers, nested in the list of permutations from 2b 
    many_min_covers_nested = [remove_transitive_FD(simplified_F, restrict_to_first_min_cover) for simplified_F in many_simplified_lhs_rhs_F]
    # Flatten nested list from 3b and 2b into a list of min_cover
    many_min_covers = [min_cover for many_min_covers_list in many_min_covers_nested for min_cover in many_min_covers_list]

    # Remove duplicated minimal covers, and convert FD from set back into list
    many_unique_min_covers = remove_duplicate_F(many_min_covers, is_convert_FD_to_list = True)

    return many_unique_min_covers


# F is a list of FDs in 'set' type
# Returns a new list of FDs, with the addition of decomposed FDs
# Using Armstrong Axioms decomposition rule, decompose FD into multiple FDs if right hand-side of FD has multiple attributes
# Example: [{'A', 'B'}, {'C', 'D'}] => [{'A', 'B'}, {'C'}] and [{'A', 'B'}, {'D'}]
def decompose_FD(F):
    decomposed_F = []

    for FD in F:
        # Append a new FD for every attribute in the rhs
        for attribute in FD[1]:
            decomposed_F.append([FD[0], set([attribute])])

    return decomposed_F


# F is a list of FDs in 'set' type
# Returns a new list of FDs, excluding the trivial ones
# Example: this will remove trivial FD = [{'A', 'B'}, {'A'}] and [{'A'}, {'A'}] and [{'A', 'B'}, {'A', 'B'}]
def remove_trivial_FD(F):
    return list(filter(lambda FD: not FD[1].issubset(FD[0]), F))


# F is a list of FDs in 'set' type
# Returns a new list of FDs, with the addition of found transitive FDs, inferred using Armstrong Axioms Transitivity Rule
# Example: if F contains FDs [{'A'}, {'B'}] and [{'B'}, {'C'}], add new FD [{'A'}, {'C'}] to resulting list 
def add_transitive_FD(F):
    incl_transitive_F = F.copy()

    # Maintain a set of FD strings for quick searching to check if FD is already added
    unique_F_string_set = set([convert_FD_list_to_string(FD) for FD in F.copy()])

    # Infer transitive FD from original F and added transitive FDs continuously, until loop is broken when no more FD can be inferred
    while True:
        counter = 0

        for outer_FD in incl_transitive_F:
            outer_FD_lhs, outer_FD_rhs = outer_FD

            for inner_FD in incl_transitive_F:
                inner_FD_lhs, inner_FD_rhs = inner_FD

                # Check if outer FD's right hand-side matches with inner FD's left hand-side to find transitive FD (Armstrong Axioms Transitivity Rule)
                # But ignore trivial FD
                if inner_FD_lhs == outer_FD_rhs and not inner_FD_rhs.issubset(outer_FD_lhs):
                    transitive_FD = convert_FD_set_to_list(
                        [outer_FD_lhs, inner_FD_rhs])
                    transitive_FD_string = convert_FD_list_to_string(
                        transitive_FD)

                    # Check if transitive FD is already added previously
                    if transitive_FD_string not in unique_F_string_set:
                        # New transitive FD, add to cumulative list and set
                        incl_transitive_F.append(convert_FD_list_to_set(transitive_FD))
                        unique_F_string_set.add(transitive_FD_string)
                        counter += 1

        if counter == 0:
            # No new transitive FD has been added in last round of while loop, stop finding transitive FD
            break

    return incl_transitive_F

# simplified_F and incl_transitive_F are both a list of FDs in 'set' type
# however incl_transitive_F should include additional transitive FDs compared to simplified_F 
# incl_transitive_F will be used during the simplication process to look for alternative FDs with minimal left hand-side
# When restrict_to_first_min_cover = True, algorithm will only return first combination of simplified alternative FDs instead of all combinations 
def simplify_lhs_FD(unsorted_simplified_F, unsorted_incl_transitive_F, restrict_to_first_min_cover):
    # Sort both F list from lhs singletons, to pairs, to triplets, etc
    # This makes the algorithm to find alternative minimal lhs for each FD more efficient later
    # because loop can be broken once a larger set of lhs is reached
    simplified_F = sorted(unsorted_simplified_F, key = lambda x: len(x[0]))
    incl_transitive_F = sorted(unsorted_incl_transitive_F, key = lambda x: len(x[0]))

    # all_alt is a nested list of FDs that have simplified alternative left hand-side for each FD
    # There could be 0, or many alternatives for each FD, which will lead to different outcomes of minimal covers
    # Store simplified alternative FDs separately instead of replacing into original list directly
    # This is to find all minimal covers by choosing different alternatives later
    # Length of all_alt corresponds to original FD list, so as to replace into original list using same index later
    # E.g. FD in all_alt[2] will replace into simplified_F[2] afterwards
    all_alt = [[] for i in range(len(simplified_F))]

    # Find alternative FDs with minimal lhs
    for FD_index, outer_FD in enumerate(simplified_F):
        outer_FD_lhs, outer_FD_rhs = outer_FD

        # If left hand-side is already simplified to 1 attribute, then skip this FD
        if len(outer_FD_lhs) == 1:
            continue

        # Loop through list of FDs (including transitive ones) to find FDs that have simpler lhs
        for inner_FD in incl_transitive_F:
            inner_FD_lhs, inner_FD_rhs = inner_FD

            # We want to replace left hand-side of outer FD with smaller subset
            # If inner FD left hand-side is equal or greater than outer FD lhs in length, then break
            if len(inner_FD_lhs) >= len(outer_FD_lhs):
                break

            FD_alt = all_alt[FD_index]

            # Simplification scenario 1:
            # outer FD rhs = inner FD rhs, AND inner FD lhs is a smaller subset of outer FD lhs
            # AND inner FD lhs has same number of attributes as any previously added alternatives, not more, otherwise it will not be minimal lhs alternative
            if outer_FD_rhs == inner_FD_rhs and inner_FD_lhs.issubset(outer_FD_lhs) and (len(FD_alt) == 0 or len(inner_FD_lhs) == len(FD_alt[0][0])):
                all_alt[FD_index].append(inner_FD)
                continue

            # Simplification scenario 2:
            # Using Armstrong Axioms Transitivity Rule, inner FD implies that a subset of outer FD lhs functionally determines another subset of outer FD lhs
            # Example - outer FD = {A, B} -> {C}, and inner FD = {A} -> {B}, then outer FD can be replaced with {A} -> {C}
            # AND lhs of FD to add as alt, has same number of attributes as any previously added alternatives, not more, otherwise it will not be minimal lhs alternative
            if inner_FD_lhs.issubset(outer_FD_lhs) and inner_FD_rhs.issubset(outer_FD_lhs - inner_FD_lhs) and (len(FD_alt) == 0 or len(outer_FD_lhs - inner_FD_rhs) == len(FD_alt[0][0])):
                all_alt[FD_index].append(
                    [(outer_FD_lhs - inner_FD_rhs), outer_FD_rhs])


        # Remove duplicated alternatives now, else it will lead to more unnecessary permutated outcomes later
        all_alt[FD_index] = remove_duplicate_FD(all_alt[FD_index])


    # Get combinations of alternatives to find all minimal covers
    # To use Python's itertools.product, convert FD format alternatives (nested list) into ids (string of nested indexes)
    # Example - if all_alt = [[], [[{'A', 'E'}, {'F'}]]], id of alt FD [{'A', 'E'}, {'F'}] => '1-0', all_alt_ids = [['1-0']] 
    all_alt_ids = []

    # Convert all alternatives into id
    for FD_index, FD_alt in enumerate(all_alt):
        # No alternative for this FD, skip to next FD
        if len(FD_alt) == 0:
            continue

        ids = [(str(FD_index) + '-' + str(alt_index)) for alt_index, alt in enumerate(FD_alt)]
        all_alt_ids.append(ids)

    # If all FDs have no alternatives, exit and return only original F passed in as argument
    if len(all_alt_ids) == 0:
        return [simplified_F]

    # Get combinations of alternatives' ids, only one alt id for each FD should be in one combination 
    # Example: if all_alt_ids = [['3-0'], ['4-0'], ['6-0', '6-1']] => all_combinations = [('3-0', '4-0', '6-0'), ('3-0', '4-0', '6-1')]
    all_combinations = list(itertools.product(*all_alt_ids))

    # If mode is set to only get one minimal cover, limit to only the first combination
    if restrict_to_first_min_cover:
        all_combinations = [all_combinations[0]]

    # Generate many sets of F based on different combinations of lhs alternatives for each FD
    # This will get all minimal covers later (will also remove duplicated outcomes later)
    many_F = []
    for combi in all_combinations:
        alt_F = simplified_F.copy()

        for alt_id in combi:
            split_id = alt_id.split('-')
            FD_index = int(split_id[0])
            alt_index = int(split_id[1])
            # Replace original FD with simplified alternative FD in this combination
            alt_F[FD_index] = all_alt[FD_index][alt_index]
        many_F.append(alt_F)

    return many_F


# F is a list of FDs in 'set' or 'list' type
# Returns a new list of FDs, excluding those that are duplicates (left hand-side and right hand-side matches with another FD)
def remove_duplicate_FD(F):
    unique_F = []
    unique_F_string_set = set()

    for FD in F:
        FD_string = convert_FD_list_to_string(convert_FD_set_to_list(FD))

        if FD_string not in unique_F_string_set:
            unique_F.append(FD)
            unique_F_string_set.add(FD_string)

    return unique_F

# F is a list of FDs in 'set' type
# Return a list of F, with transitive FDs removed based on different permutations of order for each F returned
# When restrict_to_first_min_cover = True, algorithm will only return first permutation of removing transitive FDs order instead of all permutations 
def remove_transitive_FD(F, restrict_to_first_min_cover):
    omittable_FD = []
    non_omittable_FD = []

    # Find FD that could be replaced by other FDs using Armstrong Axioms Transitivity Rule
    # Do not remove omittable FDs from original F yet, find permutations to remove omittable FDs in sequence later, as it may affect outcome of minimal cover
    for outer_FD_index, outer_FD in enumerate(F):
        is_omittable = False

        # Find matching first_inner_FD and second_inner_FD, first_inner_FD and second_inner_FD together should transitively infer outer_FD
        # Example: if outer_FD = [{'A'}, {'D'}], a first_inner_FD [{'A'}, {'B'}] and second_inner_FD [{'B'}, {'D'}] 
        # would mean outer_FD can be transitively inferred and thus can be removed
        for first_inner_FD_index, first_inner_FD in enumerate(F):
            if is_omittable:
                break

            if outer_FD_index == first_inner_FD_index:
                continue

            # first_inner_FD needs to match outer_FD lhs
            if outer_FD[0] == first_inner_FD[0]:
                
                for second_inner_FD_index, second_inner_FD in enumerate(F):
                    if outer_FD_index == second_inner_FD_index:
                        continue
                    
                    # second_inner_FD lhs needs to match first_inner_FD rhs, and second_inner_FD rhs to match outer_FD rhs
                    if first_inner_FD[1] == second_inner_FD[0] and outer_FD[1] == second_inner_FD[1]:
                        omittable_FD.append(outer_FD) 
                        is_omittable = True
                        break
        
        if not is_omittable:
            non_omittable_FD.append(outer_FD)

    # If none of the FDs can be removed (cannot be inferred by remaining FDs transitively)
    # No need to find permutations of removal sequence, simply return original F, it is already the minimal cover
    if len(omittable_FD) == 0:
        return [F]

    # Find permutations of ordering omittable FDs differently within F list
    # Different minimal cover outcomes can be reached by:
    # removing omittable transitive FD -> check remaining FDs -> remove omittable transitive FD -> rinse and repeat sequentially  
    omittable_ids = ''.join([str(index) for index in range(len(omittable_FD))])
    permutations = list(itertools.permutations(
        omittable_ids, len(omittable_FD)))

    # If mode is set to only get one minimal cover, limit to only the first permutation
    if restrict_to_first_min_cover:
        permutations = [permutations[0]]

    # Create a list of F, each F is based on a permutation of ordering the omittable FDs
    # No additional permutations need to be found for non_omittable FDs
    # as their ordering do not affect the minimal cover outcomes
    # this reduces the number of permutations, and improve performance
    many_F_with_omittable_rotated = []
    for permutation in permutations:
        omittable_permutation = [
            omittable_FD[int(omittable_index)] for omittable_index in permutation]
        many_F_with_omittable_rotated.append(
            [*omittable_permutation, *non_omittable_FD])


    for rotated_F in many_F_with_omittable_rotated:
        # Remove transitive FDs sequentially and check before removing the next
        for outer_FD_index, outer_FD in enumerate(rotated_F):
            is_outer_FD_removed = False

            for first_inner_FD_index, first_inner_FD in enumerate(rotated_F):
                if is_outer_FD_removed:
                    break

                # Skip if inner_FD has been removed in previous outer_FD loop
                # or skip if same FD for outer and inner loop
                if first_inner_FD is None or outer_FD_index == first_inner_FD_index:
                    continue
                
                # Find first and second inner FD that matches to transitively infer outer_FD
                # If two inner FDs are found, outer_FD can be removed
                if outer_FD[0] == first_inner_FD[0]:
                    for second_inner_FD_index, second_inner_FD in enumerate(rotated_F):
                        # Skip if inner_FD has been removed in previous outer_FD loop
                        # or skip if same FD for outer and inner loop
                        if second_inner_FD is None or outer_FD_index == second_inner_FD_index:
                            continue
                        
                        # second_inner_FD lhs needs to match first_inner_FD rhs, and second_inner_FD rhs to match outer_FD rhs
                        if first_inner_FD[1] == second_inner_FD[0] and outer_FD[1] == second_inner_FD[1]:
                            # Two matching inner FDs are found, remove outer_FD from rotated_F
                            # So that it is not usable by the inner_FD in the next loop
                            rotated_F[outer_FD_index] = None
                            is_outer_FD_removed = True
                            break

    # Remove FD elements that are None from each F, to get minimal cover
    many_F_filtered_out_removed = []
    for new_F in many_F_with_omittable_rotated:
        many_F_filtered_out_removed.append(
            list(filter(lambda FD: FD is not None, new_F)))

    return many_F_filtered_out_removed


# many_F takes in a list of F, containing FDs in 'set' or 'list' type
# Returns a list of F that are unique (all FDs in each F do not match all FDs of another F)
def remove_duplicate_F(many_F, is_convert_FD_to_list=False):
    many_unique_F = []
    # Store each unique F as set of FD strings, to compare uniqueness of FD set more performantly
    many_unique_F_set = [] # Example: [{'AB->C', 'D->E'}, {'B->D', 'CD->E'}]
    
    # Loop through each F to check for uniqueness
    for F in many_F:
        F_set = set(convert_FD_list_to_string(convert_FD_set_to_list(FD)) for FD in F)

        # If current loop is a unique F, it will not exactly match FDs with any previously added unique F
        if (len(many_unique_F_set) == 0) or all(True if unique_F_set != F_set else False for unique_F_set in many_unique_F_set):
            # this F is unique, add to unique list
            if is_convert_FD_to_list is True:
                # Also convert FD from set back to list
                many_unique_F.append([convert_FD_set_to_list(FD) for FD in F])
            else:
                many_unique_F.append(F)

            many_unique_F_set.append(F_set)

    return many_unique_F



## Main functions
# def main():
#     ### Test case from the project
#     R = ['A', 'B', 'C', 'D']
#     FD = [[['A', 'B'], ['C']], [['C'], ['D']]]

#     print(closure(R, FD, ['A']))
#     print(closure(R, FD, ['A', 'B']))
#     print(all_closures(R, FD))

#     R = ['A', 'B', 'C', 'D', 'E', 'F']
#     FD = [[['A'], ['B', 'C']], [['B'], ['C','D']], [['D'], ['B']], [['A','B','E'], ['F']]]
#     print(min_cover(R, FD)) 

#     R = ['A', 'B', 'C']
#     FD = [[['A'], ['B']], [['B'], ['C']], [['C'], ['A']]] 
#     print(min_covers(R, FD))
#     print(all_min_covers(R, FD)) 

    ### Add your own additional test cases if necessary


def main():

    print('TESTING...')

    print('============================================')
    print('get_subset_combination()')
    get_subset_combination_input = ['A', 'B', 'C', 'D']
    print('input =', get_subset_combination_input)
    print('\n')
    print(get_subset_combination(get_subset_combination_input))
    print('\n============================================\n\n')

    print('============================================')
    print('remove_empty_FD()')
    remove_empty_FD_input = [[['A', 'B'], ['C']], [['C'], ['D']], [[], ['A']], [['B'], []] ]
    print('input =', remove_empty_FD_input)
    print('\n')
    print(remove_empty_FD(remove_empty_FD_input))
    print('\n============================================\n\n')

    print('============================================')
    print('remove_trivial_FD()')
    remove_trivial_FD_input = [[{'A', 'B'}, {'C'}], [{'C'}, {'D'}], [{'A'}, {'A'}], [{'A', 'B'}, {'A'}], [{'B', 'D'}, {'B', 'D'}], [{'B', 'E'}, {'B', 'E', 'F'}] ]
    print('input =', remove_trivial_FD_input)
    print('\n')
    print(remove_trivial_FD(remove_trivial_FD_input))
    print('\n============================================\n\n')

    print('============================================')
    print('decompose_FD()')
    decompose_FD_input = [[{'A', 'B'}, {'C', 'D', 'E'}], [{'C'}, {'D'}], [{'A'}, {'B', 'F'}] ]
    print('input =', decompose_FD_input)
    print('\n')
    print(decompose_FD(decompose_FD_input))
    print('\n============================================\n\n')

    print('============================================')
    print('add_transitive_FD()')
    add_transitive_FD_input = [[{'A', 'B'}, {'C'}], [{'C'}, {'D'}], [{'D'}, { 'E'}], [{'B'}, {'D'}] ]
    print('input =', add_transitive_FD_input)
    print('\n')
    print(add_transitive_FD(add_transitive_FD_input))
    print('\n============================================\n\n')
    
    print('============================================')
    print('remove_duplicate_FD()')
    remove_duplicate_FD_input = [[{'A', 'B'}, {'C', 'D', 'E'}], [{'C'}, {'D'}], [{'A'}, {'B', 'F'}], [{'B', 'A'}, {'E', 'D', 'C'}], [{'C'}, {'D'}] ]
    print('input =', remove_duplicate_FD_input)
    print('\n')
    print(remove_duplicate_FD(remove_duplicate_FD_input))
    print('\n============================================\n\n')

    print('============================================')
    print('remove_duplicate_F()')
    remove_duplicate_F_input = [
        [[{'A'}, {'C'}], [{'B', 'A'}, {'A'}], [{'C'}, {'A'}], [{'A'}, {'B'}]], 
        [[{'B'}, {'C'}], [{'C'}, {'A'}], [{'A'}, {'B'}]], 
        [[{'C'}, {'B'}], [{'A'}, {'C'}], [{'C'}, {'A'}], [{'B'}, {'C'}]], 
        [[{'C'}, {'B'}], [{'A', 'D'}, {'C'}], [{'B'}, {'A'}]], 
        [[{'B'}, {'C'}], [{'A'}, {'B'}], [{'B'}, {'A'}], [{'C'}, {'B'}]], 
        [[{'A'}, {'C'}], [{'A'}, {'B'}], [{'C'}, {'A'}], [{'B', 'A'}, {'A'}]],  
        [[{'C'}, {'B'}], [{'A', 'D'}, {'C'}], [{'B'}, {'A'}]]
    ]
    print('input =', remove_duplicate_F_input)
    print('\n convert to list')
    print(remove_duplicate_F(remove_duplicate_F_input, is_convert_FD_to_list=True))
    print('\n remain as set')
    print(remove_duplicate_F(remove_duplicate_F_input, is_convert_FD_to_list=False))
    print('\n')
    print('\n============================================\n\n')

    print('============================================')
    print('simplify_lhs_FD()')
    simplify_lhs_FD_input = [[[{'A','B', 'C'}, {'C'}], [{'A','B'}, {'C'}], [{'A'}, {'C'}], [{'C'}, {'D'}], [{'A'}, {'B'}]], [[{'A','B', 'C'}, {'C'}], [{'A','B'}, {'C'}], [{'C'}, {'D'}], [{'A'}, {'C'}], [{'B'}, {'C'}], [{'A'}, {'B'}]], False]
    # simplify_lhs_FD_input = [[[{'A'}, {'C'}], [{'C'}, {'D'}], [{'A'}, {'B'}]], [[{'A'}, {'C'}], [{'C'}, {'D'}], [{'A'}, {'B'}], [{'A'}, {'D'}]], False]
    print('input =', *simplify_lhs_FD_input)
    print('\n')
    print(simplify_lhs_FD(*simplify_lhs_FD_input))
    print('\n============================================\n\n')

    print('============================================')
    print('remove_transitive_FD()')
    remove_transitive_FD_input = [[[{'A'}, {'C'}], [{'A'}, {'B'}], [{'C'}, {'D'}], [{'B'}, {'C'}], [{'B'}, {'D'}], [{'A'}, {'D'}]], False]
    print('input =', *remove_transitive_FD_input)
    print('\n')
    print(remove_transitive_FD(*remove_transitive_FD_input))
    print('\n============================================\n\n')

    print('============================================')
    print('closure()')
    closure_input = [['A', 'B', 'C', 'D'], [[['A', 'B'], ['C']], [['C'], ['D']], [[], ['A']], [['B'], []]], ['A', 'B']]
    print('input =', *closure_input)
    print('\n')
    print(closure(*closure_input))
    print('\n============================================\n\n')

    print('============================================')
    print('all_closures()')
    all_closures_input = [['A', 'B', 'C', 'D'], [[['A', 'B'], ['C']], [['C'], ['D']], [[], ['A']], [['B'], []]]]
    print('input =', *all_closures_input)
    print('\n')
    print(all_closures(*all_closures_input))
    print('\n============================================\n\n')


    # R = ['A', 'B', 'C', 'D', 'E', 'F']
    # FD = [[['A'], ['B', 'C']], [['B'], ['C','D']], [['D'], ['B', 'C']], [['A','B','E'], ['F']]]
    # print(min_covers(R, FD))


#     print(closure(R, FD, ['A']))
#     print(closure(R, FD, ['A', 'B']))

    # R = ['A', 'B', 'C', 'D']
    # FD = [[['A', 'B'], ['C']], [['C'], ['D']]]

    # print(closure(R, FD, ['A']))
    # print(closure(R, FD, ['A', 'B']))


    # Test case from the project
    # R = ['A', 'B', 'C', 'D', 'E']
    # FD = [[['A'], ['B']], [['B'], ['C']], [['C'], ['D']], [['D'], ['E']]]

    # R = ['A', 'B', 'C', 'D']
    # FD = [[['A', 'B'], ['C']], [['C'], ['D']]]

    # print(closure(R, FD, ['A']))
    # print(all_closures(R, FD))
    # print(all_min_covers(R, FD))

    R = ['A', 'B', 'C', 'D', 'E', 'F']
    FD = [[['A'], ['B', 'C', 'E']], [['A', 'E'], ['C', 'D']],
          [['D'], ['B']], [['A', 'B', 'E'], ['F']]]
    # FD = [[['A'], ['B', 'C']], [['B'], ['C','D']], [['D'], ['B', 'C']], [['A','B','E'], ['F']]]
    print(min_covers(R, FD))


if __name__ == '__main__':
    main()



