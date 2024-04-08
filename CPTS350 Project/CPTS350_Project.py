from pyeda.inter import *

# Step 3.1: Obtain BDDs for R, [even], [prime]
def obtain_bdds():
    # Define the variables
    variables = exprvars('v', 32)

    # Define the sets
    even_set = Or(*[variables[i] for i in range(0, 32, 2)])
    prime_set = Or(*[variables[i] for i in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]])

    # Create BDDs for the sets
    EVEN = expr2bdd(even_set)
    PRIME = expr2bdd(prime_set)

    # Define the edges
    edges = []
    for i in range(32):
        for j in range(32):
            if (i + 3) % 32 == j % 32 or (i + 8) % 32 == j % 32:
                edges.append(variables[i] & variables[j])

    # Create BDD for the edges
    RR = expr2bdd(Or(*edges))

    print("EVEN BDD:", EVEN)
    print("PRIME BDD:", PRIME)
    print("RR BDD:", RR)
    print("Graph G:", edges)

    return RR, EVEN, PRIME

# Test cases
def test_bdds(RR, EVEN, PRIME):
    variables = RR.inputs
    #print(RR.restrict({variables[27]: 1, variables[3]: 1}).satisfy_one())
    assert RR.restrict({variables[27]: 1, variables[3]: 1}).satisfy_one() is not None, "There should be a path from node 27 to node 3"
    #print(RR.restrict({variables[16]: 1, variables[20]: 1}).satisfy_one())
    assert RR.restrict({variables[16]: 1, variables[20]: 1}).satisfy_one(), "There should not be a path from node 16 to node 20"
    #print(EVEN.restrict({variables[14]: 1}).satisfy_one())
    assert EVEN.restrict({variables[14]: 1}).satisfy_one() is not None, "Node 14 should be even"
    #print(EVEN.restrict({variables[13]: 1}).satisfy_one())
    assert EVEN.restrict({variables[13]: 1}).satisfy_one(), "Node 13 should not be even"
    #print(PRIME.restrict({variables[7]: 1}).satisfy_one())
    assert PRIME.restrict({variables[7]: 1}).satisfy_one() is not None, "Node 7 should be prime"
    #print(PRIME.restrict({variables[2]: 1}).satisfy_one())
    assert PRIME.restrict({variables[2]: 1}).satisfy_one(), "Node 2 should not be prime"



# Step 3.2: Compute BDD RR2 for the set R ◦ R
def compute_rr2(RR):
    RR2 = expr2bdd(RR & RR)
    return RR2

# Test cases for RR2
def test_rr2(RR2):
    variables = RR2.inputs
    assert RR2.restrict({variables[27]: 1, variables[6]: 1}).satisfy_one() is not None, "There should be a path from node 27 to node 6 in 2 steps"
    assert RR2.restrict({variables[27]: 1, variables[9]: 1}).satisfy_one(), "There should not be a path from node 27 to node 9 in 2 steps"

# Step 3.3: Compute the transitive closure RR2star of RR2
def compute_rr2star(RR2):
    rr2star_bdd = ~RR2.smoothing()
    return rr2star_bdd

# Step 3.4: Test StatementA
def test_statement_a(rr2star_bdd, PRIME, EVEN):
    # Apply AND operation to negated EVEN
    temp_bdd = rr2star_bdd & ~EVEN
    # Perform quantification
    exists_bdd = temp_bdd.smoothing()
    # Implication: PRIME -> exists_bdd
    implication_bdd = ~PRIME | exists_bdd
    # Check if there exists a satisfying assignment
    return implication_bdd.satisfy_one() is not None

# Main function
def main():
    RR, EVEN, PRIME = obtain_bdds()
    test_bdds(RR, EVEN, PRIME)

    RR2 = compute_rr2(RR)
    test_rr2(RR2)

    rr2star_bdd = compute_rr2star(RR2)

    result = test_statement_a(rr2star_bdd, PRIME, EVEN)
    print("Result:")
    print("StatementA is\x1B[32m", result)
    print("\nFor each node u in [prime], there is a node v in [even]\x1B[0m")

if __name__ == "__main__":
    main()
