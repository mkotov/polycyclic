# Returns the length of w. The length is defined as the sum of the absolute values of the exponents of the generators.
get_word_length := function(w)
    return Sum(Exponents(w), x -> AbsInt(x));
end;


# Returns the length of set. The length of a set is defined as the sum of the length of the elements.
get_set_length := function(set) 
    return Sum(set, w -> get_word_length(w));
end;


# Implementation of length-based attack for AAG.
length_based_attack := function(as, bs, conjugated_bs)
    local s, a, best, conjugated_best, epsilon, t;
    s := Set([[get_set_length(conjugated_bs), conjugated_bs, One(conjugated_bs[1])]]);
    while Length(s) > 0 do
        best := Remove(s, 1);
        for epsilon in [-1, 1] do
            for a in as do
                t := List(best[2], x -> x ^ (a ^ epsilon));
                conjugated_best := [get_set_length(t), t, best[3] * a ^ epsilon];
                if conjugated_best[2] = bs then
                    return conjugated_best[3]^-1;
                fi;
                if best[1] - conjugated_best[1] > 0 then
                    AddSet(s, conjugated_best);
                fi;
            od;
        od;
    od;
    return fail;
end;


# Constructor for an element of the semidirect product of U and O. The element is presented as pair of matries.
make_pair_of_matrices := ArithmeticElementCreator(rec(
    ElementName := "pair_of_matrices",
    One := a -> rec(u := One(a.u), o := Zero(a.o)),
    Multiplication := function(a, b) return rec(u := a.u * b.u, o := a.o * b.u + b.o); end,
    Inverse := function(a) return rec(u := a.u ^ -1, o := -a.o * a.u ^ -1); end, 
    Equality := function(a, b) return a.u = b.u and a.o = b.o; end, 
    MathInfo :=  IsMultiplicativeElementWithInverse and IsAssociativeElement
));


get_u := function(p)
    return UnderlyingElement(p).u;
end;


get_o := function(p)
    return UnderlyingElement(p).o;
end;


# Constructor for a square matrix as an element of the corresponding matrix ring.
make_square_matrix := ArithmeticElementCreator(rec(
    ElementName := "square_matrix",
    One := a -> One(a),
    Zero := a -> Zero(a),
    Multiplication := function(a, b) return a * b; end,
    Addition := function(a, b) return a + b; end,
    Inverse := function(a) return a ^ -1; end, 
    AdditiveInverse := function(a) return -a; end,
    Equality := function(a, b) return a = b; end, 
    MathInfo := IsScalar and IsAssociativeElement and IsAdditivelyCommutativeElement
));


# Generates the direct product U and O, where O is the maximal order of F, U is the group of unit of F.
generate_maximal_order_by_units_group := function(f)
    local F, O, U, i, G, a;
    F := FieldByMatricesNC([CompanionMat(f)]);
    O := MaximalOrderBasis(F);
    U := UnitGroup(F);
    i := IsomorphismPcpGroup(U);
    G := Image(i);
    a := List(List(Pcp(G), u -> PreImagesRepresentative(i, u)), u -> List(O, o -> Coefficients(O, o * u)));
    return rec(
        presentation := SplitExtensionPcpGroup(G, a), 
        basis_of_maximal_order := O, 
        field := F, 
        pair_of_matrices := Concatenation(
        List(GeneratorsOfGroup(U), g -> make_pair_of_matrices(rec(u := make_square_matrix(g), o := make_square_matrix(Zero(g))))), 
        List(O, g -> make_pair_of_matrices(rec(u := make_square_matrix(One(g)), o := make_square_matrix(g))))));
end;


# Converts a word w to the corresponding pair of matrices.
convert_word_to_pair_of_matrices := function(G, w)
    return Product(ListN([1..Length(G.pair_of_matrices)], Exponents(w), function (i, p) return G.pair_of_matrices[i] ^ p; end));
end;


# Converts a pair of matrices p to the corresponding word.
convert_pair_of_matrices_to_word := function(G, p)
    return Product(ListN(
        GeneratorsOfGroup(G.presentation),
        Concatenation(ExponentsOfUnits(G.field, 
            [UnderlyingElement(get_u(p))])[1], Coefficients(G.basis_of_maximal_order, UnderlyingElement(get_o(p)))),
        function(g, n) return g ^ n; end));
end;


# Implementation of the field-based attack for AAG protocol.
field_based_attack := function(G, bs, conjugated_bs)
    local i, m, b, conjugated_b, c, d;
    m := [[], []];
    d := [];
    for i in [1..Length(bs)] do
        b := convert_word_to_pair_of_matrices(G, bs[i]);
        conjugated_b := convert_word_to_pair_of_matrices(G, conjugated_bs[i]);
        Add(m[1], One(get_u(b)) - get_u(b));
        Add(m[2], get_o(b));
        Add(d, get_o(conjugated_b));
        if RankMat(m) = 2 then
           c := SolutionMat(m, d); 
           return convert_pair_of_matrices_to_word(G, make_pair_of_matrices(rec(u := c[2], o := c[1])));
        fi;
    od;
    return fail;
end;


test_field_based_attack := function(f, public_set_size, private_key_size, test_num)   
    local alice_public_set, bob_public_set, alice_private_key, conjugated_bob_public_set, 
            G, start_time, end_time, i, founded_alice_private_key, total_time;
    G := generate_maximal_order_by_units_group(f); 

    total_time := 0;
    for i in [1..test_num] do
        alice_public_set := List([1..public_set_size], i -> Random(G.presentation));
        bob_public_set := List([1..public_set_size], i -> Random(G.presentation));
        alice_private_key := Product(List([1..private_key_size], i -> Random(alice_public_set) ^ Random([-1, 1])));
        conjugated_bob_public_set := List(bob_public_set, x -> x ^ alice_private_key);
        start_time := Runtime();
        founded_alice_private_key := field_based_attack(G, bob_public_set, conjugated_bob_public_set);
        end_time := Runtime();
        total_time := total_time + end_time - start_time;
        if alice_private_key <> founded_alice_private_key then
            Print("The keys are different!");
        fi;
    od;
    Print(Degree(f), " ", HirschLength(G.presentation), " ", Float(total_time / test_num), " ", f, "\n");
end;


test_attacks := function(f, public_set_size, private_key_size, test_num)   
    local alice_public_set, bob_public_set, alice_private_key, conjugated_bob_public_set, 
            G, start_time, end_time, i, founded_alice_private_key, fba_total_time, lba_total_time;
    G := generate_maximal_order_by_units_group(f); 

    fba_total_time := 0;
    lba_total_time := 0;
    for i in [1..test_num] do
        alice_public_set := List([1..public_set_size], i -> Random(G.presentation));
        bob_public_set := List([1..public_set_size], i -> Random(G.presentation));
        alice_private_key := Product(List([1..private_key_size], i -> Random(alice_public_set) ^ Random([-1, 1])));
        conjugated_bob_public_set := List(bob_public_set, x -> x ^ alice_private_key);
        start_time := Runtime();
        founded_alice_private_key := field_based_attack(G, bob_public_set, conjugated_bob_public_set);
        end_time := Runtime();
        fba_total_time := fba_total_time + end_time - start_time;
        if alice_private_key <> founded_alice_private_key then
            Print("FBA: the keys are different!");
        fi;
 
        start_time := Runtime();
        founded_alice_private_key := length_based_attack(alice_public_set, bob_public_set, conjugated_bob_public_set);
        end_time := Runtime();
        lba_total_time := lba_total_time + end_time - start_time;
        if alice_private_key <> founded_alice_private_key then
            Print("LBA: the keys are different!");
        fi;
   od;
    Print(Degree(f), " ", HirschLength(G.presentation), " ", Float(fba_total_time / test_num), " ", 
        Float(lba_total_time / test_num), " ", f, "\n");
end;


x := Indeterminate(Rationals);
test_field_based_attack(x^2 - x - 1, 20, 5, 100);
test_field_based_attack(x^5 - x^3- 1, 20, 5, 100);
test_field_based_attack(x^7 - x^3 - 1, 20, 5, 100);
test_field_based_attack(x^9 - 7*x^3 - 1, 20, 5, 100);
test_field_based_attack(x^11 - x^3 - 1, 20, 5, 100);

test_field_based_attack(x^2 - x - 1, 20, 100, 100);
test_field_based_attack(x^5 - x^3- 1, 20, 100, 100);
test_field_based_attack(x^7 - x^3 - 1, 20, 100, 100);
test_field_based_attack(x^9 - 7*x^3 - 1, 20, 100, 100);
test_field_based_attack(x^11 - x^3 - 1, 20, 100, 100);

