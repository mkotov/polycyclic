# Constructor for an element of the semidirect product of U and O.
make_semidirect_pair := ArithmeticElementCreator(rec(
    ElementName := "semidirect_pair",
    One := a -> rec(u := One(a.u), o := Zero(a.o)),
    Multiplication := function(a, b) return rec(u := a.u * b.u, o := a.o * b.u + b.o); end,
    Inverse := function(a) return rec(u := a.u^-1, o := -a.o * a.u^-1); end, 
    Equality := function(a, b) return a.u = b.u and a.o = b.o; end, 
    MathInfo := IsMultiplicativeElementWithInverse and IsAssociativeElement
));


# Getter u.
get_u := function(p)
    return UnderlyingElement(p).u;
end;


# Getter o.
get_o := function(p)
    return UnderlyingElement(p).o;
end;


# Constructor for a matrix.
make_matrix := ArithmeticElementCreator(rec(
    ElementName := "my_matrix",
    One := a -> One(a),
    Zero := a -> Zero(a),
    Multiplication := function(a, b) return a * b; end,
    Addition := function(a, b) return a + b; end,
    Inverse := function(a) return a^-1; end, 
    AdditiveInverse := function(a) return -a; end,
    Equality := function(a, b) return a = b; end, 
    MathInfo := IsScalar and IsAssociativeElement and IsAdditivelyCommutativeElement
));


# Converts a word w to the corresponding pair.
convert_word_to_pair := function(G, w)
    return Product(ListN([1..Length(G.pairs)], Exponents(w), function (i, p) return G.pairs[i] ^ p; end));
end;


# Returns x1, ..., xm s. t. M1^x1 * ... Mm^xm = a, where field = Q(M1, ..., Mm).
get_exponents := function(G, a) 
    return Sum(ListN(ExponentsOfUnits(G.field, [a])[1], G.unit_coeffs, function(e, u) return e * u; end));
end;


# Converts a pair  p to the corresponding word.
convert_pair_to_word := function(G, p)
    return Product(ListN(G.u_gens, get_exponents(G, UnderlyingElement(get_u(p))), function(g, n) return g ^ n; end)) *
        Product(ListN(G.o_gens, Coefficients(G.ring_basis, UnderlyingElement(get_o(p))), function(g, n) return g ^ n; end));
end;


# Implementation of the field-based attack for AAG protocol (known f).
field_based_attack := function(G, bs, conjugated_bs)
    local i, m, b, conjugated_b, c, d;
    m := [[], []];
    d := [];
    for i in [1..Length(bs)] do
        b := convert_word_to_pair(G, bs[i]);
        conjugated_b := convert_word_to_pair(G, conjugated_bs[i]);
        Add(m[1], One(get_u(b)) - get_u(b));
        Add(m[2], get_o(b));
        Add(d, get_o(conjugated_b));
        if RankMat(m) = 2 then
           c := SolutionMat(m, d); 
           return convert_pair_to_word(G, make_semidirect_pair(rec(u := c[2], o := c[1])));
        fi;
    od;
    return fail;
end;


# Generates the semidirect product U and O, where O is the maximal order of F, U is the group of unit of F.
generate_O_by_U_by_f_with_extra_info := function(f)
    local F, O, U, i, G, a, n, p, m;
    F := FieldByMatricesNC([CompanionMat(f)]);
    O := MaximalOrderBasis(F);
    U := UnitGroup(F);
    i := IsomorphismPcpGroup(U);
    G := Image(i);
    a := List(List(Pcp(G), u -> PreImagesRepresentative(i, u)), u -> List(O, o -> Coefficients(O, o * u)));
    n := Length(O);
    m := Length(GeneratorsOfGroup(U));
    p := SplitExtensionPcpGroup(G, a);
    return rec(
        presentation := p, 
        ring_basis := O,
        field := F,
        field_basis := Basis(F),
        u_gens := GeneratorsOfPcp(Pcp(p)){[1..m]}, 
        o_gens := GeneratorsOfPcp(Pcp(p)){[m+1..m+n]},
        unit_coeffs := IdentityMat(m),
        pairs := Concatenation(
            List(GeneratorsOfGroup(U), g -> make_semidirect_pair(rec(u := make_matrix(g), o := make_matrix(Zero(g))))), 
            List(O, g -> make_semidirect_pair(rec(u := make_matrix(One(g)), o := make_matrix(g))))));
end;
