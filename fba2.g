Read("fba.g");

# Implementation of the field-based attack for AAG protocol (unknown f).
field_based_attack_2 := function(G, bs, conjugated_bs)
    local i, j, k, b, conjugated_b, t, M, n, c, d;
    d := [];
    M := [];
    n := Length(G.ring_basis);
    for i in [1..2*n] do
        Add(M, []);
    od;
    for i in [1..Length(bs)] do
        b := convert_word_to_pair(G, bs[i]);
        conjugated_b := convert_word_to_pair(G, conjugated_bs[i]);
        Append(d, UnderlyingElement(get_o(conjugated_b)));
        for j in [1..n] do
            for k in [1..n] do
                if j = k then
                    Add(M[j], 1 - UnderlyingElement(get_u(b))[j][k]);
                else
                    Add(M[j], -UnderlyingElement(get_u(b))[j][k]);
                fi;
            od;
        od;
        for j in [1..n] do
            Append(M[n+j], UnderlyingElement(get_o(b)) * G.field_basis[j]);
        od;
        if RankMat(M) = 2*n then
            c := SolutionMat(M, d); 
            return convert_pair_to_word(G, make_semidirect_pair(rec(
                u := make_matrix(Sum(ListN(c{[n+1..2*n]}, G.field_basis, function(a, b) return a*b; end))), 
                o := make_matrix(c{[1..n]}))));
        fi;
    od;
   return fail; 
end;

generate_O_by_U_by_f := function(f)
    local F, O, U, i, G, a;
    F := FieldByMatricesNC([CompanionMat(f)]);
    O := MaximalOrderBasis(F);
    U := UnitGroup(F);
    i := IsomorphismPcpGroup(U);
    G := Image(i);
    a := List(List(Pcp(G), u -> PreImagesRepresentative(i, u)), u -> List(O, o -> Coefficients(O, o * u)));
    return SplitExtensionPcpGroup(G, a);
end;


# Splits generators of group to correspondings to (U_i, O) and (E, O_j).
get_us_and_os := function(presentation)
    local i, j, gs, nm, os, us;
    gs := GeneratorsOfPcp(Pcp(presentation));
    nm := Length(gs);
    os := Set([]);
    for i in [1..nm] do           
        for j in [i+1..nm] do
            if gs[j]^gs[i] <> gs[j] then
                AddSet(os, j);
            fi;
        od;
    od;
    us := Set([1..nm]);
    SubtractSet(us, os);
    return rec(us := us, os := os);
end;


# Returns map g_i --> (M, v).
get_matrices_and_vectors := function(presentation, uos)
    local gs, as, us, os, n, m, i, j, es, u, k, o, l, a;
    gs := GeneratorsOfPcp(Pcp(presentation));
    n := Length(uos.os);
    as := [];
    l := 1;
    for k in [1..Length(GeneratorsOfPcp(Pcp(presentation)))] do
        if k in uos.us then
            a := NullMat(n, n);
            for i in [1..n] do 
                es := Exponents(gs[uos.os[i]]^gs[k]);
                for j in [1..n] do
                    a[i][j] := es[uos.os[j]];
                od;
            od;
            o := List([1..n], i -> 0);
            Add(as, make_semidirect_pair(rec(u := make_matrix(a), o := make_matrix(o))));
        else
            o := List([1..n], i -> 0);
            o[l] := 1;
            l := l + 1;
            Add(as, make_semidirect_pair(rec(u := make_matrix(IdentityMat(n)), o := make_matrix(o))));
        fi;
    od;
    return as;
end;


# Generates the semidirect product U and O by polycyclic presentation.
generate_O_by_U_by_presentation_with_extra_info := function(presentation)
    local ms, F, O, U, uos, us, m;
    uos := get_us_and_os(presentation);
    ms := get_matrices_and_vectors(presentation, uos);
    us := [];
    for m in ms do
        if get_u(m) <> One(get_u(m)) then
            Add(us, UnderlyingElement(get_u(m)));
        fi;
    od;
    F := FieldByMatrices(us);
    O := MaximalOrderBasis(F);
    U := UnitGroup(F);
    return rec(
        presentation := presentation, 
        ring_basis := Basis(VectorSpace(Rationals, IdentityMat(Length(O)))), 
        field := F,
        field_basis := Basis(F),
        u_gens := GeneratorsOfPcp(Pcp(presentation)){uos.us}, 
        o_gens := GeneratorsOfPcp(Pcp(presentation)){uos.os},
        unit_coeffs := ExponentsOfUnits(F, us)^-1,
        pairs := ms);
end;
