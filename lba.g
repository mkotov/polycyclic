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
