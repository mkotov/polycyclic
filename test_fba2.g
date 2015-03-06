Read("fba2.g");

# Test suite
test_field_based_attack_2 := function(f, public_set_size, private_key_size, test_num)   
    local alice_public_set, bob_public_set, alice_private_key, conjugated_bob_public_set, 
            p, G, start_time, end_time, i, found_alice_private_key, total_time;
    start_time := Runtime();
    for i in [1..test_num] do
        p := generate_O_by_U_by_f(f);
        G := generate_O_by_U_by_presentation_with_extra_info(p); 
        alice_public_set := List([1..public_set_size], i -> Random(G.presentation));
        bob_public_set := List([1..public_set_size], i -> Random(G.presentation));
        alice_private_key := Product(List([1..private_key_size], i -> Random(alice_public_set) ^ Random([-1, 1])));
        conjugated_bob_public_set := List(bob_public_set, x -> x ^ alice_private_key);
        found_alice_private_key := field_based_attack_2(G, bob_public_set, conjugated_bob_public_set);
        if alice_private_key <> found_alice_private_key then
            Print("The keys are different!\n");
        fi;
    od;
    end_time := Runtime();
    total_time := end_time - start_time;
    Print(Degree(f), " ", HirschLength(G.presentation), " ", Float(total_time / test_num), " ", f, "\n");
end;


x := Indeterminate(Rationals);
ps := [
    x^2 - x - 1,
    x^5 - x^3- 1,
    x^7 - x^3 - 1,
    x^9 - 7*x^3 - 1,
    x^11 - x^3 - 1,
    x^15 - x - 2,
    x^20 - x - 1
];


for p in ps do
    test_field_based_attack_2(p, 20, 5, 100);
od;

for p in ps do
    test_field_based_attack_2(p, 20, 100, 100);
od;

