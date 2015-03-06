Read("lba.g");
Read("fba.g");

# Test suite
test_length_based_attack := function(f, public_set_size, private_key_size, test_num)   
    local alice_public_set, bob_public_set, alice_private_key, conjugated_bob_public_set, 
            G, start_time, end_time, i, found_alice_private_key, lba_total_time;
    G := generate_O_by_U_by_f_with_extra_info(f); 
    lba_total_time := 0;
    for i in [1..test_num] do
        alice_public_set := List([1..public_set_size], i -> Random(G.presentation));
        bob_public_set := List([1..public_set_size], i -> Random(G.presentation));
        alice_private_key := Product(List([1..private_key_size], i -> Random(alice_public_set) ^ Random([-1, 1])));
        conjugated_bob_public_set := List(bob_public_set, x -> x ^ alice_private_key);
        start_time := Runtime();
        found_alice_private_key := length_based_attack(alice_public_set, bob_public_set, conjugated_bob_public_set);
        end_time := Runtime();
        lba_total_time := lba_total_time + end_time - start_time;
        if alice_private_key <> found_alice_private_key then
            Print("LBA: the keys are different!\n");
        fi;
   od;
    Print(Degree(f), " ", HirschLength(G.presentation), " ", Float(lba_total_time / test_num), " ", f, "\n");
end;


x := Indeterminate(Rationals);
test_length_based_attack(x^2 - x - 1, 20, 5, 10);

