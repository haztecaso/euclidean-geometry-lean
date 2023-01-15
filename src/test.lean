lemma zero_max (m : ℕ) : max 0 m = m :=
max_eq_right (nat.zero_le m)

lemma zero_max_one {m : nat} : max 0 1 = 1 :=
zero_max 1

