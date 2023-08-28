lemma disctinct_lines_one_common_point
  {Point Line : Type*} [ig : incidence_geometry Point Line] :
  ∀ l m : Line, l ≠ m →
    (∃! A : Point, is_common_point A l m) ∨ (¬ have_common_point Point l m) :=
begin
  intros l m,
  contrapose,
  push_neg,
  rintro ⟨not_unique, hlm⟩,
  rw exists_unique at not_unique,
  push_neg at not_unique,
  cases hlm with A hA,
  rcases not_unique A hA with ⟨B, ⟨hB, hAB⟩⟩,
  rw ne_comm at hAB,
  exact unique_of_exists_unique (ig.I1 hAB) ⟨hA.left,hB.left⟩ ⟨hA.right,hB.right⟩,
end
