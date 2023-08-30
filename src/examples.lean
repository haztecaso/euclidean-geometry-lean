import tactic data.set .incidence_geometry.basic

def Point := ℝ × ℝ

@[simp] lemma point_neq_by_coords (A B : Point) : 
  (A ≠ B) ↔ (A.1 ≠ B.1 ∨ A.2 ≠ B.2) :=
begin
  rw ← not_iff_not,
  push_neg,
  exact prod.ext_iff
end

@[ext] structure LineEq := (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0)

definition line_eq (l m : LineEq) : Prop := 
  ∃ (x : ℝ), x≠ 0 ∧ l.a = x * m.a ∧ l.b = x * m.b ∧ l.c = x * m.c

lemma line_eq_refl : reflexive line_eq :=
begin
  intro l,
  use 1,
  refine ⟨zero_ne_one.symm, _, _, _⟩,
  { rw one_mul },
  { rw one_mul }, 
  { rw one_mul }, 
end

lemma line_eq_symm : symmetric line_eq :=
begin
  intros l m hlm,
  rcases hlm with ⟨x, ⟨hx, ha, hb, hc⟩⟩ ,
  use x⁻¹,
  have hxinv : x⁻¹*x = 1, { finish }, /- TODO: remove finish -/
  refine ⟨inv_ne_zero hx,_,_,_⟩,
  { simp only [ha], rw [← mul_assoc, hxinv, one_mul] }, 
  { simp only [hb], rw [← mul_assoc, hxinv, one_mul] },
  { simp only [hc], rw [← mul_assoc, hxinv, one_mul] },
end

lemma line_eq_trans : transitive line_eq :=
begin
  intros l m n hlm hmn,
  rcases hlm with ⟨x, ⟨hx, ha₁, hb₁, hc₁⟩⟩ ,
  rcases hmn with ⟨y, ⟨hy, ha₂, hb₂, hc₂⟩⟩ ,
  use x*y,
  refine ⟨mul_ne_zero hx hy,_,_,_⟩,
  { rw [ha₁, ha₂, mul_assoc] },
  { rw [hb₁, hb₂, mul_assoc] },
  { rw [hc₁, hc₂, mul_assoc] },
end

theorem line_equiv : equivalence line_eq := 
  ⟨line_eq_refl, line_eq_symm, line_eq_trans⟩

def Line.setoid : setoid LineEq := { r := line_eq, iseqv := line_equiv }

local attribute [instance] Line.setoid

def Line := quotient Line.setoid

def Line.reduce : LineEq → Line := quot.mk line_eq
instance : has_lift LineEq Line := { lift := Line.reduce }
instance : has_coe LineEq Line := { coe := Line.reduce }

def Line.mk (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) : Line := ↑(LineEq.mk a b c h)


def has_point' (l : LineEq) (P : Point) : Prop := l.a*P.1 + l.b*P.2 + l.c = 0

theorem has_point_well_defined {l m : LineEq} (h : l ≈ m) (P : Point) :
  has_point' l P ↔ has_point' m P :=
begin
  cases h with x h,
  rcases h with ⟨hx, ha, hb, hc⟩,
  rw [ 
    has_point', 
    ha, 
    hb, 
    hc, 
    mul_assoc, 
    mul_assoc, 
    ← left_distrib, 
    ← left_distrib 
  ],
  rw has_point',
  finish, /- TODO: remove finish -/
end

lemma has_point_well_defined' {l m : LineEq} (h: l ≈ m) : 
  has_point' l = has_point' m := 
begin
  rw function.funext_iff,
  intro P,
  rw has_point_well_defined,
  exact h,
end

def has_point := quotient.lift has_point' @has_point_well_defined'

noncomputable def line_from_points {A B : Point} (hAB : A ≠ B) : Line :=
begin
  rw point_neq_by_coords at hAB,
  by_cases hx: A.1 = B.1,
  {
    let a : ℝ := 1,
    let b : ℝ := 0,
    let c : ℝ := -(A.1+B.1)/2,
    have h : a ≠ 0 ∨ b ≠ 0, { left, exact ne_zero.ne a },
    exact Line.mk a b c h },
  { 
    rw push_neg.not_eq at hx,
    let a : ℝ := -(A.2-B.2)/(A.1-B.1),
    let b : ℝ := 1,
    let c : ℝ := -(a*(A.1+B.1)-(A.2+B.2))/2,
    have h : a ≠ 0 ∨ b ≠ 0, { right, exact ne_zero.ne b },
    exact Line.mk a b c h }
end

def line_from_points' : Point → Point → Prop
  | (x, y) (a, b) := true

lemma points_in_line_from_points {A B : Point} (hAB : A ≠ B) :
  has_point (line_from_points hAB) A ∧ has_point (line_from_points hAB) B := 
begin
  -- rw line_from_points,
  split,
  { rw [has_point], /- TODO: ¿Cómo puedo escoger un representante canónico? ¿o puedo evitar tener que escojerlo? -/
    sorry },
  { sorry },
end

instance : incidence_geometry Point Line := { 
  lies_on := λ P l, has_point l P,
  I1 := begin
    intros A B hAB,
    use line_from_points hAB,
    split,
    { simp, exact points_in_line_from_points hAB },
    { intro m, simp, intros hA hB,
      sorry }
  end,
  I2 := begin
    intro ℓ,

    -- cases l.h,
    -- { 
    --   use Point.mk (-l.c) 0, 
    --   use Point.mk (-l.c-l.b) 1,
    --   split,
    --   { rw [ ← push_neg.not_eq, Point.ext_iff, push_neg.not_and_distrib_eq ], 
    --     right,
    --     push_neg,
    --     exact zero_ne_one },
    --   { split, 
    --     { rw [h, one_mul, mul_zero, add_zero, add_left_neg] }, 
    --     { rw [h, one_mul, mul_one, sub_add_cancel, add_left_neg] }, }
    -- },
    -- {
    --   use Point.mk 0 (-l.c), 
    --   use Point.mk 1 (-l.c-l.a),
    --   split,
    --   { rw [ ← push_neg.not_eq, 
    --       Point.ext_iff, 
    --       push_neg.not_and_distrib_eq ], 
    --     left,
    --     push_neg,
    --     exact zero_ne_one },
    --   { split, 
    --     { rw [h, mul_zero, one_mul, zero_add, add_left_neg] }, 
    --     { rw [h, mul_one, one_mul, add_sub_cancel'_right, add_left_neg] }},
    -- },
    sorry
  end,
  I3 := begin
    let A : Point := (0, 1), use A, 
    let B : Point := (1, 0), use B, 
    let C : Point := (1, 1), use C, 
    split,
    { rw [neq3, point_neq_by_coords, point_neq_by_coords, point_neq_by_coords], 
      refine ⟨_, _, _⟩,
      { left, exact zero_ne_one },
      { left, exact zero_ne_one },
      { right, exact zero_ne_one },
      },
    { push_neg, 
      intros l hA hB,
      -- rw [ne.def, mul_one, mul_one],
      -- cases l.h with ha hb,
      -- { 
      --   rw [ha, mul_zero, mul_one, add_zero, add_eq_zero_iff_neg_eq] at hB, 
      --   have hc : l.c = -1, { exact hB.symm }, 
      --   rw [ha, hc, mul_zero,  zero_add, mul_one, add_eq_zero_iff_eq_neg, neg_neg ] at hA, 
      --   rw [ha, hA, hc, add_neg_cancel_comm, push_neg.not_eq],
      --   exact one_ne_zero },
      -- { 
      --   rw [hb, mul_zero, mul_one, zero_add, add_eq_zero_iff_neg_eq] at hA,
      --   have hc : l.c = -1, { exact hA.symm }, 
      --   rw [hc, mul_zero, mul_one, add_zero, add_eq_zero_iff_eq_neg, neg_neg] at hB,
      --   rw [hB, hb, hc, add_neg_cancel_comm, push_neg.not_eq],
      --   exact one_ne_zero }},
    sorry }
  end 
}