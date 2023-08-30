import ..order_geometry.basic ..order_geometry.sideness

open order_geometry
open incidence_geometry 

/-- 

# Axiomas de congruencia

En este fichero se enuncian los axiomas de congruencia, se definen conceptos 
básicos y demuestran resultados elementales.

## Los axiomas 

C1 : Given a seg and two distinct points `A` `B`, we find uniquely find a point `A` on the
same side with `B` to `A` such that seg `A` `C` is congruent to the seg.
C4 : Given a proper ang `α` and points `a` `b`, we can find `c` such that `∠c a b`
     is congruent to `α`. `c` is uniquely defined given one side of line `a` `b`.

-/

class congruence_geometry (Point Line : Type*) 
  extends order_geometry Point Line :=
  (scong : Seg Point → Seg Point → Prop)
  (acong : Ang Point Line → Ang Point Line → Prop)
  (C1 (s : Seg Point) (A B : Point) (hAB : A ≠ B) :
    ∃! C : Point, ∃ hBC : B ≠ C, ∃ hAC : A ≠ C, 
      (same_side_points Line A B C hBC) 
      ∧ (scong s (Seg.mk A C hAC))
  )
  (C21 {s1 s2 s3: Seg Point} (h1 : scong s1 s2) (h2 : scong s1 s3) :
    scong s2 s3)
  (C22 (s : Seg Point) : scong s s)
  (C3 {A B C D E F: Point} 
    (hABC : neq3 A B C ∧ between A B C)
    (hDEF : neq3 D E F ∧ between D E F)
    (h1 : scong (Seg.mk A B hABC.1.1) (Seg.mk D E hDEF.1.1))
    (h2 : scong (Seg.mk B C hABC.1.2.2) (Seg.mk E F hDEF.1.2.2)) :
    scong (Seg.mk A C hABC.1.2.1) (Seg.mk D F hDEF.1.2.1)
  )
  (C4 (α : Ang Point Line) (A B Side : Point) (hAB : A ≠ B) 
    (hSide :  ¬ Side ~ (line Line hAB).val) :
    ∃! C : Point, ∃ h : same_side_line' (line Line hAB).val Side C,
      (acong α (Ang.mk_from_points B A C (same_side_line'_non_collinear hAB hSide h))))
  (C51 {α β γ : Ang Point Line} (hαβ : acong α β) (hαγ : acong α γ) : 
    acong β γ)
  (C52 (α : Ang Point Line) : acong α α)
  (C6 (T1 T2 : Tri Point Line) 
    (h1: scong (Seg.mk T1.A T1.B T1.neq.1) (Seg.mk T2.A T2.B T2.neq.1))
    (h2: scong (Seg.mk T1.A T1.C T1.neq.2.1) (Seg.mk T2.A T2.C T2.neq.2.1)) 
    (h3: acong (Ang.mk_from_points T1.B T1.A T1.C T1.non_collinear) 
               (Ang.mk_from_points T2.B T2.A T2.C T2.non_collinear)) :
      scong (Seg.mk T1.B T1.C T1.neq.2.2) (Seg.mk T2.B T2.C T2.neq.2.2)
      ∧ acong 
        (Ang.mk_from_points T1.A T1.B T1.C T1.non_collinear_symm) 
        (Ang.mk_from_points T2.A T2.B T2.C T2.non_collinear_symm)
      ∧ acong 
        (Ang.mk_from_points T1.A T1.C T1.B T1.non_collinear_symm') 
        (Ang.mk_from_points T2.A T2.C T2.B T2.non_collinear_symm')
  )

namespace congruence_geometry

variables (Point Line : Type) [cg : congruence_geometry Point Line]

/- Seg congruence is reflexive -/
lemma scong_refl : reflexive (cg.scong) :=
begin
  intro seg,
  exact cg.C22 seg,
end

/- Seg congruence is symmetric -/
lemma scong_symm : symmetric (cg.scong) :=
begin
  intros s1 s2 h1,
  let h2 := scong_refl Point Line,
  rw reflexive at h2,
  specialize h2 s1,
  exact cg.C21 h1 h2,
end

/- Seg congruence is transitive -/
lemma scong_trans : transitive (cg.scong) :=
begin
  sorry
end

/- Seg congruence is an equivalence relation -/
theorem scong_equiv : equivalence (cg.scong) := 
  ⟨scong_refl Point Line, scong_symm Point Line, scong_trans Point Line⟩

/- Ang congruence is reflexive -/
lemma acong_refl : reflexive (cg.acong) :=
begin
  intro ang,
  exact cg.C52 ang,
end

/- Seg congruence is symmetric -/
lemma acong_symm : symmetric (cg.acong) :=
begin
  intros a1 a2 h1,
  let h2 := acong_refl Point Line,
  rw reflexive at h2,
  specialize h2 a1,
  exact cg.C51 h1 h2,
end

/- Seg congruence is transitive -/
lemma acong_trans : transitive (cg.acong) :=
begin
  sorry
end

/- Ang congruence is an equivalence relation -/
theorem acong_equiv : equivalence (cg.acong) := 
  ⟨acong_refl Point Line, acong_symm Point Line, acong_trans Point Line⟩


end congruence_geometry