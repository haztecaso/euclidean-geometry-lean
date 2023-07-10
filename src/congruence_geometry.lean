import order_geometry

open order_geometry
open incidence_geometry 

/-- Geometría de congruencia, clase que engloba los axiomas para las relaciones de congruencia entre segmentos y ángulos. 

C1 : Given a seg and two distinct points `A` `B`, we find uniquely find a point `A` on the
same side with `B` to `A` such that seg `A` `C` is congruent to the seg.
C4 : Given a proper ang `α` and points `a` `b`, we can find `c` such that `∠c a b`
     is congruent to `α`. `c` is uniquely defined given one side of line `a` `b`.

-/

class congruence_geometry (Point Line : Type*) extends order_geometry Point Line :=
  (seg_cong : Segment Point → Segment Point → Prop)
  (ang_cong : Angle Point Line → Angle Point Line → Prop)
  -- (C1 (s : Segment Point) (r : Ray Point): ∃! C : Point, seg_cong s (Segment.mk r.A C sorry) )
  (C1 (s : Segment Point) (A B : Point) (hAB : A ≠ B) :
    ∃! C : Point, ∃ hBC : B ≠ C, ∃ hAC : A ≠ C, (same_side_points Line A B C hBC) ∧ (seg_cong s (Segment.mk A C hAC))
  )
  (C21 {s1 s2 s3: Segment Point} (h1 : seg_cong s1 s2) (h2 : seg_cong s1 s3) : seg_cong s2 s3)
  (C22 (s : Segment Point) : seg_cong s s)
  (C3 {A B C D E F: Point} (hABC : neq3 A B C ∧ between A B C) (hDEF : neq3 D E F ∧ between D E F)
    (h1 : seg_cong (Segment.mk A B hABC.left.left) (Segment.mk D E hDEF.left.left))
    (h2 : seg_cong (Segment.mk B C hABC.left.right.right) (Segment.mk E F hDEF.left.right.right)) :
    seg_cong (Segment.mk A C hABC.left.right.left) (Segment.mk D F hDEF.left.right.left)
  )
  (C4 (α : Angle Point Line) (A B Side : Point) (hAB : A ≠ B) (hSide :  ¬ Side ~ (line Line hAB).val) :
    ∃! C : Point, ∃ h : same_side_line' (line Line hAB).val Side C,
      (ang_cong α (Angle.mk_from_points B A C (same_side_line'_non_collinear hAB hSide h))) )
  (C51 (α β γ : Angle Point Line) (hαβ : ang_cong α β) (hαγ : ang_cong α γ) : ang_cong β γ)
  (C52 (α : Angle Point Line) : ang_cong α α)
  (C6 (T1 T2 : Triangle Point Line) 
    (h1: seg_cong (Segment.mk T1.A T1.B T1.neq.left) (Segment.mk T2.A T2.B T2.neq.left))
    (h2: seg_cong (Segment.mk T1.A T1.C T1.neq.right.left) (Segment.mk T2.A T2.C T2.neq.right.left)) 
    (h3: ang_cong (Angle.mk_from_points T1.B T1.A T1.C T1.non_collinear) (Angle.mk_from_points T2.B T2.A T2.C T2.non_collinear)) :
      seg_cong (Segment.mk T1.B T1.C T1.neq.right.right) (Segment.mk T2.B T2.C T2.neq.right.right)
      ∧ ang_cong 
        (Angle.mk_from_points T1.A T1.B T1.C T1.non_collinear_symm) 
        (Angle.mk_from_points T2.A T2.B T2.C T2.non_collinear_symm)
      ∧ ang_cong 
        (Angle.mk_from_points T1.A T1.C T1.B T1.non_collinear_symm') 
        (Angle.mk_from_points T2.A T2.C T2.B T2.non_collinear_symm')
  )

namespace congruence_geometry

variables (Point Line : Type) [cg : congruence_geometry Point Line]

/- Segment congruence is reflexive -/
theorem seg_cong_refl : reflexive (cg.seg_cong ) :=
begin
  intro seg,
  exact cg.C22 seg,
end

/- Segment congruence is reflexive -/
theorem seg_cong_symm : symmetric (cg.seg_cong) :=
begin
  intros s1 s2 h1,
  let h2 := seg_cong_refl Point Line,
  rw reflexive at h2,
  specialize h2 s1,
  exact cg.C21 h1 h2,
end

/- Segment congruence is transitive -/
theorem seg_cong_trans : transitive (cg.seg_cong) :=
begin
  sorry
end

/- Segment congruence is an equivalence relation -/
theorem seg_cong_equiv : equivalence (cg.seg_cong) := 
  ⟨seg_cong_refl Point Line, seg_cong_symm Point Line, seg_cong_trans Point Line⟩

/- Angle congruence is an equivalence relation -/


end congruence_geometry