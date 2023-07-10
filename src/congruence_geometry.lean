import basic
import order_geometry

open order_geometry
open incidence_geometry 

/-- Geometría de congruencia, clase que engloba los axiomas para las relaciones de congruencia entre segmentos y ángulos. -/
class congruence_geometry (Point Line : Type*) extends order_geometry Point Line :=
  (seg_cong : Segment Point → Segment Point → Prop)
  (ang_cong : Angle Point Line → Angle Point Line → Prop)
  (C1 (s : Segment Point) (r : Ray Point): ∃! C : Point, seg_cong s (Segment.mk r.A C sorry) )
  (C21 {s1 s2 s3: Segment Point} (h1 : seg_cong s1 s2) (h2 : seg_cong s1 s3) : seg_cong s2 s3)
  (C22 (s : Segment Point) : seg_cong s s)
  (C3 {A B C D E F: Point} (hABC : different3 A B C ∧ between A B C) (hDEF : different3 D E F ∧ between D E F)
    (h1 : seg_cong (Segment.mk A B hABC.left.left) (Segment.mk D E hDEF.left.left))
    (h2 : seg_cong (Segment.mk B C hABC.left.right.right) (Segment.mk E F hDEF.left.right.right)) :
    seg_cong (Segment.mk A C hABC.left.right.left) (Segment.mk D F hDEF.left.right.left)
  )
  (C4 (α : Angle Point Line) (A B Side : Point) (hAB : A ≠ B) (hSide :  ¬ Side ~ (line Line hAB).val):
    ∃! C : Point, (plane_same_side' (line Line hAB).val C Side) ∧ (ang_cong α (Angle.mk_from_points C A B sorry)) )
  (C51 (α β γ : Angle Point Line) (hαβ : ang_cong α β) (hαγ : ang_cong α γ) : ang_cong β γ)
  (C52 (α : Angle Point Line) : ang_cong α α)
  (C6 (T1 T2 : Triangle Point Line) 
    (h1: seg_cong (Segment.mk T1.A T1.B T1.diff.left) (Segment.mk T2.A T2.B T2.diff.left))
    (h2: seg_cong (Segment.mk T1.A T1.C T1.diff.right.left) (Segment.mk T2.A T2.C T2.diff.right.left)) 
    (h3: ang_cong (Angle.mk_from_points T1.B T1.A T1.C T1.non_collinear) (Angle.mk_from_points T2.B T2.A T2.C T2.non_collinear)) 
    : 
    seg_cong (Segment.mk T1.B T1.C T1.diff.right.right) (Segment.mk T2.B T2.C T2.diff.right.right)
    ∧ ang_cong (Angle.mk_from_points T1.A T1.B T1.C sorry) (Angle.mk_from_points T2.A T2.B T2.C sorry)
    ∧ ang_cong (Angle.mk_from_points T1.A T1.C T1.B sorry) (Angle.mk_from_points T2.A T2.C T2.B sorry)
  )


/- Segment congruence is an equivalence relation -/

/- Angle congruence is an equivalence relation -/