import .basic ..incidence_geometry.propositions

open incidence_geometry

namespace order_geometry
variables {Point : Type*} (Line : Type*) [og : order_geometry Point Line]
local notation A `*` B `*` C := og.between A B C

/-- 
Hilbert's theorem 3.
Para dos puntos distintos existe un tercero entre ellos
-/
lemma point_between_given {A C : Point} (hAC : A ≠ C): ∃ B : Point, A * B * C := 
begin
  let AC := line Line hAC,
  have hE : ∃ E : Point, ¬ E ~ AC.val, { exact line_external_point AC.val },
  cases hE with E hE,
  have hAE : A ≠ E, { sorry }, 
  have hF : ∃ F : Point, A * E * F, { exact og.B2 hAE }, 
  cases hF with F hF,
  have hFC : F ≠ C, { sorry }, 
  have hG : ∃ G : Point, F * C * G, { exact og.B2 hFC }, 
  cases hG with G hG,
  have hGE : G ≠ E, { sorry }, 
  let GE := line Line hGE,
  have sAC : Seg Point := {
    A := A,
    B := C,
    neq := hAC,
  },
  let h := @segment_intersect_line Point Line og sAC GE,
  -- rw ← segment_intersect_line at h,
  -- have hB : segment_intersect_line
  sorry
end

end order_geometry