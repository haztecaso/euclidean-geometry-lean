import ..incidence_geometry.basic

/-!
# Axiomas de orden

En este fichero se enuncian los axiomas de orden, se definen entidades y 
demuestran resultados elementales que dependen de estos axiomas.

## Notaciones

- Se mantiene el uso de la relación de incidencia A ~ l.
- Se utiliza la notación A * B * C para la relación de orden.

-/

open incidence_geometry
open_locale classical

/-- Geometría del orden, clase que extiende la geometría de incidencia y añade 
los axiomas para la relación de orden. -/
class order_geometry (Point Line : Type*) 
  extends incidence_geometry Point Line :=
  (between: Point → Point → Point →  Prop)
  (notation A `*` B `*` C := between A B C)
  (B11 {A B C: Point} (h : A * B * C) : 
    neq3 A B C ∧ collinear Line A B C ∧ C * B * A)
  (B12 {A B C: Point} (h : A * B * C) : C * B * A)
  (B2 {A B : Point} (h : A ≠ B) : ∃ C : Point, A * B * C)
  (B3 {A B C : Point} (h : collinear Line A B C) :
    xor3 (A * B * C) (B * A * C) (A * C * B))
  (B4 {A B C D : Point} {l : Line} (h_non_collinear : ¬ collinear Line A B C) 
      (hlABC : ¬ (A ~ l ∨ B ~ l ∨ C ~ l)) (hlD : D ~ l) (hADB : A * D * B)
      : xor (∃ E ,  E ~ l ∧ (A * E * C)) (∃ E, E ~ l ∧ (B * E * C)))


namespace order_geometry

variables {Point Line : Type*} [og : order_geometry Point Line]

local notation A `*` B `*` C := og.between A B C

/-- La relación between es simétrica en el primer y tercer argumento. -/
lemma between_symm (A B C : Point) : (A * B * C) ↔ (C * B * A) :=
begin
  split,
  { intro h, exact og.B12 h },
  { intro h, exact og.B12 h },
end

/-- Los segmentos están implementados mediante estructuras determinadas por 
dos puntos distintos.  -/
structure Seg (Point : Type*) := {A B : Point} (neq : A ≠ B)

/-- Un punto pertenece a un segmento si coincide con uno de los extremos o está 
entre ellos. -/
def Seg.in (seg : Seg Point) (Line : Type*) 
  [og : order_geometry Point Line]  (P : Point) : Prop := 
  P = seg.A ∨ P = seg.B ∨ (og.between seg.A P seg.B)

/-- Relación de pertenencia entre puntos y segmentos utilizando la clase has_mem 
que permite utilizar el operador ∈. -/
instance [order_geometry Point Line] : has_mem Point (Seg Point) := 
  ⟨λ P seg, seg.in Line P⟩

/-- Lema auxiliar para reescribir la pertenencia de puntos en segmentos. -/
lemma seg_mem_def 
  {Point : Type*} (seg : Seg Point) (Line : Type*) 
  [og : order_geometry Point Line]  (P : Point) : 
  P ∈ seg ↔ seg.in Line P :=
by refl

/-- La pertenencia de puntos en segmentos es simétrica. -/
lemma seg_mem_symm
  {Point : Type*} (Line : Type*) [og : order_geometry Point Line] 
  {A B : Point} (P : Point) (hAB : A ≠ B): 
  P ∈ Seg.mk hAB ↔ P ∈ Seg.mk hAB.symm:=
begin
  split,
  { intro hP, rw [seg_mem_def, Seg.in] at hP, rw [seg_mem_def, Seg.in],
    cases hP, { right, left, exact hP },
    { cases hP, { left, exact hP }, { right, right, rw between_symm, exact hP },
  }},
  { intro hP, rw [seg_mem_def, Seg.in] at hP, rw [seg_mem_def, Seg.in],
    cases hP, { right, left, exact hP },
    { cases hP, { left, exact hP }, { right, right, rw between_symm, exact hP },
  }},
end

/-- Los extremos de un segmento están contenidos en él. -/
lemma seg_contains_extremes 
  {Point : Type*} (Line : Type*) [og : order_geometry Point Line]
  {A B : Point} (hAB : A ≠ B) : 
  A ∈ (Seg.mk hAB) ∧ B ∈ (Seg.mk hAB) :=
begin
  rw [seg_mem_def, Seg.in, seg_mem_def, Seg.in],
  split,
  { left, refl },
  { right, left, refl }
end

/--
Relación de intersección entre segmentos y líneas.
Un segmento se interseca con una línea si tienen un punto en común.
-/
def seg_intersect_line 
  [order_geometry Point Line] (S : Seg Point) (l : Line) := 
  ∃ P : Point, P ∈ S ∧ P ~ l

/-- Un triángulo está determinado por tres puntos no alineados -/
structure Tri (Point Line: Type*) [order_geometry Point Line] := 
  {A B C : Point}
  (non_collinear : ¬ collinear Line A B C)

/-- Utilidad para obtener la propiedad de no colinearidad de un segmento con la 
propiedad de simetría entre el primer y segundo argumento aplicada. -/
lemma Tri.non_collinear_symm 
  {Point Line: Type*} [order_geometry Point Line] (T : Tri Point Line) : 
  ¬ collinear Line T.B T.A T.C :=
begin  
  rw collinear_symm,
  exact T.non_collinear,
end

/-- Utilidad para obtener la propiedad de no colinearidad de un segmento con la 
propiedad de simetría entre el primer y tercer argumento aplicada. -/
lemma Tri.non_collinear_symm' 
  {Point Line: Type*} [order_geometry Point Line] (T : Tri Point Line) : 
  ¬ collinear Line T.C T.A T.B :=
begin  
  rw [collinear_symm2, collinear_symm],
  exact T.non_collinear,
end

/-- Los vértices de un triángulo son distintos entre ellos. -/
lemma Tri.neq 
  {Point Line: Type*} [order_geometry Point Line] (T : Tri Point Line) : 
  neq3 T.A T.B T.C :=
by exact non_collinear_neq Line T.non_collinear

/-- Un punto pertenece a un triángulo si pertenece a alguno de los segmentos que
determinados por sus vértices. -/
def Tri.in {Point Line: Type*} [order_geometry Point Line]
  (T: Tri Point Line) (P : Point) : Prop :=
  P ∈ (Seg.mk T.neq.1) ∨ P ∈ (Seg.mk T.neq.2.1) ∨ P ∈ (Seg.mk T.neq.2.2)

/-- Un rayo está determinado por dos puntos. El primero de estos se llama 
extremo del rayo. -/
structure Ray (Point : Type*) := {A B: Point} (neq : A ≠ B)


/-- Un punto P pertenece a un rayo AB si coincide con su vértice A o si 
A * B * P. -/
def Ray.in (ray : Ray Point) (Line : Type*)
  [og : order_geometry Point Line] (P : Point) : Prop := 
  P = ray.A ∨ (ray.A * ray.B * P)

/-- Un ángulo está determinado por dos rayos con el mismo extremo. 
Además los rayos no pueden pertenecer a una misma línea. -/
structure Ang (Point Line: Type*) [order_geometry Point Line] :=
  (r1 r2 : Ray Point)
  (vertex : r1.A = r2.A)
  (non_collinear : ¬ collinear Line r1.A r1.B r2.B)

/-- Vértice del ángulo. -/
def Ang.A {Point Line: Type*} [order_geometry Point Line]
  (α : Ang Point Line) : Point := α.r1.A

/-- Punto que define uno de los rayos. -/
def Ang.B {Point Line: Type*} [order_geometry Point Line] 
  (α : Ang Point Line) : Point := α.r1.B

/-- Punto que define uno de los rayos. -/
def Ang.C {Point Line: Type*} [order_geometry Point Line] 
  (α : Ang Point Line) : Point := α.r2.B

/-- Los puntos que definen un ángulo son distintos entre ellos. -/
lemma Ang.neq {Point Line: Type*} [order_geometry Point Line] 
  (α : Ang Point Line) : neq3 α.A α.B α.C :=
by exact non_collinear_neq Line α.non_collinear

/-- Los ángulos también se pueden construir a partir de tres puntos no 
alineados. -/
def Ang.mk_from_points [order_geometry Point Line] (B A C : Point)
  (h : ¬ collinear Line A B C) : Ang Point Line := 
begin
  let neq := non_collinear_neq Line h,
  let r1 := Ray.mk neq.left,
  let r2 := Ray.mk neq.right.left,
  have vertex : r1.A = r2.A, { refl },
  exact ⟨r1, r2, vertex, h⟩
end

/-- Relación de estar del mismo lado del plano respecto de una línea. 
En `order_geometry.propositions` se demuestra que esta es una relación de 
equivalencia.
-/
def same_side_line (l: Line) (A B : Point) := 
  A = B ∨ (∃ h : A ≠ B, ¬ @seg_intersect_line Point Line og (Seg.mk h) l)

lemma same_side_line_non_collinear 
  {A B C D: Point} [og: order_geometry Point Line] 
  (hAB : A ≠ B) (hC : ¬  C ~ (line Line hAB).val) 
  (h_same_side : same_side_line (line Line hAB).val C D) :
  ¬ collinear Line A B D := 
begin
  by_contra h_contra,
  let lAB := (line Line hAB),
  cases h_contra with l hl,
  have h2 : l = lAB.val,
  { rcases og.I1 hAB with ⟨_, ⟨_, hm⟩⟩,
    rw [hm l ⟨hl.left, hl.right.left⟩, ← hm lAB lAB.property],
    refl },
  rw h2 at hl,
  cases h_same_side, 
  { rw ← h_same_side at hl, tauto },
  { cases h_same_side with hCD h,
    rw seg_intersect_line at h,
    push_neg at h,
    have hD : D ∈ Seg.mk hCD, { exact (seg_contains_extremes Line hCD).2 },
    specialize h D hD,
    tauto },
end

/-- Relación de estar del mismo lado de una línea respecto de un punto. -/
def same_side_point {Point : Type*} (Line : Type*) [order_geometry Point Line] 
  (A B C : Point) (hBC : B ≠ C) := 
  collinear Line A B C ∧ A ∉ (Seg.mk hBC) 

end order_geometry