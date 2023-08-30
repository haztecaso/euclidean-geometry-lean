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

/-- Geometría del orden, clase que engloba los axiomas para la relación de 
orden. -/
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
structure Seg (Point : Type*) := (A B : Point) (neq : A ≠ B)

/-- Un punto pertenece a un segmento si coincide con uno de los extremos o está 
entre ellos. -/
def Seg.in 
  {Point : Type*} (seg : Seg Point) (Line : Type*) 
  [og : order_geometry Point Line]  (P : Point) : Prop := 
  P = seg.A ∨ P = seg.B ∨ (og.between seg.A P seg.B)

/--
Relación de pertenencia entre puntos y segmentos.
Un punto está en un segmento si coincide con uno de los extremos o está entre 
ellos.
-/
instance [order_geometry Point Line] : has_mem Point (Seg Point) := 
  ⟨λ P seg, seg.in Line P⟩

/--
Relación de intersección entre segmentos y líneas.
Un segmento se interseca con una línea si tienen un punto en común.
-/
def seg_intersect_line 
  [order_geometry Point Line] (S : Seg Point) (l : Line) := 
  ∃ P : Point, P ∈ S ∧ P ~ l

/-- Un triángulo está determinado por tres puntos no alineados -/
structure Tri (Point Line: Type*) [order_geometry Point Line] := 
  (A B C : Point) 
  (non_collinear : ¬ collinear Line A B C)

lemma Tri.non_collinear_symm 
  {Point Line: Type*} [order_geometry Point Line] (T : Tri Point Line) : 
  ¬ collinear Line T.B T.A T.C :=
begin  
  rw collinear_symm,
  exact T.non_collinear,
end

lemma Tri.non_collinear_symm' 
  {Point Line: Type*} [order_geometry Point Line] (T : Tri Point Line) : 
  ¬ collinear Line T.C T.A T.B :=
begin  
  rw [collinear_symm2, collinear_symm],
  exact T.non_collinear,
end

lemma Tri.neq 
  {Point Line: Type*} [order_geometry Point Line] (T : Tri Point Line) : 
  neq3 T.A T.B T.C :=
by exact non_collinear_neq Line T.non_collinear

structure Ray (Point : Type*) := (A B: Point) (neq : A ≠ B)

instance [order_geometry Point Line] : has_mem Point (Ray Point) :=
  ⟨λ P ray, begin
    by_cases P ≠ ray.B,
    { exact P = ray.A ∨ ¬ ray.A ∈ Seg.mk P ray.B h },
    { exact true, },
  end ⟩

structure Ang (Point Line: Type*) [order_geometry Point Line] :=
  (r1 r2 : Ray Point)
  (vertex : r1.A = r2.A)
  (non_collinear : ¬ collinear Line r1.A r1.B r2.B)


def Ang.A {Point Line: Type*} [order_geometry Point Line]
  (α : Ang Point Line) : Point := α.r1.A

def Ang.B {Point Line: Type*} [order_geometry Point Line] 
  (α : Ang Point Line) : Point := α.r1.B

def Ang.C {Point Line: Type*} [order_geometry Point Line] 
  (α : Ang Point Line) : Point := α.r2.B

lemma Ang.neq {Point Line: Type*} [order_geometry Point Line] 
  (α : Ang Point Line) : neq3 α.A α.B α.C :=
by exact non_collinear_neq Line α.non_collinear

def Ang.mk_from_points [order_geometry Point Line] (B A C : Point) 
  (h : ¬ collinear Line A B C) : Ang Point Line := 
begin
  let neq := non_collinear_neq Line h,
  let r1 := Ray.mk A B neq.left,
  let r2 := Ray.mk A C neq.right.left,
  have vertex : r1.A = r2.A, { refl },
  exact ⟨r1, r2, vertex, h⟩
end

def same_side_line (l: Line) (A B : Point) := 
  A = B ∨ (∃ h : A ≠ B, 
    ¬ @seg_intersect_line Point Line og (Seg.mk A B h) l)

def same_side_line_non_collinear 
  {A B C D: Point} [og: order_geometry Point Line] 
  (hAB : A ≠ B) (hC : ¬  C ~ (line Line hAB).val) 
  (h : same_side_line (line Line hAB).val C D) :
  ¬ collinear Line A B D := 
begin
  by_contra h_contra,
  let lAB := (line Line hAB),
  cases h_contra with l hl,
  have h2 : l = lAB.val,
  { rcases og.I1 hAB with ⟨_, ⟨_, hm⟩⟩,
    rw [hm l ⟨hl.left, hl.right.left⟩, ← hm lAB lAB.property],
    refl,
    },
  rw h2 at hl,
  cases h, 
  { rw ← h at hl, tauto },
  { cases h with hCD h,
    rw seg_intersect_line at h,
    push_neg at h,
    have hD : D ∈ (Seg.mk C D hCD),
    { let a : Point → Seg Point → Prop := has_mem.mem,
      sorry },
    specialize h D hD,
    tauto },
end

def same_side_point {Point : Type*} (Line : Type*) [order_geometry Point Line] 
  (A B C : Point) (hBC : B ≠ C) := 
  collinear Line A B C ∧ A ∉ (Seg.mk B C hBC) 

end order_geometry