import .basic ..incidence_geometry.propositions

open incidence_geometry

namespace order_geometry
variables {Point : Type*} (Line : Type*) [og : order_geometry Point Line]
local notation A `*` B `*` C := og.between A B C

/-- 
Para dos puntos distintos existe un tercero entre ellos (Teorema 3 en el 
Grundlagen).
Este es el teorema estudiado en el paper de Meikle & Fleuriot (ver referencia en 
la memoria), en el que se explica cómo Hilbert se apoyó en un dibujo para 
demostrar este resultado, y los detalles necesarios para completar la 
formalización son bastante extensos y sutiles.
-/
lemma point_between_given {A C : Point} (hAC : A ≠ C): ∃ B : Point, A * B * C := 
begin
  sorry
end

variables (Point) {Line}

/-- La relación de estar del mismo lado de una línea es reflexiva. -/
lemma same_side_line_refl (l : Line) : 
  reflexive (@same_side_line Point Line og l) := 
begin
  intro P,
  left,
  refl,
end 

/-- La relación de estar del mismo lado de una línea es simétrica. -/
lemma same_side_line_symm (l : Line) : 
  symmetric (@same_side_line Point Line og l) := 
begin
  intros P Q h,
  cases h with h1 h2,
  { left, rw h1 },
  { cases h2 with h h2, 
    right,
    use h.symm,
    rw seg_intersect_line at h2 ⊢,
    push_neg at h2 ⊢, 
    intros A hA,
    apply h2 A,
    rw seg_mem_symm, 
    exact hA,
  },
end

/-- 
La relación de estar del mismo lado de una línea es transitiva.
Esta es la propiedad con demostración más técnica. 
Está planteado el esquema general de la demostración, siguiendo el libro de 
Hartshorne. En los puntos sin completar está comentada la forma en la que habría 
que proceder para completar la demostración.
-/
lemma same_side_line_trans (l : Line) : 
  transitive (@same_side_line Point Line og l) := 
begin
  intros A B C hAB hBC,
  cases hAB,
  { rw hAB, exact hBC },
  { cases hBC, 
    { rw ← hBC, right, exact hAB }, 
    { cases hAB with hAB hsABl,
      cases hBC with hBC hsBCl,
      by_cases hAC : A ≠ C,
      { right,
        use hAC,
        rw seg_intersect_line at hsABl hsBCl ⊢,
        push_neg at hsABl hsBCl ⊢,
        rintros P (hPA|hPC|hPAC),
        { apply hsABl P, left, exact hPA },
        { apply hsBCl P, right, left,  exact hPC },
        -- Hasta aquí hemos tenido en cuenta los casos en los que algún punto 
        -- coincide. Ahora empieza la demostración siguiendo el libro de 
        -- Hartshorne.
        { by_cases h_collinear : collinear Line A B C,
          -- Caso 2 en el libro: Los tres puntos están alineados
          { 
            have hAl : ¬ A ~ l, 
            { apply hsABl A, rw [seg_mem_def, Seg.in], left, refl },
            have hBl : ¬ B ~ l, 
            { apply hsABl B, rw [seg_mem_def, Seg.in], right, left, refl },
            have hCl : ¬ C ~ l,
            { apply hsBCl C, rw [seg_mem_def, Seg.in], right, left, refl },
            cases h_collinear with m hABCm,
            have hlm : l ≠ m, 
            { by_contra h_contra, rw ← h_contra at hABCm, tauto },
            have hD : ∃ D : Point, D ~ l ∧ ¬ D ~ m, 
            { cases og.I2 l with Q hQR,
              cases hQR with R hQR,
              by_cases hQm : Q ~ m,
              { use R, 
                refine ⟨hQR.2.2, _⟩,
                cases neq_lines_one_common_point Point l m hlm with h,
                { cases h with O hO, 
                  by_contra h_contra,
                  let hR := hO.2 R ⟨hQR.2.2, h_contra⟩,
                  let hQ := hO.2 Q ⟨hQR.2.1, hQm⟩,
                  rw ← hQ at hR,
                  tauto },
                { rw have_common_point at h,
                  push_neg at h,
                  specialize h R,
                  rw is_common_point at h,
                  push_neg at h,
                  apply h,
                  exact hQR.2.2 }},
              { use Q, 
                exact ⟨hQR.2.1, hQm⟩, }},
            cases hD with D hD,
            have hDA : D ≠ A , { by_contra, rw ← h at hAl, tauto },
            have hE : ∃ E : Point, D * A * E,
            { cases og.B2 hDA with E hE, use E, exact hE },
            cases hE with E hE,
            have hAE : A ≠ E, { exact (og.B11 hE).1.2.2 },
            have hDE : D ≠ E, { exact (og.B11 hE).1.2.1 },
            have h_collinearDAE : collinear Line D A E, 
            { exact (og.B11 hE).2.1 },
            let AE := line Line hAE,
            have hEl : ¬ E ~ l, 
            { have hAEl : ↑AE ≠ l, 
              { by_contra, rw ←h at hAl, exact hAl AE.prop.1 },
              have hDAEl : is_common_point D ↑AE l, 
              { rw is_common_point, 
                refine ⟨_, hD.1⟩,
                rw collinear at h_collinearDAE,
                cases h_collinearDAE with n hn,
                have h2 : ↑AE = n, 
                { cases og.I1 hAE with r hr, 
                  rw [hr.2 ↑AE AE.property, hr.2 n hn.2] },
                rw h2, 
                exact hn.1 },
              have h_have_common : ¬¬ have_common_point Point ↑AE l, 
              { push_neg, rw have_common_point, use D, exact hDAEl },
              let hhh := (or_iff_left h_have_common).mp 
                (neq_lines_one_common_point Point ↑AE l hAEl),
              rw exists_unique at hhh,
              cases hhh with Q hQ,
              by_contra,
              rw [hQ.2 D hDAEl, hQ.2 E ⟨AE.prop.2, h⟩] at hDE,
              tauto },
            let sAE := Seg.mk hAE,
            have hsAEl : ¬ seg_intersect_line sAE l,
            { sorry },
            have hEm : ¬ E ~ m,
            { sorry },
            have hABE : ¬ collinear Line A B E,
            { sorry },
            have hBE : same_side_line l B E,
            { sorry }, -- Aplicación del caso 1.
            have hCE : same_side_line l C E,
            { sorry }, -- Aplicación del caso 1.
            have hAC : same_side_line l A C,
            { sorry }, -- Aplicación del caso 1.
            sorry },
          -- Caso 1 en el libro: Los tres puntos no están alineados
          -- Habría que extraer este caso a un lema externo para poder 
          -- reutilizarlo en la demostración del caso 2.
          { have hlACB : ¬ (A ~ l ∨ C ~ l ∨ B ~ l),
            { push_neg, 
              split,
              { exact hsABl A (seg_contains_extremes Line hAB).left },
              { split, 
                { exact hsBCl C (seg_contains_extremes Line hBC).right },
                {  exact hsBCl B (seg_contains_extremes Line hBC).left }}},
            have h_noncollinear' : ¬collinear Line A C B, 
            { rw [collinear_symm2, collinear_symm, collinear_symm2], 
              exact h_collinear },
            by_contra hP,
            let hPasch := og.B4 h_noncollinear' hlACB hP hPAC,
            rw xor at hPasch,
            cases hPasch,
            { cases hPasch.left with E hE, 
              specialize hsABl E, 
              rw [seg_mem_def, Seg.in] at hsABl, 
              have hEl : ¬ E ~ l, 
              { apply hsABl, 
                right, right, 
                exact hE.right },
              apply hEl,
              exact hE.left, },
            { cases hPasch.left with E hE, 
              specialize hsBCl E, 
              rw [seg_mem_def, Seg.in] at hsBCl, 
              have hEl : ¬ E ~ l, 
              { apply hsBCl, 
                right, right, 
                rw between_symm at hE, 
                exact hE.right },
              apply hEl,
              exact hE.left, }}}},
      { left, push_neg at hAC, exact hAC }}}
end

/-- La relación de estar del mismo lado del plano respecto de una línea es de 
equivalencia. -/
theorem same_side_line_equiv (l : Line) :
  equivalence (@same_side_line Point Line og l) :=
  ⟨same_side_line_refl Point l, 
    same_side_line_symm Point l, 
    same_side_line_trans Point l⟩

end order_geometry