import Mathlib
import Submission.Work.ORDunwoody.colour_collapsed

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Cayley

/-! ## The head of the negative edge tail, if it is an old vertex

`Dunwoody.edgeTailNeg D a j` is the tail of the boundary walk obtained by traversing the letter
`(j, false)` at the base point `a`, i.e. the reversal of the positive generator edge `(j, true)`
based at `a' = a * (genE P (j, true))⁻¹`, read backwards from `a` down to `a'`.

* If `L (j, true) ≠ 0` the first vertex of this tail is the *pattern point*
  `Sum.inr ⟨a', ⟨j, L - 1⟩⟩` of the last cell, so the head can never be an old vertex.
* If `L (j, true) = 0` (the generator is collapsed) the tail is the single old vertex
  `Sum.inl (a', ∗)`, and `colour` takes the same value on `(a, ∗)` and on `(a', ∗)` because the
  collapsed generator `genE P (j, true)` fixes the basepoint `t₀`.

This is the `Neg` half of the two "head" facts about the edge tails that the wall system needs. -/

/-- If the generator `(j, true)` is collapsed (`L = 0`), the tail of the negative traversal is the
single old vertex `(a * genE(j,true)⁻¹, ∗)`. -/
theorem edgeTailNeg_head_of_L_eq_zero {G : Type u} [Group G] {V : Type u} [MulAction G V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (a : G) (j : Fin P.n)
    (hL : D.L (j, true) = 0) :
    (Work.ORDunwoody.Dunwoody.edgeTailNeg D a j).head? =
      some (Sum.inl (a * (CayV.genE P (j, true))⁻¹,
        (Sum.inl () : Work.ORDunwoody.Dunwoody.BaseV₀ D)) :
        Work.ORDunwoody.Dunwoody.Vertex D) := by
  rw [Work.ORDunwoody.Dunwoody.edgeTailNeg, if_pos hL]
  rfl

/-- If the generator `(j, true)` is not collapsed (`L ≠ 0`), the tail of the negative traversal
starts at the pattern point of the last cell, so its head is never an old vertex. -/
theorem edgeTailNeg_head_of_L_ne_zero {G : Type u} [Group G] {V : Type u} [MulAction G V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (a : G) (j : Fin P.n)
    (hL : D.L (j, true) ≠ 0) :
    ∃ m : Work.ORDunwoody.Dunwoody.MidV D,
      (Work.ORDunwoody.Dunwoody.edgeTailNeg D a j).head? =
        some (Sum.inr m : Work.ORDunwoody.Dunwoody.Vertex D) := by
  have hne : (List.finRange (D.L (j, true))).reverse ≠ [] := by
    intro hnil
    have := congrArg List.length hnil
    simp only [List.length_reverse, List.length_finRange, List.length_nil] at this
    exact hL this
  obtain ⟨k, rest, hk⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨(⟨a * (CayV.genE P (j, true))⁻¹, ⟨j, k⟩⟩ : Work.ORDunwoody.Dunwoody.MidV D), ?_⟩
  rw [Work.ORDunwoody.Dunwoody.edgeTailNeg, if_neg hL, hk, List.flatMap_cons,
    List.head?_append, List.head?_cons]
  rfl

/-- The colour of the head of the negative edge tail, when that head is an old vertex: it is the
colour of the base point `(a, ∗)`. -/
theorem edgeTailNeg_head_old {G : Type u} [Group G] {V : Type u} [MulAction G V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (a : G) (j : Fin P.n)
    (b : Work.ORDunwoody.Dunwoody.BaseV D)
    (h : (Work.ORDunwoody.Dunwoody.edgeTailNeg D a j).head? =
      some (Sum.inl b : Work.ORDunwoody.Dunwoody.Vertex D)) :
    Work.ORDunwoody.Dunwoody.colour D (a, (Sum.inl () : Work.ORDunwoody.Dunwoody.BaseV₀ D)) = Work.ORDunwoody.Dunwoody.colour D b := by
  by_cases hL : D.L (j, true) = 0
  · -- the generator is collapsed: the head is the old vertex `(a * genE(j,true)⁻¹, ∗)`
    have hb : b = (a * (CayV.genE P (j, true))⁻¹, Sum.inl ()) :=
      (Sum.inl.inj (Option.some.inj
        ((edgeTailNeg_head_of_L_eq_zero a j hL).symm.trans h))).symm
    rw [hb, Work.ORDunwoody.Dunwoody.colour_base, Work.ORDunwoody.Dunwoody.colour_base]
    have hfix : CayV.genE P (j, true) • t₀ = t₀ :=
      genE_smul_eq_self_of_L_eq_zero (D := D) (j, true) hL
    have hfix' : (CayV.genE P (j, true))⁻¹ • t₀ = t₀ := by
      have h2 : (CayV.genE P (j, true))⁻¹ • (CayV.genE P (j, true) • t₀) = t₀ := by
        rw [← mul_smul, inv_mul_cancel, one_smul]
      rwa [hfix] at h2
    rw [mul_smul, hfix']
  · -- the generator is not collapsed: the head is a pattern point, so `h` is absurd
    obtain ⟨m, hm⟩ := edgeTailNeg_head_of_L_ne_zero a j hL
    rw [hm] at h
    exact absurd h (by simp)

end Work.ORDunwoody
