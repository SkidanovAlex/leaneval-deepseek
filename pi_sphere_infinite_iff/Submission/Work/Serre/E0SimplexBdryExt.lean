import Mathlib
import Submission.Work.Serre.E0SimplexDefs
import Submission.Work.RatHurewicz.Bridge.H_faces
import Submission.Work.RatHurewicz.Bridge.exists_collapse_simplex

/-!
# SUBPROJECT SERRE — E0 in range form: extension of a map on the simplex boundary

`Work.Serre.e0SimplexBdryExtension`: a map on the boundary `∂Δ^{k+2}` of the standard simplex
extends over `Δ^{k+2}`, given the corresponding extension statement for the cube `I^{k+2}`.

The proof descends through the cumulative-coordinate quotient
`Work.RatHurewicz.Bridge.H (k+2) : I^{k+2} → Δ^{k+2}`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open scoped Simplicial Topology unitInterval

namespace Work.Serre

noncomputable section

open Work.RatHurewicz.Bridge
open Work.Stems.Cubical
open Work.RatHurewicz

/-- **The cumulative-coordinate map sends the cube boundary into the simplicial boundary.**

If some coordinate of `t : I^m` is `0` or `1`, then some coordinate of `H m t` vanishes:
`Hfun m t j = Pnat m t j * (1 - tval m t j)`, `Pnat m t j = ∏_{i<j} t_i`; if `t i = 0` then
`Pnat m t (i+1) = 0`, and if `t i = 1` then `1 - tval m t i = 0`. -/
theorem H_mem_simplexBdry (m : ℕ) (t : IC m) (ht : t ∈ Cube.boundary (Fin m)) :
    ∃ j : Fin (m + 1), H m t j = 0 := by
  obtain ⟨i, hi | hi⟩ := ht
  · -- `t i = 0`: the coordinate `i+1` of the image vanishes
    refine ⟨⟨i.val + 1, by omega⟩, ?_⟩
    rw [H_apply, Hfun]
    have hzero : Pnat m t (i.val + 1) = 0 := by
      rw [Pnat]
      refine Finset.prod_eq_zero
        (show i.val ∈ Finset.range (i.val + 1) from Finset.mem_range.mpr (Nat.lt_succ_self _)) ?_
      rw [tval_of_lt _ i.isLt, show (⟨i.val, i.isLt⟩ : Fin m) = i from rfl, hi]
      norm_num
    rw [hzero, zero_mul]
  · -- `t i = 1`: the coordinate `i` of the image vanishes
    refine ⟨⟨i.val, by omega⟩, ?_⟩
    rw [H_apply, Hfun]
    have hone : tval m t i.val = 1 := by
      rw [tval_of_lt _ i.isLt, show (⟨i.val, i.isLt⟩ : Fin m) = i from rfl, hi]
      norm_num
    rw [hone, sub_self, mul_zero]

/-- **Extension of a map on the boundary of the standard simplex.**

If every map on the boundary of the cube `I^{k+2}` extends over the cube (the hypothesis `hcube`,
supplied by `Work.Serre.e0CubeBoundaryExtension` from the vanishing of `π_{k+1}`), then every map
on the simplicial boundary `∂Δ^{k+2} = Work.Serre.simplexBdry (k+2)` extends over `Δ^{k+2}`. -/
theorem e0SimplexBdryExtension (k : ℕ) {X : Type} [TopologicalSpace X]
    (hcube : ∀ (f : C(↥(Cube.boundary (Fin (k+2))), X)),
      ∃ g : C(Fin (k+2) → unitInterval, X), ∀ z : ↥(Cube.boundary (Fin (k+2))), g z.1 = f z)
    (b : C(↥(simplexBdry (k+2)), X)) :
    ∃ y : C(↥(stdSimplex ℝ (Fin (k+3))), X),
      ∀ z : ↥(simplexBdry (k+2)), y z.1 = b z := by
  -- the cube boundary, mapped into the simplex boundary by `H (k+2)`
  let hbdry : C(↥(Cube.boundary (Fin (k+2))), ↥(simplexBdry (k+2))) :=
    ⟨fun z => ⟨H (k+2) z.1, H_mem_simplexBdry (k+2) z.1 z.2⟩,
      Continuous.subtype_mk ((H (k+2)).continuous.comp continuous_subtype_val) _⟩
  have hbdry_apply : ∀ z : ↥(Cube.boundary (Fin (k+2))),
      ((hbdry z : ↥(simplexBdry (k+2))) : ↥(stdSimplex ℝ (Fin (k+3)))) = H (k+2) z.1 :=
    fun z => rfl
  -- the pulled-back boundary map
  let q : C(↥(Cube.boundary (Fin (k+2))), X) := b.comp hbdry
  have q_apply : ∀ z : ↥(Cube.boundary (Fin (k+2))), q z = b (hbdry z) := fun z => rfl
  obtain ⟨g, hg⟩ := hcube q
  -- `g` is constant on the fibres of `H (k+2)`
  have hfac : Function.FactorsThrough g (⇑(H (k+2))) := by
    intro t t' htt
    rcases H_eq_or_boundary (k+2) htt with heq | ⟨ht, ht'⟩
    · rw [heq]
    · have h1 : g t = q ⟨t, ht⟩ := hg ⟨t, ht⟩
      have h2 : g t' = q ⟨t', ht'⟩ := hg ⟨t', ht'⟩
      rw [h1, h2, q_apply, q_apply]
      have hb : hbdry ⟨t, ht⟩ = hbdry ⟨t', ht'⟩ := by
        apply Subtype.ext
        rw [hbdry_apply, hbdry_apply]
        exact htt
      rw [hb]
  -- descend
  refine ⟨(H_isQuotientMap (k+2)).lift g hfac, ?_⟩
  intro z
  -- a boundary preimage of `z`
  have hHinv : H (k+2) (Hinv (k+2) z.1) = z.1 := H_tinv (k+2) z.1
  have hbd : Hinv (k+2) z.1 ∈ Cube.boundary (Fin (k+2)) := by
    obtain ⟨j, hj⟩ := z.2
    refine Hfun_zero_mem_boundary _ ⟨j, ?_⟩
    rw [← H_apply, hHinv]
    exact hj
  have hcomp := congrArg (fun (f : C(IC (k+2), X)) => f (Hinv (k+2) z.1))
    ((H_isQuotientMap (k+2)).lift_comp g hfac)
  have hq : g (Hinv (k+2) z.1) = b z := by
    have h1 : g (Hinv (k+2) z.1) = q ⟨Hinv (k+2) z.1, hbd⟩ := hg ⟨Hinv (k+2) z.1, hbd⟩
    rw [h1, q_apply]
    have hb : hbdry ⟨Hinv (k+2) z.1, hbd⟩ = z := by
      apply Subtype.ext
      rw [hbdry_apply, hHinv]
    rw [hb]
  calc ((H_isQuotientMap (k+2)).lift g hfac) z.1
      = ((H_isQuotientMap (k+2)).lift g hfac) (H (k+2) (Hinv (k+2) z.1)) := by rw [hHinv]
    _ = g (Hinv (k+2) z.1) := hcomp
    _ = b z := hq

end

end Work.Serre
