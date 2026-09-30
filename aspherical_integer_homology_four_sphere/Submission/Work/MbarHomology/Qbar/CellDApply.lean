/-
# Evaluation of the cellular differential on a basis element

The cellular differential of a `PolyCW` is `∂e = ∑_{f ⋖ e} inc(e,f) • f`; here we record that its
value at a `k`-cell basis vector, evaluated at a `k`-cell `f`, is the incidence number when `f` is
a facet of `e` and `0` otherwise.

This is the bridge between the *geometric* chain complex (`PolyCW.cellD`, which cannot be
evaluated by the kernel because `Finsupp.single` is defined through `Classical.decEq`) and the
*sparse data* (`SOp`, which the kernel can evaluate): the per-cell certificates of the closed
cells of `Q̄` are stated and checked on the sparse side, and this lemma transfers them back.

`Submission/Work/MbarHomology/Qbar/QbarCxEnum.lean` uses it to identify the boundary matrix of the
abstract complex `Cx e` with the differential of `cellLe QbarCW hdd e`.
-/
import Mathlib
import Submission.Work.Subdivision.CellChain

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

namespace Work.Subdivision

open CategoryTheory

universe u

namespace PolyCW

variable (P : PolyCW.{u})

/-- **The cellular differential at a `k`-cell, evaluated at a `k`-cell**: the coefficient of `f` in
`∂g` is the incidence number `P.inc g f` when `f` is a facet of `g`, and `0` otherwise. -/
theorem cellD_apply_single (k : ℕ)
    (g : {e : P.Cell // P.dim e = k + 1}) (f : {e : P.Cell // P.dim e = k}) :
    (P.cellD k (Finsupp.single g 1)) f = if f.1 ∈ P.facets g.1 then P.inc g.1 f.1 else 0 := by
  rw [PolyCW.cellD_single, PolyCW.cellDval, Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
  by_cases hf : f.1 ∈ P.facets g.1
  · rw [ite_eq_left hf]
    refine (Finset.sum_eq_single (M := ℤ) (⟨f.1, hf⟩ : ↥(P.facets g.1)) ?_ ?_).trans ?_
    · intro i _ hne
      rw [ite_eq_right, mul_zero]
      intro hcon
      exact hne (Subtype.ext (congrArg (fun y : {e : P.Cell // P.dim e = k} => y.1) hcon))
    · intro hnot
      exact absurd (Finset.mem_attach _ ⟨f.1, hf⟩) hnot
    · rw [ite_eq_left rfl, mul_one]
  · rw [ite_eq_right hf]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [ite_eq_right, mul_zero]
    intro hcon
    exact hf (congrArg (fun y : {e : P.Cell // P.dim e = k} => y.1) hcon ▸ i.2)

end PolyCW

end Work.Subdivision
