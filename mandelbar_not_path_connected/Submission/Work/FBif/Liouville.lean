/-
Copyright: subproject `Submission/Work/FBif/` of `mandelbar_not_path_connected`.

# `Work.FBif` — the Liouville step of the straightening (FBif, part 3a)

The straightening of FBif produces (through MRMT `M1`/`M2″`) a *homeomorphism* `Φ` of `ℂ` with
`Φ z = z + O(1/‖z‖)` for which `G := Φ ∘ f_ε ∘ Φ⁻¹` is entire antiholomorphic.  Since `f_ε` is an
antipolynomial of antidegree `d` equal to that of the quadratic-like restriction, `G` is a
degree-`d` antiholomorphic polynomial, and for `d = 2` this pins `G` down completely:

`G` is `T_{c'}` for a unique `c'`, and the normalisation `Φ z = z + O(1/‖z‖)` plus the
antisymmetry `G(w) = w̄² + O(1)` identify `c'`.

This module records the Liouville step in the form the FBif construction uses it.
-/
import Submission.Work.FBif.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function
open scoped Topology

noncomputable section

namespace Work.FBif

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The Liouville step of the straightening.**  If `G : ℂ → ℂ` is antiholomorphic (i.e.
`z ↦ conj (G z)` is entire) and `G z - (z̄)²` is bounded, then `G` is the quadratic antipolynomial
`T_{c'}` for a unique `c'`. -/
theorem antiholo_of_norm_sub_sq_bounded {G : ℂ → ℂ} (hG : Differentiable ℂ (star ∘ G))
    (hb : ∃ C : ℝ, ∀ z : ℂ, ‖G z - (star z) ^ 2‖ ≤ C) :
    ∃ c' : ℂ, ∀ z : ℂ, G z = Tantibar c' z := by
  obtain ⟨C, hC⟩ := hb
  have hF : Differentiable ℂ (fun z : ℂ => (star ∘ G) z - z ^ 2) :=
    hG.sub (differentiable_id.pow 2)
  have hbdd : Bornology.IsBounded (Set.range fun z : ℂ => (star ∘ G) z - z ^ 2) := by
    refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := 0) (r := C)) ?_
    rintro w ⟨z, rfl⟩
    have h1 : star (G z - (star z) ^ 2) = star (G z) - z ^ 2 := by
      rw [star_sub, star_pow, star_star]
    simp only [Function.comp_apply]
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, ← h1, norm_star]
    exact hC z
  obtain ⟨γ, hγ⟩ := hF.exists_const_forall_eq_of_bounded hbdd
  refine ⟨star γ, fun z => ?_⟩
  have h1 : star (G z) = z ^ 2 + γ := by
    have h := hγ z
    simp only [Function.comp_apply] at h
    linear_combination h
  calc G z = star (star (G z)) := (star_star _).symm
    _ = star (z ^ 2 + γ) := congrArg star h1
    _ = star (z ^ 2) + star γ := star_add _ _
    _ = (star z) ^ 2 + star γ := by rw [star_pow]
    _ = Tantibar (star γ) z := by simp [Tantibar]

end Work.FBif

end
