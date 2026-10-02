import Mathlib
import Submission.Work.NAKANE2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE2.Surgery

open LeanEval.ComplexAnalysis

/-- Two points have the same image under the mandelbar iterator `T̄_c` if and only
if they are equal or opposite: `T̄_c` is (generically) two-to-one, and the two
preimages of a value are `±`-symmetric.  Here we only need the forward direction:
`T̄_c a = T̄_c b` forces `a = b` or `a = -b`. -/
lemma Tantibar_eq_or_eq_neg {c a b : ℂ} (h : Tantibar c a = Tantibar c b) :
    a = b ∨ a = -b := by
  have h2 : (starRingEnd ℂ a) ^ 2 = (starRingEnd ℂ b) ^ 2 := by
    simpa only [Tantibar] using add_right_cancel h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h' | h'
  · left
    have := congrArg (starRingEnd ℂ) h'
    simpa using this
  · right
    have := congrArg (starRingEnd ℂ) h'
    simpa using this

/-- If a homeomorphism `θ` conjugates an **even** map `g` (satisfying `g(-z) = g z`)
to the mandelbar iterator `T̄_{c'}`, then it must map the symmetry centre `0` to `0`.

Indeed, the conjugacy relation gives `T̄_{c'}(θ(-z)) = T̄_{c'}(θ z)` for every `z`.
Since the fibres of `T̄_{c'}` are `±`-symmetric, this forces `θ(-z) = ±θ(z)`;
injectivity of `θ` rules out `θ(-z) = θ(z)` unless `z = 0`, so `θ(-z) = -θ(z)`
for all `z ≠ 0`.  Continuity of `θ` then gives `θ 0 = θ(-0) = -θ 0`, hence
`θ 0 = 0`. -/
theorem principal_zero_eq_zero {c' : ℂ} {g : ℂ → ℂ} {θ : ℂ ≃ₜ ℂ}
    (hconj : ∀ z : ℂ, θ (g z) = LeanEval.ComplexAnalysis.Tantibar c' (θ z))
    (hg : ∀ z : ℂ, g (-z) = g z) : θ 0 = 0 := by
  have hanti : ∀ z : ℂ, z ≠ 0 → θ (-z) = -θ z := by
    intro z hz
    have hT : Tantibar c' (θ (-z)) = Tantibar c' (θ z) := by
      rw [← hconj (-z), ← hconj z, hg z]
    rcases Tantibar_eq_or_eq_neg hT with h | h
    · exfalso
      have hzz : -z = z := θ.injective h
      have hsum : z + z = 0 := eq_neg_iff_add_eq_zero.mp hzz.symm
      have h2 : (2 : ℂ) * z = 0 := by rw [two_mul]; exact hsum
      rcases mul_eq_zero.mp h2 with hh | hh
      · norm_num at hh
      · exact hz hh
    · exact h
  -- The continuous function `z ↦ θ(-z) + θ z` vanishes off the origin, hence at it.
  have hcont : Continuous (fun z : ℂ => θ (-z) + θ z) :=
    (θ.continuous.comp continuous_neg).add θ.continuous
  have hsub : ({0}ᶜ : Set ℂ) ⊆ (fun z : ℂ => θ (-z) + θ z) ⁻¹' {0} := by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [hanti z hz, neg_add_cancel]
  have hcl : IsClosed ((fun z : ℂ => θ (-z) + θ z) ⁻¹' {0}) :=
    isClosed_singleton.preimage hcont
  have hdense : Dense ({0}ᶜ : Set ℂ) := dense_compl_singleton 0
  have hzero : (0 : ℂ) ∈ (fun z : ℂ => θ (-z) + θ z) ⁻¹' {0} := by
    have huniv : Set.univ ⊆ (fun z : ℂ => θ (-z) + θ z) ⁻¹' {0} := by
      rw [← hdense.closure_eq]
      exact hcl.closure_subset_iff.mpr hsub
    exact huniv (Set.mem_univ 0)
  have hz0 : θ 0 + θ 0 = 0 := by simpa using hzero
  have h2 : (2 : ℂ) * θ 0 = 0 := by rw [two_mul]; exact hz0
  rcases mul_eq_zero.mp h2 with hh | hh
  · norm_num at hh
  · exact hh

end Work.NAKANE2.Surgery
