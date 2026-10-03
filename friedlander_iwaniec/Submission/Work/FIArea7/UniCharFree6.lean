/-
# `Submission.Work.FIArea7.UniCharFree6` — the §16 identity at the (17.10) mode objects

The last unwritten step of the (17.10) engine: identify the per-`(b,e,k)` term of the
*guard-free* mode sum `Work.FIArea7.uniModeSumFree` with the right-hand side of the §16 character
expansion `Work.FIArea7.uniModeCharSum` (via `Work.FIArea7.section16_omegaDetect_expansion`), and
then the full sums:

* `uniModeCharFree_eq_uniModeCharSum`  (the per-`(b,e,k)` identity, `[NeZero (4*b*e)]`),
* `uniModeSumFree_eq_WUniOmega6Pull6Char`  (the summed identity).

With `Work.FIArea7.WUniOmega6Pull6Moll_eq_modes` (`WUniOmega6Pull6Moll = uniModeSum`, proved) and
the mollifier/guard-removal errors, these give the (17.10) decomposition of `WUni6` into the
`(1/Φ(4be))Σ_χ J(χ)|S^k_χ|²` main term plus the standard errors.
-/
import Mathlib
import Submission.Work.FIArea7.GuardRemoval6
import Submission.Work.FIArea7.UniCharTerm6

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The per-`(b,e,k)` §16 identity of the (17.10) expansion.**  The guard-free mode sum
`uniModeCharFree` (left-hand side of `section16_omegaDetect_expansion` with `Q = 4be`, `e = e` and
`c = uniCoeff ε β k`) equals the `(1/Φ(4be))Σ_χ J(χ)|S^k_χ|²` of (17.10)/(17.11)/(17.12). -/
theorem uniModeCharFree_eq_uniModeCharSum (Pa : Work.FITop.Params) (b e : ℕ)
    [NeZero (4 * b * e)] (β : GaussianInt → ℂ) (k : ℤ) (ε : GaussianInt → ℤ) :
    uniModeCharFree Pa b e β k ε = uniModeCharSum Pa b e β k ε := by
  have h := section16_omegaDetect_expansion (Work.FITop.radN Pa) (4 * b * e) e
    (uniCoeff ε β k)
  simp only [uniModeCharFree, uniModeCharSum, uniJChar, uniSChar, omegaDetect_unfold6]
  rw [h]
  congr 1
  refine Finset.sum_congr rfl (fun χ _ => ?_)
  ring

/-- `4*b*e ≠ 0` for `1 ≤ b`, `1 ≤ e`. -/
lemma four_mul_ne_zero_of_pos {b e : ℕ} (hb : 1 ≤ b) (he : 1 ≤ e) : 4 * b * e ≠ 0 := by
  have h1 : 0 < b := hb
  have h2 : 0 < e := he
  positivity

/-- **The summed §16 identity (the (17.10) main term).**  `uniModeSumFree` — the guard-free mode
decomposition of `WUniOmega6Pull6Moll` — is exactly `WUniOmega6Pull6Char`, the `Σ_k û(k)Σ_{b,e}
(μ(b)/b)(1/Φ(4be))Σ_χ J(χ)|S^k_χ|²` of (17.10). -/
theorem uniModeSumFree_eq_WUniOmega6Pull6Char (Pa : Work.FITop.Params) (X : ℕ)
    (β : GaussianInt → ℂ) (K : ℕ) (ε : GaussianInt → ℤ) :
    uniModeSumFree Pa X β K ε = WUniOmega6Pull6Char Pa X β K ε := by
  rw [uniModeSumFree, WUniOmega6Pull6Char]
  congr 1
  refine Finset.sum_congr rfl (fun b hb => ?_)
  refine Finset.sum_congr rfl (fun e he => ?_)
  obtain ⟨hb1, _⟩ := Finset.mem_Icc.mp hb
  obtain ⟨he1, _⟩ := Finset.mem_Icc.mp he
  have hne : 4 * b * e ≠ 0 := four_mul_ne_zero_of_pos hb1 he1
  rw [uniCharTerm, dif_neg hne]
  haveI : NeZero (4 * b * e) := ⟨hne⟩
  have key : ∀ k : ℤ, uniModeCharFree Pa b e β k ε = uniModeCharSum Pa b e β k ε :=
    fun k => uniModeCharFree_eq_uniModeCharSum Pa b e β k ε
  simp only [key]

end

end Work.FIArea7
