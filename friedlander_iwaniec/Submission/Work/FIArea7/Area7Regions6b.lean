/-
# `Work.FIArea7.Area7Regions6b` — the modulus-threshold split with the angular-mode slack

`NOTES.md` §60 records that the round-6 reduction applies the deep input to sums whose coefficient
carries the **angular mollifier** `q(arg z − φ)` of (5.12) (and, in case (B) of
`reflSign_separable`, the reflection sign `ε = ±sign(re)`), whereas *FI* Proposition 17.2 is a
statement about the **moment-free** coefficient (17.15).  The paper bridges the two by expanding the
angular content in Fourier modes `e^{iℓα}` (16.27), which replaces one sum at frequency `k` by
`Σ_{|ℓ|≤L} ĉ(ℓ)·S^{k+ℓ}` — so the deep input is applied at the *shifted* frequencies `k+ℓ`, and the
Proposition-17.2 restriction becomes

  `(4be)·(|k+ℓ| + 1) ≤ N^{δ₁}`   for all `|k| ≤ 2K`, `|ℓ| ≤ L`,

i.e. `4be(2K + L + 2) ≤ N^{δ₁}`.  This file fixes that split, with the mode length `L` left as an
explicit parameter `L₀` (the assembly instantiates it at `⌈√X⌉ + 2`, see *NOTES* §60.4; the bound
`L₀ ≤ 2K+1` then makes the two regions differ from the ones of `Area7Regions6` by at most a
constant factor, which is why the repair is affordable).

Everything else — the engine, the guard removal, the mass caps, the numeric core — is untouched.
-/
import Mathlib
import Submission.Work.FIArea7.Area7Char6

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **Region I of the (17.10) main term, with the angular-mode slack**: the `(b,e)` such that
`4be(2K + L₀ + 2) ≤ N^{δ₁}`.  For every frequency `k` of `uniCharTerm` (`k = 0` or
`0 < |k| ≤ 2K`) and every Fourier mode `ℓ` with `|ℓ| ≤ L₀` one then has
`(4be)(|k+ℓ| + 1) ≤ N^{δ₁}`, which is the Proposition-17.2 restriction at the shifted frequency. -/
def charRegionLow6 (Pa : Work.FITop.Params) (X K L₀ : ℕ) (δ₁ : ℝ) (β : GaussianInt → ℂ)
    (ε : GaussianInt → ℤ) : ℂ :=
  2 * ∑ p ∈ ((Finset.Icc 1 (uniB Pa)).product (Finset.Icc 1 X)).filter
        (fun p => 4 * (p.1 : ℝ) * (p.2 : ℝ) * (2 * (K : ℝ) + (L₀ : ℝ) + 2) ≤ Pa.N ^ δ₁),
      uniCharTerm Pa p.1 p.2 β K ε

/-- **Region II of the (17.10) main term, with the angular-mode slack**: the complement of
`charRegionLow6`.  Here the modulus is large enough for the lattice count, which never uses the deep
input. -/
def charRegionHigh6 (Pa : Work.FITop.Params) (X K L₀ : ℕ) (δ₁ : ℝ) (β : GaussianInt → ℂ)
    (ε : GaussianInt → ℤ) : ℂ :=
  2 * ∑ p ∈ ((Finset.Icc 1 (uniB Pa)).product (Finset.Icc 1 X)).filter
        (fun p => ¬ (4 * (p.1 : ℝ) * (p.2 : ℝ) * (2 * (K : ℝ) + (L₀ : ℝ) + 2) ≤ Pa.N ^ δ₁)),
      uniCharTerm Pa p.1 p.2 β K ε

/-- **The modulus-threshold split with the angular-mode slack.**  (The same computation as
`Work.FIArea7.WUniOmega6Pull6Char_eq_regions`.) -/
theorem WUniOmega6Pull6Char_eq_regions6b (Pa : Work.FITop.Params) (X K L₀ : ℕ) (δ₁ : ℝ)
    (β : GaussianInt → ℂ) (ε : GaussianInt → ℤ) :
    WUniOmega6Pull6Char Pa X β K ε
      = charRegionLow6 Pa X K L₀ δ₁ β ε + charRegionHigh6 Pa X K L₀ δ₁ β ε := by
  have hprod : (∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X, uniCharTerm Pa b e β K ε)
      = ∑ p ∈ (Finset.Icc 1 (uniB Pa)).product (Finset.Icc 1 X), uniCharTerm Pa p.1 p.2 β K ε :=
    (Finset.sum_product (Finset.Icc 1 (uniB Pa)) (Finset.Icc 1 X)
      (fun p : ℕ × ℕ => uniCharTerm Pa p.1 p.2 β K ε)).symm
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 (uniB Pa)).product (Finset.Icc 1 X))
    (fun p : ℕ × ℕ =>
      4 * (p.1 : ℝ) * (p.2 : ℝ) * (2 * (K : ℝ) + (L₀ : ℝ) + 2) ≤ Pa.N ^ δ₁)
    (fun p : ℕ × ℕ => uniCharTerm Pa p.1 p.2 β K ε)
  rw [WUniOmega6Pull6Char, charRegionLow6, charRegionHigh6, hprod, ← mul_add, ← hsplit]

/-- The mode length used by the assembly.  Two lengths are needed by the angular Fourier
expansion of *NOTES* §60:

* `⌈√X⌉` bounds the truncation error of the angular mollifier `q` after squaring
  (`|δS| ≤ N/L` gives `|δS|² ≤ N²/X` for the target, §60.4);
* `⌈ϑ⁻¹⌉` is the mode length needed by the *step* factors — the strip boundaries of `IsAxisFree`
  (`§60.6(d)`), whose angular width is `≍ ϑ` — and by the sector ends (`§60.6(a)`).

Both are dominated by `2K+1` in the composition's regime (`X ≥ 1`, `K ≥ 1`), so the two regions
differ from those of `Area7Regions6` by at most a constant factor; see *NOTES* §60.4. -/
def angModeLen (Pa : Work.FITop.Params) (X : ℕ) : ℕ :=
  max (Nat.ceil (Real.sqrt X)) (Nat.ceil Pa.ϑ⁻¹) + 2

/-- `angModeLen` dominates `⌈√X⌉ + 2`. -/
lemma ceil_sqrt_le_angModeLen (Pa : Work.FITop.Params) (X : ℕ) :
    Nat.ceil (Real.sqrt X) + 2 ≤ angModeLen Pa X := by
  unfold angModeLen
  omega

end

end Work.FIArea7
