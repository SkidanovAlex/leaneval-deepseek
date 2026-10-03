/-
# The support of the modulated Ionescu--Wainger bump at *every* height `k₁ : ℕ`

`Work.KMTAreas.A7.varphiNt_support_le` gives the support bound

    `varphiNt N k₁ t ξ ≠ 0  →  |ξ| ≤ 2^{k₁ - Log N}`

under the hypothesis `1 ≤ k₁` (the range in which `φ_N` is the *difference* of the two rescalings
`η(2^{Log N - k₁}·) − η(2^{Log N - k₁ + 1}·)`).

Here the same bound is proved with **no** hypothesis on `k₁`: at the bottom height `k₁ = 0` the bump
degenerates to `φ_N = η(2^{Log N}·)`, whose support is `|ξ| < 2^{-Log N}`, still inside the bound
`|ξ| ≤ 2^{0 - Log N}`.  The modulation `e(Nt·)` is nowhere zero, so it never enlarges the support.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.varphiNt_support_le

namespace Work.KMTPlan.A6

/-- **The support of `φ_{N,t}` at an arbitrary height.**  A nonzero value of the modulated bump
`varphiNt N k₁ t` forces `|ξ| ≤ 2 ^ (k₁ - Log N)`, the case `k₁ = 0` included.

For `k₁ ≥ 1` this is exactly `varphiNt_support_le`; for `k₁ = 0` we have
`varphiN N 0 ξ = kmtEta (2^{Log N} ξ)`, so `kmtEta_zero` bounds `2^{Log N} |ξ|` by `1`. -/
theorem varphiNt_support_all (N k₁ : ℕ) (t : ℝ) :
    ∀ ξ : ℝ, Work.KMTAreas.A7.varphiNt N k₁ t ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by
  intro ξ hξ
  rcases Nat.eq_zero_or_pos k₁ with hk | hk
  · -- the bottom height `k₁ = 0`, where `φ_N = η(2^{Log N}·)`
    subst hk
    -- the modulation `e(Nt·)` is nowhere zero, so it may be discarded
    have hprod : Work.KMTAreas.A7.varphiN N 0 ξ * Work.KMTAreas.A7.ee ((N : ℝ) * t * ξ) ≠ 0 := by
      simpa only [Work.KMTAreas.A7.varphiNt] using hξ
    have h1 : Work.KMTAreas.A7.varphiN N 0 ξ ≠ 0 := (mul_ne_zero_iff.mp hprod).1
    have h2 : Work.KMTContract.kmtEta ((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) * ξ) ≠ 0 := by
      simpa only [Work.KMTAreas.A7.varphiN, if_true] using h1
    -- a nonzero value of the cutoff forces its argument inside `(-1, 1)`
    have h3 : ¬ (1 ≤ |(2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) * ξ|) :=
      fun hc => h2 (Work.KMTContract.kmtEta_zero hc)
    have h4 : |(2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) * ξ| < 1 := lt_of_not_ge h3
    have hp : (0 : ℝ) < (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) :=
      Real.rpow_pos_of_pos (by norm_num) _
    rw [abs_mul, abs_of_pos hp] at h4
    -- solve `2^{Log N} |ξ| < 1` for `|ξ|`
    have h7 : |ξ| < ((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ))⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ hp]
      linarith
    rw [← Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num) (Work.Analysis.EndVar.logN N : ℝ)] at h7
    simpa only [Nat.cast_zero, zero_sub] using le_of_lt h7
  · -- the heights `k₁ ≥ 1`
    exact Work.KMTAreas.A7.varphiNt_support_le k₁ hk N t ξ hξ

end Work.KMTPlan.A6
