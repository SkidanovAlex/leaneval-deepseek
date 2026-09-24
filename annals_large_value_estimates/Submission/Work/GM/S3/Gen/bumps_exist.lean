import Mathlib
import Submission.Work.GM.S3.gen_defs
import Submission.Work.GM.S3.bumpAtOne_majorant
import Submission.Commons.Analysis.Calculus.smooth_bump_support_Icc_deriv_bounds

/-!
# Existence of the two Gauss–Maynard bumps of §7 (at the scale `C₀ = 4`)

The proof of Proposition 7.2 of Guth–Maynard uses a smooth bump `ψ₁` supported on `|x| ≤ 4`
with `ψ₁ 0 = 1` and `ψ₁ ≥ 1` on `|x| ≤ 1`, and a smooth bump `ψ₂` supported on `[1/4, 4]`
with `ψ₂ 1 = 1` and `ψ₂ ≥ 1` on `[1/2, 2]`.  This file constructs them explicitly out of
`Real.smoothTransition` (the standard `C^∞` step, `0` on `(-∞,0]` and `1` on `[1,∞)`):

* `ψ₁ x = st (2 + x/2) * st (2 - x/2)` — the first factor equals `1` for `x ≥ -2` and vanishes
  for `x ≤ -4`, the second equals `1` for `x ≤ 2` and vanishes for `x ≥ 4`; the product is `1`
  on `[-2,2] ⊇ [-1,1]` and vanishes off `(-4,4)`.
* `ψ₂ x = st (8x - 2) * st (32 - 8x)` — the first factor equals `1` for `x ≥ 3/8` and vanishes
  for `x ≤ 1/4`, the second equals `1` for `x ≤ 31/8` and vanishes for `x ≥ 4`; the product is `1`
  on `[3/8, 31/8] ⊇ [1/2,2]` and vanishes off `(1/4, 4)`.

Both are non-negative, `C^∞`, compactly supported, hence (by
`Commons.Analysis.Calculus.exists_bound_iteratedDeriv_of_hasCompactSupport_smooth`) have uniformly
bounded iterated derivatives.
-/

namespace Work.GM.S3.Gen

theorem bumps_exist :
    ∃ ψ₁ ψ₂ : ℝ → ℝ, Work.GM.S3.IsBumpAtZero ψ₁ 4 ∧ Work.GM.S3.IsBumpAtOne ψ₂ 4 ∧
      (∀ x, |x| ≤ 1 → 1 ≤ ψ₁ x) ∧ (∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, 1 ≤ ψ₂ x) := by
  set f : ℝ → ℝ := fun x => Real.smoothTransition (2 + x / 2) * Real.smoothTransition (2 - x / 2)
  set g : ℝ → ℝ := fun x => Real.smoothTransition (8 * x - 2) * Real.smoothTransition (32 - 8 * x)
  have hfcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
    rw [show f = fun x => Real.smoothTransition (2 + x / 2) * Real.smoothTransition (2 - x / 2)
      from rfl]
    fun_prop
  have hfnonneg : ∀ x, 0 ≤ f x := by
    intro x
    change 0 ≤ Real.smoothTransition (2 + x / 2) * Real.smoothTransition (2 - x / 2)
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hfsupp : ∀ x, f x ≠ 0 → |x| ≤ 4 := by
    intro x hx
    change Real.smoothTransition (2 + x / 2) * Real.smoothTransition (2 - x / 2) ≠ 0 at hx
    have h1 : Real.smoothTransition (2 + x / 2) ≠ 0 := fun h => hx (by rw [h, zero_mul])
    have h2 : Real.smoothTransition (2 - x / 2) ≠ 0 := fun h => hx (by rw [h, mul_zero])
    have h1' : 0 < 2 + x / 2 := by
      by_contra h
      rw [not_lt] at h
      exact h1 (Real.smoothTransition.zero_of_nonpos h)
    have h2' : 0 < 2 - x / 2 := by
      by_contra h
      rw [not_lt] at h
      exact h2 (Real.smoothTransition.zero_of_nonpos h)
    rw [abs_le]
    constructor <;> linarith
  have hfzero : f 0 = 1 := by
    change Real.smoothTransition (2 + 0 / 2) * Real.smoothTransition (2 - 0 / 2) = 1
    rw [Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2 + 0 / 2),
        Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2 - 0 / 2)]
    norm_num
  have hfcs : HasCompactSupport f :=
    HasCompactSupport.intro (K := Set.Icc (-4 : ℝ) 4) isCompact_Icc fun x hx =>
      by_contra fun hne => hx (by
        have h := hfsupp x hne
        rw [abs_le] at h
        exact h)
  have hfmaj : ∀ x, |x| ≤ 1 → 1 ≤ f x := by
    intro x hx
    change 1 ≤ Real.smoothTransition (2 + x / 2) * Real.smoothTransition (2 - x / 2)
    rw [Real.smoothTransition.one_of_one_le (by rw [abs_le] at hx; linarith : (1 : ℝ) ≤ 2 + x / 2),
        Real.smoothTransition.one_of_one_le (by rw [abs_le] at hx; linarith : (1 : ℝ) ≤ 2 - x / 2)]
    norm_num
  have hgcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := by
    rw [show g = fun x => Real.smoothTransition (8 * x - 2) * Real.smoothTransition (32 - 8 * x)
      from rfl]
    fun_prop
  have hgnonneg : ∀ x, 0 ≤ g x := by
    intro x
    change 0 ≤ Real.smoothTransition (8 * x - 2) * Real.smoothTransition (32 - 8 * x)
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hgsupp : ∀ x, g x ≠ 0 → x ∈ Set.Icc (1 / 4 : ℝ) 4 := by
    intro x hx
    change Real.smoothTransition (8 * x - 2) * Real.smoothTransition (32 - 8 * x) ≠ 0 at hx
    have h1 : Real.smoothTransition (8 * x - 2) ≠ 0 := fun h => hx (by rw [h, zero_mul])
    have h2 : Real.smoothTransition (32 - 8 * x) ≠ 0 := fun h => hx (by rw [h, mul_zero])
    have h1' : 0 < 8 * x - 2 := by
      by_contra h
      rw [not_lt] at h
      exact h1 (Real.smoothTransition.zero_of_nonpos h)
    have h2' : 0 < 32 - 8 * x := by
      by_contra h
      rw [not_lt] at h
      exact h2 (Real.smoothTransition.zero_of_nonpos h)
    rw [Set.mem_Icc]
    constructor <;> linarith
  have hgone : g 1 = 1 := by
    change Real.smoothTransition (8 * 1 - 2) * Real.smoothTransition (32 - 8 * 1) = 1
    rw [Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 8 * 1 - 2),
        Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 32 - 8 * 1)]
    norm_num
  have hgcs : HasCompactSupport g :=
    HasCompactSupport.intro (K := Set.Icc (1 / 4 : ℝ) 4) isCompact_Icc fun x hx =>
      by_contra fun hne => hx (hgsupp x hne)
  have hgmaj : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, 1 ≤ g x := by
    intro x hx
    rw [Set.mem_Icc] at hx
    change 1 ≤ Real.smoothTransition (8 * x - 2) * Real.smoothTransition (32 - 8 * x)
    rw [Real.smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ 8 * x - 2),
        Real.smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ 32 - 8 * x)]
    norm_num
  have hfderiv : ∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x, |iteratedDeriv j f x| ≤ c :=
    Commons.Analysis.Calculus.exists_bound_iteratedDeriv_of_hasCompactSupport_smooth hfcont hfcs
  have hgderiv : ∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x, |iteratedDeriv j g x| ≤ c :=
    Commons.Analysis.Calculus.exists_bound_iteratedDeriv_of_hasCompactSupport_smooth hgcont hgcs
  exact ⟨f, g, ⟨hfcont, hfnonneg, hfsupp, hfzero, hfderiv⟩,
    ⟨hgcont, hgnonneg, hgsupp, hgone, hgderiv⟩, hfmaj, hgmaj⟩

end Work.GM.S3.Gen
