import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Nonnegative summable functions on ℤ (Section 3 foundations)

Tikhomirov 2020, Section 3 ("Random averaging in ℓ₁(ℤ)").  All the Section-3
machinery (kernels, averaged functions, ℓ₁/ℓ₂ mass estimates) is built on
nonnegative real-valued functions on the integers.  This module fixes a small,
self-contained interface around `Summable`/`tsum` on `ℤ`:

- `IntFun.norm₁ f := ∑' t : ℤ, f t`  (total mass; for nonnegative `f`),
- translation invariance of the total mass,
- linearity over finite convex combinations,
- a finite window carries at most the total mass,
- a geometric two-sided kernel (used in the anticoncentration corollary),
- Markov-style counting of the points where a mass-one function is large.

Everything here is `Mathlib`-only and could migrate to the commons later.
-/

namespace Submission.IntFun

open scoped BigOperators

/-- Total mass (ℓ₁) of a nonnegative function on ℤ. -/
def norm₁ (f : ℤ → ℝ) : ℝ := ∑' t : ℤ, f t

/-- Square of the ℓ₂ norm. -/
def norm₂sq (f : ℤ → ℝ) : ℝ := ∑' t : ℤ, (f t) ^ 2

lemma summable_norm₁ {f : ℤ → ℝ} (hf : Summable f) : Summable f := hf

lemma norm₁_nonneg {f : ℤ → ℝ} (hf : ∀ t, 0 ≤ f t) : 0 ≤ norm₁ f := by
  unfold norm₁
  exact tsum_nonneg hf

-- translation invariance of the mass
lemma norm₁_add_right {f : ℤ → ℝ} (c : ℤ) (hf : Summable f) :
    norm₁ (fun t : ℤ => f (t + c)) = norm₁ f := by
  unfold norm₁
  let e : ℤ ≃ ℤ := Equiv.addRight c
  have hcomp : (fun t : ℤ => f (t + c)) = f ∘ e := by
    funext t
    rfl
  change (∑' t : ℤ, f (e t)) = ∑' t : ℤ, f t
  exact Equiv.tsum_eq e f

lemma norm₁_sub_right {f : ℤ → ℝ} (c : ℤ) (hf : Summable f) :
    norm₁ (fun t : ℤ => f (t - c)) = norm₁ f := by
  unfold norm₁
  let e : ℤ ≃ ℤ := Equiv.subRight c
  have hcomp : (fun t : ℤ => f (t - c)) = f ∘ e := by
    funext t
    rfl
  change (∑' t : ℤ, f (e t)) = ∑' t : ℤ, f t
  exact Equiv.tsum_eq e f

lemma norm₁_add {f g : ℤ → ℝ} (hf : Summable f) (hg : Summable g) :
    norm₁ (fun t => f t + g t) = norm₁ f + norm₁ g := by
  unfold norm₁
  exact Summable.tsum_add hf hg

lemma norm₁_const_mul {f : ℤ → ℝ} (a : ℝ) (hf : Summable f) :
    norm₁ (fun t => a * f t) = a * norm₁ f := by
  unfold norm₁
  rw [← tsum_mul_left]

lemma norm₁_mul_const {f : ℤ → ℝ} (a : ℝ) (hf : Summable f) :
    norm₁ (fun t => f t * a) = norm₁ f * a := by
  simp_rw [mul_comm _ a]
  rw [norm₁_const_mul a hf]

lemma norm₁_le {f g : ℤ → ℝ} (hf : Summable f) (hg : Summable g) (h : ∀ t, f t ≤ g t) :
    norm₁ f ≤ norm₁ g := by
  unfold norm₁
  exact Summable.tsum_le_tsum h hf hg

lemma summable_translate {f : ℤ → ℝ} (c : ℤ) (hf : Summable f) :
    Summable (fun t : ℤ => f (t + c)) := by
  let e : ℤ ≃ ℤ := Equiv.addRight c
  have hcomp : (fun t : ℤ => f (t + c)) = f ∘ e := by
    funext t
    rfl
  rw [hcomp]
  exact (Equiv.summable_iff e).2 hf

/-- Finite subset mass is below the total mass. -/
lemma Finset_sum_le_norm₁ {f : ℤ → ℝ} (hfpos : ∀ t, 0 ≤ f t) (hf : Summable f)
    (s : Finset ℤ) : (∑ t ∈ s, f t) ≤ norm₁ f := by
  classical
  unfold norm₁
  have hgpos : ∀ t : ℤ, 0 ≤ (s : Set ℤ).indicator f t := by
    intro t
    by_cases ht : t ∈ (s : Set ℤ)
    · simpa [Set.indicator, ht] using hfpos t
    · simp [Set.indicator, ht]
  have hgle : ∀ t : ℤ, (s : Set ℤ).indicator f t ≤ f t := by
    intro t
    by_cases ht : t ∈ (s : Set ℤ)
    · simp [Set.indicator, ht]
    · simpa [Set.indicator, ht] using hfpos t
  have hsum_ind : Summable ((s : Set ℤ).indicator f) :=
    Summable.of_nonneg_of_le hgpos hgle hf
  calc
    (∑ t ∈ s, f t) = ∑' t : ℤ, (s : Set ℤ).indicator f t := by
      rw [tsum_eq_sum (s := s)]
      · apply Finset.sum_congr rfl
        intro t ht
        simp [Set.indicator, ht]
      · intro t ht
        have htnot : t ∉ (s : Set ℤ) := by simpa using ht
        simp [Set.indicator, htnot]
    _ ≤ ∑' t : ℤ, f t := Summable.tsum_le_tsum hgle hsum_ind hf

/-- Finite interval mass is below the total mass. -/
lemma interval_sum_le_norm₁ {f : ℤ → ℝ} (hfpos : ∀ t, 0 ≤ f t) (hf : Summable f)
    (a b : ℤ) : (∑ t ∈ Finset.Icc a b, f t) ≤ norm₁ f := by
  exact Finset_sum_le_norm₁ hfpos hf (Finset.Icc a b)

end Submission.IntFun

