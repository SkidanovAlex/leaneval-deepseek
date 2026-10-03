/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Analysis.IonescuWainger.Symbol

/-!
# `ℓ^∞` membership of the periodisation of a compactly supported bounded function

`periodize φ ξ = ∑' k : ℤ, φ (x + k)`, where `x = (AddCircle.equivIco 1 0 ξ).val ∈ [0,1)` is the
canonical representative of `ξ ∈ ℝ/ℤ`.  If `φ` is measurable, vanishes outside `[-R, R]` and is
bounded by `C`, then for every `ξ` only the (uniformly bounded number of) integers `k` with
`-R-1 < k ≤ R` contribute, so `periodize φ` is bounded by `(2⌊R⌋+4) C`; being a finite sum of
measurable functions it is measurable.  Hence `periodize φ ∈ L^∞(ℝ/ℤ)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Analysis.IonescuWainger

open MeasureTheory

/-- The canonical representative `ℝ/ℤ → [0,1)` is measurable. -/
private lemma measurable_equivIco_val :
    Measurable (fun ξ : Circle => (AddCircle.equivIco (1 : ℝ) 0 ξ).val) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable

private lemma measurable_periodize_term {φ : ℝ → ℂ} (hmeas : Measurable φ) (k : ℤ) :
    Measurable (fun ξ : Circle => φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + k)) :=
  hmeas.comp (measurable_equivIco_val.add measurable_const)

/-- The integers `k` contributing to the periodisation of a function supported in `[-R, R]`
evaluated at a point of `[0,1)`: all contributions lie in the fixed interval
`[-(⌊R⌋+2), ⌊R⌋+1]`. -/
private lemma periodize_term_eq_zero {φ : ℝ → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hφ0 : ∀ x, R < |x| → φ x = 0) (ξ : Circle) {k : ℤ}
    (hk : k ∉ Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1)) :
    φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + k) = 0 := by
  by_contra hne
  have hx := (AddCircle.equivIco (1 : ℝ) 0 ξ).prop
  rw [Set.mem_Ico] at hx
  have hle : |(AddCircle.equivIco (1 : ℝ) 0 ξ).val + k| ≤ R := by
    by_contra h
    exact hne (hφ0 _ (lt_of_not_ge h))
  rw [abs_le] at hle
  have h1 : k ≤ ⌊R⌋ + 1 := by
    have hkx : (k : ℝ) ≤ R := by linarith [hle.2, hx.1]
    have := Int.le_floor.mpr hkx
    linarith
  have h2 : -(⌊R⌋ + 2) ≤ k := by
    have hk2 : ((-k - 2 : ℤ) : ℝ) ≤ R := by
      push_cast
      linarith [hle.1, hx.2, hR]
    have := Int.le_floor.mpr hk2
    linarith
  exact hk (by rw [Finset.mem_Icc]; exact ⟨h2, h1⟩)

theorem memLp_periodize {φ : ℝ → ℂ} (hmeas : Measurable φ) {R C : ℝ} (hR : 0 ≤ R)
    (hφ0 : ∀ x, R < |x| → φ x = 0) (hφC : ∀ x, ‖φ x‖ ≤ C) :
    MeasureTheory.MemLp (periodize φ) ⊤ circleMeasure := by
  set s : Finset ℤ := Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1) with hs
  have hkey : ∀ ξ : Circle,
      periodize φ ξ = ∑ k ∈ s, φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + k) := by
    intro ξ
    change (∑' k : ℤ, φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + k)) = _
    exact tsum_eq_sum fun k hk => periodize_term_eq_zero hR hφ0 ξ (by simpa [hs] using hk)
  have hbound : ∀ ξ : Circle, ‖periodize φ ξ‖ ≤ (s.card : ℝ) * C := by
    intro ξ
    rw [hkey ξ]
    calc ‖∑ k ∈ s, φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + k)‖
        ≤ ∑ k ∈ s, ‖φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + k)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ s, C := Finset.sum_le_sum fun k _ => hφC _
      _ = s.card * C := by simp [Finset.sum_const, nsmul_eq_mul]
  have hmeas_per : Measurable (periodize φ) := by
    rw [funext hkey]
    exact Finset.measurable_sum _ fun k _ => measurable_periodize_term hmeas k
  exact MemLp.mono' (memLp_top_const ((s.card : ℝ) * C)) hmeas_per.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

end Work.Analysis.IonescuWainger
