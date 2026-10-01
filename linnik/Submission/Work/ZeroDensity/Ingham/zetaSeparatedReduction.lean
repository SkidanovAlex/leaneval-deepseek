import Mathlib
import Submission.Work.ZeroDensity.Zeta.ZetaZeroDefs
import Submission.Work.ZeroDensity.Ingham.localZeroCountZeta
import Submission.Work.ZeroDensity.Ingham.existsSeparatedCover
import Submission.Work.ZeroDensity.Ingham.zetaStripCountBound
import Submission.Work.ZeroDensity.Ingham.zetaWindowZerosFinset
import Submission.Work.ZeroDensity.Ingham.logAddTwoLeRpow

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators
open MeasureTheory

/-- Auxiliary: a Finset sum of a nonnegative, finitely supported function is at most its `finsum`. -/
private lemma finset_sum_le_finsum {f : ℂ → ℝ} (hf : Function.HasFiniteSupport f)
    (h0 : ∀ a, 0 ≤ f a) (s : Finset ℂ) : ∑ a ∈ s, f a ≤ ∑ᶠ a, f a := by
  have hf' : (Function.support f).Finite := hf
  have hsub : Function.support f ⊆ ↑(s ∪ hf'.toFinset) := by
    intro a ha
    rw [Finset.mem_coe, Finset.mem_union]
    exact Or.inr ((Set.Finite.mem_toFinset hf').mpr ha)
  rw [finsum_eq_sum_of_support_subset f (s := s ∪ hf'.toFinset) hsub]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun a _ _ => h0 a)

/-- Auxiliary: the summand of a unit-strip zero count is nonnegative. -/
private lemma stripSummand_nonneg (t : ℝ) (ρ : ℂ) :
    0 ≤ (if |ρ.im - t| ≤ 1 then ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ) else 0) := by
  by_cases h : |ρ.im - t| ≤ 1
  · rw [if_pos h]; exact Nat.cast_nonneg _
  · rw [if_neg h]

/-- **The separated-set reduction for the zeros of `ζ`.**  For every `ε > 0` and all
`1/2 ≤ σ ≤ 1`, `T ≥ 2` the multiplicity-weighted zero count `N(σ,T)` of `ζ` is bounded by
`≪ T^ε #R`, where `R` is a maximal set of zeros whose imaginary parts are pairwise `≥ 1` apart:
`N(σ,T) ≤ C T^ε #R`, with `R` maximal `1`-separated in `Im` and every zero of the window within
`1` of some element of `R`.  (The local zero count `localZeroCountZeta` bounds the number of
zeros in a unit window by `≪ log(‖a‖+2) ≪ log T`, and the window count is absorbed into `T^ε`.) -/
theorem zetaSeparatedReduction :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (σ T : ℝ), 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      ∃ R : Finset ℂ,
        (∀ z ∈ R, analyticOrderNatAt completedRiemannZeta z ≠ 0 ∧
          σ ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T) ∧
        (∀ z ∈ R, ∀ z' ∈ R, z ≠ z' → 1 ≤ |z.im - z'.im|) ∧
        (∀ ρ : ℂ, analyticOrderNatAt completedRiemannZeta ρ ≠ 0 →
          σ ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T → ∃ z ∈ R, |ρ.im - z.im| ≤ 1) ∧
        (Work.ZeroDensity.Zeta.zetaZeroCount σ T ≤ C * T ^ ε * (R.card : ℝ)) := by
  intro ε hε
  obtain ⟨C₁, hC₁pos, hC₁fin, hC₁bd⟩ := zetaStripCountBound
  obtain ⟨K, hKpos, hK⟩ := logAddTwoLeRpow hε
  refine ⟨C₁ * K, mul_pos hC₁pos hKpos, ?_⟩
  intro σ T hσ _hσ1 hT
  obtain ⟨S, hS, hSsum⟩ := zetaWindowZerosFinset σ T hσ hT
  obtain ⟨R, hRS, hRsep, hRcov⟩ := existsSeparatedCover S
  have hRwin : ∀ z ∈ R, analyticOrderNatAt completedRiemannZeta z ≠ 0 ∧
      σ ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T := fun z hz => (hS z).mp (hRS hz)
  refine ⟨R, hRwin, hRsep, ?_, ?_⟩
  · intro ρ hρ hσρ hρ1 himρ
    exact hRcov ρ ((hS ρ).mpr ⟨hρ, hσρ, hρ1, himρ⟩)
  · rw [hSsum]
    have hstep1 : ∑ ρ ∈ S, ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ)
        ≤ ∑ ρ ∈ S, ∑ z ∈ R, (if |ρ.im - z.im| ≤ 1 then
            ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ) else 0) := by
      refine Finset.sum_le_sum (fun ρ hρS => ?_)
      obtain ⟨z₀, hz₀R, hz₀⟩ := hRcov ρ hρS
      calc ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ)
          = (if |ρ.im - z₀.im| ≤ 1 then
              ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ) else 0) := by rw [if_pos hz₀]
        _ ≤ ∑ z ∈ R, (if |ρ.im - z.im| ≤ 1 then
              ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ) else 0) :=
            Finset.single_le_sum (f := fun z : ℂ => (if |ρ.im - z.im| ≤ 1 then
              ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ) else 0))
              (fun z _ => stripSummand_nonneg z.im ρ) hz₀R
    have hstep2 : ∑ ρ ∈ S, ∑ z ∈ R, (if |ρ.im - z.im| ≤ 1 then
            ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ) else 0)
        = ∑ z ∈ R, ∑ ρ ∈ S, (if |ρ.im - z.im| ≤ 1 then
            ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ) else 0) := Finset.sum_comm
    have hstep3 : ∀ z ∈ R, ∑ ρ ∈ S, (if |ρ.im - z.im| ≤ 1 then
            ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ) else 0)
        ≤ ∑ᶠ ρ : ℂ, (if |ρ.im - z.im| ≤ 1 then
            ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ) else 0) :=
      fun z _ => finset_sum_le_finsum (hC₁fin z.im) (fun ρ => stripSummand_nonneg z.im ρ) S
    have hstep4 : ∑ z ∈ R, (∑ᶠ ρ : ℂ, (if |ρ.im - z.im| ≤ 1 then
            ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ) else 0))
        ≤ ∑ z ∈ R, C₁ * (Real.log (2 + |z.im|) + 2) :=
      Finset.sum_le_sum (fun z _ => hC₁bd z.im)
    have hstep5 : ∑ z ∈ R, C₁ * (Real.log (2 + |z.im|) + 2)
        ≤ ∑ z ∈ R, C₁ * (Real.log (2 + T) + 2) := by
      refine Finset.sum_le_sum (fun z hz => ?_)
      have him : |z.im| ≤ T := (hRwin z hz).2.2.2
      have hlog : Real.log (2 + |z.im|) ≤ Real.log (2 + T) :=
        Real.log_le_log (by positivity) (by linarith)
      exact mul_le_mul_of_nonneg_left (by linarith) hC₁pos.le
    have hstep6 : ∑ z ∈ R, C₁ * (Real.log (2 + T) + 2)
        = (R.card : ℝ) * (C₁ * (Real.log (2 + T) + 2)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hstep7 : (R.card : ℝ) * (C₁ * (Real.log (2 + T) + 2))
        ≤ (R.card : ℝ) * (C₁ * (K * T ^ ε)) := by
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      refine mul_le_mul_of_nonneg_left ?_ hC₁pos.le
      rw [show (2 : ℝ) + T = T + 2 by ring]
      exact hK T hT
    have hstep8 : (R.card : ℝ) * (C₁ * (K * T ^ ε)) = (C₁ * K) * T ^ ε * (R.card : ℝ) := by
      ring
    calc ∑ ρ ∈ S, ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ)
        ≤ ∑ ρ ∈ S, ∑ z ∈ R, (if |ρ.im - z.im| ≤ 1 then
            ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ) else 0) := hstep1
      _ = ∑ z ∈ R, ∑ ρ ∈ S, (if |ρ.im - z.im| ≤ 1 then
            ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ) else 0) := hstep2
      _ ≤ ∑ z ∈ R, (∑ᶠ ρ : ℂ, (if |ρ.im - z.im| ≤ 1 then
            ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ) else 0)) :=
          Finset.sum_le_sum hstep3
      _ ≤ ∑ z ∈ R, C₁ * (Real.log (2 + |z.im|) + 2) := hstep4
      _ ≤ ∑ z ∈ R, C₁ * (Real.log (2 + T) + 2) := hstep5
      _ = (R.card : ℝ) * (C₁ * (Real.log (2 + T) + 2)) := hstep6
      _ ≤ (R.card : ℝ) * (C₁ * (K * T ^ ε)) := hstep7
      _ = (C₁ * K) * T ^ ε * (R.card : ℝ) := hstep8

end Work.ZeroDensity.Ingham
