import Mathlib
import Submission.Work.BMF.mr_direct.range_defs
import Submission.Work.BMF.mr_direct.goodSet_bound_range_defs
import Submission.Work.BMF.Defs
import Submission.Work.BMF.mr_direct.rough_energy_transfer

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- The "rough" (no prime factor in `[P,Q]`) part of a Dirichlet polynomial over a range
`[X₁,X₂]`, integrated over a measurable set `u ⊆ [-S,S]`, is bounded by the trivial mean-value
bound: its mean square is at most `3 (C₀+1) (S+X₂)/X₁` times the reciprocal-weighted energy of
the coefficients over the integers coprime to `∏ p ∈ primesIn P Q, p`.

Proof: enlarge `u` to `[-S,S]`, apply the Montgomery-Vaughan mean value theorem
`Work.BMF.mrDirect.MVConst.mv_natIcc`, use the support hypothesis to discard the integers having
a prime factor in `[P,Q]` (the lemma `coprime_primesIn_iff` identifies "no prime of `[P,Q]`
divides `n`" with `n` coprime to the product; prove it locally if that separate file is not yet
ready), replace `1/n²` by `(1/X₁)·(1/n)` for `n ≥ X₁`, and compare
`2S + 3C₀X₂ ≤ 3 (C₀+1) (S+X₂)`. -/
theorem rough_set_integral_le (C₀ : ℝ) (hC₀ : Work.BMF.mrDirect.MVConst C₀)
    (a : ℕ → ℂ) (X₁ X₂ P Q S : ℝ) (u : Set ℝ)
    (hX1 : 1 ≤ X₁) (hX12 : X₁ ≤ X₂) (hS : 0 ≤ S)
    (hu : MeasurableSet u) (husub : u ⊆ Set.Icc (-S) S) (ha : ∀ n, ‖a n‖ ≤ 1)
    (hsupp : ∀ n : ℕ, (∃ p : ℕ, Nat.Prime p ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ p ∣ n) →
      a n = 0) :
    (∫ t in u, ‖Work.BMF.mrDirect.dirPolyR a X₁ X₂ t‖ ^ 2)
      ≤ 3 * (C₀ + 1) * ((S + X₂) / X₁ *
          (∑ n ∈ (Work.BMF.natIcc X₁ X₂).filter
            (fun n => n.Coprime (∏ p ∈ Work.BMF.primesIn P Q, p)), ‖a n‖ ^ 2 / (n : ℝ))) := by
  have hX1pos : 0 < X₁ := lt_of_lt_of_le zero_lt_one hX1
  have hX2pos : 0 < X₂ := lt_of_lt_of_le hX1pos hX12
  have hC₀nn : 0 ≤ C₀ := Work.BMF.mrDirect.MVConst.nonneg hC₀
  set E₁ : ℝ := ∑ n ∈ (Work.BMF.natIcc X₁ X₂).filter
        (fun n => n.Coprime (∏ p ∈ Work.BMF.primesIn P Q, p)), ‖a n‖ ^ 2 / (n : ℝ) with hE₁
  have hE₁nn : 0 ≤ E₁ := by
    rw [hE₁]
    exact Finset.sum_nonneg fun n _ => div_nonneg (by positivity) (by positivity)
  -- Step 1: enlarge the set `u` to the interval `[-S,S]`.
  have hcont : Continuous fun t : ℝ => ‖Work.BMF.mrDirect.dirPolyR a X₁ X₂ t‖ ^ 2 :=
    (Work.BMF.mrDirect.continuous_dirPolyR a X₁ X₂ hX1pos).norm.pow 2
  have hstep1 : (∫ t in u, ‖Work.BMF.mrDirect.dirPolyR a X₁ X₂ t‖ ^ 2)
      ≤ ∫ t in (-S)..S, ‖Work.BMF.mrDirect.dirPolyR a X₁ X₂ t‖ ^ 2 :=
    Work.BMF.mr_direct.setIntegral_le_intervalIntegral hS husub hcont (fun x _ => by positivity)
  -- Step 2: the Montgomery-Vaughan mean value bound.
  have hmv : (∫ t in (-S)..S, ‖Work.BMF.mrDirect.dirPolyR a X₁ X₂ t‖ ^ 2)
      ≤ (2 * S + 3 * C₀ * X₂) * ∑ n ∈ Work.BMF.natIcc X₁ X₂, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 :=
    Work.BMF.mrDirect.MVConst.mv_natIcc hC₀ a X₁ X₂ S hX1pos hX12 hS
  -- Step 3: drop the integers having a prime factor in `[P,Q]` and replace `1/n²` by `(1/X₁)/n`.
  have htr : (∑ n ∈ Work.BMF.natIcc X₁ X₂, ‖a n‖ ^ 2 / (n : ℝ) ^ 2) ≤ (1 / X₁) * E₁ := by
    rw [hE₁]
    exact rough_energy_transfer a X₁ X₂ P Q hX1 hsupp
  have hcoefnn : 0 ≤ 2 * S + 3 * C₀ * X₂ := by
    have h : 0 ≤ C₀ * X₂ := mul_nonneg hC₀nn hX2pos.le
    linarith
  have hnum : 2 * S + 3 * C₀ * X₂ ≤ 3 * (C₀ + 1) * (S + X₂) := by
    have h1 : 0 ≤ C₀ * S := mul_nonneg hC₀nn hS
    nlinarith [h1, hS, hC₀nn, hX2pos]
  have hstep4 : (2 * S + 3 * C₀ * X₂) * ((1 / X₁) * E₁)
      ≤ (3 * (C₀ + 1) * (S + X₂) / X₁) * E₁ := by
    have h1 : (2 * S + 3 * C₀ * X₂) / X₁ ≤ 3 * (C₀ + 1) * (S + X₂) / X₁ :=
      div_le_div_of_nonneg_right hnum hX1pos.le
    calc (2 * S + 3 * C₀ * X₂) * ((1 / X₁) * E₁)
        = ((2 * S + 3 * C₀ * X₂) / X₁) * E₁ := by ring
      _ ≤ (3 * (C₀ + 1) * (S + X₂) / X₁) * E₁ := mul_le_mul_of_nonneg_right h1 hE₁nn
  have hmain : (∫ t in u, ‖Work.BMF.mrDirect.dirPolyR a X₁ X₂ t‖ ^ 2)
      ≤ 3 * (C₀ + 1) * ((S + X₂) / X₁ * E₁) :=
    calc (∫ t in u, ‖Work.BMF.mrDirect.dirPolyR a X₁ X₂ t‖ ^ 2)
        ≤ ∫ t in (-S)..S, ‖Work.BMF.mrDirect.dirPolyR a X₁ X₂ t‖ ^ 2 := hstep1
      _ ≤ (2 * S + 3 * C₀ * X₂) * ∑ n ∈ Work.BMF.natIcc X₁ X₂, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := hmv
      _ ≤ (2 * S + 3 * C₀ * X₂) * ((1 / X₁) * E₁) :=
          mul_le_mul_of_nonneg_left htr hcoefnn
      _ ≤ (3 * (C₀ + 1) * (S + X₂) / X₁) * E₁ := hstep4
      _ = 3 * (C₀ + 1) * ((S + X₂) / X₁ * E₁) := by ring
  simpa only [hE₁] using hmain

end Work.BMF.mr_direct
