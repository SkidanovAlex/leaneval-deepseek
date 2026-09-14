import Submission.NBody.LYZBound
import Submission.NBody.Minimizer
import Submission.Commons.MeasureTheory.Integral.intervalIntegrable_deriv_of_absolutelyContinuousOnInterval
import Mathlib

/-!
# Sub-curves of `h`-minimisers and the mass length (Liu--Yan--Zhou route)

This module collects the toolkit used by the dyadic induction of Liu--Yan--Zhou:

* `intervalIntegrable_weightedNorm_deriv` -- the mass norm of the derivative of an absolutely
  continuous curve is interval integrable;
* `massLength_add` -- the mass length is additive (for absolutely continuous curves);
* `IsHMinimizer.sub_left_of_le`, `actionOn_lt_top_of_le` -- the initial sub-curve of an
  `h`-minimiser is again an `h`-minimiser with finite action;
* `massLength_le_psi_sub` -- the length bound of Liu--Yan--Zhou Lemma 4.1 applied to an initial
  sub-curve.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The mass norm of the derivative is interval integrable** along an absolutely continuous
curve. -/
lemma intervalIntegrable_weightedNorm_deriv {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i)
    {γ : ℝ → EN E N} {a b : ℝ} (hab : a ≤ b) (hac : AbsolutelyContinuousOnInterval γ a b) :
    IntervalIntegrable (fun t : ℝ => ‖deriv γ t‖_[m]) volume a b := by
  have hint : IntervalIntegrable (deriv γ) volume a b :=
    Commons.MeasureTheory.Integral.intervalIntegrable_deriv_of_absolutelyContinuousOnInterval hac
  have hnorm : Integrable (fun t : ℝ => ‖deriv γ t‖) (volume.restrict (Set.Ioc a b)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hint.norm
  have hg : Integrable (fun t : ℝ => Real.sqrt (∑ i, m i) * ‖deriv γ t‖)
      (volume.restrict (Set.Ioc a b)) := hnorm.const_mul _
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine hg.mono' (aestronglyMeasurable_weightedNorm_deriv hac) ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (weightedNorm_nonneg m _)]
  exact weightedNorm_le_mul_norm hm (deriv γ t)

/-- **Additivity of the mass length.** -/
theorem massLength_add {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i)
    {γ : ℝ → EN E N} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hac : AbsolutelyContinuousOnInterval γ a c) :
    massLength m γ a c = massLength m γ a b + massLength m γ b c := by
  have hab_ac : AbsolutelyContinuousOnInterval γ a b :=
    hac.mono (by rw [uIcc_of_le hab, uIcc_of_le (hab.trans hbc)]
                 exact Set.Icc_subset_Icc_right hbc)
  have hbc_ac : AbsolutelyContinuousOnInterval γ b c :=
    hac.mono (by rw [uIcc_of_le hbc, uIcc_of_le (hab.trans hbc)]
                 exact Set.Icc_subset_Icc_left hab)
  have h1 := intervalIntegrable_weightedNorm_deriv hm hab hab_ac
  have h2 := intervalIntegrable_weightedNorm_deriv hm hbc hbc_ac
  have h := intervalIntegral.integral_add_adjacent_intervals h1 h2
  rw [massLength, massLength, massLength]
  linarith [h]

/-- **The initial sub-curve of an `h`-minimiser is an `h`-minimiser.** -/
theorem IsHMinimizer.sub_left_of_le {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {τ σ : ℝ}
    (hac : AbsolutelyContinuousOnInterval γ 0 τ) (hmin : IsHMinimizer m h γ 0 τ)
    (hfin : actionOn m h γ 0 τ < ⊤) (hσ0 : 0 < σ) (hστ : σ ≤ τ) :
    IsHMinimizer m h γ 0 σ := by
  rcases lt_or_eq_of_le hστ with hlt | heq
  · exact IsHMinimizer.sub_left hac hmin hfin hσ0 hlt
  · rw [heq]; exact hmin

/-- Finiteness of the action on an initial sub-interval. -/
theorem actionOn_lt_top_of_le {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {τ σ : ℝ}
    (hσ0 : 0 ≤ σ) (hστ : σ ≤ τ) (hfin : actionOn m h γ 0 τ < ⊤) :
    actionOn m h γ 0 σ < ⊤ := by
  rw [actionOn_add γ hσ0 hστ] at hfin
  exact (ENNReal.add_lt_top.mp hfin).1

/-- **Liu--Yan--Zhou Lemma 4.1 for an initial sub-curve.**  If `γ` is an `h`-minimiser on
`[0,τ]` with finite action, collision free, and `γ σ = x* + D • b` with `‖b‖_[m] = 1`, then the
mass length of `γ|[0,σ]` is at most `D + Ψ(D)`. -/
theorem massLength_le_psi_sub {m : Fin N → ℝ} {h : ℝ} (hh : 0 < h) (hm : ∀ i, 0 ≤ m i)
    {γ : ℝ → EN E N} {xstar b : EN E N} {σ τ D A B M : ℝ}
    (hσ0 : 0 ≤ σ) (hστ : σ ≤ τ) (hD : 0 < D)
    (hac : AbsolutelyContinuousOnInterval γ 0 τ)
    (hnc : ∀ t ∈ Set.Icc 0 τ, WithoutCollisions (γ t))
    (hfin : actionOn m h γ 0 τ < ⊤)
    (hmin : IsHMinimizer m h γ 0 τ)
    (hγσ : γ σ = xstar + D • b) (hb : ‖b‖_[m] = 1)
    (hncseg : ∀ t ∈ Set.Icc (0:ℝ) D, WithoutCollisions (xstar + t • b))
    (hΦ₁ : actionPot m h (γ 0) xstar < ⊤)
    (hA : (Real.sqrt (2 * h))⁻¹ * (actionPot m h (γ 0) xstar).toReal ≤ A)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hM0 : 0 ≤ M)
    (hpot : ∫ t in (0:ℝ)..D, U m (xstar + t • b) ≤ (2 * h) * B * Real.log (2 * D + 2 * M + 1))
    (hlog : 0 ≤ Real.log (2 * D + 2 * M + 1)) :
    massLength m γ 0 σ ≤ D + lyzPsi A B M D := by
  rcases eq_or_lt_of_le hσ0 with h0 | h0
  · rw [← h0, massLength]
    simp only [intervalIntegral.integral_same]
    have := lyzPsi_nonneg hA0 hB0 hM0 (le_of_lt hD)
    linarith
  rcases lt_or_eq_of_le hστ with hlt | heq
  · have hacσ : AbsolutelyContinuousOnInterval γ 0 σ :=
      hac.mono (by rw [uIcc_of_le hσ0, uIcc_of_le (le_trans hσ0 hστ)]
                   exact Set.Icc_subset_Icc_right hστ)
    have hncσ : ∀ t ∈ Set.Icc 0 σ, WithoutCollisions (γ t) :=
      fun t ht => hnc t ⟨ht.1, ht.2.trans hστ⟩
    have hminσ : IsHMinimizer m h γ 0 σ := IsHMinimizer.sub_left_of_le hac hmin hfin h0 hlt.le
    have hfinσ : actionOn m h γ 0 σ < ⊤ := actionOn_lt_top_of_le hσ0 hστ hfin
    exact massLength_le_psi hh hm hσ0 hD hacσ hncσ hfinσ hminσ hγσ hb hncseg hΦ₁ hA hpot hlog
  · rw [heq]
    exact massLength_le_psi hh hm (le_trans hσ0 (le_of_eq heq)) hD hac hnc hfin hmin
      (heq ▸ hγσ) hb hncseg hΦ₁ hA hpot hlog

end Submission.NBody
