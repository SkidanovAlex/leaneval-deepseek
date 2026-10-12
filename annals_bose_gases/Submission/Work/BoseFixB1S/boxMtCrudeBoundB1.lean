import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxMtMomentBoundsB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The crude scalar weight bound**: for `c ≥ 0` and an occupation number `n : ℕ`,

    n·(√(n+1) − √c)² ≤ 4n² + 2cn .

At `n = 0` both sides are `0`; for `n ≥ 1` the difference of the two sides equals
`n·(3n − 1 + c + 2√(n+1)√c) ≥ 0`. -/
theorem mtCrudeScalarB1 {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    (n : ℝ) * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt c) ^ 2
      ≤ 4 * (n : ℝ) ^ 2 + 2 * c * (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; norm_num
  · have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    have hs : (0 : ℝ) ≤ (n : ℝ) := le_trans zero_le_one hn
    have hAsq : (Real.sqrt ((n : ℝ) + 1)) ^ 2 = (n : ℝ) + 1 :=
      Real.sq_sqrt (by linarith : (0 : ℝ) ≤ (n : ℝ) + 1)
    have hcsq : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc
    have hdiff : 4 * (n : ℝ) ^ 2 + 2 * c * (n : ℝ)
        - (n : ℝ) * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt c) ^ 2
        = (n : ℝ) * (3 * (n : ℝ) - 1 + c
            + 2 * Real.sqrt ((n : ℝ) + 1) * Real.sqrt c) := by
      rw [sub_sq, hAsq, hcsq]; ring
    have h3 : 0 ≤ 3 * (n : ℝ) - 1 := by linarith
    have hprod : 0 ≤ 2 * Real.sqrt ((n : ℝ) + 1) * Real.sqrt c :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    have hnn : 0 ≤ (n : ℝ) * (3 * (n : ℝ) - 1 + c
        + 2 * Real.sqrt ((n : ℝ) + 1) * Real.sqrt c) :=
      mul_nonneg hs (by linarith)
    linarith [hdiff ▸ hnn]

theorem boxMtCrudeBoundB1 {N : ℕ} {ℓ V c : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) (hc : 0 ≤ c)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) = 1) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
          (Work.UBBInputs8.boxPInd V A i Φ)) x ^ 2)
        ≤ 4 * (Work.BoseFixB1S.boxPairCount V ℓ A Φ
            - (Work.BoseFixB1S.boxFlatCount V ℓ A Φ ^ 2
                - Work.BoseFixB1S.boxFlatCount V ℓ A Φ))
          + 4 * (Work.BoseFixB1S.boxFlatCount V ℓ A Φ) ^ 2
          + 2 * c * Work.BoseFixB1S.boxFlatCount V ℓ A Φ := by
  classical
  -- `Φ` is bounded on the box, so the spectral machinery applies
  have hΦG : Work.BoseFixB1S.GoodState ℓ Φ := by
    obtain ⟨C, hC⟩ :=
      (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn hΦc.continuousOn
    exact ⟨hΦc.measurable, C, fun x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩
  -- the sector weights `p S = ∫ (P_S Φ)²`, nonnegative
  let p : Finset (Fin N) → ℝ := fun S => ∫ x in Submission.BoseGases.abox N ℓ,
    (Work.BoseFixB1S.n0ProjOp V A S Φ) x ^ 2
  have hpnonneg : ∀ S : Finset (Fin N), 0 ≤ p S := by
    intro S
    exact MeasureTheory.integral_nonneg
      (f := fun x : Submission.BoseGases.X N =>
        (Work.BoseFixB1S.n0ProjOp V A S Φ) x ^ 2) (fun x => sq_nonneg _)
  -- the three spectral moments of `n₀`
  have hM0 : (∑ S : Finset (Fin N), p S) = 1 :=
    (n0Moments_oneB1 hℓ hV hA hVeq hAc hΦc).trans hnorm
  have hM1 : (∑ S : Finset (Fin N), (S.card : ℝ) * p S) = boxFlatCount V ℓ A Φ :=
    n0Moments_twoB1 hℓ hV hA hVeq hAc hΦc
  have hM2 : (∑ S : Finset (Fin N), ((S.card : ℝ) ^ 2) * p S)
      = boxFlatCount V ℓ A Φ + boxPairCount V ℓ A Φ :=
    n0Moments_threeB1 hℓ hV hA hVeq hAc hΦc
  -- the spectral expansion of the `P`-side moment
  have hT : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
        (Work.UBBInputs8.boxPInd V A i Φ)) x ^ 2)
      = ∑ S : Finset (Fin N), (S.card : ℝ) *
          (Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt c) ^ 2 * p S :=
    n0FunOpSumSpectralB1 hℓ hV hA hVeq hAc
      (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c) hΦG
  -- the crude pointwise weight bound, summed against the nonnegative weights `p S`
  have step : (∑ S : Finset (Fin N), (S.card : ℝ) *
        (Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt c) ^ 2 * p S)
      ≤ ∑ S : Finset (Fin N),
          (4 * (S.card : ℝ) ^ 2 + 2 * c * (S.card : ℝ)) * p S := by
    refine Finset.sum_le_sum (fun S _ => ?_)
    exact mul_le_mul_of_nonneg_right (mtCrudeScalarB1 hc S.card) (hpnonneg S)
  -- the quadratic expansion in the three moments
  have quad : (∑ S : Finset (Fin N),
        (4 * (S.card : ℝ) ^ 2 + 2 * c * (S.card : ℝ)) * p S)
      = 4 * (∑ S : Finset (Fin N), ((S.card : ℝ) ^ 2) * p S)
        + 2 * c * (∑ S : Finset (Fin N), (S.card : ℝ) * p S) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun S _ => by ring)
  calc (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
          (Work.UBBInputs8.boxPInd V A i Φ)) x ^ 2)
      = ∑ S : Finset (Fin N), (S.card : ℝ) *
          (Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt c) ^ 2 * p S := hT
    _ ≤ ∑ S : Finset (Fin N),
          (4 * (S.card : ℝ) ^ 2 + 2 * c * (S.card : ℝ)) * p S := step
    _ = 4 * (Work.BoseFixB1S.boxFlatCount V ℓ A Φ
            + Work.BoseFixB1S.boxPairCount V ℓ A Φ)
          + 2 * c * Work.BoseFixB1S.boxFlatCount V ℓ A Φ := by
        rw [quad, hM2, hM1]
    _ = 4 * (Work.BoseFixB1S.boxPairCount V ℓ A Φ
            - (Work.BoseFixB1S.boxFlatCount V ℓ A Φ ^ 2
                - Work.BoseFixB1S.boxFlatCount V ℓ A Φ))
          + 4 * (Work.BoseFixB1S.boxFlatCount V ℓ A Φ) ^ 2
          + 2 * c * Work.BoseFixB1S.boxFlatCount V ℓ A Φ := by ring

end Work.BoseFixB1S
