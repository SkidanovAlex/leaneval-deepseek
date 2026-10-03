import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface

/-!
# Minkowski's inequality for the variational norm

The `r`-variational norm `PointwiseErgodicTheorems.variationalNorm r a` of a sequence `a : ℕ → ℂ`
is the sum of two suprema: the supremum part `⨆ n, ‖a n‖ₑ` and the variation part
`Submission.PointwiseErgodicTheorems.varPart r a` (the supremum, over all monotone index maps `N`,
of the `ℓ^r` norm of the successive differences of `a` along `N`).  Both parts are suprema of
finite-dimensional norms, and each of those commutes with the Bochner integral.

The lemma below is the resulting Minkowski-type inequality: the variational norm of the family of
interval integrals `m ↦ ∫_{1/2}^1 X t m dt` is at most the integral of the variational norms of the
integrands:

  `variationalNorm r (fun m => ∫_{1/2}^1 X t m dt) ≤ ∫_{1/2}^1 variationalNorm r (fun m => X t m) dt`.

The two terms are handled separately:

* the supremum part, by `enorm_integral_le_lintegral_enorm` and `iSup_le` (the supremum of the
  integrals is at most the integral of the supremum);
* the variation part, by the finite-dimensional Minkowski inequality
  `enorm_integral_le_lintegral_enorm` applied in the space `PiLp r (Fin J → ℂ)` (whose norm is the
  `ℓ^r` norm of the successive differences), after transporting the integral through the
  continuous linear equivalence `PiLp.continuousLinearEquiv` (whose inverse is
  `WithLp.toLp r`) and reading off the coordinates with `MeasureTheory.eval_integral`;

the two estimates are added with the additivity of the `ℝ≥0∞`-valued integral
(`lintegral_add_left'`, whose measurability hypothesis is the almost-everywhere measurability of
the countable supremum `t ↦ ⨆ n, ‖X t n‖ₑ`, supplied by `AEMeasurable.iSup`).
-/

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators

theorem varNorm_intervalIntegral_le (r : NNReal) (hr : 1 ≤ r) (X : ℝ → ℕ → ℂ)
    (hint : ∀ m : ℕ, MeasureTheory.Integrable (fun t : ℝ => X t m)
      (MeasureTheory.volume.restrict (Set.Ioc (1/2 : ℝ) 1))) :
    PointwiseErgodicTheorems.variationalNorm r
        (fun m : ℕ => intervalIntegral (fun t : ℝ => X t m) (1/2 : ℝ) 1 MeasureTheory.volume) ≤
      MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioc (1/2 : ℝ) 1))
        (fun t => PointwiseErgodicTheorems.variationalNorm r (fun m : ℕ => X t m)) := by
  haveI : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  set μ : Measure ℝ := volume.restrict (Set.Ioc (1/2 : ℝ) 1) with hμ
  have hle : (1/2 : ℝ) ≤ 1 := by norm_num
  have hint' : ∀ m : ℕ, Integrable (fun t : ℝ => X t m) μ := fun m => by rw [hμ]; exact hint m
  set a : ℕ → ℂ := fun m => ∫ t, X t m ∂μ with ha
  have ha_eq : (fun m : ℕ => intervalIntegral (fun t : ℝ => X t m) (1/2 : ℝ) 1
      MeasureTheory.volume) = a := by
    funext m
    rw [intervalIntegral.integral_of_le hle]
  rw [ha_eq]
  -- The supremum part: the supremum of the integrals is bounded by the integral of the supremum.
  have hS : (⨆ n : ℕ, ‖a n‖ₑ) ≤ ∫⁻ t, (⨆ n : ℕ, ‖X t n‖ₑ) ∂μ := by
    refine iSup_le fun n => ?_
    calc ‖a n‖ₑ = ‖∫ t, X t n ∂μ‖ₑ := by rfl
      _ ≤ ∫⁻ t, ‖X t n‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t, (⨆ n : ℕ, ‖X t n‖ₑ) ∂μ :=
          lintegral_mono fun t => le_iSup (fun n : ℕ => ‖X t n‖ₑ) n
  -- The countable supremum of the extended norms is almost everywhere measurable.
  have hmeasS : AEMeasurable (fun t : ℝ => ⨆ n : ℕ, ‖X t n‖ₑ) μ :=
    AEMeasurable.iSup fun n => (hint' n).aestronglyMeasurable.enorm
  -- The variation part: Minkowski's inequality in the finite-dimensional space `ℓ^r`.
  have hV : Submission.PointwiseErgodicTheorems.varPart r a ≤
      ∫⁻ t, Submission.PointwiseErgodicTheorems.varPart r (fun m : ℕ => X t m) ∂μ := by
    unfold Submission.PointwiseErgodicTheorems.varPart
    refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
    set F : ℝ → (Fin J → ℂ) := fun t i => X t (N (i + 1)) - X t (N i) with hF
    have hFint : ∀ i : Fin J, Integrable (fun t => F t i) μ := by
      intro i
      simp only [hF]
      exact (hint' (N (i + 1))).sub (hint' (N i))
    -- The coordinates of the integral of `F` are the differences of the integrals.
    have hcoord : (∫ t, F t ∂μ) = fun i : Fin J => a (N (i + 1)) - a (N i) := by
      funext i
      rw [eval_integral hFint i]
      simp only [hF]
      rw [integral_sub (hint' (N (i + 1))) (hint' (N i))]
    -- The integral commutes with `WithLp.toLp r` (a continuous linear equivalence).
    have hCLE : (∫ t, WithLp.toLp r (F t) ∂μ) = WithLp.toLp r (∫ t, F t ∂μ) :=
      (PiLp.continuousLinearEquiv (r : ℝ≥0∞) ℝ (fun _ : Fin J => ℂ)).symm.integral_comp_comm F
    calc ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J => a (N (i + 1)) - a (N i))‖
        = ENNReal.ofReal ‖WithLp.toLp r (∫ t, F t ∂μ)‖ := by rw [hcoord]
      _ = ‖∫ t, WithLp.toLp r (F t) ∂μ‖ₑ := by rw [← hCLE, ofReal_norm]
      _ ≤ ∫⁻ t, ‖WithLp.toLp r (F t)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t, Submission.PointwiseErgodicTheorems.varPart r (fun m : ℕ => X t m) ∂μ := by
          refine lintegral_mono fun t => ?_
          rw [← ofReal_norm]
          simp only [hF]
          refine le_iSup_of_le (f := fun J' => ⨆ (N' : ℕ → ℕ) (_ : Monotone N'),
              ENNReal.ofReal ‖WithLp.toLp r
                (fun i : Fin J' => X t (N' (i + 1)) - X t (N' i))‖) J ?_
          exact le_iSup₂ (f := fun (N' : ℕ → ℕ) (_ : Monotone N') =>
              ENNReal.ofReal ‖WithLp.toLp r
                (fun i : Fin J => X t (N' (i + 1)) - X t (N' i))‖) N hN
  calc PointwiseErgodicTheorems.variationalNorm r a
      = (⨆ n : ℕ, ‖a n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r a :=
          Submission.PointwiseErgodicTheorems.variationalNorm_eq_add r a
    _ ≤ (∫⁻ t, (⨆ n : ℕ, ‖X t n‖ₑ) ∂μ) +
          (∫⁻ t, Submission.PointwiseErgodicTheorems.varPart r (fun m : ℕ => X t m) ∂μ) :=
          add_le_add hS hV
    _ = ∫⁻ t, ((⨆ n : ℕ, ‖X t n‖ₑ) +
          Submission.PointwiseErgodicTheorems.varPart r (fun m : ℕ => X t m)) ∂μ :=
          (lintegral_add_left' hmeasS _).symm
    _ = ∫⁻ t, PointwiseErgodicTheorems.variationalNorm r (fun m : ℕ => X t m) ∂μ :=
          lintegral_congr fun t =>
            (Submission.PointwiseErgodicTheorems.variationalNorm_eq_add r
              (fun m : ℕ => X t m)).symm

end Work.KMTAreas.A7
