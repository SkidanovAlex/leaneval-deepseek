/-
# The `§6` model-approximation error of the mixed range at bounded height

The band-restricted single-scale error at `ρ ≤ 1` is supplied by
`Work.Analysis.LoMixedPorts.singleScaleErrBand` (a copy of
`Work.KMTAreas.A7.LoMixedSingleScaleHolds` with the `ρ ≤ 1` range).  This module

* states it as the `Prop` `SingleScaleErrBand` (so that the summation can be proved before the
  single-scale estimate lands),
* performs the **summation over the lacunary scales** at bounded height: the weight
  `smallScaleWeight C ρ 0 l₂ k₁ k₂` is a constant once `lcL 0 l₂ k₁ k₂ ≤ B`, and
  `∑'_n ⌊a n⌋⁻¹ ≤ 2Λ/(Λ-1)` (`Work.KMTAreas.A7.tsum_inv_floor_le`), so the variational norm of the
  band-gated error is bounded by `K(Λ)‖f‖₂‖g‖₂`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.VarNormTsumLp
import Submission.Work.KMTAreas.A7.ModelApproxHelpers
import Submission.Work.KMTAreas.A7.lacDilTriVar
import Submission.Work.KMTPlan.A6.BoundedHMain.HZ.SymDMass

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6.BoundedHMain

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7 Work.KMTContract
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

noncomputable section

/-- **The band-restricted single-scale `§6` error of the mixed range, for `ρ ≤ 1` and the exponents
`(2,2,1)`.**  This is the `ρ ≤ 1` strengthening of `Work.KMTAreas.A7.LoMixedSingleScaleStatement`
specialised to `p₁ = p₂ = 2`. -/
def SingleScaleErrBand (P : Polynomial ℤ) : Prop :=
  ∀ C₀ : ℕ, 1 ≤ C₀ → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
    ∃ C : ℝ, 0 ≤ C ∧ ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ) (n : ℕ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) → 1 ≤ l₂ →
        MeasureTheory.eLpNorm (fun x : ℤ =>
            if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n
              ∧ Work.KMTAreas.A7.loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) then
              Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
                - Work.KMTAreas.A7.loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x
            else 0) 1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.smallScaleWeight C ρ 0 l₂ k₁ k₂)
              * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹)
              * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count

/-- **The weight `smallScaleWeight C ρ 0 l₂ k₁ k₂` is a constant at bounded height.** -/
theorem smallScaleWeight_le_of_lcL_le {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ) {l₂ k₁ k₂ B : ℕ}
    (hB : Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ ≤ B) :
    Work.KMTAreas.A7.smallScaleWeight C ρ 0 l₂ k₁ k₂
      ≤ (2 : ℝ) ^ (C * max ((2 : ℝ) ^ (ρ * (B : ℝ))) (B : ℝ)) := by
  have hB' : ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hL : Work.KMTAreas.A7.lmaxR 0 l₂ k₁ k₂ ≤ (B : ℝ) := by
    rw [Work.KMTAreas.A7.lmaxR, ← Work.KMTPlan.A6.lcL_eq]
    exact hB'
  have hmax : max ((2 : ℝ) ^ (ρ * Work.KMTAreas.A7.lmaxR 0 l₂ k₁ k₂))
        (Work.KMTAreas.A7.lmaxR 0 l₂ k₁ k₂)
      ≤ max ((2 : ℝ) ^ (ρ * (B : ℝ))) (B : ℝ) := by
    refine max_le (le_trans ?_ (le_max_left _ _)) (le_trans hL (le_max_right _ _))
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_left hL hρ)
  rw [Work.KMTAreas.A7.smallScaleWeight]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_left hmax hC)

/-- **The band-restricted `§6` error, summed over the lacunary scales, at bounded height.** -/
theorem bandErr_of_singleScale (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℕ)
    (hs : SingleScaleErrBand P) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ ≤ B → 1 ≤ l₂ →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ =>
              if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n
                ∧ Work.KMTAreas.A7.loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) then
                Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
                  - Work.KMTAreas.A7.loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x
              else 0)) 1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  obtain ⟨C, hC0, K₀, hK₀⟩ := hs C₀ hC₀ ρ hρ hρ1
  set Wmax : ℝ := (2 : ℝ) ^ (C * max ((2 : ℝ) ^ (ρ * (B : ℝ))) (B : ℝ)) with hWmax
  refine ⟨fun Λ => Real.toNNReal (4 * (K₀ Λ : ℝ) * Wmax
    * (2 * (Λ : ℝ) / ((Λ : ℝ) - 1))), ?_⟩
  intro a Λ l₂ k₁ k₂ f g hΛ ha ha1 hlB hl₂
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  set X : ENNReal := MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
    * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count with hX
  set u : ℕ → ℤ → ℂ := fun n x =>
    (if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n
      ∧ Work.KMTAreas.A7.loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) then
      Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
        - Work.KMTAreas.A7.loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x
    else 0) with hu
  -- the per-scale bound, with the weight replaced by the constant `Wmax`
  have hper : ∀ n : ℕ, MeasureTheory.eLpNorm (fun x : ℤ => u n x) 1 MeasureTheory.Measure.count
      ≤ (K₀ Λ : ENNReal) * ENNReal.ofReal Wmax
        * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) * X := by
    intro n
    have h := hK₀ a Λ l₂ k₁ k₂ f g n hΛ ha ha1 hl₂
    have hW : Work.KMTAreas.A7.smallScaleWeight C ρ 0 l₂ k₁ k₂ ≤ Wmax := by
      rw [hWmax]
      exact smallScaleWeight_le_of_lcL_le hC0 hρ.le hlB
    rw [hu]
    refine h.trans ?_
    rw [hX]
    calc (K₀ Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.smallScaleWeight C ρ 0 l₂ k₁ k₂)
          * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹)
          * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
        = (K₀ Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.smallScaleWeight C ρ 0 l₂ k₁ k₂)
          * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹)
          * (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) := by ring
      _ ≤ (K₀ Λ : ENNReal) * ENNReal.ofReal Wmax
          * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹)
          * (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) := by
          gcongr
  -- the reciprocal sum over the lacunary scales
  have hsumm : Summable fun n : ℕ => (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ :=
    Work.KMTAreas.A7.summable_invFloor Λ hΛ a ha ha1
  have htsum : (∑' n : ℕ, ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹))
      ≤ ENNReal.ofReal (2 * (Λ : ℝ) / ((Λ : ℝ) - 1)) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm]
    exact ENNReal.ofReal_le_ofReal (Work.KMTAreas.A7.tsum_inv_floor_le Λ hΛ a ha ha1)
  -- the summation
  refine (Work.KMTAreas.A7.VarNormTsumLp (r := r) hr1 (p := 1) le_rfl u).trans ?_
  have hstep1 : (∑' n : ℕ, 4 * MeasureTheory.eLpNorm (fun x : ℤ => u n x) 1
        MeasureTheory.Measure.count)
      ≤ ∑' n : ℕ, 4 * ((K₀ Λ : ENNReal) * ENNReal.ofReal Wmax
          * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) * X) :=
    ENNReal.tsum_le_tsum (fun n => mul_le_mul' le_rfl (hper n))
  refine hstep1.trans ?_
  have hstep2 : (∑' n : ℕ, 4 * ((K₀ Λ : ENNReal) * ENNReal.ofReal Wmax
        * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) * X))
      = 4 * (K₀ Λ : ENNReal) * ENNReal.ofReal Wmax * X
        * (∑' n : ℕ, ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹)) := by
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    ring
  rw [hstep2]
  refine (mul_le_mul' le_rfl htsum).trans ?_
  -- the final arithmetic
  have hEq' : (4 : ENNReal) * (K₀ Λ : ENNReal) * ENNReal.ofReal Wmax
      * ENNReal.ofReal (2 * (Λ : ℝ) / ((Λ : ℝ) - 1))
      = ENNReal.ofReal (4 * (K₀ Λ : ℝ) * Wmax * (2 * (Λ : ℝ) / ((Λ : ℝ) - 1))) := by
    rw [show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) from (ENNReal.ofReal_ofNat 4).symm,
      show (K₀ Λ : ENNReal) = ENNReal.ofReal (K₀ Λ : ℝ) from (ENNReal.ofReal_coe_nnreal).symm,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * (K₀ Λ : ℝ)),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * (K₀ Λ : ℝ) * Wmax)]
  rw [hX, ENNReal.ofNNReal_toNNReal, ← hEq']
  exact le_of_eq (by ring)

end

end Work.KMTPlan.A6.BoundedHMain
