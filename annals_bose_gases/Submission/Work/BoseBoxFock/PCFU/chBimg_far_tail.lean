import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.W1funFarIntegrable
import Submission.Work.BoseBoxFock.PCFU.latVec_far_tail_sum
import Submission.Work.BoseBoxFock.PCFU.uvKernel_moment_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chBimg_far_tail`

The **far lattice tail** of the `(B)`-channel: for `x` in the box ball (`‖x‖ ≤ ℓ`) the images of
the smoothed weight `W₁ = W1fun v h ℓ` at the lattice points `x + ℓ•d` are summable outside the
small lattice `smLab = {-3,…,3}³`, with the sharp box-smallness

    Σ'_{d ∉ smLab} |uvSmear fu Λ W₁ (x + ℓ•d)|
      ≤ 4^5·227·Cd·(Λℓ)^{-2}·ℓ^{-3}·∫|W₁| .

## Mechanics

Off `smLab` the Euclidean norm `‖latVec d‖` is at least `4`, while `‖x‖ ≤ ℓ` and
`tsupport W₁ ⊆ ball 0 R` with `2R ≤ ℓ`; so every image point `x + ℓ•d` sits at distance

    D_d = ℓ·(‖latVec d‖ - 3/2)

from `tsupport W₁`.  The *scaled* Schwartz decay of the smoothing kernel
(`hdec`, the `N = 5` instance of `Work.BoseBoxFock.uvKernel_decay`) converts that distance into

    |uvSmear fu Λ W₁ (x + ℓ•d)| ≤ Cd·Λ³·(1 + Λ·D_d)^{-5}·∫|W₁| ≤ Cd·Λ^{-2}·D_d^{-5}·∫|W₁| ,

and since `D_d ≥ ℓ·(‖latVec d‖ - 3/2) ≥ ℓ·‖latVec d‖/4` (as `‖latVec d‖ ≥ 4`),

    Σ_{d ∉ smLab} D_d^{-5} ≤ ℓ^{-5}·4^5·Σ_{d ∉ smLab} ‖latVec d‖^{-5}
      ≤ ℓ^{-5}·4^5·Σ_{d ∉ smLab} ‖latVec d‖^{-4} ≤ ℓ^{-5}·4^5·227 .

The last sum is bounded by `227` for *every* finite set of lattice points
(`Work.BoseBoxFock.sum_inv_norm_latVec_le`), which is the source of the constant `4^5·227`.

The only place where the (weak) hypothesised integrability of `W₁` is used is to make the
Bochner integral `∫|W₁|` an honest number; it is supplied by the companion lemma
`Work.BoseBoxFock.PCFU.W1funFarIntegrable` (valid in the regime `2R ≤ ℓ`, via the positive lower
bound on `(χ⋆χ)(·/ℓ)` on the compact ball of radius `R < ℓ`).
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory
open scoped Real BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `y^{-5} = y^{-2}·y^{-3}` for `y ≠ 0` (the exponent bookkeeping used throughout). -/
lemma zpow_neg_five_eq_mul (y : ℝ) (hy : y ≠ 0) :
    y ^ (-(5 : ℤ)) = y ^ (-(2 : ℤ)) * y ^ (-(3 : ℤ)) := by
  rw [show (-(5 : ℤ)) = (-(2 : ℤ)) + (-(3 : ℤ)) by norm_num, zpow_add₀ hy]

/-- **The far-tail estimate**, with the two analytic inputs (integrability of `W₁` and the lattice
tail bound) supplied as hypotheses.

* `hWint` is exactly `Work.BoseBoxFock.PCFU.W1funFarIntegrable`;
* `hlat` is exactly `Work.BoseBoxFock.PCFU.latVec_far_tail_sum`. -/
theorem chBimg_far_tail_core {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fu : Work.BoseBoxFix.LowCut} {R ℓ Λ Cd : ℝ}
    (hR : 0 < R) (hℓ : 0 < ℓ) (hRℓ : 2 * R ≤ ℓ) (hΛ : 1 ≤ Λ) (hCd : 0 ≤ Cd)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hdec : ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖Work.BoseBoxFock.uvKernel fu Λ z‖ ≤ Cd * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(5 : ℤ)))
    (hWint : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => |Work.BoseFixR.W1fun v h ℓ z|))
    (hlat : ∀ u : Finset (Fin 3 → ℤ),
      (∑ d ∈ u, if d ∈ smLab then 0 else (‖latVec d‖ - 3 / 2) ^ (-(5 : ℤ))) ≤ 4 ^ 5 * 227)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ ≤ ℓ) :
    (∑' d : Fin 3 → ℤ, if d ∈ Work.BoseBoxFock.PCFU.smLab then 0
        else |Work.BoseBoxFock.uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ)
              (x + ℓ • Work.BoseBoxFock.latVec d)|)
      ≤ 4 ^ 5 * 227 * Cd * (Λ * ℓ) ^ (-(2 : ℤ)) * ℓ ^ (-(3 : ℤ))
          * (∫ y : EuclideanSpace ℝ (Fin 3), |Work.BoseFixR.W1fun v h ℓ y|) := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hΛne : Λ ≠ 0 := hΛpos.ne'
  have hℓne : ℓ ≠ 0 := hℓ.ne'
  let W : E3 → ℝ := Work.BoseFixR.W1fun v h ℓ
  let J : ℝ := ∫ y : E3, |W y|
  have hInn : 0 ≤ J := integral_nonneg (fun y => abs_nonneg _)
  have hWint' : Integrable (fun z : E3 => |W z|) := hWint
  -- the constant factor appearing inside the sum
  let C₀ : ℝ := Cd * Λ ^ (-(2 : ℤ)) * (ℓ ^ (-(2 : ℤ)) * ℓ ^ (-(3 : ℤ))) * J
  have hC₀nn : 0 ≤ C₀ := by
    refine mul_nonneg (mul_nonneg (mul_nonneg hCd (zpow_pos hΛpos _).le)
      (mul_nonneg (zpow_pos hℓ _).le (zpow_pos hℓ _).le)) hInn
  -- ## (A) the decay at a single far lattice point
  have hfar : ∀ d : Fin 3 → ℤ, d ∉ smLab →
      |Work.BoseBoxFock.uvSmear fu Λ W (x + ℓ • Work.BoseBoxFock.latVec d)|
        ≤ C₀ * (‖Work.BoseBoxFock.latVec d‖ - 3 / 2) ^ (-(5 : ℤ)) := by
    intro d hd
    have hd4 : 4 ≤ ‖Work.BoseBoxFock.latVec d‖ := norm_latVec_ge_of_notMem_smLab hd
    let K : ℝ := ‖Work.BoseBoxFock.latVec d‖ - 3 / 2
    have hKpos : 0 < K := by dsimp only [K]; linarith
    let D : ℝ := ℓ * K
    have hDpos : 0 < D := by dsimp only [D]; positivity
    have hΛDpos : 0 < Λ * D := mul_pos hΛpos hDpos
    -- the distance from `x + ℓ•d` to the origin
    have hy : R + D ≤ ‖x + ℓ • Work.BoseBoxFock.latVec d‖ := by
      have h1 : ℓ * ‖Work.BoseBoxFock.latVec d‖ - ‖x‖
          ≤ ‖x + ℓ • Work.BoseBoxFock.latVec d‖ := by
        have h2 : ‖(x + ℓ • Work.BoseBoxFock.latVec d) - x‖
            ≤ ‖x + ℓ • Work.BoseBoxFock.latVec d‖ + ‖x‖ := norm_sub_le _ _
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hℓ.le] at h2
        linarith
      have h2 : R + ℓ * (‖Work.BoseBoxFock.latVec d‖ - 3 / 2)
          ≤ ℓ * ‖Work.BoseBoxFock.latVec d‖ - ℓ := by nlinarith [hRℓ]
      have h3 : ℓ * ‖Work.BoseBoxFock.latVec d‖ - ℓ
          ≤ ℓ * ‖Work.BoseBoxFock.latVec d‖ - ‖x‖ := by linarith
      dsimp only [D, K]
      linarith
    -- the pointwise kernel majorant
    have hker : ∀ z : E3,
        |Work.BoseBoxFock.uvKernel fu Λ ((x + ℓ • Work.BoseBoxFock.latVec d) - z)| * |W z|
        ≤ (Cd * Λ ^ 3 * (1 + Λ * D) ^ (-(5 : ℤ))) * |W z| := by
      intro z
      by_cases hz : W z = 0
      · rw [hz, abs_zero, mul_zero, mul_zero]
      · have hzR : ‖z‖ < R := by
          have h1 : z ∈ tsupport W := subset_tsupport W (Function.mem_support.mpr hz)
          have h2 : z ∈ Metric.ball (0 : E3) R :=
            Work.BoseFixR.tsupport_W1fun_subset h hv_supp ℓ h1
          rwa [Metric.mem_ball, dist_zero_right] at h2
        have hdz : D ≤ ‖(x + ℓ • Work.BoseBoxFock.latVec d) - z‖ := by
          have h1 : ‖x + ℓ • Work.BoseBoxFock.latVec d‖ - ‖z‖
              ≤ ‖(x + ℓ • Work.BoseBoxFock.latVec d) - z‖ := by
            have h2 := abs_norm_sub_norm_le (x + ℓ • Work.BoseBoxFock.latVec d) z
            have h3 := le_abs_self (‖x + ℓ • Work.BoseBoxFock.latVec d‖ - ‖z‖)
            linarith
          linarith
        have hbase : 1 + Λ * D ≤ 1 + Λ * ‖(x + ℓ • Work.BoseBoxFock.latVec d) - z‖ := by
          have h2 : Λ * D ≤ Λ * ‖(x + ℓ • Work.BoseBoxFock.latVec d) - z‖ :=
            mul_le_mul_of_nonneg_left hdz hΛpos.le
          linarith
        have hExp : (1 + Λ * ‖(x + ℓ • Work.BoseBoxFock.latVec d) - z‖) ^ (-(5 : ℤ))
            ≤ (1 + Λ * D) ^ (-(5 : ℤ)) := by
          rw [zpow_neg, zpow_neg]
          exact (inv_le_inv₀ (by positivity) (by positivity)).mpr
            (pow_le_pow_left₀ (by positivity) hbase 5)
        have hdec' : |Work.BoseBoxFock.uvKernel fu Λ ((x + ℓ • Work.BoseBoxFock.latVec d) - z)|
            ≤ Cd * Λ ^ 3 * (1 + Λ * ‖(x + ℓ • Work.BoseBoxFock.latVec d) - z‖) ^ (-(5 : ℤ)) := by
          rw [← Real.norm_eq_abs]
          exact hdec _
        calc |Work.BoseBoxFock.uvKernel fu Λ ((x + ℓ • Work.BoseBoxFock.latVec d) - z)| * |W z|
            ≤ (Cd * Λ ^ 3
                * (1 + Λ * ‖(x + ℓ • Work.BoseBoxFock.latVec d) - z‖) ^ (-(5 : ℤ))) * |W z| :=
              mul_le_mul_of_nonneg_right hdec' (abs_nonneg _)
          _ ≤ (Cd * Λ ^ 3 * (1 + Λ * D) ^ (-(5 : ℤ))) * |W z| := by
              refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
              exact mul_le_mul_of_nonneg_left hExp (by positivity)
    have hstep : |Work.BoseBoxFock.uvSmear fu Λ W (x + ℓ • Work.BoseBoxFock.latVec d)|
        ≤ ∫ z : E3,
            |Work.BoseBoxFock.uvKernel fu Λ ((x + ℓ • Work.BoseBoxFock.latVec d) - z)| * |W z| := by
      rw [Work.BoseBoxFock.uvSmear]
      refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
      apply integral_congr_ae
      filter_upwards with z
      rw [abs_mul]
    have hInt : (∫ z : E3,
          |Work.BoseBoxFock.uvKernel fu Λ ((x + ℓ • Work.BoseBoxFock.latVec d) - z)| * |W z|)
        ≤ (Cd * Λ ^ 3 * (1 + Λ * D) ^ (-(5 : ℤ))) * J := by
      calc (∫ z : E3,
            |Work.BoseBoxFock.uvKernel fu Λ ((x + ℓ • Work.BoseBoxFock.latVec d) - z)| * |W z|)
          ≤ ∫ z : E3, (Cd * Λ ^ 3 * (1 + Λ * D) ^ (-(5 : ℤ))) * |W z| :=
            integral_mono_of_nonneg (ae_of_all _ (fun z => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
              (hWint'.const_mul _) (ae_of_all _ (fun z => hker z))
        _ = (Cd * Λ ^ 3 * (1 + Λ * D) ^ (-(5 : ℤ))) * J := by
            dsimp only [J]
            rw [integral_const_mul]
    have hmid : |Work.BoseBoxFock.uvSmear fu Λ W (x + ℓ • Work.BoseBoxFock.latVec d)|
        ≤ (Cd * Λ ^ 3 * (1 + Λ * D) ^ (-(5 : ℤ))) * J := hstep.trans hInt
    -- replace `(1 + ΛD)^{-5}` by `(ΛD)^{-5}` and collect the powers
    have hz1 : (1 + Λ * D) ^ (-(5 : ℤ)) ≤ (Λ * D) ^ (-(5 : ℤ)) := by
      rw [zpow_neg, zpow_neg]
      exact (inv_le_inv₀ (by positivity) (by positivity)).mpr
        (pow_le_pow_left₀ hΛDpos.le (by linarith) 5)
    have hsplit : Λ ^ 3 * (Λ * D) ^ (-(5 : ℤ)) = Λ ^ (-(2 : ℤ)) * D ^ (-(5 : ℤ)) := by
      rw [mul_zpow, ← mul_assoc]
      congr 1
      rw [← zpow_natCast Λ 3, ← zpow_add₀ hΛne]
      norm_num
    have hDpow : D ^ (-(5 : ℤ)) = (ℓ ^ (-(2 : ℤ)) * ℓ ^ (-(3 : ℤ))) * K ^ (-(5 : ℤ)) := by
      dsimp only [D]
      rw [mul_zpow, zpow_neg_five_eq_mul ℓ hℓne]
    calc |Work.BoseBoxFock.uvSmear fu Λ W (x + ℓ • Work.BoseBoxFock.latVec d)|
        ≤ (Cd * Λ ^ 3 * (1 + Λ * D) ^ (-(5 : ℤ))) * J := hmid
      _ ≤ (Cd * Λ ^ 3 * (Λ * D) ^ (-(5 : ℤ))) * J :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hz1 (by positivity)) hInn
      _ = C₀ * K ^ (-(5 : ℤ)) := by
          have hstep1 : Cd * Λ ^ 3 * (Λ * D) ^ (-(5 : ℤ)) * J
              = Cd * (Λ ^ 3 * (Λ * D) ^ (-(5 : ℤ))) * J := by ring
          rw [hstep1, hsplit, hDpow]
          dsimp only [C₀]
          ring
  -- ## (B) summation over the lattice
  have hpartial : ∀ u : Finset (Fin 3 → ℤ),
      (∑ d ∈ u, (if d ∈ Work.BoseBoxFock.PCFU.smLab then 0
        else |Work.BoseBoxFock.uvSmear fu Λ W (x + ℓ • Work.BoseBoxFock.latVec d)|))
        ≤ 4 ^ 5 * 227 * Cd * (Λ * ℓ) ^ (-(2 : ℤ)) * ℓ ^ (-(3 : ℤ)) * J := by
    intro u
    have h1 : (∑ d ∈ u, (if d ∈ Work.BoseBoxFock.PCFU.smLab then 0
        else |Work.BoseBoxFock.uvSmear fu Λ W (x + ℓ • Work.BoseBoxFock.latVec d)|))
        ≤ ∑ d ∈ u, (if d ∈ Work.BoseBoxFock.PCFU.smLab then 0
            else C₀ * (‖Work.BoseBoxFock.latVec d‖ - 3 / 2) ^ (-(5 : ℤ))) := by
      refine Finset.sum_le_sum (fun d _ => ?_)
      by_cases hd : d ∈ Work.BoseBoxFock.PCFU.smLab
      · simp [hd]
      · simp only [if_neg hd]
        exact hfar d hd
    have h2 : (∑ d ∈ u, (if d ∈ Work.BoseBoxFock.PCFU.smLab then 0
            else C₀ * (‖Work.BoseBoxFock.latVec d‖ - 3 / 2) ^ (-(5 : ℤ))))
        = C₀ * (∑ d ∈ u, if d ∈ Work.BoseBoxFock.PCFU.smLab then 0
            else (‖Work.BoseBoxFock.latVec d‖ - 3 / 2) ^ (-(5 : ℤ))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      by_cases hd : d ∈ Work.BoseBoxFock.PCFU.smLab <;> simp [hd]
    have h3 : C₀ * (∑ d ∈ u, if d ∈ Work.BoseBoxFock.PCFU.smLab then 0
            else (‖Work.BoseBoxFock.latVec d‖ - 3 / 2) ^ (-(5 : ℤ)))
        ≤ C₀ * (4 ^ 5 * 227) := mul_le_mul_of_nonneg_left (hlat u) hC₀nn
    have h4 : C₀ * (4 ^ 5 * 227)
        = 4 ^ 5 * 227 * Cd * (Λ * ℓ) ^ (-(2 : ℤ)) * ℓ ^ (-(3 : ℤ)) * J := by
      dsimp only [C₀]
      rw [mul_zpow]
      ring
    calc (∑ d ∈ u, (if d ∈ Work.BoseBoxFock.PCFU.smLab then 0
          else |Work.BoseBoxFock.uvSmear fu Λ W (x + ℓ • Work.BoseBoxFock.latVec d)|))
        ≤ _ := h1
      _ = _ := h2
      _ ≤ _ := h3
      _ = _ := h4
  refine Real.tsum_le_of_sum_le
    (f := fun d : Fin 3 → ℤ => if d ∈ Work.BoseBoxFock.PCFU.smLab then 0
      else |Work.BoseBoxFock.uvSmear fu Λ W (x + ℓ • Work.BoseBoxFock.latVec d)|) ?_ hpartial
  intro d
  by_cases hd : d ∈ Work.BoseBoxFock.PCFU.smLab
  · simp [hd]
  · simp only [if_neg hd]
    exact abs_nonneg _

theorem chBimg_far_tail {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fu : Work.BoseBoxFix.LowCut} {R ℓ Λ Cd : ℝ}
    (hR : 0 < R) (hℓ : 0 < ℓ) (hRℓ : 2 * R ≤ ℓ) (hΛ : 1 ≤ Λ) (hCd : 0 ≤ Cd)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hdec : ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖Work.BoseBoxFock.uvKernel fu Λ z‖ ≤ Cd * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(5 : ℤ)))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ ≤ ℓ) :
    (∑' d : Fin 3 → ℤ, if d ∈ Work.BoseBoxFock.PCFU.smLab then 0
        else |Work.BoseBoxFock.uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ)
              (x + ℓ • Work.BoseBoxFock.latVec d)|)
      ≤ 4 ^ 5 * 227 * Cd * (Λ * ℓ) ^ (-(2 : ℤ)) * ℓ ^ (-(3 : ℤ))
          * (∫ y : EuclideanSpace ℝ (Fin 3), |Work.BoseFixR.W1fun v h ℓ y|) :=
  chBimg_far_tail_core hR hℓ hRℓ hΛ hCd hv_supp hdec
    (W1funFarIntegrable hR hℓ hRℓ hv_supp) latVec_far_tail_sum hx

end Work.BoseBoxFock.PCFU
