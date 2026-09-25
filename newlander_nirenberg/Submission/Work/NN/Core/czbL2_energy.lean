import Mathlib
import Submission.Work.NN.Core.czB_L2_defs
import Submission.Work.NN.Core.integral_normSq_dCoord_eq_dbarCoord_of_contDiff
import Submission.Work.CR.Flat.integral_mul_dbarCoord_eq_neg
import Submission.Work.NN.Core.bmPotential_dCoord_eq
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmPotential_iteratedFDeriv
import Submission.Work.CR.Flat.Cauchy.bmPot_dbarCoord
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dCoord
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_bmDzKernel_sub_le
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_bmDbarKernel_sub_le
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dbarCoord
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_fderiv_le_sum_wirtinger
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_fderiv_sub_le_sum_wirtinger
import Submission.Work.CR.Flat.Cauchy.bmCz.dCoord_bmKernel
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.bmCz.hasFDerivAt_bmKernel
import Submission.Work.NN.Core.bmPotential_holder
import Submission.Work.CR.Flat.Cauchy.bmDzKernel_cz_bound
import Submission.Work.NN.Core.czB_L2_aux
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dCoord

set_option maxHeartbeats 800000

namespace Work.NN.Core

open MeasureTheory
open Work.CR.Flat.Cauchy


/-- Rewriting helper: `x ^ (-(m:ℝ)) = (x ^ m)⁻¹` for `x ≥ 0` and `m : ℕ`. -/
private lemma rpow_neg_nat_eq_inv {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    x ^ (-(m : ℝ)) = ((x ^ m : ℝ))⁻¹ := by
  rw [Real.rpow_neg hx, Real.rpow_natCast]

/-- **Pointwise bound for the derivative of the Bochner–Martinelli kernel.**  For `y ≠ 0`,
`‖fderiv ℝ (bmKernel j) y‖ ≤ C ‖y‖^{-2n}` (Euclidean norm), uniformly in `j`. -/
lemma exists_norm_fderiv_bmKernel_le {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Fin n) (y : Fin n → ℂ), y ≠ 0 →
      ‖fderiv ℝ (bmKernel j) y‖
        ≤ C * (eucNorm y) ^ (-(2 * (n : ℝ))) := by
  refine ⟨2 * (n : ℝ) * (2 * (n : ℝ) + 1), by positivity, ?_⟩
  intro j y hy
  have hE : 0 < eucNorm y := eucNorm_pos hy
  have hrw : (eucNorm y) ^ (-(2 * (n : ℝ))) = ((eucNorm y) ^ (2 * n))⁻¹ := by
    have h : (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) := by push_cast; ring
    rw [h, rpow_neg_nat_eq_inv (le_of_lt hE)]
  have hterm : ∀ k : Fin n,
      ‖Work.CR.Flat.dCoord k (fun y => bmKernel j y) y‖
        + ‖Work.CR.Flat.dbarCoord k (fun y => bmKernel j y) y‖
      ≤ (2 * (n : ℝ) + 1) * (eucNorm y) ^ (-(2 * (n : ℝ))) := by
    intro k
    rw [bmCz.dCoord_bmKernel hy, bmCz.dbarCoord_bmKernel hy, hrw]
    have h1 := BmDzCzAux.norm_bmDzKernel_le k j hy
    have h2 := bmCz.norm_bmDbarKernel_le k j hy
    rw [div_eq_mul_inv] at h1 h2
    calc ‖bmDzKernel k j y‖ + ‖bmDbarKernel k j y‖
        ≤ (n : ℝ) * ((eucNorm y) ^ (2 * n))⁻¹
            + ((n : ℝ) + 1) * ((eucNorm y) ^ (2 * n))⁻¹ := add_le_add h1 h2
      _ = (2 * (n : ℝ) + 1) * ((eucNorm y) ^ (2 * n))⁻¹ := by ring
  calc ‖fderiv ℝ (fun y => bmKernel j y) y‖
      ≤ 2 * ∑ k : Fin n, (‖Work.CR.Flat.dCoord k (fun y => bmKernel j y) y‖
          + ‖Work.CR.Flat.dbarCoord k (fun y => bmKernel j y) y‖) :=
        bmCz.norm_fderiv_le_sum_wirtinger _ _
    _ ≤ 2 * ∑ _k : Fin n, (2 * (n : ℝ) + 1) * (eucNorm y) ^ (-(2 * (n : ℝ))) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hterm k) (by norm_num)
    _ = 2 * (n : ℝ) * (2 * (n : ℝ) + 1) * (eucNorm y) ^ (-(2 * (n : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- **Lipschitz bound for the derivative of the Bochner–Martinelli kernel.**
For `2‖h‖ ≤ ‖x‖` (Euclidean norms), `‖fderiv (bmKernel j) (x-h) - fderiv (bmKernel j) x‖ ≤
C ‖h‖ ‖x‖^{-(2n+1)}`, uniformly in `j`. -/
lemma exists_norm_fderiv_sub_bmKernel_le {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Fin n) (x h : Fin n → ℂ), x ≠ 0 →
      2 * eucNorm h ≤ eucNorm x →
      ‖fderiv ℝ (bmKernel j) (x - h) - fderiv ℝ (bmKernel j) x‖
        ≤ C * eucNorm h * (eucNorm x) ^ (-(2 * (n : ℝ) + 1)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := bmCz.norm_bmDzKernel_sub_le hn
  obtain ⟨C₂, hC₂pos, hC₂⟩ := bmCz.norm_bmDbarKernel_sub_le hn
  refine ⟨2 * (n : ℝ) * (C₁ + C₂), by positivity, ?_⟩
  intro j x h hx hh
  have hE : 0 < eucNorm x := eucNorm_pos hx
  have hsub : x - h ≠ 0 := by
    intro h0
    have h1 : eucNorm h = eucNorm x := by
      have h2 : h = x := by
        have := sub_eq_zero.mp h0
        exact this.symm
      rw [h2]
    rw [h1] at hh
    linarith
  have hpow : (eucNorm x) ^ (-(2 * (n : ℝ) + 1)) = ((eucNorm x) ^ (2 * n + 1))⁻¹ := by
    have h : (2 * (n : ℝ) + 1) = ((2 * n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [h, rpow_neg_nat_eq_inv (le_of_lt hE)]
  have hterm : ∀ k : Fin n,
      ‖Work.CR.Flat.dCoord k (fun y => bmKernel j y) (x - h)
          - Work.CR.Flat.dCoord k (fun y => bmKernel j y) x‖
        + ‖Work.CR.Flat.dbarCoord k (fun y => bmKernel j y) (x - h)
          - Work.CR.Flat.dbarCoord k (fun y => bmKernel j y) x‖
      ≤ (C₁ + C₂) * eucNorm h * (eucNorm x) ^ (-(2 * (n : ℝ) + 1)) := by
    intro k
    rw [bmCz.dCoord_bmKernel hsub, bmCz.dCoord_bmKernel hx,
      bmCz.dbarCoord_bmKernel hsub, bmCz.dbarCoord_bmKernel hx]
    have h2 := hC₁ k j x h hh
    have h3 := hC₂ k j x h hh
    have h3' : ‖bmDbarKernel k j (x - h) - bmDbarKernel k j x‖
        ≤ C₂ * eucNorm h * (eucNorm x) ^ (-(2 * (n : ℝ) + 1)) := by
      rw [div_eq_mul_inv] at h3
      rw [hpow]
      exact h3
    calc ‖bmDzKernel k j (x - h) - bmDzKernel k j x‖
          + ‖bmDbarKernel k j (x - h) - bmDbarKernel k j x‖
        ≤ C₁ * eucNorm h * (eucNorm x) ^ (-(2 * (n : ℝ) + 1))
          + C₂ * eucNorm h * (eucNorm x) ^ (-(2 * (n : ℝ) + 1)) := add_le_add h2 h3'
      _ = (C₁ + C₂) * eucNorm h * (eucNorm x) ^ (-(2 * (n : ℝ) + 1)) := by ring
  calc ‖fderiv ℝ (fun y => bmKernel j y) (x - h) - fderiv ℝ (fun y => bmKernel j y) x‖
      ≤ 2 * ∑ k : Fin n, (‖Work.CR.Flat.dCoord k (fun y => bmKernel j y) (x - h)
            - Work.CR.Flat.dCoord k (fun y => bmKernel j y) x‖
          + ‖Work.CR.Flat.dbarCoord k (fun y => bmKernel j y) (x - h)
            - Work.CR.Flat.dbarCoord k (fun y => bmKernel j y) x‖) :=
        bmCz.norm_fderiv_sub_le_sum_wirtinger _ _ _
    _ ≤ 2 * ∑ _k : Fin n, (C₁ + C₂) * eucNorm h * (eucNorm x) ^ (-(2 * (n : ℝ) + 1)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hterm k) (by norm_num)
    _ = 2 * (n : ℝ) * (C₁ + C₂) * eucNorm h * (eucNorm x) ^ (-(2 * (n : ℝ) + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring


/-- `(3/4 * z) ^ (-p) = (4/3) ^ p * z ^ (-p)` for `z > 0`. -/
private lemma rpow_neg_three_quarter {z p : ℝ} (hz : 0 < z) :
    ((3:ℝ) / 4 * z) ^ (-p) = ((4:ℝ) / 3) ^ p * z ^ (-p) := by
  rw [Real.mul_rpow (by norm_num) hz.le, Real.rpow_neg (by norm_num),
    show ((3:ℝ) / 4) = ((4:ℝ) / 3)⁻¹ by norm_num, Real.inv_rpow (by norm_num),
    Real.rpow_neg hz.le, inv_inv]

/-- **Decay of the Bochner–Martinelli potential of mean-zero data.** -/
lemma bmPotential_decay_zero_mean {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, MeasureTheory.Integrable (w j)) →
      (∀ j, Continuous (w j)) →
      (∀ j x, R ≤ eucNorm x → w j x = 0) →
      (∀ j, ∫ x, w j x = 0) →
      ∀ z : Fin n → ℂ, 4 * R ≤ ‖z‖ →
        ‖bmPotential w z‖ ≤ C * (∑ j, ∫ x, ‖w j x‖) * ‖z‖ ^ (-(2 * (n : ℝ))) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := exists_norm_fderiv_bmKernel_le (n := n) hn
  refine ⟨C₀ * ((4:ℝ) / 3) ^ (2 * (n : ℝ)) * R, by positivity, ?_⟩
  intro w hwint hwcont hwsup hwzero z hz
  have hzpos : 0 < ‖z‖ := by linarith
  have hcs : ∀ j, HasCompactSupport (w j) := fun j => hasCompactSupport_of_eucNorm (hwsup j)
  -- the shifted data
  have hshiftfun : ∀ j : Fin n, (fun x : Fin n → ℂ => w j (z + x)) = fun x => w j (x + z) :=
    fun j => by funext x; rw [add_comm]
  have hshift : ∀ j : Fin n, ∫ x, w j (z + x) = 0 := by
    intro j
    rw [hshiftfun j, MeasureTheory.integral_add_right_eq_self (μ := volume) (fun y => w j y) z]
    exact hwzero j
  have hint : ∀ j : Fin n, Integrable (fun x => w j (z + x)) := fun j =>
    ((hwcont j).comp (continuous_const.add continuous_id)).integrable_of_hasCompactSupport
      ((hcs j).comp_homeomorph (Homeomorph.addLeft z))
  have hintnorm : ∀ j : Fin n, Integrable (fun x => ‖w j (z + x)‖) := fun j => (hint j).norm
  have hshiftnorm : ∀ j : Fin n, ∫ x, ‖w j (z + x)‖ = ∫ x, ‖w j x‖ := by
    intro j
    rw [show (fun x : Fin n → ℂ => ‖w j (z + x)‖) = fun x => (fun y => ‖w j y‖) (x + z) from
      by funext x; rw [add_comm]]
    exact MeasureTheory.integral_add_right_eq_self (μ := volume) (fun y => ‖w j y‖) z
  -- geometry on the ball
  have hball : ∀ y : Fin n → ℂ, y ∈ Metric.closedBall (-z) R → (3:ℝ) / 4 * ‖z‖ ≤ ‖y‖ := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    have h1 : ‖(-z : Fin n → ℂ)‖ ≤ ‖-z - y‖ + ‖y‖ := by
      have h := norm_add_le (-z - y) y
      rwa [sub_add_cancel] at h
    have h2 : ‖-z - y‖ = ‖y - (-z)‖ := norm_sub_rev _ _
    rw [norm_neg, h2] at h1
    linarith
  -- the derivative bound on the ball
  have hM : ∀ j : Fin n, ∀ y ∈ Metric.closedBall (-z) R,
      ‖fderiv ℝ (bmKernel j) y‖
        ≤ C₀ * ((4:ℝ) / 3) ^ (2 * (n : ℝ)) * ‖z‖ ^ (-(2 * (n : ℝ))) := by
    intro j y hy
    have hy1 := hball y hy
    have hypos : 0 < ‖y‖ := by linarith [hzpos, hR]
    have hE : 0 < eucNorm y := lt_of_lt_of_le hypos (pi_norm_le_eucNorm y)
    have hyne : y ≠ 0 := fun h => by rw [h, eucNorm_zero] at hE; linarith
    have h1 : eucNorm y ^ (-(2 * (n : ℝ))) ≤ ((3:ℝ)/4 * ‖z‖) ^ (-(2 * (n : ℝ))) :=
      Real.rpow_le_rpow_of_nonpos (by positivity)
        (le_trans hy1 (pi_norm_le_eucNorm y)) (by linarith)
    have h2 : ((3:ℝ)/4 * ‖z‖) ^ (-(2 * (n : ℝ)))
        = ((4:ℝ)/3) ^ (2 * (n : ℝ)) * ‖z‖ ^ (-(2 * (n : ℝ))) :=
      rpow_neg_three_quarter (p := 2 * (n : ℝ)) hzpos
    calc ‖fderiv ℝ (bmKernel j) y‖ ≤ C₀ * eucNorm y ^ (-(2 * (n : ℝ))) := hC₀ j y hyne
      _ ≤ C₀ * ((3:ℝ)/4 * ‖z‖) ^ (-(2 * (n : ℝ))) := mul_le_mul_of_nonneg_left h1 hC₀pos.le
      _ = C₀ * ((4:ℝ)/3) ^ (2 * (n : ℝ)) * ‖z‖ ^ (-(2 * (n : ℝ))) := by rw [h2, mul_assoc]
  have hyne : ∀ y : Fin n → ℂ, y ∈ Metric.closedBall (-z) R → y ≠ 0 := by
    intro y hy
    have h1 := hball y hy
    have h2 : 0 < ‖y‖ := by linarith [hzpos, hR]
    exact fun h => by rw [h, norm_zero] at h2; linarith
  -- the kernel difference bound
  have hKdiff : ∀ j : Fin n, ∀ x : Fin n → ℂ, eucNorm (z + x) ≤ R →
      ‖bmKernel j x - bmKernel j (-z)‖
        ≤ C₀ * ((4:ℝ) / 3) ^ (2 * (n : ℝ)) * ‖z‖ ^ (-(2 * (n : ℝ))) * R := by
    intro j x hxR
    have hxmem : x ∈ Metric.closedBall (-z) R := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      rw [show x - -z = x + z from by abel]
      exact le_trans (pi_norm_le_eucNorm _) (by rw [add_comm]; exact hxR)
    have hzmem : (-z) ∈ Metric.closedBall (-z) R := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      rw [show (-z : Fin n → ℂ) - -z = 0 from by abel, norm_zero]
      exact hR.le
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := fun y : Fin n → ℂ => bmKernel j y)
      (s := Metric.closedBall (-z) R)
      (C := C₀ * ((4:ℝ) / 3) ^ (2 * (n : ℝ)) * ‖z‖ ^ (-(2 * (n : ℝ))))
      (fun y hy => (bmCz.hasFDerivAt_bmKernel j (hyne y hy)).differentiableAt)
      (hM j) (convex_closedBall _ _) hzmem hxmem
    refine hmv.trans ?_
    have hxd : ‖x - (-z)‖ ≤ R := by
      rw [show x - -z = x + z from by abel]
      exact le_trans (pi_norm_le_eucNorm _) (by rw [add_comm]; exact hxR)
    have hMnn : 0 ≤ C₀ * ((4:ℝ) / 3) ^ (2 * (n : ℝ)) * ‖z‖ ^ (-(2 * (n : ℝ))) := by positivity
    calc _ ≤ (C₀ * ((4:ℝ)/3)^(2*(n:ℝ)) * ‖z‖^(-(2*(n:ℝ)))) * R :=
          mul_le_mul_of_nonneg_left hxd hMnn
      _ = _ := by ring
  -- integrability of the two pieces
  have hIntA : ∀ j : Fin n, Integrable (fun x => bmKernel j x * w j (z + x)) := fun j =>
    integrable_bmKernel_mul hn j ((hwcont j).comp (continuous_const.add continuous_id))
      ((hcs j).comp_homeomorph (Homeomorph.addLeft z))
  have hIntB : ∀ j : Fin n, Integrable (fun x => bmKernel j (-z) * w j (z + x)) := fun j =>
    (hint j).const_mul _
  have hmeanzero : ∀ j : Fin n, ∫ x, bmKernel j x * w j (z + x)
      = ∫ x, (bmKernel j x - bmKernel j (-z)) * w j (z + x) := by
    intro j
    rw [show (fun x : Fin n → ℂ => (bmKernel j x - bmKernel j (-z)) * w j (z + x))
        = fun x => bmKernel j x * w j (z + x) - bmKernel j (-z) * w j (z + x) from
      by funext x; ring]
    rw [MeasureTheory.integral_sub (hIntA j) (hIntB j), MeasureTheory.integral_const_mul,
      hshift j, mul_zero, sub_zero]
  -- the bound for one component
  have hbound : ∀ j : Fin n,
      ‖∫ x, (bmKernel j x - bmKernel j (-z)) * w j (z + x)‖
        ≤ (C₀ * ((4:ℝ) / 3) ^ (2 * (n : ℝ)) * ‖z‖ ^ (-(2 * (n : ℝ))) * R)
            * ∫ x, ‖w j x‖ := by
    intro j
    calc ‖∫ x, (bmKernel j x - bmKernel j (-z)) * w j (z + x)‖
        ≤ ∫ x, ‖(bmKernel j x - bmKernel j (-z)) * w j (z + x)‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ x, ‖bmKernel j x - bmKernel j (-z)‖ * ‖w j (z + x)‖ := by simp_rw [norm_mul]
      _ ≤ ∫ x, (C₀ * ((4:ℝ)/3)^(2*(n:ℝ)) * ‖z‖^(-(2*(n:ℝ))) * R) * ‖w j (z + x)‖ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
            ((hintnorm j).const_mul _) (Filter.Eventually.of_forall fun x => ?_)
          by_cases hx : w j (z + x) = 0
          · simp [hx]
          · have hxR : eucNorm (z + x) ≤ R := by
              by_contra hcon
              push Not at hcon
              exact hx (hwsup j (z + x) hcon.le)
            exact mul_le_mul_of_nonneg_right (hKdiff j x hxR) (norm_nonneg _)
      _ = (C₀ * ((4:ℝ)/3)^(2*(n:ℝ)) * ‖z‖^(-(2*(n:ℝ))) * R) * ∫ x, ‖w j (z + x)‖ :=
          MeasureTheory.integral_const_mul _ _
      _ = (C₀ * ((4:ℝ)/3)^(2*(n:ℝ)) * ‖z‖^(-(2*(n:ℝ))) * R) * ∫ x, ‖w j x‖ := by
          rw [hshiftnorm j]
  rw [bmPotential_eq_bmPot, bmPot]
  calc ‖∑ j, ∫ x, bmKernel j x * w j (z + x)‖
      ≤ ∑ j, ‖∫ x, bmKernel j x * w j (z + x)‖ := norm_sum_le _ _
    _ = ∑ j, ‖∫ x, (bmKernel j x - bmKernel j (-z)) * w j (z + x)‖ :=
        Finset.sum_congr rfl fun j _ => by rw [hmeanzero j]
    _ ≤ ∑ j, (C₀ * ((4:ℝ)/3)^(2*(n:ℝ)) * ‖z‖^(-(2*(n:ℝ))) * R) * ∫ x, ‖w j x‖ :=
        Finset.sum_le_sum fun j _ => hbound j
    _ = ((C₀ * ((4:ℝ)/3)^(2*(n:ℝ)) * R) * (∑ j, ∫ x, ‖w j x‖))
          * ‖z‖ ^ (-(2 * (n : ℝ))) := by
        have h1 : (∑ j : Fin n,
              (C₀ * ((4:ℝ)/3)^(2*(n:ℝ)) * ‖z‖ ^ (-(2*(n:ℝ))) * R) * ∫ x, ‖w j x‖)
            = (C₀ * ((4:ℝ)/3)^(2*(n:ℝ)) * ‖z‖ ^ (-(2*(n:ℝ))) * R)
                * (∑ j, ∫ x, ‖w j x‖) :=
          (Finset.mul_sum Finset.univ (fun j : Fin n => ∫ x, ‖w j x‖)
            (C₀ * ((4:ℝ)/3)^(2*(n:ℝ)) * ‖z‖ ^ (-(2*(n:ℝ))) * R)).symm
        rw [h1]
        ring


/-- Decomposition of a real-linear map on `ℂⁿ` along the real basis. -/
private lemma linearMap_decompose {n : ℕ} (L : (Fin n → ℂ) →L[ℝ] ℂ) (y : Fin n → ℂ) :
    L y = ∑ p : Fin n, ((y p).re * L (Pi.single p (1 : ℂ))
        + (y p).im * L (Pi.single p Complex.I)) := by
  conv_lhs => rw [show y = ∑ p : Fin n, ((y p).re • (Pi.single p (1 : ℂ) : Fin n → ℂ)
      + (y p).im • (Pi.single p Complex.I : Fin n → ℂ)) from by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same]
      apply Complex.ext <;> simp
    · intro k _ hk
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hk),
        Pi.single_eq_of_ne (Ne.symm hk)]
      simp
    · intro hj; exact absurd (Finset.mem_univ j) hj]
  rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_add, map_smul, map_smul, ← Complex.real_smul, ← Complex.real_smul]

/-- Wirtinger decomposition of a real-linear map on `ℂⁿ`:
`L y = Σ_p (a_p y_p + b_p conj y_p)`. -/
private lemma linearMap_decompose_conj {n : ℕ} (L : (Fin n → ℂ) →L[ℝ] ℂ) (y : Fin n → ℂ) :
    L y = ∑ p : Fin n, (((L (Pi.single p (1 : ℂ)) - Complex.I * L (Pi.single p Complex.I)) / 2)
        * (y p)
      + ((L (Pi.single p (1 : ℂ)) + Complex.I * L (Pi.single p Complex.I)) / 2) * star (y p)) := by
  rw [linearMap_decompose L y]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h1 : ((y p : ℂ)) + star (y p) = 2 * (((y p).re : ℝ) : ℂ) := by
    rw [show (star (y p) : ℂ) = starRingEnd ℂ (y p) from rfl, Complex.add_conj]
    push_cast; ring
  have h2 : ((y p : ℂ)) - star (y p) = 2 * (((y p).im : ℝ) : ℂ) * Complex.I := by
    rw [show (star (y p) : ℂ) = starRingEnd ℂ (y p) from rfl, Complex.sub_conj]
    push_cast; ring
  have hre : (((y p).re : ℝ) : ℂ) = ((y p) + star (y p)) / 2 := by rw [h1]; ring
  have him : (((y p).im : ℝ) : ℂ) = (star (y p) - (y p)) * Complex.I / 2 := by
    rw [show star (y p) - (y p) = -(2 * (((y p).im : ℝ) : ℂ) * Complex.I) from by
      rw [← h2]; ring]
    field_simp
    rw [Complex.I_sq]
    ring
  rw [hre, him]
  ring

/-- The product of any function with a compactly supported one has compact support. -/
private lemma hasCompactSupport_mul_of {n : ℕ} {f g : (Fin n → ℂ) → ℂ}
    (hg : HasCompactSupport g) : HasCompactSupport (fun y => f y * g y) := by
  refine IsCompact.of_isClosed_subset hg (isClosed_tsupport _) ?_
  rw [tsupport]
  refine closure_minimal ?_ (isClosed_tsupport g)
  intro y hy
  refine subset_tsupport g ?_
  rw [Function.mem_support] at hy ⊢
  intro h
  exact hy (by rw [h, mul_zero])

/-- **Fast decay of the Bochner–Martinelli potential of data with two vanishing moments.** -/
lemma bmPotential_decay_two_moments {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, MeasureTheory.Integrable (w j)) →
      (∀ j, Continuous (w j)) →
      (∀ j x, R ≤ eucNorm x → w j x = 0) →
      (∀ j, ∫ x, w j x = 0) →
      (∀ j p, ∫ x, x p * w j x = 0) →
      (∀ j p, ∫ x, star (x p) * w j x = 0) →
      ∀ z : Fin n → ℂ, (4 * Real.sqrt n + 4) * R ≤ ‖z‖ →
        ‖bmPotential w z‖ ≤ C * (∑ j, ∫ x, ‖w j x‖) * ‖z‖ ^ (-(2 * (n : ℝ) + 1)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := exists_norm_fderiv_sub_bmKernel_le (n := n) hn
  refine ⟨C₀ * Real.sqrt n * R ^ 2, by positivity, ?_⟩
  intro w hwint hwcont hwsup hwzero hmom hmomC z hz
  set K : ℝ := C₀ * Real.sqrt n * R * ‖z‖ ^ (-(2 * (n : ℝ) + 1)) * R with hK
  have hs : (0:ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg n
  have hzpos : 0 < ‖z‖ := by nlinarith
  have hcs : ∀ j, HasCompactSupport (w j) := fun j => hasCompactSupport_of_eucNorm (hwsup j)
  have hcs_shift : ∀ j, HasCompactSupport (fun x => w j (z + x)) :=
    fun j => (hcs j).comp_homeomorph (Homeomorph.addLeft z)
  have hcont_shift : ∀ j, Continuous (fun x => w j (z + x)) :=
    fun j => (hwcont j).comp (continuous_const.add continuous_id)
  have hIntShift : ∀ (j : Fin n) (f : (Fin n → ℂ) → ℂ), Continuous f →
      Integrable (fun x => f x * w j (z + x)) := fun j f hf =>
    (hf.mul (hcont_shift j)).integrable_of_hasCompactSupport (hasCompactSupport_mul_of (hcs_shift j))
  have hIntShiftOne : ∀ j : Fin n, Integrable (fun x => w j (z + x)) := fun j => by
    simpa using hIntShift j (fun _ => (1:ℂ)) continuous_const
  have hIntShiftNorm : ∀ j : Fin n, Integrable (fun x => ‖w j (z + x)‖) := fun j =>
    (hIntShiftOne j).norm
  -- the shifted moment integrals vanish
  have hshiftW : ∀ j : Fin n, ∫ x, w j (z + x) = 0 := by
    intro j
    rw [show (fun x : Fin n → ℂ => w j (z + x)) = (fun x => w j (x + z)) from by
      funext x; rw [add_comm]]
    rw [MeasureTheory.integral_add_right_eq_self (μ := volume)]
    exact hwzero j
  have hshiftP : ∀ (j p : Fin n), ∫ x, (x + z) p * w j (z + x) = 0 := by
    intro j p
    rw [show (fun x : Fin n → ℂ => (x + z) p * w j (z + x))
        = (fun x => (x + z) p * w j (x + z)) from by funext x; rw [add_comm]]
    rw [MeasureTheory.integral_add_right_eq_self (μ := volume) (fun y => y p * w j y) z]
    exact hmom j p
  have hshiftC : ∀ (j p : Fin n), ∫ x, star ((x + z) p) * w j (z + x) = 0 := by
    intro j p
    rw [show (fun x : Fin n → ℂ => star ((x + z) p) * w j (z + x))
        = (fun x => star ((x + z) p) * w j (x + z)) from by funext x; rw [add_comm]]
    rw [MeasureTheory.integral_add_right_eq_self (μ := volume) (fun y => star (y p) * w j y) z]
    exact hmomC j p
  -- the linear term integrates to zero
  have hLzero : ∀ (j : Fin n) (L : (Fin n → ℂ) →L[ℝ] ℂ),
      ∫ x, L (x + z) * w j (z + x) = 0 := by
    intro j L
    have hpt : ∀ x : Fin n → ℂ, L (x + z) * w j (z + x) = ∑ p : Fin n,
        (((L (Pi.single p (1 : ℂ)) - Complex.I * L (Pi.single p Complex.I)) / 2)
            * ((x + z) p * w j (z + x))
          + ((L (Pi.single p (1 : ℂ)) + Complex.I * L (Pi.single p Complex.I)) / 2)
            * (star ((x + z) p) * w j (z + x))) := by
      intro x
      have hdec := linearMap_decompose_conj L (x + z)
      rw [hdec, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    have hcont1 : ∀ p : Fin n, Continuous (fun x : Fin n → ℂ => (x + z) p) := by
      intro p
      have h : (fun x : Fin n → ℂ => (x + z) p) = fun x => x p + z p := by
        funext x; simp
      rw [h]; exact (continuous_apply p).add continuous_const
    have hcont2 : ∀ p : Fin n, Continuous (fun x : Fin n → ℂ => star ((x + z) p)) := fun p =>
      continuous_star.comp (hcont1 p)
    have h1 : ∀ p : Fin n, Integrable (fun x : Fin n → ℂ =>
        ((L (Pi.single p (1 : ℂ)) - Complex.I * L (Pi.single p Complex.I)) / 2)
          * ((x + z) p * w j (z + x))) := fun p => (hIntShift j _ (hcont1 p)).const_mul _
    have h2 : ∀ p : Fin n, Integrable (fun x : Fin n → ℂ =>
        ((L (Pi.single p (1 : ℂ)) + Complex.I * L (Pi.single p Complex.I)) / 2)
          * (star ((x + z) p) * w j (z + x))) := fun p => (hIntShift j _ (hcont2 p)).const_mul _
    rw [funext hpt, MeasureTheory.integral_finsetSum]
    · refine Finset.sum_eq_zero fun p _ => ?_
      rw [MeasureTheory.integral_add (h1 p) (h2 p), MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, hshiftP j p, hshiftC j p]
      ring
    · intro p _
      exact (h1 p).add (h2 p)
  -- geometry
  have hzon : 0 < eucNorm z := lt_of_lt_of_le hzpos (pi_norm_le_eucNorm z)
  have hzR : 4 * R ≤ ‖z‖ := by nlinarith
  have hball : ∀ u : Fin n → ℂ, u ∈ Metric.closedBall (-z) R → u ≠ 0 := by
    intro u hu h0
    rw [Metric.mem_closedBall, dist_eq_norm] at hu
    rw [h0] at hu
    simp only [zero_sub, norm_neg] at hu
    linarith
  -- the second-order Taylor bound
  have hMVI : ∀ j : Fin n, ∀ x : Fin n → ℂ, eucNorm (z + x) ≤ R →
      ‖bmKernel j x - bmKernel j (-z) - fderiv ℝ (bmKernel j) (-z) (x + z)‖ ≤ K := by
    intro j x hxR
    set L : (Fin n → ℂ) →L[ℝ] ℂ := fderiv ℝ (bmKernel j) (-z) with hL
    set ψ : (Fin n → ℂ) → ℂ := fun u => bmKernel j u - L (u + z) with hψ
    have hxmem : x ∈ Metric.closedBall (-z) R := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      rw [show x - -z = x + z from by abel]
      exact le_trans (pi_norm_le_eucNorm _) (by rw [add_comm]; exact hxR)
    have hzmem : (-z) ∈ Metric.closedBall (-z) R := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      rw [show (-z : Fin n → ℂ) - -z = 0 from by abel, norm_zero]
      exact hR.le
    have hzne : (-z : Fin n → ℂ) ≠ 0 := by
      intro h0
      have h1 : eucNorm z = 0 := by rw [← eucNorm_neg, h0, eucNorm_zero]
      linarith
    have hchain : ∀ u ∈ Metric.closedBall (-z) R,
        HasFDerivAt (fun u : Fin n → ℂ => bmKernel j u) (fderiv ℝ (bmKernel j) u) u := by
      intro u hu
      have h := bmCz.hasFDerivAt_bmKernel j (hball u hu)
      rw [← h.fderiv] at h
      exact h
    have hderiv : ∀ u ∈ Metric.closedBall (-z) R, fderiv ℝ ψ u = fderiv ℝ (bmKernel j) u - L := by
      intro u hu
      have hA : HasFDerivAt (fun u : Fin n → ℂ => L (u + z)) L u := by
        have h1 : (fun u : Fin n → ℂ => L (u + z)) = fun u => L u + L z := by
          funext u; rw [map_add]
        rw [h1]
        exact (ContinuousLinearMap.hasFDerivAt L).add_const (L z)
      exact ((hchain u hu).sub hA).fderiv
    have hbound : ∀ u ∈ Metric.closedBall (-z) R,
        ‖fderiv ℝ (bmKernel j) u - L‖ ≤ C₀ * Real.sqrt n * R * ‖z‖ ^ (-(2 * (n : ℝ) + 1)) := by
      intro u hu
      have hu1 : ‖u + z‖ ≤ R := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hu
        rw [show u - -z = u + z from by abel] at hu
        exact hu
      have h1 : 2 * eucNorm (-(u + z)) ≤ eucNorm (-z) := by
        rw [eucNorm_neg, eucNorm_neg]
        have h2 : eucNorm (u + z) ≤ Real.sqrt n * R :=
          le_trans (bmCz.eucNorm_le_sqrt_mul_norm _) (mul_le_mul_of_nonneg_left hu1 hs)
        have h3 : eucNorm z ≥ ‖z‖ := pi_norm_le_eucNorm z
        nlinarith [h2, h3, hz, hs, hR]
      have h2 := hC₀ j (-z) (-(u + z)) hzne h1
      have h3 : (-z : Fin n → ℂ) - (-(u + z)) = u := by abel
      rw [h3, eucNorm_neg, eucNorm_neg] at h2
      have h4 : eucNorm (u + z) ≤ Real.sqrt n * R :=
        le_trans (bmCz.eucNorm_le_sqrt_mul_norm _) (mul_le_mul_of_nonneg_left hu1 hs)
      have h5 : (eucNorm z) ^ (-(2 * (n : ℝ) + 1)) ≤ ‖z‖ ^ (-(2 * (n : ℝ) + 1)) :=
        Real.rpow_le_rpow_of_nonpos hzpos (pi_norm_le_eucNorm z) (by linarith)
      calc ‖fderiv ℝ (bmKernel j) u - L‖
          = ‖fderiv ℝ (bmKernel j) u - fderiv ℝ (bmKernel j) (-z)‖ := by rw [hL]
        _ ≤ C₀ * eucNorm (u + z) * eucNorm z ^ (-(2 * (n : ℝ) + 1)) := h2
        _ ≤ C₀ * (Real.sqrt n * R) * ‖z‖ ^ (-(2 * (n : ℝ) + 1)) := by
            refine le_trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h4 hC₀pos.le) (Real.rpow_nonneg hzon.le _)) ?_
            refine mul_le_mul_of_nonneg_left h5 ?_
            positivity
        _ = C₀ * Real.sqrt n * R * ‖z‖ ^ (-(2 * (n : ℝ) + 1)) := by ring
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := ψ) (s := Metric.closedBall (-z) R)
      (C := C₀ * Real.sqrt n * R * ‖z‖ ^ (-(2 * (n : ℝ) + 1)))
      (fun u hu => ((hchain u hu).sub (by
        rw [show (fun u : Fin n → ℂ => L (u + z)) = fun u => L u + L z from by
          funext u; rw [map_add]]
        exact (ContinuousLinearMap.hasFDerivAt L).add_const (L z))).differentiableAt)
      (fun u hu => by rw [hderiv u hu]; exact hbound u hu)
      (convex_closedBall _ _) hzmem hxmem
    have hval : ψ x - ψ (-z) = bmKernel j x - bmKernel j (-z) - L (x + z) := by
      simp only [hψ]
      rw [neg_add_cancel, map_zero]
      ring
    rw [hval] at hmv
    have hxd : ‖x - (-z)‖ ≤ R := by
      rw [show x - -z = x + z from by abel]
      exact le_trans (pi_norm_le_eucNorm _) (by rw [add_comm]; exact hxR)
    have hCnn : 0 ≤ C₀ * Real.sqrt n * R * ‖z‖ ^ (-(2 * (n : ℝ) + 1)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hC₀pos.le hs) hR.le) (Real.rpow_nonneg hzpos.le _)
    refine hmv.trans ?_
    calc C₀ * Real.sqrt n * R * ‖z‖ ^ (-(2 * (n : ℝ) + 1)) * ‖x - -z‖
        ≤ C₀ * Real.sqrt n * R * ‖z‖ ^ (-(2 * (n : ℝ) + 1)) * R :=
          mul_le_mul_of_nonneg_left hxd hCnn
      _ = K := by rw [hK]
  -- the Taylor identity for each component
  have hTaylor : ∀ j : Fin n, ∫ x, bmKernel j x * w j (z + x)
      = ∫ x, (bmKernel j x - bmKernel j (-z) - fderiv ℝ (bmKernel j) (-z) (x + z))
          * w j (z + x) := by
    intro j
    have hIntB : Integrable (fun x => (bmKernel j x - bmKernel j (-z)
        - fderiv ℝ (bmKernel j) (-z) (x + z)) * w j (z + x)) := by
      refine Integrable.mono' ((hIntShiftNorm j).const_mul K) ?_ ?_
      · refine (((measurable_bmKernel j).sub measurable_const).sub
          (((fderiv ℝ (bmKernel j) (-z)).continuous.comp
            (continuous_id.add continuous_const)).measurable)).mul
          (hcont_shift j).measurable |>.aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun x => ?_
        rw [norm_mul]
        by_cases hx : w j (z + x) = 0
        · simp [hx]
        · have hxR : eucNorm (z + x) ≤ R := by
            by_contra hcon
            push Not at hcon
            exact hx (hwsup j (z + x) hcon.le)
          exact mul_le_mul_of_nonneg_right (hMVI j x hxR) (norm_nonneg _)
    have hIntL : Integrable (fun x : Fin n → ℂ =>
        fderiv ℝ (bmKernel j) (-z) (x + z) * w j (z + x)) :=
      hIntShift j _ ((fderiv ℝ (bmKernel j) (-z)).continuous.comp
        (continuous_id.add continuous_const))
    have hInt2 : Integrable (fun x => (bmKernel j (-z)
        + fderiv ℝ (bmKernel j) (-z) (x + z)) * w j (z + x)) := by
      have h2 : Integrable (fun x : Fin n → ℂ => bmKernel j (-z) * w j (z + x)
          + fderiv ℝ (bmKernel j) (-z) (x + z) * w j (z + x)) :=
        ((hIntShiftOne j).const_mul _).add hIntL
      refine h2.congr ?_
      refine Filter.Eventually.of_forall fun x => ?_
      ring
    have hrest0 : ∫ x, (bmKernel j (-z)
        + fderiv ℝ (bmKernel j) (-z) (x + z)) * w j (z + x) = 0 := by
      have hpt : ∀ x : Fin n → ℂ, (bmKernel j (-z)
          + fderiv ℝ (bmKernel j) (-z) (x + z)) * w j (z + x)
          = bmKernel j (-z) * w j (z + x)
            + fderiv ℝ (bmKernel j) (-z) (x + z) * w j (z + x) := fun x => by ring
      rw [funext hpt, MeasureTheory.integral_add ((hIntShiftOne j).const_mul _) hIntL,
        MeasureTheory.integral_const_mul, hshiftW j, mul_zero,
        hLzero j (fderiv ℝ (bmKernel j) (-z)), add_zero]
    calc ∫ x, bmKernel j x * w j (z + x)
        = ∫ x, ((bmKernel j x - bmKernel j (-z) - fderiv ℝ (bmKernel j) (-z) (x + z))
              * w j (z + x)
            + (bmKernel j (-z) + fderiv ℝ (bmKernel j) (-z) (x + z)) * w j (z + x)) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          ring
      _ = (∫ x, (bmKernel j x - bmKernel j (-z) - fderiv ℝ (bmKernel j) (-z) (x + z))
              * w j (z + x))
            + ∫ x, (bmKernel j (-z) + fderiv ℝ (bmKernel j) (-z) (x + z)) * w j (z + x) :=
          MeasureTheory.integral_add hIntB hInt2
      _ = ∫ x, (bmKernel j x - bmKernel j (-z) - fderiv ℝ (bmKernel j) (-z) (x + z))
              * w j (z + x) := by rw [hrest0, add_zero]
  -- the bound for one component
  have hbound : ∀ j : Fin n,
      ‖∫ x, (bmKernel j x - bmKernel j (-z) - fderiv ℝ (bmKernel j) (-z) (x + z))
          * w j (z + x)‖ ≤ K * ∫ y, ‖w j y‖ := by
    intro j
    have hnormshift : ∫ x, ‖w j (z + x)‖ = ∫ y, ‖w j y‖ := by
      rw [show (fun x : Fin n → ℂ => ‖w j (z + x)‖)
          = (fun x => (fun y => ‖w j y‖) (x + z)) from by funext x; rw [add_comm]]
      exact MeasureTheory.integral_add_right_eq_self (μ := volume) (fun y => ‖w j y‖) z
    calc ‖∫ x, (bmKernel j x - bmKernel j (-z) - fderiv ℝ (bmKernel j) (-z) (x + z))
            * w j (z + x)‖
        ≤ ∫ x, ‖(bmKernel j x - bmKernel j (-z) - fderiv ℝ (bmKernel j) (-z) (x + z))
            * w j (z + x)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, K * ‖w j (z + x)‖ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
            ((hIntShiftNorm j).const_mul K) (Filter.Eventually.of_forall fun x => ?_)
          simp only
          rw [norm_mul]
          by_cases hx : w j (z + x) = 0
          · simp [hx]
          · have hxR : eucNorm (z + x) ≤ R := by
              by_contra hcon
              push Not at hcon
              exact hx (hwsup j (z + x) hcon.le)
            exact mul_le_mul_of_nonneg_right (hMVI j x hxR) (norm_nonneg _)
      _ = K * ∫ x, ‖w j (z + x)‖ := MeasureTheory.integral_const_mul _ _
      _ = K * ∫ y, ‖w j y‖ := by rw [hnormshift]
  rw [bmPotential_eq_bmPot, bmPot]
  calc ‖∑ j, ∫ x, bmKernel j x * w j (z + x)‖
      ≤ ∑ j, ‖∫ x, bmKernel j x * w j (z + x)‖ := norm_sum_le _ _
    _ = ∑ j, ‖∫ x, (bmKernel j x - bmKernel j (-z) - fderiv ℝ (bmKernel j) (-z) (x + z))
            * w j (z + x)‖ := Finset.sum_congr rfl fun j _ => by rw [hTaylor j]
    _ ≤ ∑ j, K * ∫ y, ‖w j y‖ := Finset.sum_le_sum fun j _ => hbound j
    _ = (C₀ * Real.sqrt n * R ^ 2) * (∑ j, ∫ x, ‖w j x‖) * ‖z‖ ^ (-(2 * (n : ℝ) + 1)) := by
        rw [← Finset.mul_sum]
        rw [hK]
        ring

/-! ## Gluing far-field decay with boundedness on a compact set -/

/-- `(x / y) ^ p = x ^ p * y ^ (-p)` for `x, y > 0`. -/
private lemma rpow_div_mul_inv_rpow {x y p : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x / y) ^ p = x ^ p * y ^ (-p) := by
  rw [Real.div_rpow hx.le hy.le, Real.rpow_neg hy.le, div_eq_mul_inv]

private lemma one_le_div_rpow {a b p : ℝ} (hb : 0 < b) (hab : b ≤ a) (hp : 0 ≤ p) :
    (1:ℝ) ≤ (a / b) ^ p :=
  Real.one_le_rpow (by rw [one_le_div hb]; exact hab) hp

/-- **From far-field decay to a global bound.**  If a continuous function decays like
`‖z‖ ^ (-p)` for `‖z‖ ≥ 2R`, then it is bounded by `K (1 + ‖z‖) ^ (-p)` everywhere. -/
lemma bound_of_far_decay {n : ℕ} {p : ℝ} (hp : 0 < p) {R : ℝ} (hR : 0 < R)
    {f : (Fin n → ℂ) → ℂ} (hf : Continuous f) {C : ℝ}
    (hfar : ∀ z : Fin n → ℂ, 2 * R ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ (-p)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z, ‖f z‖ ≤ K * (1 + ‖z‖) ^ (-p) := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Fin n → ℂ) (2 * R)).exists_bound_of_continuousOn
    hf.continuousOn
  have h2R : (0:ℝ) < 2 * R := by linarith
  have hDpos : (0:ℝ) < 1 + 2 * R := by linarith
  have hA0 : (0:ℝ) ≤ (1 + (2*R)⁻¹) ^ p := Real.rpow_nonneg (by positivity) p
  refine ⟨(max B 0 + max C 0 * (1 + (2*R)⁻¹)^p) * (1 + 2*R)^p, ?_, ?_⟩
  · exact mul_nonneg (add_nonneg (le_max_right B 0) (mul_nonneg (le_max_right C 0) hA0))
      (Real.rpow_nonneg (by linarith) p)
  · intro z
    have hzpos : (0:ℝ) < 1 + ‖z‖ := by positivity
    rcases le_or_gt ‖z‖ (2*R) with hz | hz
    · have hBz : ‖f z‖ ≤ max B 0 :=
        le_trans (hB z (by rw [Metric.mem_closedBall, dist_zero_right]; exact hz)) (le_max_left _ _)
      have hfac : (1 + 2*R)^p * (1 + ‖z‖)^(-p) = ((1 + 2*R)/(1 + ‖z‖))^p :=
        (rpow_div_mul_inv_rpow hDpos hzpos).symm
      have h1 : (1:ℝ) ≤ (1 + 2*R)^p * (1 + ‖z‖)^(-p) := by
        rw [hfac]; exact one_le_div_rpow hzpos (by linarith) hp.le
      have hnm : (0:ℝ) ≤ max B 0 + max C 0 * (1 + (2*R)⁻¹)^p := by
        have := le_max_right B 0; linarith [mul_nonneg (le_max_right C 0) hA0]
      have hK : max B 0 ≤ (max B 0 + max C 0 * (1 + (2*R)⁻¹)^p) * (1 + 2*R)^p * (1 + ‖z‖)^(-p) := by
        calc max B 0 ≤ (max B 0 + max C 0 * (1 + (2*R)⁻¹)^p) * 1 := by
                rw [mul_one]; linarith [mul_nonneg (le_max_right C 0) hA0]
          _ ≤ (max B 0 + max C 0 * (1 + (2*R)⁻¹)^p) * ((1 + 2*R)^p * (1 + ‖z‖)^(-p)) :=
                mul_le_mul_of_nonneg_left h1 hnm
          _ = (max B 0 + max C 0 * (1 + (2*R)⁻¹)^p) * (1 + 2*R)^p * (1 + ‖z‖)^(-p) := by ring
      exact le_trans hBz hK
    · have hCz : ‖f z‖ ≤ max C 0 * ‖z‖ ^ (-p) :=
        le_trans (hfar z (le_of_lt hz))
          (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg (norm_nonneg z) _))
      have hzpos' : (0:ℝ) < ‖z‖ := lt_of_lt_of_le h2R (le_of_lt hz)
      have hbase : (1:ℝ) / ‖z‖ ≤ (1 + (2*R)⁻¹) / (1 + ‖z‖) := by
        rw [div_le_div_iff₀ hzpos' hzpos]
        have hdiv : (1:ℝ) ≤ (2*R)⁻¹ * ‖z‖ := by
          rw [inv_mul_eq_div, one_le_div h2R]; linarith
        linarith
      have hstep : ‖z‖ ^ (-p) ≤ (1 + (2*R)⁻¹)^p * (1 + ‖z‖)^(-p) := by
        have h1 : (1 / ‖z‖)^p ≤ ((1 + (2*R)⁻¹)/(1 + ‖z‖))^p :=
          Real.rpow_le_rpow (by positivity) hbase hp.le
        have h2 : (1 / ‖z‖)^p = ‖z‖ ^ (-p) := by
          rw [one_div, Real.inv_rpow (norm_nonneg z), Real.rpow_neg (norm_nonneg z)]
        have h3 : ((1 + (2*R)⁻¹)/(1 + ‖z‖))^p
            = (1 + (2*R)⁻¹)^p * (1 + ‖z‖)^(-p) := rpow_div_mul_inv_rpow (by positivity) hzpos
        rwa [h2, h3] at h1
      have hK : max C 0 * ‖z‖ ^ (-p) ≤
          (max B 0 + max C 0 * (1 + (2*R)⁻¹)^p) * (1 + 2*R)^p * (1 + ‖z‖)^(-p) := by
        have hb : max C 0 * ‖z‖^(-p) ≤ max C 0 * ((1 + (2*R)⁻¹)^p * (1 + ‖z‖)^(-p)) :=
          mul_le_mul_of_nonneg_left hstep (le_max_right C 0)
        have hmain : max C 0 * (1 + (2*R)⁻¹)^p
            ≤ (max B 0 + max C 0 * (1 + (2*R)⁻¹)^p) * (1 + 2*R)^p := by
          have hD1 : (1:ℝ) ≤ (1 + 2*R)^p := Real.one_le_rpow (by linarith) hp.le
          nlinarith [le_max_right B 0, mul_nonneg (le_max_right C 0) hA0, hD1]
        calc max C 0 * ‖z‖ ^ (-p)
            ≤ max C 0 * ((1 + (2*R)⁻¹)^p * (1 + ‖z‖)^(-p)) := hb
          _ = max C 0 * (1 + (2*R)⁻¹)^p * (1 + ‖z‖)^(-p) := by ring
          _ ≤ (max B 0 + max C 0 * (1 + (2*R)⁻¹)^p) * (1 + 2*R)^p * (1 + ‖z‖)^(-p) := by
              refine mul_le_mul_of_nonneg_right hmain (Real.rpow_nonneg (by positivity) _)
      exact le_trans hCz hK

/-! ## Wirtinger derivatives of conjugates -/

lemma dbarCoord_star {n : ℕ} (k : Fin n) (u : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hu : DifferentiableAt ℝ u z) :
    Work.CR.Flat.dbarCoord k (fun w => star (u w)) z = star (Work.CR.Flat.dCoord k u z) := by
  have h1 : fderiv ℝ (fun w => star (u w)) z
      = (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ u z) :=
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp z hu.hasFDerivAt).fderiv
  rw [Work.CR.Flat.dbarCoord, Work.CR.Flat.dCoord, h1]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    starRingEnd_apply]
  have key : (star ((1/2 : ℂ) * ((fderiv ℝ u z) (Pi.single k (1 : ℂ))
        - Complex.I * (fderiv ℝ u z) (Pi.single k Complex.I))))
      = (1/2 : ℂ) * (star ((fderiv ℝ u z) (Pi.single k (1 : ℂ)))
        + Complex.I * star ((fderiv ℝ u z) (Pi.single k Complex.I))) := by
    rw [star_mul, star_div₀, star_one, star_ofNat, star_sub, star_mul]
    simp [Complex.conj_I]
    ring
  rw [key]

lemma dCoord_star {n : ℕ} (k : Fin n) (u : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hu : DifferentiableAt ℝ u z) :
    Work.CR.Flat.dCoord k (fun w => star (u w)) z = star (Work.CR.Flat.dbarCoord k u z) := by
  have h1 : fderiv ℝ (fun w => star (u w)) z
      = (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ u z) :=
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp z hu.hasFDerivAt).fderiv
  rw [Work.CR.Flat.dbarCoord, Work.CR.Flat.dCoord, h1]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    starRingEnd_apply]
  have key : (star ((1/2 : ℂ) * ((fderiv ℝ u z) (Pi.single k (1 : ℂ))
        + Complex.I * (fderiv ℝ u z) (Pi.single k Complex.I))))
      = (1/2 : ℂ) * (star ((fderiv ℝ u z) (Pi.single k (1 : ℂ)))
        - Complex.I * star ((fderiv ℝ u z) (Pi.single k Complex.I))) := by
    rw [star_mul, star_div₀, star_one, star_ofNat, star_add, star_mul]
    simp [Complex.conj_I]
    ring
  rw [key]

/-! ## The Wirtinger derivatives of the coordinate functions -/

private lemma differentiableAt_coord {n : ℕ} (k : Fin n) (z : Fin n → ℂ) :
    DifferentiableAt ℝ (fun w : Fin n → ℂ => w k) z :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k).differentiableAt

private lemma differentiableAt_star_coord {n : ℕ} (p : Fin n) (z : Fin n → ℂ) :
    DifferentiableAt ℝ (fun w : Fin n → ℂ => star (w p)) z :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp z (differentiableAt_coord p z)

private lemma contDiff_star_coord {n : ℕ} (p : Fin n) :
    ContDiff ℝ 1 (fun x : Fin n → ℂ => star (x p)) :=
  (Complex.conjCLE.contDiff).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) p).contDiff

private lemma contDiff_coord {n : ℕ} (p : Fin n) :
    ContDiff ℝ 1 (fun x : Fin n → ℂ => x p) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) p).contDiff

lemma dCoord_apply_coord {n : ℕ} (j k : Fin n) (z : Fin n → ℂ) :
    Work.CR.Flat.dCoord j (fun w : Fin n → ℂ => w k) z = if j = k then 1 else 0 := by
  have h := dCoord_star j (fun w : Fin n → ℂ => star (w k)) z (differentiableAt_star_coord k z)
  have h2 : (fun w : Fin n → ℂ => star (star (w k))) = (fun w : Fin n → ℂ => w k) := by
    funext w; simp
  rw [h2, Work.CR.Flat.Polydisc.dbarCoord_apply_conj_coord] at h
  simpa using h

lemma dCoord_apply_conj_coord {n : ℕ} (j k : Fin n) (z : Fin n → ℂ) :
    Work.CR.Flat.dCoord j (fun w : Fin n → ℂ => star (w k)) z = 0 := by
  have h := dCoord_star j (fun w : Fin n → ℂ => w k) z (differentiableAt_coord k z)
  rw [Work.CR.Flat.Polydisc.dbarCoord_apply_coord j k z] at h
  simpa using h

/-! ## Moments of Wirtinger derivatives -/

/-- A compactly supported `C¹` function is integrable on `ℂⁿ`. -/
lemma integrable_of_contDiff_one_hasCompactSupport {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    (hf : ContDiff ℝ 1 f) (hcs : HasCompactSupport f) : Integrable f :=
  hf.continuous.integrable_of_hasCompactSupport hcs

/-- The derivative of a compactly supported function, evaluated on a vector, is compactly
supported. -/
lemma hasCompactSupport_fderiv_apply {n : ℕ} {f : (Fin n → ℂ) → ℂ} (hcs : HasCompactSupport f)
    (v : Fin n → ℂ) : HasCompactSupport (fun y => fderiv ℝ f y v) := by
  have h1 : (fun y => fderiv ℝ f y v) = (fun L : (Fin n → ℂ) →L[ℝ] ℂ => L v) ∘ (fderiv ℝ f) :=
    rfl
  rw [h1]
  exact (hcs.fderiv (𝕜 := ℝ)).comp_left (by simp)

/-- Integration by parts for `∂_k`, for `C¹` data with compact support. -/
lemma ibp_dCoord {n : ℕ} (k : Fin n) {u f : (Fin n → ℂ) → ℂ}
    (hu : ContDiff ℝ 1 u) (hf : ContDiff ℝ 1 f) (hcs : HasCompactSupport f) :
    ∫ x, u x * Work.CR.Flat.dCoord k f x = -∫ x, Work.CR.Flat.dCoord k u x * f x := by
  refine Work.CR.Flat.Cauchy.bmCz.integral_mul_dCoord_eq_neg k hu hf ?_ ?_ ?_ ?_ ?_
  · exact (hu.continuous_fderiv (by norm_num) |>.clm_apply continuous_const |>.mul
      hf.continuous).integrable_of_hasCompactSupport (hasCompactSupport_mul_of hcs)
  · exact (hu.continuous_fderiv (by norm_num) |>.clm_apply continuous_const |>.mul
      hf.continuous).integrable_of_hasCompactSupport (hasCompactSupport_mul_of hcs)
  · exact (hu.continuous.mul ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)
      ).integrable_of_hasCompactSupport (hasCompactSupport_mul_of (hasCompactSupport_fderiv_apply hcs _))
  · exact (hu.continuous.mul ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)
      ).integrable_of_hasCompactSupport (hasCompactSupport_mul_of (hasCompactSupport_fderiv_apply hcs _))
  · exact (hu.continuous.mul hf.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_mul_of hcs)

/-- Integration by parts for `∂̄_k`, for `C¹` data with compact support. -/
lemma ibp_dbarCoord {n : ℕ} (k : Fin n) {u f : (Fin n → ℂ) → ℂ}
    (hu : ContDiff ℝ 1 u) (hf : ContDiff ℝ 1 f) (hcs : HasCompactSupport f) :
    ∫ x, u x * Work.CR.Flat.dbarCoord k f x = -∫ x, Work.CR.Flat.dbarCoord k u x * f x := by
  refine Work.CR.Flat.integral_mul_dbarCoord_eq_neg k hu hf ?_ ?_ ?_ ?_ ?_
  · exact (hu.continuous_fderiv (by norm_num) |>.clm_apply continuous_const |>.mul
      hf.continuous).integrable_of_hasCompactSupport (hasCompactSupport_mul_of hcs)
  · exact (hu.continuous_fderiv (by norm_num) |>.clm_apply continuous_const |>.mul
      hf.continuous).integrable_of_hasCompactSupport (hasCompactSupport_mul_of hcs)
  · exact (hu.continuous.mul ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)
      ).integrable_of_hasCompactSupport (hasCompactSupport_mul_of (hasCompactSupport_fderiv_apply hcs _))
  · exact (hu.continuous.mul ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)
      ).integrable_of_hasCompactSupport (hasCompactSupport_mul_of (hasCompactSupport_fderiv_apply hcs _))
  · exact (hu.continuous.mul hf.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_mul_of hcs)

lemma integral_dCoord_eq_zero {n : ℕ} {f : (Fin n → ℂ) → ℂ} (hf : ContDiff ℝ 1 f)
    (hcs : HasCompactSupport f) (k : Fin n) :
    ∫ x, Work.CR.Flat.dCoord k f x = 0 := by
  have h := ibp_dCoord k (u := fun _ : Fin n → ℂ => (1:ℂ)) (f := f) contDiff_const hf hcs
  have h0 : ∀ x : Fin n → ℂ, Work.CR.Flat.dCoord k (fun _ : Fin n → ℂ => (1:ℂ)) x = 0 :=
    fun x => by simp [Work.CR.Flat.dCoord]
  simp only [h0, zero_mul, integral_zero, neg_zero] at h
  simpa using h

lemma integral_dbarCoord_eq_zero {n : ℕ} {f : (Fin n → ℂ) → ℂ} (hf : ContDiff ℝ 1 f)
    (hcs : HasCompactSupport f) (k : Fin n) :
    ∫ x, Work.CR.Flat.dbarCoord k f x = 0 := by
  have h := ibp_dbarCoord k (u := fun _ : Fin n → ℂ => (1:ℂ)) (f := f) contDiff_const hf hcs
  have h0 : ∀ x : Fin n → ℂ, Work.CR.Flat.dbarCoord k (fun _ : Fin n → ℂ => (1:ℂ)) x = 0 :=
    fun x => by simp [Work.CR.Flat.dbarCoord]
  simp only [h0, zero_mul, integral_zero, neg_zero] at h
  simpa using h

lemma integral_coord_mul_dCoord {n : ℕ} {f : (Fin n → ℂ) → ℂ} (hf : ContDiff ℝ 1 f)
    (hcs : HasCompactSupport f) (p k : Fin n) :
    ∫ x, x p * Work.CR.Flat.dCoord k f x
      = -(if p = k then (1:ℂ) else 0) * ∫ x, f x := by
  have h := ibp_dCoord k (u := fun x : Fin n → ℂ => x p) (f := f) (contDiff_coord p) hf hcs
  have hd : ∀ x : Fin n → ℂ, Work.CR.Flat.dCoord k (fun x : Fin n → ℂ => x p) x
      = if p = k then 1 else 0 := by
    intro x
    rw [dCoord_apply_coord k p x]
    by_cases hpk : p = k
    · simp [hpk]
    · have hkp : ¬ (k = p) := fun h => hpk h.symm
      simp [hpk, hkp]
  simp only [hd] at h
  rw [h]
  by_cases hpk : p = k
  · simp [hpk]
  · simp [hpk]

lemma integral_coord_mul_dbarCoord {n : ℕ} {f : (Fin n → ℂ) → ℂ} (hf : ContDiff ℝ 1 f)
    (hcs : HasCompactSupport f) (p k : Fin n) :
    ∫ x, x p * Work.CR.Flat.dbarCoord k f x = 0 := by
  have h := ibp_dbarCoord k (u := fun x : Fin n → ℂ => x p) (f := f) (contDiff_coord p) hf hcs
  have hd : ∀ x : Fin n → ℂ, Work.CR.Flat.dbarCoord k (fun x : Fin n → ℂ => x p) x = 0 :=
    fun x => Work.CR.Flat.Polydisc.dbarCoord_apply_coord k p x
  simp only [hd, zero_mul] at h
  simpa using h

lemma integral_star_coord_mul_dCoord {n : ℕ} {f : (Fin n → ℂ) → ℂ} (hf : ContDiff ℝ 1 f)
    (hcs : HasCompactSupport f) (p k : Fin n) :
    ∫ x, star (x p) * Work.CR.Flat.dCoord k f x = 0 := by
  have h := ibp_dCoord k (u := fun x : Fin n → ℂ => star (x p)) (f := f)
    (contDiff_star_coord p) hf hcs
  have hd : ∀ x : Fin n → ℂ, Work.CR.Flat.dCoord k (fun x : Fin n → ℂ => star (x p)) x = 0 :=
    fun x => dCoord_apply_conj_coord k p x
  simp only [hd, zero_mul] at h
  simpa using h

lemma integral_star_coord_mul_dbarCoord {n : ℕ} {f : (Fin n → ℂ) → ℂ} (hf : ContDiff ℝ 1 f)
    (hcs : HasCompactSupport f) (p k : Fin n) :
    ∫ x, star (x p) * Work.CR.Flat.dbarCoord k f x
      = -(if p = k then (1:ℂ) else 0) * ∫ x, f x := by
  have h := ibp_dbarCoord k (u := fun x : Fin n → ℂ => star (x p)) (f := f)
    (contDiff_star_coord p) hf hcs
  have hd : ∀ x : Fin n → ℂ, Work.CR.Flat.dbarCoord k (fun x : Fin n → ℂ => star (x p)) x
      = if p = k then 1 else 0 := by
    intro x
    rw [Work.CR.Flat.Polydisc.dbarCoord_apply_conj_coord k p x]
    by_cases hpk : p = k
    · simp [hpk]
    · have hkp : ¬ (k = p) := fun h => hpk h.symm
      simp [hpk, hkp]
  simp only [hd] at h
  rw [h]
  by_cases hpk : p = k
  · simp [hpk]
  · simp [hpk]

/-! ## The Wirtinger derivatives of the Bochner–Martinelli potential -/

lemma dCoord_bmPotential_eq {n : ℕ} (hn : 0 < n) {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiff ℝ 1 (f j)) (hcs : ∀ j, HasCompactSupport (f j)) (k : Fin n) :
    (fun z => Work.CR.Flat.dCoord k (Work.CR.Flat.Cauchy.bmPotential f) z)
      = fun z => Work.CR.Flat.Cauchy.bmPotential
          (fun j y => Work.CR.Flat.dCoord k (f j) y) z := by
  funext z
  rw [Work.NN.Core.bmPotential_dCoord_eq hn hf hcs k z, Work.CR.Flat.Cauchy.bmPotential_eq_bmPot]
  simp only [Work.CR.Flat.Cauchy.bmPot]

lemma dbarCoord_bmPotential_eq {n : ℕ} (hn : 0 < n) {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiff ℝ 1 (f j)) {R : ℝ} (hR : 0 < R)
    (hsupp : ∀ j x, R ≤ ‖x‖ → f j x = 0) (k : Fin n) :
    (fun z => Work.CR.Flat.dbarCoord k (Work.CR.Flat.Cauchy.bmPotential f) z)
      = fun z => Work.CR.Flat.Cauchy.bmPotential
          (fun j y => Work.CR.Flat.dbarCoord k (f j) y) z := by
  have hfun : Work.CR.Flat.Cauchy.bmPotential f = Work.CR.Flat.Cauchy.bmPot f :=
    funext fun w => Work.CR.Flat.Cauchy.bmPotential_eq_bmPot f w
  funext z
  rw [hfun, Work.CR.Flat.Cauchy.bmPot_dbarCoord hn hf hR hsupp k z]
  exact (Work.CR.Flat.Cauchy.bmPotential_eq_bmPot _ z).symm

/-! ## Integrable dominating functions for the energy identity -/

/-- The function `z ↦ c (1 + ‖z‖²)^{-(2n - 3/4)}` is integrable on `ℂⁿ` (for `n ≥ 1`). -/
lemma integrable_dominating {n : ℕ} (hn : 0 < n) (c : ℝ) :
    Integrable (fun z : Fin n → ℂ => c * (1 + ‖z‖ ^ 2) ^ (-(2 * (n : ℝ) - 3/4))) := by
  have hfr : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Complex.finrank_real_complex, smul_eq_mul]
    ring
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hfin : ((Module.finrank ℝ (Fin n → ℂ) : ℕ) : ℝ) < 4 * (n:ℝ) - 3/2 := by
    rw [hfr]; push_cast; linarith
  have h := integrable_rpow_neg_one_add_norm_sq (μ := volume) (E := Fin n → ℂ)
    (r := 4 * (n:ℝ) - 3/2) hfin
  have hexp : -(4 * (n:ℝ) - 3/2) / 2 = -(2 * (n : ℝ) - 3/4) := by ring
  rw [hexp] at h
  simpa using h.const_mul c

/-- Pointwise domination of `(1 + ‖z‖)^{-p}` by the integrable weight, for `p ≥ 4n - 1`. -/
lemma one_add_norm_rpow_le {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 4 * (n:ℝ) - 1 ≤ p)
    (z : Fin n → ℂ) :
    (1 + ‖z‖) ^ (-p) ≤ (1 + ‖z‖ ^ 2) ^ (-(2 * (n : ℝ) - 3/4)) := by
  have hzn : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
  have ha0 : (0:ℝ) ≤ 1 + ‖z‖ := by linarith
  have hapos : (0:ℝ) < 1 + ‖z‖ := by linarith
  have ha1 : (1:ℝ) ≤ 1 + ‖z‖ := by linarith
  have hb0 : (0:ℝ) ≤ 1 + ‖z‖ ^ 2 := by positivity
  have hbpos : (0:ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  have hb1 : (1:ℝ) ≤ 1 + ‖z‖ ^ 2 := by nlinarith
  have hab : 1 + ‖z‖ ^ 2 ≤ (1 + ‖z‖) ^ 2 := by nlinarith
  have hstep1 : (1 + ‖z‖) ^ (-p) ≤ (1 + ‖z‖) ^ (-(4 * (n:ℝ) - 1)) := by
    have h : (1 + ‖z‖) ^ (4 * (n:ℝ) - 1) ≤ (1 + ‖z‖) ^ p :=
      Real.rpow_le_rpow_of_exponent_le ha1 hp
    rw [Real.rpow_neg ha0, Real.rpow_neg ha0]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hapos _) h
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have h3 : (1 + ‖z‖ ^ 2) ^ (2 * (n:ℝ) - 3/4) ≤ ((1 + ‖z‖)^2) ^ (2 * (n:ℝ) - 3/4) :=
    Real.rpow_le_rpow hb0 hab (by linarith)
  have h4 : ((1 + ‖z‖)^2) ^ (2 * (n:ℝ) - 3/4) ≤ ((1 + ‖z‖)^2) ^ (2 * (n:ℝ) - 1/2) :=
    Real.rpow_le_rpow_of_exponent_le (by nlinarith : (1:ℝ) ≤ (1 + ‖z‖)^2) (by linarith)
  have h5 : ((1 + ‖z‖)^2) ^ (2 * (n:ℝ) - 1/2) = (1 + ‖z‖) ^ (4 * (n:ℝ) - 1) := by
    rw [← Real.rpow_natCast (1 + ‖z‖) 2, ← Real.rpow_mul (by linarith)]
    congr 1
    ring
  have h6 : (1 + ‖z‖ ^ 2) ^ (2 * (n:ℝ) - 3/4) ≤ (1 + ‖z‖) ^ (4 * (n:ℝ) - 1) := by
    linarith [h3, h4, le_of_eq h5]
  have hstep2 : (1 + ‖z‖) ^ (-(4 * (n:ℝ) - 1)) ≤ (1 + ‖z‖ ^ 2) ^ (-(2 * (n : ℝ) - 3/4)) := by
    rw [Real.rpow_neg ha0, Real.rpow_neg hb0]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hbpos _) h6
  linarith [hstep1, hstep2]

/-- A function vanishing near a point has vanishing `∂`-derivative there. -/
lemma dCoord_eq_zero_of_eventuallyEq_zero {n : ℕ} {g : (Fin n → ℂ) → ℂ} {x : Fin n → ℂ}
    (h : g =ᶠ[nhds x] 0) (k : Fin n) : Work.CR.Flat.dCoord k g x = 0 := by
  have hfd : fderiv ℝ g x = 0 := by rw [h.fderiv_eq]; simp
  rw [Work.CR.Flat.dCoord, hfd]
  simp

/-- **The `L²` energy identity for the Bochner–Martinelli potential.**  For `h ∈ C²_c` (each
component of class `C²` with compact support) put `u = bmPotential h`.  Then
`Σ_k ∫ ‖∂_k u‖² = -(1/4) ∫ Re(u · conj(Δu))`, where `flatLap f = 4 Σ_k ∂_k ∂̄_k f` is the flat
Laplacian (`Work.NN.Core.czB_L2_defs`). -/
theorem czbL2_energy {n : ℕ} (hn : 0 < n) {h : Fin n → (Fin n → ℂ) → ℂ}
    (hh : ∀ j, ContDiff ℝ 2 (h j)) (hcs : ∀ j, HasCompactSupport (h j)) :
    ∑ k : Fin n, ∫ z : Fin n → ℂ, ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2
      = -(1 / 4) * ∫ z : Fin n → ℂ,
          (bmPotential h z * star (flatLap (bmPotential h) z)).re := by
  classical
  have hh1 : ∀ j, ContDiff ℝ 1 (h j) := fun j => (hh j).of_le (by norm_num)
  -- ============================== the support radii ==============================
  choose Rj hRj using fun j => (hcs j).exists_pos_le_norm
  set R₀ : ℝ := (∑ j : Fin n, Rj j) + 1 with hR₀def
  have hR₀pos : 0 < R₀ := by
    rw [hR₀def]
    have : 0 < ∑ j : Fin n, Rj j :=
      Finset.sum_pos (fun j _ => (hRj j).1) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    linarith
  have hR₀sup : ∀ j x, R₀ ≤ ‖x‖ → h j x = 0 := by
    intro j x hx
    refine (hRj j).2 x (le_trans ?_ hx)
    rw [hR₀def]
    have h := Finset.single_le_sum (fun i _ => (hRj i).1.le) (Finset.mem_univ j)
    linarith
  set R : ℝ := Real.sqrt n * R₀ + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hsupp : ∀ j x, R ≤ eucNorm x → h j x = 0 := by
    intro j x hx
    refine hR₀sup j x ?_
    have h1 : eucNorm x ≤ Real.sqrt n * ‖x‖ := bmCz.eucNorm_le_sqrt_mul_norm x
    have h3 : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    nlinarith [h1, hx, hR₀pos, h3]
  have hsupp1 : ∀ j x, R + 1 ≤ eucNorm x → h j x = 0 := fun j x hx => hsupp j x (by linarith)
  have hnbR : ∀ x : Fin n → ℂ, R < eucNorm x → ({y : Fin n → ℂ | R < eucNorm y} ∈ nhds x) :=
    fun x hx => (isOpen_lt continuous_const continuous_eucNorm).mem_nhds hx
  have hnbR1 : ∀ x : Fin n → ℂ, R + 1 < eucNorm x →
      ({y : Fin n → ℂ | R + 1 < eucNorm y} ∈ nhds x) :=
    fun x hx => (isOpen_lt continuous_const continuous_eucNorm).mem_nhds hx
  have hsD : ∀ (k j : Fin n) x, R + 1 ≤ eucNorm x → Work.CR.Flat.dCoord k (h j) x = 0 := by
    intro k j x hx
    have hev : h j =ᶠ[nhds x] 0 := by
      filter_upwards [hnbR x (by linarith)] with y hy
      exact hsupp j y (le_of_lt hy)
    exact dCoord_eq_zero_of_eventuallyEq_zero hev k
  have hsDb : ∀ (k j : Fin n) x, R + 1 ≤ eucNorm x → Work.CR.Flat.dbarCoord k (h j) x = 0 := by
    intro k j x hx
    have hev : h j =ᶠ[nhds x] 0 := by
      filter_upwards [hnbR x (by linarith)] with y hy
      exact hsupp j y (le_of_lt hy)
    exact Work.NN.Core.dbarCoord_eq_zero_of_eventuallyEq_zero hev k
  have hsDD : ∀ (l k j : Fin n) x, R + 2 ≤ eucNorm x →
      Work.CR.Flat.dCoord l (fun y => Work.CR.Flat.dCoord k (h j) y) x = 0 := by
    intro l k j x hx
    have hev : (fun y => Work.CR.Flat.dCoord k (h j) y) =ᶠ[nhds x] 0 := by
      filter_upwards [hnbR1 x (by linarith)] with y hy
      exact hsD k j y (le_of_lt hy)
    exact dCoord_eq_zero_of_eventuallyEq_zero hev l
  have hsDbD : ∀ (l k j : Fin n) x, R + 2 ≤ eucNorm x →
      Work.CR.Flat.dbarCoord l (fun y => Work.CR.Flat.dCoord k (h j) y) x = 0 := by
    intro l k j x hx
    have hev : (fun y => Work.CR.Flat.dCoord k (h j) y) =ᶠ[nhds x] 0 := by
      filter_upwards [hnbR1 x (by linarith)] with y hy
      exact hsD k j y (le_of_lt hy)
    exact Work.NN.Core.dbarCoord_eq_zero_of_eventuallyEq_zero hev l
  have hsDDb : ∀ (l k j : Fin n) x, R + 2 ≤ eucNorm x →
      Work.CR.Flat.dCoord l (fun y => Work.CR.Flat.dbarCoord k (h j) y) x = 0 := by
    intro l k j x hx
    have hev : (fun y => Work.CR.Flat.dbarCoord k (h j) y) =ᶠ[nhds x] 0 := by
      filter_upwards [hnbR1 x (by linarith)] with y hy
      exact hsDb k j y (le_of_lt hy)
    exact dCoord_eq_zero_of_eventuallyEq_zero hev l
  have hu2 : ContDiff ℝ 2 (bmPotential h) := bmPotential_contDiff_of_hasCompactSupport hn hh hcs
  have hu2' : ContDiff ℝ 1 (bmPotential h) := hu2.of_le (by norm_num)
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  -- ============================== bounds ==============================
  -- the potential itself
  obtain ⟨cu, hcunn, hbndu⟩ : ∃ K : ℝ, 0 ≤ K ∧
      ∀ z : Fin n → ℂ, ‖bmPotential h z‖ ≤ K * (1 + ‖z‖) ^ (-(2*(n:ℝ) - 1)) := by
    obtain ⟨C, hC, hfar⟩ := norm_bmPot_le_of_large (n := n) hn (h := h) (R := R₀) hR₀pos
      (fun j => (hh j).continuous) hcs hR₀sup
    refine bound_of_far_decay (n := n) (p := 2*(n:ℝ) - 1) (C := C) (by linarith) (R := R₀) hR₀pos
      (f := fun z => bmPotential h z) ((hu2.differentiable (by norm_num)).continuous)
      (fun z hz => ?_)
    rw [bmPotential_eq_bmPot]
    refine (hfar z hz).trans (le_of_eq ?_)
    rw [show (1:ℝ) - 2*(n:ℝ) = -(2*(n:ℝ) - 1) from by ring]
  -- the decay lemmas
  obtain ⟨C₁, hC₁nn, hdec₁⟩ := bmPotential_decay_zero_mean (n := n) hn (R := R + 1) (by linarith)
  obtain ⟨C₂, hC₂nn, hdec₂⟩ := bmPotential_decay_two_moments (n := n) hn (R := R + 2) (by linarith)
  -- the first derivatives
  have hbndD : ∃ K : ℝ, 0 ≤ K ∧ ∀ (k : Fin n) (z : Fin n → ℂ),
      ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ≤ K * (1 + ‖z‖) ^ (-(2*(n:ℝ))) := by
    have hper : ∀ k : Fin n, ∃ K : ℝ, 0 ≤ K ∧ ∀ z : Fin n → ℂ,
        ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ≤ K * (1 + ‖z‖) ^ (-(2*(n:ℝ))) := by
      intro k
      refine bound_of_far_decay (p := 2*(n:ℝ)) (C := C₁ * ∑ j, ∫ x, ‖Work.CR.Flat.dCoord k (h j) x‖)
        (by positivity) (R := 2*(R+1)) (by linarith)
        (f := fun z => Work.CR.Flat.dCoord k (bmPotential h) z) ?_ (fun z hz => ?_)
      · exact continuous_dCoord_of_contDiff_one hu2' k
      · have hz' : Work.CR.Flat.dCoord k (bmPotential h) z
            = bmPotential (fun j y => Work.CR.Flat.dCoord k (h j) y) z :=
          congrFun (dCoord_bmPotential_eq hn hh1 hcs k) z
        rw [hz']
        exact hdec₁ (fun j y => Work.CR.Flat.dCoord k (h j) y)
          (fun j => (continuous_dCoord_of_contDiff_one (hh1 j) k).integrable_of_hasCompactSupport
            (hasCompactSupport_dCoord (hcs j) k))
          (fun j => continuous_dCoord_of_contDiff_one (hh1 j) k)
          (fun j x hx => hsD k j x hx)
          (fun j => integral_dCoord_eq_zero (hh1 j) (hcs j) k) z (by linarith)
    choose K hKnn hKb using hper
    exact ⟨∑ k, K k, Finset.sum_nonneg fun k _ => hKnn k, fun k z => by
      refine (hKb k z).trans ?_
      exact mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun i _ => hKnn i) (Finset.mem_univ k))
        (Real.rpow_nonneg (by positivity) _)⟩
  have hbndDb : ∃ K : ℝ, 0 ≤ K ∧ ∀ (k : Fin n) (z : Fin n → ℂ),
      ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ≤ K * (1 + ‖z‖) ^ (-(2*(n:ℝ))) := by
    have hper : ∀ k : Fin n, ∃ K : ℝ, 0 ≤ K ∧ ∀ z : Fin n → ℂ,
        ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ≤ K * (1 + ‖z‖) ^ (-(2*(n:ℝ))) := by
      intro k
      refine bound_of_far_decay (p := 2*(n:ℝ)) (C := C₁ * ∑ j, ∫ x, ‖Work.CR.Flat.dbarCoord k (h j) x‖)
        (by positivity) (R := 2*(R+1)) (by linarith)
        (f := fun z => Work.CR.Flat.dbarCoord k (bmPotential h) z) ?_ (fun z hz => ?_)
      · exact (Work.NN.Core.contDiff_one_dbarCoord hu2 k).continuous
      · have hz' : Work.CR.Flat.dbarCoord k (bmPotential h) z
            = bmPotential (fun j y => Work.CR.Flat.dbarCoord k (h j) y) z :=
          congrFun (dbarCoord_bmPotential_eq hn hh1 hR₀pos hR₀sup k) z
        rw [hz']
        exact hdec₁ (fun j y => Work.CR.Flat.dbarCoord k (h j) y)
          (fun j => (Work.NN.Core.contDiff_one_dbarCoord (hh j) k).continuous.integrable_of_hasCompactSupport
            (hasCompactSupport_dbarCoordAux (hcs j) k))
          (fun j => (Work.NN.Core.contDiff_one_dbarCoord (hh j) k).continuous)
          (fun j x hx => hsDb k j x hx)
          (fun j => integral_dbarCoord_eq_zero (hh1 j) (hcs j) k) z (by linarith)
    choose K hKnn hKb using hper
    exact ⟨∑ k, K k, Finset.sum_nonneg fun k _ => hKnn k, fun k z => by
      refine (hKb k z).trans ?_
      exact mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun i _ => hKnn i) (Finset.mem_univ k))
        (Real.rpow_nonneg (by positivity) _)⟩
  -- the second order derivatives
  have hbndDD : ∃ K : ℝ, 0 ≤ K ∧ ∀ (l k : Fin n) (z : Fin n → ℂ),
      ‖Work.CR.Flat.dCoord l (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z‖
        ≤ K * (1 + ‖z‖) ^ (-(2*(n:ℝ) + 1)) := by
    have hper : ∀ l k : Fin n, ∃ K : ℝ, 0 ≤ K ∧ ∀ z : Fin n → ℂ,
        ‖Work.CR.Flat.dCoord l (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z‖
          ≤ K * (1 + ‖z‖) ^ (-(2*(n:ℝ) + 1)) := by
      intro l k
      have hid : (fun z => Work.CR.Flat.dCoord l
            (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z)
          = fun z => bmPotential (fun j y => Work.CR.Flat.dCoord l
              (fun y' => Work.CR.Flat.dCoord k (h j) y') y) z := by
        have hfun : (fun y => Work.CR.Flat.dCoord k (bmPotential h) y)
            = fun y => bmPotential (fun j y' => Work.CR.Flat.dCoord k (h j) y') y :=
          dCoord_bmPotential_eq hn hh1 hcs k
        rw [hfun]
        exact dCoord_bmPotential_eq hn (fun j => contDiff_one_dCoord (hh j) k)
          (fun j => hasCompactSupport_dCoord (hcs j) k) l
      refine bound_of_far_decay (p := 2*(n:ℝ) + 1)
        (C := C₂ * ∑ j, ∫ x, ‖Work.CR.Flat.dCoord l (fun y' => Work.CR.Flat.dCoord k (h j) y') x‖)
        (by positivity)
        (f := fun z => Work.CR.Flat.dCoord l
          (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z)
        (R := (2*Real.sqrt n + 2) * (R+2)) (by positivity) ?_ (fun z hz => ?_)
      · exact continuous_dCoord_of_contDiff_one
          (contDiff_one_dCoord hu2 k) l
      · have hz' : Work.CR.Flat.dCoord l (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z
            = bmPotential (fun j y => Work.CR.Flat.dCoord l
                (fun y' => Work.CR.Flat.dCoord k (h j) y') y) z := congrFun hid z
        rw [hz']
        exact hdec₂ (fun j y => Work.CR.Flat.dCoord l (fun y' => Work.CR.Flat.dCoord k (h j) y') y)
          (fun j => (continuous_dCoord_of_contDiff_one (contDiff_one_dCoord (hh j) k) l).integrable_of_hasCompactSupport
            (hasCompactSupport_dCoord (hasCompactSupport_dCoord (hcs j) k) l))
          (fun j => continuous_dCoord_of_contDiff_one (contDiff_one_dCoord (hh j) k) l)
          (fun j x hx => hsDD l k j x hx)
          (fun j => integral_dCoord_eq_zero (contDiff_one_dCoord (hh j) k)
            (hasCompactSupport_dCoord (hcs j) k) l)
          (fun j p => by
            have h0 : ∫ x, Work.CR.Flat.dCoord k (h j) x = 0 := integral_dCoord_eq_zero (hh1 j) (hcs j) k
            have h := integral_coord_mul_dCoord (contDiff_one_dCoord (hh j) k)
              (hasCompactSupport_dCoord (hcs j) k) p l
            rw [h0, mul_zero] at h
            exact h)
          (fun j p => integral_star_coord_mul_dCoord (contDiff_one_dCoord (hh j) k)
            (hasCompactSupport_dCoord (hcs j) k) p l)
          z (by linarith [show (0:ℝ) ≤ Real.sqrt n by positivity])
    choose K hKnn hKb using hper
    exact ⟨∑ l, ∑ k, K l k, Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun k _ => hKnn l k,
      fun l k z => by
      refine (hKb l k z).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
      exact le_trans (Finset.single_le_sum (fun i _ => hKnn l i) (Finset.mem_univ k))
        (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun k _ => hKnn i k) (Finset.mem_univ l))⟩
  -- the mixed second order derivatives
  have hbndDbD : ∃ K : ℝ, 0 ≤ K ∧ ∀ (l k : Fin n) (z : Fin n → ℂ),
      ‖Work.CR.Flat.dbarCoord l (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z‖
        ≤ K * (1 + ‖z‖) ^ (-(2*(n:ℝ) + 1)) := by
    have hper : ∀ l k : Fin n, ∃ K : ℝ, 0 ≤ K ∧ ∀ z : Fin n → ℂ,
        ‖Work.CR.Flat.dbarCoord l (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z‖
          ≤ K * (1 + ‖z‖) ^ (-(2*(n:ℝ) + 1)) := by
      intro l k
      have hid : (fun z => Work.CR.Flat.dbarCoord l
            (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z)
          = fun z => bmPotential (fun j y => Work.CR.Flat.dbarCoord l
              (fun y' => Work.CR.Flat.dCoord k (h j) y') y) z := by
        have hfun : (fun y => Work.CR.Flat.dCoord k (bmPotential h) y)
            = fun y => bmPotential (fun j y' => Work.CR.Flat.dCoord k (h j) y') y :=
          dCoord_bmPotential_eq hn hh1 hcs k
        rw [hfun]
        exact dbarCoord_bmPotential_eq hn (fun j => contDiff_one_dCoord (hh j) k) (by linarith)
          (fun j x hx => hsD k j x (le_trans hx (pi_norm_le_eucNorm x)))
          l
      refine bound_of_far_decay (p := 2*(n:ℝ) + 1)
        (C := C₂ * ∑ j, ∫ x, ‖Work.CR.Flat.dbarCoord l (fun y' => Work.CR.Flat.dCoord k (h j) y') x‖)
        (by positivity)
        (f := fun z => Work.CR.Flat.dbarCoord l
          (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z)
        (R := (2*Real.sqrt n + 2) * (R+2)) (by positivity) ?_ (fun z hz => ?_)
      · exact continuous_dbarCoord_of_contDiff
          (contDiff_one_dCoord hu2 k) l
      · have hz' : Work.CR.Flat.dbarCoord l (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z
            = bmPotential (fun j y => Work.CR.Flat.dbarCoord l
                (fun y' => Work.CR.Flat.dCoord k (h j) y') y) z := congrFun hid z
        rw [hz']
        exact hdec₂ (fun j y => Work.CR.Flat.dbarCoord l (fun y' => Work.CR.Flat.dCoord k (h j) y') y)
          (fun j => (continuous_dbarCoord_of_contDiff (contDiff_one_dCoord (hh j) k) l).integrable_of_hasCompactSupport
            (hasCompactSupport_dbarCoordAux (hasCompactSupport_dCoord (hcs j) k) l))
          (fun j => continuous_dbarCoord_of_contDiff (contDiff_one_dCoord (hh j) k) l)
          (fun j x hx => hsDbD l k j x hx)
          (fun j => integral_dbarCoord_eq_zero (contDiff_one_dCoord (hh j) k)
            (hasCompactSupport_dCoord (hcs j) k) l)
          (fun j p => integral_coord_mul_dbarCoord (contDiff_one_dCoord (hh j) k)
            (hasCompactSupport_dCoord (hcs j) k) p l)
          (fun j p => by
            have h0 : ∫ x, Work.CR.Flat.dCoord k (h j) x = 0 :=
              integral_dCoord_eq_zero (hh1 j) (hcs j) k
            have h := integral_star_coord_mul_dbarCoord (contDiff_one_dCoord (hh j) k)
              (hasCompactSupport_dCoord (hcs j) k) p l
            rw [h0, mul_zero] at h
            exact h)
          z (by linarith [show (0:ℝ) ≤ Real.sqrt n by positivity])
    choose K hKnn hKb using hper
    exact ⟨∑ l, ∑ k, K l k, Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun k _ => hKnn l k,
      fun l k z => by
      refine (hKb l k z).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
      exact le_trans (Finset.single_le_sum (fun i _ => hKnn l i) (Finset.mem_univ k))
        (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun k _ => hKnn i k) (Finset.mem_univ l))⟩
  have hbndDDb : ∃ K : ℝ, 0 ≤ K ∧ ∀ (l k : Fin n) (z : Fin n → ℂ),
      ‖Work.CR.Flat.dCoord l (fun y => Work.CR.Flat.dbarCoord k (bmPotential h) y) z‖
        ≤ K * (1 + ‖z‖) ^ (-(2*(n:ℝ) + 1)) := by
    have hper : ∀ l k : Fin n, ∃ K : ℝ, 0 ≤ K ∧ ∀ z : Fin n → ℂ,
        ‖Work.CR.Flat.dCoord l (fun y => Work.CR.Flat.dbarCoord k (bmPotential h) y) z‖
          ≤ K * (1 + ‖z‖) ^ (-(2*(n:ℝ) + 1)) := by
      intro l k
      have hid : (fun z => Work.CR.Flat.dCoord l
            (fun y => Work.CR.Flat.dbarCoord k (bmPotential h) y) z)
          = fun z => bmPotential (fun j y => Work.CR.Flat.dCoord l
              (fun y' => Work.CR.Flat.dbarCoord k (h j) y') y) z := by
        have hfun : (fun y => Work.CR.Flat.dbarCoord k (bmPotential h) y)
            = fun y => bmPotential (fun j y' => Work.CR.Flat.dbarCoord k (h j) y') y :=
          dbarCoord_bmPotential_eq hn hh1 hR₀pos hR₀sup k
        rw [hfun]
        exact dCoord_bmPotential_eq hn (fun j => Work.NN.Core.contDiff_one_dbarCoord (hh j) k)
          (fun j => hasCompactSupport_dbarCoordAux (hcs j) k) l
      refine bound_of_far_decay (p := 2*(n:ℝ) + 1)
        (C := C₂ * ∑ j, ∫ x, ‖Work.CR.Flat.dCoord l (fun y' => Work.CR.Flat.dbarCoord k (h j) y') x‖)
        (by positivity)
        (f := fun z => Work.CR.Flat.dCoord l
          (fun y => Work.CR.Flat.dbarCoord k (bmPotential h) y) z)
        (R := (2*Real.sqrt n + 2) * (R+2)) (by positivity) ?_ (fun z hz => ?_)
      · exact continuous_dCoord_of_contDiff_one
          (Work.NN.Core.contDiff_one_dbarCoord hu2 k) l
      · have hz' : Work.CR.Flat.dCoord l (fun y => Work.CR.Flat.dbarCoord k (bmPotential h) y) z
            = bmPotential (fun j y => Work.CR.Flat.dCoord l
                (fun y' => Work.CR.Flat.dbarCoord k (h j) y') y) z := congrFun hid z
        rw [hz']
        exact hdec₂ (fun j y => Work.CR.Flat.dCoord l (fun y' => Work.CR.Flat.dbarCoord k (h j) y') y)
          (fun j => (continuous_dCoord_of_contDiff_one (Work.NN.Core.contDiff_one_dbarCoord (hh j) k) l).integrable_of_hasCompactSupport
            (hasCompactSupport_dCoord (hasCompactSupport_dbarCoordAux (hcs j) k) l))
          (fun j => continuous_dCoord_of_contDiff_one (Work.NN.Core.contDiff_one_dbarCoord (hh j) k) l)
          (fun j x hx => hsDDb l k j x hx)
          (fun j => integral_dCoord_eq_zero (Work.NN.Core.contDiff_one_dbarCoord (hh j) k)
            (hasCompactSupport_dbarCoordAux (hcs j) k) l)
          (fun j p => by
            have h0 : ∫ x, Work.CR.Flat.dbarCoord k (h j) x = 0 :=
              integral_dbarCoord_eq_zero (hh1 j) (hcs j) k
            have h := integral_coord_mul_dCoord (Work.NN.Core.contDiff_one_dbarCoord (hh j) k)
              (hasCompactSupport_dbarCoordAux (hcs j) k) p l
            rw [h0, mul_zero] at h
            exact h)
          (fun j p => integral_star_coord_mul_dCoord (Work.NN.Core.contDiff_one_dbarCoord (hh j) k)
            (hasCompactSupport_dbarCoordAux (hcs j) k) p l)
          z (by linarith [show (0:ℝ) ≤ Real.sqrt n by positivity])
    choose K hKnn hKb using hper
    exact ⟨∑ l, ∑ k, K l k, Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun k _ => hKnn l k,
      fun l k z => by
      refine (hKb l k z).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
      exact le_trans (Finset.single_le_sum (fun i _ => hKnn l i) (Finset.mem_univ k))
        (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun k _ => hKnn i k) (Finset.mem_univ l))⟩
  -- ============================== derivative bounds ==============================
  obtain ⟨Kdu, hKdunn, hKdub⟩ := hbndD
  obtain ⟨Kdub, hKdubnn, hKdubb⟩ := hbndDb
  obtain ⟨Kdd, hKddnn, hKddb⟩ := hbndDD
  obtain ⟨Kdbd, hKdbdnn, hKdbdb⟩ := hbndDbD
  obtain ⟨Kddb, hKddbnn, hKddbb⟩ := hbndDDb
  -- `fderiv u`
  have hdfu : ∀ z : Fin n → ℂ, ‖fderiv ℝ (bmPotential h) z‖
      ≤ (2 * (n:ℝ) * (Kdu + Kdub)) * (1 + ‖z‖) ^ (-(2*(n:ℝ))) := by
    intro z
    refine (bmCz.norm_fderiv_le_sum_wirtinger _ z).trans ?_
    have hterm : ∀ l : Fin n, ‖Work.CR.Flat.dCoord l (bmPotential h) z‖
        + ‖Work.CR.Flat.dbarCoord l (bmPotential h) z‖
        ≤ (Kdu + Kdub) * (1 + ‖z‖) ^ (-(2*(n:ℝ))) := fun l => by
      refine (add_le_add (hKdub l z) (hKdubb l z)).trans (le_of_eq ?_)
      ring
    calc 2 * ∑ l : Fin n, (‖Work.CR.Flat.dCoord l (bmPotential h) z‖
          + ‖Work.CR.Flat.dbarCoord l (bmPotential h) z‖)
        ≤ 2 * ∑ _l : Fin n, (Kdu + Kdub) * (1 + ‖z‖) ^ (-(2*(n:ℝ))) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => hterm l) (by norm_num)
      _ = 2 * (n:ℝ) * (Kdu + Kdub) * (1 + ‖z‖) ^ (-(2*(n:ℝ))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  -- `fderiv (∂_k u)`
  have hdfG : ∀ (k : Fin n) (z : Fin n → ℂ),
      ‖fderiv ℝ (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z‖
        ≤ (2 * (n:ℝ) * (Kdd + Kdbd)) * (1 + ‖z‖) ^ (-(2*(n:ℝ) + 1)) := by
    intro k z
    refine (bmCz.norm_fderiv_le_sum_wirtinger _ z).trans ?_
    have hterm : ∀ l : Fin n,
        ‖Work.CR.Flat.dCoord l (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z‖
          + ‖Work.CR.Flat.dbarCoord l (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z‖
        ≤ (Kdd + Kdbd) * (1 + ‖z‖) ^ (-(2*(n:ℝ) + 1)) := fun l => by
      refine (add_le_add (hKddb l k z) (hKdbdb l k z)).trans (le_of_eq ?_)
      ring
    calc 2 * ∑ l : Fin n, (‖Work.CR.Flat.dCoord l
            (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z‖
          + ‖Work.CR.Flat.dbarCoord l (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z‖)
        ≤ 2 * ∑ _l : Fin n, (Kdd + Kdbd) * (1 + ‖z‖) ^ (-(2*(n:ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => hterm l) (by norm_num)
      _ = 2 * (n:ℝ) * (Kdd + Kdbd) * (1 + ‖z‖) ^ (-(2*(n:ℝ) + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  -- ============================== integrability ==============================
  have hIntProd : ∀ {f g : (Fin n → ℂ) → ℂ} {p q c d : ℝ}, 0 ≤ c → 0 ≤ d →
      4*(n:ℝ) - 1 ≤ p + q → (∀ z, ‖f z‖ ≤ c * (1 + ‖z‖) ^ (-p)) →
      (∀ z, ‖g z‖ ≤ d * (1 + ‖z‖) ^ (-q)) →
      AEStronglyMeasurable (fun z => f z * g z) volume → Integrable (fun z => f z * g z) := by
    intro f g p q c d hc hd hpq hf hg hm
    refine Integrable.mono' (integrable_dominating hn (c*d)) hm (Filter.Eventually.of_forall fun z => ?_)
    rw [norm_mul]
    refine le_trans (mul_le_mul (hf z) (hg z) (norm_nonneg _)
      (mul_nonneg hc (Real.rpow_nonneg (by positivity) _))) ?_
    have h2 : (c * (1 + ‖z‖) ^ (-p)) * (d * (1 + ‖z‖) ^ (-q))
        = (c*d) * ((1 + ‖z‖) ^ (-(p+q))) := by
      rw [show -(p+q) = -p + -q from by ring, Real.rpow_add (by positivity)]
      ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left (one_add_norm_rpow_le hn hpq z) (mul_nonneg hc hd)
  -- ============================== the integration by parts ==============================
  have hkey : ∀ k : Fin n,
      (∫ z : Fin n → ℂ, ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2 : ℝ)
        = -(∫ z : Fin n → ℂ, Work.CR.Flat.dbarCoord k
              (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z
            * star (bmPotential h z)).re := by
    intro k
    have hG1 : ContDiff ℝ 1 (fun z => Work.CR.Flat.dCoord k (bmPotential h) z) :=
      contDiff_one_dCoord hu2 k
    have hv1 : ContDiff ℝ 1 (fun z => star (bmPotential h z)) :=
      (Complex.conjCLE.contDiff).comp hu2'
    have hGcont : Continuous (fun z => Work.CR.Flat.dCoord k (bmPotential h) z) := hG1.continuous
    have hfc : Continuous (fun z => fderiv ℝ (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z) :=
      hG1.continuous_fderiv (by norm_num)
    have huc : Continuous (fun z => bmPotential h z) := hu2'.continuous
    have hfc_u : Continuous (fun z => fderiv ℝ (bmPotential h) z) :=
      hu2'.continuous_fderiv (by norm_num)
    have h1u : Integrable (fun x => fderiv ℝ (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) x
        (Pi.single k (1 : ℂ)) * star (bmPotential h x)) := by
      refine hIntProd (c := 2 * (n:ℝ) * (Kdd + Kdbd)) (d := cu)
        (p := 2*(n:ℝ) + 1) (q := 2*(n:ℝ) - 1) (by positivity) hcunn (by linarith) ?_ ?_ ?_
      · intro z
        refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
        rw [Pi.norm_single, norm_one, mul_one]
        exact hdfG k z
      · intro z; simpa only [norm_star] using hbndu z
      · exact ((hfc.clm_apply continuous_const).mul (huc.star)).aestronglyMeasurable
    have hIu : Integrable (fun x => fderiv ℝ (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) x
        (Pi.single k Complex.I) * star (bmPotential h x)) := by
      refine hIntProd (c := 2 * (n:ℝ) * (Kdd + Kdbd)) (d := cu)
        (p := 2*(n:ℝ) + 1) (q := 2*(n:ℝ) - 1) (by positivity) hcunn (by linarith) ?_ ?_ ?_
      · intro z
        refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
        rw [Pi.norm_single, Complex.norm_I, mul_one]
        exact hdfG k z
      · intro z; simpa only [norm_star] using hbndu z
      · exact ((hfc.clm_apply continuous_const).mul (huc.star)).aestronglyMeasurable
    have hfv_cont : ∀ v : Fin n → ℂ, Continuous (fun x : Fin n → ℂ =>
        fderiv ℝ (fun y => star (bmPotential h y)) x v) := by
      intro v
      have h1 : (fun x => fderiv ℝ (fun y => star (bmPotential h y)) x v)
          = fun x => (Complex.conjCLE : ℂ →L[ℝ] ℂ) (fderiv ℝ (bmPotential h) x v) := by
        funext x
        rw [show fderiv ℝ (fun y => star (bmPotential h y)) x
            = (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ (bmPotential h) x) from
          ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x (hu2'.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt).fderiv]
        rfl
      rw [h1]
      exact Complex.conjCLE.continuous.comp
        (hfc_u.clm_apply (continuous_const : Continuous fun _ : Fin n → ℂ => v))
    have h1v : Integrable (fun x => Work.CR.Flat.dCoord k (bmPotential h) x
        * fderiv ℝ (fun y => star (bmPotential h y)) x (Pi.single k (1 : ℂ))) := by
      refine hIntProd (c := Kdu) (d := 2 * (n:ℝ) * (Kdu + Kdub))
        (p := 2*(n:ℝ)) (q := 2*(n:ℝ)) (by positivity) (by positivity) (by linarith) ?_ ?_ ?_
      · intro z; exact hKdub k z
      · intro z
        rw [show fderiv ℝ (fun y => star (bmPotential h y)) z
            = (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ (bmPotential h) z) from
          ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp z
            (hu2'.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt).fderiv]
        refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
        rw [Pi.norm_single, norm_one, mul_one]
        refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
        have hnorm : ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ)‖ ≤ 1 := by
          refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun w => ?_
          rw [show (Complex.conjCLE : ℂ →L[ℝ] ℂ) w = star w from rfl, norm_star, one_mul]
        exact le_trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
          (by rw [one_mul]; exact hdfu z)
      · exact (hGcont.mul (hfv_cont _)).aestronglyMeasurable
    have hIv : Integrable (fun x => Work.CR.Flat.dCoord k (bmPotential h) x
        * fderiv ℝ (fun y => star (bmPotential h y)) x (Pi.single k Complex.I)) := by
      refine hIntProd (c := Kdu) (d := 2 * (n:ℝ) * (Kdu + Kdub))
        (p := 2*(n:ℝ)) (q := 2*(n:ℝ)) (by positivity) (by positivity) (by linarith) ?_ ?_ ?_
      · intro z; exact hKdub k z
      · intro z
        rw [show fderiv ℝ (fun y => star (bmPotential h y)) z
            = (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ (bmPotential h) z) from
          ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp z
            (hu2'.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt).fderiv]
        refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
        rw [Pi.norm_single, Complex.norm_I, mul_one]
        refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
        have hnorm : ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ)‖ ≤ 1 := by
          refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun w => ?_
          rw [show (Complex.conjCLE : ℂ →L[ℝ] ℂ) w = star w from rfl, norm_star, one_mul]
        exact le_trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
          (by rw [one_mul]; exact hdfu z)
      · exact (hGcont.mul (hfv_cont _)).aestronglyMeasurable
    have huv : Integrable (fun x => Work.CR.Flat.dCoord k (bmPotential h) x * star (bmPotential h x)) := by
      refine hIntProd (c := Kdu) (d := cu) (p := 2*(n:ℝ)) (q := 2*(n:ℝ) - 1)
        (by positivity) hcunn (by linarith) ?_ ?_ ?_
      · intro z; exact hKdub k z
      · intro z; simpa only [norm_star] using hbndu z
      · exact (hGcont.mul huc.star).aestronglyMeasurable
    have hIB := Work.CR.Flat.integral_mul_dbarCoord_eq_neg k hG1 hv1 h1u hIu h1v hIv huv
    have hL : (∫ z : Fin n → ℂ, Work.CR.Flat.dCoord k (bmPotential h) z
          * Work.CR.Flat.dbarCoord k (fun y => star (bmPotential h y)) z)
        = ∫ z : Fin n → ℂ, ((‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2 : ℝ) : ℂ) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only []
      rw [dbarCoord_star k (bmPotential h) z
        (hu2'.contDiffAt.differentiableAt (by norm_num))]
      simpa [Complex.normSq_eq_norm_sq] using
        Complex.mul_conj (Work.CR.Flat.dCoord k (bmPotential h) z)
    have hL' : (∫ z : Fin n → ℂ, Work.CR.Flat.dCoord k (bmPotential h) z
          * Work.CR.Flat.dbarCoord k (fun y => star (bmPotential h y)) z)
        = ((∫ z : Fin n → ℂ, ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2 : ℝ) : ℂ) := by
      rw [hL]
      exact integral_ofReal
    rw [hL'] at hIB
    have := congrArg Complex.re hIB
    simpa using this
  -- ============================== assembly ==============================
  have hsum_in : (∑ k : Fin n, ∫ z : Fin n → ℂ, Work.CR.Flat.dbarCoord k
        (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z * star (bmPotential h z))
      = ∫ z : Fin n → ℂ, (∑ k : Fin n, Work.CR.Flat.dbarCoord k
          (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z) * star (bmPotential h z) := by
    rw [← MeasureTheory.integral_finsetSum]
    · congr 1
      funext z
      rw [Finset.sum_mul]
    · intro k _
      refine hIntProd (c := Kdbd) (d := cu) (p := 2*(n:ℝ) + 1) (q := 2*(n:ℝ) - 1)
        (by positivity) hcunn (by linarith) ?_ ?_ ?_
      · intro z; exact hKdbdb k k z
      · intro z; simpa only [norm_star] using hbndu z
      · have hcont1 : Continuous (fun x : Fin n → ℂ => Work.CR.Flat.dbarCoord k
            (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) x) :=
          continuous_dbarCoord_of_contDiff (contDiff_one_dCoord hu2 k) k
        exact (hcont1.mul (continuous_star.comp hu2'.continuous)).aestronglyMeasurable
  have hflat : ∀ z : Fin n → ℂ, (∑ k : Fin n, Work.CR.Flat.dbarCoord k
      (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z)
        = (1/4) * flatLap (bmPotential h) z := by
    intro z
    have hcom : ∀ k : Fin n, Work.CR.Flat.dbarCoord k
          (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z
        = Work.CR.Flat.dCoord k (fun y => Work.CR.Flat.dbarCoord k (bmPotential h) y) z :=
      fun k => Work.CR.Flat.Cauchy.dbarCoord_dCoord_comm k k (bmPotential h) z
        (hu2.contDiffAt)
    simp only [hcom, flatLap_apply]
    ring
  have hIntFlat : Integrable (fun z : Fin n → ℂ => flatLap (bmPotential h) z
      * star (bmPotential h z)) := by
    have hpt : ∀ z : Fin n → ℂ, ‖flatLap (bmPotential h) z‖
        ≤ (4 * ((n:ℝ) * Kddb)) * (1 + ‖z‖) ^ (-(2*(n:ℝ) + 1)) := by
      intro z
      rw [flatLap_apply]
      rw [norm_mul]
      rw [show ‖(4:ℂ)‖ = 4 from by norm_num]
      have h2 : ‖∑ k : Fin n, Work.CR.Flat.dCoord k
            (fun w => Work.CR.Flat.dbarCoord k (bmPotential h) w) z‖
          ≤ (n:ℝ) * Kddb * (1 + ‖z‖) ^ (-(2*(n:ℝ) + 1)) := by
        refine (norm_sum_le _ _).trans ?_
        calc ∑ k : Fin n, ‖Work.CR.Flat.dCoord k
              (fun w => Work.CR.Flat.dbarCoord k (bmPotential h) w) z‖
            ≤ ∑ _k : Fin n, Kddb * (1 + ‖z‖) ^ (-(2*(n:ℝ) + 1)) :=
              Finset.sum_le_sum fun k _ => hKddbb k k z
          _ = (n:ℝ) * Kddb * (1 + ‖z‖) ^ (-(2*(n:ℝ) + 1)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              push_cast
              ring
      calc 4 * ‖∑ k : Fin n, Work.CR.Flat.dCoord k
            (fun w => Work.CR.Flat.dbarCoord k (bmPotential h) w) z‖
          ≤ 4 * ((n:ℝ) * Kddb * (1 + ‖z‖) ^ (-(2*(n:ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ = (4 * ((n:ℝ) * Kddb)) * (1 + ‖z‖) ^ (-(2*(n:ℝ) + 1)) := by ring
    have hcont_flat : Continuous (fun z : Fin n → ℂ => flatLap (bmPotential h) z) := by
      simp only [flatLap_apply]
      refine continuous_const.mul (continuous_finsetSum Finset.univ fun k _ => ?_)
      exact continuous_dCoord_of_contDiff_one
        (Work.NN.Core.contDiff_one_dbarCoord hu2 k) k
    exact hIntProd (c := 4 * ((n:ℝ) * Kddb)) (d := cu) (p := 2*(n:ℝ) + 1) (q := 2*(n:ℝ) - 1)
      (by positivity) hcunn (by linarith) hpt (fun z => by simpa only [norm_star] using hbndu z)
      ((hcont_flat.mul (hu2'.continuous.star)).aestronglyMeasurable)
  calc ∑ k : Fin n, (∫ z : Fin n → ℂ, ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2 : ℝ)
      = ∑ k : Fin n, -(∫ z : Fin n → ℂ, Work.CR.Flat.dbarCoord k
            (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z
          * star (bmPotential h z)).re := Finset.sum_congr rfl fun k _ => hkey k
    _ = -(∑ k : Fin n, (∫ z : Fin n → ℂ, Work.CR.Flat.dbarCoord k
            (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z
          * star (bmPotential h z)).re) := by rw [Finset.sum_neg_distrib]
    _ = -(∑ k : Fin n, ∫ z : Fin n → ℂ, Work.CR.Flat.dbarCoord k
            (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z
          * star (bmPotential h z)).re := by
        congr 1
        exact (map_sum Complex.reCLM (fun k : Fin n => (∫ z : Fin n → ℂ, Work.CR.Flat.dbarCoord k
            (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z * star (bmPotential h z))) Finset.univ).symm
    _ = -(∫ z : Fin n → ℂ, (∑ k : Fin n, Work.CR.Flat.dbarCoord k
            (fun y => Work.CR.Flat.dCoord k (bmPotential h) y) z)
          * star (bmPotential h z)).re := by rw [hsum_in]
    _ = -(∫ z : Fin n → ℂ, ((1/4) * flatLap (bmPotential h) z)
          * star (bmPotential h z)).re := by
        congr 1
        congr 1
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [hflat z]
    _ = -(1/4) * (∫ z : Fin n → ℂ, flatLap (bmPotential h) z * star (bmPotential h z)).re := by
        rw [show (∫ z : Fin n → ℂ, ((1/4) * flatLap (bmPotential h) z) * star (bmPotential h z))
            = (1/4) * (∫ z : Fin n → ℂ, flatLap (bmPotential h) z * star (bmPotential h z)) from by
          rw [show (fun z : Fin n → ℂ => ((1/4) * flatLap (bmPotential h) z) * star (bmPotential h z))
              = fun z => (1/4) * (flatLap (bmPotential h) z * star (bmPotential h z)) from
            by funext z; ring]
          rw [MeasureTheory.integral_const_mul]]
        rw [Complex.mul_re]
        norm_num
    _ = -(1/4) * (∫ z : Fin n → ℂ, (bmPotential h z * star (flatLap (bmPotential h) z))).re := by
        have hconj : (∫ z : Fin n → ℂ, flatLap (bmPotential h) z * star (bmPotential h z))
            = star (∫ z : Fin n → ℂ, bmPotential h z * star (flatLap (bmPotential h) z)) := by
          calc ∫ z : Fin n → ℂ, flatLap (bmPotential h) z * star (bmPotential h z)
              = ∫ z : Fin n → ℂ, star (bmPotential h z * star (flatLap (bmPotential h) z)) := by
                refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
                simp only []
                rw [star_mul, star_star]
            _ = star (∫ z : Fin n → ℂ,
                  bmPotential h z * star (flatLap (bmPotential h) z)) := integral_conj
        rw [hconj]
        have hc : (star (∫ z : Fin n → ℂ, bmPotential h z * star (flatLap (bmPotential h) z))).re
            = (∫ z : Fin n → ℂ, bmPotential h z * star (flatLap (bmPotential h) z)).re :=
          Complex.conj_re _
        rw [hc]
    _ = -(1 / 4) * ∫ z : Fin n → ℂ,
          (bmPotential h z * star (flatLap (bmPotential h) z)).re := by
        have hptF : (fun z : Fin n → ℂ => bmPotential h z * star (flatLap (bmPotential h) z))
            = fun z => star (flatLap (bmPotential h) z * star (bmPotential h z)) := by
          funext z
          rw [star_mul, star_star]
        have hmeasF : AEStronglyMeasurable
            (fun z : Fin n → ℂ => bmPotential h z * star (flatLap (bmPotential h) z)) volume := by
          rw [hptF]
          exact hIntFlat.aestronglyMeasurable.star
        have hIntFlat' : Integrable (fun z : Fin n → ℂ =>
            bmPotential h z * star (flatLap (bmPotential h) z)) :=
          hIntFlat.mono hmeasF (Filter.Eventually.of_forall fun z => by
            rw [norm_mul, norm_mul, norm_star, norm_star]
            exact le_of_eq (mul_comm (‖bmPotential h z‖) (‖flatLap (bmPotential h) z‖)))
        have hre := (integral_re hIntFlat').symm
        exact congrArg (fun t : ℝ => -(1/4) * t) hre


end Work.NN.Core
