/-
Assembly of Proposition 2.4 of Shankar--Yuan (the a priori *doubling inequality* for `Delta u`)
in dimension `n = 4`.

The mathematical content: for a smooth solution `u` of `sigma_2(D^2u) = 1` with `Delta u > 0` on a
neighbourhood of `closedBall 0 3`, one has, with `Gamma` a bound for `|u|` and `|Du|` on `closedBall 0 3`
and `M = sup_{ball 0 1} Delta u`,

  `Delta u z <= C * exp (C * Gamma^2) * M`  for `z` in `ball 0 2`.

This file contains the *assembly*: the case analysis at a maximum point of the test function
`P_{alpha beta gamma}`, the choice of the constants `alpha = gamma^4/Gamma`, `beta = gamma^6/Gamma^2`,
`gamma = 10^{-6}`, and the final translation into the doubling inequality.
-/
import ChallengeDeps
import Submission.Prop24
import Submission.Commons.Analysis.Sigma2.degenerate_case_bound_pos
import Submission.Commons.Analysis.Sigma2.regular_case_bound_sharp
import Submission.Commons.Analysis.Sigma2.regular_case_contradiction
import Submission.Commons.Analysis.Sigma2.linearized_lower_large_four
import Submission.Commons.Analysis.Sigma2.largest_ge_average_four
import Submission.Commons.Analysis.Sigma2.f0_lambda0_sq_ge_sigma1_div_sixteen
import Submission.Commons.Analysis.Sigma2.f3_lambda3_sq_lower_in_degenerate_case
import Submission.Commons.Analysis.Sigma2.sharp_minEigen_four
import Submission.Commons.Analysis.Sigma2.sigma1_sq_ge_two
import Submission.Commons.Analysis.Sigma2.maxP_regular_of_eps
import Submission.Commons.Analysis.Sigma2.maxP_degenerate_of_eps
import Submission.Commons.Analysis.Calculus.ContinuousOn.sSup_image_bounds
import Submission.Commons.Analysis.Calculus.Laplacian.continuousOn_laplacian
import Submission.Commons.Analysis.Calculus.FDeriv.continuousOn_fderiv

open HessianEstimates
open Commons.Analysis.Calculus.FDeriv
open Commons.Analysis.Sigma2
open Commons.Analysis.InnerProductSpace
open Commons.Analysis.Calculus.ContinuousOn
open Laplacian Metric
open scoped BigOperators RealInnerProductSpace Topology

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- The (fixed) small dimensional constant `gamma = 10^{-6}` used in Proposition 2.4. -/
local notation "γ₀" => (1 / 10 ^ 6 : ℝ)

/-! ## The test function is independent of the orthonormal basis -/

theorem QF_eq_norm_sq (v : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (u : ℝ⁴ → ℝ) (z : ℝ⁴) :
    QF v u z = ‖fderiv ℝ u z‖ ^ 2 := by
  simp only [QF]
  rw [norm_sq_eq_sum_sq_apply (v := v)]

theorem QF_congr (v w : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (u : ℝ⁴ → ℝ) :
    QF v u = QF w u := by
  funext z
  rw [QF_eq_norm_sq, QF_eq_norm_sq]

theorem P0_congr (v w : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (u : ℝ⁴ → ℝ) (c α β : ℝ) :
    P0 v u c α β = P0 w u c α β := by
  funext z
  simp only [P0]
  rw [show QF v u z = QF w u z from congrFun (QF_congr v w u) z]

theorem Pfun_congr (v w : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (u : ℝ⁴ → ℝ) (c α β γ : ℝ) :
    Pfun v u c α β γ = Pfun w u c α β γ := by
  funext z
  simp only [Pfun]
  rw [show QF v u z = QF w u z from congrFun (QF_congr v w u) z]

/-! ## Elementary bounds on the pieces of the test function -/

/-- The `x · Du - u` term is bounded by `4 Gamma` under the standing bounds. -/
theorem abs_WF_le {u : ℝ⁴ → ℝ} {Γ : ℝ} {z : ℝ⁴} (hΓ : 4 ≤ Γ)
    (huz : |u z| ≤ Γ - 4) (hdz : ‖fderiv ℝ u z‖ ≤ Γ - 4) (hz : ‖z‖ ≤ 3) :
    |WF u z| ≤ 4 * Γ := by
  have h4 : (0 : ℝ) ≤ Γ - 4 := by linarith
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have h1 : ‖(fderiv ℝ u z) z‖ ≤ ‖fderiv ℝ u z‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
  rw [Real.norm_eq_abs] at h1
  have h2 : |(fderiv ℝ u z) z| ≤ (Γ - 4) * 3 := le_trans h1 (mul_le_mul hdz hz hz0 h4)
  rw [WF]
  have h3 : |(fderiv ℝ u z) z - u z| ≤ |(fderiv ℝ u z) z| + |u z| := abs_sub _ _
  linarith

/-- The `|Du|^2` term is nonnegative. -/
theorem QF_nonneg (v : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (u : ℝ⁴ → ℝ) (z : ℝ⁴) :
    0 ≤ QF v u z :=
  Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- The `|Du|^2` term is bounded by `Gamma^2`. -/
theorem QF_le_sq {u : ℝ⁴ → ℝ} {Γ : ℝ} {z : ℝ⁴} (hΓ : 4 ≤ Γ)
    (hdz : ‖fderiv ℝ u z‖ ≤ Γ - 4) (v : OrthonormalBasis (Fin 4) ℝ ℝ⁴) :
    QF v u z ≤ Γ ^ 2 := by
  simpa only [QF] using sum_sq_fderiv_le (v := v) (x := z) hΓ hdz

/-! ## The "trivial" case of the maximum principle: `bar b <= gamma^{-1}` -/

theorem Pfun_le_trivial {u : ℝ⁴ → ℝ} {Γ c α β γ : ℝ} {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴}
    {x : ℝ⁴} (hΓ : 4 ≤ Γ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hux : |u x| ≤ Γ - 4) (hdx : ‖fderiv ℝ u x‖ ≤ Γ - 4) (hx3 : ‖x‖ ≤ 3)
    (hrho : 0 < rhoF x) (hrho9 : rhoF x ≤ 9)
    (hb : barF u c x ≤ γ⁻¹) :
    Pfun v u c α β γ x ≤ 2 * Real.log 9 + 4 * α * Γ + (β / 2) * Γ ^ 2 + Real.log γ⁻¹ := by
  have hγinv : (0 : ℝ) < γ⁻¹ := inv_pos.mpr hγ
  have hlog : Real.log (max (barF u c x) γ⁻¹) = Real.log γ⁻¹ := by
    rw [max_eq_right hb]
  have h1 : 2 * Real.log (rhoF x) ≤ 2 * Real.log 9 := by
    have := Real.log_le_log hrho hrho9
    linarith
  have h2 : α * WF u x ≤ α * (4 * Γ) :=
    mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (abs_WF_le hΓ hux hdx hx3)) hα
  have h3 : (β / 2) * QF v u x ≤ (β / 2) * Γ ^ 2 :=
    mul_le_mul_of_nonneg_left (QF_le_sq hΓ hdx v) (by linarith)
  simp only [Pfun, hlog]
  linarith

/-! ## The numerical comparison in the trivial case -/

theorem trivial_bound_le {Γ α β : ℝ} (hΓ : 4 ≤ Γ) (hαΓ : α * Γ ≤ 1) (hβΓ2 : β * Γ ^ 2 ≤ 1) :
    2 * Real.log 9 + 4 * α * Γ + (β / 2) * Γ ^ 2 + Real.log γ₀⁻¹
      ≤ 12000000 + Real.log (Γ ^ 2 * (γ₀ ^ 8)⁻¹) := by
  have h1 : Real.log 9 ≤ 9 := Real.log_le_self (by norm_num)
  have h2 : 4 * α * Γ ≤ 4 := by nlinarith [hαΓ]
  have h3 : (β / 2) * Γ ^ 2 ≤ 1 / 2 := by nlinarith [hβΓ2]
  have h4 : Real.log γ₀⁻¹ ≤ 11943000 := by
    have hγ : γ₀⁻¹ = (10 : ℝ) ^ 6 := by norm_num
    rw [hγ, Real.log_pow]
    have : Real.log 10 ≤ 10 := Real.log_le_self (by norm_num)
    push_cast
    linarith
  have h5 : (0 : ℝ) ≤ Real.log (Γ ^ 2 * (γ₀ ^ 8)⁻¹) := by
    apply Real.log_nonneg
    have h6 : (1 : ℝ) ≤ Γ ^ 2 := by nlinarith
    have h7 : (1 : ℝ) ≤ (γ₀ ^ 8)⁻¹ := by norm_num
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Γ ^ 2 * (γ₀ ^ 8)⁻¹ := by
          exact mul_le_mul h6 h7 (by norm_num) (by linarith)
  linarith

/-! ## The value of `Pfun` at the maximum point in terms of `rho^2 b` -/

theorem Pfun_le_pieces {u : ℝ⁴ → ℝ} {Γ M α β b rho : ℝ}
    {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴} {x : ℝ⁴}
    (hΓ : 4 ≤ Γ) (hαnn : 0 ≤ α) (hβnn : 0 ≤ β)
    (hux : |u x| ≤ Γ - 4) (hdx : ‖fderiv ℝ u x‖ ≤ Γ - 4) (hx3 : ‖x‖ ≤ 3)
    (hb : b = barF u (Real.log M) x) (hrho : rho = rhoF x) (hγlt : γ₀⁻¹ < b) :
    Pfun v u (Real.log M) α β γ₀ x
      ≤ 2 * Real.log rho + Real.log b + 4 * α * Γ + (β / 2) * Γ ^ 2 := by
  have h1 := abs_WF_le (u := u) (Γ := Γ) (z := x) hΓ hux hdx hx3
  have h2 := QF_le_sq (u := u) (Γ := Γ) (z := x) hΓ hdx v
  have hγlt' : γ₀⁻¹ < barF u (Real.log M) x := by rw [← hb]; exact hγlt
  have hbm : max (barF u (Real.log M) x) γ₀⁻¹ = barF u (Real.log M) x :=
    max_eq_left (le_of_lt hγlt')
  have h3 : α * WF u x ≤ α * (4 * Γ) :=
    mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) h1) hαnn
  have h4 : (β / 2) * QF v u x ≤ (β / 2) * Γ ^ 2 :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  simp only [Pfun, hbm]
  rw [← hrho, ← hb]
  linarith

/-! ## `bar b <= S` -/

theorem barF_le_sum_lam {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} {x : ℝ⁴} {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴}
    {lam : Fin 4 → ℝ} {S M : ℝ} (hx : x ∈ s) (hΔ : ∀ y ∈ s, 0 < (Δ u) y)
    (hMpos : 0 < M) (hMone : 1 ≤ M) (hbγ : γ₀⁻¹ < barF u (Real.log M) x)
    (hdiag : ∀ i j : Fin 4, (iteratedFDeriv ℝ 2 u x) ![v i, v j] = if i = j then lam i else 0)
    (hSdef : S = ∑ t : Fin 4, lam t) :
    barF u (Real.log M) x ≤ S := by
  have hSpos : 0 < S := by rw [hSdef, ← laplacian_eq_sum_lam hdiag]; exact hΔ x hx
  have hΔx : (Δ u) x = S := by rw [hSdef]; exact laplacian_eq_sum_lam hdiag
  have hbpos : 0 < barF u (Real.log M) x := lt_trans (by norm_num : (0:ℝ) < γ₀⁻¹) hbγ
  have hb_eq : barF u (Real.log M) x = Real.log (S / M) := by
    rw [barF, bF, hΔx, Real.log_div (ne_of_gt hSpos) (ne_of_gt hMpos)]
  rw [hb_eq]
  have h2 : S / M ≤ S := by
    rw [div_le_iff₀ hMpos]; nlinarith [hSpos, hMone]
  calc Real.log (S / M) ≤ Real.log S := Real.log_le_log (by positivity) h2
    _ ≤ S := Real.log_le_self (le_of_lt hSpos)

/-! ## The degenerate case of the maximum principle -/

theorem hC1_of_last {S : ℝ} {lam : Fin 4 → ℝ}
    (hnn : ∀ i : Fin 4, 0 ≤ S - lam i)
    (hlast : ((1 - 1 / Real.sqrt 2) / 16) * S ^ 3 ≤ (S - lam 3) * (lam 3) ^ 2) :
    ((1 - 1 / Real.sqrt 2) / 16) * S ^ 3 ≤ ∑ i : Fin 4, (S - lam i) * (lam i) ^ 2 := by
  refine le_trans hlast ?_
  exact Finset.single_le_sum (f := fun i : Fin 4 => (S - lam i) * (lam i) ^ 2)
    (fun i _ => mul_nonneg (hnn i) (sq_nonneg _)) (Finset.mem_univ 3)


/-! ## Auxiliary numerical lemma for the degenerate case -/

theorem one_sub_inv_sqrt_two_pos : (0 : ℝ) < 1 - 1 / Real.sqrt 2 := by
  have hlt : (1 : ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two
  have hpos : (0 : ℝ) < Real.sqrt 2 := by linarith
  have h : (1 : ℝ) / Real.sqrt 2 < 1 := by rw [div_lt_iff₀ hpos]; simpa using hlt
  linarith

theorem Kd_le : 3240 * 16 / (1 - 1 / Real.sqrt 2) ≤ 207360 := by
  have hden : (0 : ℝ) < 1 - 1 / Real.sqrt 2 := one_sub_inv_sqrt_two_pos
  rw [div_le_iff₀ hden]
  have h1 : (4 : ℝ) / 3 ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h2 : 1 / Real.sqrt 2 ≤ (3 : ℝ) / 4 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4 / 3) h1
    simpa using this
  nlinarith

theorem Pfun_max_bound
    {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s) (hsub : closedBall 0 3 ⊆ s)
    (hu : ContDiffOn ℝ 4 u s) (hσ2 : ∀ y ∈ s, σ₂ (H u s y) = 1)
    (hΔ : ∀ y ∈ s, 0 < (Δ u) y)
    {Γ M α β : ℝ} (hΓ : 4 ≤ Γ)
    (huΓ : ∀ z ∈ closedBall 0 3, |u z| ≤ Γ - 4)
    (hdΓ : ∀ z ∈ closedBall 0 3, ‖fderiv ℝ u z‖ ≤ Γ - 4)
    (hMpos : 0 < M) (hMone : 1 ≤ M) (hMle : ∀ z ∈ ball 0 1, (Δ u) z ≤ M)
    (hαpos : 0 < α) (hαdef : α = γ₀ ^ 4 / Γ)
    (hβpos : 0 < β) (hβdef : β = γ₀ ^ 6 / Γ ^ 2)
    {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴} {x : ℝ⁴} (hx : x ∈ ball 0 3)
    (hmax : ∀ y ∈ ball 0 3, Pfun v u (Real.log M) α β γ₀ y ≤ Pfun v u (Real.log M) α β γ₀ x) :
    Pfun v u (Real.log M) α β γ₀ x ≤ 12000000 + Real.log (Γ ^ 2 * (γ₀ ^ 8)⁻¹) := by
  have hΓpos : 0 < Γ := by linarith
  have hΓ1 : (1 : ℝ) ≤ Γ := by linarith
  have hΓ2 : (16 : ℝ) ≤ Γ ^ 2 := by nlinarith
  have hαnn : 0 ≤ α := le_of_lt hαpos
  have hβnn : 0 ≤ β := le_of_lt hβpos
  have hx3 : ‖x‖ < 3 := mem_ball_zero_iff.mp hx
  have hx3le : ‖x‖ ≤ 3 := le_of_lt hx3
  have hxs : x ∈ s := hsub (ball_subset_closedBall hx)
  have hux : |u x| ≤ Γ - 4 := huΓ x (ball_subset_closedBall hx)
  have hdx : ‖fderiv ℝ u x‖ ≤ Γ - 4 := hdΓ x (ball_subset_closedBall hx)
  -- numeric consequences of the definitions of `alpha`, `beta`
  have hαΓeq : α * Γ = γ₀ ^ 4 := by rw [hαdef]; field_simp
  have hβΓ2eq : β * Γ ^ 2 = γ₀ ^ 6 := by rw [hβdef]; field_simp
  have hαΓ : α * Γ ≤ 1 := by rw [hαΓeq]; norm_num
  have hβΓ2 : β * Γ ^ 2 ≤ 1 := by rw [hβΓ2eq]; norm_num
  have hβ2 : β * Γ ^ 2 ≤ 1 / 100 := by rw [hβΓ2eq]; norm_num
  have hβΓ : β * Γ ≤ α / 4 := by
    have h1 : β * Γ = γ₀ ^ 6 / Γ := by rw [hβdef]; field_simp
    have h2 : α / 4 = γ₀ ^ 4 / (4 * Γ) := by rw [hαdef]; field_simp
    rw [h1, h2, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : 4 * γ₀ ^ 6 ≤ γ₀ ^ 4 := by
      have h4 : γ₀ ^ 4 * (4 * γ₀ ^ 2) ≤ γ₀ ^ 4 * 1 :=
        mul_le_mul_of_nonneg_left (by norm_num : 4 * γ₀ ^ 2 ≤ 1) (by positivity)
      nlinarith [h4]
    nlinarith [h3, hΓpos]
  have hα2 : α ^ 2 ≤ β / 200 := by
    have h1 : α ^ 2 = γ₀ ^ 8 / Γ ^ 2 := by rw [hαdef]; field_simp
    have h2 : β / 200 = γ₀ ^ 6 / (200 * Γ ^ 2) := by rw [hβdef]; field_simp
    rw [h1, h2, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : 200 * γ₀ ^ 8 ≤ γ₀ ^ 6 := by
      have h4 : γ₀ ^ 6 * (200 * γ₀ ^ 2) ≤ γ₀ ^ 6 * 1 :=
        mul_le_mul_of_nonneg_left (by norm_num : 200 * γ₀ ^ 2 ≤ 1) (by positivity)
      nlinarith [h4]
    nlinarith [h3, sq_nonneg Γ]
  -- the two "trivial" cases
  have htriv_of : barF u (Real.log M) x ≤ γ₀⁻¹ →
      Pfun v u (Real.log M) α β γ₀ x ≤ 12000000 + Real.log (Γ ^ 2 * (γ₀ ^ 8)⁻¹) := by
    intro hb
    have htriv := Pfun_le_trivial (v := v) (c := Real.log M) (x := x) (γ := γ₀)
      hΓ hαnn hβnn (by norm_num : (0 : ℝ) < γ₀) hux hdx hx3le
      (by rw [rhoF]; nlinarith [norm_nonneg x, hx3])
      (by rw [rhoF]; nlinarith [sq_nonneg ‖x‖]) hb
    exact le_trans htriv (trivial_bound_le hΓ hαΓ hβΓ2)
  by_cases hbγ : barF u (Real.log M) x ≤ γ₀⁻¹
  · exact htriv_of hbγ
  · push_neg at hbγ
    by_cases hx1 : ‖x‖ < 1
    · refine htriv_of ?_
      have hb0 : barF u (Real.log M) x ≤ 0 := by
        simp only [barF, bF]
        have h := Real.log_le_log (hΔ x hxs) (hMle x (mem_ball_zero_iff.mpr hx1))
        linarith
      linarith [hb0]
    · push_neg at hx1
      have hbγ' : γ₀⁻¹ < barF u (Real.log M) x := hbγ
      have hbpos : 0 < barF u (Real.log M) x := lt_trans (by norm_num : (0 : ℝ) < γ₀⁻¹) hbγ
      -- local maximum of the test function
      have hcont : ContinuousAt (barF u (Real.log M)) x := by
        have h1 : ContinuousAt (fun z => (Δ u) z) x :=
          (Commons.Analysis.Calculus.Laplacian.continuousOn_laplacian hs
            (hu.of_le (by norm_num))).continuousAt (hs.mem_nhds hxs)
        have h2 : ContinuousAt (bF u) x := h1.log (ne_of_gt (hΔ x hxs))
        show ContinuousAt (fun z => bF u z - Real.log M) x
        exact h2.sub continuousAt_const
      have hPfunmax : IsLocalMax (Pfun v u (Real.log M) α β γ₀) x :=
        Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hx) (fun y hy => hmax y hy)
      -- diagonalise the Hessian at `x`
      obtain ⟨w, lam, hdiag, hmono⟩ := exists_diagonal_basis hs (hu.of_le (by norm_num)) hxs
      have hPfunmaxw : IsLocalMax (Pfun w u (Real.log M) α β γ₀) x := by
        rw [Pfun_congr w v u (Real.log M) α β γ₀]; exact hPfunmax
      have hP0max : IsLocalMax (P0 w u (Real.log M) α β) x :=
        isLocalMax_P0_of_Pfun (v := w) (c := Real.log M) hcont hbγ' hPfunmaxw
      have hrel : ∀ i : Fin 4, fderiv ℝ (bF u) x (w i) / barF u (Real.log M) x
          = 4 * ⟪x, w i⟫ / (9 - ‖x‖ ^ 2) - α * ⟪x, w i⟫ * lam i
            - β * (fderiv ℝ u x) (w i) * lam i :=
        fun i => first_deriv_relation_at_max (v := w) (u := u) (s := s) (x := x) (lam := lam)
          (c := Real.log M) (α := α) (β := β) (γ := γ₀) hs hxs hu hΔ hdiag hPfunmaxw hx3 hbγ' hbpos i
      set S : ℝ := ∑ t : Fin 4, lam t with hSdef
      set b : ℝ := barF u (Real.log M) x with hbdef
      set rho : ℝ := rhoF x with hrhodef
      set D : ℝ := ∑ i : Fin 4, (S - lam i) * (fderiv ℝ (bF u) x (w i)) ^ 2 with hDdef
      set ε : ℝ := (2 / 9 : ℝ) * (1 / 2 + lam 3 / S) with hεdef
      have hSpos : 0 < S := by
        rw [hSdef, ← laplacian_eq_sum_lam hdiag]; exact hΔ x hxs
      have hpair : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1 :=
        pair_sum_lam_eq_one hs (hu.of_le (by norm_num)) hσ2 hxs hdiag
      have hfs : ∀ i : Fin 4, 0 < S - lam i := by
        intro i; rw [hSdef]; exact linearized_pos_four lam hmono hpair hSpos i
      have hfsnn : ∀ i : Fin 4, 0 ≤ S - lam i := fun i => le_of_lt (hfs i)
      have hfs3 : (∑ i : Fin 4, (S - lam i)) = 3 * S := by rw [hSdef]; exact sum_S_sub_lam
      have hlarge : S / 4 ≤ lam 0 := by rw [hSdef]; exact largest_ge_average_four lam hmono
      have hf0 : S / 16 ≤ (S - lam 0) * (lam 0) ^ 2 := by
        rw [hSdef]; exact f0_lambda0_sq_ge_sigma1_div_sixteen lam hmono hpair hSpos
      have hklow : ∀ i : Fin 4, i ≠ 0 → (1 - 1 / Real.sqrt 2) * S ≤ S - lam i := by
        intro i hi; rw [hSdef]; exact linearized_lower_large_four lam hmono hpair hSpos i hi
      have hlam0 : 0 < lam 0 := by linarith [hlarge, hSpos]
      have hS2 : 2 ≤ S ^ 2 := by rw [hSdef]; exact sigma1_sq_ge_two lam hpair
      have hρpos : 0 < rho := by
        rw [hrhodef]; simp only [rhoF]; nlinarith [norm_nonneg x, hx3]
      have hρ9 : rho < 9 := by rw [hrhodef]; simp only [rhoF]; nlinarith [norm_nonneg x]
      have hρle9 : rho ≤ 9 := le_of_lt hρ9
      have h9rho : (9 : ℝ) - ‖x‖ ^ 2 = rho := by rw [hrhodef]; rfl
      have hbpos' : 0 < b := by rw [hbdef]; exact hbpos
      have hγlt_b : γ₀⁻¹ < b := by rw [hbdef]; exact hbγ
      have hbS : b ≤ S := barF_le_sum_lam (u := u) (s := s) (x := x) (v := w) (lam := lam)
        hxs hΔ hMpos hMone (by rw [← hbdef]; exact hbγ) hdiag hSdef
      have hDnn : 0 ≤ D := by
        rw [hDdef]
        exact Finset.sum_nonneg (fun i _ => mul_nonneg (hfsnn i) (sq_nonneg _))
      have hmax1 : ∀ i : Fin 4, fderiv ℝ (bF u) x (w i) / b
          = 4 * (⟪x, w i⟫) / rho - α * (⟪x, w i⟫) * lam i
            - β * ((fderiv ℝ u x) (w i)) * lam i := by
        intro i; rw [hbdef, hrhodef]; exact hrel i
      -- the maximum principle inequality, sharp form
      have hmeps := max_ineq_eps (v := w) (u := u) (s := s) (x := x) (lam := lam)
        (c := Real.log M) (α := α) (β := β) hs hxs hu hσ2 hΔ hdiag hmono hP0max hx3 hbpos
      rw [← hSdef, ← hbdef, h9rho, ← hDdef, ← hεdef] at hmeps
      have huxc : ∀ i : Fin 4, |⟪x, w i⟫| ≤ 3 := fun i => abs_coord_le_three hx3 i
      have hu1 : ∀ i : Fin 4, |(fderiv ℝ u x) (w i)| ≤ Γ := fun i => abs_fderiv_le hΓ hdx i
      by_cases hdeg : lam 3 ≤ -S / 4
      · -- degenerate case
        have hεnn : 0 ≤ ε := by
          rw [hεdef]
          have hsharp := sharp_minEigen_four lam hmono hpair hSpos
          have hts : -(1 / 2 : ℝ) < lam 3 / S := by
            rw [lt_div_iff₀ hSpos]
            nlinarith [hsharp, abs_nonneg (lam 3), neg_le_abs (lam 3)]
          linarith
        have hmaxP := maxP_degenerate_of_eps hbpos' hDnn hεnn hmeps
        rw [hDdef] at hmaxP
        have hf3 := f3_lambda3_sq_lower_in_degenerate_case lam hmono hpair hSpos
          (by rw [← hSdef]; exact hdeg)
        rw [← hSdef] at hf3
        have hC1 : ((1 - 1 / Real.sqrt 2) / 16) * S ^ 3 ≤ ∑ i : Fin 4, (S - lam i) * (lam i) ^ 2 :=
          hC1_of_last hfsnn hf3
        have hbd := degenerate_case_bound_pos (S := S) (rho := rho) (b := b) (α := α) (β := β)
          (Γ := Γ) (lam := lam) (xc := fun i => ⟪x, w i⟫)
          (u := fun i => (fderiv ℝ u x) (w i)) (D1b := fun i => fderiv ℝ (bF u) x (w i))
          hbpos' hβpos hρpos hρ9 hSpos hΓ hαnn hα2 hβ2 huxc hu1 hfs3 hfsnn hC1 hmax1 hmaxP
        have hbdd : rho ^ 2 * S ^ 2 ≤ 3240 * 16 / (1 - 1 / Real.sqrt 2) / β := hbd
        have hρS : rho * S ≤ Real.sqrt (3240 * 16 / (1 - 1 / Real.sqrt 2) / β) := by
          rw [← Real.sqrt_sq (mul_nonneg (le_of_lt hρpos) (le_of_lt hSpos))]
          apply Real.sqrt_le_sqrt
          rw [mul_pow]
          exact hbdd
        have hρb : rho ^ 2 * b ≤ Γ ^ 2 * (γ₀ ^ 8)⁻¹ := by
          have h1 : rho ^ 2 * b ≤ rho ^ 2 * S := mul_le_mul_of_nonneg_left hbS (by positivity)
          have h2 : rho ^ 2 * S ≤ 9 * Real.sqrt (3240 * 16 / (1 - 1 / Real.sqrt 2) / β) := by
            have he : rho ^ 2 * S = rho * (rho * S) := by ring
            rw [he]
            exact mul_le_mul hρle9 hρS (mul_nonneg (le_of_lt hρpos) (le_of_lt hSpos))
              (by norm_num)
          have h3 : 9 * Real.sqrt (3240 * 16 / (1 - 1 / Real.sqrt 2) / β) ≤ Γ ^ 2 * (γ₀ ^ 8)⁻¹ := by
            have hKd_le : 3240 * 16 / (1 - 1 / Real.sqrt 2) ≤ 207360 := Kd_le
            have hγ6inv : (γ₀ ^ 6)⁻¹ = (10 : ℝ) ^ 36 := by norm_num
            have hγ8inv : (γ₀ ^ 8)⁻¹ = (10 : ℝ) ^ 48 := by norm_num
            have hKdnn : (0 : ℝ) ≤ 3240 * 16 / (1 - 1 / Real.sqrt 2) :=
              le_of_lt (div_pos (by norm_num) one_sub_inv_sqrt_two_pos)
            have hq : (0 : ℝ) ≤ 3240 * 16 / (1 - 1 / Real.sqrt 2) / β :=
              div_nonneg hKdnn (le_of_lt hβpos)
            have h1 : Real.sqrt (3240 * 16 / (1 - 1 / Real.sqrt 2) / β)
                ≤ 3240 * 16 / (1 - 1 / Real.sqrt 2) / β + 1 := by
              rw [Real.sqrt_le_left (by linarith : (0 : ℝ)
                ≤ 3240 * 16 / (1 - 1 / Real.sqrt 2) / β + 1)]
              nlinarith [hq]
            have hβ1 : (3240 * 16 / (1 - 1 / Real.sqrt 2)) / β
                = (3240 * 16 / (1 - 1 / Real.sqrt 2)) * Γ ^ 2 / γ₀ ^ 6 := by
              rw [hβdef]; field_simp
            have hstep : (3240 * 16 / (1 - 1 / Real.sqrt 2)) / β
                ≤ 207360 * Γ ^ 2 * (10 : ℝ) ^ 36 := by
              rw [hβ1]
              have heq : (3240 * 16 / (1 - 1 / Real.sqrt 2)) * Γ ^ 2 / γ₀ ^ 6
                  = (3240 * 16 / (1 - 1 / Real.sqrt 2)) * Γ ^ 2 * (10 : ℝ) ^ 36 := by
                rw [div_eq_mul_inv, hγ6inv]
              rw [heq]
              have hmul := mul_le_mul_of_nonneg_right hKd_le
                (show (0 : ℝ) ≤ Γ ^ 2 * (10 : ℝ) ^ 36 by positivity)
              nlinarith [hmul]
            have hlast : 9 * ((3240 * 16 / (1 - 1 / Real.sqrt 2)) / β) + 9
                ≤ Γ ^ 2 * (10 : ℝ) ^ 48 := by
              have hm := mul_le_mul_of_nonneg_left hstep (show (0 : ℝ) ≤ 9 by norm_num)
              nlinarith [hm, hΓ2]
            rw [hγ8inv]
            calc 9 * Real.sqrt (3240 * 16 / (1 - 1 / Real.sqrt 2) / β)
                ≤ 9 * (3240 * 16 / (1 - 1 / Real.sqrt 2) / β + 1) := by linarith [h1]
              _ = 9 * ((3240 * 16 / (1 - 1 / Real.sqrt 2)) / β) + 9 := by ring
              _ ≤ Γ ^ 2 * (10 : ℝ) ^ 48 := hlast
          linarith
        have hkey : 2 * Real.log rho + Real.log b + 4 * α * Γ + (β / 2) * Γ ^ 2
            ≤ Real.log (Γ ^ 2 * (γ₀ ^ 8)⁻¹) + 11943995 := by
          have h1 : 2 * Real.log rho + Real.log b = Real.log (rho ^ 2 * b) := by
            rw [Real.log_mul (by positivity) (ne_of_gt hbpos'), Real.log_pow]; ring
          rw [h1]
          have h2 := Real.log_le_log (by positivity) hρb
          have h3 : 4 * α * Γ + (β / 2) * Γ ^ 2 ≤ 5 := by
            have h4 : 4 * α * Γ = 4 * γ₀ ^ 4 := by rw [← hαΓeq]; ring
            have h5 : β * Γ ^ 2 = γ₀ ^ 6 := hβΓ2eq
            nlinarith [h4, h5]
          linarith
        exact le_trans (Pfun_le_pieces (v := v) hΓ hαnn hβnn hux hdx hx3le hbdef hrhodef hγlt_b)
          (by linarith [hkey])
      · -- regular case
        have hdeg' : -(S / 4) < lam 3 := by linarith [not_le.mp hdeg]
        have hε : 1 / 18 ≤ ε := by
          rw [hεdef]
          have hts : (-(1 / 4) : ℝ) < lam 3 / S := by
            rw [lt_div_iff₀ hSpos]; linarith
          linarith
        have hb36 : 36 ≤ b := by
          rw [hbdef]
          exact le_trans (by norm_num : (36 : ℝ) ≤ γ₀⁻¹) (le_of_lt hbγ)
        have hmaxP := maxP_regular_of_eps hb36 hDnn hε hmeps
        rw [hDdef] at hmaxP
        by_cases hx0 : 1 / 4 ≤ (⟪x, w 0⟫) ^ 2
        · have hbd : rho ^ 2 * b ≤ 11943936 / α ^ 2 := regular_case_bound_sharp
            (S := S) (rho := rho) (b := b) (α := α) (β := β)
            (Γ := Γ) (lam := lam) (xc := fun i => ⟪x, w i⟫)
            (u := fun i => (fderiv ℝ u x) (w i)) (D1b := fun i => fderiv ℝ (bF u) x (w i))
            hbpos' hρpos hρ9 hSpos hΓ hαpos hβnn hβΓ hbS hS2 huxc hu1 hfs3 hfsnn hlam0 hlarge
            hf0 hx0 hmax1 hmaxP
          have hkey : 2 * Real.log rho + Real.log b + 4 * α * Γ + (β / 2) * Γ ^ 2
              ≤ Real.log (Γ ^ 2 * (γ₀ ^ 8)⁻¹) + 11943995 := by
            have h1 : 2 * Real.log rho + Real.log b = Real.log (rho ^ 2 * b) := by
              rw [Real.log_mul (by positivity) (ne_of_gt hbpos'), Real.log_pow]; ring
            have h2 : Real.log (rho ^ 2 * b) ≤ Real.log (11943936 / α ^ 2) :=
              Real.log_le_log (by positivity) hbd
            have h3 : Real.log (11943936 / α ^ 2)
                = Real.log 11943936 + Real.log (Γ ^ 2 * (γ₀ ^ 8)⁻¹) := by
              have hαinv : (1 / α) ^ 2 = Γ ^ 2 * (γ₀ ^ 8)⁻¹ := by rw [hαdef]; field_simp
              have hαne : α ≠ 0 := ne_of_gt hαpos
              have hsplit : (11943936 : ℝ) / α ^ 2 = 11943936 * (1 / α) ^ 2 := by
                field_simp
              rw [hsplit, Real.log_mul (by norm_num) (by positivity),
                ← hαinv, Real.log_pow]
            have h4 : Real.log 11943936 ≤ 11943936 := Real.log_le_self (by norm_num)
            have h5 : 4 * α * Γ + (β / 2) * Γ ^ 2 ≤ 5 := by
              have h4' : 4 * α * Γ = 4 * γ₀ ^ 4 := by rw [← hαΓeq]; ring
              have h5' : β * Γ ^ 2 = γ₀ ^ 6 := hβΓ2eq
              nlinarith [h4', h5']
            linarith
          exact le_trans (Pfun_le_pieces (v := v) hΓ hαnn hβnn hux hdx hx3le hbdef hrhodef hγlt_b)
            (by linarith [hkey])
        · push_neg at hx0
          have hnorm2 : 1 ≤ ‖x‖ ^ 2 := by nlinarith [hx1]
          have hsum : (⟪x, w 0⟫) ^ 2 + (⟪x, w 1⟫) ^ 2 + (⟪x, w 2⟫) ^ 2 + (⟪x, w 3⟫) ^ 2
              = ‖x‖ ^ 2 := by
            have h := OrthonormalBasis.sum_sq_inner_left w x
            simp only [Fin.sum_univ_four] at h
            simpa using h
          have hk : ∃ k : Fin 4, 1 ≤ (k : ℕ) ∧ 1 / 4 ≤ (⟪x, w k⟫) ^ 2 := by
            by_contra hcon
            push_neg at hcon
            have h1 := hcon 1 (by norm_num)
            have h2 := hcon 2 (by norm_num)
            have h3 := hcon 3 (by norm_num)
            linarith
          exact (regular_case_contradiction (S := S) (rho := rho) (b := b) (α := α) (β := β)
            (Γ := Γ) (γ := γ₀) (lam := lam) (xc := fun i => ⟪x, w i⟫)
            (u := fun i => (fderiv ℝ u x) (w i)) (D1b := fun i => fderiv ℝ (bF u) x (w i))
            hbpos' (by rw [one_div γ₀]; exact le_of_lt hγlt_b) hρpos hρ9 hSpos hΓ
            (by norm_num : (0 : ℝ) < γ₀) (by norm_num : (4000 : ℝ) ≤ 1 / γ₀) hαdef hβdef
            huxc hu1 hfs3 hfsnn hklow hf0 hk hmax1 hmaxP).elim


/-! ## Continuity of the pieces of the test function -/

theorem continuousOn_fderiv_apply_self {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hu : ContDiffOn ℝ 2 u s) :
    ContinuousOn (fun z => (fderiv ℝ u z) z) s :=
  (continuousOn_fderiv hs (hu.of_le (by norm_num))).clm_apply continuousOn_id

theorem continuousOn_WF {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s) (hu : ContDiffOn ℝ 2 u s) :
    ContinuousOn (WF u) s := by
  change ContinuousOn (fun z : ℝ⁴ => (fderiv ℝ u z) z - u z) s
  exact (continuousOn_fderiv_apply_self hs hu).sub hu.continuousOn

theorem continuousOn_QF {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s) (hu : ContDiffOn ℝ 2 u s)
    (v : OrthonormalBasis (Fin 4) ℝ ℝ⁴) :
    ContinuousOn (QF v u) s := by
  have h : ∀ k : Fin 4, ContinuousOn (fun z => ((fderiv ℝ u z) (v k)) ^ 2) s := fun k =>
    ((continuousOn_fderiv hs (hu.of_le (by norm_num))).clm_apply continuousOn_const).pow 2
  have hsum := continuousOn_finsetSum (Finset.univ) (fun k _ => h k)
  change ContinuousOn (fun z : ℝ⁴ => ∑ k : Fin 4, ((fderiv ℝ u z) (v k)) ^ 2) s
  exact hsum

theorem continuousOn_bF {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s) (hu : ContDiffOn ℝ 2 u s)
    (hΔ : ∀ y ∈ s, 0 < (Δ u) y) : ContinuousOn (bF u) s := by
  change ContinuousOn (fun z : ℝ⁴ => Real.log ((Δ u) z)) s
  exact (Commons.Analysis.Calculus.Laplacian.continuousOn_laplacian hs hu).log
    (fun y hy => ne_of_gt (hΔ y hy))

theorem continuousOn_barF {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s) (hu : ContDiffOn ℝ 2 u s)
    (hΔ : ∀ y ∈ s, 0 < (Δ u) y) (c : ℝ) : ContinuousOn (barF u c) s := by
  change ContinuousOn (fun z : ℝ⁴ => bF u z - c) s
  exact (continuousOn_bF hs hu hΔ).sub continuousOn_const

theorem continuousOn_Pfun {u : ℝ⁴ → ℝ} {s t : Set ℝ⁴} (hs : IsOpen s)
    (hsub : closedBall 0 3 ⊆ s) (hu : ContDiffOn ℝ 4 u s) (hΔ : ∀ y ∈ s, 0 < (Δ u) y)
    (ht : t ⊆ ball 0 3) (v : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (c α β γ : ℝ) (hγ : 0 < γ) :
    ContinuousOn (Pfun v u c α β γ) t := by
  have hus : ContDiffOn ℝ 2 u s := hu.of_le (by norm_num)
  have hts : t ⊆ s := fun z hz => hsub (ball_subset_closedBall (ht hz))
  have hrho : ContinuousOn (fun z : ℝ⁴ => rhoF z) t := by
    change ContinuousOn (fun z : ℝ⁴ => 9 - ‖z‖ ^ 2) t
    exact (continuous_const.sub (continuous_norm.pow 2)).continuousOn
  have hrho_pos : ∀ z ∈ t, 0 < rhoF z := by
    intro z hz
    have hz3 : ‖z‖ < 3 := mem_ball_zero_iff.mp (ht hz)
    rw [rhoF]; nlinarith [norm_nonneg z]
  have hlogrho : ContinuousOn (fun z => Real.log (rhoF z)) t :=
    hrho.log (fun z hz => ne_of_gt (hrho_pos z hz))
  have hmaxg : ContinuousOn (fun z => Real.log (max (barF u c z) γ⁻¹)) t := by
    have hm : ContinuousOn (fun z => max (barF u c z) γ⁻¹) t :=
      ((continuousOn_barF hs hus hΔ c).sup continuousOn_const).mono hts
    exact hm.log (fun z hz =>
      ne_of_gt (lt_of_lt_of_le (inv_pos.mpr hγ) (le_max_right _ _)))
  have h1 : ContinuousOn (fun z => 2 * Real.log (rhoF z)) t :=
    continuousOn_const.mul hlogrho
  have h2 : ContinuousOn (fun z => α * WF u z) t :=
    continuousOn_const.mul ((continuousOn_WF hs hus).mono hts)
  have h3 : ContinuousOn (fun z => (β / 2) * QF v u z) t :=
    continuousOn_const.mul ((continuousOn_QF hs hus v).mono hts)
  have h4 := ((h1.add h2).add h3).add hmaxg
  change ContinuousOn (fun z => 2 * Real.log (rhoF z) + α * WF u z + (β / 2) * QF v u z
    + Real.log (max (barF u c z) γ⁻¹)) t
  exact h4

/-! ## Existence of the maximum of the test function on `ball 0 3` -/

theorem exists_radius_le {A B C : ℝ} :
    ∃ R : ℝ, 0 < R ∧ R < 3 ∧ 2 * Real.log (9 - R ^ 2) + A + B < C := by
  set C₀ : ℝ := (C - A - B) / 2 with hC₀def
  set u : ℝ := min (Real.exp (C₀ - 1)) (1 / 2) with hudef
  have hupos : 0 < u := by rw [hudef]; positivity
  have hule : u ≤ 1 / 2 := by rw [hudef]; exact min_le_right _ _
  have h9u : (0 : ℝ) < 9 - u := by linarith
  have hlogu : Real.log u < C₀ := by
    have h1 : Real.log u ≤ Real.log (Real.exp (C₀ - 1)) := by
      apply Real.log_le_log hupos
      rw [hudef]; exact min_le_left _ _
    rw [Real.log_exp] at h1
    linarith
  refine ⟨Real.sqrt (9 - u), ?_, ?_, ?_⟩
  · rw [Real.sqrt_pos]; exact h9u
  · have hsq : (Real.sqrt (9 - u)) ^ 2 < 3 ^ 2 := by
      rw [Real.sq_sqrt (le_of_lt h9u)]; norm_num; linarith
    nlinarith [Real.sqrt_nonneg (9 - u), hsq]
  · rw [Real.sq_sqrt (le_of_lt h9u), show (9 : ℝ) - (9 - u) = u by ring]
    rw [hC₀def] at hlogu
    linarith

theorem exists_Pfun_max {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hsub : closedBall 0 3 ⊆ s) (hu : ContDiffOn ℝ 4 u s) (hΔ : ∀ y ∈ s, 0 < (Δ u) y)
    {Γ c α β γ : ℝ} (hΓ : 4 ≤ Γ) (hγ : 0 < γ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (huΓ : ∀ z ∈ closedBall 0 3, |u z| ≤ Γ - 4)
    (hdΓ : ∀ z ∈ closedBall 0 3, ‖fderiv ℝ u z‖ ≤ Γ - 4)
    (v : OrthonormalBasis (Fin 4) ℝ ℝ⁴) :
    ∃ x ∈ ball 0 3, ∀ y ∈ ball 0 3, Pfun v u c α β γ y ≤ Pfun v u c α β γ x := by
  have hu2 : ContDiffOn ℝ 2 u s := hu.of_le (by norm_num)
  have hΔcont : ContinuousOn (fun z => (Δ u) z) (closedBall 0 3) :=
    (Commons.Analysis.Calculus.Laplacian.continuousOn_laplacian hs hu2).mono hsub
  have hcomp : IsCompact (closedBall (0 : ℝ⁴) 3) := isCompact_closedBall 0 3
  obtain ⟨z₀, -, hz₀max⟩ :=
    hcomp.exists_isMaxOn ⟨0, by simp [mem_closedBall]⟩ hΔcont
  set Λ : ℝ := (Δ u) z₀ with hΛdef
  have hΛle : ∀ z ∈ closedBall 0 3, (Δ u) z ≤ Λ := isMaxOn_iff.mp hz₀max
  have hΛpos : 0 < Λ := lt_of_lt_of_le (hΔ 0 (hsub (by simp [mem_closedBall]))) (hΛle 0 (by simp [mem_closedBall]))
  set B1 : ℝ := 4 * α * Γ + (β / 2) * Γ ^ 2 with hB1def
  set B2 : ℝ := max (Real.log Λ - c) (Real.log γ⁻¹) with hB2def
  have hpiece : ∀ z ∈ ball 0 3, α * WF u z + (β / 2) * QF v u z ≤ B1 := by
    intro z hz
    have h1 := abs_WF_le (u := u) (Γ := Γ) (z := z) hΓ (huΓ z (ball_subset_closedBall hz))
      (hdΓ z (ball_subset_closedBall hz)) (le_of_lt (mem_ball_zero_iff.mp hz))
    have h2 := QF_le_sq (u := u) (Γ := Γ) (z := z) hΓ (hdΓ z (ball_subset_closedBall hz)) v
    have h3 : α * WF u z ≤ α * (4 * Γ) :=
      mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) h1) hα
    have h4 : (β / 2) * QF v u z ≤ (β / 2) * Γ ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    rw [hB1def]; linarith
  have hlogle : ∀ z ∈ ball 0 3, Real.log (max (barF u c z) γ⁻¹) ≤ B2 := by
    intro z hz
    have hb : barF u c z ≤ Real.log Λ - c := by
      have hzm : Δ u z ≤ Λ := hΛle z (ball_subset_closedBall hz)
      simp only [barF, bF]
      have h := Real.log_le_log (hΔ z (hsub (ball_subset_closedBall hz))) hzm
      linarith
    have hexpB2 : Real.log Λ - c ≤ Real.exp B2 := by
      have h1 : Real.log Λ - c ≤ B2 := by rw [hB2def]; exact le_max_left _ _
      have h2 : B2 ≤ Real.exp B2 := by have := Real.add_one_le_exp B2; linarith
      linarith
    have hγle : γ⁻¹ ≤ Real.exp B2 := by
      have h1 : Real.log γ⁻¹ ≤ B2 := by rw [hB2def]; exact le_max_right _ _
      rw [← Real.exp_log (inv_pos.mpr hγ)]
      exact Real.exp_le_exp.mpr h1
    rw [Real.log_le_iff_le_exp (lt_of_lt_of_le (inv_pos.mpr hγ) (le_max_right _ _))]
    exact max_le (le_trans hb hexpB2) hγle
  have hbound : ∀ z ∈ ball 0 3,
      Pfun v u c α β γ z ≤ 2 * Real.log (rhoF z) + B1 + B2 := by
    intro z hz
    have h1 : Real.log (max (barF u c z) γ⁻¹) ≤ B2 := hlogle z hz
    have h2 := hpiece z hz
    simp only [Pfun]
    linarith
  obtain ⟨R, hRpos, hR3, hR⟩ := exists_radius_le (A := B1) (B := B2) (C := Pfun v u c α β γ 0)
  have hcont : ContinuousOn (Pfun v u c α β γ) (closedBall 0 R) :=
    continuousOn_Pfun hs hsub hu hΔ (fun z hz => by
      rw [mem_closedBall] at hz; rw [mem_ball]; linarith) v c α β γ hγ
  obtain ⟨x, hxK, hxmax⟩ := (isCompact_closedBall (0 : ℝ⁴) R).exists_isMaxOn
    ⟨0, by rw [mem_closedBall]; simpa using le_of_lt hRpos⟩ hcont
  have hxmax' : ∀ y ∈ closedBall 0 R, Pfun v u c α β γ y ≤ Pfun v u c α β γ x :=
    isMaxOn_iff.mp hxmax
  have hx3 : x ∈ ball 0 3 := by
    rw [mem_ball]; rw [mem_closedBall] at hxK; linarith
  refine ⟨x, hx3, fun y hy => ?_⟩
  by_cases hyR : ‖y‖ ≤ R
  · exact hxmax' y (by rw [mem_closedBall, dist_zero_right]; exact hyR)
  · push_neg at hyR
    have hy3 : ‖y‖ < 3 := mem_ball_zero_iff.mp hy
    have hr : rhoF y ≤ 9 - R ^ 2 := by
      rw [rhoF]; nlinarith [norm_nonneg y, hRpos]
    have hrpos : 0 < rhoF y := by rw [rhoF]; nlinarith [norm_nonneg y]
    have hlog : 2 * Real.log (rhoF y) ≤ 2 * Real.log (9 - R ^ 2) := by
      have := Real.log_le_log hrpos hr
      linarith
    have hb := hbound y hy
    have h0 : Pfun v u c α β γ y < Pfun v u c α β γ 0 := by linarith
    have h0K : (0 : ℝ⁴) ∈ closedBall 0 R := by rw [mem_closedBall]; simpa using le_of_lt hRpos
    exact le_trans (le_of_lt h0) (hxmax' 0 h0K)

/-! ## Proposition 2.4: the doubling inequality -/

/-- The explicit (universal) constant produced by the doubling inequality. -/
noncomputable def doublingConst : ℝ := Real.exp 12000004 * (10 : ℝ) ^ 49

theorem doubling_inequality_const {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hsub : closedBall 0 3 ⊆ s) (hu : ContDiffOn ℝ 4 u s)
    (hσ2 : ∀ y ∈ s, σ₂ (H u s y) = 1) (hΔ : ∀ y ∈ s, 0 < (Δ u) y)
    {Γ : ℝ} (hΓ : 4 ≤ Γ)
    (huΓ : ∀ z ∈ closedBall 0 3, |u z| ≤ Γ - 4)
    (hdΓ : ∀ z ∈ closedBall 0 3, ‖fderiv ℝ u z‖ ≤ Γ - 4) :
    ∀ z ∈ ball 0 2,
      (Δ u) z ≤ doublingConst * Real.exp (doublingConst * Γ ^ 2)
        * sSup ((fun z => (Δ u) z) '' ball 0 1) := by
  classical
  have hΓpos : 0 < Γ := by linarith
  have hΓ1 : (1 : ℝ) ≤ Γ := by linarith
  have hΓ2 : (16 : ℝ) ≤ Γ ^ 2 := by nlinarith
  have hΓle : Γ ≤ Γ ^ 2 := by nlinarith
  set M : ℝ := sSup ((fun z => (Δ u) z) '' ball 0 1) with hMdef
  have hΔcont1 : ContinuousOn (fun z => (Δ u) z) (closure (ball (0 : ℝ⁴) 1)) := by
    rw [closure_ball 0 one_ne_zero]
    exact (Commons.Analysis.Calculus.Laplacian.continuousOn_laplacian hs
      (hu.of_le (by norm_num))).mono (fun z hz => hsub (by
        rw [mem_closedBall] at hz ⊢; linarith))
  have hsSup := sSup_image_bounds (K := ball (0 : ℝ⁴) 1) (f := fun z => (Δ u) z)
    (by rw [closure_ball 0 one_ne_zero]; exact isCompact_closedBall 0 1) hΔcont1
    ⟨0, by simp [mem_ball]⟩
  have hMle : ∀ z ∈ ball 0 1, (Δ u) z ≤ M := hsSup.1
  have hM0 : 0 < M := lt_of_lt_of_le (hΔ 0 (hsub (by simp [mem_closedBall])))
    (hMle 0 (by simp [mem_ball]))
  obtain ⟨v, lam₀, hdiag₀, -⟩ := exists_diagonal_basis (x := (0 : ℝ⁴)) hs
    (hu.of_le (by norm_num)) (hsub (by simp [mem_closedBall]))
  obtain ⟨x, hx, hxmax⟩ := exists_Pfun_max hs hsub hu hΔ hΓ
    (by norm_num : (0 : ℝ) < γ₀) (by positivity : (0 : ℝ) ≤ γ₀ ^ 4 / Γ)
    (by positivity : (0 : ℝ) ≤ γ₀ ^ 6 / Γ ^ 2)
    huΓ hdΓ v
  have hM1 : (1 : ℝ) ≤ M := by
    have h0 : (Δ u) 0 ≤ M := hMle 0 (by simp [mem_ball])
    have h02 : 2 ≤ ((Δ u) 0) ^ 2 := laplacian_sq_ge_two hs (hsub (by simp [mem_closedBall]))
      (hu.of_le (by norm_num)) hσ2
    have h03 : 0 < (Δ u) 0 := hΔ 0 (hsub (by simp [mem_closedBall]))
    nlinarith [h0, h02, h03]
  have hpmax := Pfun_max_bound hs hsub hu hσ2 hΔ hΓ huΓ hdΓ hM0 hM1 hMle
    (by positivity : (0 : ℝ) < γ₀ ^ 4 / Γ) rfl (by positivity : (0 : ℝ) < γ₀ ^ 6 / Γ ^ 2) rfl
    hx hxmax
  have hC1 : (1 : ℝ) ≤ doublingConst := by
    rw [doublingConst]
    have h1 : (1 : ℝ) ≤ Real.exp 12000004 := Real.one_le_exp (by norm_num)
    have h2 : (1 : ℝ) ≤ (10 : ℝ) ^ 49 := by norm_num
    exact le_trans (by norm_num) (mul_le_mul h1 h2 (by norm_num) (by linarith))
  intro z hz
  have hz3 : z ∈ ball 0 3 := by rw [mem_ball] at hz ⊢; linarith
  have hzle : Pfun v u (Real.log M) (γ₀ ^ 4 / Γ) (γ₀ ^ 6 / Γ ^ 2) γ₀ z
      ≤ 12000000 + Real.log (Γ ^ 2 * (γ₀ ^ 8)⁻¹) := le_trans (hxmax z hz3) hpmax
  have hWFz := abs_WF_le (u := u) (Γ := Γ) (z := z) hΓ (huΓ z (ball_subset_closedBall hz3))
    (hdΓ z (ball_subset_closedBall hz3)) (le_of_lt (mem_ball_zero_iff.mp hz3))
  have hQFz := QF_nonneg v u z
  have hρz : (1 : ℝ) ≤ rhoF z := by
    rw [rhoF]; have : ‖z‖ < 2 := mem_ball_zero_iff.mp hz; nlinarith [norm_nonneg z]
  have hslack : Real.log (max (barF u (Real.log M) z) γ₀⁻¹)
      ≤ 12000000 + Real.log (Γ ^ 2 * (γ₀ ^ 8)⁻¹) + 4 * γ₀ ^ 4 := by
    have h := hzle
    simp only [Pfun] at h
    have h1 : 0 ≤ 2 * Real.log (rhoF z) := by
      have := Real.log_nonneg hρz; linarith
    have h2 : -(4 * γ₀ ^ 4) ≤ (γ₀ ^ 4 / Γ) * WF u z := by
      have h2a : -(4 * Γ) ≤ WF u z := neg_le_of_abs_le hWFz
      have h2b : (γ₀ ^ 4 / Γ) * (-(4 * Γ)) ≤ (γ₀ ^ 4 / Γ) * WF u z :=
        mul_le_mul_of_nonneg_left h2a (by positivity)
      have h2c : (γ₀ ^ 4 / Γ) * (4 * Γ) = 4 * γ₀ ^ 4 := by field_simp
      rw [mul_neg, h2c] at h2b
      linarith
    have h3 : 0 ≤ ((γ₀ ^ 6 / Γ ^ 2) / 2) * QF v u z := mul_nonneg (by positivity) hQFz
    linarith [h, h1, h2, h3]
  have hb_le : barF u (Real.log M) z ≤ doublingConst * Γ ^ 2 := by
    by_cases hb : barF u (Real.log M) z ≤ γ₀⁻¹
    · have h1 : barF u (Real.log M) z ≤ 1000000 := le_trans hb (by norm_num)
      have h2 : (1000000 : ℝ) ≤ doublingConst * Γ ^ 2 := by
        rw [doublingConst]
        have h3 := Real.add_one_le_exp (12000004 : ℝ)
        nlinarith [hΓ2, h3]
      linarith
    · push_neg at hb
      have hbpos : 0 < barF u (Real.log M) z :=
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < γ₀⁻¹) (le_of_lt hb)
      have hm : Real.log (max (barF u (Real.log M) z) γ₀⁻¹)
          = Real.log (barF u (Real.log M) z) := by rw [max_eq_left (le_of_lt hb)]
      have h1 : Real.log (barF u (Real.log M) z)
          ≤ 12000004 + Real.log (Γ ^ 2 * (γ₀ ^ 8)⁻¹) := by
        rw [← hm]
        have : (4 : ℝ) * γ₀ ^ 4 ≤ 4 := by norm_num
        linarith [hslack, this]
      have h2 : Real.exp (12000004 + Real.log (Γ ^ 2 * (γ₀ ^ 8)⁻¹)) ≤ doublingConst * Γ ^ 2 := by
        rw [doublingConst, Real.exp_add, Real.exp_log (by positivity)]
        have hγ8 : (γ₀ ^ 8)⁻¹ ≤ (10 : ℝ) ^ 49 := by
          have h : (γ₀ ^ 8)⁻¹ = (10 : ℝ) ^ 48 := by norm_num
          rw [h]; norm_num
        nlinarith [hγ8, hΓ2, Real.exp_pos (12000004 : ℝ)]
      calc barF u (Real.log M) z
          ≤ Real.exp (Real.log (barF u (Real.log M) z)) := le_of_eq (Real.exp_log hbpos).symm
        _ ≤ Real.exp (12000004 + Real.log (Γ ^ 2 * (γ₀ ^ 8)⁻¹)) := Real.exp_le_exp.mpr h1
        _ ≤ doublingConst * Γ ^ 2 := h2
  have hΔz : (Δ u) z = M * Real.exp (barF u (Real.log M) z) := by
    have h1 : Real.log ((Δ u) z) = Real.log M + barF u (Real.log M) z := by
      simp only [barF, bF]; ring
    rw [← Real.exp_log (hΔ z (hsub (ball_subset_closedBall hz3))), h1, Real.exp_add,
      Real.exp_log hM0]
  have hfin : M * Real.exp (barF u (Real.log M) z)
      ≤ doublingConst * Real.exp (doublingConst * Γ ^ 2) * M := by
    have h1 : Real.exp (barF u (Real.log M) z) ≤ Real.exp (doublingConst * Γ ^ 2) :=
      Real.exp_le_exp.mpr hb_le
    have h2 : M * Real.exp (barF u (Real.log M) z) ≤ M * Real.exp (doublingConst * Γ ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hM0)
    have h3 : M * Real.exp (doublingConst * Γ ^ 2)
        ≤ doublingConst * Real.exp (doublingConst * Γ ^ 2) * M := by
      have h4 : (0 : ℝ) < M * Real.exp (doublingConst * Γ ^ 2) := mul_pos hM0 (Real.exp_pos _)
      calc M * Real.exp (doublingConst * Γ ^ 2)
          = 1 * (M * Real.exp (doublingConst * Γ ^ 2)) := by ring
        _ ≤ doublingConst * (M * Real.exp (doublingConst * Γ ^ 2)) :=
            mul_le_mul_of_nonneg_right hC1 (le_of_lt h4)
        _ = doublingConst * Real.exp (doublingConst * Γ ^ 2) * M := by ring
    linarith
  linarith [hΔz, hfin]

/-- Proposition 2.4 (doubling inequality) in existential form. -/
theorem doubling_inequality {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hsub : closedBall 0 3 ⊆ s) (hu : ContDiffOn ℝ 4 u s)
    (hσ2 : ∀ y ∈ s, σ₂ (H u s y) = 1) (hΔ : ∀ y ∈ s, 0 < (Δ u) y)
    {Γ : ℝ} (hΓ : 4 ≤ Γ)
    (huΓ : ∀ z ∈ closedBall 0 3, |u z| ≤ Γ - 4)
    (hdΓ : ∀ z ∈ closedBall 0 3, ‖fderiv ℝ u z‖ ≤ Γ - 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ ball 0 2,
      (Δ u) z ≤ C * Real.exp (C * Γ ^ 2) * sSup ((fun z => (Δ u) z) '' ball 0 1) :=
  ⟨doublingConst, by
      rw [doublingConst]
      have h1 : (1 : ℝ) ≤ Real.exp 12000004 := Real.one_le_exp (by norm_num)
      have h2 : (1 : ℝ) ≤ (10 : ℝ) ^ 49 := by norm_num
      have h3 : (1:ℝ) ≤ Real.exp 12000004 * (10:ℝ)^49 := by
        have := mul_le_mul h1 h2 (by norm_num : (0:ℝ) ≤ 1) (le_trans zero_le_one h1)
        simpa using this
      exact lt_of_lt_of_le zero_lt_one h3,
    doubling_inequality_const hs hsub hu hσ2 hΔ hΓ huΓ hdΓ⟩

end Submission
