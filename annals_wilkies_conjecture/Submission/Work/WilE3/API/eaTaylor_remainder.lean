import Mathlib
import Submission.Work.WilE3.API.RemDefs
import Submission.Work.WilE3.API.Rem.eaDmulti_comp
import Submission.Work.WilE3.API.Rem.sum_miFinset_shift
import Submission.Work.WilE3.API.Rem.fderiv_eaEval
import Submission.Work.WilE3.API.Rem.fderiv_eTay

namespace Work.WilE3.API

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

/-!
## The Taylor remainder estimate for EA functions

`eaEval c Q` is smooth (a polynomial in `x` and the exponentials `exp (ℓ_j x)`), so the Taylor
polynomial `eaTaylor c Q N y` of order `N` approximates it to order `N + 1` near `y`.  This file
proves that, from the two derivative formulas for `eaEval` and `eaTaylor`.
-/

/-! ### The induction -/

theorem eaTaylor_remainder_aux {k r : ℕ} (c : EAChain k r) (y : Fin k → ℝ)
    (hD : ∀ (Q : EAPoly k r) (x : Fin k → ℝ), HasFDerivAt (eaEval c Q)
      ((∑ i : Fin k, (eaEval c (eaD c i Q) x) •
        (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i)) : (Fin k → ℝ) →L[ℝ] ℝ) x)
    (hT : ∀ (Q : EAPoly k r) (N : ℕ) (x : Fin k → ℝ),
      HasFDerivAt (fun z => eaTaylor c Q (N + 1) y z)
      ((∑ i : Fin k, (eaTaylor c (eaD c i Q) N y x) •
        (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i)) : (Fin k → ℝ) →L[ℝ] ℝ) x) :
    ∀ N : ℕ, ∀ Q : EAPoly k r, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in 𝓝 y,
      |eaEval c Q x - eaTaylor c Q N y x| ≤ C * dist x y ^ (N + 1) := by
  intro N
  induction N with
  | zero =>
    intro Q
    have hbdd : ∀ i : Fin k, ∀ᶠ z in 𝓝 y,
        |eaEval c (eaD c i Q) z| ≤ |eaEval c (eaD c i Q) y| + 1 := by
      intro i
      have hc : ContinuousAt (fun z => eaEval c (eaD c i Q) z) y :=
        (hD (eaD c i Q) y).continuousAt
      obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hc 1 one_pos
      filter_upwards [Metric.ball_mem_nhds y hδ] with z hz
      have hz' : |eaEval c (eaD c i Q) z - eaEval c (eaD c i Q) y| < 1 := by
        have h := hδ' (Metric.mem_ball.mp hz)
        simpa [Real.dist_eq] using h
      have h2 := abs_sub_abs_le_abs_sub (eaEval c (eaD c i Q) z) (eaEval c (eaD c i Q) y)
      linarith
    obtain ⟨ε, hε, hball⟩ :=
      Metric.eventually_nhds_iff_ball.mp (Filter.eventually_all.mpr hbdd)
    refine ⟨∑ i, (|eaEval c (eaD c i Q) y| + 1), Finset.sum_nonneg fun i _ => by positivity, ?_⟩
    filter_upwards [Metric.ball_mem_nhds y hε] with x hx
    have hMVT := (convex_closedBall y (dist x y)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun z => eaEval c Q z - eaEval c Q y)
      (f' := fun z => ∑ i : Fin k, (eaEval c (eaD c i Q) z) •
        (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i))
      (s := Metric.closedBall y (dist x y)) (x := y) (y := x)
      (C := ∑ i, (|eaEval c (eaD c i Q) y| + 1))
      (fun z _ => ((hD Q z).sub_const (eaEval c Q y)).hasFDerivWithinAt)
      (fun z hz => by
        have hzx : dist z y ≤ dist x y := Metric.mem_closedBall.mp hz
        have hzε : dist z y < ε := lt_of_le_of_lt hzx hx
        calc ‖∑ i : Fin k, (eaEval c (eaD c i Q) z) •
              (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i)‖
            ≤ ∑ i, |eaEval c (eaD c i Q) z| := norm_sum_smul_proj_le _
          _ ≤ ∑ i, (|eaEval c (eaD c i Q) y| + 1) :=
              Finset.sum_le_sum fun i _ => hball z hzε i)
      (Metric.mem_closedBall.mpr (by simp)) (Metric.mem_closedBall.mpr le_rfl)
    rw [eaTaylor_zero]
    calc |eaEval c Q x - eaEval c Q y|
        = ‖(fun z => eaEval c Q z - eaEval c Q y) x‖ := by simp [Real.norm_eq_abs]
      _ = ‖(fun z => eaEval c Q z - eaEval c Q y) x
            - (fun z => eaEval c Q z - eaEval c Q y) y‖ := by simp
      _ ≤ (∑ i, (|eaEval c (eaD c i Q) y| + 1)) * ‖x - y‖ := hMVT
      _ = (∑ i, (|eaEval c (eaD c i Q) y| + 1)) * dist x y := by rw [dist_eq_norm]
      _ = (∑ i, (|eaEval c (eaD c i Q) y| + 1)) * dist x y ^ (0 + 1) := by
            rw [zero_add, pow_one]
  | succ N ih =>
    intro Q
    have hih : ∀ i : Fin k, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in 𝓝 y,
        |eaEval c (eaD c i Q) x - eaTaylor c (eaD c i Q) N y x| ≤ C * dist x y ^ (N + 1) :=
      fun i => ih (eaD c i Q)
    choose C hCpos hCbound using hih
    refine ⟨∑ i, C i, Finset.sum_nonneg fun i _ => hCpos i, ?_⟩
    obtain ⟨ε, hε, hball⟩ :=
      Metric.eventually_nhds_iff_ball.mp (Filter.eventually_all.mpr hCbound)
    filter_upwards [Metric.ball_mem_nhds y hε] with x hx
    have hgy : (fun z => eaEval c Q z - eaTaylor c Q (N + 1) y z) y = 0 := by
      simp [eaTaylor_self]
    have hMVT := (convex_closedBall y (dist x y)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun z => eaEval c Q z - eaTaylor c Q (N + 1) y z)
      (f' := fun z => ∑ i : Fin k,
        (eaEval c (eaD c i Q) z - eaTaylor c (eaD c i Q) N y z) •
          (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i))
      (s := Metric.closedBall y (dist x y)) (x := y) (y := x)
      (C := (∑ i, C i) * dist x y ^ (N + 1))
      (fun z _ => by
        have h1 : HasFDerivAt (fun z => eaEval c Q z - eaTaylor c Q (N + 1) y z)
            ((∑ i : Fin k, (eaEval c (eaD c i Q) z) •
                (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i))
              - ∑ i : Fin k, (eaTaylor c (eaD c i Q) N y z) •
                (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i)) z :=
          (hD Q z).sub (hT Q N z)
        rw [sum_smul_proj_sub] at h1
        exact h1.hasFDerivWithinAt)
      (fun z hz => by
        have hzx : dist z y ≤ dist x y := Metric.mem_closedBall.mp hz
        have hzε : dist z y < ε := lt_of_le_of_lt hzx hx
        calc ‖∑ i : Fin k, (eaEval c (eaD c i Q) z - eaTaylor c (eaD c i Q) N y z) •
              (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i)‖
            ≤ ∑ i, |eaEval c (eaD c i Q) z - eaTaylor c (eaD c i Q) N y z| :=
              norm_sum_smul_proj_le _
          _ ≤ ∑ i, C i * dist x y ^ (N + 1) := Finset.sum_le_sum fun i _ =>
              le_trans (hball z hzε i)
                (mul_le_mul_of_nonneg_left (pow_le_pow_of_le dist_nonneg hzx (N + 1)) (hCpos i))
          _ = (∑ i, C i) * dist x y ^ (N + 1) := by rw [Finset.sum_mul])
      (Metric.mem_closedBall.mpr (by simp)) (Metric.mem_closedBall.mpr le_rfl)
    calc |eaEval c Q x - eaTaylor c Q (N + 1) y x|
        = ‖(fun z => eaEval c Q z - eaTaylor c Q (N + 1) y z) x‖ := by simp [Real.norm_eq_abs]
      _ = ‖(fun z => eaEval c Q z - eaTaylor c Q (N + 1) y z) x
            - (fun z => eaEval c Q z - eaTaylor c Q (N + 1) y z) y‖ := by rw [hgy, sub_zero]
      _ ≤ ((∑ i, C i) * dist x y ^ (N + 1)) * ‖x - y‖ := hMVT
      _ = (∑ i, C i) * dist x y ^ (N + 1 + 1) := by rw [dist_eq_norm, pow_succ]; ring

/-! ### The derivative of the Taylor polynomial -/

theorem fderiv_eaTaylor_aux {k r : ℕ} (c : EAChain k r)
    (hcomp : ∀ (m m' : Fin k → ℕ) (Q : EAPoly k r),
      eaDmulti c m (eaDmulti c m' Q) = eaDmulti c (m + m') Q)
    (hshift : ∀ (F : (Fin k → ℕ) → ℝ) (N : ℕ) (i : Fin k),
      ∑ m ∈ (miFinset k (N + 1)).filter (fun m => 0 < m i), F (miS m i)
        = ∑ n ∈ miFinset k N, F n)
    (hTay : ∀ (y : Fin k → ℝ) (S : Finset (Fin k → ℕ)) (b : (Fin k → ℕ) → ℝ)
      (x : Fin k → ℝ), HasFDerivAt (fun z => eTay y S b z)
      ((∑ i : Fin k, (∑ m ∈ S.filter (fun m => 0 < m i), eDTay y b i m x) •
        (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i)) : (Fin k → ℝ) →L[ℝ] ℝ) x) :
    ∀ (Q : EAPoly k r) (N : ℕ) (y x : Fin k → ℝ),
      HasFDerivAt (fun z => eaTaylor c Q (N + 1) y z)
        ((∑ i : Fin k, (eaTaylor c (eaD c i Q) N y x) •
          (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i)) : (Fin k → ℝ) →L[ℝ] ℝ) x := by
  intro Q N y x
  have hmain := hTay y (miFinset k (N + 1)) (fun m => eaEval c (eaDmulti c m Q) y) x
  have hfun : (fun z => eTay y (miFinset k (N + 1)) (fun m => eaEval c (eaDmulti c m Q) y) z)
      = fun z => eaTaylor c Q (N + 1) y z := by
    funext z
    exact (eaTaylor_eq_eTay c Q (N + 1) y z).symm
  rw [hfun] at hmain
  have hder : ((∑ i : Fin k, (∑ m ∈ (miFinset k (N + 1)).filter (fun m => 0 < m i),
        eDTay y (fun m => eaEval c (eaDmulti c m Q) y) i m x) •
        (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i)) : (Fin k → ℝ) →L[ℝ] ℝ)
      = ∑ i : Fin k, (eaTaylor c (eaD c i Q) N y x) •
        (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    have h1 : ∑ m ∈ (miFinset k (N + 1)).filter (fun m => 0 < m i),
          eDTay y (fun m => eaEval c (eaDmulti c m Q) y) i m x
        = ∑ m ∈ (miFinset k (N + 1)).filter (fun m => 0 < m i),
          eTayCoeff y (fun n => eaEval c (eaDmulti c (n + eMI i) Q) y) (miS m i) x := by
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm0 : 0 < m i := (Finset.mem_filter.mp hm).2
      simp only [eDTay, eTayCoeff]
      rw [miS_add_eMI hm0]
    rw [h1,
      hshift (fun n => eTayCoeff y (fun n' => eaEval c (eaDmulti c (n' + eMI i) Q) y) n x) N i,
      eaTaylor_eq_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [eTayCoeff]
    have hc : eaEval c (eaDmulti c (n + eMI i) Q) y = eaEval c (eaDmulti c n (eaD c i Q)) y := by
      rw [← hcomp n (eMI i) Q, eaDmulti_eMI]
    rw [hc]
  rw [hder] at hmain
  exact hmain

/-! ### The target statement -/

/-- The derivative of the truncated Taylor polynomial of an EA function. -/
theorem fderiv_eaTaylor {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (N : ℕ)
    (y x : Fin k → ℝ) :
    HasFDerivAt (fun z => eaTaylor c Q (N + 1) y z)
      ((∑ i : Fin k, (eaTaylor c (eaD c i Q) N y x) •
        (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i)) : (Fin k → ℝ) →L[ℝ] ℝ) x :=
  fderiv_eaTaylor_aux c (fun m m' Q => Rem.eaDmulti_comp c m m' Q)
    (fun F N i => Rem.sum_miFinset_shift F N i)
    (fun y S b x => Rem.fderiv_eTay y S b x) Q N y x

theorem eaTaylor_remainder {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (N : ℕ)
    (y : Fin k → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in 𝓝 y,
      |eaEval c Q x - eaTaylor c Q N y x| ≤ C * dist x y ^ (N + 1) :=
  eaTaylor_remainder_aux c y (fun Q x => Rem.fderiv_eaEval c Q x)
    (fun Q N x => fderiv_eaTaylor c Q N y x) N Q

end Work.WilE3.API
