import Mathlib
import Submission.Work.Diff.GE.fixRmDefs
import Submission.Work.Diff.Evol.Calc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Fréchet-derivative bound for the reaction map `rmReact`

`Work.Diff.GE.rmReact n R = Q R - Xact R` is a quadratic polynomial in the components of the
curvature array `R` (`Curv4 n = Fin n → Fin n → Fin n → Fin n → ℝ`).  Consequently

* it is smooth (`C^∞`),
* it is homogeneous of degree two, `rmReact (c • R) = c^2 • rmReact R`,

and these two facts force its Fréchet derivative to grow at most linearly:

  `∃ C ≥ 0, ∀ R, ‖fderiv ℝ (rmReact n) R‖ ≤ C * ‖R‖`.

Proof route.  Homogeneity of `rmReact` together with the chain rule gives the scaling law
`fderiv f (c • R) = c • fderiv f R` for `c ≠ 0`; taking `R = 0` (any base point) and `c = 2`
yields `fderiv f 0 = 0`.  For `R ≠ 0` write `R = ‖R‖ • x` with `‖x‖ = 1`, so
`‖fderiv f R‖ = ‖R‖ * ‖fderiv f x‖` and `x` lies in the compact unit ball, on which the
continuous map `x ↦ ‖fderiv f x‖` is bounded by compactness
(`IsCompact.exists_bound_of_continuousOn`).  This is the same technique used for the local
Lipschitz estimate `Work.Diff.Alg.Pinch.Q_lipschitz_local`.
-/

set_option linter.unusedSimpArgs false

open Submission.Diff.Alg

namespace Work.Diff.GE.react

variable {n : ℕ}

/-- The Ricci-array `ricArr` is homogeneous of degree one. -/
lemma rmReact_ricArr_smul (c : ℝ) (R : Submission.Diff.Alg.Curv4 n) (i j : Fin n) :
    Work.Diff.Evol.ricArr (c • R) i j = c * Work.Diff.Evol.ricArr R i j := by
  simp [Work.Diff.Evol.ricArr, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- `rmReact n` is smooth: it is a quadratic polynomial in the components of `R`. -/
lemma rmReact_contDiff_aux (n : ℕ) : ContDiff ℝ ⊤ (Work.Diff.GE.rmReact n) := by
  unfold Work.Diff.GE.rmReact
  refine ContDiff.sub ?_ ?_
  · unfold Submission.Diff.Alg.Q; fun_prop
  · unfold Work.Diff.Evol.Xact Work.Diff.Evol.ricArr; fun_prop

/-- `rmReact n` is homogeneous of degree two. -/
lemma rmReact_smul_aux (c : ℝ) (R : Submission.Diff.Alg.Curv4 n) :
    Work.Diff.GE.rmReact n (c • R) = c^2 • Work.Diff.GE.rmReact n R := by
  ext i j k l
  simp only [Work.Diff.GE.rmReact_apply, Submission.Diff.Alg.Q, Work.Diff.Evol.Xact,
    Pi.smul_apply, smul_eq_mul, rmReact_ricArr_smul]
  rw [mul_sub]
  simp only [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    ring
  · apply Finset.sum_congr rfl; intro p _
    ring

/-- The scaling law for the Fréchet derivative, obtained by differentiating the degree-two
homogeneity identity. -/
lemma rmReact_fderiv_smul_aux (c : ℝ) (hc : c ≠ 0) (R : Submission.Diff.Alg.Curv4 n) :
    fderiv ℝ (Work.Diff.GE.rmReact n) (c • R)
      = c • fderiv ℝ (Work.Diff.GE.rmReact n) R := by
  have hcd := rmReact_contDiff_aux n
  have hdiff : Differentiable ℝ (Work.Diff.GE.rmReact n) := hcd.differentiable (by simp)
  have hL : HasFDerivAt (fun x : Submission.Diff.Alg.Curv4 n => c^2 • Work.Diff.GE.rmReact n x)
      ((fderiv ℝ (Work.Diff.GE.rmReact n) (c • R)).comp
        (c • ContinuousLinearMap.id ℝ (Submission.Diff.Alg.Curv4 n))) R := by
    have h1 : HasFDerivAt (fun x : Submission.Diff.Alg.Curv4 n => Work.Diff.GE.rmReact n (c • x))
        ((fderiv ℝ (Work.Diff.GE.rmReact n) (c • R)).comp
          (c • ContinuousLinearMap.id ℝ (Submission.Diff.Alg.Curv4 n))) R :=
      ((hdiff (c • R)).hasFDerivAt).comp R ((hasFDerivAt_id R).const_smul c)
    rwa [show (fun x : Submission.Diff.Alg.Curv4 n => Work.Diff.GE.rmReact n (c • x))
        = (fun x => c^2 • Work.Diff.GE.rmReact n x) from funext (fun x => rmReact_smul_aux c x)]
      at h1
  have hR : HasFDerivAt (fun x : Submission.Diff.Alg.Curv4 n => c^2 • Work.Diff.GE.rmReact n x)
      (c^2 • fderiv ℝ (Work.Diff.GE.rmReact n) R) R :=
    (hdiff R).hasFDerivAt.const_smul (c^2)
  have hEq := hL.unique hR
  have key : ∀ v : Submission.Diff.Alg.Curv4 n,
      fderiv ℝ (Work.Diff.GE.rmReact n) (c • R) v
        = c • fderiv ℝ (Work.Diff.GE.rmReact n) R v := by
    intro v
    have hv : fderiv ℝ (Work.Diff.GE.rmReact n) (c • R) (c • v)
        = c^2 • (fderiv ℝ (Work.Diff.GE.rmReact n) R v) := by
      have h1 := congrArg
        (fun (T : Submission.Diff.Alg.Curv4 n →L[ℝ] Submission.Diff.Alg.Curv4 n) => T v) hEq
      simpa only [ContinuousLinearMap.comp_apply, smul_apply,
        ContinuousLinearMap.id_apply] using h1
    rw [map_smul] at hv
    rw [pow_two, mul_smul] at hv
    ext i j k l
    have h2 := congrArg (fun (w : Submission.Diff.Alg.Curv4 n) => w i j k l) hv
    simp only [Pi.smul_apply, smul_eq_mul] at h2 ⊢
    exact mul_left_cancel₀ hc h2
  exact ContinuousLinearMap.ext key

/-- The derivative of a degree-two homogeneous map vanishes at the origin. -/
lemma rmReact_fderiv_zero_aux (n : ℕ) :
    fderiv ℝ (Work.Diff.GE.rmReact n) (0 : Submission.Diff.Alg.Curv4 n) = 0 := by
  have h2 : fderiv ℝ (Work.Diff.GE.rmReact n) (0 : Submission.Diff.Alg.Curv4 n)
      = (2:ℝ) • fderiv ℝ (Work.Diff.GE.rmReact n) (0 : Submission.Diff.Alg.Curv4 n) := by
    simpa using rmReact_fderiv_smul_aux (n := n) 2 (by norm_num) (0 : Submission.Diff.Alg.Curv4 n)
  have h3 : (2:ℝ) • fderiv ℝ (Work.Diff.GE.rmReact n) (0 : Submission.Diff.Alg.Curv4 n)
      - fderiv ℝ (Work.Diff.GE.rmReact n) (0 : Submission.Diff.Alg.Curv4 n) = 0 := by
    rw [← h2]; exact sub_self _
  rw [two_smul] at h3
  simpa using h3

theorem rmReact_fderiv_bound (n : ℕ) : ∃ CF' : ℝ, 0 ≤ CF' ∧ ∀ R : Submission.Diff.Alg.Curv4 n, ‖fderiv ℝ (Work.Diff.GE.rmReact n) R‖ ≤ CF' * ‖R‖ := by
  have hcd := rmReact_contDiff_aux n
  have hcont : Continuous (fderiv ℝ (Work.Diff.GE.rmReact n)) := hcd.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : Submission.Diff.Alg.Curv4 n) 1).exists_bound_of_continuousOn
      hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun R => ?_⟩
  rcases eq_or_ne R 0 with rfl | hR
  · simp [rmReact_fderiv_zero_aux n]
  · have hnorm : (0:ℝ) < ‖R‖ := norm_pos_iff.mpr hR
    set x : Submission.Diff.Alg.Curv4 n := (‖R‖)⁻¹ • R with hxdef
    have hxnorm : ‖x‖ = 1 := by
      rw [hxdef, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hnorm,
        inv_mul_cancel₀ (ne_of_gt hnorm)]
    have hxmem : x ∈ Metric.closedBall (0 : Submission.Diff.Alg.Curv4 n) 1 := by
      simp [Metric.mem_closedBall, dist_eq_norm, hxnorm]
    have hxc : (‖R‖ : ℝ) • x = R := by
      rw [hxdef, ← mul_smul, mul_inv_cancel₀ (ne_of_gt hnorm), one_smul]
    have hscale := rmReact_fderiv_smul_aux (n := n) (‖R‖) (ne_of_gt hnorm) x
    rw [hxc] at hscale
    rw [hscale]
    calc ‖(‖R‖ : ℝ) • fderiv ℝ (Work.Diff.GE.rmReact n) x‖
        = ‖R‖ * ‖fderiv ℝ (Work.Diff.GE.rmReact n) x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg R)]
      _ ≤ ‖R‖ * max C 0 :=
          mul_le_mul_of_nonneg_left (le_trans (hC x hxmem) (le_max_left _ _)) (norm_nonneg R)
      _ = max C 0 * ‖R‖ := by ring

end Work.Diff.GE.react
