/-
# The local bound at a coincidence

This file proves `Work.Asymptotics.KaxisMid.exists_local_bound_coincidence`: at a parameter
point `p = (τ₀,t₀) ∈ K × [ε,1]` with `j τ₀ = j (i t₀)` the kernel is bounded on a neighbourhood
of `p`.

By `Work.Asymptotics.KaxisMid.eq_or_eq_S_of_re_eq_zero` the coincidence lies on one of the two branches
`z = τ` and `z = S τ`, on which the cleared kernel vanishes
(`Work.Residues.KPlusClear_diag`, `Work.Asymptotics.KClear_S_vanishing`).  Two situations occur:

* `τ₀ ≠ i`: the difference quotient of `j` is bounded below on a neighbourhood of the diagonal
  (`Work.Asymptotics.KaxisMid.exists_diffQuotient_lower`), and the one-zero bound for the
  holomorphic function `z ↦ KfunClear(τ,z)` gives the comparison;
* `τ₀ = i` (hence `t₀ = 1` and `z₀ = i`): the two branches merge and `j'(i) = 0`, so the
  *two*-zero bound (`Work.Asymptotics.KaxisMid.norm_le_of_norm_le_of_two_zeros`) and the
  `λ`-comparison `Work.Asymptotics.KaxisMid.exists_j_sub_lower_lambda_near_I` together with
  `Work.Asymptotics.KaxisMid.exists_lambdaFun_lipschitz` give the comparison.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.Theorem31
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Kernels.KernelGrowth
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.KClear_mg2
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic
import Submission.Work.Kernels.ClearLink.KPlusClear_eq_smul
import Submission.Work.Kernels.ClearLink.KMinusClear_eq_smul
import Submission.Work.Residues.KPlusClear_diag
import Submission.Work.Residues.KMinusClear_diag
import Submission.Work.Asymptotics.KClear_S_vanishing
import Submission.Work.Asymptotics.orbit_imagAxis_of_mem_DomainD
import Submission.Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Rigidity.LambdaBasic
import Submission.Work.Kernels.LogLambda.LambdaLaws
import Submission.Work.Asymptotics.KaxisMid.Basic
import Submission.Work.Asymptotics.KaxisMid.Classify
import Submission.Work.Asymptotics.KaxisMid.Main
import Submission.Work.Asymptotics.KaxisMid.norm_le_of_norm_le_of_two_zeros
import Submission.Work.Asymptotics.KaxisMid.exists_lambdaFun_lipschitz
import Submission.Work.Asymptotics.KaxisMid.exists_diffQuotient_lower
import Submission.Work.Asymptotics.KaxisMid.exists_j_sub_lower_lambda_near_I
import Submission.Work.Asymptotics.KaxisMid.exists_bound_Kfun_of_coincidence

set_option maxHeartbeats 4000000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped Topology MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Asymptotics.KaxisMid

open Work.Kernels

/-! ## The one-zero bound -/

/-- **One-zero bound.**  A function holomorphic on the ball `ball c ρ` which vanishes at a point
`z₁ ∈ ball c (ρ/2)` is bounded by `(2 M / ρ) ‖z - z₁‖` on `ball c (ρ/2)`. -/
theorem norm_le_of_norm_le_of_zero {f : ℂ → ℂ} {c : ℂ} {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M)
    (hf : DiffContOnCl ℂ f (Metric.ball c ρ)) (hbd : ∀ z ∈ Metric.ball c ρ, ‖f z‖ ≤ M)
    {z₁ : ℂ} (h₁ : z₁ ∈ Metric.ball c (ρ / 2)) (hf₁ : f z₁ = 0) :
    ∀ z ∈ Metric.ball c (ρ / 2), ‖f z‖ ≤ (2 * M / ρ) * ‖z - z₁‖ := by
  intro z hz
  have hhalfball : ∀ w : ℂ, dist w c < ρ / 2 → Metric.closedBall w (ρ / 2) ⊆ Metric.ball c ρ := by
    intro w hw u hu
    rw [Metric.mem_closedBall] at hu
    rw [Metric.mem_ball]
    have h1 : dist u c ≤ dist u w + dist w c := dist_triangle _ _ _
    linarith [hρ]
  have hderiv : ∀ w : ℂ, dist w c < ρ / 2 → ‖deriv f w‖ ≤ M / (ρ / 2) := by
    intro w hw
    have hsub := hhalfball w hw
    have hdwc : DiffContOnCl ℂ f (Metric.ball w (ρ / 2)) := by
      refine ⟨hf.differentiableOn.mono (fun y hy => hsub (Metric.ball_subset_closedBall hy)), ?_⟩
      refine hf.continuousOn.mono ?_
      rw [closure_ball _ (by positivity)]
      intro y hy
      exact subset_closure (hsub hy)
    have hsphere : ∀ u ∈ Metric.sphere w (ρ / 2), ‖f u‖ ≤ M := by
      intro u hu
      refine hbd u (hsub ?_)
      rw [Metric.mem_sphere] at hu
      rw [Metric.mem_closedBall, hu]
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) hdwc hsphere
  have hconv : Convex ℝ (Metric.ball c (ρ / 2)) := convex_ball c (ρ / 2)
  have hdiff : ∀ x ∈ Metric.ball c (ρ / 2), DifferentiableAt ℂ f x := by
    intro x hx
    refine hf.differentiableOn.differentiableAt ?_
    rw [Metric.mem_nhds_iff]
    refine ⟨ρ / 2, by positivity, fun y hy => ?_⟩
    rw [Metric.mem_ball] at hy ⊢
    calc dist y c ≤ dist y x + dist x c := dist_triangle _ _ _
      _ < ρ / 2 + ρ / 2 := add_lt_add hy (Metric.mem_ball.mp hx)
      _ = ρ := by ring
  have hbound : ∀ x ∈ Metric.ball c (ρ / 2), ‖deriv f x‖ ≤ M / (ρ / 2) :=
    fun x hx => hderiv x (Metric.mem_ball.mp hx)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound hconv hz h₁
  have h' : ‖f z‖ ≤ M / (ρ / 2) * ‖z - z₁‖ := by
    simpa [hf₁, norm_sub_rev] using h
  calc ‖f z‖ ≤ M / (ρ / 2) * ‖z - z₁‖ := h'
    _ = (2 * M / ρ) * ‖z - z₁‖ := by
        congr 1
        field_simp

/-! ## The action of `S` and the vanishing of the cleared kernel on the branches -/

lemma coe_S_smul (z : ℍ) : ((ModularGroup.S • z : ℍ) : ℂ) = -1 / (z : ℂ) := by
  have h : (ModularGroup.S • z : ℍ) = ⟨(-(z : ℂ))⁻¹, z.im_inv_neg_coe_pos⟩ :=
    UpperHalfPlane.modular_S_smul z
  rw [h]
  show (-(z : ℂ))⁻¹ = -1 / (z : ℂ)
  rw [div_eq_mul_inv, inv_neg, neg_mul, one_mul]

lemma S_smul_S_smul (z : ℍ) : ModularGroup.S • (ModularGroup.S • z) = z := by
  have hSS : ModularGroup.S * ModularGroup.S = (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) := by
    decide
  rw [← mul_smul, hSS, ModularGroup.SL_neg_smul, one_smul]

lemma coe_S_sub_I (w : ℍ) :
    ((ModularGroup.S • w : ℍ) : ℂ) - Complex.I
      = ((w : ℂ) - Complex.I) / ((w : ℂ) * Complex.I) := by
  have hI : (Complex.I : ℂ) = -1 / Complex.I := by
    rw [div_eq_mul_inv, Complex.inv_I]; ring
  rw [coe_S_smul, hI]
  field_simp [UpperHalfPlane.ne_zero w, Complex.I_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `S` moves points near `i` by at most `2` times their distance to `i`. -/
lemma norm_S_sub_I_le (w : ℍ) (hw : (1:ℝ) / 2 ≤ ‖(w : ℂ)‖) :
    ‖((ModularGroup.S • w : ℍ) : ℂ) - Complex.I‖ ≤ 4 * ‖(w : ℂ) - Complex.I‖ := by
  rw [coe_S_sub_I, norm_div, norm_mul, Complex.norm_I, mul_one]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg ((w : ℂ) - Complex.I), hw]

lemma KfunClear_self_eq_zero (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    KfunClear ℓ d z z = 0 := by
  simp only [KfunClear, Residues.KPlusClear_diag d hd z, Residues.KMinusClear_diag ℓ d hd z,
    zero_add, zero_div]

lemma KfunClear_S_eq_zero (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    KfunClear ℓ d (ModularGroup.S • z) z = 0 := by
  obtain ⟨h1, h2⟩ := KClear_S_vanishing ℓ d hd z
  simp only [KfunClear, h1, h2, zero_add, zero_div]

lemma KfunClear_smul_S_eq_zero (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    KfunClear ℓ d z (ModularGroup.S • z) = 0 := by
  have h := KfunClear_S_eq_zero ℓ d hd (ModularGroup.S • z)
  rwa [S_smul_S_smul] at h

/-- The `λ`-value of `i`. -/
lemma lambdaFun_I : lambdaFun (imagAxis 1 one_pos) = 1 / 2 := by
  have hS : ModularGroup.S • imagAxis 1 one_pos = imagAxis 1 one_pos := by
    apply UpperHalfPlane.ext
    rw [coe_S_smul, imagAxis_coe]
    field_simp
    norm_num [Complex.I_sq]
  have h1 : lambdaFun (imagAxis 1 one_pos) = lambdaSFun (imagAxis 1 one_pos) := by
    have := LogLambda.lambdaFun_S (imagAxis 1 one_pos)
    rwa [hS] at this
  have h2' : lambdaFun (imagAxis 1 one_pos) + lambdaFun (imagAxis 1 one_pos) = 1 := by
    have h := Work.Rigidity.lambdaFun_add_lambdaSFun (imagAxis 1 one_pos)
    rw [← h1] at h
    exact h
  have h3 : (2 : ℂ) * lambdaFun (imagAxis 1 one_pos) = 1 := by
    rw [two_mul]; exact h2'
  exact (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).mpr (by rw [mul_comm]; exact h3)

end Work.Asymptotics.KaxisMid