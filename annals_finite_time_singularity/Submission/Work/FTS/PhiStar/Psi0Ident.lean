/-
# `Work.FTS.PhiStar.Psi0Ident` — the reduced second-derivative identity and the moment

For the explicit model `ψ = psiSol α` (`Psi0Ode.lean`) we prove

* `dthU_psiSol`: `D_θψ = 2cos 2θ·ψ + 4cos²θ·P`;
* `psiSol_sndDeriv`: `ψ'' = 2P − 4ψ − Γ̄` (the reduced form of `Lzero1 ψ = Γ̄`);
* `abs_Kc_le`: `|Kc| ≤ 250π`;
* `psiSol_moment`: `∫_0^{π/2} ψ sinθcos²θ = 0`, the normalisation of the kernel component.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Psi0Ode

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `D_θψ = 2cos 2θ·ψ + 4cos²θ·P` for the explicit model. -/
theorem dthU_psiSol (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.dthU (psiSol α) θ
      = 2 * Real.cos (2 * θ) * psiSol α θ + 4 * Real.cos θ ^ 2 * Pfun α θ := by
  have hS : Real.sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1
    (by linarith [hθ.2, Real.pi_gt_three]))
  have hd : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h := hlin.sin
    convert h using 1
    ring
  have hw : HasDerivAt (fun t : ℝ => Kc α + wZer α t) (Pfun α θ / (Real.sin θ) ^ 2) θ :=
    (hasDerivAt_wZer α hα hα1 hθ).const_add (Kc α)
  have hderiv : deriv (psiSol α) θ
      = 2 * Real.cos (2 * θ) * (Kc α + wZer α θ)
        + Real.sin (2 * θ) * (Pfun α θ / (Real.sin θ) ^ 2) := (hd.mul hw).deriv
  have hpsi : psiSol α θ = Real.sin (2 * θ) * (Kc α + wZer α θ) := rfl
  rw [Work.Spaces.dthU_apply, hderiv, hpsi, Real.sin_two_mul]
  field_simp
  ring

/-- **The reduced second-derivative identity**: `ψ'' = 2P − 4ψ − Γ̄`. -/
theorem psiSol_sndDeriv (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    iteratedDeriv 2 (psiSol α) θ
      = 2 * Pfun α θ - 4 * psiSol α θ - Work.FTS.VocabO.GamBar α θ := by
  have hC : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hS : Real.sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1
    (by linarith [hθ.2, Real.pi_gt_three]))
  have hode := psiSol_ode α hα hα1 hθ
  have hL : Work.FTS.EllipticEst.Lzero1 (psiSol α) θ
      = -iteratedDeriv 2 (psiSol α) θ + deriv (fun t : ℝ => Real.tan t * psiSol α t) θ
        - 6 * psiSol α θ := by
    rw [Work.FTS.EllipticEst.Lzero1]
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hdif : DifferentiableAt ℝ (psiSol α) θ :=
    (((contDiffOn_psiSol α hα hα1).differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ))
  have htan : deriv (fun t : ℝ => Real.tan t * psiSol α t) θ
      = (1 / Real.cos θ ^ 2) * psiSol α θ + Real.tan θ * deriv (psiSol α) θ := by
    have h1 : HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ := Real.hasDerivAt_tan hC
    exact (h1.mul hdif.hasDerivAt).deriv
  have hsin2 : Real.sin (2 * θ) ≠ 0 := by
    rw [Real.sin_two_mul]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hS) hC
  have hdψ : deriv (psiSol α) θ
      = (2 * Real.cos (2 * θ) * psiSol α θ + 4 * Real.cos θ ^ 2 * Pfun α θ)
        / Real.sin (2 * θ) := by
    rw [← dthU_psiSol α hα hα1 hθ, Work.Spaces.dthU_apply]
    field_simp
  rw [hL, htan, hdψ] at hode
  have htanθ : Real.tan θ = Real.sin θ / Real.cos θ := Real.tan_eq_sin_div_cos θ
  have hcos2 : Real.cos (2 * θ) = Real.cos θ ^ 2 - Real.sin θ ^ 2 := Real.cos_two_mul' θ
  have hsq : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  rw [htanθ, hcos2, Real.sin_two_mul] at hode
  have hsq' : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by linarith
  rw [hsq'] at hode
  field_simp at hode
  ring_nf at hode
  have h2 : 2 * Real.cos θ ^ 2 * iteratedDeriv 2 (psiSol α) θ
      = 2 * Real.cos θ ^ 2 * (2 * Pfun α θ - 4 * psiSol α θ
        - Work.FTS.VocabO.GamBar α θ) := by
    linarith [hode]
  exact mul_left_cancel₀ (by positivity : (2 * Real.cos θ ^ 2) ≠ 0) h2

/-- `|Kc| ≤ 250π`. -/
lemma abs_Kc_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) : |Kc α| ≤ 250 * π := by
  have hπ : (0:ℝ) ≤ π / 2 := by linarith [Real.pi_pos]
  have hcont : ContinuousOn (fun θ : ℝ => Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ)
      (Set.uIcc (0:ℝ) (π / 2)) := by
    rw [Set.uIcc_of_le hπ]
    exact continuousOn_wZer' α hα hα1
  have hint : IntervalIntegrable (fun θ : ℝ =>
      |Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ|) volume 0 (π / 2) :=
    hcont.abs.intervalIntegrable
  have h2 : IntervalIntegrable (fun θ : ℝ =>
      (500 * (π / 2)) * (Real.sin θ ^ 2 * Real.cos θ ^ 3)) volume 0 (π / 2) :=
    (by fun_prop : Continuous fun θ : ℝ =>
      (500 * (π/2)) * (Real.sin θ ^ 2 * Real.cos θ ^ 3)).intervalIntegrable _ _
  have h1 : (∫ θ in (0:ℝ)..(π / 2), |Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ|)
      ≤ 500 * (π / 2) * (∫ θ in (0:ℝ)..(π / 2), Real.sin θ ^ 2 * Real.cos θ ^ 3) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hπ hint h2 ?_
    intro θ hθ
    have hSC : 0 ≤ Real.sin θ ^ 2 * Real.cos θ ^ 3 := by
      have h1 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1,
        by linarith [hθ.2, Real.pi_gt_three]⟩
      have h2 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      positivity
    rw [abs_mul, abs_of_nonneg hSC]
    exact mul_le_mul_of_nonneg_left (abs_wZer_le α hα hα1 hθ) hSC |>.trans_eq (by ring)
  have h3 : (∫ θ in (0:ℝ)..(π / 2), Real.sin θ ^ 2 * Real.cos θ ^ 3) = 2 / 15 := by
    rw [integral_sin_sq_cos_cu (0:ℝ) (π/2) hπ, PsiS_zero, PsiS_pi_div_two, sub_zero]
  have h4 := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := fun θ : ℝ =>
    Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ) hπ
  rw [h3] at h1
  have hKc : Kc α = -(15 / 2) * (∫ θ in (0:ℝ)..(π / 2),
      Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ) := rfl
  have hA : |∫ θ in (0:ℝ)..(π / 2), Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ|
      ≤ 500 * (π / 2) * (2 / 15) := h4.trans h1
  rw [hKc, abs_mul]
  have habs : |-((15:ℝ) / 2)| = 15 / 2 := by
    rw [abs_of_neg (by norm_num : -((15:ℝ) / 2) < 0)]; norm_num
  rw [habs]
  calc (15 / 2) * |∫ θ in (0:ℝ)..(π / 2), Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ|
      ≤ (15 / 2) * (500 * (π / 2) * (2 / 15)) :=
        mul_le_mul_of_nonneg_left hA (by norm_num)
    _ = 250 * π := by ring

/-- **The moment condition**: `∫_0^{π/2} ψ sinθcos²θ = 0`. -/
theorem psiSol_moment (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    (∫ θ in Work.Spaces.Iθ, psiSol α θ * Work.Elliptic.sinCos2 θ) = 0 := by
  have hπ : (0:ℝ) ≤ π / 2 := by linarith [Real.pi_pos]
  have hint1 : IntervalIntegrable (fun θ : ℝ =>
      Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ) volume 0 (π / 2) := by
    have hcont : ContinuousOn (fun θ : ℝ => Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ)
        (Set.uIcc (0:ℝ) (π / 2)) := by
      rw [Set.uIcc_of_le hπ]
      exact continuousOn_wZer' α hα hα1
    exact hcont.intervalIntegrable
  have hint2 : IntervalIntegrable (fun θ : ℝ =>
      (2 * Kc α) * (Real.sin θ ^ 2 * Real.cos θ ^ 3)) volume 0 (π / 2) :=
    (by fun_prop : Continuous fun θ : ℝ =>
      (2 * Kc α) * (Real.sin θ ^ 2 * Real.cos θ ^ 3)).intervalIntegrable _ _
  have hint3 : IntervalIntegrable (fun θ : ℝ =>
      2 * (Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ)) volume 0 (π / 2) :=
    hint1.const_mul 2
  have hpt : ∀ θ : ℝ, psiSol α θ * Work.Elliptic.sinCos2 θ
      = 2 * (Kc α + wZer α θ) * (Real.sin θ ^ 2 * Real.cos θ ^ 3) := by
    intro θ
    simp only [psiSol, Work.Elliptic.sinCos2, Real.sin_two_mul]
    ring
  have key : (∫ θ in (0:ℝ)..(π / 2), psiSol α θ * Work.Elliptic.sinCos2 θ)
      = 2 * Kc α * (∫ θ in (0:ℝ)..(π / 2), Real.sin θ ^ 2 * Real.cos θ ^ 3)
        + 2 * (∫ θ in (0:ℝ)..(π / 2), Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ) := by
    rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
    rw [show (fun θ : ℝ => 2 * (Kc α + wZer α θ) * (Real.sin θ ^ 2 * Real.cos θ ^ 3))
        = fun θ => (2 * Kc α) * (Real.sin θ ^ 2 * Real.cos θ ^ 3)
          + 2 * (Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ) by
      funext θ; ring]
    rw [intervalIntegral.integral_add hint2 hint3, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hval : (∫ θ in (0:ℝ)..(π / 2), Real.sin θ ^ 2 * Real.cos θ ^ 3) = 2 / 15 := by
    rw [integral_sin_sq_cos_cu (0:ℝ) (π/2) hπ, PsiS_zero, PsiS_pi_div_two, sub_zero]
  have hKc : Kc α = -(15 / 2) * (∫ θ in (0:ℝ)..(π / 2),
      Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ) := rfl
  rw [hval, hKc] at key
  have hzero : 2 * (-(15 / 2) * (∫ θ in (0:ℝ)..(π / 2),
      Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ)) * (2 / 15)
      + 2 * (∫ θ in (0:ℝ)..(π / 2), Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ) = 0 := by
    ring
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hπ, key]
  ring

end Work.FTS.PhiStar
