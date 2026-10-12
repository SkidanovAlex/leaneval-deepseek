import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Submission.Work.BoseFixB1S.CubeWindowSymbol
import Submission.Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Gradient Plancherel for a `C¹` compactly supported real function

The target identity

`(2π)⁻³ ∫_q ‖q‖²‖kinFT f q‖² = ∫_z ‖∇f(z)‖²`  (`f : ℝ³ → ℝ`, `C¹`, compactly supported)

is Plancherel's theorem applied to the three partial derivatives of `f`.  The route:

* `kinFT g p = 𝓕 g ((2π)⁻¹ • p)` (`kinFT_eq_fourier`, valid for *any* `g`);
* the Fourier transform of the directional derivative
  (`Real.fourier_fderiv`, applied to the complexification `F` of `f`, together with
  `Real.fourier_continuousLinearMap_apply` to pass to the `e_k`-component and
  `VectorFourier.fourierSMulRight_apply` to evaluate the multiplier):
  `kinFT (∂_{e_k} F) p = I ⟪p, e_k⟫ · kinFT F p`;
* Plancherel in the `kinFT` convention for `L¹ ∩ L²` functions
  (`kinFT_l1l2_plancherel`) applied to each `∂_{e_k} F`;
* Parseval for the coordinate basis `Σ_k ⟪ξ, e_k⟫² = ‖ξ‖²` and
  `‖∇f z‖² = Σ_k (∂_{e_k} f z)²`.
-/

noncomputable section

open MeasureTheory Filter
open scoped FourierTransform ContDiff BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option maxHeartbeats 800000

/-- **The `kinFT`-transform of a directional derivative.**  For `F : ℝ³ → ℂ` integrable,
differentiable with integrable derivative, and every coordinate direction `e_k`,

`kinFT (fun x => fderiv ℝ F x e_k) p = I ⟪p, e_k⟫ · kinFT F p`. -/
lemma kinFT_fderiv_apply {F : ℝ³ → ℂ}
    (hF : Integrable F) (hdF : Differentiable ℝ F) (hdFi : Integrable (fderiv ℝ F))
    (k : Fin 3) (p : ℝ³) :
    kinFT (fun x => fderiv ℝ F x (kcStdBasis k)) p
      = Complex.I * (inner ℝ p (kcStdBasis k) : ℂ) * kinFT F p := by
  have hsl : (((-innerSL ℝ) ((2 * Real.pi)⁻¹ • p)) (kcStdBasis k))
      = -((2 * Real.pi)⁻¹ * inner ℝ p (kcStdBasis k)) := by
    change -(((innerSL ℝ) ((2 * Real.pi)⁻¹ • p)) (kcStdBasis k))
      = -((2 * Real.pi)⁻¹ * inner ℝ p (kcStdBasis k))
    rw [innerSL_apply_apply, real_inner_smul_left]
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have h1 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero h1
  have hAB : (-(2 * (Real.pi : ℂ) * Complex.I)) *
        (-((2 * (Real.pi : ℂ))⁻¹ * (inner ℝ p (kcStdBasis k) : ℂ)))
      = Complex.I * (inner ℝ p (kcStdBasis k) : ℂ) := by
    calc (-(2 * (Real.pi : ℂ) * Complex.I)) *
          (-((2 * (Real.pi : ℂ))⁻¹ * (inner ℝ p (kcStdBasis k) : ℂ)))
        = ((2 * (Real.pi : ℂ)) * (2 * (Real.pi : ℂ))⁻¹) *
            (Complex.I * (inner ℝ p (kcStdBasis k) : ℂ)) := by ring
      _ = 1 * (Complex.I * (inner ℝ p (kcStdBasis k) : ℂ)) := by
            rw [mul_inv_cancel₀ hpi]
      _ = Complex.I * (inner ℝ p (kcStdBasis k) : ℂ) := by ring
  calc kinFT (fun x => fderiv ℝ F x (kcStdBasis k)) p
      = (𝓕 (fderiv ℝ F) ((2 * Real.pi)⁻¹ • p)) (kcStdBasis k) := by
        rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
        exact (Real.fourier_continuousLinearMap_apply (f := fderiv ℝ F) (a := kcStdBasis k)
          (v := (2 * Real.pi)⁻¹ • p) hdFi).symm
    _ = (VectorFourier.fourierSMulRight (-innerSL ℝ) (𝓕 F) ((2 * Real.pi)⁻¹ • p))
          (kcStdBasis k) := by
        rw [Real.fourier_fderiv hF hdF hdFi]
    _ = -(2 * ↑Real.pi * Complex.I) •
          (((-innerSL ℝ) ((2 * Real.pi)⁻¹ • p)) (kcStdBasis k)) •
            𝓕 F ((2 * Real.pi)⁻¹ • p) := by
        rw [VectorFourier.fourierSMulRight_apply]
    _ = -(2 * ↑Real.pi * Complex.I) •
          (-((2 * Real.pi)⁻¹ * inner ℝ p (kcStdBasis k))) • kinFT F p := by
        rw [hsl, ← Work.SmallBoxBridge.Resolve.kinFT_eq_fourier F p]
    _ = Complex.I * (inner ℝ p (kcStdBasis k) : ℂ) * kinFT F p := by
        rw [smul_eq_mul, Complex.real_smul]
        push_cast
        rw [show (-(2 * (Real.pi : ℂ) * Complex.I)) *
              (-((2 * (Real.pi : ℂ))⁻¹ * (inner ℝ p (kcStdBasis k) : ℂ)) * kinFT F p)
            = ((-(2 * (Real.pi : ℂ) * Complex.I)) *
                (-((2 * (Real.pi : ℂ))⁻¹ * (inner ℝ p (kcStdBasis k) : ℂ)))) * kinFT F p
            from (mul_assoc _ _ _).symm, hAB]

theorem gradient_plancherel_of_contDiff_one {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ 1 f) (hcs : HasCompactSupport f) :
    ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ q : EuclideanSpace ℝ (Fin 3),
          ‖q‖ ^ 2 * ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (f z : ℂ)) q‖ ^ 2)
      = ∫ z : EuclideanSpace ℝ (Fin 3), ‖gradient f z‖ ^ 2 := by
  let F : ℝ³ → ℂ := fun z => (f z : ℂ)
  change ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : ℝ³, ‖q‖ ^ 2 * ‖kinFT F q‖ ^ 2)
      = ∫ z : ℝ³, ‖gradient f z‖ ^ 2
  have hF_eq : F = ⇑Complex.ofRealCLM ∘ f := by
    funext z
    simp [F, Complex.ofRealCLM_apply]
  have hF_cd : ContDiff ℝ 1 F := by
    rw [hF_eq]
    exact Complex.ofRealCLM.contDiff.comp hf
  have hF_cont : Continuous F := hF_cd.continuous
  have hf_diff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hF_diff : Differentiable ℝ F := hF_cd.differentiable (by norm_num)
  have hF_cs : HasCompactSupport F := by
    rw [hF_eq]
    exact hcs.comp_left (by simp)
  have hF_int : Integrable F := hF_cont.integrable_of_hasCompactSupport hF_cs
  have hF_mlp : MemLp F 2 := hF_cont.memLp_of_hasCompactSupport hF_cs
  have hFderiv_int : Integrable (fderiv ℝ F) :=
    (hF_cd.continuous_fderiv (by norm_num)).integrable_of_hasCompactSupport (hF_cs.fderiv ℝ)
  have hDk_cont : ∀ k : Fin 3, Continuous (fun x : ℝ³ => fderiv ℝ F x (kcStdBasis k)) :=
    fun k => (hF_cd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDk_cs : ∀ k : Fin 3, HasCompactSupport (fun x : ℝ³ => fderiv ℝ F x (kcStdBasis k)) :=
    fun k => hF_cs.fderiv_apply ℝ (kcStdBasis k)
  have hDk_int : ∀ k : Fin 3, Integrable (fun x : ℝ³ => fderiv ℝ F x (kcStdBasis k)) :=
    fun k => (hDk_cont k).integrable_of_hasCompactSupport (hDk_cs k)
  have hDk_mlp : ∀ k : Fin 3, MemLp (fun x : ℝ³ => fderiv ℝ F x (kcStdBasis k)) 2 :=
    fun k => (hDk_cont k).memLp_of_hasCompactSupport (hDk_cs k)
  have hDk_sq_int : ∀ k : Fin 3,
      Integrable (fun p : ℝ³ => ‖kinFT (fun x : ℝ³ => fderiv ℝ F x (kcStdBasis k)) p‖ ^ 2) :=
    fun k => (memLp_two_iff_integrable_sq_norm (Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable
        (hDk_int k)).aestronglyMeasurable).mp
      (Work.BoseKinLoc.Momentum.memLp_kinFT (hDk_int k) (hDk_mlp k))
  have hGk_int : ∀ k : Fin 3,
      Integrable (fun x : ℝ³ => ‖fderiv ℝ F x (kcStdBasis k)‖ ^ 2) :=
    fun k => (memLp_two_iff_integrable_sq_norm (hDk_cont k).aestronglyMeasurable).mp (hDk_mlp k)
  have hNorm : ∀ a : ℝ, ‖((a : ℝ) : ℂ)‖ ^ 2 = a ^ 2 := fun a => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  have hpt : ∀ (k : Fin 3) (p : ℝ³),
      ‖kinFT (fun x : ℝ³ => fderiv ℝ F x (kcStdBasis k)) p‖ ^ 2
        = (inner ℝ p (kcStdBasis k)) ^ 2 * ‖kinFT F p‖ ^ 2 := by
    intro k p
    rw [kinFT_fderiv_apply hF_int hF_diff hFderiv_int k p, norm_mul, norm_mul, Complex.norm_I,
      one_mul, mul_pow, hNorm (inner ℝ p (kcStdBasis k))]
  have hInt_k : ∀ k : Fin 3,
      Integrable (fun p : ℝ³ => (inner ℝ p (kcStdBasis k)) ^ 2 * ‖kinFT F p‖ ^ 2) := by
    intro k
    exact (hDk_sq_int k).congr (Eventually.of_forall fun p => hpt k p)
  have hfderivF : ∀ z : ℝ³, fderiv ℝ F z = Complex.ofRealCLM.comp (fderiv ℝ f z) := by
    intro z
    rw [hF_eq, fderiv_comp z Complex.ofRealCLM.differentiable.differentiableAt (hf_diff z),
      (Complex.ofRealCLM.hasFDerivAt (x := f z)).fderiv]
  have hDgrad : ∀ (z : ℝ³) (k : Fin 3),
      ‖fderiv ℝ F z (kcStdBasis k)‖ ^ 2
        = (inner ℝ (gradient f z) (kcStdBasis k)) ^ 2 := by
    intro z k
    rw [hfderivF z, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, hNorm,
      inner_gradient_left]
  have hsum : ∀ z : ℝ³,
      (∑ k : Fin 3, ‖fderiv ℝ F z (kcStdBasis k)‖ ^ 2) = ‖gradient f z‖ ^ 2 := by
    intro z
    refine (Finset.sum_congr rfl (fun k _ => hDgrad z k)).trans ?_
    exact sum_inner_kcStdBasis_sq (gradient f z)
  have hmain : (∫ p : ℝ³, ‖p‖ ^ 2 * ‖kinFT F p‖ ^ 2)
      = (2 * Real.pi) ^ 3 * ∫ z : ℝ³, ‖gradient f z‖ ^ 2 := by
    calc (∫ p : ℝ³, ‖p‖ ^ 2 * ‖kinFT F p‖ ^ 2)
        = ∫ p : ℝ³, ∑ k : Fin 3,
            (inner ℝ p (kcStdBasis k)) ^ 2 * ‖kinFT F p‖ ^ 2 := by
          refine integral_congr_ae (Eventually.of_forall fun p => ?_)
          have h1 := Finset.sum_mul (s := Finset.univ)
            (f := fun k : Fin 3 => (inner ℝ p (kcStdBasis k)) ^ 2) (a := ‖kinFT F p‖ ^ 2)
          have h2 : (∑ k : Fin 3, (inner ℝ p (kcStdBasis k)) ^ 2) * ‖kinFT F p‖ ^ 2
              = ‖p‖ ^ 2 * ‖kinFT F p‖ ^ 2 := by
            rw [sum_inner_kcStdBasis_sq]
          exact h2.symm.trans h1
        _ = ∑ k : Fin 3, ∫ p : ℝ³,
              (inner ℝ p (kcStdBasis k)) ^ 2 * ‖kinFT F p‖ ^ 2 :=
            integral_finsetSum Finset.univ (f := fun k p =>
              (inner ℝ p (kcStdBasis k)) ^ 2 * ‖kinFT F p‖ ^ 2) (fun k _ => hInt_k k)
        _ = ∑ k : Fin 3, ∫ p : ℝ³,
              ‖kinFT (fun x : ℝ³ => fderiv ℝ F x (kcStdBasis k)) p‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          refine integral_congr_ae (Eventually.of_forall fun p => ?_)
          exact (hpt k p).symm
        _ = ∑ k : Fin 3, (2 * Real.pi) ^ 3 *
              ∫ x : ℝ³, ‖fderiv ℝ F x (kcStdBasis k)‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          exact Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel (hDk_int k) (hDk_mlp k)
        _ = (2 * Real.pi) ^ 3 * ∑ k : Fin 3,
              ∫ x : ℝ³, ‖fderiv ℝ F x (kcStdBasis k)‖ ^ 2 :=
            (Finset.mul_sum (s := Finset.univ) (f := fun k : Fin 3 =>
              ∫ x : ℝ³, ‖fderiv ℝ F x (kcStdBasis k)‖ ^ 2) (a := (2 * Real.pi) ^ 3)).symm
        _ = (2 * Real.pi) ^ 3 * ∫ x : ℝ³, ∑ k : Fin 3,
              ‖fderiv ℝ F x (kcStdBasis k)‖ ^ 2 := by
          rw [integral_finsetSum Finset.univ (f := fun k x =>
            ‖fderiv ℝ F x (kcStdBasis k)‖ ^ 2) (fun k _ => hGk_int k)]
        _ = (2 * Real.pi) ^ 3 * ∫ z : ℝ³, ‖gradient f z‖ ^ 2 := by
          congr 1
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          exact hsum z
  rw [hmain, inv_mul_cancel_left₀ (pow_ne_zero 3 (by positivity : (2 * Real.pi : ℝ) ≠ 0))]

end Work.BoseFixB1S
