import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxTauGen
import Submission.Work.BoseFixB1S.BoxPotOper
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxD1Defs` — vocabulary of the genuine box D1 pairing chain

The genuine box `τ`-operators `boxTauAnnGen`/`boxTauDagGen` and the mean-free windowed
modes `boxWinModeReGen`/`boxWinModeImGen` live in `BoxTauGen.lean`.  This module adds their
**complex** combination

    `boxWinModeC volA A χ p z = 1_A(z)·(χ z e^{−i⟪p,z⟫} − volA⁻¹∫_A χ e^{−i⟪p,·⟫})`

together with the elementary facts (`boxWinModeC_eq`, parity, mean-vanishing, continuity) that
the port of the corpus D1 chain to the box uses.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- The complex `Q_A`-projected (mean-free) windowed exponential
`1_A(z)·(χ z e^{−i⟪p,z⟫} − volA⁻¹ ∫_A χ e^{−i⟪p,·⟫})`; its real and imaginary parts are the
`Work.BoseFixB1.boxWinModeReGen` / `boxWinModeImGen` of `BoxTauGen.lean`. -/
noncomputable def boxWinModeC (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (p z : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  A.indicator (fun _ => (1 : ℂ)) z
    * ((χ z : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ)))
        - (((volA⁻¹ : ℝ)) : ℂ) * ∫ w in A,
            (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ))))

/-- `e^{−iθ} = cos θ − i sin θ`. -/
lemma cexp_neg_I_eq (θ : ℝ) :
    Complex.exp (-(Complex.I * (θ : ℂ)))
      = (Real.cos θ : ℂ) - Complex.I * (Real.sin θ : ℂ) := by
  have h : -(Complex.I * (θ : ℂ)) = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I]
  simp only [Complex.ofReal_neg, Real.cos_neg, Real.sin_neg]
  ring

lemma cexp_neg_I_re (θ : ℝ) : (Complex.exp (-(Complex.I * (θ : ℂ)))).re = Real.cos θ := by
  rw [cexp_neg_I_eq, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  simp

lemma cexp_neg_I_im (θ : ℝ) : (Complex.exp (-(Complex.I * (θ : ℂ)))).im = - Real.sin θ := by
  rw [cexp_neg_I_eq, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  simp

/-- Complex integral of the windowed exponential:
`∫_A χ e^{−i⟪p,·⟫} = ∫_A χ cos⟪p,·⟫ − i∫_A χ sin⟪p,·⟫`. -/
lemma boxChat_eq {A : Set (EuclideanSpace ℝ (Fin 3))}
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    (∫ w in A, (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ))))
      = ((∫ w in A, χ w * Real.cos (inner ℝ p w) : ℝ) : ℂ)
        - Complex.I * ((∫ w in A, χ w * Real.sin (inner ℝ p w) : ℝ) : ℂ) := by
  have hconte : Continuous (fun w : EuclideanSpace ℝ (Fin 3) =>
      (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ)))) :=
    (Complex.continuous_ofReal.comp hχc).mul (Complex.continuous_exp.comp (by fun_prop))
  have hsuppe : HasCompactSupport (fun w : EuclideanSpace ℝ (Fin 3) =>
      (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ)))) :=
    (hχs.comp_left (g := fun z : ℝ => (z : ℂ)) (by simp)).mul_right
      (f' := fun w : EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ))))
  have hfe : Integrable (fun w : EuclideanSpace ℝ (Fin 3) =>
      (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ)))) volume :=
    hconte.integrable_of_hasCompactSupport hsuppe
  have hc : Continuous (fun w : EuclideanSpace ℝ (Fin 3) => χ w * Real.cos (inner ℝ p w)) :=
    hχc.mul (Real.continuous_cos.comp (by fun_prop))
  have hs : Continuous (fun w : EuclideanSpace ℝ (Fin 3) => χ w * Real.sin (inner ℝ p w)) :=
    hχc.mul (Real.continuous_sin.comp (by fun_prop))
  have hconsc : Integrable (fun w : EuclideanSpace ℝ (Fin 3) =>
      χ w * Real.cos (inner ℝ p w)) volume :=
    hc.integrable_of_hasCompactSupport
      (hχs.mul_right (f' := fun w : EuclideanSpace ℝ (Fin 3) => Real.cos (inner ℝ p w)))
  have hconss : Integrable (fun w : EuclideanSpace ℝ (Fin 3) =>
      χ w * Real.sin (inner ℝ p w)) volume :=
    hs.integrable_of_hasCompactSupport
      (hχs.mul_right (f' := fun w : EuclideanSpace ℝ (Fin 3) => Real.sin (inner ℝ p w)))
  have hfc : Integrable (fun w : EuclideanSpace ℝ (Fin 3) =>
      ((χ w * Real.cos (inner ℝ p w) : ℝ) : ℂ)) volume := hconsc.ofReal
  have hfs : Integrable (fun w : EuclideanSpace ℝ (Fin 3) =>
      ((χ w * Real.sin (inner ℝ p w) : ℝ) : ℂ)) volume := hconss.ofReal
  have hpt : ∀ w : EuclideanSpace ℝ (Fin 3),
      (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ)))
        = ((χ w * Real.cos (inner ℝ p w) : ℝ) : ℂ)
          - Complex.I * ((χ w * Real.sin (inner ℝ p w) : ℝ) : ℂ) := by
    intro w
    rw [show Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ)))
        = ((Real.cos (inner ℝ p w) : ℝ) : ℂ)
          - Complex.I * ((Real.sin (inner ℝ p w) : ℝ) : ℂ) from by
      have h : -(Complex.I * (((inner ℝ p w : ℝ)) : ℂ))
          = ((-(inner ℝ p w) : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [h, Complex.exp_ofReal_mul_I]
      simp only [Complex.ofReal_neg, Real.cos_neg, Real.sin_neg]
      ring]
    push_cast
    ring
  have hg : Integrable (fun w : EuclideanSpace ℝ (Fin 3) =>
      Complex.I * ((χ w * Real.sin (inner ℝ p w) : ℝ) : ℂ)) volume := hfs.const_mul Complex.I
  calc (∫ w in A, (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ))))
      = ∫ w in A, (((χ w * Real.cos (inner ℝ p w) : ℝ) : ℂ)
          - Complex.I * ((χ w * Real.sin (inner ℝ p w) : ℝ) : ℂ)) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ w in A, ((χ w * Real.cos (inner ℝ p w) : ℝ) : ℂ))
          - ∫ w in A, Complex.I * ((χ w * Real.sin (inner ℝ p w) : ℝ) : ℂ) :=
        MeasureTheory.integral_sub hfc.integrableOn hg.integrableOn
    _ = ((∫ w in A, χ w * Real.cos (inner ℝ p w) : ℝ) : ℂ)
          - Complex.I * ((∫ w in A, χ w * Real.sin (inner ℝ p w) : ℝ) : ℂ) := by
        rw [MeasureTheory.integral_const_mul]
        rw [show (∫ w in A, ((χ w * Real.cos (inner ℝ p w) : ℝ) : ℂ))
              = ((∫ w in A, χ w * Real.cos (inner ℝ p w) : ℝ) : ℂ) from
            Complex.ofRealCLM.integral_comp_comm (φ := fun w => χ w * Real.cos (inner ℝ p w))
              (φ_int := hconsc.integrableOn)]
        rw [show (∫ w in A, ((χ w * Real.sin (inner ℝ p w) : ℝ) : ℂ))
              = ((∫ w in A, χ w * Real.sin (inner ℝ p w) : ℝ) : ℂ) from
            Complex.ofRealCLM.integral_comp_comm (φ := fun w => χ w * Real.sin (inner ℝ p w))
              (φ_int := hconss.integrableOn)]

/-- The complex mode is the sum of the two real modes:
`boxWinModeC = boxWinModeReGen + i·boxWinModeImGen`. -/
lemma boxWinModeC_eq (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (p z : EuclideanSpace ℝ (Fin 3)) :
    boxWinModeC volA A χ p z
      = (boxWinModeReGen volA A χ p z : ℂ)
        + Complex.I * (boxWinModeImGen volA A χ p z : ℂ) := by
  rw [boxWinModeC]
  rw [boxChat_eq hχc hχs p]
  rw [boxWinModeReGen, boxWinModeImGen]
  rw [cexp_neg_I_eq]
  have hAind : A.indicator (fun _ => (1 : ℂ)) z
      = ((A.indicator (fun _ => (1 : ℝ)) z : ℝ) : ℂ) := by
    by_cases hz : z ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
  rw [hAind]
  push_cast
  ring

/-- Real part of the complex mode. -/
lemma boxWinModeC_re (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (p z : EuclideanSpace ℝ (Fin 3)) :
    (boxWinModeC volA A χ p z).re = boxWinModeReGen volA A χ p z := by
  rw [boxWinModeC_eq volA A hχc hχs p z]; simp

/-- Imaginary part of the complex mode. -/
lemma boxWinModeC_im (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (p z : EuclideanSpace ℝ (Fin 3)) :
    (boxWinModeC volA A χ p z).im = boxWinModeImGen volA A χ p z := by
  rw [boxWinModeC_eq volA A hχc hχs p z]; simp

/-- The complexified genuine D1 creation operator at the box `A`:
`(|A|)^{−1/2}Σ_i 1_A(x_i)g(x_i)∫_A Ψ(x_{i←z})dz` for a complex mode `g` — the ℂ-valued
version of `Work.BoseFixB1.boxTauDagGen`. -/
noncomputable def boxTauDagGenC {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (g : EuclideanSpace ℝ (Fin 3) → ℂ) (Ψ : Submission.BoseGases.X N → ℂ)
    (x : Submission.BoseGases.X N) : ℂ :=
  (Real.sqrt volA)⁻¹ * ∑ i : Fin N,
    A.indicator (fun _ => (1 : ℂ)) (x i) * g (x i)
      * ∫ z in A, Ψ (Function.update x i z)

/-- The complexified genuine D1 annihilation operator at the box `A`. -/
noncomputable def boxTauAnnGenC {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (g : EuclideanSpace ℝ (Fin 3) → ℂ) (Ψ : Submission.BoseGases.X N → ℂ)
    (x : Submission.BoseGases.X N) : ℂ :=
  (Real.sqrt volA)⁻¹ * ∑ i : Fin N,
    A.indicator (fun _ => (1 : ℂ)) (x i)
      * ∫ z in A, g z * Ψ (Function.update x i z)

end Work.BoseFixB1
