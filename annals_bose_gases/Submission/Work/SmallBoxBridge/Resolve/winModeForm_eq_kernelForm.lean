import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SmallBoxBridge.Resolve.integrable_kinFT_fubini
import Submission.Work.SmallBoxBridge.Resolve.integrable_winMode_reIntegrand
import Submission.Work.SmallBoxBridge.Resolve.kinKernelC_eq_ofReal_aux
import Submission.Work.SmallBoxBridge.Resolve.kinKernel_aestronglyMeasurable
import Submission.Work.SmallBoxBridge.Resolve.kinKernel_bdd
import Submission.Work.SmallBoxBridge.Resolve.kinKernel_even
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The (c1) kernel identity: `winModeForm χ F u = ∫_x (χ u)(x)·(K_F ⋆ (χ u))(x)`

This is the (c1) resolution-of-identity half of the smallbox kinetic bridge: the *windowed
mode form* of the radial symbol `p ↦ F ‖p‖` (the squared spectrum of the windowed
exponentials, i.e. the quadratic form of the one-body operator `χ·F(√−Δ)·χ`),

  `winModeForm χ F u = (2π)⁻³ ∫_p F‖p‖ · ‖∫_y e^{−i⟪p,y⟫} χ(y)u(y) dy‖²`,

equals the position-space quadratic form of the convolution operator with kernel
`K_F = 𝓕⁻¹F` (`kinKernel F`), i.e. the double integral
`∫_x (χu)(x) · ∫_y K_F(x−y)(χu)(y) dy`.

The proof is the standard Fubini/Plancherel computation, carried out in `ℂ` and specialised
to `ℝ` at the end.  With `g = χ·u` and `W p = ∫_y e^{−i⟪p,y⟫}g(y)dy` one has

* `‖W p‖² = (W p)·conj(W p) = ∫_z e^{−i⟪p,z₁⟫}g(z₁)·e^{i⟪p,z₂⟫}g(z₂)`;
* Fubini between `p` and the double variable `z`, then the inner `p`-integral is
  `(2π)³·kinKernelC F (z₂−z₁) = (2π)³·(kinKernel F (z₂−z₁) : ℂ)`;
* taking real parts, using the evenness of `K_F`, and pulling the `g(x)` out of the inner
  integral gives the iterated form of the right-hand side.

## Ingredients

* `Work.SmallBoxBridge.Resolve.kinKernelC_eq_ofReal_aux` — the complex kernel is the real one;
* `Work.SmallBoxBridge.Resolve.integrable_winMode_reIntegrand`,
  `…integrable_kinFT_fubini` — the two integrability inputs for the `re`-step and Fubini;
* `…kinKernel_bdd`, `…kinKernel_aestronglyMeasurable`, `…kinKernel_even` — the kernel is
  bounded, measurable and even.
-/

noncomputable section

open MeasureTheory Complex

namespace Work.SmallBoxBridge.Resolve

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

theorem winModeForm_eq_kernelForm (χ u : EuclideanSpace ℝ (Fin 3) → ℝ) (F : ℝ → ℝ)
    (hF : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    (hu : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => χ x * u x))
    (hχ : Measurable χ) (hχb : ∀ x, |χ x| ≤ 1) :
    Submission.BoseGases.winModeForm χ F u = ∫ x : EuclideanSpace ℝ (Fin 3),
      (χ x * u x) * (∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.kinKernel F (x - y) * (χ y * u y)) := by
  classical
  set g : ℝ³ → ℝ := fun y => χ y * u y with hgdef
  have hg : MeasureTheory.Integrable g := hu
  set W : ℝ³ → ℂ := fun p => ∫ y : ℝ³, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (g y : ℂ)
    with hWdef
  -- the kernel is bounded and (a.e.) measurable, hence the pair integrand is integrable
  have hKbdd : ∀ z : ℝ³, ‖Submission.BoseGases.kinKernel F z‖ ≤
      ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖F ‖p‖‖ := kinKernel_bdd F hF
  have hIntC : MeasureTheory.Integrable (fun z : ℝ³ × ℝ³ =>
      g z.1 * (g z.2 * Submission.BoseGases.kinKernel F (z.2 - z.1)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have hKmeas : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ³ × ℝ³ => Submission.BoseGases.kinKernel F (z.2 - z.1))
        (MeasureTheory.volume.prod MeasureTheory.volume) := by
      have hcont : Continuous
          (fun a : (ℝ³ × ℝ³) × ℝ³ => Real.cos (inner ℝ a.2 (a.1.2 - a.1.1))) := by fun_prop
      have h1 : MeasureTheory.AEStronglyMeasurable
          (fun a : (ℝ³ × ℝ³) × ℝ³ => (F ‖a.2‖ : ℝ) * Real.cos (inner ℝ a.2 (a.1.2 - a.1.1)))
          (MeasureTheory.volume.prod MeasureTheory.volume) :=
        hF.aestronglyMeasurable.comp_snd.mul hcont.aestronglyMeasurable
      have h3 : MeasureTheory.AEStronglyMeasurable
          (fun w : ℝ³ × ℝ³ => ∫ p : ℝ³, F ‖p‖ * Real.cos (inner ℝ p (w.2 - w.1)))
          (MeasureTheory.volume.prod MeasureTheory.volume) :=
        h1.integral_prod_right'
      refine (h3.const_mul (((2 * Real.pi) ^ 3)⁻¹)).congr ?_
      filter_upwards with w
      rw [Submission.BoseGases.kinKernel]
    have hgg : MeasureTheory.Integrable (fun z : ℝ³ × ℝ³ => g z.1 * g z.2)
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      MeasureTheory.Integrable.mul_prod hg hg
    refine (hgg.mul_bdd (c := ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖F ‖p‖‖) hKmeas ?_).congr ?_
    · filter_upwards with z
      exact hKbdd (z.2 - z.1)
    · filter_upwards with z
      ring
  have hIntC' : MeasureTheory.Integrable (fun z : ℝ³ × ℝ³ =>
      g z.1 * (g z.2 * Submission.BoseGases.kinKernel F (z.2 - z.1)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := hIntC
  -- integrability of the cast of the real double integrand
  have hIntD : MeasureTheory.Integrable (fun z : ℝ³ × ℝ³ =>
      (((2 * Real.pi) ^ 3 * (g z.1 * g z.2 * Submission.BoseGases.kinKernel F (z.2 - z.1)) : ℝ) : ℂ))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    refine (hIntC'.ofReal.const_mul (((2 * Real.pi) ^ 3 : ℝ) : ℂ)).congr ?_
    filter_upwards with z
    show (((2 * Real.pi) ^ 3 : ℝ) : ℂ) *
        ↑(g z.1 * (g z.2 * Submission.BoseGases.kinKernel F (z.2 - z.1)))
      = ↑(((2 * Real.pi) ^ 3 : ℝ) * (g z.1 * g z.2 * Submission.BoseGases.kinKernel F (z.2 - z.1)))
    rw [← Complex.ofReal_mul]
    congr 1
    ring
  -- converting the product measure integral to the iterated integral
  have hZ1 : (∫ z : ℝ³ × ℝ³,
        (2 * Real.pi) ^ 3 * (g z.1 * g z.2 * Submission.BoseGases.kinKernel F (z.2 - z.1)))
      = (2 * Real.pi) ^ 3 * ∫ z : ℝ³ × ℝ³,
          g z.1 * g z.2 * Submission.BoseGases.kinKernel F (z.2 - z.1) :=
    MeasureTheory.integral_const_mul _ _
  have hZ2 : (∫ z : ℝ³ × ℝ³, g z.1 * g z.2 * Submission.BoseGases.kinKernel F (z.2 - z.1))
      = ∫ x : ℝ³, ∫ y : ℝ³, g x * g y * Submission.BoseGases.kinKernel F (y - x) := by
    have h : MeasureTheory.Integrable (fun z : ℝ³ × ℝ³ =>
        g z.1 * g z.2 * Submission.BoseGases.kinKernel F (z.2 - z.1))
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      hIntC'.congr (Filter.Eventually.of_forall (fun z => by ring))
    exact MeasureTheory.integral_prod _ h
  have hZ3 : ∀ x : ℝ³, (∫ y : ℝ³, g x * g y * Submission.BoseGases.kinKernel F (y - x))
      = g x * ∫ y : ℝ³, Submission.BoseGases.kinKernel F (x - y) * g y := by
    intro x
    rw [show (∫ y : ℝ³, g x * g y * Submission.BoseGases.kinKernel F (y - x))
        = ∫ y : ℝ³, g x * (Submission.BoseGases.kinKernel F (x - y) * g y) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => by
        show g x * g y * Submission.BoseGases.kinKernel F (y - x)
          = g x * (Submission.BoseGases.kinKernel F (x - y) * g y)
        rw [show y - x = -(x - y) from (neg_sub x y).symm, kinKernel_even F (x - y)]
        ring))]
    rw [MeasureTheory.integral_const_mul]
  -- step 0: the `p`-convention Fourier transform is `W`
  have h0 : ∀ p : ℝ³, Submission.BoseGases.kinFT (fun y => (χ y : ℂ) * (u y : ℂ)) p = W p := by
    intro p
    rw [hWdef]
    unfold Submission.BoseGases.kinFT
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [Complex.ofReal_mul]
  -- step A: real part of the complexified form
  have hIntA : MeasureTheory.Integrable (fun p : ℝ³ => ((F ‖p‖ : ℝ) : ℂ) *
      ((∫ y : ℝ³, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (g y : ℂ)) *
       (starRingEnd ℂ)
        (∫ y : ℝ³, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (g y : ℂ))))
      MeasureTheory.volume :=
    integrable_winMode_reIntegrand hF hg
  have hA : ∫ p : ℝ³, F ‖p‖ * ‖W p‖ ^ 2 =
      (∫ p : ℝ³, ((F ‖p‖ : ℝ) : ℂ) * (W p * (starRingEnd ℂ) (W p))).re := by
    have h := Complex.reCLM.integral_comp_comm hIntA
    simp only [Complex.reCLM_apply] at h
    rw [← h]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    rw [Complex.re_ofReal_mul, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  -- step B: conjugation of the windowed mode
  have hB : ∀ p : ℝ³, (starRingEnd ℂ) (W p) =
      ∫ y : ℝ³, Complex.exp (Complex.I * (inner ℝ p y : ℂ)) * (g y : ℂ) := by
    intro p
    rw [hWdef]
    have h := Complex.conjCLE.integral_comp_comm (μ := MeasureTheory.volume)
      (fun y : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (g y : ℂ))
    simp only [Complex.conjCLE_apply] at h
    rw [← h]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [map_mul, ← Complex.exp_conj, Complex.conj_ofReal]
    congr 1
    simp
  -- step C1: expand the modulus square into the double integral
  have hC1 : (∫ p : ℝ³, ((F ‖p‖ : ℝ) : ℂ) * (W p * (starRingEnd ℂ) (W p)))
      = ∫ p : ℝ³, ∫ z : ℝ³ × ℝ³, ((F ‖p‖ : ℝ) : ℂ) *
        ((Complex.exp (-(Complex.I * (inner ℝ p z.1 : ℂ))) * (g z.1 : ℂ)) *
         (Complex.exp (Complex.I * (inner ℝ p z.2 : ℂ)) * (g z.2 : ℂ))) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    rw [hB p, hWdef]
    rw [← MeasureTheory.integral_prod_mul
        (fun y : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (g y : ℂ))
        (fun y : ℝ³ => Complex.exp (Complex.I * (inner ℝ p y : ℂ)) * (g y : ℂ))]
    rw [← MeasureTheory.integral_const_mul]
    rfl
  -- step C2: Fubini between `p` and the double variable `z`
  have hIntB : MeasureTheory.Integrable (fun a : ℝ³ × (ℝ³ × ℝ³) => ((F ‖a.1‖ : ℝ) : ℂ) *
      ((Complex.exp (-(Complex.I * (inner ℝ a.1 a.2.1 : ℂ))) * (g a.2.1 : ℂ)) *
       (Complex.exp (Complex.I * (inner ℝ a.1 a.2.2 : ℂ)) * (g a.2.2 : ℂ))))
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    integrable_kinFT_fubini hF hg
  have hC2 : (∫ p : ℝ³, ∫ z : ℝ³ × ℝ³, ((F ‖p‖ : ℝ) : ℂ) *
        ((Complex.exp (-(Complex.I * (inner ℝ p z.1 : ℂ))) * (g z.1 : ℂ)) *
         (Complex.exp (Complex.I * (inner ℝ p z.2 : ℂ)) * (g z.2 : ℂ))))
      = ∫ z : ℝ³ × ℝ³, ∫ p : ℝ³, ((F ‖p‖ : ℝ) : ℂ) *
        ((Complex.exp (-(Complex.I * (inner ℝ p z.1 : ℂ))) * (g z.1 : ℂ)) *
         (Complex.exp (Complex.I * (inner ℝ p z.2 : ℂ)) * (g z.2 : ℂ))) := by
    refine MeasureTheory.integral_integral_swap (μ := MeasureTheory.volume)
      (ν := MeasureTheory.volume) ?_
    exact hIntB
  -- step C3: the inner `p`-integral is `(2π)³` times the kernel
  have hC3 : ∀ z : ℝ³ × ℝ³, (∫ p : ℝ³, ((F ‖p‖ : ℝ) : ℂ) *
        ((Complex.exp (-(Complex.I * (inner ℝ p z.1 : ℂ))) * (g z.1 : ℂ)) *
         (Complex.exp (Complex.I * (inner ℝ p z.2 : ℂ)) * (g z.2 : ℂ))))
      = (((2 * Real.pi) ^ 3 * (g z.1 * g z.2 * Submission.BoseGases.kinKernel F (z.2 - z.1)) : ℝ) : ℂ) := by
    intro z
    rw [show (fun p : ℝ³ => ((F ‖p‖ : ℝ) : ℂ) *
          ((Complex.exp (-(Complex.I * (inner ℝ p z.1 : ℂ))) * (g z.1 : ℂ)) *
           (Complex.exp (Complex.I * (inner ℝ p z.2 : ℂ)) * (g z.2 : ℂ))))
        = fun p : ℝ³ => (((F ‖p‖ : ℝ) : ℂ) *
            (Complex.exp (-(Complex.I * (inner ℝ p z.1 : ℂ))) *
             Complex.exp (Complex.I * (inner ℝ p z.2 : ℂ)))) *
            ((g z.1 : ℂ) * (g z.2 : ℂ)) from funext (fun p => by ring)]
    rw [MeasureTheory.integral_mul_const]
    rw [show (fun p : ℝ³ => ((F ‖p‖ : ℝ) : ℂ) *
            (Complex.exp (-(Complex.I * (inner ℝ p z.1 : ℂ))) *
             Complex.exp (Complex.I * (inner ℝ p z.2 : ℂ))))
        = fun p : ℝ³ => ((F ‖p‖ : ℝ) : ℂ) *
            Complex.exp (Complex.I * (inner ℝ p (z.2 - z.1) : ℂ))
      from funext (fun p => by
        congr 1
        rw [← Complex.exp_add]
        congr 1
        rw [inner_sub_right, Complex.ofReal_sub]
        ring)]
    have h4 : ∫ p : ℝ³, ((F ‖p‖ : ℝ) : ℂ) *
          Complex.exp (Complex.I * (inner ℝ p (z.2 - z.1) : ℂ))
        = (((2 * Real.pi) ^ 3 : ℝ) : ℂ) * Submission.BoseGases.kinKernelC F (z.2 - z.1) := by
      unfold Submission.BoseGases.kinKernelC
      rw [← mul_assoc, ← Complex.ofReal_mul,
        mul_inv_cancel₀ (by positivity : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0), Complex.ofReal_one,
        one_mul]
    rw [h4, kinKernelC_eq_ofReal_aux F hF]
    simp only [Complex.ofReal_mul]
    ring
  -- step C: the complexified identity
  have hC : (∫ p : ℝ³, ((F ‖p‖ : ℝ) : ℂ) * (W p * (starRingEnd ℂ) (W p)))
      = ∫ z : ℝ³ × ℝ³,
          (((2 * Real.pi) ^ 3 * (g z.1 * g z.2 * Submission.BoseGases.kinKernel F (z.2 - z.1)) : ℝ) : ℂ) := by
    rw [hC1, hC2]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    exact hC3 z
  -- taking real parts
  have hRe : (∫ z : ℝ³ × ℝ³,
        (((2 * Real.pi) ^ 3 * (g z.1 * g z.2 * Submission.BoseGases.kinKernel F (z.2 - z.1)) : ℝ) : ℂ)).re
      = ∫ z : ℝ³ × ℝ³,
          (2 * Real.pi) ^ 3 * (g z.1 * g z.2 * Submission.BoseGases.kinKernel F (z.2 - z.1)) := by
    have h := Complex.reCLM.integral_comp_comm hIntD
    simp only [Complex.reCLM_apply] at h
    refine h.symm.trans ?_
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    rw [Complex.ofReal_re]
  -- the value of the left-hand side
  have key : (∫ p : ℝ³, F ‖p‖ * ‖W p‖ ^ 2)
      = (2 * Real.pi) ^ 3 *
          ∫ x : ℝ³, g x * (∫ y : ℝ³, Submission.BoseGases.kinKernel F (x - y) * g y) := by
    rw [hA, hC, hRe, hZ1]
    congr 1
    rw [hZ2]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    exact hZ3 x
  have hkin : (∫ p : ℝ³,
        F ‖p‖ * ‖Submission.BoseGases.kinFT (fun y => (χ y : ℂ) * (u y : ℂ)) p‖ ^ 2)
      = ∫ p : ℝ³, F ‖p‖ * ‖W p‖ ^ 2 := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    rw [h0 p]
  unfold Submission.BoseGases.winModeForm
  rw [hkin, key, ← mul_assoc,
    inv_mul_cancel₀ (by positivity : (((2 : ℝ) * Real.pi) ^ 3) ≠ 0), one_mul]

end Work.SmallBoxBridge.Resolve
