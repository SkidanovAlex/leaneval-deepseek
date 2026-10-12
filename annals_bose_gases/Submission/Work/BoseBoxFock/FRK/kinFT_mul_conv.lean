import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.kinFT_mul_conv`

**The convolution theorem for the corpus's `p`-convention Fourier transform `kinFT`.**

`Submission.BoseGases.kinFT u p = ∫_y e^{−i⟪p,y⟫}u(y)dy` (`SmallBoxBridge.Defs`) is the
pointwise-multiplication Fourier convention, so the transform of a *pointwise product* is the
`((2π)^3)^{-1}`-normalised *convolution* of the transforms:

  `kinFT (χ·w) p = (2π)^{-3} ∫_s kinFT χ s · kinFT w (p − s)`.

## Route

Everything is done in the corpus's own convention, with no appeal to Mathlib's transform:

1. `kinFT w (p − s) = ∫_z e^{−i⟪p,z⟫}·(e^{i⟪s,z⟫}·w z) dz` — `inner_sub_left` + `Complex.exp_add`;
2. the `(s,z)`-integrand `K s·(e^{−i⟪p,z⟫}·(e^{i⟪s,z⟫}·w z))`, with `K = kinFT χ`, is dominated by
   the *product* `‖K s‖·‖w z‖` (all phases have modulus one), hence integrable on
   `volume.prod volume` (`Integrable.mul_prod` + `Integrable.mono'`), so
   `integral_integral_swap` (Fubini) applies;
3. the `z`-only factors `e^{−i⟪p,z⟫}` and `w z` are pulled out of the `s`-integral
   (`integral_const_mul`, `integral_mul_const`);
4. the remaining `s`-integral is the Fourier inversion formula for `χ`, which is *hypothesis*
   `hinv` here: `(2π)^{-3} ∫_s e^{i⟪s,z⟫}kinFT χ s = χ z` (for smooth compactly supported `χ` this
   is `Work.BoseFixB3.Eps.kinFT_inversion_integrable`); it is the only place where `hinv` is used;
5. the prefactor `(2π)^{-3}` is moved inside the `z`-integral (`integral_const_mul`) and absorbed by
   the inversion identity, leaving exactly `∫_z e^{−i⟪p,z⟫}·(χ z·w z) = kinFT (χ·w) p`.

No integrability of the pointwise product `χ·w` is needed: the two sides are computed as iterated
integrals, the Fubini step being justified by `kinFT χ ∈ L¹` (`hχint`) and `w ∈ L¹` (`hw`) together
with the boundedness `‖kinFT w‖ ≤ ‖w‖₁`.  The smoothness hypotheses `hχc`, `hχs` are not needed on
this route (`hinv` already carries the inversion statement for `χ`).
-/

open MeasureTheory

namespace Work.BoseBoxFock.FRK

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem kinFT_mul_conv {χ w : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hχc : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχint : MeasureTheory.Integrable (Submission.BoseGases.kinFT χ))
    (hinv : ∀ z : EuclideanSpace ℝ (Fin 3), χ z = (((2 * Real.pi) ^ 3 : ℝ)⁻¹ : ℂ) *
      MeasureTheory.integral MeasureTheory.volume
        (fun s : EuclideanSpace ℝ (Fin 3) =>
          Complex.exp (Complex.I * ((inner ℝ s z : ℝ) : ℂ)) * Submission.BoseGases.kinFT χ s))
    (hw : MeasureTheory.Integrable w) (p : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT (fun z => χ z * w z) p
      = (((2 * Real.pi) ^ 3 : ℝ)⁻¹ : ℂ) * MeasureTheory.integral MeasureTheory.volume
          (fun s : EuclideanSpace ℝ (Fin 3) =>
            Submission.BoseGases.kinFT χ s * Submission.BoseGases.kinFT w (p - s)) := by
  classical
  -- the two unit-modulus phases
  have hexp_neg : ∀ r : ℝ, ‖Complex.exp (-(Complex.I * (r : ℂ)))‖ = 1 := by
    intro r
    rw [show -(Complex.I * (r : ℂ)) = ((-r : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I (-r)
  have hexp_pos : ∀ r : ℝ, ‖Complex.exp (Complex.I * (r : ℂ))‖ = 1 := by
    intro r
    rw [mul_comm Complex.I (r : ℂ), Complex.norm_exp_ofReal_mul_I]
  let ep : E3 → ℂ := fun z => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
  let ek : E3 → E3 → ℂ := fun k z => Complex.exp (Complex.I * (inner ℝ k z : ℂ))
  let K : E3 → ℂ := fun k => Submission.BoseGases.kinFT χ k
  have hKi : Integrable K := hχint
  have hep_c : Continuous ep := by simp only [ep]; fun_prop
  have hek_c : Continuous (fun a : E3 × E3 => ek a.1 a.2) := by simp only [ek]; fun_prop
  -- **Step 1**: split the phase of `kinFT w (p − k)`
  have hexpand : ∀ k : E3, Submission.BoseGases.kinFT w (p - k)
      = ∫ z : E3, ep z * (ek k z * w z) := by
    intro k
    simp only [Submission.BoseGases.kinFT]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    have h : Complex.exp (-(Complex.I * (inner ℝ (p - k) z : ℂ))) = ep z * ek k z := by
      simp only [ep, ek]
      rw [← Complex.exp_add]
      congr 1
      rw [inner_sub_left]
      push_cast
      ring
    rw [h]
    ring
  -- **Step 2**: the Fubini integrability, by the product majorant `‖K k‖·‖w z‖`
  have hInt : Integrable (Function.uncurry fun (k : E3) (z : E3) =>
      K k * (ep z * (ek k z * w z))) (volume.prod volume) := by
    refine Integrable.mono' (hKi.norm.mul_prod hw.norm) ?_ ?_
    · exact (hKi.1.comp_fst (ν := volume)).mul
        ((hep_c.comp continuous_snd).aestronglyMeasurable.mul
          ((hek_c.aestronglyMeasurable).mul (hw.1.comp_snd)))
    · filter_upwards with a
      simp only [Function.uncurry]
      rw [norm_mul, norm_mul, norm_mul]
      simp only [ep, ek]
      rw [hexp_neg, hexp_pos]
      simp only [one_mul]
      exact le_of_eq rfl
  -- **Step 3**: pull `K k` inside the `z`-integral
  have h1 : (∫ k, K k * (∫ z, ep z * (ek k z * w z)))
      = ∫ k, ∫ z, K k * (ep z * (ek k z * w z)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    exact (MeasureTheory.integral_const_mul (K k) (fun z => ep z * (ek k z * w z))).symm
  -- **Step 4**: Fubini
  have h2 : (∫ k, ∫ z, K k * (ep z * (ek k z * w z)))
      = ∫ z, ∫ k, K k * (ep z * (ek k z * w z)) := integral_integral_swap hInt
  -- **Step 5**: pull the `z`-only factors out of the `k`-integral
  have h3 : ∀ z, (∫ k, K k * (ep z * (ek k z * w z)))
      = ep z * ((∫ k, K k * ek k z) * w z) := by
    intro z
    rw [show (fun k : E3 => K k * (ep z * (ek k z * w z)))
        = (fun k : E3 => ep z * (K k * (ek k z * w z))) from by funext k; ring]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [show (fun k : E3 => K k * (ek k z * w z))
        = (fun k : E3 => (K k * ek k z) * w z) from by funext k; ring]
    rw [MeasureTheory.integral_mul_const]
  -- **Step 6**: the Fourier inversion for `χ`, in the shape the assembly uses
  have hinv' : ∀ z : E3, (((2 * Real.pi) ^ 3 : ℝ)⁻¹ : ℂ) * (∫ k, K k * ek k z) = χ z := by
    intro z
    have hfun : (∫ k, K k * ek k z)
        = ∫ k, Complex.exp (Complex.I * (inner ℝ k z : ℂ)) *
            Submission.BoseGases.kinFT χ k := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [K, ek]
      ring
    rw [hfun, ← hinv z]
  -- **Step 7**: the left-hand side, as an integral
  have hLHS : Submission.BoseGases.kinFT (fun x : E3 => χ x * w x) p
      = ∫ z, ep z * (χ z * w z) := rfl
  have eq1 : (∫ k, K k * Submission.BoseGases.kinFT w (p - k))
      = ∫ k, K k * (∫ z, ep z * (ek k z * w z)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show K k * Submission.BoseGases.kinFT w (p - k) = K k * (∫ z, ep z * (ek k z * w z))
    rw [hexpand k]
  have eq2 : (∫ z, ∫ k, K k * (ep z * (ek k z * w z)))
      = ∫ z, ep z * ((∫ k, K k * ek k z) * w z) :=
    integral_congr_ae (Filter.Eventually.of_forall h3)
  have eq3 : (((2 * Real.pi) ^ 3 : ℝ)⁻¹ : ℂ) * (∫ z, ep z * ((∫ k, K k * ek k z) * w z))
      = ∫ z, (((2 * Real.pi) ^ 3 : ℝ)⁻¹ : ℂ) * (ep z * ((∫ k, K k * ek k z) * w z)) :=
    (MeasureTheory.integral_const_mul (((2 * Real.pi) ^ 3 : ℝ)⁻¹ : ℂ)
      (fun z => ep z * ((∫ k, K k * ek k z) * w z))).symm
  have eq4 : (∫ z, (((2 * Real.pi) ^ 3 : ℝ)⁻¹ : ℂ) * (ep z * ((∫ k, K k * ek k z) * w z)))
      = ∫ z, ep z * (χ z * w z) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show (((2 * Real.pi) ^ 3 : ℝ)⁻¹ : ℂ) * (ep z * ((∫ k, K k * ek k z) * w z))
        = ep z * (χ z * w z)
    rw [show (((2 * Real.pi) ^ 3 : ℝ)⁻¹ : ℂ) * (ep z * ((∫ k, K k * ek k z) * w z))
          = ep z * ((((2 * Real.pi) ^ 3 : ℝ)⁻¹ : ℂ) * (∫ k, K k * ek k z) * w z) from by ring,
      hinv' z]
  -- assembly
  rw [hLHS, eq1, h1, h2, eq2, eq3, eq4]

end Work.BoseBoxFock.FRK
