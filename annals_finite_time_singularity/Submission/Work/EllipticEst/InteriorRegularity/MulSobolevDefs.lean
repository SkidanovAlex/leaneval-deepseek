/-
Interior regularity: multiplication by a compactly supported smooth function preserves
Bessel-potential Sobolev spaces `H^s = MemSobolev s 2`.

The main result of this file is `mul_memSobolev`: for a compactly supported `C^∞` function
`γ` and `u ∈ H^s` (any real `s`), the distribution `γ u` is again in `H^s`.

The proof is the classical one: write `γ u = Λ^s(γ · Λ^{-s}U)` where `U = Λ^s u ∈ L²`, and show
that the operator `T = Λ^s ∘ M_γ ∘ Λ^{-s}` is bounded on `L²`, using
* Plancherel (the Fourier transform is an isometry on `L²`),
* the product formula `𝓕(f·g) = 𝓕f ⋆ 𝓕g` for Schwartz functions,
* Peetre's inequality `⟨x⟩^s ≤ 2^{|s|/2}⟨x-y⟩^{|s|}⟨y⟩^s` for the weight `⟨x⟩ = (1+‖x‖²)^{1/2}`,
* Young's inequality for convolutions `‖F ⋆ u‖₂ ≤ ‖F‖₁‖u‖₂`.

Then `T` is extended from Schwartz functions to all of `L²` by a Cauchy-sequence argument, which
gives `Λ^s(γu) ∈ L²`, i.e. `γu ∈ H^s`.
-/
import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FourierTransform TemperedDistribution MeasureTheory Filter
open scoped SchwartzMap BesselPotentialSpace ENNReal Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.EllipticEst.InteriorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## The Bessel symbol -/

/-- The symbol of the Bessel potential `Λ^t`, as a complex valued function. -/
def mms_wfun (t : ℝ) : E → ℂ := fun x => ((1 + ‖x‖ ^ 2) ^ (t / 2) : ℝ)

theorem mms_wfun_apply (t : ℝ) (x : E) :
    mms_wfun (E := E) t x = (((1 + ‖x‖ ^ 2) ^ (t / 2) : ℝ) : ℂ) := rfl

theorem mms_wfun_temperate (t : ℝ) : (mms_wfun (E := E) t).HasTemperateGrowth := by
  have h : (fun x : E => (1 + ‖x‖ ^ 2) ^ (t / 2)).HasTemperateGrowth :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow (H := E) (t / 2)
  have h2 : (fun x : E => (((1 + ‖x‖ ^ 2) ^ (t / 2) : ℝ) : ℂ)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp h
  change (fun x : E => (((1 + ‖x‖ ^ 2) ^ (t / 2) : ℝ) : ℂ)).HasTemperateGrowth
  exact h2

theorem mms_norm_wfun (t : ℝ) (x : E) : ‖mms_wfun (E := E) t x‖ = (1 + ‖x‖ ^ 2) ^ (t / 2) := by
  rw [mms_wfun_apply, Complex.norm_of_nonneg (by positivity)]

theorem mms_wfun_mul_neg (t : ℝ) (x : E) :
    mms_wfun (E := E) t x * mms_wfun (E := E) (-t) x = 1 := by
  rw [mms_wfun_apply, mms_wfun_apply, ← Complex.ofReal_mul, ← Real.rpow_add (by positivity),
    show t / 2 + -t / 2 = 0 by ring, Real.rpow_zero, Complex.ofReal_one]

theorem mms_wfun_mul_neg_fun (t : ℝ) :
    mms_wfun (E := E) t * mms_wfun (E := E) (-t) = 1 := by
  funext x
  rw [Pi.mul_apply, mms_wfun_mul_neg]
  rfl

theorem mms_wfun_neg (t : ℝ) (x : E) : mms_wfun (E := E) t (-x) = mms_wfun (E := E) t x := by
  rw [mms_wfun_apply, mms_wfun_apply]
  simp

/-- `besselPotential` is the Fourier multiplier with symbol `mms_wfun t`. -/
theorem mms_bessel_eq (t : ℝ) (u : 𝓢'(E, ℂ)) :
    besselPotential E ℂ t u = fourierMultiplierCLM ℂ (mms_wfun (E := E) t) u := rfl

/-- The Bessel potential of a Schwartz function is the Schwartz function obtained by the
Schwartz-level Fourier multiplier. -/
theorem mms_bessel_schwartz (t : ℝ) (f : 𝓢(E, ℂ)) :
    besselPotential E ℂ t (f : 𝓢'(E, ℂ))
      = (SchwartzMap.fourierMultiplierCLM ℂ (mms_wfun (E := E) t) f : 𝓢(E, ℂ)) := by
  rw [mms_bessel_eq]
  exact fourierMultiplierCLM_toTemperedDistributionCLM_eq (mms_wfun_temperate t) f

/-- Multiplication of the distribution of a Schwartz function by another Schwartz function. -/
theorem mms_smulLeftCLM_schwartz (g f : 𝓢(E, ℂ)) :
    smulLeftCLM ℂ (⇑g) (f : 𝓢'(E, ℂ))
      = ((SchwartzMap.smulLeftCLM ℂ (⇑g) f : 𝓢(E, ℂ)) : 𝓢'(E, ℂ)) := by
  ext φ
  rw [smulLeftCLM_apply_apply, SchwartzMap.coe_apply, SchwartzMap.coe_apply]
  simp only [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with x
  ring

theorem mms_bessel_neg_bessel (t : ℝ) (u : 𝓢'(E, ℂ)) :
    besselPotential E ℂ (-t) (besselPotential E ℂ t u) = u := by
  rw [besselPotential_besselPotential_apply, show t + -t = 0 by ring, besselPotential_zero]
  rfl

theorem mms_fourier_fourierMultiplier (g : E → ℂ) (_hg : g.HasTemperateGrowth) (f : 𝓢(E, ℂ)) :
    𝓕 (SchwartzMap.fourierMultiplierCLM ℂ g f) = SchwartzMap.smulLeftCLM ℂ g (𝓕 f) := by
  rw [SchwartzMap.fourierMultiplierCLM_apply, fourier_fourierInv_eq]

/-! ## The Schwartz-level operator `Λ^s ∘ M_γ ∘ Λ^{-s}` -/

/-- `mms_Phi s γS` is the Schwartz-level operator `k ↦ Λ^s(γ · Λ^{-s} k)`. -/
def mms_Phi (s : ℝ) (γS : 𝓢(E, ℂ)) (k : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMap.fourierMultiplierCLM ℂ (mms_wfun (E := E) s)
    (SchwartzMap.smulLeftCLM ℂ (⇑γS)
      (SchwartzMap.fourierMultiplierCLM ℂ (mms_wfun (E := E) (-s)) k))

/-- The distribution associated with `mms_Phi s γS k` is `Λ^s(γ · Λ^{-s} k)`. -/
theorem mms_Phi_toTempered (s : ℝ) (γS k : 𝓢(E, ℂ)) :
    (mms_Phi s γS k : 𝓢'(E, ℂ))
      = besselPotential E ℂ s
          (smulLeftCLM ℂ (⇑γS) (besselPotential E ℂ (-s) (k : 𝓢'(E, ℂ)))) := by
  unfold mms_Phi
  rw [← mms_bessel_schwartz s
      (SchwartzMap.smulLeftCLM ℂ (⇑γS) (SchwartzMap.fourierMultiplierCLM ℂ (mms_wfun (-s)) k)),
    ← mms_smulLeftCLM_schwartz γS (SchwartzMap.fourierMultiplierCLM ℂ (mms_wfun (-s)) k),
    ← mms_bessel_schwartz (-s) k]

end Work.EllipticEst.InteriorRegularity
