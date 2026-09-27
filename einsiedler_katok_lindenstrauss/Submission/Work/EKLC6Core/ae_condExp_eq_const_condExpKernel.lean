import Mathlib

/-!
# `Work.EKLC6Core.ae_condExp_eq_const_condExpKernel`

For a finite measure `μ` on a standard Borel space `X`, a sub-σ-algebra `m ≤ mX` and an `L²(μ)`
function `h`, the conditional expectation `g := μ[h | m]` is, for `μ`-a.e. `x`, almost everywhere
equal to the constant `g x` with respect to the conditional measure
`ν_x := ProbabilityTheory.condExpKernel μ m x`.

## Proof

`condExpKernel μ m` is a disintegration of `μ` over the sub-σ-algebra `m`: for every integrable
function `f`,

`μ[f | m] =ᵐ[μ] fun x => ∫ y, f y ∂ν_x`
(`ProbabilityTheory.condExp_ae_eq_integral_condExpKernel`).

Both `g` and `fun y => (g y)^2` are `m`-strongly-measurable and integrable, so their `m`-conditional
expectations are themselves (`MeasureTheory.condExp_of_stronglyMeasurable`).  Applying the
disintegration identity to `g` and to `g²` therefore gives, for `μ`-a.e. `x`,

`∫ y, g y ∂ν_x = g x`,   `∫ y, (g y)^2 ∂ν_x = (g x)^2`.

Hence `Var[g; ν_x] = ∫ y, (g y)^2 ∂ν_x - (∫ y, g y ∂ν_x)^2 = 0`
(`ProbabilityTheory.variance_eq_sub`), and a random variable with vanishing variance is a.e.
constant equal to its mean (`ProbabilityTheory.ae_eq_integral_of_variance_eq_zero`), i.e.
`g =ᵐ[ν_x] fun _ => g x`.

The integrability of `g` and `g²` with respect to `ν_x` is supplied a.e. by
`MeasureTheory.Integrable.condExpKernel_ae`.
-/

namespace Work.EKLC6Core

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory

theorem ae_condExp_eq_const_condExpKernel {X : Type*} (m : MeasurableSpace X)
    [mX : MeasurableSpace X] [StandardBorelSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasure μ] (hm : m ≤ mX) (h : X → ℝ) (hf : MeasureTheory.MemLp h 2 μ) :
    ∀ᵐ x ∂μ, MeasureTheory.condExp m μ h =ᵐ[ProbabilityTheory.condExpKernel μ m x]
      (fun _ => MeasureTheory.condExp m μ h x) := by
  set g : X → ℝ := MeasureTheory.condExp m μ h with hg_def
  -- `g` is `m`-strongly-measurable and in `L²(μ)`; so are `g` itself and `g ^ 2` integrable.
  have hg_sm : StronglyMeasurable[m] g := by
    rw [hg_def]; exact MeasureTheory.stronglyMeasurable_condExp
  have hg_memLp : MeasureTheory.MemLp g 2 μ := by
    rw [hg_def]; exact MeasureTheory.MemLp.condExp (by norm_num) hf
  have hg_int : MeasureTheory.Integrable g μ := hg_memLp.integrable (by norm_num)
  have hg2_int : MeasureTheory.Integrable (fun y => g y ^ 2) μ := hg_memLp.integrable_sq
  have hg2_sm : StronglyMeasurable[m] (fun y => g y ^ 2) := by
    convert hg_sm.pow 2 using 1
    all_goals (ext y; rw [Pi.pow_apply])
  -- `g` and `g ^ 2` are `m`-measurable, so they are their own `m`-conditional expectations.
  have hce_g : MeasureTheory.condExp m μ g = g :=
    MeasureTheory.condExp_of_stronglyMeasurable hm hg_sm hg_int
  have hce_g2 : MeasureTheory.condExp m μ (fun y => g y ^ 2) = (fun y => g y ^ 2) :=
    MeasureTheory.condExp_of_stronglyMeasurable hm hg2_sm hg2_int
  -- The first two moments of `g` under the conditional measure `ν_x`.
  have step1 : ∀ᵐ x ∂μ, ∫ y, g y ∂(ProbabilityTheory.condExpKernel μ m x) = g x := by
    filter_upwards [ProbabilityTheory.condExp_ae_eq_integral_condExpKernel (μ := μ) (m := m) hm
      hg_int] with x hx
    rw [hce_g] at hx
    exact hx.symm
  have step2 : ∀ᵐ x ∂μ, ∫ y, g y ^ 2 ∂(ProbabilityTheory.condExpKernel μ m x) = g x ^ 2 := by
    filter_upwards [ProbabilityTheory.condExp_ae_eq_integral_condExpKernel (μ := μ) (m := m) hm
      hg2_int] with x hx
    rw [hce_g2] at hx
    exact hx.symm
  -- Integrability of `g` and `g ^ 2` with respect to `ν_x`, for `μ`-a.e. `x`.
  have step3 : ∀ᵐ x ∂μ, MeasureTheory.Integrable g (ProbabilityTheory.condExpKernel μ m x) :=
    MeasureTheory.Integrable.condExpKernel_ae hg_int
  have step4 : ∀ᵐ x ∂μ, MeasureTheory.Integrable (fun y => g y ^ 2)
      (ProbabilityTheory.condExpKernel μ m x) :=
    MeasureTheory.Integrable.condExpKernel_ae hg2_int
  filter_upwards [step1, step2, step3, step4] with x hx1 hx2 hx3 hx4
  -- `g` has vanishing variance under `ν_x`, hence is a.e. equal to its mean `g x`.
  have haes : AEStronglyMeasurable g (ProbabilityTheory.condExpKernel μ m x) :=
    (hg_sm.mono hm).aestronglyMeasurable
  have hMemLp : MeasureTheory.MemLp g 2 (ProbabilityTheory.condExpKernel μ m x) :=
    (MeasureTheory.memLp_two_iff_integrable_sq haes).2 hx4
  have hVar : ProbabilityTheory.variance g (ProbabilityTheory.condExpKernel μ m x) = 0 := by
    rw [ProbabilityTheory.variance_eq_sub hMemLp]
    simp only [Pi.pow_apply]
    rw [hx2, hx1]
    ring
  have hae := ProbabilityTheory.ae_eq_integral_of_variance_eq_zero hMemLp hVar
  filter_upwards [hae] with y hy
  rw [hy, hx1]

end Work.EKLC6Core
