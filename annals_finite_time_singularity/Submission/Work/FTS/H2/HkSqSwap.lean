/-
Copyright: work module for the Elgindi finite-time singularity project.

# Swapping the order of the two integrations in `HkSq`

`Work.Spaces.HkSq α k f` is the iterated integral of the nonnegative integrand
`Work.Spaces.HkIntegrand α k f` over the domain `[0,∞) × [0,π/2]`, integrated first in
the angle `θ` and then in the radial variable `z`.  Several estimates of §H2 of the
paper are naturally stated with the integration performed in the opposite order (outer
integral in `θ`, inner integral in `z`), and this file provides the swap together with
the two integrability statements that make the swapped integral meaningful:

* `∫_θ ∫_z = HkSq` (Tonelli for a nonnegative integrand);
* the partially integrated integrand `σ ↦ ∫_z HkIntegrand α k f z σ` is integrable in
  `σ` over `Iθ`;
* for almost every angle `σ`, the angular slice `s ↦ HkIntegrand α k f s σ` is
  integrable over `Iz`.

The only hypotheses are the ones already available in this development: `HkMem` gives
the two *iterated* integrals of the integrand in the `z`-outer order
(`∀ z ∈ Iz, IntegrableOn (fun θ => …) Iθ` and `IntegrableOn (fun z => ∫ θ …) Iz`), and
`SmoothNbhd f` gives the a.e. strong measurability of the uncurried integrand for the
product of the two restricted measures (`Work.Coercivity.aesm_uncurry_HkIntegrand`),
since the integrand of a smooth function is continuous on the open quadrant and the
closed quadrant differs from it by a null set.

The measure-theoretic content is isolated in the general lemma
`swap_iterated_integral_of_nonneg` (arbitrary measure spaces), which is the Tonelli
statement used above; the target lemma `HkSqSwap` is then a direct instantiation.
-/
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Coercivity.HkMem_mono

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-- **Tonelli for a nonnegative integrand, with the two iterated integrals swapped.**

Let `g : α → β → ℝ` be nonnegative, a.e. strongly measurable on the product of the
`σ`-finite measures `μ` and `ν`, with `ν`-integrable slices and `μ`-integrable partially
integrated function `a ↦ ∫ b, g a b ∂ν`.  Then the iterated integral in the opposite
order exists, equals the original one, and its two ingredients are integrable:

* `∫ b, ∫ a, g a b ∂μ ∂ν = ∫ a, ∫ b, g a b ∂ν ∂μ`;
* the partially integrated function `b ↦ ∫ a, g a b ∂μ` is integrable for `ν`;
* for `ν`-almost every `b`, the slice `a ↦ g a b` is integrable for `μ`.

The proof is `Work.Spaces.integrable_prod_of_iterated` (which produces the integrability
of the uncurried `g` on the product measure from the two iterated-integral hypotheses),
followed by Fubini for the integrable function `g` in the swapped order. -/
theorem swap_iterated_integral_of_nonneg {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β} [MeasureTheory.SFinite μ]
    [MeasureTheory.SFinite ν] {g : α → β → ℝ} (hnn : ∀ a b, 0 ≤ g a b)
    (haesm : MeasureTheory.AEStronglyMeasurable (Function.uncurry g) (μ.prod ν))
    (hslice : ∀ᵐ a ∂μ, MeasureTheory.Integrable (fun b => g a b) ν)
    (houter : MeasureTheory.Integrable (fun a => ∫ b, g a b ∂ν) μ) :
    (∫ b, ∫ a, g a b ∂μ ∂ν = ∫ a, ∫ b, g a b ∂ν ∂μ) ∧
      MeasureTheory.Integrable (fun b => ∫ a, g a b ∂μ) ν ∧
      (∀ᵐ b ∂ν, MeasureTheory.Integrable (fun a => g a b) μ) := by
  obtain ⟨hint, hprod⟩ :=
    Work.Spaces.integrable_prod_of_iterated (μ := μ) (ν := ν) hnn haesm hslice houter
  -- the uncurried integrand of the swapped order is integrable on the swapped product
  have hswap : MeasureTheory.Integrable (Function.uncurry fun b a => g a b) (ν.prod μ) :=
    hint.swap
  refine ⟨?_, hswap.integral_prod_left, hswap.prod_right_ae⟩
  calc (∫ b, ∫ a, g a b ∂μ ∂ν)
      = ∫ p : β × α, g p.2 p.1 ∂(ν.prod μ) := MeasureTheory.integral_integral hswap
    _ = ∫ p : α × β, g p.1 p.2 ∂(μ.prod ν) :=
          MeasureTheory.integral_prod_swap (Function.uncurry g)
    _ = ∫ a, ∫ b, g a b ∂ν ∂μ := hprod

theorem HkSqSwap (α : ℝ) (f : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd f)
    (hmem : Work.Spaces.HkMem α 4 f) :
    (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ
        = Work.Spaces.HkSq α 4 f) ∧
      MeasureTheory.Integrable
        (fun σ : ℝ => ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α 4 f s σ)
          Work.Spaces.Iz) := by
  -- Nonnegativity of the integrand.
  have hnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  -- A.e. strong measurability of the uncurried integrand, from smoothness on a neighbourhood.
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry fun z θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Coercivity.aesm_uncurry_HkIntegrand α 4 hsm
  -- The angular slices are integrable, for every `z ∈ Iz` (hence a.e.).
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hmem.1 z hz)
  -- ... and the `z`-integral of the angular slices is integrable.
  have houter : MeasureTheory.Integrable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmem.2
  obtain ⟨h1, h2, h3⟩ :=
    swap_iterated_integral_of_nonneg (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) hnn haesm hslice houter
  refine ⟨?_, h2, h3⟩
  rw [Work.Spaces.HkSq]
  exact h1

end Work.FTS.H2
