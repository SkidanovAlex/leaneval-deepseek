/-
Copyright: work module for the Elgindi finite-time singularity project.

# Honesty in `ℋ⁴` of an angular `×` radial product

`Work.Spaces.HkMem α 4 (fun z θ => a θ * r z)` for an angular profile `a` whose
`D_θ`-iterates of orders `1..4` are dominated by `B1 · G`, and a radial profile `r` whose
radial lift lies in `ℋ⁴`.

The proof is the majorant criterion `Work.FTS.LocData.HkMem_of_majorant`: the `ℋ⁴`-integrand
of the product is dominated pointwise on the closed angular interval `Iθ` by

`Rint r z * (B0²·smE θ + 4·B1²·G(θ)²·smG α θ)`,

where `smE θ = sin(2θ)^{-η}`, `smG α θ = sin(2θ)^{-γ(α)}` are the two angular weights and
`Rint r z = Σ_{i≤4}(D_z^i r z)²·w(z)²` is the radial density of the `ℋ⁴`-norm.  This is the
separated (in `θ` and `z`) form of the integrand, and it is the `ℋ⁴`-analogue of

  `|a·r|_{ℋ⁴} ≤ √(10000·B0² + 4·B1²·M1)·|r|_{ℋ⁴}`  (`Pieces.RNP.Xn_ang_rad_le_gen`),

with the norm estimate replaced by the (stronger) honesty statement: the product has honest
iterated integrals, since every slot of its integrand is dominated by an integrable function.

The two ingredients are

* `Work.FTS.NonlinRows.AuxAngRad.HkIntegrand_ang_rad_le` — the pointwise domination
  (`dzIter_ang_rad`/`mixed_ang_rad` split the slots, and the two squared-weight identities of
  `AngRadWeights` — valid for `0 ≤ sin(2θ)`, hence including the endpoints `θ = 0, π/2` —
  turn the weights into `smE`, `smG`; the constant `4` counts the `i ∈ {1,2,3,4}`);
* `Work.FTS.NonlinRows.AuxAngRad.angRad_majorant_integrable` — integrability of the majorant
  (`smE` is integrable on `Iθ` by `Spaces.sin_two_rpow` applied to the exponent `-η ∈ (-1,0)`,
  `G²·smG` is integrable by hypothesis, and `Rint r` is integrable in `z` because
  `∫_θ HkIntegrand α 4 (fun z _ => r z) z θ = Rint r z · Kth` with `Kth ≥ 1`).

The continuity of the integrand on the open quadrant — needed for the measurability of the
slices and for Fubini's measurability theorem — is `SmoothOpen.continuousOn_HkIntegrand`
applied to the product datum, which is `SmoothOpen` because both factors are.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.NonlinRows.AuxAngRad.AngRadWeights
import Submission.Work.FTS.NonlinRows.AuxAngRad.HkIntegrand_ang_rad_le
import Submission.Work.FTS.NonlinRows.AuxAngRad.angRad_majorant_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The `ℋ⁴`-integrand of an angular `×` radial product is dominated by the product of the
radial density with the separated angular majorant.**

This is a local restatement of `Work.FTS.NonlinRows.AuxAngRad.HkIntegrand_ang_rad_le` in the
form (with the weight factor of the `B1`-term grouped as `G(θ)²·smG α θ`) used by the majorant
criterion below. -/
private theorem hkIntegrand_ang_rad_le {α : ℝ} {a r G : ℝ → ℝ} {B0 B1 : ℝ}
    (ha0 : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B0)
    (ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ B1 * G θ)
    {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * r z) z θ
      ≤ Work.FTS.Nonlinear.RadialProd.Rint r z
          * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              + 4 * B1 ^ 2 * (G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)) := by
  have h := Work.FTS.NonlinRows.AuxAngRad.HkIntegrand_ang_rad_le (α := α) (a := a) (r := r)
    (G := G) (B0 := B0) (B1 := B1) (z := z) ha0 ha1 hθ
  calc Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * r z) z θ
      ≤ Work.FTS.Nonlinear.RadialProd.Rint r z
          * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              + 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) := h
    _ = Work.FTS.Nonlinear.RadialProd.Rint r z
          * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              + 4 * B1 ^ 2 * (G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)) := by
        ring

/-- **Integrability of the separated angular majorant and of its `z`-slice-integral.**

Local restatement of `Work.FTS.NonlinRows.AuxAngRad.angRad_majorant_integrable`, with the
weight factor of the `B1`-term grouped as `G(θ)²·smG α θ`. -/
private theorem majorant_integrable {α : ℝ} {r G : ℝ → ℝ} {B0 B1 : ℝ}
    (hGint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ)
    (hrmem : Work.Spaces.HkMem α 4 (fun z _ => r z)) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.FTS.Nonlinear.RadialProd.Rint r z
          * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              + 4 * B1 ^ 2 * (G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)))
        Work.Spaces.Iθ)
      ∧ MeasureTheory.IntegrableOn
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          Work.FTS.Nonlinear.RadialProd.Rint r z
            * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
                + 4 * B1 ^ 2 * (G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)))
        Work.Spaces.Iz := by
  have hAng : MeasureTheory.IntegrableOn
      (fun θ : ℝ => B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
          + 4 * B1 ^ 2 * (G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ))
      Work.Spaces.Iθ :=
    (Work.FTS.NonlinRows.AuxAngRad.integrableOn_smE.const_mul _).add (hGint.const_mul _)
  refine ⟨fun z _ => hAng.const_mul _, ?_⟩
  have hRint := Work.FTS.NonlinRows.AuxAngRad.integrableOn_Rint_of_HkMem hrmem
  have hK : MeasureTheory.IntegrableOn
      (fun z : ℝ => Work.FTS.Nonlinear.RadialProd.Rint r z
        * (∫ θ in Work.Spaces.Iθ, (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
            + 4 * B1 ^ 2 * (G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ))))
      Work.Spaces.Iz := hRint.mul_const _
  refine MeasureTheory.IntegrableOn.congr_fun hK (fun z _ => ?_) measurableSet_Ici
  rw [MeasureTheory.integral_const_mul]

theorem AngRadHkMem {α : ℝ} {a r G : ℝ → ℝ} {B0 B1 : ℝ}
    (ha : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ))
    (hr : Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z))
    (hGnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ G θ)
    (hGint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ)
    (ha0 : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B0)
    (ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ B1 * G θ)
    (hrmem : Work.Spaces.HkMem α 4 (fun z _ => r z)) :
    Work.Spaces.HkMem α 4 (fun z θ => a θ * r z) := by
  -- The product datum is `C^∞` on the open quadrant, hence its `ℋ⁴`-integrand is continuous
  -- there.
  have hsmooth : Work.FTS.EllipticEst.SmoothOpen (fun z θ => a θ * r z) :=
    Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad ha hr
  obtain ⟨hMslice, hMz⟩ := majorant_integrable (α := α) (r := r) (G := G)
    (B0 := B0) (B1 := B1) hGint hrmem
  -- The majorant criterion, with the majorant written out explicitly so that the final goal
  -- is the pointwise domination.
  refine Work.FTS.LocData.HkMem_of_majorant α 4 (f := fun z θ => a θ * r z)
    (M := fun z θ => Work.FTS.Nonlinear.RadialProd.Rint r z
      * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
          + 4 * B1 ^ 2 * (G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ))) ?_ ?_ ?_ ?_
  · exact hsmooth.continuousOn_HkIntegrand α 4
  · exact hMslice
  · exact hMz
  · intro z _ θ hθ
    exact hkIntegrand_ang_rad_le (α := α) (a := a) (r := r) (G := G) (B0 := B0) (B1 := B1)
      ha0 ha1 hθ

end Work.FTS.Nonlinear.Open
