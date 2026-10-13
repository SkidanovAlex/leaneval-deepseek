import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row23
import Submission.Work.FTS.NonlinRows.AuxAngRad.AngRadWeights
import Submission.Work.FTS.NonlinRows.AuxAngRad.HkIntegrand_ang_rad_le
import Submission.Work.FTS.NonlinRows.AuxAngRad.angRad_majorant_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.AuxAngRad

/-! ## Honesty in `ℋ⁴` of an angular `×` radial product

`HkMem α 4 (fun z θ => a θ * r z)` for an angular profile `a` whose `D_θ`-iterates are
dominated by `B1 · G` and a radial function `r ∈ ℋ⁴`: the `ℋ⁴`-integrand of the product is
dominated pointwise (on the whole closed angular interval `Iθ`) by

`Rint r z * (B0² σ(θ) + 4 B1² G(θ)² τ(α,θ))`,

with `σ = smE`, `τ = smG` the two angular weights and `Rint r` the radial density of the
`ℋ⁴`-norm.  `σ` is integrable on `Iθ` and `G² τ` is integrable by hypothesis, so the slices
of the majorant are integrable; integrating in `θ` leaves the constant
`B0² ∫σ + 4 B1² ∫G²τ` times `Rint r z`, which is integrable in `z` because
`∫_θ HkIntegrand α 4 r z θ = Rint r z · Kth` with `Kth ≥ 1` and `r ∈ ℋ⁴`.

Continuity of the integrand on the open quadrant (needed to make the slices measurable and
to apply Fubini's measurability theorem) is inherited from `SmoothOpen` of the two factors.
The two ingredients are `HkIntegrand_ang_rad_le` (pointwise domination) and
`angRad_majorant_integrable` (integrability of the majorant); the assembly is
`HkMem_of_majorant`. -/

theorem HkMem_ang_rad {α : ℝ} {a : ℝ → ℝ} {r : ℝ → ℝ} {G : ℝ → ℝ} {B0 B1 : ℝ}
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
  -- there (this is what makes the `θ`-slices and their `z`-integral measurable).
  have hsmooth : Work.FTS.EllipticEst.SmoothOpen (fun z θ => a θ * r z) :=
    smoothOpen_ang_rad ha hr
  -- The majorant `M z θ = Rint r z * (B0² σ θ + 4 B1² G(θ)² τ α θ)` has integrable slices and
  -- an integrable slice-integral.
  have hmaj := angRad_majorant_integrable (α := α) (r := r) (G := G) (B0 := B0) (B1 := B1)
    hGint hrmem
  refine Work.FTS.LocData.HkMem_of_majorant α 4 (f := fun z θ => a θ * r z)
    (M := fun z θ => Work.FTS.Nonlinear.RadialProd.Rint r z
      * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
          + 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)) ?_ ?_ ?_ ?_
  · exact hsmooth.continuousOn_HkIntegrand α 4
  · exact hmaj.1
  · exact hmaj.2
  · intro z _ θ hθ
    exact HkIntegrand_ang_rad_le ha0 ha1 hθ

end Work.FTS.NonlinRows.AuxAngRad
