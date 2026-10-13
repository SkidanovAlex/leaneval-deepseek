import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Vocabulary for the mixed-derivative interpolation `interpMixedGen`

This module collects the small definitional layer shared by the analytic pieces of the
`alphaDz_pth_core_le` estimate:

* `MixInt`, `DDInt`, `TTInt`, `DInt` — the four weighted functionals
  `∫∫ (D_z∂_θu)² w² σ_η`, `∫∫ (D_z²u)² w² σ_η`, `∫∫ (∂_θ²u)² w² σ_η`, `∫∫ (D_zu)² w² σ_η`
  (written as iterated integrals, `θ` first, against `w z ^ 2 * thEta θ`);
* `SliceHonest u z` — the four corresponding `θ`-slice integrals at `z` are finite;
* `RHSInt u` — the three *right-hand side* functionals are integrable in `z`.

There are no `sorry`s here; the analytic statements live in the sibling modules.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core

set_option autoImplicit false

/-- The `θ`-slice integrand of `MixInt`. -/
def mixIntS (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)

/-- The `θ`-slice integrand of `∫∫ (D_z² u)² w² σ_η`. -/
def ddIntS (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.Dz (Work.Spaces.Dz u) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)

/-- The `θ`-slice integrand of `∫∫ (∂_θ² u)² w² σ_η`. -/
def ttIntS (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.pth (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)

/-- The `θ`-slice integrand of `∫∫ (D_z u)² w² σ_η`. -/
def dIntS (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.Dz u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)


/-- The `θ`-slice integrand of the `D_θ`-summand `(D_z^{j+1}D_θ^i∂_θu)² w² σ_γ`, `i ≥ 1`. -/
def mixedIntS (α : ℝ) (i j : ℕ) (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth u) z θ) ^ 2
      * Work.FTS.EllipticEst.thGam α θ)

/-- The four `θ`-slices at `z` of the interpolation are finite. -/
def SliceHonest (u : ℝ → ℝ → ℝ) (z : ℝ) : Prop :=
  IntegrableOn (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
      * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
  IntegrableOn (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.Dz u) z θ) ^ 2
      * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
  IntegrableOn (fun θ : ℝ => (Work.Spaces.pth (Work.Spaces.pth u) z θ) ^ 2
      * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
  IntegrableOn (fun θ : ℝ => (Work.Spaces.Dz u z θ) ^ 2
      * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ

/-- The three right-hand side functionals of the interpolation are integrable in `z`. -/
def RHSInt (u : ℝ → ℝ → ℝ) : Prop :=
  IntegrableOn (ddIntS u) Work.Spaces.Iz ∧
  IntegrableOn (ttIntS u) Work.Spaces.Iz ∧
  IntegrableOn (dIntS u) Work.Spaces.Iz

end Work.EllipticEst.Core
