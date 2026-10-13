/-
# `ℋ^k` is closed under addition

`Work.Spaces.HkMem α k f` says that the weighted `H^k`-integrand
`Work.Spaces.HkIntegrand α k f` has honest iterated integrals over the closed quadrant
`[0,∞) × [0,π/2]` (measure `dz dθ`): every angular slice `θ ↦ HkIntegrand α k f z θ` is
integrable on `Iθ` (`z ∈ Iz`) and `z ↦ ∫_θ HkIntegrand α k f z θ` is integrable on `Iz`.

Here we prove that `ℋ^k` is closed under addition, for functions that are smooth on an
open neighbourhood of the closed quadrant (`Work.Spaces.SmoothNbhd`).  The smoothness
hypothesis is *not* redundant: `HkMem` records only the integrability of a sum of
*squares*, so without it the class contains functions that are not a.e. strongly
measurable (see `Work.Coercivity.H1IP_add_fails`), and such a function is not closed
under addition.  For smooth functions the integrand of a sum is a.e. strongly measurable
(`Work.Coercivity.aesm_HkIntegrand_slice`), and the pointwise domination

  `HkIntegrand α k (f + g) ≤ 2 · HkIntegrand α k f + 2 · HkIntegrand α k g`

(a consequence of the additivity of `D_z^i` and `D_z^j D_θ^i` on the quadrant and of
`(a + b)² ≤ 2a² + 2b²`) transfers both integrability clauses.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.HkMem_mono
import Submission.Work.Coercivity.E2Mixed.E2model_mixed_split
import Submission.Work.FTS.Galerkin.Hilbert.HkIntegrand_add_le
import Submission.Work.FTS.CoercivityStep.Norm.HkMem_of_add_dominated

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep.Norm

set_option autoImplicit false

/-! ## `SmoothNbhd` is closed under addition -/

/-- `SmoothNbhd` is closed under (pointwise) addition.  This is what makes the
smoothness hypothesis of the transfer lemmas available for `f + g`: the two summands are
smooth on the open rectangle `(-1,∞) × (-1,π/2+1)`, hence so is their sum. -/
theorem SmoothNbhd_add {f g : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (hg : Work.Spaces.SmoothNbhd g) : Work.Spaces.SmoothNbhd (f + g) := by
  show ContDiffOn ℝ ⊤ (Function.uncurry (f + g)) (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1))
  have h : Function.uncurry (f + g) = Function.uncurry f + Function.uncurry g := rfl
  rw [h]
  exact hf.add hg

/-! ## The pointwise domination, almost everywhere in `θ` -/

/-- The subadditivity of the `H^k`-integrand, in the `2·(·) + 2·(·)` form and almost
everywhere in the angle, which is the form consumed by the integrability transfer: the
endpoints `θ = 0, π/2` of `Iθ` form a null set, and on the closed quadrant the pointwise
inequality is `Work.FTS.Galerkin.Hilbert.HkIntegrand_add_le`. -/
theorem HkIntegrand_add_le_ae_of_smoothNbhd (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.SmoothNbhd f) (hg : Work.Spaces.SmoothNbhd g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  intro z hz
  filter_upwards [MeasureTheory.ae_restrict_mem
    (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
  have h := Work.FTS.Galerkin.Hilbert.HkIntegrand_add_le (α := α) (k := k) (f := f) (g := g)
    hf hg z hz θ hθ
  linarith [h]

/-! ## The main theorem -/

/-- **`ℋ^k` is closed under addition.**  If `f` and `g` are smooth on an open
neighbourhood of the closed quadrant and both lie in `ℋ^k`, then so does `f + g`. -/
theorem HkMem_add (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (hg : Work.Spaces.SmoothNbhd g) (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (f + g) :=
  HkMem_of_add_dominated α k (SmoothNbhd_add hf hg) hmf hmg
    (HkIntegrand_add_le_ae_of_smoothNbhd α k hf hg)

end Work.FTS.CoercivityStep.Norm
