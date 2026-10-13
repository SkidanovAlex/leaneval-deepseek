/-
Copyright: work module for the Elgindi finite-time singularity project.

# The radial pointwise estimate of `WtoH` in the interior class

`Work.Elliptic.WtoH_Radial` proves the radial pointwise estimate of Elgindi's Proposition
`WtoH` (tex 1237) for functions which are *analytic* on a neighbourhood of the closed quadrant
(`Work.Spaces.SmoothNbhd`).  The objects of the construction are only `C^∞` on the open
quadrant (`Work.FTS.LocData.SmoothQuad`), so this file re-proves the estimate in that class,
with the conclusion restricted to the open quadrant `θ ∈ (0,π/2)`: on the boundary lines
`θ = 0, π/2` the values of `f` are not constrained by `SmoothQuad f`, so nothing can be said
there (and nothing is needed: the boundary is null for the `ℋ⁴`-integrals).

The proof is the delivered one, with the three analytic-order helpers replaced by their
genuine-smooth-order counterparts from `Submission/Work/FTS/H2/Q/Base.lean`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.Q.Base
import Submission.Work.Elliptic.radial_arith

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Q

open Work.Spaces

set_option autoImplicit false

/-- Elgindi's *radial* pointwise estimate from Proposition `WtoH` (tex 1237), in the interior
class `Work.FTS.LocData.SmoothQuad` (genuine `C^∞` on the open quadrant — `ContDiffOn ℝ
Work.Stability.smoothOrder`, *not* the analytic order `⊤`):

if `((z+1)³/z²) f ∈ 𝒲^{4,∞}` and `f` is `C^∞` on the open quadrant, then for every `m ≤ 4`,
every `z > 0` and every `θ ∈ (0,π/2)`,
`|(1+z)·w(z)·z^m·∂_z^m f(z,θ)| ≤ 200000·|((z+1)³/z²)f|_{𝒲^{4,∞}}`, where `w(z) = (1+z)²/z²`.

This is `Work.Elliptic.WtoH_Radial` with the hypothesis `SmoothNbhd f` (= analyticity on a
neighbourhood of the closed quadrant, unusable for `F_*` and the stream functions) replaced by
`SmoothQuad f`, and the conclusion restricted to the open quadrant — on the boundary lines
`θ = 0, π/2` the values of `f` (and hence of its `z`-derivatives) are *not* constrained by
`SmoothQuad f`, so no bound can hold there. -/
theorem WtoH_Radial_Q {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f)
    (hmem : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)) :
    ∀ (m : ℕ), m ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ), θ ∈ Set.Ioo 0 (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ m * Work.Spaces.pzIter m f z θ|
        ≤ 200000 * Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) := by
  intro m hm z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  let G : ℝ → ℝ → ℝ := fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ
  have hmemG : Work.Spaces.WlInfMem α 4 G := hmem
  have hΛ : 0 ≤ Work.Spaces.WlInf α 4 G := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 G hmemG)
      (Work.Spaces.wlThSum_nonneg α 4 G hmemG)
  have hG : G = fun z θ => (z + 1) ^ 3 * Work.Elliptic.divZ2 f z θ :=
    Work.Elliptic.g_divZ2_eq f
  have hκ : ContDiffAt ℝ Work.Stability.smoothOrder
      (fun z' => Work.Elliptic.divZ2 f z' θ) z :=
    contDiffAt_divZ2_zslice_sm hsm hθ z hz
  have htri : ∀ j ≤ m,
      |(1 + z) ^ (j + 3) * Work.Spaces.pzIter j (Work.Elliptic.divZ2 f) z θ|
        ≤ 6000 * Work.Spaces.WlInf α 4 G := by
    have h := tri_bound_sm (G := G) (κ := Work.Elliptic.divZ2 f) hG hm hz hκ (fun j hj =>
      Work.Spaces.WlInf_z_bound α 4 G hmemG j (by omega) z θ (le_of_lt hz) hθI)
    intro j hj
    have h' := h j hj
    rw [show (1 : ℝ) + z = z + 1 by ring]
    exact h'
  have hA := pzIter_divZ2_expansion_aux_sm hsm hm hz hθ
  rw [hA]
  exact Work.Elliptic.radial_arith (Λ := Work.Spaces.WlInf α 4 G) hm hz hΛ
    (fun j => Work.Spaces.pzIter j (Work.Elliptic.divZ2 f) z θ) htri

end Work.FTS.H2.Q
