/-
Work module for the Elgindi finite-time singularity project.

# The angular vanishing of `D_z^j D_θ^i g` with `i ≥ 1`

The operator `D_θ` carries an explicit factor `sin(2θ)`; consequently, whenever the
number of `θ`-derivatives is at least one, the mixed derivative `D_z^j D_θ^i g` itself
carries a factor `sin(2θ)`.  Since `D_z = z ∂_z` only differentiates in the radial
direction, and `sin(2θ)` is constant in `z`, the factor survives all the `z`-derivatives
(lemma `DzIter_const_mul_apply` below), giving the identity

  `mixed j (i' + 1) g z θ = sin(2θ) · D_z^j ∂_θ D_θ^{i'} g (z, θ)`

of `mixed_eq_sin_mul`.  As `g` is smooth on a neighbourhood of the closed quadrant, the
remaining factor is bounded in `θ` on `[0, π/2]` for each fixed `z ≥ 0` (it is the
`θ`-slice of a smooth function), so one obtains the bound

  `|mixed j i g z θ| ≤ C · sin(2θ)`  for all `θ ∈ Iθ`, whenever `1 ≤ i`,

with `C` the supremum of that factor over the angular interval, computed as the
`Work.Spaces.boxSup` of the box `[0, z] × [0, π/2]`.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.RCLike.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.Spaces.BoxBounds

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

/-! ## Pulling a `z`-independent factor out of the iterated operators -/

/-- A factor which does not depend on `z` passes through `∂_z`. -/
theorem pz_const_mul (c : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz (fun z θ => c θ * K z θ) z θ = c θ * Work.Spaces.pz K z θ := by
  rw [Work.Spaces.pz, Work.Spaces.pz]
  exact deriv_const_mul_field _

/-- A factor which does not depend on `z` passes through `D_z^j`. -/
theorem DzIter_const_mul_apply (c : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z θ => c θ * K z θ) z θ = c θ * Work.Spaces.DzIter j K z θ := by
  induction j generalizing z θ with
  | zero => rfl
  | succ j ih =>
    rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.DzIter_succ, Work.Spaces.Dz]
    have heq : Work.Spaces.DzIter j (fun z θ => c θ * K z θ)
        = fun z θ => c θ * Work.Spaces.DzIter j K z θ :=
      funext fun z => funext fun θ => ih z θ
    rw [heq, pz_const_mul]
    ring

/-! ## The explicit factor `sin(2θ)` in the mixed derivatives -/

/-- For `i ≥ 1` the mixed derivative `D_z^j D_θ^i g` is `sin(2θ)` times the function
obtained from `∂_θ D_θ^{i-1} g` by the same radial derivatives `D_z^j`. -/
theorem mixed_eq_sin_mul (g : ℝ → ℝ → ℝ) (j i' : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j (i' + 1) g z θ
      = Real.sin (2 * θ)
        * Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i' g)) z θ := by
  rw [Work.Spaces.mixed, Work.Spaces.DthIter_succ]
  have hDth : Work.Spaces.Dth (Work.Spaces.DthIter i' g)
      = fun z θ => Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DthIter i' g) z θ := rfl
  rw [hDth]
  exact DzIter_const_mul_apply (fun θ => Real.sin (2 * θ)) _ j z θ

/-! ## The main bound -/

theorem mixed_sin_bound : ∀ (g : ℝ → ℝ → ℝ), Work.Spaces.SmoothNbhd g →
    ∀ z ∈ Work.Spaces.Iz, ∀ (j i : ℕ), 1 ≤ i →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.mixed j i g z θ| ≤ C * Real.sin (2 * θ) := by
  intro g hg z hz j i hi
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  -- the factor which remains after pulling out `sin(2θ)`
  set X : ℝ → ℝ → ℝ :=
    Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i' g)) with hX
  -- it is smooth on the neighbourhood of the quadrant, hence bounded on `[0,z] × Iθ`
  have hsmX : Work.Spaces.SmoothNbhd X :=
    Work.Spaces.smoothNbhd_DzIter
      (Work.Spaces.SmoothNbhd.pth (Work.Spaces.smoothNbhd_DthIter hg i')) j
  have hbdd : BddAbove (Work.Spaces.boxSet z X) :=
    Work.Spaces.bddAbove_boxSup_of_continuousOn
      (Work.Spaces.continuousOn_box_of_contDiffOn hsmX)
  refine ⟨Work.Spaces.boxSup z X, Work.Spaces.boxSup_nonneg hz hbdd, fun θ hθ => ?_⟩
  have hfac := mixed_eq_sin_mul g j i' z θ
  have hXb : |X z θ| ≤ Work.Spaces.boxSup z X :=
    Work.Spaces.le_boxSup hbdd ⟨hz, le_refl z⟩ hθ
  have hsin : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
  calc |Work.Spaces.mixed j (i' + 1) g z θ| = |Real.sin (2 * θ) * X z θ| := by rw [hfac]
    _ = Real.sin (2 * θ) * |X z θ| := by rw [abs_mul, abs_of_nonneg hsin]
    _ ≤ Real.sin (2 * θ) * Work.Spaces.boxSup z X := mul_le_mul_of_nonneg_left hXb hsin
    _ = Work.Spaces.boxSup z X * Real.sin (2 * θ) := by ring

end Work.FTS.H2
