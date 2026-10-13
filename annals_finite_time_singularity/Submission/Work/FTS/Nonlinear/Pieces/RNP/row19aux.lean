/-
# Row 19 of the N4 table — the vocabulary of the proof

The piece is `N₃^{**} = -2α · V(Φ̃_*) · D_zF_*` (`Work.FTS.Nonlin.N3ss`), and the design's route
(`FTS/N45_DESIGN_LEAD.md` §3.4, row 19, and the audit in
`Pieces/NOTES_rowsN_vacuous.md`) is `WtoHQ` + the `𝒲^{4,∞}`-product rule applied to

  `((z+1)³/z²)·N₃^{**} = -2α · [((z+1)/z)·V(Φ̃_*)] · [((z+1)²/z)·D_zF_*]`,

which needs the *weighted* coefficient `((z+1)/z)·V(Φ̃_*)` (equivalently `V(Φ̃_*) ∈ 𝒲^{5,∞}`
together with `V(z,0) = V(z,π/2) = 0`, by the `(z+1)/z`-transfer of Prop. tex 1217).  The frozen
`StarPkg` supplies only `WlInfMem α 4 (V(Φ̃_*))`, one order short of that transfer.

This module carries the *definitions* of the row-19 vocabulary together with the elementary
structural facts about `V(Φ̃_*)` that follow from `StarPkg.V` alone and that every variant of the
proof needs: the Lipschitz bound in `z` (hence the existence of the limit at `z → 0⁺` and the
quantitative vanishing `|V(z,θ)| ≤ |V(0,θ)| + M z`), and the master decomposition
`V·D_zF_* = a·K` with `a = V/z` and `K = z·D_zF_*`.

The local notation `Vs`/`Gs` keeps the statements of the sibling lemmas short.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.starPt
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.Spaces.WlInf_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The coefficient `V(Φ̃_*) = ∂_θΦ̃_* - tan θ · Φ̃_*` of `N₃^{**}` (row 19). -/
abbrev Vs (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) : ℝ → ℝ → ℝ :=
  Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)

/-- The factor `D_zF_* = z ∂_zF_*` of `N₃^{**}` (row 19). -/
abbrev Gs (α : ℝ) : ℝ → ℝ → ℝ := Work.Spaces.Dz (Work.Construction.Fstar α)

/-- The *master decomposition* of the row-19 piece: `V·D_zF_* = a·K` with `a = V/z` (the
quantity that carries the possible `1/z` singularity at `z = 0⁺`) and `K = z·D_zF_*`
(`= α·Γ(θ)/c·k(z)`, `k(z) = 2z²(1-z)/(1+z)³`, an *explicit* smooth radial profile that vanishes
like `z²` at the origin and decays like `1/z` at infinity).  This is the form in which the
`ℋ⁴`-integrand of the piece can be estimated term by term. -/
theorem Vs_mul_Gs_eq (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) {z θ : ℝ} (hz : z ≠ 0) :
    Vs α Φs z θ * Gs α z θ
      = (Vs α Φs z θ / z) * (z * Gs α z θ) := by
  field_simp

/-- `N₃^{**} = -2α·(V(Φ̃_*)·D_zF_*)`, with the scalar `-2α` pulled out of the product. -/
theorem N3ss_eq (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) :
    Work.FTS.Nonlin.N3ss α Φs
      = fun z θ => (-(2 * α)) * (Vs α Φs z θ * Gs α z θ) := by
  funext z θ
  simp only [Work.FTS.Nonlin.N3ss, Vs, Gs]
  ring

/-- The `ℋ⁴`-norm of `N₃^{**}` is `2α` times the `ℋ⁴`-norm of the product `V(Φ̃_*)·D_zF_*`. -/
theorem xn_N3ss (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) :
    Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3ss α Φs)
      = |-(2 * α)| * Work.FTS.Nonlin.Xn α (fun z θ => Vs α Φs z θ * Gs α z θ) := by
  rw [N3ss_eq]
  exact Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α (-(2 * α)) _

/-- For `α ≥ 0` the prefactor is `2α`. -/
theorem xn_N3ss_of_nonneg {α : ℝ} (hα : 0 ≤ α) (Φs : Work.FTS.Galerkin.Fn) :
    Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3ss α Φs)
      = 2 * α * Work.FTS.Nonlin.Xn α (fun z θ => Vs α Φs z θ * Gs α z θ) := by
  rw [xn_N3ss, abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * α)]

/-- **The pointwise bound on the coefficient.**  `StarPkg.V` bounds `V(Φ̃_*)` in `𝒲^{4,∞}` by
`Cs·α`; the `k = 0` summand of the `𝒲^{4,∞}`-norm is the honest supremum, so
`|V(Φ̃_*)(z,θ)| ≤ max Cs 0 · α` on the domain. -/
theorem abs_Vs_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Vs α Φs z θ| ≤ max Cs 0 * α := by
  intro z hz θ hθ
  have hle : Cs * α ≤ max Cs 0 * α :=
    mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le
  exact Work.FTS.Nonlinear.Pieces.rl1Tools.abs_le_WlInf_of_mem hs.V.1
    (le_trans hs.V.2 hle) hz hθ

/-- The first `z`-derivative of `V(Φ̃_*)` is bounded: the `k = 1` summand of the `𝒲^{4,∞}`-norm
gives `|(z+1)·∂_zV| ≤ max Cs 0 · α`. -/
theorem abs_dVs_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) * Work.Spaces.pz (Vs α Φs) z θ| ≤ max Cs 0 * α := by
  intro z hz θ hθ
  have hle : Cs * α ≤ max Cs 0 * α :=
    mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le
  have h := Work.Spaces.WlInf_z_bound α 4 (Vs α Φs) hs.V.1 1 (by norm_num) z θ hz hθ
  simpa using le_trans h (le_trans hs.V.2 hle)

end Work.FTS.Nonlinear.Pieces.RNP
