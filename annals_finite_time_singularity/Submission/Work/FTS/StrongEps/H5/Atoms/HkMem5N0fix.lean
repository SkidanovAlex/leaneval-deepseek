import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.StrongEps.H5.Data
import Submission.Work.FTS.StrongEps.H5.AngRad5.HkIntegrand_ang_rad_le5
import Submission.Work.FTS.StrongEps.H5.AngFac5.ang_fac5_integrable_bound
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsN0FixBlock
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.StrongPersist.H6Rows.FstarI12H6
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5.Atoms

/-- `N0fix α` is literally the collapsed `I₁ + I₂` combination of `FstarI12H6`, i.e. the
function `(3/(2α)) sin(2θ) L₁₂(F_*) ∂_θF_* - c₂m(θ) L₁₂(F_*) D_zF_*` of tex 1398--1402.  This is
just the definition of `N0fix = N₀₁ + N₀₂` (`Work.Construction.N01`, `Work.Construction.N02`),
written in the association used by `Work.FTS.StrongPersist.H6Rows.FstarI12H6`. -/
theorem N0fix_eq_I12 (α : ℝ) : Work.FTS.Nonlin.N0fix α = fun z θ =>
    (3 / (2 * α)) * Work.Construction.s2 θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ
    - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ := by
  funext z θ
  simp only [Work.FTS.Nonlin.N0fix, Work.Construction.N01, Work.Construction.N02]
  ring

/-- **`N0fix = N₀₁ + N₀₂` is `ℋ⁵`-honest (with a finite level-five norm).**  On the open quadrant
`N0fix α` collapses to the separated datum `8 α² c₂(θ) z² Γ(α,θ) / (c(α)(1+z)⁴)`
(`Work.Construction.N0_first_two_eq'`), which is `C^∞` on the quadrant
(`Work.FTS.StrongPersist.L3Rhs.smoothOpen_N0fix`).

Route.  Write the datum as `a(θ)·r(z)` with `a(θ) = 8α²·c₂(θ)·Γ(α,θ)/c(α)` (angular) and
`r(z) = z²/(1+z)⁴` (radial) and combine the pointwise separation at order five
(`Work.FTS.StrongEps.H5.AngRad5.HkIntegrand_ang_rad_le5`, with the angular data of `c₂` and `Γ`:
`|c₂| ≤ 2` and `|DthIter i c₂| ≤ 1000·sin 2θ` for `i ≤ 4` from
`Work.FTS.Nonlinear.Pieces.DthIter_c2m_le`, and the corresponding bounds for `Γ` / `c₂·Γ` from
`Work.FTS.Spaces.Gamma_WlInf` or the `fstarDat`-style estimates) with
`Work.FTS.LocData.HkMem_of_majorant`.  The radial factor is explicit: `DzdIter i r` is a rational
function and `(DzdIter i r z)² w(z)²` is bounded by a constant times `(1+z)^{-2}` on `(0,∞)` for
`i ≤ 5` (the elementary identity `(z²/(1+z)⁴)² w = 1/(1+z)⁴` and its analogues), so the radial
integrals and their `z`-integrability are elementary; the angular `θ`-factor is integrable by
`Work.FTS.StrongEps.H5.AngFac5.ang_fac5_integrable_bound`.  Finally transport the majorant back
to `N0fix α` with `Work.FTS.EllipticEst.HkIntegrand_congr` /
`Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0` (pointwise equality on the open quadrant).
`a` may depend on `α` (and may simply be `HkNorm α 5 (N0fix α) + 1`, since it only has to dominate
the norm).

The proof carried out here takes the shorter route through the *level-six* analysis of the same
`I₁ + I₂` combination: `Work.FTS.StrongPersist.H6Rows.FstarI12H6` already establishes the
level-`6` membership of that combination together with the bound `|·|_{ℋ⁶} ≤ K α²` (`K`
independent of `α ≤ 1`).  Since `N0fix α` is exactly that combination (`N0fix_eq_I12`) and is
`C^∞` on the quadrant (`Work.FTS.StrongPersist.L3Rhs.smoothOpen_N0fix`), the level-five statement
follows from monotonicity of `HkMem` (`Work.FTS.OpenPkg.HkMem_mono_open`) and of `HkSq`
(`Work.FTS.CoercivityStep.Norm.HkSq_mono_le`), and `a := max (K α²) 0 + 1` dominates the norm. -/
theorem HkMem5N0fix : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∃ a : ℝ, 0 < a ∧
    Work.Spaces.HkMem α 5 (Work.FTS.Nonlin.N0fix α) ∧
    Work.Spaces.HkNorm α 5 (Work.FTS.Nonlin.N0fix α) ≤ a := by
  intro α hαI
  have hα : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  obtain ⟨K, hK, hF⟩ := Work.FTS.StrongPersist.H6Rows.FstarI12H6
  obtain ⟨hmem6, hbd6⟩ := hF α hα hα1
  have hmem6' : Work.Spaces.HkMem α 6 (Work.FTS.Nonlin.N0fix α) := by
    rw [N0fix_eq_I12 α]; exact hmem6
  have hbd6' : Work.Spaces.HkNorm α 6 (Work.FTS.Nonlin.N0fix α) ≤ K * α ^ 2 := by
    rw [N0fix_eq_I12 α]; exact hbd6
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N0fix α) :=
    Work.FTS.StrongPersist.L3Rhs.smoothOpen_N0fix α hα hα1
  have hmem5 : Work.Spaces.HkMem α 5 (Work.FTS.Nonlin.N0fix α) :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm 5 (by norm_num) hmem6'
  have hsq : Work.Spaces.HkSq α 5 (Work.FTS.Nonlin.N0fix α)
      ≤ Work.Spaces.HkSq α 6 (Work.FTS.Nonlin.N0fix α) :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hmem6'
  have hn5 : Work.Spaces.HkNorm α 5 (Work.FTS.Nonlin.N0fix α) ≤ K * α ^ 2 := by
    calc Work.Spaces.HkNorm α 5 (Work.FTS.Nonlin.N0fix α)
        = Real.sqrt (Work.Spaces.HkSq α 5 (Work.FTS.Nonlin.N0fix α)) := rfl
      _ ≤ Real.sqrt (Work.Spaces.HkSq α 6 (Work.FTS.Nonlin.N0fix α)) := Real.sqrt_le_sqrt hsq
      _ = Work.Spaces.HkNorm α 6 (Work.FTS.Nonlin.N0fix α) := rfl
      _ ≤ K * α ^ 2 := hbd6'
  refine ⟨max (K * α ^ 2) 0 + 1, by positivity, hmem5, ?_⟩
  linarith [hn5, le_max_left (K * α ^ 2) 0]

end Work.FTS.StrongEps.H5.Atoms
