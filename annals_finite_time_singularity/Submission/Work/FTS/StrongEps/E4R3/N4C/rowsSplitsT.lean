import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Submission.Work.FTS.StrongEps.E4R3.N4C.Defs
import Submission.Work.FTS.NonlinRows.Rl1.splitOpen
import Submission.Work.FTS.StrongEps.ClassCRHS.N0_split_open
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add
import Submission.Work.FTS.StrongEps.EpsWPLim.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)

set_option maxHeartbeats 1600000

/-- **The algebraic collapse of `N_*` at `λ = lamfun μ`** (the third conjunct of
`Work.FTS.NonlinRows.SplitsData`): for `μ ≠ -1` the coefficient
`μ + lamfun μ + μ·lamfun μ` equals `-μ`, so `N_* μ (lamfun μ) g = μ (D_z g - g) = NstarLam μ g`.

This is hypothesis-free (a polynomial identity in `μ`). -/
theorem nstar_lamfun_collapse (μ : ℝ) (hμ : μ ≠ -1) (g : Fn) (z θ : ℝ) :
    Work.Construction.Nstar μ (Work.Construction.lamfun μ) g z θ
      = Work.FTS.Nonlin.NstarLam μ g z θ := by
  have hμ1 : (1 : ℝ) + μ ≠ 0 := by intro h; exact hμ (by linarith)
  have hcoef : μ + Work.Construction.lamfun μ + μ * Work.Construction.lamfun μ = -μ := by
    rw [Work.Construction.lamfun]
    field_simp
    ring
  simp only [Work.Construction.Nstar, Work.FTS.Nonlin.NstarLam, Work.Spaces.Dz]
  rw [hcoef]
  ring

/-- **The `L₁₂`/`FK`-additivity and the differentiability of `z ↦ L₁₂ g z` on `(0,∞)`**, in the
honest class (`SmoothOpen` + `HkMem α 4`) of the `ClassC` profile of `CtxT`.

Both are the open-quadrant (`SmoothOpen`) forms of the standing inputs of the split: `L₁₂` is
additive above `0` by `NZeroAux.L12add` (its two densities are integrable there, and the slices
are integrable by `SmoothOpen` + `HkMem`), the angular moment `FK` by
`EpsWPLim.FK_Fstar_add_of_SmoothOpen_HkMem`, and the differentiability of `z ↦ L₁₂(g)(z)` is the
second conjunct of `NZeroAux.L12add`. -/
theorem l12FK_add_of_classC {α : ℝ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hso : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    (∀ z : ℝ, 0 < z → Work.Construction.L12 (Work.Construction.Ftot α g) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 g z) ∧
    (∀ z : ℝ, 0 < z → Work.Construction.FK (Work.Construction.Ftot α g) z
        = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK g z) ∧
    (∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z) := by
  have h := Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add hα hα1 hso hmem
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => h.2.1 z hz⟩
  · exact h.1 z hz.le
  · exact Work.FTS.StrongEps.EpsWPLim.FK_Fstar_add_of_SmoothOpen_HkMem hso hmem hz

theorem rowsSplitsT {α₂ Cs Ce : ℝ} :
    ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.NonlinRows.SplitsData α g Φs Φg := by
  intro α g Φs Φg hctx
  obtain ⟨hα, hα1, _hαα₂, hg, _hco, hs, hell⟩ := hctx
  have hsmg : Work.FTS.EllipticEst.SmoothOpen g := hg.reg
  have hmem4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hg.reg 4 (by norm_num) hg.mem
  have hΦs : Work.FTS.EllipticEst.SmoothOpen Φs := hs.smooth
  have hΦg : Work.FTS.EllipticEst.SmoothOpen Φg := hell.smooth
  obtain ⟨hL, hFK, hL12⟩ := l12FK_add_of_classC hα hα1 hsmg hmem4
  refine ⟨?_, ?_, ?_⟩
  · -- ## the split of `N₀` (additivity of `∂_θ` and of `D_z` on `F = F_* + g`)
    intro z θ hq
    simpa only [add_assoc] using
      Work.FTS.StrongEps.ClassCRHS.N0_split_open hα hsmg z θ hq
  · -- ## the four-way split of `N`
    intro z θ hq
    exact Work.FTS.NonlinRows.Rl1.splitOpen hα hα1 hsmg hΦs hΦg hL hFK hL12 z θ hq
  · -- ## the collapse of `N_*` at `λ = lamfun μ`
    intro μ hμ z θ
    exact nstar_lamfun_collapse μ hμ g z θ

end Work.FTS.StrongEps.E4R3.N4C
