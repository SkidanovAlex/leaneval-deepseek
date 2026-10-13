/-
# `Submission/Work/FTS/NonlinRows/SplitsAll_proof.lean` — the three exact splits, in the primed
# vocabulary

`Work.FTS.NonlinRows.SplitsAll α₂ Ci Ct Ce Cs` is the `splits` obligation of the assembly
(`NonlinRows/Assembly.lean`): for every context `Ctx α₂ Ci Ct Ce Cs α g Φs Φg` (i.e. `0 < α ≤ 1`,
`α ≤ α₂`, `GalClass α g`, `StarPkgo α Cs Φs`, `EllPkgGo α Ce g Φg`) the three identities of
`Work.FTS.NonlinRows.SplitsData α g Φs Φg` hold:

* `N₀ α (F_* + g) g = N0fix + (N03g + N04aF + N04bF + N05aF + N05bF + N06F)` on the open
  quadrant `Qd`;
* the 5×4 split of `N α (F_* + g) (Φ̃_* + Φ̃_g)` into `N_i^{gg} + N_i^{gs} + N_i^{sg} + N_i^{ss}`,
  `i = 1..5`;
* `N_* μ (lamfun μ) g = NstarLam μ g` for every `μ ≠ -1`.

The route is the open-quadrant analogue of `Work.FTS.Nonlinear.Pieces.splits_of_diff` /
`splits_of_ctx`; the difference is that the *local* hypotheses (`SmoothOpen`, `0 < z`) are enough,
and that the additivity of `L₁₂`/`FK` is only needed on `z ≥ 0` — where it is supplied by
`Work.FTS.Nonlinear.Pieces.L12FK_add_ge0` (the unrestricted form is false: the `L₁₂`-density of
`F_*` has a non-integrable pole at `s = -1`) — while the differentiability of `z ↦ L₁₂(g)(z)` on
`(0,∞)` comes from the field `N4Norm'.l12diff`.

* **second conjunct**: `Work.FTS.NonlinRows.Rl1.splitOpen` (already proved), applied to
  `SmoothOpen` of `g`, `Φs`, `Φg` (from `GalClass`, `StarPkgo.smooth`, `EllPkgGo.smooth`) and to
  `L12FK_add_ge0` and `hN.l12diff`;
* **first conjunct**: the same argument with the three `N₁`-`N₅` operators removed: it only needs
  the additivity of `∂_θ` and of `D_z = z∂_z` on `F = F_* + g`, i.e.
  `Rl1.openSlice_pth_add` and `Rl1.openSlice_pz_add` (through `Dz_add_of_diff`), since
  `F_*` is `SmoothOpen` (`SmoothQuad_Fstar`);
* **third conjunct**: an algebraic identity, valid for all `z, θ`
  (`field_simp` on `1 + μ ≠ 0` for the collapsed coefficient `μ + lamfun μ + μ·lamfun μ = -μ`).

Everything imports only already-proved material; axioms `[propext, Classical.choice,
Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.NonlinRows.Defs
import Submission.Work.FTS.NonlinRows.Goals
import Submission.Work.FTS.NonlinRows.Rl1.splitOpen
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.Nonlinear.Pieces.L12FK_add_ge0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.NonlinRows

theorem SplitsAll_proof (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    Work.FTS.NonlinRows.SplitsAll α₂ Ci Ct Ce Cs := by
  intro α g Φs Φg hctx
  obtain ⟨hα, hα1, hαα₂, hgal, hs, hell⟩ := hctx
  -- ## the data of the context
  have hsmg : Work.FTS.EllipticEst.SmoothOpen g :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hgal.reg.1
  have hmemg : Work.Spaces.HkMem α 4 g := (Work.FTS.Nonlin.galClass_regQ4 hgal).2.1
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hadd := Work.FTS.Nonlinear.Pieces.L12FK_add_ge0 hα hα1 hgal
  have hL12 : ∀ z : ℝ, 0 < z → DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z :=
    fun z hz => hN.l12diff α ⟨hα, hαα₂⟩ g ⟨hsmg, hmemg⟩ z hz
  refine ⟨?_, ?_, ?_⟩
  · -- ## the split of `N₀` (additivity of `∂_θ` and `D_z` on `F = F_* + g`)
    intro z θ hq
    have hz : 0 < z := hq.1
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := hq.2
    have hpth : Work.Spaces.pth (Work.Construction.Ftot α g) z θ
        = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth g z θ :=
      Work.FTS.NonlinRows.Rl1.openSlice_pth_add hF hsmg hz hθ
    have hDz : Work.Spaces.Dz (Work.Construction.Ftot α g) z θ
        = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz g z θ :=
      Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
        (Work.FTS.NonlinRows.Rl1.openSlice_pz_add hF hsmg hz hθ)
    simp only [Work.Construction.N0, Work.FTS.Nonlin.N0fix, Work.FTS.Nonlin.N03g,
      Work.FTS.Nonlin.N04aF, Work.FTS.Nonlin.N04bF, Work.FTS.Nonlin.N05aF,
      Work.FTS.Nonlin.N05bF, Work.FTS.Nonlin.N06F, Work.Construction.N01,
      Work.Construction.N02, Work.Construction.N03, Work.Construction.N04a,
      Work.Construction.N04b, Work.Construction.N05a, Work.Construction.N05b,
      Work.Construction.N06]
    rw [hpth, hDz]
    ring
  · -- ## the four-way split of `N` (the open-quadrant split, `Rl1.splitOpen`)
    exact Work.FTS.NonlinRows.Rl1.splitOpen hα hα1 hsmg hs.smooth hell.smooth
      (fun z hz => hadd.1 z hz.le) (fun z hz => hadd.2 z hz.le) hL12
  · -- ## the collapse of `N_*` at `λ = lamfun μ`
    intro μ hμ z θ
    have hμ1 : (1 : ℝ) + μ ≠ 0 := by intro h; exact hμ (by linarith)
    have hcoef : μ + Work.Construction.lamfun μ + μ * Work.Construction.lamfun μ = -μ := by
      rw [Work.Construction.lamfun]
      field_simp
      ring
    simp only [Work.Construction.Nstar, Work.FTS.Nonlin.NstarLam, Work.Spaces.Dz]
    rw [hcoef]
    ring

end Work.FTS.NonlinRows
