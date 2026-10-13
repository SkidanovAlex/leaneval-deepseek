/-
# `Splits` — the three exact splits of `N₀`, `N` and `N_*`, in the honest vocabulary

The three identities the assembly consumes.  They are proved in the `NonlinRows` subproject
(`Work.FTS.NonlinRows.SplitsAll_proof`, `sorry`-free, against `NonlinRows.Ctx`) with the
`SmoothOpen`-based slice-differentiability (`NonlinRows/Rl1/splitOpen.lean`); this module
re-exports them with the context of this chapter, where the star package is the upgraded
`VocabO2.StarPkgo2` (its `toStarPkgo` is the `Ctx` hypothesis).

The `N₀`- and `N_*`-conjuncts are algebra (elementary identities of `N01…N06` and of the
Lambert collapse); the middle one is the four-way split of `N = N₁+…+N₅`, which is *equivalent*
to the additivity of `∂_z` and `∂_θ` on the two straightened stream functions `Φ̃_*`, `Φ̃_g` on
the open quadrant (they agree with `Φ̃` there by `L₁₂`-additivity of `F = F_* + g` on `z ≥ 0`).
-/
import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.NonlinRows.SplitsAll_proof

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

theorem Splits (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      (∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ
          = Work.FTS.Nonlin.N0fix α z θ + (Work.FTS.Nonlin.N03g α g z θ + Work.FTS.Nonlin.N04aF α g z θ + Work.FTS.Nonlin.N04bF α g z θ
              + Work.FTS.Nonlin.N05aF α g z θ + Work.FTS.Nonlin.N05bF α g z θ + Work.FTS.Nonlin.N06F α g z θ)) ∧
      (∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
          = (Work.FTS.Nonlin.N1gg α g Φg z θ + Work.FTS.Nonlin.N1gs α g Φg z θ + Work.FTS.Nonlin.N1sg α Φs g z θ + Work.FTS.Nonlin.N1ss α Φs z θ)
            + (Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ + Work.FTS.Nonlin.N2sg α Φs g z θ + Work.FTS.Nonlin.N2ss α Φs z θ)
            + (Work.FTS.Nonlin.N3gg α g Φg z θ + Work.FTS.Nonlin.N3gs α g Φg z θ + Work.FTS.Nonlin.N3sg α Φs g z θ + Work.FTS.Nonlin.N3ss α Φs z θ)
            + (Work.FTS.Nonlin.N4gg α g z θ + Work.FTS.Nonlin.N4gs α g z θ + Work.FTS.Nonlin.N4sg α g z θ + Work.FTS.Nonlin.N4ss α z θ)
            + (Work.FTS.Nonlin.N5gg g z θ + Work.FTS.Nonlin.N5gs α g z θ + Work.FTS.Nonlin.N5sg α g z θ + Work.FTS.Nonlin.N5ss α z θ)) ∧
      (∀ μ : ℝ, μ ≠ -1 → ∀ z θ,
        Work.Construction.Nstar μ (Work.Construction.lamfun μ) g z θ = Work.FTS.Nonlin.NstarLam μ g z θ) := by
  intro α g Φs Φg hα hα1 hαα₂ hg hs hell
  exact Work.FTS.NonlinRows.SplitsAll_proof IP hN hE
    (Work.FTS.NonlinRows.Ctx.mk' hα hα1 hαα₂ hg hs.toStarPkgo hell)

end Work.FTS.Nonlinear.Open
