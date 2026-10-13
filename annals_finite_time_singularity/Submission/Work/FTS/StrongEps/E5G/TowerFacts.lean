/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5G/TowerFacts.lean` — an interface fact of the E5 assembly

**`epsWP_zero_tower`** — the zero mode of the `P₀`-scheme's pre-mollified right-hand side vanishes
along the tower.  This is the hypothesis `h0` of `EpsCorr_tendsto_zero4` (the level-4 vanishing of
the projection's rank-one correction), i.e. the input that makes the *outer* `P₀` disappear in the
limit.  It is a *pointwise* transfer of the proved `EpsZeroMode`: the latter needs only the
class-`C` clause and the small-ball bound at the profile `Pz (J_ε g(τ))`, both of which the tower
carries (`TowerAt.hC`, `TowerAt.hb4`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS.StrongEps.EpsZeroMode

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The zero mode of the tower's pre-mollified right-hand side vanishes.** -/
theorem epsWP_zero_tower {α C₀ Ce Cs T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {ε : ℕ → ℝ} {G : ℕ → Fam}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : IsSmoothKernel ρ)
    (hε : ∀ n : ℕ, ε n ∈ Set.Ioc (0 : ℝ) 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : MuLamOK α C₀ Φs E)
    (hC : ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.ClassC.ClassC α (slice (JfamP ρ (ε n) (G n)) s))
    (hb4 : ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (slice (JfamP ρ (ε n) (G n)) s) ≤ C₀ * α ^ 2) :
    ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Construction.L12 (epsWP α ρ (ε n) Φs E (G n) s) 0 = 0 :=
  fun n s hs => EpsZeroMode hα hρ (hε n).1 (hC n s hs) (hb4 n s hs) hEll hstar hml

end Work.FTS.StrongEps.E5G
