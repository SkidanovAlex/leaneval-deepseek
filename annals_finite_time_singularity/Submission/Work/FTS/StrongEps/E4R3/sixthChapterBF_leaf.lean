import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.ChapterOfS2
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Assembly
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.P0
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.N_b6_p48
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.N_b6_star
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.N_b6_rad
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.N_b6_five
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.NBlk_hkMem6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/sixthChapterBF_leaf` — the level-six chapter over the flow class

`SixthChapterBF Ce Cs C₀ ρ` asks, above a `C₀`-threshold, for the `ε`- and solution-uniform
level-six bound `rawE6 α' g τ ≤ E₁` along `EpsFlowP` flows.  The route is the assembly

* `Nblock6/ChapterOfS2.lean` — `sixthChapterBF_of_S2` (PROVED): the chapter from the semi-tame
  estimate `S2`, via the proved `E4R4.rawE6_ineq_flow` (L-A) + `E4R5.rawE6_deriv_of_flow` (S4) +
  `E4R4.gronwall_absorb` (L-C) + `Apriori4Proofs.exists_IP6o_cs_uniform` (the datum's energy);
* `Nblock6/Assembly.lean` — `S2_of_groups'` (PROVED): `S2` from the four level-six group bounds of
  the twenty pieces of the `N`-block + the per-piece `ℋ⁶`-membership + the five already-proved
  blocks of `epsWBlk`;
* `E4R5.SixthChapterBF` over `EpsFlowP`, as stated.

The four group bounds are `Nblock6.N_b6_star` (PROVED), `Nblock6.N_b6_rad` (PROVED),
`Nblock6.N_b6_five` (PROVED), and the `gg`-group `{NBlk 0, 4, 8}`, which is obtained from the two
proved pieces `Nblock6.N_b6_p0` (this work) and `Nblock6.N_b6_p48` via
`Nblock6.GGStmt_of_p0_p48`; the membership is `Nblock6.NBlk_hkMem6` (PROVED).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The chapter from the four `N`-block groups** — the assembly of `sixthChapterBF_of_S2` with
the `S2` produced by `Nblock6/Assembly.lean` from the four group lemmas and the per-piece
`ℋ⁶`-membership. -/
theorem sixthChapterBF_leaf_of_groups
    (hgg : Work.FTS.StrongEps.E4R3.Nblock6.GGStmt)
    (hstar : Work.FTS.StrongEps.E4R3.Nblock6.StarStmt)
    (hrad : Work.FTS.StrongEps.E4R3.Nblock6.RadStmt)
    (hfive : Work.FTS.StrongEps.E4R3.Nblock6.FiveStmt)
    (hmem : Work.FTS.StrongEps.E4R3.Nblock6.MemStmt)
    {Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hρs : ∀ p : ℝ × ℝ, ρ (-p) = ρ p) :
    ∃ C : ℝ, ∀ C₀ : ℝ, C ≤ C₀ →
      Work.FTS.StrongEps.EpsE4Thr.E4R5.SixthChapterBF Ce Cs C₀ ρ :=
  sixthChapterBF_of_S2 (Work.FTS.StrongEps.E4R3.Nblock6.S2_of_groups' hgg hstar hrad hfive hmem)
    hρ hρs

theorem sixthChapterBF_leaf {Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hρs : ∀ p : ℝ × ℝ, ρ (-p) = ρ p) :
    ∃ C : ℝ, ∀ C₀ : ℝ, C ≤ C₀ →
      Work.FTS.StrongEps.EpsE4Thr.E4R5.SixthChapterBF Ce Cs C₀ ρ :=
  sixthChapterBF_leaf_of_groups
    (Work.FTS.StrongEps.E4R3.Nblock6.GGStmt_of_p0_p48
      Work.FTS.StrongEps.E4R3.Nblock6.N_b6_p0 Work.FTS.StrongEps.E4R3.Nblock6.N_b6_p48)
    Work.FTS.StrongEps.E4R3.Nblock6.N_b6_star
    Work.FTS.StrongEps.E4R3.Nblock6.N_b6_rad
    Work.FTS.StrongEps.E4R3.Nblock6.N_b6_five
    Work.FTS.StrongEps.E4R3.Nblock6.NBlk_hkMem6 hρ hρs

end Work.FTS.StrongEps.E4R3
