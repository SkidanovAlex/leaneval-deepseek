import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.SerreExact
import Submission.Work.Serre.SPC.Defs
import Submission.Work.Serre.SPC.Setup
import Submission.Work.Serre.SPC.Square
import Submission.Work.Serre.SPC.Assembly
import Submission.Work.Serre.SPC.towerComparison
import Submission.Work.Serre.SPC.pullbackPairComparison
import Submission.Work.Serre.ZeroCase.cellStepHyp
import Submission.Work.Serre.ZeroCase.B1
import Submission.Work.Serre.Assembly.pairMapOf_isIso
import Submission.Work.Serre.Assembly.pullbackPairMap_comp

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Serre pair comparison in the stable range

`Work.Serre.serrePairComparison` is the cell-attachment comparison behind
`Work.Serre.serreStableExact`: for a Serre fibration `p : E → B` with `B` `(b-1)`-connected
(`1 ≤ b`), the fibre `(f-1)`-connected (`1 ≤ f`), the pair map
`(E, p⁻¹b₀) → (B, {b₀})` is an isomorphism on integral homology in degrees `< b + f` **and an
epimorphism in degree `b + f`** (the one degree of slack used by the assembly
`Work.Serre.SPC.serrePairComparison_of`).

* For `b ≥ 2` the model of `B` is `Work.Serre.CWModel.towerA` (cells of dimension `≥ b`), and the
  induction is `Work.Serre.SPC.towerComparison`, whose cell step is the strengthened integral cell
  step `Work.Serre.ZeroCase.cellStepHyp`.
* For `b = 1` the model is `Work.Serre.SPC.Skeleton` followed by the tower
  `Work.Serre.SPC.towerB`; the comparison is `Work.Serre.ZeroCase.b1Comparison`
  (`Submission/Work/Serre/ZeroCase/B1.lean`).

The hypothesis `1 ≤ f` is needed only in the `b = 1` branch; the `f = 0` case of the target
`Work.Serre.SerreStableExact` is handled separately by `Work.Serre.serreComparison_zero`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre

theorem serrePairComparison {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B)
    (e₀ : E) (he₀ : p e₀ = b₀) (b f : ℕ) (hb : 1 ≤ b) (hf : 1 ≤ f)
    (hconn : ∀ i < b, Subsingleton (HomotopyGroup (Fin i) B b₀))
    (hfib0 : Subsingleton (HomotopyGroup (Fin 0) (Work.StemsB.fibre p b₀) ⟨e₀, he₀⟩))
    (hfib : ∀ j : ℕ, 0 < j → j < f →
      CategoryTheory.Limits.IsZero
        ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p b₀))).homology j)) :
    (∀ i : ℕ, i < b + f → CategoryTheory.IsIso
        (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) i)) ∧
      Function.Surjective
        (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) (b + f)).hom := by
  classical
  -- `B` is path connected: this is the `π₀` part of the connectivity hypothesis.
  have hB : PathConnectedSpace B :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero b₀ (hconn 0 (by omega))
  by_cases hb2 : 2 ≤ b
  · -- **The stable range `b ≥ 2`.**  Take the top stage of the CW model of `B`: its structure map
    -- is a `π`-bijection up to degree `b + f + 1`, and the cellular induction gives the comparison
    -- of the pullback along it.
    set K : ℕ := (b + f + 1) + 2 with hK
    set s := Work.Serre.CWModel.towerA B b₀ b hb2 hconn K with hs
    exact Work.Serre.SPC.serrePairComparison_of p hp b₀ s.g s.y₀ s.gbase b f s.conn hB
      (fun i hi x =>
        Work.Serre.SPC.towerA_piMapN_bijective b₀ b hb2 hconn (b + f + 1) i hi x)
      (Work.Serre.SPC.towerComparison p hp b₀ e₀ he₀ b f hb2 hconn hfib0 hfib
        Work.Serre.ZeroCase.cellStepHyp Work.Serre.SPC.fibreTransport K)
  · -- **The case `b = 1`.**  Here the model of the base starts with `1`-cells, which is built
    -- separately; `Work.Serre.ZeroCase.b1Comparison` supplies a self-contained model together
    -- with the comparison of the pullback along it.
    have hb1 : b = 1 := by omega
    subst hb1
    obtain ⟨Γ, instΓ, γ₀, g, hbase, hΓ, hg, htow⟩ :=
      Work.Serre.ZeroCase.b1Comparison p hp b₀ e₀ he₀ f (f + 2) hf hB hfib0 hfib
    letI := instΓ
    exact Work.Serre.SPC.serrePairComparison_of p hp b₀ g γ₀ hbase 1 f hΓ hB
      (fun i hi x => hg i (by omega) x) htow

end Work.Serre
