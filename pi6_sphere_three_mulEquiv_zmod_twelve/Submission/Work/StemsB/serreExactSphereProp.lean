import Mathlib
import Submission.Work.StemsB.SerreSphereInfty
import Submission.Work.StemsB.fibrewiseTrivial_of_contraction
import Submission.Work.StemsB.serreSphere_contract_big
import Submission.Work.StemsB.serreSphere_sets

/-!
# The sphere case of the Serre exact sequence in the stable range

`Work.StemsB.SerreExactSphere` (`SerreExact.lean`) is the `B = S^b` case of the Serre exact
sequence in the stable range, in the *homological* form of the fibre hypothesis (the fibre is path
connected and its homology vanishes in degrees `0 < j < f`).

The proof was already available in this directory: `Work.StemsB.serreExactSphere_infty`
(`SerreSphereInfty.lean`) proves the statement for a Hurewicz fibration over `SphModel b` which is
fibrewise trivial over the inner cube `sphLoopBig b`.  For a **Hurewicz** fibration that hypothesis
is a *theorem*: `sphLoopBig b` is contractible into the shell point `sphShellPt b`
(`Work.StemsB.serreSphere_contract_big`, `Work.StemsB.serreSphere_sets`), and a fibration over a
contractible set is fibrewise trivial
(`Work.StemsB.fibrewiseTrivial_of_contraction`).  This file supplies that hypothesis, i.e. proves
the `Prop` `Work.StemsB.SerreExactSphere` for `b ≥ 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.StemsB

noncomputable section

/-- **The sphere case of the Serre exact sequence, for `b ≥ 1`.** -/
theorem serreExactSphereProp_of_one_le (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (eInf : E) (heInf : p eInf = OnePoint.infty) (f : ℕ)
    (hp : IsHurewiczFibration p)
    (hconn : Subsingleton (HomotopyGroup (Fin 0) (↥{x : E | p x = OnePoint.infty}) ⟨eInf, heInf⟩))
    (hH : ∀ j : ℕ, 0 < j → j < f →
      IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥{x : E | p x = OnePoint.infty})).homology j))
    (i : ℕ) (hi : i < b + f) :
    IsIso (HomologicalComplex.homologyMap (relPairMap p OnePoint.infty) i) := by
  have hshell : sphShellPt b ∈ sphLoopBig b := (serreSphere_sets b hb).2.2.2.2
  obtain ⟨c, hc0, hc1, hcb⟩ := serreSphere_contract_big b hb hshell
  have hT : FibrewiseTrivial p (sphLoopBig b) ⟨sphShellPt b, hshell⟩ :=
    fibrewiseTrivial_of_contraction p hp (sphLoopBig b) ⟨sphShellPt b, hshell⟩ c hc0 hc1 hcb
  exact serreExactSphere_infty b hb E p hp ⟨sphShellPt b, hshell⟩ f hT eInf heInf hconn hH i hi

end

end Work.StemsB
