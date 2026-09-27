import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.SL3Topology
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLComp.X3Topology.PolishOfLocallyCompact

/-!
# Topological background of the space of lattices `X₃ = SL₃(ℝ)/SL₃(ℤ)`

This file collects the elementary point-set topological facts about `X₃` needed by the
Einsiedler–Katok–Lindenstrauss argument (component `C2`, `P_X3`):

* `X₃` is Hausdorff (quotient of a topological group by the closed subgroup `Γ₃`);
* `X₃` is locally compact and second countable (quotients of locally compact / second countable
  groups by arbitrary subgroups);
* `X₃` is Polish, since a second countable locally compact Hausdorff space is Polish
  (`PolishOfLocallyCompact`);
* consequently `X₃` is a standard Borel space.
-/

open Work.EKLContract

set_option linter.style.haveILetI false

namespace Work.EKLComp

/-- `SL₃(ℝ)` is locally compact: it is the closed subset `det = 1` of the finite dimensional
matrix space `Matrix (Fin 3) (Fin 3) ℝ = (Fin 3 → Fin 3 → ℝ)`, which is locally compact as a
finite product of copies of `ℝ`. -/
lemma locallyCompactSpace_SL3 : LocallyCompactSpace SL3 := by
  have : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → ℝ))
  exact (isClosed_eq (continuous_id.matrix_det (n := Fin 3) (R := ℝ)) continuous_const).locallyCompactSpace

theorem X3Background :
    T2Space Work.EKLContract.X3 ∧ LocallyCompactSpace Work.EKLContract.X3 ∧
      SecondCountableTopology Work.EKLContract.X3 ∧ PolishSpace Work.EKLContract.X3 ∧
      StandardBorelSpace Work.EKLContract.X3 := by
  haveI : IsClosed (Γ3 : Set SL3) := Work.EKLContract.Lemmas.isClosed_Γ3
  haveI : LocallyCompactSpace SL3 := locallyCompactSpace_SL3
  haveI : SecondCountableTopology SL3 := Work.EKLContract.Lemmas.SL3Topology.2
  haveI : PolishSpace SL3 := Work.EKLContract.Lemmas.polishSpace_specialLinearGroup
  haveI : T2Space X3 := inferInstance
  haveI : LocallyCompactSpace X3 := inferInstance
  haveI : SecondCountableTopology X3 := inferInstance
  haveI : PolishSpace X3 := Work.EKLComp.X3Topology.PolishOfLocallyCompact X3
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

end Work.EKLComp
