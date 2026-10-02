import Mathlib
import Submission.Work.Thom.tautologicalQuotient

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Thom

/-- The `VectorBundleCore` of the tautological quotient `π*V / ℂ·s`, in the *strong* form needed by
the rest of the Thom chapter: the chosen index is *definitionally* the pair consisting of the base
index of `Z` at the point together with the chosen non-vanishing coordinate `tqCoord`.

Starting from `Work.Thom.tautologicalQuotient`, note that in a `VectorBundleCore` the fields
`coordChange_self`, `continuousOn_coordChange` and `coordChange_comp` do not mention `indexAt`.
Hence replacing `indexAt` (and the corresponding `mem_baseSet_at` witness) of the witness produced
by `tautologicalQuotient` with the explicit pair leaves all the other fields intact and yields the
required core. -/
theorem exists_tautQuotientCore {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) :
    ∃ Q : VectorBundleCore ℂ ↥(Work.Thom.zeroComplement (Work.Thom.realification Z))
        (EuclideanSpace ℂ (Fin m)) (ι × Fin (m + 1)),
      (∀ p : ↥(Work.Thom.zeroComplement (Work.Thom.realification Z)),
        Q.indexAt p = (Z.indexAt ((p : (Work.Thom.realification Z).TotalSpace)).1,
          Work.Thom.tqCoord Z p)) ∧
      (∀ (i : ι) (k : Fin (m + 1)), Q.baseSet (i, k) = Work.Thom.tqBaseSet Z i k) ∧
      (∀ (i j : ι) (k l : Fin (m + 1))
        (p : ↥(Work.Thom.zeroComplement (Work.Thom.realification Z)))
        (z : EuclideanSpace ℂ (Fin m)),
        Q.coordChange (i, k) (j, l) p z =
          Work.Thom.quoFun l ((Z.localTriv j ((p : (Work.Thom.realification Z).TotalSpace))).2)
            (Z.coordChange i j ((p : (Work.Thom.realification Z).TotalSpace)).1
              (Work.Thom.fillFun k z))) := by
  obtain ⟨Q, hbs, _hidx, hcc⟩ := tautologicalQuotient Z
  refine ⟨{ Q with
    indexAt := fun p => (Z.indexAt ((p : (realification Z).TotalSpace)).1, tqCoord Z p),
    mem_baseSet_at := fun p => ?_ }, ?_, ?_, ?_⟩
  · rw [hbs (Z.indexAt ((p : (realification Z).TotalSpace)).1) (tqCoord Z p)]
    exact ⟨Z.mem_baseSet_at _, tqCoord_spec Z p⟩
  · intro p
    rfl
  · intro i k
    exact hbs i k
  · intro i j k l p z
    exact hcc i j k l p z

end Work.Thom
