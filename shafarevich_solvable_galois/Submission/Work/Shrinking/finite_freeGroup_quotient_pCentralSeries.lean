import Mathlib.FieldTheory.Normal.Defs
import Submission.Work.ProP.finite_freePQuotient
import Submission.Work.Shrinking.map_pCentralSeries_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Shrinking

/-- For a finite type `α`, the quotient of the free group on `α` by the `ν`-th term of its
descending `p`-central series is finite.  Indeed any equivalence `α ≃ Fin n` with
`n = Fintype.card α` induces an isomorphism of groups `FreeGroup α ≃* FreeGroup (Fin n)`
(`FreeGroup.freeGroupCongr`) which maps `pCentralSeries p (FreeGroup α) ν` onto
`pCentralSeries p (FreeGroup (Fin n)) ν` (`map_pCentralSeries_surjective`), and the target is
`FreePQuotient p n ν`, finite by `Work.ProP.finite_freePQuotient`. -/
theorem finite_freeGroup_quotient_pCentralSeries (p : ℕ) [Fact p.Prime] (α : Type*) [Fintype α] (ν : ℕ) :
    Finite (FreeGroup α ⧸ Work.Shrinking.pCentralSeries p (FreeGroup α) ν) := by
  let n := Fintype.card α
  let e : α ≃ Fin n := Fintype.equivFin α
  let E : FreeGroup α ≃* FreeGroup (Fin n) := FreeGroup.freeGroupCongr e
  haveI : (pCentralSeries p (FreeGroup α) ν).Normal :=
    pCentralSeries_normal p (FreeGroup α) ν
  haveI : (pCentralSeries p (FreeGroup (Fin n)) ν).Normal :=
    pCentralSeries_normal p (FreeGroup (Fin n)) ν
  have hmap : Subgroup.map (E : FreeGroup α →* FreeGroup (Fin n))
      (pCentralSeries p (FreeGroup α) ν) = pCentralSeries p (FreeGroup (Fin n)) ν :=
    map_pCentralSeries_surjective p (E : FreeGroup α →* FreeGroup (Fin n)) E.surjective ν
  haveI : Finite (FreeGroup (Fin n) ⧸ pCentralSeries p (FreeGroup (Fin n)) ν) :=
    Work.ProP.finite_freePQuotient (p := p) n ν
  exact Finite.of_equiv _ (QuotientGroup.congr _ _ E hmap).toEquiv.symm

end Work.Shrinking
