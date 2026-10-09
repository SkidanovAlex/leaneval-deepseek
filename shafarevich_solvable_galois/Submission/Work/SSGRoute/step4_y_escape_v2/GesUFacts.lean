import Mathlib
import Submission.Work.SSGRoute.ges_escape_aux
import Submission.Work.SSGRoute.finiteIndex_gesU
import Submission.Work.SSGRoute.EscapeCoreLib.charSeparation
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_vocab
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The two subgroup facts about `U' = U ⊔ C_K^p` needed by the correction

The class field of `U' = gesU K p T' ⊔ pPowSubgroup p C_K` inside `Ω` is the field in which the
escape-form Grünwald correction chooses its Artin symbol
(`EscapeCoreLib.exists_intermediateField_normClassSubgroup_eq`), which needs `U'` to be **open**
and of **finite index** in `C_K`.  Both are immediate from the corresponding facts for `U = gesU`
(`Work.SSGRoute.isOpen_gesU`, `Work.SSGRoute.finiteIndex_gesU`) because `U'` contains `U`:
a subgroup containing an open subgroup is open (it is a union of translates of the open subgroup),
and a subgroup containing a finite-index subgroup has finite index.
-/

namespace Work.SSGRoute.step4_y_escape_v2

open scoped Pointwise
open NK.GlobalCFT

set_option linter.style.haveILetI false

/-- **A subgroup containing an open subgroup is open** (it is a union of translates of the open
subgroup). -/
theorem isOpen_of_le_isOpen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H K : Subgroup G} (hle : H ≤ K) (hH : IsOpen (H : Set G)) : IsOpen (K : Set G) := by
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have h1 : IsOpen ((fun y : G => g * y) '' (H : Set G)) := (Homeomorph.mulLeft g).isOpenMap _ hH
  have h2 : g ∈ (fun y : G => g * y) '' (H : Set G) := ⟨1, H.one_mem, mul_one g⟩
  refine Filter.mem_of_superset (h1.mem_nhds h2) ?_
  rintro x ⟨y, hy, rfl⟩
  exact K.mul_mem hg (hle hy)

/-- **A subgroup containing a finite-index subgroup has finite index.** -/
theorem finiteIndex_of_le {G : Type} [Group G] {H K : Subgroup G} (hle : H ≤ K)
    (hH : H.FiniteIndex) : K.FiniteIndex := by
  haveI := hH
  exact Subgroup.finiteIndex_of_le hle

/-- **`U' = gesU K p T' ⊔ C_K^p` is open** (it contains the open `gesU K p T'`). -/
theorem isOpen_gesU_sup_pPow (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [NumberField K]
    (T' : Finset (NK.Chebotarev.PrimeIdeal K)) :
    IsOpen (((Work.SSGRoute.GrunwaldEscapeCore.gesU K p T'
      ⊔ Work.SSGRoute.EscapeCoreLib.pPowSubgroup p (IdeleClassGroup K) :
      Subgroup (IdeleClassGroup K)) : Set (IdeleClassGroup K))) :=
  isOpen_of_le_isOpen le_sup_left (Work.SSGRoute.isOpen_gesU (K := K) Fact.out T')

/-- **`U' = gesU K p T' ⊔ C_K^p` has finite index** (it contains the finite-index
`gesU K p T'`). -/
theorem finiteIndex_gesU_sup_pPow (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [NumberField K]
    (T' : Finset (NK.Chebotarev.PrimeIdeal K)) :
    (Work.SSGRoute.GrunwaldEscapeCore.gesU K p T'
      ⊔ Work.SSGRoute.EscapeCoreLib.pPowSubgroup p (IdeleClassGroup K) :
      Subgroup (IdeleClassGroup K)).FiniteIndex :=
  finiteIndex_of_le le_sup_left (Work.SSGRoute.finiteIndex_gesU K p T')

end Work.SSGRoute.step4_y_escape_v2
