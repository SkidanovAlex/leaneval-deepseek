import Mathlib.FieldTheory.KrullTopology
import Mathlib.Algebra.CharP.IntermediateField
import Submission.Work.SSGRoute.grunwald_distinct_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- For a field `E` finite over `↥K` (with `K/ℚ` finite), some open subgroup of `G_ℚ` consists of
elements which lie in `K.fixingSubgroup` and whose image in `Gal(ℚ̄/↥K)` lies in `E.fixingSubgroup`.

Sketch.  Let `b : Fin n → ↥E` be a `↥K`-basis of `E` and let `x i := ((b i : ↥E) : ℚ̄)` be its
image in `ℚ̄`.  Take the subgroup

`U' := K.fixingSubgroup ⊓ ⨅ i, MulAction.stabilizer SSGRoute.GalQ (x i)`

of `SSGRoute.GalQ` (the stabilisers are taken in `G_ℚ` acting on `ℚ̄`, so that the elements
stabilised are the coerced basis elements `x i : ℚ̄`).  It is open: `K.fixingSubgroup` is open by
`IntermediateField.fixingSubgroup_isOpen` (`K/ℚ` finite), each point stabiliser is open by
`stabilizer_isOpen_of_isIntegral` (`ℚ̄/ℚ` is integral), and a finite infimum of open subgroups is
open (`Subgroup.coe_iInf`, `isOpen_iInter_of_finite`).

Any `u ∈ U'` lies in `K.fixingSubgroup` (second factor) and fixes each `x i` (first factor, via
`MulAction.mem_stabilizer_iff` and `AlgEquiv.smul_def`).  Let `ℓ u` be the image of `u` in
`Gal(ℚ̄/↥K)` under `IntermediateField.fixingSubgroupEquiv K`; its underlying function is that of `u`
(`coe_fixingSubgroupEquiv`), so it fixes `K` and each `x i`.  Finally a `↥K`-basis generates `E`
as a `↥K`-algebra: `Algebra.adjoin ↥K (Set.range b) = ⊤` follows from `b.span_eq` and
`Submodule.span_le` (each `b i` lies in the adjoin by `Algebra.subset_adjoin`).  Hence the fixed
subalgebra `{y : ↥E | u (y : ℚ̄) = (y : ℚ̄)}` (multiplication by `map_mul`, addition by `map_add`,
`↥K`-scalars using that `u` fixes `K`) contains the range of `b`, so it is everything:
`ℓ u ∈ E.fixingSubgroup`. -/
theorem exists_open_subgroup_stabilizer (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] (E : IntermediateField ↥K SSGRoute.QBar) [FiniteDimensional ↥K E] :
    ∃ U' : Subgroup SSGRoute.GalQ, IsOpen (U' : Set SSGRoute.GalQ) ∧
      ∀ u ∈ U', ∃ (h : u ∈ K.fixingSubgroup),
        ((IntermediateField.fixingSubgroupEquiv K) ⟨u, h⟩) ∈ E.fixingSubgroup := by
  -- Regard `E` as an intermediate field over `ℚ` (same underlying set as `E`).
  let F : IntermediateField ℚ SSGRoute.QBar := E.restrictScalars ℚ
  have hFE : (F : Set SSGRoute.QBar) = (E : Set SSGRoute.QBar) :=
    IntermediateField.coe_restrictScalars ℚ
  -- `E` is finite over `ℚ`, hence `F.fixingSubgroup` is open in `G_ℚ`.
  haveI : FiniteDimensional ℚ ↥F := FiniteDimensional.trans ℚ ↥K ↥E
  refine ⟨F.fixingSubgroup, F.fixingSubgroup_isOpen, ?_⟩
  intro u hu
  -- `u` fixes every element of `F`, hence of `E`.
  have hF : ∀ x : SSGRoute.QBar, x ∈ F → u x = x := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hu
    intro x hx
    exact hu x hx
  -- `K` is contained in `F`: an element of `K` is the image of itself under the algebra map.
  have hKleF : K ≤ F := by
    intro x hx
    change x ∈ (E.restrictScalars ℚ : IntermediateField ℚ SSGRoute.QBar)
    rw [IntermediateField.mem_restrictScalars]
    simpa using E.algebraMap_mem' (⟨x, hx⟩ : ↥K)
  -- First conjunct: `u` lies in `K.fixingSubgroup`.
  have hK : u ∈ K.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact hF x (hKleF hx)
  refine ⟨hK, ?_⟩
  -- Second conjunct: the image of `u` in `Gal(ℚ̄/↥K)` fixes `E`.
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  rw [coe_fixingSubgroupEquiv K u hK]
  refine hF x ?_
  change x ∈ (E.restrictScalars ℚ : IntermediateField ℚ SSGRoute.QBar)
  rw [IntermediateField.mem_restrictScalars]
  exact hx

end Work.SSGRoute
