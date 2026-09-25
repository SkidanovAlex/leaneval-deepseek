import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.Main
import Submission.Commons.GroupTheory.PGroup.index_coatom_eq_prime

/-!
# `Work.ShafarevichKoch.exists_isOpen_index_two_le_of_isClosed`

**Every proper closed subgroup of `G_∅ = Gal(F_∅/F)` is contained in an open subgroup of
index `2`.**

`F_∅ = M.K` is the maximal unramified pro-`2` extension of the number field `F`, so `G_∅` is a
pro-`2` group: by `M.proP` every finite-dimensional Galois subextension of `F_∅/F` has pro-`2`
Galois group.  The statement is the pro-`2` shadow of the fact that *every proper subgroup of a
finite `2`-group lies in a subgroup of index `2`*, transported to the profinite group by the
fundamental theorem of infinite Galois theory.

Proof.  Let `H ≤ G_∅` be closed and proper, and let `L = F_∅^H` be its fixed field.  Since `H` is
closed, `Gal(F_∅/L) = H` (`InfiniteGalois.fixingSubgroup_fixedField`), so `L ≠ F`; pick
`x ∈ L`, `x ∉ F`.  Let `E/F` be a finite Galois subextension of `F_∅/F` containing `x`
(`FiniteGaloisIntermediateField.adjoin`).  The restriction `φ : G_∅ → Gal(E/F)` is surjective, and
its image `H.map φ` is *not* all of `Gal(E/F)`; otherwise, by
`InfiniteGalois.restrict_fixedField`, `L ∩ E = E^{H.map φ} = E^{Gal(E/F)} = F` would contain `x`.
Now `Gal(E/F)` is a finite `2`-group (by `M.proP`), so the proper subgroup `H.map φ` is contained in
a *maximal* subgroup `M₀` (coatoms of the subgroup lattice of a finite group are maximal subgroups:
`IsCoatomic`), and every maximal subgroup of a finite `p`-group has index `p = 2`
(`Commons.GroupTheory.PGroup.index_coatom_eq_prime`).  Pulling `M₀` back along the surjection `φ`
gives a subgroup `M' = φ⁻¹(M₀) ≤ G_∅` with `H ≤ M'`, index `2`, which is open because `φ` is
continuous and `Gal(E/F)` is discrete.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-- A proper closed subgroup of `G_∅ = Gal(F_∅/F)` lies in an open subgroup of index `2`: take a
finite Galois subextension `E/F` of `F_∅/F` meeting the fixed field of `H` non-trivially, restrict
`H` to the finite `2`-group `Gal(E/F)`, extend the (proper) image to a maximal subgroup and pull it
back. -/
theorem exists_isOpen_index_two_le_of_isClosed {F : Type} [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2)
    {H : Subgroup (Work.ClassFieldTower.galoisGroup M)}
    (hH : IsClosed (H : Set (Work.ClassFieldTower.galoisGroup M))) (hne : H ≠ ⊤) :
    ∃ M' : Subgroup (Work.ClassFieldTower.galoisGroup M),
      H ≤ M' ∧ M'.index = 2 ∧ IsOpen (M' : Set (Work.ClassFieldTower.galoisGroup M)) := by
  have hGalK : IsGalois F M.K := inferInstance
  -- the fixed field of `H`, and the fact that `H` is exactly its stabilizer (as `H` is closed)
  set L : IntermediateField F M.K := IntermediateField.fixedField H with hLdef
  have hfix : L.fixingSubgroup = H := by
    have h1 := InfiniteGalois.fixingSubgroup_fixedField (⟨H, hH⟩ : ClosedSubgroup (galoisGroup M))
    simpa only [hLdef] using h1
  -- `H ≠ ⊤` gives `L ≠ ⊥ = F`
  have hLne : L ≠ ⊥ := by
    intro hb
    apply hne
    rw [← hfix, hb, IntermediateField.fixingSubgroup_bot]
  obtain ⟨x, hxL, hxbot⟩ := SetLike.exists_of_lt (lt_of_le_of_ne bot_le hLne.symm)
  -- a finite Galois subextension `E` of `F_∅/F` containing `x`
  have hfin : Finite ({x} : Set M.K) := Set.finite_singleton x
  let E : FiniteGaloisIntermediateField F M.K := FiniteGaloisIntermediateField.adjoin F ({x} : Set M.K)
  have hxE : x ∈ E.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin F {x} (Set.mem_singleton x)
  have hfdE : FiniteDimensional F ↥E.toIntermediateField := E.finiteDimensional
  have hgalE : IsGalois F ↥E.toIntermediateField := E.isGalois
  -- the restriction of `G_∅` to the finite quotient `Gal(E/F)`
  let φ : galoisGroup M →* (↥E.toIntermediateField ≃ₐ[F] ↥E.toIntermediateField) :=
    AlgEquiv.restrictNormalHom ↥E.toIntermediateField
  have hφsurj : Function.Surjective φ := AlgEquiv.restrictNormalHom_surjective M.K
  -- the image of `H` is a proper subgroup of `Gal(E/F)`
  have hJne : H.map φ ≠ ⊤ := by
    intro hJtop
    have hfx : x ∈ IntermediateField.fixedField H ⊓ E.toIntermediateField := ⟨hxL, hxE⟩
    have h2 : IntermediateField.fixedField H ⊓ (E.toIntermediateField : IntermediateField F M.K)
        = IntermediateField.lift (IntermediateField.fixedField (H.map φ)) := by
      have h3 := InfiniteGalois.restrict_fixedField H (E.toIntermediateField)
      simpa only [φ] using h3
    rw [h2, hJtop] at hfx
    rw [InfiniteGalois.fixedField_bot, IntermediateField.lift_bot] at hfx
    exact hxbot hfx
  haveI : Fintype (↥E.toIntermediateField ≃ₐ[F] ↥E.toIntermediateField) :=
    AlgEquiv.fintype F ↥E.toIntermediateField
  -- `Gal(E/F)` is a finite `2`-group
  have hpg : IsPGroup 2 (↥E.toIntermediateField ≃ₐ[F] ↥E.toIntermediateField) :=
    M.proP E.toIntermediateField E.finiteDimensional E.isGalois
  -- a maximal subgroup of `Gal(E/F)` above the image of `H`, of index `2`
  obtain ⟨M₀, hM₀coat, hJM₀⟩ := (IsCoatomic.eq_top_or_exists_le_coatom (H.map φ)).resolve_left hJne
  have hidx : M₀.index = 2 := Commons.GroupTheory.PGroup.index_coatom_eq_prime hpg hM₀coat
  refine ⟨Subgroup.comap φ M₀, ?_, ?_, ?_⟩
  · exact (Subgroup.map_le_iff_le_comap).mp hJM₀
  · rw [Subgroup.index_comap_of_surjective _ hφsurj, hidx]
  · have hcont : Continuous φ := InfiniteGalois.restrictNormalHom_continuous (E.toIntermediateField)
    exact hcont.isOpen_preimage M₀.carrier (isOpen_discrete M₀.carrier)

end Work.ShafarevichKoch
