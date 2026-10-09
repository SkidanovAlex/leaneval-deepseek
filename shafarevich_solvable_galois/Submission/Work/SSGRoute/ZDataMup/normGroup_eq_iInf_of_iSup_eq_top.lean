import Mathlib
import Submission.Work.SSGRoute.ZDataMup.AbelianOnePlaceAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.SSGRoute.ZDataMup

open NK.LocalReciprocity

/-- **Norm group of a top field via a generating family of subfields.**

Let `B` be a field with Galois extension `F' = SeparableClosure B` and `D` the local Artin
reciprocity datum.  Let `E / B` be a finite abelian Galois extension and
`N : ι → IntermediateField B E` a family of finite normal subextensions whose compositum is `E`.
Then `N_{E/B} Eˣ = ⨅ i, N_{N_i/B} N_iˣ`.

Route: `Work.SSGRoute.ZDataMup.exists_level_realization` realizes `E` as a level `Λ` of
`maxAbelianSubext B (SeparableClosure B)` (using the commutativity `hcommE`); each `N i` maps into a
level `Λ i ≤ Λ` of `maxAbelianSubext B (SeparableClosure B)`; norm groups are transported by
`NK.LocalReciprocity.normGroup_eq_of_algEquiv`; the computation is closed by
`Work.SSGRoute.ZDataMup.normGroup_iSup_eq_iInf` (or by `NK.LocalCFT.NormGroup.normGroup_eq_iff_comap_fixingSubgroup`
plus `Subgroup.comap_iInf`) together with `⨆ i, Λ i = Λ`. -/
theorem normGroup_eq_iInf_of_iSup_eq_top
    {B : Type*} [Field B]
    (D : NK.LocalCFT.ArtinReciprocity B (SeparableClosure B))
    {E : Type*} [Field E] [Algebra B E] [FiniteDimensional B E] [IsGalois B E]
    (hcommE : ∀ a b : E ≃ₐ[B] E, a * b = b * a)
    {ι : Type*} (N : ι → IntermediateField B E)
    (hdim : ∀ i, FiniteDimensional B ↥(N i)) (hnorm : ∀ i, Normal B ↥(N i))
    (htop : ⨆ i, N i = ⊤) :
    NK.LocalReciprocity.normGroup B E = ⨅ i, NK.LocalReciprocity.normGroup B ↥(N i) := by
  haveI hgal : IsGalois B (SeparableClosure B) := inferInstance
  -- Realize `E` as a level `Λ` of the maximal abelian subextension of `SeparableClosure B / B`.
  obtain ⟨Λ, ⟨eΛ⟩⟩ := exists_level_realization (B := B) (E := E) hcommE
  -- The `B`-algebra embedding of `E` into `F^{ab}`, through `Λ`.
  let ψ : E →ₐ[B] (maxAbelianSubext B (SeparableClosure B)) :=
    (IntermediateField.val Λ).comp eΛ.toAlgHom
  have hψinj : Function.Injective ψ := fun x y h =>
    eΛ.injective ((IntermediateField.val Λ).injective h)
  -- The levels `Λ i` of `F^{ab}` cut out by the `N i`.
  let A : ι → IntermediateField B (maxAbelianSubext B (SeparableClosure B)) :=
    fun i => (N i).map ψ
  -- The isomorphism `N i ≃ₐ[B] Λ i` transports the norm group.
  have hAeq : ∀ i, normGroup B ↥(A i) = normGroup B ↥(N i) := fun i =>
    (normGroup_eq_of_algEquiv
      (Subalgebra.equivMapOfInjective (N i).toSubalgebra ψ hψinj)).symm
  have hfdA : ∀ i, FiniteDimensional B (A i) := fun i =>
    (Subalgebra.equivMapOfInjective (N i).toSubalgebra ψ hψinj).toLinearEquiv.finiteDimensional
  have hnA : ∀ i, Normal B (A i) := fun i =>
    Normal.of_algEquiv (h := hnorm i) (F := B)
      (Subalgebra.equivMapOfInjective (N i).toSubalgebra ψ hψinj)
  -- The `Λ i` generate `Λ`: `⨆ i, Λ i = (⨆ i, N i).map ψ = ⊤.map ψ = ψ.fieldRange = Λ`.
  have hsup : (⨆ i, A i) = Λ := by
    have h1 : (⨆ i, A i) = (⊤ : IntermediateField B E).map ψ := by
      have hgc := (IntermediateField.gc_map_comap ψ).l_iSup (f := N)
      rw [← hgc, htop]
    rw [h1]
    have h2 : (⊤ : IntermediateField B E).map ψ = ψ.fieldRange := by
      ext y; simp [IntermediateField.mem_map]
    rw [h2]
    ext y
    rw [AlgHom.mem_fieldRange]
    constructor
    · rintro ⟨x, rfl⟩
      exact (eΛ x).2
    · intro hy
      exact ⟨eΛ.symm ⟨y, hy⟩, by simp [ψ]⟩
  -- `Λ` is finite and normal over `B`, hence so is the sup.
  haveI hfdSup : FiniteDimensional B ↥(⨆ i, A i) := by
    rw [hsup]; exact eΛ.toLinearEquiv.finiteDimensional
  haveI hnSup : Normal B ↥(⨆ i, A i) := by
    rw [hsup]; exact Normal.of_algEquiv (F := B) eΛ
  -- The norm group of the join of the levels is the intersection of the norm groups.
  have hkey := normGroup_iSup_eq_iInf D A hfdA hnA
  have hE : normGroup B E = normGroup B ↥Λ := normGroup_eq_of_algEquiv eΛ
  rw [hE, ← hsup, hkey]
  exact iInf_congr fun i => hAeq i

end Work.SSGRoute.ZDataMup
