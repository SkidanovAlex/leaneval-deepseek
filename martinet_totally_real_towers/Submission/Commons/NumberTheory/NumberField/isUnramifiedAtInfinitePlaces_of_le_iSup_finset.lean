import Mathlib.Order.CompletePartialOrder
import Submission.Commons.NumberTheory.NumberField.isUnramifiedAtInfinitePlaces_of_forall_comap_isReal

open NumberField

namespace Commons.NumberTheory.NumberField

/-- **Key step.** Let `(f i)` be a family of intermediate fields of `AlgebraicClosure F`, each
unramified at the infinite places of `F`. If `L` is contained in the compositum `⨆ i, f i`, then
every infinite place of `L` whose restriction to `F` is real is itself real.

The proof extends an embedding `ψ : ↥L →+* ℂ` to `Ψ : AlgebraicClosure F →+* ℂ` and considers the
intermediate field `T` of elements on which `Ψ` is real; `T` contains each `f i` (since the `f i`
are unramified over `F` in the sense that a place of `f i` is real as soon as its restriction is),
hence contains `L`. -/
theorem isReal_of_isReal_comap_of_le_iSup {F : Type*} [Field F]
    {ι : Type*} {f : ι → IntermediateField F (AlgebraicClosure F)}
    (hunr : ∀ i, IsUnramifiedAtInfinitePlaces F ↥(f i))
    {L : IntermediateField F (AlgebraicClosure F)} (hL : L ≤ ⨆ i, f i)
    {w : InfinitePlace ↥L} (hw : (w.comap (algebraMap F ↥L)).IsReal) : w.IsReal := by
  rw [← InfinitePlace.mk_embedding w, InfinitePlace.isReal_mk_iff]
  -- `ψ := w.embedding` is a complex embedding of `L` whose restriction to `F` is real
  have hψ : ComplexEmbedding.IsReal (w.embedding.comp (algebraMap F ↥L)) := by
    rw [← InfinitePlace.isReal_mk_iff, ← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
    exact hw
  -- extend it to the algebraic closure of `F`
  let Ψ : AlgebraicClosure F →+* ℂ := ComplexEmbedding.lift (AlgebraicClosure F) w.embedding
  have hΨ : Ψ.comp (algebraMap ↥L (AlgebraicClosure F)) = w.embedding := by
    dsimp only [Ψ]
    rw [ComplexEmbedding.lift_comp_algebraMap]
  have hrealF : ComplexEmbedding.IsReal (Ψ.comp (algebraMap F (AlgebraicClosure F))) := by
    rw [IsScalarTower.algebraMap_eq F ↥L (AlgebraicClosure F), ← RingHom.comp_assoc, hΨ]
    exact hψ
  -- the intermediate field of elements where `Ψ` is real
  let T : IntermediateField F (AlgebraicClosure F) :=
    { carrier := {x | starRingEnd ℂ (Ψ x) = Ψ x}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [map_mul, map_mul, hx, hy]
      one_mem' := by simp
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [map_add, map_add, hx, hy]
      zero_mem' := by simp
      algebraMap_mem' := fun c => by
        have h := RingHom.congr_fun (ComplexEmbedding.isReal_iff.mp hrealF) c
        simpa [ComplexEmbedding.conjugate_coe_eq] using h
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [map_inv₀, map_inv₀, hx] }
  have hT : ∀ x : AlgebraicClosure F, x ∈ T ↔ starRingEnd ℂ (Ψ x) = Ψ x := fun _ => Iff.rfl
  -- each `f i` is contained in `T`
  have hfi : ∀ i, f i ≤ T := by
    intro i x hx
    rw [hT]
    have hunmix : ComplexEmbedding.IsUnmixed F (Ψ.comp (algebraMap ↥(f i) (AlgebraicClosure F))) :=
      InfinitePlace.isUnramified_mk_iff_isUnmixed.mp
        ((hunr i).isUnramified (InfinitePlace.mk _))
    have hreal : ComplexEmbedding.IsReal (Ψ.comp (algebraMap ↥(f i) (AlgebraicClosure F))) :=
      hunmix (by
        rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq F ↥(f i) (AlgebraicClosure F)]
        exact hrealF)
    have h := RingHom.congr_fun (ComplexEmbedding.isReal_iff.mp hreal) ⟨x, hx⟩
    simpa [ComplexEmbedding.conjugate_coe_eq] using h
  have hLT : L ≤ T := le_trans hL (iSup_le hfi)
  -- conclude that `ψ` is real
  rw [ComplexEmbedding.isReal_iff, RingHom.ext_iff]
  intro x
  rw [ComplexEmbedding.conjugate_coe_eq]
  have hxT : starRingEnd ℂ (Ψ ((x : ↥L) : AlgebraicClosure F)) = Ψ ((x : ↥L) : AlgebraicClosure F) :=
    (hT _).mp (hLT x.2)
  have h1 : Ψ ((x : ↥L) : AlgebraicClosure F) = w.embedding x := by
    dsimp only [Ψ]
    exact ComplexEmbedding.lift_algebraMap_apply (AlgebraicClosure F) w.embedding x
  rw [← h1]
  exact hxT

theorem isUnramifiedAtInfinitePlaces_of_le_iSup_finset {F : Type*} [Field F] [NumberField F]
    {ι : Type*} {f : ι → IntermediateField F (AlgebraicClosure F)} [∀ i, NumberField ↥(f i)]
    (hgal : ∀ i, IsGalois F ↥(f i)) (hunr : ∀ i, IsUnramifiedAtInfinitePlaces F ↥(f i))
    {L : IntermediateField F (AlgebraicClosure F)} [NumberField ↥L] [FiniteDimensional F ↥L]
    (hL : L ≤ ⨆ i, f i) : IsUnramifiedAtInfinitePlaces F ↥L := by
  refine isUnramifiedAtInfinitePlaces_of_forall_comap_isReal F ↥L ?_
  intro w hw w' hw'
  exact isReal_of_isReal_comap_of_le_iSup hunr hL (hw' ▸ hw)

end Commons.NumberTheory.NumberField