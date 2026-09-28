import Mathlib
import Submission.Work.Serre.E2dEngine
import Submission.Work.Cohomology.RelMVLes
import Submission.Work.Cohomology.Endgame.relCohMV_elim
import Submission.Work.ThreeConnected.Excision.relMV_iso_of_acyclic
import Submission.Work.ThreeConnected.Excision.isIso_relMVdelta_of_coverData

/-!
# The Mayer–Vietoris step of the E2(d) argument for the pullback

`Work.Serre.SerreE2d` computes `H_{k+n}(τ^*E, τ^*E|_{∂Iⁿ})` by induction on `n`.  The induction
step replaces the cube `I^{n+1}` by the cover consisting of the two slabs

* `U = pbPre p τ (slabU n) = {last < 3/4}`,
* `V = pbPre p τ (slabV n) = {last > 1/4}`,

whose intersection is the middle slab `pbPre p τ (slabM n)`.  The relative Mayer–Vietoris sequence
of this cover reads

`⋯ → H_{m+1}(U, U ∩ A) ⊕ H_{m+1}(V, V ∩ A) → H_{m+1}(X, A) --δ--> H_m(U ∩ V, U ∩ V ∩ A) → ⋯`

for `X = τ^*E` and `A = pbPre p τ (cubeBdryS (n+1))`.  If the two chart terms vanish in every
degree, the connecting map `δ` is an isomorphism, which is the content of
`Work.Serre.mvStep_pullback`.

The actual computations (that the two chart terms really do vanish) are the acyclicity of the slab
pairs, and are not part of this file: here the vanishings are hypotheses.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- `pbPre` is the preimage of `S` under the second projection of the pullback. -/
lemma pbPre_eq_preimage {E B : Type} [TopologicalSpace E] [TopologicalSpace B] {m : ℕ}
    (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC m, B)) (S : Set (Work.Stems.Cubical.IC m)) :
    pbPre p τ S = (Work.StemsB.pullbackSnd p τ) ⁻¹' S := rfl

/-- **The relative Mayer–Vietoris step for an open cover of a space.**

If `X = U ∪ V` is an open cover and the relative homology of the two chart pairs `(U, U ∩ A)` and
`(V, V ∩ A)` vanishes in every degree, then the connecting map of the relative Mayer–Vietoris
sequence is an isomorphism, i.e. `H_{m+1}(X, A) ≅ H_m(U ∩ V, U ∩ V ∩ A)`. -/
theorem mvStep_of_vanishing {X : TopCat} (A U V : Set X) (hUo : IsOpen U) (hVo : IsOpen V)
    (hcov : U ∪ V = Set.univ)
    (hU : ∀ m, IsZero ((Work.Cohomology.relChains (TopCat.of ↥U)
      ((Subtype.val : ↥U → X) ⁻¹' A)).homology m))
    (hV : ∀ m, IsZero ((Work.Cohomology.relChains (TopCat.of ↥V)
      ((Subtype.val : ↥V → X) ⁻¹' A)).homology m))
    (m : ℕ) :
    Nonempty ((Work.Cohomology.relChains X A).homology (m+1) ≅
      ((Work.Cohomology.relChains (TopCat.of ↥(U ∩ V))
        ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' (U ∩ V ∩ A))).homology m)) := by
  -- the middle term of the relative Mayer–Vietoris sequence vanishes
  have h₂ : ∀ n, IsZero (Work.Cohomology.relMVH₂ X A U V n) := by
    intro n
    refine Work.ThreeConnected.Excision.isZero_homology_biprod ?_ ?_
    · obtain ⟨e⟩ := Work.Cohomology.Endgame.relSmallChains_iso_relChains U V U (U ∩ A)
        Set.inter_subset_left (Or.inl subset_rfl)
      have hset : ((Subtype.val : ↥U → X) ⁻¹' (U ∩ A)) = ((Subtype.val : ↥U → X) ⁻¹' A) := by
        ext x
        exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
      rw [hset] at e
      exact IsZero.of_iso (hU n)
        ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso e)
    · obtain ⟨e⟩ := Work.Cohomology.Endgame.relSmallChains_iso_relChains U V V (V ∩ A)
        Set.inter_subset_left (Or.inr subset_rfl)
      have hset : ((Subtype.val : ↥V → X) ⁻¹' (V ∩ A)) = ((Subtype.val : ↥V → X) ⁻¹' A) := by
        ext x
        exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
      rw [hset] at e
      exact IsZero.of_iso (hV n)
        ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso e)
  -- hence the connecting map of the sequence is an isomorphism
  haveI := Work.ThreeConnected.Excision.relMV_iso_of_acyclic (X := X) A U V h₂ m
  -- and the first term of the sequence is the relative homology of the intersection
  obtain ⟨eUV⟩ := Work.Cohomology.Endgame.relSmallChains_iso_relChains U V (U ∩ V) (U ∩ V ∩ A)
    Set.inter_subset_left (Or.inl Set.inter_subset_left)
  exact ⟨(Work.Cohomology.relMVSmallIso X A U V hUo hVo hcov (m+1)).symm
    ≪≫ asIso (Work.Cohomology.relMVδ X A U V m)
    ≪≫ (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) m).mapIso eUV⟩

theorem mvStep_pullback (n : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (τ : C(Work.Stems.Cubical.IC (n+1), B))
    (hU : ∀ m, CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains
        (TopCat.of ↥(Work.Serre.pbPre p τ (Work.Serre.slabU n)))
        (Work.Serre.pbSub p τ (Work.Serre.slabU n)
          (Work.Serre.slabU n ∩ Work.Serre.cubeBdryS (n+1)))).homology m))
    (hV : ∀ m, CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains
        (TopCat.of ↥(Work.Serre.pbPre p τ (Work.Serre.slabV n)))
        (Work.Serre.pbSub p τ (Work.Serre.slabV n)
          (Work.Serre.slabV n ∩ Work.Serre.cubeBdryS (n+1)))).homology m))
    (m : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback p τ))
        (Work.Serre.pbPre p τ (Work.Serre.cubeBdryS (n+1)))).homology (m+1)) ≅
      ((Work.Cohomology.relChains (TopCat.of ↥(Work.Serre.pbPre p τ (Work.Serre.slabM n)))
        (Work.Serre.pbSub p τ (Work.Serre.slabM n)
          (Work.Serre.slabM n ∩ Work.Serre.cubeBdryS (n+1)))).homology m)) := by
  -- the two slabs are open and cover the pullback
  have hUo : IsOpen (pbPre p τ (slabU n)) := by
    rw [pbPre_eq_preimage]
    exact IsOpen.preimage (Work.StemsB.pullbackSnd p τ).continuous (isOpen_slabU n)
  have hVo : IsOpen (pbPre p τ (slabV n)) := by
    rw [pbPre_eq_preimage]
    exact IsOpen.preimage (Work.StemsB.pullbackSnd p τ).continuous (isOpen_slabV n)
  have hcov : pbPre p τ (slabU n) ∪ pbPre p τ (slabV n) = Set.univ := by
    rw [pbPre_eq_preimage, pbPre_eq_preimage, ← Set.preimage_union, slabU_union_slabV,
      Set.preimage_univ]
  -- the two vanishing hypotheses, in the form used by the general step
  have hU' : ∀ m, IsZero ((Work.Cohomology.relChains (TopCat.of ↥(pbPre p τ (slabU n)))
      ((Subtype.val : ↥(pbPre p τ (slabU n)) → TopCat.of (Work.StemsB.Pullback p τ)) ⁻¹'
        (pbPre p τ (cubeBdryS (n+1))))).homology m) := by
    intro k
    have hset : pbSub p τ (slabU n) (slabU n ∩ cubeBdryS (n+1))
        = ((Subtype.val : ↥(pbPre p τ (slabU n)) → TopCat.of (Work.StemsB.Pullback p τ)) ⁻¹'
            (pbPre p τ (cubeBdryS (n+1)))) := by
      ext x
      simp only [mem_pbSub, Set.mem_preimage, mem_pbPre, Set.mem_inter_iff]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨x.2, h⟩
    have hk := hU k
    rw [hset] at hk
    exact hk
  have hV' : ∀ m, IsZero ((Work.Cohomology.relChains (TopCat.of ↥(pbPre p τ (slabV n)))
      ((Subtype.val : ↥(pbPre p τ (slabV n)) → TopCat.of (Work.StemsB.Pullback p τ)) ⁻¹'
        (pbPre p τ (cubeBdryS (n+1))))).homology m) := by
    intro k
    have hset : pbSub p τ (slabV n) (slabV n ∩ cubeBdryS (n+1))
        = ((Subtype.val : ↥(pbPre p τ (slabV n)) → TopCat.of (Work.StemsB.Pullback p τ)) ⁻¹'
            (pbPre p τ (cubeBdryS (n+1)))) := by
      ext x
      simp only [mem_pbSub, Set.mem_preimage, mem_pbPre, Set.mem_inter_iff]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨x.2, h⟩
    have hk := hV k
    rw [hset] at hk
    exact hk
  obtain ⟨e⟩ := mvStep_of_vanishing (X := TopCat.of (Work.StemsB.Pullback p τ))
    (pbPre p τ (cubeBdryS (n+1))) (pbPre p τ (slabU n)) (pbPre p τ (slabV n))
    hUo hVo hcov hU' hV' m
  -- the intersection of the two slabs is the middle slab
  have hUV : pbPre p τ (slabU n) ∩ pbPre p τ (slabV n) = pbPre p τ (slabM n) := by
    rw [slabM_eq_inter]
    ext x
    simp only [mem_pbPre, Set.mem_inter_iff]
  have hC : ((Subtype.val : ↥(pbPre p τ (slabM n)) → TopCat.of (Work.StemsB.Pullback p τ)) ⁻¹'
        (pbPre p τ (slabM n) ∩ pbPre p τ (cubeBdryS (n+1))))
      = pbSub p τ (slabM n) (slabM n ∩ cubeBdryS (n+1)) := by
    ext x
    simp only [mem_pbSub, Set.mem_preimage, Set.mem_inter_iff, mem_pbPre]
  have hObj : Work.Cohomology.relChains
        (TopCat.of ↥(pbPre p τ (slabU n) ∩ pbPre p τ (slabV n)))
        ((Subtype.val : ↥(pbPre p τ (slabU n) ∩ pbPre p τ (slabV n)) →
            TopCat.of (Work.StemsB.Pullback p τ)) ⁻¹'
          ((pbPre p τ (slabU n) ∩ pbPre p τ (slabV n)) ∩ pbPre p τ (cubeBdryS (n+1))))
      = Work.Cohomology.relChains (TopCat.of ↥(pbPre p τ (slabM n)))
          (pbSub p τ (slabM n) (slabM n ∩ cubeBdryS (n+1))) := by
    rw [hUV, hC]
  exact ⟨e ≪≫ (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) m).mapIso
    (eqToIso hObj)⟩

end

end Work.Serre
