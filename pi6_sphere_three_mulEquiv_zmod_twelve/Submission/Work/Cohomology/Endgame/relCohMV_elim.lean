import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.relCohMV_les
import Submission.Work.Cohomology.relSmallCochains_iso
import Submission.Work.Cohomology.relComplexIsoDual

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology.Endgame

noncomputable section

/-! ## General helpers -/

/-- `inclChains` is the chain map induced by the inclusion of the subspace. -/
theorem inclChains_eq_map (X : TopCat) (A : Set X) :
    inclChains X A
      = SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A)) (ModuleCat.of ℤ ℤ) := rfl

/-- `Subsingleton` transports backwards along an isomorphism of `ℤ`-modules. -/
theorem subsingleton_of_iso {M N : ModuleCat ℤ} (e : M ≅ N) (h : Subsingleton N) :
    Subsingleton M :=
  ⟨fun a b => e.toLinearEquiv.injective (Subsingleton.elim _ _)⟩

/-- `Subsingleton` transports forwards along an isomorphism of `ℤ`-modules. -/
theorem subsingleton_of_iso_symm {M N : ModuleCat ℤ} (e : M ≅ N) (h : Subsingleton M) :
    Subsingleton N :=
  ⟨fun a b => e.toLinearEquiv.symm.injective (Subsingleton.elim _ _)⟩

/-- A biproduct of two subsingleton `ℤ`-modules is a subsingleton. -/
theorem subsingleton_biprod (M N : ModuleCat ℤ) [Subsingleton ↥M] [Subsingleton ↥N] :
    Subsingleton ↥(M ⊞ N) :=
  ⟨fun a b => (ModuleCat.biprodIsoProd M N).toLinearEquiv.injective (Subsingleton.elim _ _)⟩

/-- The contravariant dual of an isomorphism of chain complexes. -/
def dualComplexIso {C D : ChainComplex (ModuleCat ℤ) ℕ} (e : C ≅ D) :
    dualComplex ℤ D ≅ dualComplex ℤ C where
  hom := dualComplexMap ℤ C D e.hom
  inv := dualComplexMap ℤ D C e.inv
  hom_inv_id := by
    rw [← dualComplexMap_comp (f := e.inv) (g := e.hom), e.inv_hom_id, dualComplexMap_id]
  inv_hom_id := by
    rw [← dualComplexMap_comp (f := e.hom) (g := e.inv), e.hom_inv_id, dualComplexMap_id]

/-- **The relative cohomology of a pair is the cohomology of the dual of any chain complex that is
isomorphic to the relative chain complex of the pair.** -/
theorem relCohomology_iso_homology {Y : TopCat} {B : Set Y} {C : ChainComplex (ModuleCat ℤ) ℕ}
    (e : C ≅ relChains Y B) (k : ℕ) :
    Nonempty (relCohomology ℤ Y B k ≅ (dualComplex ℤ C).homology k) := by
  obtain ⟨e0⟩ := relComplexIsoDual Y B
  exact ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) k).mapIso e0
    ≪≫ (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) k).mapIso
      (dualComplexIso e)⟩

/-! ## The small relative chains of a subset lying in one chart -/

variable {X : TopCat}

/-- If every simplex lying in `S` is small (e.g. `S ⊆ U` or `S ⊆ V`), then the small simplices
lying in `S` are exactly the singular simplices of the subspace `S`. -/
theorem smallInSubcomplex_eq_range (U V S : Set X) (hS : S ⊆ U ∨ S ⊆ V) :
    smallInSubcomplex U V S = Subfunctor.range (TopCat.toSSet.map (subtypeIncl X S)) := by
  ext n σ
  rw [Subfunctor.range_obj]
  constructor
  · intro h
    exact exists_map_inclUX_of_range_subset S n σ h.2
  · rintro ⟨a, rfl⟩
    have hcoe : ∀ z : stdSimplex ℝ (Fin (n.unop.len + 1)),
        TopCat.toSSetObjEquivT X n ((TopCat.toSSet.map (subtypeIncl X S)).app n a) z
          = subtypeIncl X S (TopCat.toSSetObjEquivT (TopCat.of ↥S) n a z) := fun _ => rfl
    refine ⟨?_, ?_⟩
    · rcases hS with hS | hS
      · left
        rintro y ⟨z, rfl⟩
        show TopCat.toSSetObjEquivT X n ((TopCat.toSSet.map (subtypeIncl X S)).app n a) z ∈ U
        rw [hcoe z]
        exact hS (TopCat.toSSetObjEquivT (TopCat.of ↥S) n a z).2
      · right
        rintro y ⟨z, rfl⟩
        show TopCat.toSSetObjEquivT X n ((TopCat.toSSet.map (subtypeIncl X S)).app n a) z ∈ V
        rw [hcoe z]
        exact hS (TopCat.toSSetObjEquivT (TopCat.of ↥S) n a z).2
    · rintro y ⟨z, rfl⟩
      show TopCat.toSSetObjEquivT X n ((TopCat.toSSet.map (subtypeIncl X S)).app n a) z ∈ S
      rw [hcoe z]
      exact (TopCat.toSSetObjEquivT (TopCat.of ↥S) n a z).2

/-- The corestriction of the small simplices lying in `S` to the subspace `S` is an isomorphism
whenever every simplex of `S` is small. -/
theorem isIso_homOfLe_range (U V S : Set X) (hS : S ⊆ U ∨ S ⊆ V) :
    IsIso (Subfunctor.homOfLe (smallInSubcomplex_le_range U V S)) := by
  refine ⟨Subfunctor.homOfLe (le_of_eq (smallInSubcomplex_eq_range U V S hS).symm), ?_, ?_⟩
  · ext x; rfl
  · ext x; rfl

/-- **The lift of a small-in-`S` simplex is an isomorphism** when `S` is contained in one of the
two charts. -/
theorem isIso_smallInLift_of_subset (U V S : Set X) (hS : S ⊆ U ∨ S ⊆ V) :
    IsIso (smallInLift U V S) := by
  rw [smallInLift]
  haveI := isIso_homOfLe_range U V S hS
  infer_instance

/-! ## The compatibility of the small chains of `(S,C)` with the genuine relative chains -/

/-- The canonical homeomorphism `C ≅ S ∩ C` for `C ⊆ S`. -/
def subPreImageHomeo (S C : Set X) (h : C ⊆ S) :
    TopCat.of ↥C ≅ TopCat.of ↥((Subtype.val : ↥S → X) ⁻¹' C) where
  hom := TopCat.ofHom ⟨fun x => ⟨⟨(x : X), h x.2⟩, x.2⟩, by fun_prop⟩
  inv := TopCat.ofHom ⟨fun y => ⟨(y.1.1 : X), y.2⟩, by fun_prop⟩
  hom_inv_id := by ext x; rfl
  inv_hom_id := by ext y; rfl

/-- `subPreImageHomeo` intertwines the two inclusions into `X`. -/
theorem subPreImageHomeo_comp (S C : Set X) (h : C ⊆ S) :
    (subPreImageHomeo S C h).hom
      ≫ subtypeIncl (TopCat.of ↥S) ((Subtype.val : ↥S → X) ⁻¹' C)
      ≫ subtypeIncl X S = subtypeIncl X C := by
  apply TopCat.hom_ext
  ext x
  rfl

/-- **The chain-level naturality of the small-in-`C` chains lying in `S`.** -/
theorem subInclChain_natural_comp (U V S C : Set X) (hCS : C ⊆ S) :
    subInclChain U V hCS ≫ SSet.chainComplexMap (smallInLift U V S) (ModuleCat.of ℤ ℤ)
      = SSet.chainComplexMap (smallInLift U V C) (ModuleCat.of ℤ ℤ)
        ≫ (SSet.chainComplexMap (TopCat.toSSet.map (subPreImageHomeo S C hCS).hom)
              (ModuleCat.of ℤ ℤ)
            ≫ inclChains (TopCat.of ↥S) ((Subtype.val : ↥S → X) ⁻¹' C)) := by
  have hkey : Subfunctor.homOfLe (smallInSubcomplex_mono hCS) ≫ smallInLift U V S
      = smallInLift U V C ≫ TopCat.toSSet.map (subPreImageHomeo S C hCS).hom
        ≫ TopCat.toSSet.map (subtypeIncl (TopCat.of ↥S)
            ((Subtype.val : ↥S → X) ⁻¹' C)) := by
    apply (cancel_mono (TopCat.toSSet.map (subtypeIncl X S))).1
    rw [Category.assoc, smallInLift_comp, Subfunctor.homOfLe_ι]
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      subPreImageHomeo_comp, smallInLift_comp]
  have h := congrArg (fun (f : smallInSSet U V C ⟶ TopCat.toSSet.obj (TopCat.of ↥S)) =>
      SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)) hkey
  simpa only [inclChains_eq_map, subInclChain, Functor.map_comp, Category.assoc] using h

/-- **The small relative chains `C^{U,V}(S,C)` compute the genuine relative chains of the pair
`(S, C)`** whenever `S` is contained in one of the two charts. -/
theorem relSmallChains_iso_relChains (U V S C : Set X) (hCS : C ⊆ S)
    (hS : S ⊆ U ∨ S ⊆ V) :
    Nonempty (relSmallChains U V S C hCS ≅
      relChains (TopCat.of ↥S) ((Subtype.val : ↥S → X) ⁻¹' C)) := by
  have hC : C ⊆ U ∨ C ⊆ V :=
    hS.imp (fun h => hCS.trans h) (fun h => hCS.trans h)
  haveI hSiso : IsIso (smallInLift U V S) := isIso_smallInLift_of_subset U V S hS
  haveI hCiso : IsIso (smallInLift U V C) := isIso_smallInLift_of_subset U V C hC
  let eS : smallInChains U V S ≅ singularChains ℤ (TopCat.of ↥S) :=
    Functor.mapIso ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
      (asIso (smallInLift U V S))
  let eC : smallInChains U V C ≅ singularChains ℤ (TopCat.of ↥C) :=
    Functor.mapIso ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
      (asIso (smallInLift U V C))
  let gIso : singularChains ℤ (TopCat.of ↥C)
      ≅ singularChains ℤ (TopCat.of ↥((Subtype.val : ↥S → X) ⁻¹' C)) :=
    Functor.mapIso ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
      (Functor.mapIso TopCat.toSSet (subPreImageHomeo S C hCS))
  let k := inclChains (TopCat.of ↥S) ((Subtype.val : ↥S → X) ⁻¹' C)
  have hsq : subInclChain U V hCS ≫ eS.hom = eC.hom ≫ (gIso.hom ≫ k) :=
    subInclChain_natural_comp U V S C hCS
  refine ⟨cokernel.mapIso (subInclChain U V hCS) (gIso.hom ≫ k) eC eS hsq
    ≪≫ (cokernel.mapIso k (gIso.hom ≫ k) gIso.symm (Iso.refl _) ?_).symm⟩
  simp

/-! ## The target -/

/-- **Relative Mayer–Vietoris, elimination form.**

For an open cover `U ∪ V = X` and any subset `A ⊆ X`, if the relative cohomology `H^n` of the
intersection pair `(U ∩ V, (U ∩ V) ∩ A)` vanishes and the relative cohomology `H^{n+1}` of the two
chart pairs `(U, U ∩ A)` and `(V, V ∩ A)` vanish, then `H^{n+1}(X, A)` vanishes.

This is the exactness of the relative Mayer–Vietoris sequence at `H^{n+1}(X,A)` (see
`Work.Cohomology.relCohMVLes_exact₁`, whose terms are the duals of the small relative chain
complexes; the comparison with the genuine relative cohomology is
`Work.Cohomology.relSmallCochains_iso` for the top term, and the analogous statement for the
`U`-, `V`- and intersection-terms, which may be proved from the quasi-isomorphism
`Work.Cohomology.smallInToSingA` (an isomorphism for open covers) together with
`Work.Cohomology.relComplexIsoDual`). -/
theorem relCohMV_elim (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ)
    (h0 : Subsingleton (Work.Cohomology.relCohomology ℤ (TopCat.of ↥(U ∩ V))
      ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' A) n))
    (h1 : Subsingleton (Work.Cohomology.relCohomology ℤ (TopCat.of ↥U)
      ((Subtype.val : ↥U → X) ⁻¹' A) (n + 1)))
    (h2 : Subsingleton (Work.Cohomology.relCohomology ℤ (TopCat.of ↥V)
      ((Subtype.val : ↥V → X) ⁻¹' A) (n + 1))) :
    Subsingleton (Work.Cohomology.relCohomology ℤ X A (n + 1)) := by
  -- comparison isomorphisms for the four terms of the Mayer–Vietoris sequence
  obtain ⟨eTop⟩ := relSmallCochains_iso X A U V hU hV hcov (n + 1)
  have hsetU : ((Subtype.val : ↥U → X) ⁻¹' (U ∩ A)) = ((Subtype.val : ↥U → X) ⁻¹' A) := by
    ext x; exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  obtain ⟨eUmv⟩ := relSmallChains_iso_relChains U V U (U ∩ A) Set.inter_subset_left
    (Or.inl subset_rfl)
  rw [hsetU] at eUmv
  obtain ⟨eU⟩ := relCohomology_iso_homology eUmv (n + 1)
  have hsetV : ((Subtype.val : ↥V → X) ⁻¹' (V ∩ A)) = ((Subtype.val : ↥V → X) ⁻¹' A) := by
    ext x; exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  obtain ⟨eVmv⟩ := relSmallChains_iso_relChains U V V (V ∩ A) Set.inter_subset_left
    (Or.inr subset_rfl)
  rw [hsetV] at eVmv
  obtain ⟨eV⟩ := relCohomology_iso_homology eVmv (n + 1)
  have hsetUV : ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' (U ∩ V ∩ A))
      = ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' A) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨⟨x.2.1, x.2.2⟩, h⟩
  obtain ⟨eUVmv⟩ := relSmallChains_iso_relChains U V (U ∩ V) (U ∩ V ∩ A) Set.inter_subset_left
    (Or.inl Set.inter_subset_left)
  rw [hsetUV] at eUVmv
  obtain ⟨eUV⟩ := relCohomology_iso_homology eUVmv n
  -- the four small models of the terms of the Mayer-Vietoris sequence
  let MU : ModuleCat ℤ := (relCohMVUUDual X A U V).homology (n + 1)
  let MV : ModuleCat ℤ := (relCohMVVVDual X A U V).homology (n + 1)
  let MUV : ModuleCat ℤ := (relCohMVUVDual X A U V).homology n
  let MT : ModuleCat ℤ := (relCohMVTopDual X A U V).homology (n + 1)
  -- the vanishing hypotheses, transferred to the small models
  haveI h1' : Subsingleton ↥MU := subsingleton_of_iso_symm eU h1
  haveI h2' : Subsingleton ↥MV := subsingleton_of_iso_symm eV h2
  haveI h0' : Subsingleton ↥MUV := subsingleton_of_iso_symm eUV h0
  haveI hmid : Subsingleton ↥(MU ⊞ MV) := subsingleton_biprod _ _
  -- exactness at the top term forces it to vanish
  have hM : Subsingleton ↥MT := by
    have hzero : ∀ w : ↥MT, w = 0 := by
      intro w
      have hw : (relCohMVLesSC₁ X A U V n).g.hom w = 0 := hmid.elim _ _
      obtain ⟨z, hz⟩ := (CategoryTheory.ShortComplex.moduleCat_exact_iff
        (relCohMVLesSC₁ X A U V n)).1 (relCohMVLes_exact₁ X A U V n) w hw
      calc w = (relCohMVLesSC₁ X A U V n).f.hom z := hz.symm
        _ = (relCohMVLesSC₁ X A U V n).f.hom 0 := by rw [h0'.elim z 0]
        _ = 0 := (relCohMVLesSC₁ X A U V n).f.hom.map_zero
    exact ⟨fun x y => by rw [hzero x, hzero y]⟩
  exact subsingleton_of_iso eTop hM

end

end Work.Cohomology.Endgame
