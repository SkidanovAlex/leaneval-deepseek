import Mathlib
import Submission.Work.Serre.cubePairDefs
import Submission.Work.Cohomology.relChainsMapOf_comp
import Submission.Work.Cohomology.isZero_dualComplex_empty
import Submission.Work.StemsB.CubePairHomology
import Submission.Work.Serre.cubeBdry_isZero
import Submission.Work.Serre.cubeAmbient_isZero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Serre

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## Elementary consequences for `ℤ`-modules -/

/-- The isomorphism of a morphism known to be an isomorphism (explicitly, without instance
search). -/
def isoOfIsIso {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) (h : IsIso f) : X ≅ Y :=
  ⟨f, h.out.choose, h.out.choose_spec.1, h.out.choose_spec.2⟩

/-- A surjective `ℤ`-linear endomorphism of `ℤ` is bijective. -/
theorem intLinear_bijective_of_surjective (g : ℤ →ₗ[ℤ] ℤ) (hg : Function.Surjective g) :
    Function.Bijective g := by
  have hformula : ∀ x : ℤ, g x = x * g 1 := by
    intro x
    calc g x = g (x • (1 : ℤ)) := by rw [zsmul_eq_mul, Int.cast_id, mul_one]
      _ = x • g 1 := map_zsmul g x 1
      _ = x * g 1 := by rw [zsmul_eq_mul, Int.cast_id]
  refine ⟨?_, hg⟩
  have hunit : g 1 = 1 ∨ g 1 = -1 := by
    obtain ⟨m, hm⟩ := hg 1
    rw [hformula m] at hm
    exact Int.eq_one_or_neg_one_of_mul_eq_one (u := g 1) (v := m) (by rw [mul_comm, hm])
  have hg1 : g 1 ≠ 0 := by
    rcases hunit with h | h <;> rw [h] <;> norm_num
  intro a b hab
  have hsub : (a - b) * g 1 = 0 := by
    rw [sub_mul, ← hformula a, ← hformula b, hab, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_right hg1)

/-- A surjective morphism of `ℤ`-modules between two copies of `ℤ` is an isomorphism. -/
theorem isIso_of_surjective_of_intIso {M N : ModuleCat ℤ} (eM : M ≅ ModuleCat.of ℤ ℤ)
    (eN : N ≅ ModuleCat.of ℤ ℤ) (f : M ⟶ N) (hf : Function.Surjective (ModuleCat.Hom.hom f)) :
    IsIso f := by
  haveI hfE : Epi f := (ModuleCat.epi_iff_surjective f).mpr hf
  set g : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ := eM.inv ≫ f ≫ eN.hom with hg
  haveI hEg : Epi g := by rw [hg]; infer_instance
  have hgs : Function.Surjective (ModuleCat.Hom.hom g) := (ModuleCat.epi_iff_surjective g).mp hEg
  have hbi := intLinear_bijective_of_surjective (ModuleCat.Hom.hom g) hgs
  haveI : Mono g := (ModuleCat.mono_iff_injective g).mpr hbi.1
  haveI : IsIso g := isIso_of_mono_of_epi g
  have key : eM.hom ≫ g ≫ eN.inv = f := by
    rw [hg]
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  haveI : IsIso (eM.hom ≫ g ≫ eN.inv) := inferInstance
  rwa [key] at this

/-! ## A point of the fibre from the degree-zero augmentation -/

/-- If the augmentation `H₀(X;ℤ) ⟶ ℤ` is an isomorphism then `X` is nonempty. -/
theorem nonempty_of_isIso_singularHomology₀ε {X : TopCat}
    (h : IsIso (TopCat.singularHomology₀ε X (ModuleCat.of ℤ ℤ))) : Nonempty X := by
  have hdesc : IsIso (Limits.Sigma.desc (fun _ : ZerothHomotopy X => 𝟙 (ModuleCat.of ℤ ℤ))) := by
    rw [← TopCat.singularHomology₀Iso_sigma_desc_id X (ModuleCat.of ℤ ℤ)] at h
    exact IsIso.of_isIso_comp_left ((TopCat.singularHomology₀Iso X (ModuleCat.of ℤ ℤ)).hom)
      (Limits.Sigma.desc (fun _ : ZerothHomotopy X => 𝟙 (ModuleCat.of ℤ ℤ)))
  by_contra hemp
  haveI : IsEmpty (ZerothHomotopy X) :=
    ⟨fun z => hemp (Quotient.inductionOn z (motive := fun _ => Nonempty X) (fun x => ⟨x⟩))⟩
  have hzero : IsZero (∐ (fun _ : ZerothHomotopy X => ModuleCat.of ℤ ℤ)) :=
    Work.Cohomology.isZero_coproduct_of_isEmpty _
  haveI hdescI : IsIso (Limits.Sigma.desc (fun _ : ZerothHomotopy X => 𝟙 (ModuleCat.of ℤ ℤ))) :=
    hdesc
  have hZ : IsZero (ModuleCat.of ℤ ℤ) :=
    IsZero.of_iso hzero
      (asIso (Limits.Sigma.desc (fun _ : ZerothHomotopy X => 𝟙 (ModuleCat.of ℤ ℤ)))).symm
  haveI : Subsingleton ℤ := ModuleCat.subsingleton_of_isZero hZ
  exact one_ne_zero (Subsingleton.elim (1 : ℤ) 0)

/-! ## A section of the projection over the cube -/

/-- **A Serre fibration over the cube admits a section** as soon as its total space is nonempty:
the cube is contractible, so a point can be transported along the contraction. -/
theorem exists_section_cubePullback (D : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (τ : C(Work.Stems.Cubical.IC D, B))
    (x₀ : Work.StemsB.Pullback p τ) :
    ∃ s : C(Work.Stems.Cubical.IC D, Work.StemsB.Pullback p τ),
      (Work.StemsB.pullbackSnd p τ).comp s = ContinuousMap.id _ := by
  classical
  set d₀ : Work.Stems.Cubical.IC D := Work.StemsB.pullbackSnd p τ x₀ with hd₀
  have h0 : (ContinuousMap.id (Work.Stems.Cubical.IC D)).Homotopy
      (ContinuousMap.const (Work.Stems.Cubical.IC D) d₀) :=
    { toContinuousMap :=
        ⟨fun z : unitInterval × Work.Stems.Cubical.IC D => cubeContraction D d₀ (z.2, z.1), by
          exact (cubeContraction D d₀).continuous.comp (continuous_snd.prodMk continuous_fst)⟩
      map_zero_left := fun u => cubeContraction_zero D d₀ u
      map_one_left := fun u => cubeContraction_one D d₀ u }
  have hHom : ((Work.StemsB.pullbackSnd p τ).comp
        (ContinuousMap.const (Work.Stems.Cubical.IC D) x₀)).Homotopy
      (ContinuousMap.id (Work.Stems.Cubical.IC D)) :=
    { toContinuousMap := h0.symm.toContinuousMap
      map_zero_left := fun u => h0.symm.map_zero_left u
      map_one_left := fun u => h0.symm.map_one_left u }
  obtain ⟨g, H', hH'⟩ := Work.StemsB.hasHLP_pullback p τ (hp D)
    (ContinuousMap.const _ x₀) (ContinuousMap.id _) hHom
  refine ⟨g, ?_⟩
  apply ContinuousMap.ext
  intro u
  show Work.StemsB.pullbackSnd p τ (g u) = u
  have h := congrFun (congrArg DFunLike.coe hH') (1, u)
  have h1 : H'.toContinuousMap (1, u) = g u := H'.map_one_left u
  have h2 : hHom.toContinuousMap (1, u) = u := hHom.map_one_left u
  simp only [ContinuousMap.comp_apply] at h
  rw [h1, h2] at h
  exact h

/-! ## The cube pair

The two facts about the pair `(I^D, ∂I^D)` that the proof uses. -/

/-- The top relative homology of the cube pair is `ℤ`. -/
theorem cubeBdry_top_iso (D : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of (Work.Stems.Cubical.IC D))
      (cubeBdryS D)).homology D) ≅ ModuleCat.of ℤ ℤ) := by
  haveI : PathConnectedSpace ↥(TopCat.of PUnit) := inferInstance
  have hε : IsIso (TopCat.singularHomology₀ε (TopCat.of PUnit) (ModuleCat.of ℤ ℤ)) :=
    inferInstance
  obtain ⟨e⟩ := Work.Cohomology.relChainsHomeomorphCompat (Work.Stems.Cubical.IC D)
    (Work.StemsB.CubeP PUnit D) (cubeBdryS D) (Work.StemsB.cubeBdryK PUnit D)
    { toFun := fun x => (x, ⟨⟩)
      invFun := fun y => y.1
      left_inv := fun x => rfl
      right_inv := fun y => by ext <;> simp
      continuous_toFun := continuous_id.prodMk continuous_const
      continuous_invFun := continuous_fst }
    (fun x => Iff.rfl) D
  obtain ⟨e₂⟩ := Work.StemsB.cubePair_iso D PUnit 0
  refine ⟨e ≪≫ ?_ ≪≫ isoOfIsIso (TopCat.singularHomology₀ε (TopCat.of PUnit) (ModuleCat.of ℤ ℤ)) hε⟩
  exact (eqToIso (congrArg (fun k => (Work.Cohomology.relChains
    (Work.StemsB.CubeSpace PUnit D) (Work.StemsB.cubeBdryK PUnit D)).homology k)
    (Nat.zero_add D))).symm ≪≫ e₂

/-! ## The vanishing below the dimension, for the pullback of a fibration -/

/-! ## The section map on relative chains -/

/-- The map induced by a section of the projection on the relative parts. -/
def cubeSectionPointMap (D : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC D, B))
    (s : C(Work.Stems.Cubical.IC D, Work.StemsB.Pullback p τ))
    (hs : (Work.StemsB.pullbackSnd p τ).comp s = ContinuousMap.id _) :
    C(↥(cubeBdryS D), ↥(pbPre p τ (cubeBdryS D))) :=
  ⟨fun x => ⟨s x.1, by
      have hx1 : Work.StemsB.pullbackSnd p τ (s x.1) = (x.1 : Work.Stems.Cubical.IC D) :=
        congrFun (congrArg DFunLike.coe hs) x.1
      show Work.StemsB.pullbackSnd p τ (s x.1) ∈ cubeBdryS D
      rw [hx1]
      exact x.2⟩, by
      refine Continuous.subtype_mk ?_ _
      exact s.continuous.comp continuous_subtype_val⟩

/-- The map of relative chain complexes induced by a section of the projection `τ^*E → I^D`. -/
def cubeSectionMap (D : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (τ : C(Work.Stems.Cubical.IC D, B))
    (s : C(Work.Stems.Cubical.IC D, Work.StemsB.Pullback p τ))
    (hs : (Work.StemsB.pullbackSnd p τ).comp s = ContinuousMap.id _) :
    Work.Cohomology.relChains (TopCat.of (Work.Stems.Cubical.IC D)) (cubeBdryS D) ⟶
      Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback p τ))
        (pbPre p τ (cubeBdryS D)) :=
  Work.Cohomology.relChainsMapOf (TopCat.of (Work.Stems.Cubical.IC D))
    (TopCat.of (Work.StemsB.Pullback p τ)) (cubeBdryS D) (pbPre p τ (cubeBdryS D))
    (TopCat.ofHom s) (TopCat.ofHom (cubeSectionPointMap D p τ s hs)) (by ext x; rfl)

/-- The identity form of `relChainsMapOf`. -/
theorem relChainsMapOf_id {X : TopCat} (A : Set X)
    (w : Work.Cohomology.subtypeIncl X A ≫ 𝟙 X = 𝟙 (TopCat.of A) ≫ Work.Cohomology.subtypeIncl X A) :
    Work.Cohomology.relChainsMapOf X X A A (𝟙 X) (𝟙 (TopCat.of A)) w =
      𝟙 (Work.Cohomology.relChains X A) := by
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains X A))).mp
  show cokernel.π (Work.Cohomology.inclChains X A) ≫
      Work.Cohomology.relChainsMapOf X X A A (𝟙 X) (𝟙 (TopCat.of A)) w =
    cokernel.π (Work.Cohomology.inclChains X A) ≫ 𝟙 (cokernel (Work.Cohomology.inclChains X A))
  unfold Work.Cohomology.relChainsMapOf
  rw [Work.Cohomology.cokernel_π_map]
  simp [Work.Cohomology.chainMap]

/-- The composite of the section map with the map of the pair is the identity. -/
theorem cubeSectionMap_comp (D : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC D, B))
    (s : C(Work.Stems.Cubical.IC D, Work.StemsB.Pullback p τ))
    (hs : (Work.StemsB.pullbackSnd p τ).comp s = ContinuousMap.id _) :
    cubeSectionMap D p τ s hs ≫ cubePairMap D p τ =
      𝟙 (Work.Cohomology.relChains (TopCat.of (Work.Stems.Cubical.IC D)) (cubeBdryS D)) := by
  have hπ1 : cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.Stems.Cubical.IC D))
        (cubeBdryS D)) ≫ cubeSectionMap D p τ s hs =
      Work.Cohomology.chainMap ℤ (TopCat.of (Work.Stems.Cubical.IC D))
        (TopCat.of (Work.StemsB.Pullback p τ)) (TopCat.ofHom s) ≫
      cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback p τ))
        (pbPre p τ (cubeBdryS D))) := by
    unfold cubeSectionMap Work.Cohomology.relChainsMapOf
    exact Work.Cohomology.cokernel_π_map _ _ _ _ _
  have hπ2 : cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback p τ))
        (pbPre p τ (cubeBdryS D))) ≫ cubePairMap D p τ =
      Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback p τ))
        (TopCat.of (Work.Stems.Cubical.IC D)) (TopCat.ofHom (Work.StemsB.pullbackSnd p τ)) ≫
      cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.Stems.Cubical.IC D))
        (cubeBdryS D)) := by
    unfold cubePairMap Work.Cohomology.relChainsMapOf
    exact Work.Cohomology.cokernel_π_map _ _ _ _ _
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.Stems.Cubical.IC D))
    (cubeBdryS D)))).mp
  show cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.Stems.Cubical.IC D))
        (cubeBdryS D)) ≫ (cubeSectionMap D p τ s hs ≫ cubePairMap D p τ) =
      cokernel.π (Work.Cohomology.inclChains (TopCat.of (Work.Stems.Cubical.IC D))
        (cubeBdryS D)) ≫ 𝟙 (cokernel (Work.Cohomology.inclChains (TopCat.of (Work.Stems.Cubical.IC D))
          (cubeBdryS D)))
  rw [← Category.assoc, hπ1, Category.assoc, hπ2, ← Category.assoc,
    ← Work.Cohomology.chainMap_comp_relChains, ← TopCat.ofHom_comp, hs, TopCat.ofHom_id]
  simp [Work.Cohomology.chainMap]

/-! ## The main theorem -/

/-- **(P_D)**: for a Serre fibration `p : E → B`, a map `τ : I^D → B` and a fibre which is
homologically `f`-connected over every point of the cube, the map of pairs
`(τ^*E, τ^*E|_{∂I^D}) → (I^D, ∂I^D)` induced by the fibration
(`Work.Serre.cubePairMap D p τ`) is an isomorphism on homology in degrees `< D + f`. -/
theorem cubeRelIso (D : ℕ) :
    ∀ (E : Type) [TopologicalSpace E] (B : Type) [TopologicalSpace B] (p : C(E, B))
      (hp : Work.StemsB.IsSerreFibration p) (τ : C(Work.Stems.Cubical.IC D, B)) (f : ℕ),
      (∀ y : Work.Stems.Cubical.IC D, ∀ j : ℕ, 0 < j → j < f →
        IsZero ((Work.Cohomology.singularChains ℤ
          (TopCat.of (Work.StemsB.fibre p (τ y)))).homology j)) →
      (∀ y : Work.Stems.Cubical.IC D,
        IsIso (TopCat.singularHomology₀ε
          (TopCat.of (Work.StemsB.fibre p (τ y))) (ModuleCat.of ℤ ℤ))) →
      ∀ i : ℕ, i < D + f →
        IsIso (HomologicalComplex.homologyMap (Work.Serre.cubePairMap D p τ) i) := by
  intro E _ B _ p hp τ f h1 h2 i hi
  classical
  rcases eq_or_ne i D with hD | hne
  · -- the top degree: the projection splits and both sides are `ℤ`
    rw [hD]
    have hne' : Nonempty (Work.StemsB.fibre p (τ (fun _ => 0))) :=
      nonempty_of_isIso_singularHomology₀ε (h2 (fun _ => 0))
    obtain ⟨e₀⟩ := hne'
    obtain ⟨s, hs⟩ := exists_section_cubePullback D p hp τ
      (⟨(e₀.1, fun _ => 0), e₀.2⟩ : Work.StemsB.Pullback p τ)
    have hsurj : Function.Surjective (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (cubePairMap D p τ) D)) := by
      intro y
      refine ⟨(ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (cubeSectionMap D p τ s hs) D)) y, ?_⟩
      have hcomp : HomologicalComplex.homologyMap (cubeSectionMap D p τ s hs) D ≫
          HomologicalComplex.homologyMap (cubePairMap D p τ) D = 𝟙 _ := by
        rw [← HomologicalComplex.homologyMap_comp (cubeSectionMap D p τ s hs)
          (cubePairMap D p τ) D, cubeSectionMap_comp, HomologicalComplex.homologyMap_id]
      have h := congrArg (fun φ => ModuleCat.Hom.hom φ y) hcomp
      simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
        LinearMap.id_apply] at h
      exact h
    obtain ⟨eM⟩ := serreE2d E B p D hp τ (fun _ => 0) 0
    have hM : ((Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback p τ))
        (pbPre p τ (cubeBdryS D))).homology D) ≅ ModuleCat.of ℤ ℤ :=
      (eqToIso (congrArg (fun k => (Work.Cohomology.relChains
        (TopCat.of (Work.StemsB.Pullback p τ)) (pbPre p τ (cubeBdryS D))).homology k)
        (Nat.zero_add D))).symm ≪≫ eM ≪≫ isoOfIsIso _ (h2 (fun _ => 0))
    obtain ⟨eN⟩ := cubeBdry_top_iso D
    exact isIso_of_surjective_of_intIso hM eN _ hsurj
  · -- away from the top degree both sides vanish
    have hN : IsZero ((Work.Cohomology.relChains (TopCat.of (Work.Stems.Cubical.IC D))
        (cubeBdryS D)).homology i) := cubeBdry_isZero D i hne
    have hM : IsZero ((Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback p τ))
        (pbPre p τ (cubeBdryS D))).homology i) := by
      by_cases hlt : i < D
      · exact cubeAmbient_isZero D E B p hp τ i hlt
      · have hDle : D ≤ i := Nat.le_of_not_lt hlt
        have hDlt : D < i := lt_of_le_of_ne hDle (Ne.symm hne)
        have hpos : 0 < i - D := Nat.sub_pos_of_lt hDlt
        have hltf : i - D < f := by omega
        obtain ⟨e⟩ := serreE2d E B p D hp τ (fun _ => 0) (i - D)
        exact IsZero.of_iso (h1 (fun _ => 0) (i - D) hpos hltf)
          ((eqToIso (congrArg (fun k => (Work.Cohomology.relChains
            (TopCat.of (Work.StemsB.Pullback p τ)) (pbPre p τ (cubeBdryS D))).homology k)
            (Nat.sub_add_cancel hDle))).symm ≪≫ e)
    exact Work.StemsB.isIso_of_isZero_of_isZero hM hN

end

end Work.Serre
