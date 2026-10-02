import Mathlib
import Submission.Work.CharacteristicClasses.Degree
import Submission.Work.Cohomology.Compat.homology_prod_sphere
import Submission.Work.Cohomology.Compat.prodSphereAux
import Submission.Work.Cohomology.Compat.prodSphereDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Hopf formula: the degree of a pointwise product

This file proves `Work.CharacteristicClasses.chern2_mul`, the additivity of the degree of a
self-map of `S³ = Sp(1)` under the pointwise product `(f, g) ↦ fun q => f q * g q`.

The proof is the standard H-space argument, expressed in the language of singular homology:

* `p1`, `p2 : S³ × S³ ⟶ S³` are the two projections, `i1 x = (x,1)`, `i2 x = (1,x)` the two
  sections, `m3 (x,y) = x * y` the multiplication and `diag x = (x,x)` the diagonal;
* `hmap f` is the map induced by `f` on `H₃(-;ℤ)`;
* `Phi = (p1_*, p2_*) : H₃(S³ × S³) ⟶ H₃(S³) ⊕ H₃(S³)` is injective.  It is *surjective*
  because of the two sections, and a surjective endomorphism of the free module `ℤ²` is injective
  (`Module.End.injective_of_surjective`, transported along the isomorphism
  `H₃(S³ × S³) ≅ ℤ²` coming from `Work.Cohomology.Compat.homology_prod_sphere 3 3 3`).
* consequently `diag_* z = (i1)_* z + (i2)_* z`, and `(f × g)_*` acts diagonally on these two
  classes with eigenvalues `chern2 f` and `chern2 g`;
* finally `m3 ∘ (f × g) ∘ diag = fun q => f q * g q`, and `m3 ∘ i1 = m3 ∘ i2 = id`, so the
  degree of the product is the sum of the degrees.

Everything here lives in the "compatible world": the only product-of-spheres input used is
`Work.Cohomology.Compat.homology_prod_sphere`, so the result can be imported from the endgame
chapter `SignatureBordism`.
-/

set_option maxHeartbeats 1000000

namespace Work.CharacteristicClasses

open CategoryTheory Limits
open scoped Topology

noncomputable section

/-! ## 1. The induced map on the third homology -/

/-- The quaternionic `S³ = Sp(1)` as a topological space. -/
private abbrev cmXt : TopCat := TopCat.of S3

/-- `S³ × S³`. -/
private abbrev cmPt : TopCat := TopCat.of (S3 × S3)

/-- The third singular homology of `A` with `ℤ`-coefficients. -/
private abbrev cmH3 (A : TopCat) : ModuleCat ℤ := (Work.Cohomology.singularChains ℤ A).homology 3

/-- The map induced by a continuous map on the third singular homology. -/
private def cmHmap {A B : TopCat} (f : A ⟶ B) : cmH3 A ⟶ cmH3 B :=
  HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ A B f) 3

private lemma cmHmap_id (A : TopCat) : cmHmap (𝟙 A) = 𝟙 (cmH3 A) := by
  unfold cmHmap
  rw [Work.Cohomology.chainMap, CategoryTheory.Functor.map_id,
    HomologicalComplex.homologyMap_id]

private lemma cmHmap_comp {A B C : TopCat} (f : A ⟶ B) (g : B ⟶ C) :
    cmHmap (f ≫ g) = cmHmap f ≫ cmHmap g := by
  unfold cmHmap
  rw [← Work.Cohomology.Compat.chainMap_comp', HomologicalComplex.homologyMap_comp]

/-! Elementary rewriting rules for morphisms of `ℤ`-modules and for the homology of `ℤ²`. -/

private lemma cmMapAdd {M N : ModuleCat ℤ} (f : M ⟶ N) (a b : M) :
    f (a + b) = f a + f b :=
  map_add (ConcreteCategory.hom f) a b

private lemma cmMapZsmul {M N : ModuleCat ℤ} (f : M ⟶ N) (k : ℤ) (a : M) :
    f (k • a) = k • f a :=
  map_zsmul (ConcreteCategory.hom f) k a

/-- The first component of a `biprod.lift`. -/
private lemma cmFstLiftApply {M N P : ModuleCat ℤ} (f : M ⟶ N) (g : M ⟶ P) (x : M) :
    (ConcreteCategory.hom (biprod.fst : N ⊞ P ⟶ N)) ((biprod.lift f g) x) = f x := by
  have h := congrArg (fun (k : M ⟶ N) => k.hom x) (biprod.lift_fst f g)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- The second component of a `biprod.lift`. -/
private lemma cmSndLiftApply {M N P : ModuleCat ℤ} (f : M ⟶ N) (g : M ⟶ P) (x : M) :
    (ConcreteCategory.hom (biprod.snd : N ⊞ P ⟶ P)) ((biprod.lift f g) x) = g x := by
  have h := congrArg (fun (k : M ⟶ P) => k.hom x) (biprod.lift_snd f g)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- The inverse of a module isomorphism cancels its direct map. -/
private lemma cmIso_inv_apply {M N : ModuleCat ℤ} (e : M ≅ N) (x : M) :
    ModuleCat.Hom.hom e.inv (ModuleCat.Hom.hom e.hom x) = x := by
  have h := congrArg ModuleCat.Hom.hom e.hom_inv_id
  rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
  exact LinearMap.congr_fun h x

/-- The direct map of a module isomorphism cancels its inverse. -/
private lemma cmIso_hom_inv_apply {M N : ModuleCat ℤ} (e : M ≅ N) (y : N) :
    ModuleCat.Hom.hom e.hom (ModuleCat.Hom.hom e.inv y) = y := by
  have h := congrArg ModuleCat.Hom.hom e.inv_hom_id
  rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
  exact LinearMap.congr_fun h y

/-- **A surjective map `M ⟶ N` of `ℤ`-modules which are both isomorphic to `ℤⁿ` is injective.**
The conjugate of `f` is a surjective endomorphism of `ℤⁿ`, and those are injective
(`Module.End.injective_of_surjective`, `Module.Finite`/`Module.Free`/`IsStablyFiniteRing ℤ`). -/
private lemma cmInjectiveOfSurjectiveOfIso {M N : ModuleCat ℤ} {n : ℕ}
    (eM : M ≅ ModuleCat.of ℤ (Fin n → ℤ)) (eN : N ≅ ModuleCat.of ℤ (Fin n → ℤ))
    (f : M ⟶ N) (h : Function.Surjective (ModuleCat.Hom.hom f)) :
    Function.Injective (ModuleCat.Hom.hom f) := by
  let G : Module.End ℤ (Fin n → ℤ) :=
    (ModuleCat.Hom.hom eN.hom).comp ((ModuleCat.Hom.hom f).comp (ModuleCat.Hom.hom eM.inv))
  have hsurj_inv : Function.Surjective (ModuleCat.Hom.hom eM.inv) :=
    (ModuleCat.epi_iff_surjective eM.inv).mp inferInstance
  have hsurj_G : Function.Surjective G := by
    rintro z
    obtain ⟨w, hw⟩ := h ((ModuleCat.Hom.hom eN.inv) z)
    refine ⟨(ModuleCat.Hom.hom eM.hom) w, ?_⟩
    show (ModuleCat.Hom.hom eN.hom)
      (ModuleCat.Hom.hom f (ModuleCat.Hom.hom eM.inv (ModuleCat.Hom.hom eM.hom w))) = z
    rw [cmIso_inv_apply eM w, hw, cmIso_hom_inv_apply eN z]
  have hinj_G : Function.Injective G :=
    Module.End.injective_of_surjective ℤ (Fin n → ℤ) hsurj_G
  have hinj_eM : Function.Injective (ModuleCat.Hom.hom eM.hom) :=
    (ModuleCat.mono_iff_injective eM.hom).mp inferInstance
  intro x y hxy
  refine hinj_eM (hinj_G ?_)
  show G (ModuleCat.Hom.hom eM.hom x) = G (ModuleCat.Hom.hom eM.hom y)
  show (ModuleCat.Hom.hom eN.hom)
      (ModuleCat.Hom.hom f (ModuleCat.Hom.hom eM.inv (ModuleCat.Hom.hom eM.hom x)))
    = (ModuleCat.Hom.hom eN.hom)
      (ModuleCat.Hom.hom f (ModuleCat.Hom.hom eM.inv (ModuleCat.Hom.hom eM.hom y)))
  rw [cmIso_inv_apply eM x, cmIso_inv_apply eM y, hxy]

/-! ## 2. The concrete maps on `S³` and `S³ × S³` -/

/-- First projection `S³ × S³ ⟶ S³`. -/
private def cmP1 : cmPt ⟶ cmXt := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- Second projection `S³ × S³ ⟶ S³`. -/
private def cmP2 : cmPt ⟶ cmXt := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

/-- The section `x ↦ (x, 1)`. -/
private def cmI1 : cmXt ⟶ cmPt :=
  TopCat.ofHom ⟨fun x => (x, s3One), continuous_id.prodMk continuous_const⟩

/-- The section `x ↦ (1, x)`. -/
private def cmI2 : cmXt ⟶ cmPt :=
  TopCat.ofHom ⟨fun x => (s3One, x), continuous_const.prodMk continuous_id⟩

/-- Quaternion multiplication `S³ × S³ ⟶ S³`. -/
private def cmM : cmPt ⟶ cmXt := TopCat.ofHom ⟨fun p => s3Mul p.1 p.2, continuous_s3Mul⟩

/-- The diagonal `x ↦ (x, x)`. -/
private def cmDiag : cmXt ⟶ cmPt :=
  TopCat.ofHom ⟨fun x => (x, x), continuous_id.prodMk continuous_id⟩

/-- The map `(x, y) ↦ (f x, g y)`. -/
private def cmProdCm (f g : C(S3, S3)) : cmPt ⟶ cmPt := TopCat.ofHom (f.prodMap g)

private lemma cmP1_apply (z : S3 × S3) : TopCat.Hom.hom cmP1 z = z.1 := rfl
private lemma cmP2_apply (z : S3 × S3) : TopCat.Hom.hom cmP2 z = z.2 := rfl
private lemma cmI1_apply (x : S3) : TopCat.Hom.hom cmI1 x = (x, s3One) := rfl
private lemma cmI2_apply (x : S3) : TopCat.Hom.hom cmI2 x = (s3One, x) := rfl
private lemma cmM_apply (z : S3 × S3) : TopCat.Hom.hom cmM z = s3Mul z.1 z.2 := rfl
private lemma cmDiag_apply (x : S3) : TopCat.Hom.hom cmDiag x = (x, x) := rfl
private lemma cmProdCm_apply (f g : C(S3, S3)) (z : S3 × S3) :
    TopCat.Hom.hom (cmProdCm f g) z = (f z.1, g z.2) := rfl

private lemma cmI1_comp_cmP1 : cmI1 ≫ cmP1 = 𝟙 cmXt := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  show TopCat.Hom.hom cmP1 (TopCat.Hom.hom cmI1 x) = x
  rfl

private lemma cmI1_comp_cmP2 : cmI1 ≫ cmP2 = TopCat.ofHom (ContinuousMap.const cmXt s3One) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  show TopCat.Hom.hom cmP2 (TopCat.Hom.hom cmI1 x) = s3One
  rfl

private lemma cmI2_comp_cmP2 : cmI2 ≫ cmP2 = 𝟙 cmXt := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  show TopCat.Hom.hom cmP2 (TopCat.Hom.hom cmI2 x) = x
  rfl

private lemma cmI2_comp_cmP1 : cmI2 ≫ cmP1 = TopCat.ofHom (ContinuousMap.const cmXt s3One) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  show TopCat.Hom.hom cmP1 (TopCat.Hom.hom cmI2 x) = s3One
  rfl

private lemma cmDiag_comp_cmP1 : cmDiag ≫ cmP1 = 𝟙 cmXt := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  show TopCat.Hom.hom cmP1 (TopCat.Hom.hom cmDiag x) = x
  rfl

private lemma cmDiag_comp_cmP2 : cmDiag ≫ cmP2 = 𝟙 cmXt := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  show TopCat.Hom.hom cmP2 (TopCat.Hom.hom cmDiag x) = x
  rfl

private lemma cmI1_comp_cmM : cmI1 ≫ cmM = 𝟙 cmXt := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  show TopCat.Hom.hom cmM (TopCat.Hom.hom cmI1 x) = x
  simp [cmM, cmI1]

private lemma cmI2_comp_cmM : cmI2 ≫ cmM = 𝟙 cmXt := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  show TopCat.Hom.hom cmM (TopCat.Hom.hom cmI2 x) = x
  simp [cmM, cmI2]

private lemma cmProdCm_comp_cmP1 (f g : C(S3, S3)) :
    cmProdCm f g ≫ cmP1 = cmP1 ≫ TopCat.ofHom f := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  show TopCat.Hom.hom cmP1 (TopCat.Hom.hom (cmProdCm f g) z)
    = TopCat.Hom.hom (TopCat.ofHom f) (TopCat.Hom.hom cmP1 z)
  rfl

private lemma cmProdCm_comp_cmP2 (f g : C(S3, S3)) :
    cmProdCm f g ≫ cmP2 = cmP2 ≫ TopCat.ofHom g := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  show TopCat.Hom.hom cmP2 (TopCat.Hom.hom (cmProdCm f g) z)
    = TopCat.Hom.hom (TopCat.ofHom g) (TopCat.Hom.hom cmP2 z)
  rfl

/-- The multiplication composed with the diagonal and `(f × g)` is the pointwise product. -/
private lemma cmOfHom_s3MulCm (f g : C(S3, S3)) :
    TopCat.ofHom (s3MulCm f g) = cmDiag ≫ cmProdCm f g ≫ cmM := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  show TopCat.Hom.hom (TopCat.ofHom (s3MulCm f g)) z
    = TopCat.Hom.hom cmM (TopCat.Hom.hom (cmProdCm f g) (TopCat.Hom.hom cmDiag z))
  rfl

/-! ## 3. Elementary computation rules for `cmHmap` -/

/-- The constant map induces zero on `H₃`. -/
private lemma cmHmap_const (y : S3) :
    cmHmap (TopCat.ofHom (ContinuousMap.const cmXt y)) = 0 := by
  simpa only [cmHmap] using
    Work.Cohomology.Compat.homologyMap_const_eq_zero (X := cmXt) (Y := cmXt) y 3 (by norm_num)

private lemma cmHmap_p1_i1 (x : cmH3 cmXt) : cmHmap cmP1 (cmHmap cmI1 x) = x := by
  rw [← ConcreteCategory.comp_apply, ← cmHmap_comp, cmI1_comp_cmP1, cmHmap_id]
  simp

private lemma cmHmap_p2_i1 (x : cmH3 cmXt) : cmHmap cmP2 (cmHmap cmI1 x) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← cmHmap_comp, cmI1_comp_cmP2, cmHmap_const]
  simp

private lemma cmHmap_p2_i2 (x : cmH3 cmXt) : cmHmap cmP2 (cmHmap cmI2 x) = x := by
  rw [← ConcreteCategory.comp_apply, ← cmHmap_comp, cmI2_comp_cmP2, cmHmap_id]
  simp

private lemma cmHmap_p1_i2 (x : cmH3 cmXt) : cmHmap cmP1 (cmHmap cmI2 x) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← cmHmap_comp, cmI2_comp_cmP1, cmHmap_const]
  simp

private lemma cmHmap_p1_diag (x : cmH3 cmXt) : cmHmap cmP1 (cmHmap cmDiag x) = x := by
  rw [← ConcreteCategory.comp_apply, ← cmHmap_comp, cmDiag_comp_cmP1, cmHmap_id]
  simp

private lemma cmHmap_p2_diag (x : cmH3 cmXt) : cmHmap cmP2 (cmHmap cmDiag x) = x := by
  rw [← ConcreteCategory.comp_apply, ← cmHmap_comp, cmDiag_comp_cmP2, cmHmap_id]
  simp

private lemma cmHmap_m_i1 (x : cmH3 cmXt) : cmHmap cmM (cmHmap cmI1 x) = x := by
  rw [← ConcreteCategory.comp_apply, ← cmHmap_comp, cmI1_comp_cmM, cmHmap_id]
  simp

private lemma cmHmap_m_i2 (x : cmH3 cmXt) : cmHmap cmM (cmHmap cmI2 x) = x := by
  rw [← ConcreteCategory.comp_apply, ← cmHmap_comp, cmI2_comp_cmM, cmHmap_id]
  simp

/-- `(f × g)` intertwines the first projection with `f`. -/
private lemma cmHmap_p1_prodCm (f g : C(S3, S3)) (w : cmH3 cmPt) :
    cmHmap cmP1 (cmHmap (cmProdCm f g) w) = cmHmap (TopCat.ofHom f) (cmHmap cmP1 w) := by
  rw [← ConcreteCategory.comp_apply, ← cmHmap_comp, cmProdCm_comp_cmP1, cmHmap_comp,
    ConcreteCategory.comp_apply]

/-- `(f × g)` intertwines the second projection with `g`. -/
private lemma cmHmap_p2_prodCm (f g : C(S3, S3)) (w : cmH3 cmPt) :
    cmHmap cmP2 (cmHmap (cmProdCm f g) w) = cmHmap (TopCat.ofHom g) (cmHmap cmP2 w) := by
  rw [← ConcreteCategory.comp_apply, ← cmHmap_comp, cmProdCm_comp_cmP2, cmHmap_comp,
    ConcreteCategory.comp_apply]

/-! ## 4. The pair of the projections on `H₃(S³ × S³)` -/

/-- The pair of the two projections as a morphism of `ℤ`-modules. -/
private abbrev cmPhi : cmH3 cmPt ⟶ (cmH3 cmXt ⊞ cmH3 cmXt) :=
  biprod.lift (cmHmap cmP1) (cmHmap cmP2)

/-- `cmPhi` is surjective, using the two sections `i₁ x = (x,1)` and `i₂ x = (1,x)`. -/
private lemma cmPhi_surjective : Function.Surjective (ModuleCat.Hom.hom cmPhi) := by
  intro y
  refine ⟨cmHmap cmI1
      ((ConcreteCategory.hom (biprod.fst : cmH3 cmXt ⊞ cmH3 cmXt ⟶ cmH3 cmXt)) y)
    + cmHmap cmI2
      ((ConcreteCategory.hom (biprod.snd : cmH3 cmXt ⊞ cmH3 cmXt ⟶ cmH3 cmXt)) y), ?_⟩
  show (ConcreteCategory.hom (biprod.lift (cmHmap cmP1) (cmHmap cmP2)))
      (cmHmap cmI1 ((ConcreteCategory.hom (biprod.fst : cmH3 cmXt ⊞ cmH3 cmXt ⟶ cmH3 cmXt)) y)
        + cmHmap cmI2
            ((ConcreteCategory.hom (biprod.snd : cmH3 cmXt ⊞ cmH3 cmXt ⟶ cmH3 cmXt)) y)) = y
  refine Work.Cohomology.biprod_ext_apply ?_ ?_
  · simp only [cmFstLiftApply, cmMapAdd, cmHmap_p1_i1, cmHmap_p1_i2, add_zero]
  · simp only [cmSndLiftApply, cmMapAdd, cmHmap_p2_i1, cmHmap_p2_i2, zero_add]

/-- `H₃(S³ × S³) ≅ ℤ²`, transported from the Euclidean model along the quaternionic
homeomorphism. -/
private lemma expo_three_three_three : Work.Cohomology.Compat.expo 3 3 3 = 2 := by
  simp [Work.Cohomology.Compat.expo]

private noncomputable def cmEProd : cmH3 cmPt ≅ ModuleCat.of ℤ (Fin 2 → ℤ) :=
  (Work.Cohomology.homologyIso_of_homotopyEquiv
      (s3Homeo.prodCongr s3Homeo).toHomotopyEquiv 3).some
    ≪≫ (Work.Cohomology.Compat.homology_prod_sphere 3 3 3 (by norm_num) (by norm_num)).some
    ≪≫ LinearEquiv.toModuleIso
      (LinearEquiv.funCongrLeft ℤ ℤ (finCongr expo_three_three_three)).symm

/-- `H₃(S³) ≅ ℤ ≅ ℤ¹`. -/
private noncomputable def cmEOne : cmH3 cmXt ≅ ModuleCat.of ℤ (Fin 1 → ℤ) :=
  s3HomologyIso ≪≫ (Work.Cohomology.Compat.nonempty_int_fin_one).some

/-- `H₃(S³) ⊞ H₃(S³) ≅ ℤ²`. -/
private noncomputable def cmEProd2 :
    (cmH3 cmXt ⊞ cmH3 cmXt) ≅ ModuleCat.of ℤ (Fin 2 → ℤ) :=
  biprod.mapIso cmEOne cmEOne ≪≫
    (Work.Cohomology.Compat.nonempty_finArrow_biprod 1 1).some

/-- **The pair of the two projections of `S³ × S³` is injective on `H₃`.** -/
private lemma cmPhi_injective : Function.Injective (ModuleCat.Hom.hom cmPhi) :=
  cmInjectiveOfSurjectiveOfIso cmEProd cmEProd2 cmPhi cmPhi_surjective

/-! ## 5. The degree as the eigenvalue on the generator -/

/-- An element of `H₃(S³)` whose image under the chosen isomorphism `H₃(S³) ≅ ℤ` is `k` equals
`k • s3HomologyGen`. -/
private lemma cmEqSmulGenOfHomEq {u : cmH3 cmXt} {k : ℤ}
    (h : ModuleCat.Hom.hom s3HomologyIso.hom u = k) : u = k • s3HomologyGen := by
  have h1 : ModuleCat.Hom.hom s3HomologyIso.inv (ModuleCat.Hom.hom s3HomologyIso.hom u) = u :=
    cmIso_inv_apply s3HomologyIso u
  rw [← h1, h]
  rw [show s3HomologyGen = ModuleCat.Hom.hom s3HomologyIso.inv (1 : ℤ) from rfl, ← map_zsmul]
  congr 1
  simp

/-- The degree is the eigenvalue of `f_*` on the chosen generator of `H₃(S³)`. -/
private lemma cmHmapOfHom (f : C(S3, S3)) :
    cmHmap (TopCat.ofHom f) s3HomologyGen = chern2 f • s3HomologyGen :=
  cmEqSmulGenOfHomEq (u := cmHmap (TopCat.ofHom f) s3HomologyGen) rfl

/-! ## 6. The Hopf formula -/

/-- **The Hopf formula: degrees are additive under the pointwise product.**  For continuous maps
`f g : S³ → S³` one has `deg (q ↦ f q * g q) = deg f + deg g` on `S³ = Sp(1)`.  This is the
additivity `c₂(V ⊗ W) = c₂V + c₂W` for `SU(2)`-bundles over `S⁴`, i.e. the input that makes the
first Pontryagin class additive under Whitney sums.

**Compatibility requirement (important).**  The proof must live in the "compatible world": it may
import only `Submission.Work.CharacteristicClasses.Degree`,
`Submission.Work.Cohomology.Compat.homology_prod_sphere`, `…Compat.prodSphereAux`,
`…Compat.prodSphereDefs`, `…Compat.proj_pair_injective` (and clean modules such as
`…Cohomology.sphereHomologyTop`).  It must **not** import `Submission.Work.Cohomology.prodSphereAux`,
`…homology_prod_sphere`, `…proj_pair_injective`, `…pjPairInjectiveThree` or
`…isIso_mvRightX_YV_low`: those clash with the endgame chapter (`SignatureBordism`), where this
result has to be usable.

Proof route (H-space argument, all clean).
1. `e : H₃(S3 × S3) ≅ (Fin 2 → ℤ)`: transport `Work.Cohomology.Compat.homology_prod_sphere 3 3 3`
   along `Homeomorph.prodCongr` of `Work.CharacteristicClasses.s3Homeo` (and
   `Work.Cohomology.sphereSet_eq'`) with `Work.Cohomology.homologyIso_of_homotopyEquiv`.
2. Let `Φ` be the pair of the homology maps of the two projections `p₁ p₂ : S3 × S3 → S3`.
   `Φ` is *surjective*: for the sections `i₁ x = (x, s3One)`, `i₂ x = (s3One, x)` one has
   `p₁ ∘ i₁ = 𝟙`, `p₂ ∘ i₁ = const s3One` — whose homology map is `0` by
   `Work.Cohomology.Compat.homologyMap_const_eq_zero` — so `Φ ((i₁)_* x) = (x, 0)`, and dually
   `Φ ((i₂)_* y) = (0, y)`; hence `(x,y) = Φ ((i₁)_* x + (i₂)_* y)`.
3. `Φ` is then injective: via `e` and `H₃(S3) ≅ ℤ` (`sphereHomologyTop 3`) it becomes a `2 × 2`
   integer matrix `A` with `A.mulVec` surjective; a right inverse `B` (`A * B = 1`) gives
   `det A * det B = 1`, so `det A = ±1`, and `Matrix.adjugate_mul` gives injectivity of `A.mulVec`.
   (If `Work.CharacteristicClasses.proj_pair_injective_product_three` is available — delegated in
   parallel with the same recipe — it supplies the same statement in the Euclidean model and can be
   transported instead.)
4. H-space computation: with `m` the quaternion multiplication and `Δ` the diagonal,
   `s3MulCm f g = m ∘ (f × g) ∘ Δ`; `Φ (Δ_* z) = (z, z)` and `Φ ((f × g)_* z) =
   (chern2 f • z, chern2 g • z)` for `z = s3HomologyGen`; `m_* ((i₁)_* z) = m_* ((i₂)_* z) = z`
   (because `m ∘ i₁ = 𝟙 = m ∘ i₂`); hence `(s3MulCm f g)_* z = (chern2 f + chern2 g) • z`, and
   `s3HomologyIso` is injective, which gives the claim.
All the ingredients above are in the *compatible* world; the projection-injectivity step can also
be transported from `Work.CharacteristicClasses.proj_pair_injective_product_three`
(`Submission/Work/CharacteristicClasses/proj_pair_injective_product_three.lean`). -/
theorem chern2_mul (f g : ContinuousMap Work.CharacteristicClasses.S3 Work.CharacteristicClasses.S3) :
    Work.CharacteristicClasses.chern2 (Work.CharacteristicClasses.s3MulCm f g) =
      Work.CharacteristicClasses.chern2 f + Work.CharacteristicClasses.chern2 g := by
  set z := s3HomologyGen with hz
  have hgen : ModuleCat.Hom.hom s3HomologyIso.hom z = 1 := by
    rw [hz]
    have h := congrArg ModuleCat.Hom.hom s3HomologyIso.inv_hom_id
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact LinearMap.congr_fun h (1 : ℤ)
  have hA : cmHmap cmDiag z = cmHmap cmI1 z + cmHmap cmI2 z := by
    apply cmPhi_injective
    rw [cmMapAdd]
    refine Work.Cohomology.biprod_ext_apply ?_ ?_
    · rw [cmMapAdd, cmFstLiftApply, cmFstLiftApply, cmFstLiftApply,
        cmHmap_p1_diag, cmHmap_p1_i1, cmHmap_p1_i2, add_zero]
    · rw [cmMapAdd, cmSndLiftApply, cmSndLiftApply, cmSndLiftApply,
        cmHmap_p2_diag, cmHmap_p2_i1, cmHmap_p2_i2, zero_add]
  have hC : cmHmap (cmProdCm f g) (cmHmap cmDiag z) =
      chern2 f • cmHmap cmI1 z + chern2 g • cmHmap cmI2 z := by
    apply cmPhi_injective
    rw [cmMapAdd, cmMapZsmul, cmMapZsmul]
    refine Work.Cohomology.biprod_ext_apply ?_ ?_
    · rw [cmFstLiftApply, cmMapAdd, cmMapZsmul, cmMapZsmul,
        cmFstLiftApply, cmFstLiftApply,
        cmHmap_p1_prodCm, cmHmap_p1_diag, cmHmapOfHom, cmHmap_p1_i1, cmHmap_p1_i2]
      simp only [zsmul_zero, add_zero, hz]
    · rw [cmSndLiftApply, cmMapAdd, cmMapZsmul, cmMapZsmul,
        cmSndLiftApply, cmSndLiftApply,
        cmHmap_p2_prodCm, cmHmap_p2_diag, cmHmapOfHom, cmHmap_p2_i1, cmHmap_p2_i2]
      simp only [zsmul_zero, zero_add, hz]
  have hmain : cmHmap (TopCat.ofHom (s3MulCm f g)) z = (chern2 f + chern2 g) • z := by
    have hmor : cmHmap (TopCat.ofHom (s3MulCm f g))
        = cmHmap cmDiag ≫ cmHmap (cmProdCm f g) ≫ cmHmap cmM := by
      rw [cmOfHom_s3MulCm, cmHmap_comp, cmHmap_comp]
    rw [hmor, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hC, cmMapAdd,
      cmMapZsmul, cmMapZsmul, cmHmap_m_i1, cmHmap_m_i2, add_zsmul]
  rw [show chern2 (s3MulCm f g) = ModuleCat.Hom.hom s3HomologyIso.hom
      (cmHmap (TopCat.ofHom (s3MulCm f g)) z) from by rw [hz]; rfl]
  rw [hmain, map_zsmul, hgen]
  simp

end

end Work.CharacteristicClasses
