import Mathlib
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.SphDefs
import Submission.Work.Cohomology.homotopyInvariance
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.mv_shortExact
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.mv_shortExact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Auxiliary algebra and topology for the homology of a product of spheres
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Limits
open scoped Topology

namespace Work.Cohomology.Compat

noncomputable section

section BiprodAux

variable {A B T : ModuleCat ℤ}

/-- A morphism out of a binary biproduct is the sum of its composites with `inl` and `inr`. -/
lemma biprod_desc_inl_inr (f : A ⊞ B ⟶ T) :
    biprod.desc (biprod.inl ≫ f) (biprod.inr ≫ f) = f := by
  rw [biprod.desc_eq, ← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, biprod.total,
    Category.id_comp]

/-- Two morphisms out of a binary biproduct which agree after precomposition with `inl` and with
`inr` are equal. -/
lemma biprod_ext_out (f g : A ⊞ B ⟶ T) (h1 : biprod.inl ≫ f = biprod.inl ≫ g)
    (h2 : biprod.inr ≫ f = biprod.inr ≫ g) : f = g := by
  rw [← biprod_desc_inl_inr f, ← biprod_desc_inl_inr g, h1, h2]

end BiprodAux

section BiprodBlock

variable {A B C D : ModuleCat ℤ}

/-- The block matrix `(a, b) ↦ (g a, f b)` as a morphism of biproducts. -/
def biprodBlock (g : A ⟶ C) (f : B ⟶ D) : A ⊞ B ⟶ C ⊞ D :=
  biprod.desc (g ≫ biprod.inl) (f ≫ biprod.inr)

@[simp]
lemma biprodBlock_inl (g : A ⟶ C) (f : B ⟶ D) :
    biprod.inl ≫ biprodBlock g f = g ≫ biprod.inl := biprod.inl_desc _ _

@[simp]
lemma biprodBlock_inr (g : A ⟶ C) (f : B ⟶ D) :
    biprod.inr ≫ biprodBlock g f = f ≫ biprod.inr := biprod.inr_desc _ _

/-- The block matrix `(a, b) ↦ (g a, f b)` is an isomorphism when `f` and `g` are. -/
lemma isIso_biprodBlock {g : A ⟶ C} {f : B ⟶ D} [IsIso g] [IsIso f] :
    IsIso (biprodBlock g f) := by
  refine ⟨biprodBlock (inv g) (inv f), ?_, ?_⟩
  · apply biprod_ext_out
    · rw [← Category.assoc, biprodBlock_inl, Category.assoc, biprodBlock_inl]
      simp
    · rw [← Category.assoc, biprodBlock_inr, Category.assoc, biprodBlock_inr]
      simp
  · apply biprod_ext_out
    · rw [← Category.assoc, biprodBlock_inl, Category.assoc, biprodBlock_inl]
      simp
    · rw [← Category.assoc, biprodBlock_inr, Category.assoc, biprodBlock_inr]
      simp

end BiprodBlock

/-! ## 2. The homology of a biproduct of chain complexes -/

section HomologyBiprod

variable {C D : ChainComplex (ModuleCat ℤ) ℕ}

/-- The homology version of the biproduct identity: on the homology of a biproduct of chain
complexes, `fst ≫ inl + snd ≫ inr = 𝟙`. -/
lemma homologyMap_total' (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    HomologicalComplex.homologyMap (biprod.fst (X := C) (Y := D)) n
        ≫ HomologicalComplex.homologyMap (biprod.inl (X := C) (Y := D)) n
      + HomologicalComplex.homologyMap (biprod.snd (X := C) (Y := D)) n
        ≫ HomologicalComplex.homologyMap (biprod.inr (X := C) (Y := D)) n
    = 𝟙 ((C ⊞ D).homology n) := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_add, biprod.total, HomologicalComplex.homologyMap_id]

/-- The map `(C ⊞ D).homology n → C.homology n ⊞ D.homology n` given by the two projections is an
isomorphism. -/
theorem isIso_homologyMap_lift (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    IsIso (biprod.lift (HomologicalComplex.homologyMap (biprod.fst (X := C) (Y := D)) n)
      (HomologicalComplex.homologyMap (biprod.snd (X := C) (Y := D)) n)) := by
  set α := HomologicalComplex.homologyMap (biprod.fst (X := C) (Y := D)) n with hα
  set β := HomologicalComplex.homologyMap (biprod.snd (X := C) (Y := D)) n with hβ
  set α' := HomologicalComplex.homologyMap (biprod.inl (X := C) (Y := D)) n with hα'
  set β' := HomologicalComplex.homologyMap (biprod.inr (X := C) (Y := D)) n with hβ'
  have hαα : α' ≫ α = 𝟙 (C.homology n) := by
    rw [hα', hα, ← HomologicalComplex.homologyMap_comp, biprod.inl_fst,
      HomologicalComplex.homologyMap_id]
  have hαβ : α' ≫ β = 0 := by
    rw [hα', hβ, ← HomologicalComplex.homologyMap_comp, biprod.inl_snd,
      HomologicalComplex.homologyMap_zero]
  have hβα : β' ≫ α = 0 := by
    rw [hβ', hα, ← HomologicalComplex.homologyMap_comp, biprod.inr_fst,
      HomologicalComplex.homologyMap_zero]
  have hββ : β' ≫ β = 𝟙 (D.homology n) := by
    rw [hβ', hβ, ← HomologicalComplex.homologyMap_comp, biprod.inr_snd,
      HomologicalComplex.homologyMap_id]
  have hfst : ∀ z : ↥((C ⊞ D).homology n),
      (biprod.fst : C.homology n ⊞ D.homology n ⟶ C.homology n)
        ((biprod.lift α β : (C ⊞ D).homology n ⟶ C.homology n ⊞ D.homology n) z) = α z := by
    intro z
    rw [← ConcreteCategory.comp_apply, biprod.lift_fst]
  have hsnd : ∀ z : ↥((C ⊞ D).homology n),
      (biprod.snd : C.homology n ⊞ D.homology n ⟶ D.homology n)
        ((biprod.lift α β : (C ⊞ D).homology n ⟶ C.homology n ⊞ D.homology n) z) = β z := by
    intro z
    rw [← ConcreteCategory.comp_apply, biprod.lift_snd]
  have htotal : ∀ z : ↥((C ⊞ D).homology n), α' (α z) + β' (β z) = z := by
    intro z
    have h := congrArg (fun (g : (C ⊞ D).homology n ⟶ (C ⊞ D).homology n) => g z)
      (homologyMap_total' C D n)
    simpa only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply, hα, hβ, hα', hβ'] using h
  have hinj : Function.Injective (biprod.lift α β : (C ⊞ D).homology n ⟶ C.homology n ⊞ D.homology n).hom := by
    intro x y hxy
    have hx : α x = α y := by
      have h := congrArg (fun w : ↥(C.homology n ⊞ D.homology n) =>
        (biprod.fst : C.homology n ⊞ D.homology n ⟶ C.homology n) w) hxy
      simpa only [hfst] using h
    have hy : β x = β y := by
      have h := congrArg (fun w : ↥(C.homology n ⊞ D.homology n) =>
        (biprod.snd : C.homology n ⊞ D.homology n ⟶ D.homology n) w) hxy
      simpa only [hsnd] using h
    calc x = α' (α x) + β' (β x) := (htotal x).symm
      _ = α' (α y) + β' (β y) := by rw [hx, hy]
      _ = y := htotal y
  have hsurj : Function.Surjective (biprod.lift α β : (C ⊞ D).homology n ⟶ C.homology n ⊞ D.homology n).hom := by
    intro y
    refine ⟨α' ((biprod.fst : C.homology n ⊞ D.homology n ⟶ C.homology n) y)
      + β' ((biprod.snd : C.homology n ⊞ D.homology n ⟶ D.homology n) y), ?_⟩
    have hp : α (α' ((biprod.fst : C.homology n ⊞ D.homology n ⟶ C.homology n) y))
        = (biprod.fst : C.homology n ⊞ D.homology n ⟶ C.homology n) y := by
      rw [← ConcreteCategory.comp_apply, hαα]
      simp
    have hq : β (α' ((biprod.fst : C.homology n ⊞ D.homology n ⟶ C.homology n) y)) = 0 := by
      rw [← ConcreteCategory.comp_apply, hαβ]
      simp
    have hp' : α (β' ((biprod.snd : C.homology n ⊞ D.homology n ⟶ D.homology n) y)) = 0 := by
      rw [← ConcreteCategory.comp_apply, hβα]
      simp
    have hq' : β (β' ((biprod.snd : C.homology n ⊞ D.homology n ⟶ D.homology n) y))
        = (biprod.snd : C.homology n ⊞ D.homology n ⟶ D.homology n) y := by
      rw [← ConcreteCategory.comp_apply, hββ]
      simp
    have h1 : (biprod.lift α β : (C ⊞ D).homology n ⟶ C.homology n ⊞ D.homology n)
        (α' ((biprod.fst : C.homology n ⊞ D.homology n ⟶ C.homology n) y))
        = (biprod.inl : C.homology n ⟶ C.homology n ⊞ D.homology n)
            ((biprod.fst : C.homology n ⊞ D.homology n ⟶ C.homology n) y) := by
      apply biprod_ext_apply
      · rw [hfst, hp, biprod_fst_inl_apply]
      · rw [hsnd, hq, biprod_snd_inl_apply]
    have h2 : (biprod.lift α β : (C ⊞ D).homology n ⟶ C.homology n ⊞ D.homology n)
        (β' ((biprod.snd : C.homology n ⊞ D.homology n ⟶ D.homology n) y))
        = (biprod.inr : D.homology n ⟶ C.homology n ⊞ D.homology n)
            ((biprod.snd : C.homology n ⊞ D.homology n ⟶ D.homology n) y) := by
      apply biprod_ext_apply
      · rw [hfst, hp', biprod_fst_inr_apply]
      · rw [hsnd, hq', biprod_snd_inr_apply]
    rw [map_add, h1, h2, biprod_total_apply]
  haveI : Mono (biprod.lift α β : (C ⊞ D).homology n ⟶ C.homology n ⊞ D.homology n) :=
    ModuleCat.mono_iff_injective _ |>.mpr hinj
  haveI : Epi (biprod.lift α β : (C ⊞ D).homology n ⟶ C.homology n ⊞ D.homology n) :=
    ModuleCat.epi_iff_surjective _ |>.mpr hsurj
  exact isIso_of_mono_of_epi _

/-- The homology of a binary biproduct of chain complexes of `ℤ`-modules is the biproduct of the
homologies. -/
def homologyBiprodIso (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (C ⊞ D).homology n ≅ C.homology n ⊞ D.homology n :=
  haveI := isIso_homologyMap_lift C D n
  asIso (biprod.lift (HomologicalComplex.homologyMap (biprod.fst (X := C) (Y := D)) n)
    (HomologicalComplex.homologyMap (biprod.snd (X := C) (Y := D)) n))

@[simp]
lemma homologyBiprodIso_hom (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (homologyBiprodIso C D n).hom
      = biprod.lift (HomologicalComplex.homologyMap (biprod.fst (X := C) (Y := D)) n)
        (HomologicalComplex.homologyMap (biprod.snd (X := C) (Y := D)) n) := rfl

end HomologyBiprod

/-! ## 3. Extracting isomorphisms from a long exact sequence -/

/-- **Extraction lemma.** In an exact sequence of `ℤ`-modules
`A --f--> B --g--> M --δ--> C --f'--> D`, if `f = 0` and `f'` is injective, then `g` is an
isomorphism. -/
theorem isIso_of_exact_of_zero_of_inj {A B M C D : ModuleCat ℤ}
    (f : A ⟶ B) (g : B ⟶ M) (δ : M ⟶ C) (f' : C ⟶ D)
    (h1 : δ.hom.range = f'.hom.ker) (h2 : f.hom.range = g.hom.ker)
    (h3 : g.hom.range = δ.hom.ker) (hf : f = 0) (hf' : Function.Injective f'.hom) :
    IsIso g := by
  have hrange : δ.hom.range = ⊥ := by
    rw [h1, LinearMap.ker_eq_bot.mpr hf']
  have hδ0 : δ.hom = 0 := LinearMap.range_eq_bot.mp hrange
  have hker : g.hom.ker = ⊥ := by
    rw [← h2, hf]
    simp
  have hrange' : g.hom.range = ⊤ := by
    rw [h3, hδ0]
    simp
  haveI : Mono g := ModuleCat.mono_iff_injective g |>.mpr (LinearMap.ker_eq_bot.mp hker)
  haveI : Epi g := ModuleCat.epi_iff_surjective g |>.mpr (LinearMap.range_eq_top.mp hrange')
  exact isIso_of_mono_of_epi g

/-- **Extraction lemma, second form.** In an exact sequence of `ℤ`-modules
`A --f--> B --g--> M --δ--> C --f'--> D`, if `g = 0` and `f' = 0`, then `δ` is an isomorphism. -/
theorem isIso_delta_of_exact_of_zero_zero {A B M C D : ModuleCat ℤ}
    (f : A ⟶ B) (g : B ⟶ M) (δ : M ⟶ C) (f' : C ⟶ D)
    (h1 : δ.hom.range = f'.hom.ker) (h2 : f.hom.range = g.hom.ker)
    (h3 : g.hom.range = δ.hom.ker) (hg : g = 0) (hf' : f' = 0) :
    IsIso δ := by
  have hf'0 : f'.hom = 0 := by rw [hf']; simp
  have hg0 : g.hom = 0 := by rw [hg]; simp
  have hker : δ.hom.ker = ⊥ := by
    rw [← h3, hg0]
    simp
  have hrange : δ.hom.range = ⊤ := by
    rw [h1, hf'0]
    simp
  haveI : Mono δ := ModuleCat.mono_iff_injective δ |>.mpr (LinearMap.ker_eq_bot.mp hker)
  haveI : Epi δ := ModuleCat.epi_iff_surjective δ |>.mpr (LinearMap.range_eq_top.mp hrange)
  exact isIso_of_mono_of_epi δ


/-! ## 4. Further helpers on the homology of a biproduct -/

section HomologyBiprodAux

lemma homologyBiprodIso_hom_eq (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (homologyBiprodIso C D n).hom
      = biprod.lift (HomologicalComplex.homologyMap (biprod.fst (X := C) (Y := D)) n)
        (HomologicalComplex.homologyMap (biprod.snd (X := C) (Y := D)) n) := rfl

lemma homologyBiprodIso_hom_fst (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (homologyBiprodIso C D n).hom ≫ biprod.fst =
      HomologicalComplex.homologyMap (biprod.fst (X := C) (Y := D)) n := by
  rw [homologyBiprodIso_hom_eq]
  exact biprod.lift_fst _ _

lemma homologyBiprodIso_hom_snd (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (homologyBiprodIso C D n).hom ≫ biprod.snd =
      HomologicalComplex.homologyMap (biprod.snd (X := C) (Y := D)) n := by
  rw [homologyBiprodIso_hom_eq]
  exact biprod.lift_snd _ _

/-- The homology of a lift is the lift of the homologies. -/
lemma homologyMap_biprod_lift (K C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (u : K ⟶ C) (v : K ⟶ D) :
    HomologicalComplex.homologyMap (biprod.lift u v) n ≫ (homologyBiprodIso C D n).hom
      = biprod.lift (HomologicalComplex.homologyMap u n) (HomologicalComplex.homologyMap v n) := by
  apply biprod.hom_ext
  · rw [Category.assoc, homologyBiprodIso_hom_fst, ← HomologicalComplex.homologyMap_comp,
      biprod.lift_fst, biprod.lift_fst]
  · rw [Category.assoc, homologyBiprodIso_hom_snd, ← HomologicalComplex.homologyMap_comp,
      biprod.lift_snd, biprod.lift_snd]

lemma homologyMap_inl_comp_homologyBiprodIso (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    HomologicalComplex.homologyMap (biprod.inl (X := C) (Y := D)) n
        ≫ (homologyBiprodIso C D n).hom = biprod.inl := by
  apply biprod.hom_ext
  · rw [Category.assoc, homologyBiprodIso_hom_fst, ← HomologicalComplex.homologyMap_comp,
      biprod.inl_fst, HomologicalComplex.homologyMap_id, biprod.inl_fst]
  · rw [Category.assoc, homologyBiprodIso_hom_snd, ← HomologicalComplex.homologyMap_comp,
      biprod.inl_snd, HomologicalComplex.homologyMap_zero, biprod.inl_snd]

lemma homologyMap_inr_comp_homologyBiprodIso (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    HomologicalComplex.homologyMap (biprod.inr (X := C) (Y := D)) n
        ≫ (homologyBiprodIso C D n).hom = biprod.inr := by
  apply biprod.hom_ext
  · rw [Category.assoc, homologyBiprodIso_hom_fst, ← HomologicalComplex.homologyMap_comp,
      biprod.inr_fst, HomologicalComplex.homologyMap_zero, biprod.inr_fst]
  · rw [Category.assoc, homologyBiprodIso_hom_snd, ← HomologicalComplex.homologyMap_comp,
      biprod.inr_snd, HomologicalComplex.homologyMap_id, biprod.inr_snd]

end HomologyBiprodAux

/-! ## 5. Miscellaneous topological helpers -/

/-- Chain maps are functorial. -/
lemma chainMap_comp' {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    chainMap ℤ X Y f ≫ chainMap ℤ Y Z g = chainMap ℤ X Z (f ≫ g) := by
  simp only [chainMap, Functor.map_comp]

/-- A map factoring through a space with vanishing `Hₙ` induces zero on `Hₙ`. -/
lemma homologyMap_eq_zero_of_factor {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) (h : Z ⟶ Y)
    (hfac : g ≫ h = f) (n : ℕ) (hz : IsZero ((singularChains ℤ Z).homology n)) :
    HomologicalComplex.homologyMap (chainMap ℤ X Y f) n = 0 := by
  rw [← hfac, ← chainMap_comp', HomologicalComplex.homologyMap_comp,
    IsZero.eq_zero_of_tgt hz (HomologicalComplex.homologyMap (chainMap ℤ X Z g) n), zero_comp]

/-- A constant map induces zero on `Hₙ` for `n ≥ 1`. -/
lemma homologyMap_const_eq_zero {X Y : TopCat} (y : ↥Y) (n : ℕ) (hn : 1 ≤ n) :
    HomologicalComplex.homologyMap (chainMap ℤ X Y
      (TopCat.ofHom (ContinuousMap.const X y))) n = 0 := by
  refine homologyMap_eq_zero_of_factor _ (TopCat.ofHom (ContinuousMap.const X PUnit.unit))
    (TopCat.ofHom (ContinuousMap.const (TopCat.of PUnit) y)) ?_ n
    (homologyPUnit ℤ n (by omega))
  apply TopCat.hom_ext
  ext x
  rfl


/-- Injectivity of a map out of a zero object. -/
lemma injective_of_isZero_src {M N : ModuleCat ℤ} (f : M ⟶ N) (h : IsZero M) :
    Function.Injective f.hom := by
  haveI : Subsingleton ↥M := ModuleCat.isZero_iff_subsingleton.mp h
  exact fun a b _ => Subsingleton.elim a b

/-- The swap map `A ⊞ B ⟶ B ⊞ A`. -/
def biprodSwapHom (A B : ModuleCat ℤ) : A ⊞ B ⟶ B ⊞ A :=
  biprod.lift (biprod.snd (X := A) (Y := B)) (biprod.fst (X := A) (Y := B))

lemma biprodSwapHom_comp (A B : ModuleCat ℤ) :
    biprodSwapHom A B ≫ biprodSwapHom B A = 𝟙 (A ⊞ B) := by
  have h : biprodSwapHom A B ≫ biprodSwapHom B A
      = biprod.lift (biprod.fst (X := A) (Y := B)) (biprod.snd (X := A) (Y := B)) := by
    apply biprod.hom_ext
    · rw [Category.assoc,
        show biprodSwapHom B A ≫ biprod.fst
          = biprod.snd (X := B) (Y := A) from biprod.lift_fst _ _,
        show biprodSwapHom A B ≫ biprod.snd (X := B) (Y := A)
          = biprod.fst (X := A) (Y := B) from biprod.lift_snd _ _,
        biprod.lift_fst _ _]
    · rw [Category.assoc,
        show biprodSwapHom B A ≫ biprod.snd
          = biprod.fst (X := B) (Y := A) from biprod.lift_snd _ _,
        show biprodSwapHom A B ≫ biprod.fst (X := B) (Y := A)
          = biprod.snd (X := A) (Y := B) from biprod.lift_fst _ _,
        biprod.lift_snd _ _]
  rw [h, biprod.lift_eq, biprod.total]

/-- The swap isomorphism of a binary biproduct. -/
def biprodSwap (A B : ModuleCat ℤ) : A ⊞ B ≅ B ⊞ A where
  hom := biprodSwapHom A B
  inv := biprodSwapHom B A
  hom_inv_id := biprodSwapHom_comp A B
  inv_hom_id := biprodSwapHom_comp B A

/-- The biproduct of two zero modules is zero. -/
lemma isZero_biprod_of {A B : ModuleCat ℤ} (hA : IsZero A) (hB : IsZero B) : IsZero (A ⊞ B) := by
  haveI : Subsingleton ↥A := ModuleCat.isZero_iff_subsingleton.mp hA
  haveI : Subsingleton ↥B := ModuleCat.isZero_iff_subsingleton.mp hB
  haveI : Subsingleton (↥A × ↥B) := inferInstance
  exact IsZero.of_iso (ModuleCat.isZero_iff_subsingleton.mpr inferInstance)
    (ModuleCat.biprodIsoProd A B)

end

end Work.Cohomology.Compat
