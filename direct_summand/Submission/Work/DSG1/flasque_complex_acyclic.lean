import Mathlib
import Submission.Work.DSMap.Map

/-!
# DSG1: acyclicity of a complex of flasque sheaves of modules

`Work.DSG1.flasque_complex_acyclic`: a bounded below complex `C` of `𝒪_X`-modules whose terms are
flasque (as sheaves of abelian groups) and which is exact has the property that `Γ(X, C^•)`
(in `A`-modules, via `DSMap.GammaA`) is exact.  This is the classical Cartan–Eilenberg statement
that a complex of flasque sheaves computes its own hypercohomology.

The proof is a dévissage.  Writing `Z^j = kernel (K.d j (j+1))` for the cycles of `K = C.obj`,
exactness of `K` gives short exact sequences `0 → Z^j → K^j → Z^{j+1} → 0`; the key inputs are
Mathlib's flasque lemmas `TopCat.Sheaf.IsFlasque.epi_of_shortExact` and
`TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂` (for sheaves of abelian groups),
transported to `X.Modules` along `SheafOfModules.toSheaf` — which lands in sheaves of abelian
groups, so that flasqueness of its image is exactly the hypothesis `hfl`, and which sends short
exact sequences to short exact sequences (see `epi_toSheaf_map` below).
-/

open CategoryTheory AlgebraicGeometry Limits

set_option maxHeartbeats 800000

namespace Work.DSG1

universe u

/-! ## Instances and vocabulary -/

instance toSheaf_preservesZeroMorphisms {C : Type*} [Category* C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat) : (SheafOfModules.toSheaf R).PreservesZeroMorphisms :=
  ⟨fun _ _ => by simp⟩

/-- `SheafOfModules.toSheaf` restricted to a scheme, with domain and codomain pinned, so that
type class inference can find the relevant instances. -/
noncomputable abbrev toSheafAb {X : Scheme.{u}} :
    X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat :=
  SheafOfModules.toSheaf X.ringCatSheaf

instance toSheafAb_preservesZeroMorphisms {X : Scheme.{u}} :
    (toSheafAb (X := X)).PreservesZeroMorphisms :=
  ⟨fun A B => (toSheaf_preservesZeroMorphisms X.ringCatSheaf).map_zero A B⟩

instance toSheafAb_preservesFiniteLimits {X : Scheme.{u}} :
    Limits.PreservesFiniteLimits (toSheafAb (X := X)) :=
  inferInstanceAs (Limits.PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf))

/-- `ModuleCat.restrictScalars` preserves zero morphisms. -/
instance restrictScalars_preservesZeroMorphisms {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    (ModuleCat.restrictScalars f).PreservesZeroMorphisms where
  map_zero X Y := by
    ext x
    rfl

instance sheafForget_preservesZeroMorphisms {X : TopCat.{u}} :
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X).PreservesZeroMorphisms :=
  ⟨fun _ _ => by simp⟩

instance evaluation_preservesZeroMorphisms {C : Type*} [Category* C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat) (Y : Cᵒᵖ) :
    (SheafOfModules.evaluation R Y).PreservesZeroMorphisms := ⟨fun _ _ => by simp⟩

/-- Global sections of `𝒪_X`-modules, as a functor to `Γ(X, ⊤)`-modules. -/
noncomputable abbrev gammaMod {X : Scheme.{u}} :
    X.Modules ⥤ ModuleCat (X.ringCatSheaf.obj.obj (Opposite.op ⊤)) :=
  SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)

/-- `Γ(X,-)`, viewed in `A`-modules through `f : X ⟶ Spec A`, preserves zero morphisms. -/
instance gammaA_preservesZeroMorphisms {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) : (DSMap.GammaA A X f).PreservesZeroMorphisms where
  map_zero M N := by
    haveI h1 : (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).PreservesZeroMorphisms :=
      evaluation_preservesZeroMorphisms _ _
    haveI h2 : (ModuleCat.restrictScalars (DSMap.phi A X f)).PreservesZeroMorphisms :=
      restrictScalars_preservesZeroMorphisms _
    change (ModuleCat.restrictScalars (DSMap.phi A X f)).map
      ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map (0 : M ⟶ N)) = 0
    rw [show (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map (0 : M ⟶ N) = 0
      from h1.map_zero M N]
    exact h2.map_zero _ _

set_option maxHeartbeats 800000 in
/-- `ModuleCat.restrictScalars` preserves epimorphisms (it is the identity on underlying
functions). -/
lemma restrictScalars_epi_map {R S : Type*} [Ring R] [Ring S] (χ : R →+* S)
    {M N : ModuleCat S} (g : M ⟶ N) (hg : Epi g) :
    Epi ((ModuleCat.restrictScalars χ).map g) := by
  rw [ModuleCat.epi_iff_surjective] at hg ⊢
  exact hg

/-! ## Elementary homological helpers -/

section Zero

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

lemma isZero_obj_of_isZero (F : C ⥤ D) [F.PreservesZeroMorphisms] {M : C} (h : IsZero M) :
    IsZero (F.obj M) := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  rw [← F.map_id, h, F.map_zero]

lemma isZero_obj_of_isZero_functor {C' D' : Type*} [Category* C'] [Category* D']
    [HasZeroMorphisms D'] {F : C' ⥤ D'} (h : IsZero F) (X : C') : IsZero (F.obj X) := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  simpa using NatTrans.congr_app h X

/-- The kernel inclusion `kernel.ι f` is a monomorphism, directly from the universal property
of the kernel. -/
lemma mono_kernel_ι {X Y : C} (f : X ⟶ Y) [HasKernel f] : Mono (kernel.ι f) where
  right_cancellation {Z} g h eq := by
    apply Fork.IsLimit.hom_ext (kernelIsKernel f)
    simpa using eq

/-- The `hom` of an isomorphism is an epimorphism. -/
lemma iso_hom_epi {X Y : C} (e : X ≅ Y) : Epi e.hom where
  left_cancellation {Z} a b hab := by
    calc a = 𝟙 Y ≫ a := (Category.id_comp a).symm
      _ = (e.inv ≫ e.hom) ≫ a := by rw [Iso.inv_hom_id]
      _ = e.inv ≫ (e.hom ≫ a) := Category.assoc _ _ _
      _ = e.inv ≫ (e.hom ≫ b) := by rw [hab]
      _ = (e.inv ≫ e.hom) ≫ b := (Category.assoc _ _ _).symm
      _ = 𝟙 Y ≫ b := by rw [Iso.inv_hom_id]
      _ = b := Category.id_comp b

/-- Composition of epimorphisms, with the two epimorphism proofs passed explicitly. -/
lemma epi_comp' {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : Epi f) (hg : Epi g) : Epi (f ≫ g) where
  left_cancellation {W} a b hab := by
    have h1 : f ≫ (g ≫ a) = f ≫ (g ≫ b) := by
      rw [← Category.assoc, ← Category.assoc]
      exact hab
    exact hg.left_cancellation a b (hf.left_cancellation (g ≫ a) (g ≫ b) h1)

instance iso_hom_epi_inst {X Y : C} (e : X ≅ Y) : Epi e.hom := iso_hom_epi e

end Zero

section Kernel

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]

lemma PreservesKernel.iso_hom_ι (F : C ⥤ D) [F.PreservesZeroMorphisms] {B Z : C} (g : B ⟶ Z)
    [HasKernel g] [HasKernel (F.map g)] [PreservesLimit (parallelPair g 0) F] :
    (PreservesKernel.iso F g).hom ≫ kernel.ι (F.map g) = F.map (kernel.ι g) := by
  rw [← PreservesKernel.iso_inv_ι]
  simp

/-- Functoriality of `kernel.lift`. -/
lemma kernel_lift_map (F : C ⥤ D) [F.PreservesZeroMorphisms] {A B Z : C} (g : B ⟶ Z) (f : A ⟶ B)
    [HasKernel g] [HasKernel (F.map g)] [PreservesLimit (parallelPair g 0) F] (w : f ≫ g = 0) :
    F.map (kernel.lift g f w) ≫ (PreservesKernel.iso F g).hom =
      kernel.lift (F.map g) (F.map f) (by rw [← F.map_comp, w, F.map_zero]) := by
  rw [← cancel_mono (kernel.ι (F.map g)), Category.assoc, PreservesKernel.iso_hom_ι,
    ← F.map_comp, kernel.lift_ι, kernel.lift_ι]

/-- A functor which preserves kernels preserves monomorphisms. -/
lemma mono_map_of_mono (F : C ⥤ D) [F.PreservesZeroMorphisms] {M N : C} (g : M ⟶ N)
    (hg : Mono g) [HasKernel g] [HasKernel (F.map g)] [PreservesLimit (parallelPair g 0) F] :
    Mono (F.map g) := by
  haveI := hg
  rw [Preadditive.mono_iff_isZero_kernel]
  have h1 : IsZero (kernel g) := isZero_kernel_of_mono g
  have h2 : IsZero (F.obj (kernel g)) := by
    rw [IsZero.iff_id_eq_zero] at h1 ⊢
    rw [← F.map_id, h1, F.map_zero]
  exact (Iso.isZero_iff (PreservesKernel.iso F g).symm).mpr h2

end Kernel

/-! ## Flasqueness -/

section Flasque

variable {X : Scheme.{u}}

/-- The flasqueness condition on an `𝒪_X`-module used throughout: the underlying sheaf of
abelian groups is flasque.  This is verbatim the hypothesis of `flasque_complex_acyclic`. -/
abbrev IsFlasqueMod (M : X.Modules) : Prop :=
  TopCat.Presheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj

/-- The cycles `Z^j = ker (d^j)` of a cochain complex of `𝒪_X`-modules. -/
noncomputable abbrev Zk (K : CochainComplex X.Modules ℤ) (j : ℤ) : X.Modules :=
  kernel (K.d j (j + 1))

/-- The canonical map `K^j → Z^{j+1}` (the differential followed by the inclusion of cycles). -/
noncomputable abbrev kap (K : CochainComplex X.Modules ℤ) (j : ℤ) :
    K.X j ⟶ Zk K (j + 1) :=
  kernel.lift (K.d (j + 1) (j + 1 + 1)) (K.d j (j + 1)) (K.d_comp_d j (j + 1) (j + 1 + 1))

lemma kap_kernel_ι (K : CochainComplex X.Modules ℤ) (j : ℤ) :
    kap K j ≫ kernel.ι (K.d (j + 1) (j + 1 + 1)) = K.d j (j + 1) :=
  kernel.lift_ι _ _ _

/-- The canonical identification of `kernel (kap K n)` with the cycles `Z^n`. -/
noncomputable abbrev kernel_kap_iso (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    kernel (kap K n) ≅ Zk K n := by
  have hA : kernel.ι (K.d n (n + 1)) ≫ kap K n = 0 := by
    apply Fork.IsLimit.hom_ext (kernelIsKernel (K.d (n + 1) (n + 1 + 1)))
    rw [Fork.ι_ofι]
    simp only [kap]
    rw [Category.assoc, kernel.lift_ι, kernel.condition, zero_comp]
  have hB : kernel.ι (kap K n) ≫ K.d n (n + 1) = 0 := by
    rw [← kap_kernel_ι K n]
    simp only [kap]
    rw [← Category.assoc, kernel.condition, zero_comp]
  refine ⟨kernel.lift (K.d n (n + 1)) (kernel.ι (kap K n)) hB,
    kernel.lift (kap K n) (kernel.ι (K.d n (n + 1))) hA, ?_, ?_⟩
  · apply Fork.IsLimit.hom_ext (kernelIsKernel (kap K n))
    rw [Fork.ι_ofι]
    simp only [Category.assoc, kernel.lift_ι, Category.id_comp]
  · apply Fork.IsLimit.hom_ext (kernelIsKernel (K.d n (n + 1)))
    rw [Fork.ι_ofι]
    simp only [Category.assoc, kernel.lift_ι, Category.id_comp]

lemma isFlasque_of_iso {F G : TopCat.Presheaf AddCommGrpCat.{u} X.toTopCat} (e : F ≅ G)
    (h : TopCat.Presheaf.IsFlasque F) : TopCat.Presheaf.IsFlasque G where
  epi {U V} i := by
    haveI hA : Epi (F.map i) := h.epi i
    have key : G.map i = e.inv.app U ≫ F.map i ≫ e.hom.app V := by
      rw [e.hom.naturality i, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    rw [key]
    haveI hB : Epi (F.map i ≫ e.hom.app V) := epi_comp (F.map i) (e.hom.app V)
    exact epi_comp (e.inv.app U) (F.map i ≫ e.hom.app V)

lemma IsFlasqueMod.of_iso {M N : X.Modules} (e : M ≅ N) (h : IsFlasqueMod M) :
    IsFlasqueMod N :=
  isFlasque_of_iso
    ((TopCat.Sheaf.forget AddCommGrpCat X.toTopCat).mapIso
      ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso e)) h

lemma IsFlasqueMod.of_isZero {M : X.Modules} (h : IsZero M) : IsFlasqueMod M := by
  have h1 : IsZero ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) :=
    isZero_obj_of_isZero _ h
  haveI h2 : IsZero ((TopCat.Sheaf.forget AddCommGrpCat X.toTopCat).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) := isZero_obj_of_isZero _ h1
  refine ⟨fun {U V} i => ?_⟩
  haveI h3 : IsZero (((TopCat.Sheaf.forget AddCommGrpCat X.toTopCat).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)).obj V) :=
    isZero_obj_of_isZero_functor h2 V
  exact h3.epi _

/-! ## `toSheaf` sends epimorphisms of sheaves of modules to epimorphisms of sheaves of
abelian groups -/

/-- An epimorphism of sheaves of `𝒪_X`-modules remains an epimorphism after forgetting the
`𝒪_X`-module structure.  Both notions mean "locally surjective on sections".

The proof is a computation with cokernels.  Let `L = PresheafOfModules.sheafification (𝟙 𝒪_X)` be
the sheafification of presheaves of modules, `G = forget ⋙ restrictScalars 𝟙` the forgetful
functor going back, and `T = toSheaf`.  The counit of the adjunction `L ⊣ G` is an isomorphism
`ε : G ⋙ L ≅ 𝟭`, which exhibits `f` as conjugate to `L (G f)`; since `cokernel` is a functor this
gives `IsZero (cokernel (L (G f)))` from `IsZero (cokernel f)`, i.e. from `Epi f`.  On the other
hand `L ⋙ T` is definitionally `toPresheaf ⋙ presheafToSheaf`
(`PresheafOfModules.sheafificationCompToSheaf`, an `Iso.refl`), and `toPresheaf` as well as the
left adjoint `presheafToSheaf` preserve cokernels, so
`cokernel (T (L (G f))) ≅ T (cokernel (L (G f))) = 0`.  Conjugating back along `ε` (applied to
`T`) gives `IsZero (cokernel (T f))`, which is exactly `Epi (T f)`. -/
theorem epi_toSheaf_map {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (hf : Epi f) :
    Epi ((SheafOfModules.toSheaf X.ringCatSheaf).map f) := by
  show Epi ((toSheafAb (X := X)).map f)
  let T := toSheafAb (X := X)
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let P := PresheafOfModules.toPresheaf X.ringCatSheaf.obj
  let S := presheafToSheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}
  let G : X.Modules ⥤ X.PresheafOfModules :=
    SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
  let ε := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit
  have hε : IsIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit) := inferInstance
  let η : G ⋙ L ≅ 𝟭 X.Modules := @asIso _ _ (G ⋙ L) (𝟭 X.Modules) ε hε
  let E : L ⋙ T ≅ P ⋙ S :=
    PresheafOfModules.sheafificationCompToSheaf (α := 𝟙 X.ringCatSheaf.obj)
  have hconj : L.map (G.map f) ≫ ε.app N = ε.app M ≫ f := ε.naturality f
  -- `f` is conjugate to the sheafification of its underlying presheaf morphism, so the cokernel
  -- of the latter vanishes as well
  have h1 : IsZero (cokernel f) := (Preadditive.epi_iff_isZero_cokernel f).mp hf
  have h2 : IsZero (cokernel (L.map (G.map f))) :=
    h1.of_iso (cokernel.mapIso (L.map (G.map f)) f (η.app M) (η.app N) hconj)
  -- `L ⋙ T` is `toPresheaf ⋙ presheafToSheaf`, and both factors preserve cokernels
  have eT : cokernel (T.map (L.map (G.map f))) ≅ T.obj (cokernel (L.map (G.map f))) :=
    cokernel.mapIso ((L ⋙ T).map (G.map f)) ((P ⋙ S).map (G.map f))
        (E.app (G.obj M)) (E.app (G.obj N)) (E.hom.naturality (G.map f))
      ≪≫ (PreservesCokernel.iso S (P.map (G.map f))).symm
      ≪≫ S.mapIso (PreservesCokernel.iso P (G.map f)).symm
      ≪≫ (E.app (cokernel (G.map f))).symm
      ≪≫ T.mapIso (PreservesCokernel.iso L (G.map f))
  have h3 : IsZero (cokernel (T.map (L.map (G.map f)))) :=
    (isZero_obj_of_isZero (toSheafAb (X := X)) h2).of_iso eT
  -- transport back to `f` along the (applied) counit isomorphism
  have hw : T.map (L.map (G.map f)) ≫ T.map (ε.app N) = T.map (ε.app M) ≫ T.map f := by
    calc T.map (L.map (G.map f)) ≫ T.map (ε.app N)
        = T.map (L.map (G.map f) ≫ ε.app N) := (Functor.map_comp T _ _).symm
      _ = T.map (ε.app M ≫ f) := congrArg (fun t => T.map t) hconj
      _ = T.map (ε.app M) ≫ T.map f := Functor.map_comp T _ _
  have h4 : IsZero (cokernel (T.map f)) :=
    h3.of_iso (cokernel.mapIso (T.map (L.map (G.map f))) (T.map f)
      (T.mapIso (η.app M)) (T.mapIso (η.app N)) hw).symm
  exact Preadditive.epi_of_isZero_cokernel _ h4

/-- `SheafOfModules.toSheaf` sends a short exact sequence of `𝒪_X`-modules to a short exact
sequence of sheaves of abelian groups. -/
theorem toSheaf_map_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (S.map (toSheafAb (X := X))).ShortExact := by
  have hm : Mono S.f := hS.mono_f
  have he : Epi S.g := hS.epi_g
  have hk : Epi (kernel.lift S.g S.f S.zero) := by
    rw [← ShortComplex.exact_iff_epi_kernel_lift]
    exact hS.exact
  have hmono : Mono ((S.map (toSheafAb (X := X))).f) :=
    mono_map_of_mono (toSheafAb (X := X)) S.f hm
  have hepi : Epi ((S.map (toSheafAb (X := X))).g) :=
    epi_toSheaf_map S.g he
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  simp only [ShortComplex.map_f, ShortComplex.map_g]
  have h1 : Epi ((toSheafAb (X := X)).map (kernel.lift S.g S.f S.zero)) :=
    epi_toSheaf_map (kernel.lift S.g S.f S.zero) hk
  haveI h1' : Epi ((toSheafAb (X := X)).map (kernel.lift S.g S.f S.zero)) := h1
  rw [← kernel_lift_map (toSheafAb (X := X)) S.g S.f S.zero]
  exact epi_comp _ _

/-- The flasque lemma of Cartan–Eilenberg in the form needed here: if `0 → A → B → C → 0` is
a short exact sequence of `𝒪_X`-modules with `A` flasque, then `Γ(X, B) → Γ(X, C)` is
surjective. -/
theorem flasque_shortExact_epi {X : Scheme.{u}} {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h : IsFlasqueMod S.X₁) : Epi ((gammaMod (X := X)).map S.g) := by
  have hS' := toSheaf_map_shortExact hS
  haveI : ((S.map (toSheafAb (X := X))).X₁).IsFlasque := h
  have hU := TopCat.Sheaf.IsFlasque.epi_of_shortExact
    (X := X.toTopCat) (U := ⊤)
    (S := S.map (toSheafAb (X := X))) hS'
  rw [ModuleCat.epi_iff_surjective]
  rw [AddCommGrpCat.epi_iff_surjective] at hU
  exact hU

/-- The quotient of a flasque `𝒪_X`-module by a flasque submodule is flasque. -/
theorem flasque_of_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : IsFlasqueMod S.X₁) (h₂ : IsFlasqueMod S.X₂) : IsFlasqueMod S.X₃ := by
  have hS' := toSheaf_map_shortExact hS
  haveI : ((S.map (toSheafAb (X := X))).X₁).IsFlasque := h₁
  haveI : ((S.map (toSheafAb (X := X))).X₂).IsFlasque := h₂
  exact TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
    (S := S.map (toSheafAb (X := X))) hS'

/-- The flasque lemma applied to an epimorphism with flasque kernel. -/
theorem gammaA_epi_of_epi_kernel {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) {B Cc : X.Modules} (k : B ⟶ Cc) (hk : Epi k)
    (hfl : IsFlasqueMod (kernel k)) : Epi ((DSMap.GammaA A X f).map k) := by
  haveI := hk
  have hS : (ShortComplex.kernelSequence k).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact k)
      (by rw [ShortComplex.kernelSequence_f]; exact mono_kernel_ι k)
      (show Epi (ShortComplex.kernelSequence k).g from hk)
  have h1 : Epi ((gammaMod (X := X)).map k) :=
    flasque_shortExact_epi hS hfl
  rw [ModuleCat.epi_iff_surjective] at h1
  rw [ModuleCat.epi_iff_surjective]
  exact h1

end Flasque

/-! ## The main theorem -/

theorem flasque_complex_acyclic {A : Type u} [CommRing A] {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    (C : CochainComplex.Plus X.Modules)
    (hfl : ∀ n : ℤ, TopCat.Presheaf.IsFlasque
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj (C.obj.X n)).obj)
    (hac : C.obj.Acyclic) :
    ((DSMap.GammaA A X f).mapCochainComplexPlus.obj C).obj.Acyclic := by
  change (((DSMap.GammaA A X f).mapHomologicalComplex (ComplexShape.up ℤ)).obj C.obj).Acyclic
  rw [HomologicalComplex.acyclic_iff]
  obtain ⟨n₀, hn₀⟩ := C.2
  have hGE : ∀ (i : ℤ), i < n₀ → IsZero (C.obj.X i) := fun i hi =>
    (CochainComplex.isStrictlyGE_iff C.obj n₀).mp hn₀ i hi
  have hprev : ∀ j : ℤ, (ComplexShape.up ℤ).prev (j + 1) = j := by
    intro j
    rw [CochainComplex.prev]
    omega
  have hnext : ∀ j : ℤ, (ComplexShape.up ℤ).next (j + 1) = j + 1 + 1 := by
    intro j
    rw [CochainComplex.next]
  have hκ : ∀ j : ℤ, Epi (kap C.obj j) := by
    intro j
    have hex : (C.obj.sc' j (j + 1) (j + 1 + 1)).Exact :=
      (C.obj.exactAt_iff' j (j + 1) (j + 1 + 1)
        (ComplexShape.prev_eq' _ (ComplexShape.up_mk j (j + 1) rfl))
        (ComplexShape.next_eq' _ (ComplexShape.up_mk (j + 1) (j + 1 + 1) rfl))).mp (hac (j + 1))
    rw [ShortComplex.exact_iff_epi_kernel_lift] at hex
    exact hex
  have hZbase : IsFlasqueMod (Zk C.obj n₀) := by
    have h0 : C.obj.d (n₀ - 1) n₀ = 0 := (hGE (n₀ - 1) (by omega)).eq_of_src _ _
    have hex : (C.obj.sc' (n₀ - 1) n₀ (n₀ + 1)).Exact :=
      (C.obj.exactAt_iff' (n₀ - 1) n₀ (n₀ + 1)
        (ComplexShape.prev_eq' _ (ComplexShape.up_mk (n₀ - 1) n₀ (by omega)))
        (ComplexShape.next_eq' _ (ComplexShape.up_mk n₀ (n₀ + 1) rfl))).mp (hac n₀)
    have hmono : Mono (C.obj.d n₀ (n₀ + 1)) :=
      (ShortComplex.exact_iff_mono _
        (show (C.obj.sc' (n₀ - 1) n₀ (n₀ + 1)).f = 0 from h0)).mp hex
    exact IsFlasqueMod.of_isZero (isZero_kernel_of_mono (C.obj.d n₀ (n₀ + 1)))
  have hZstep : ∀ n : ℤ, n₀ ≤ n → IsFlasqueMod (Zk C.obj n) →
      IsFlasqueMod (Zk C.obj (n + 1)) := by
    intro n _ ih
    have hS : (ShortComplex.kernelSequence (kap C.obj n)).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact (kap C.obj n))
        (by rw [ShortComplex.kernelSequence_f]; exact mono_kernel_ι (kap C.obj n))
        (by rw [ShortComplex.kernelSequence_g]; exact hκ n)
    exact flasque_of_shortExact (S := ShortComplex.kernelSequence (kap C.obj n)) hS
      (IsFlasqueMod.of_iso (kernel_kap_iso C.obj n).symm ih) (hfl n)
  have hZ : ∀ j : ℤ, n₀ ≤ j → IsFlasqueMod (Zk C.obj j) :=
    Int.leInduction hZbase hZstep
  intro i
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j + 1 := ⟨i - 1, by omega⟩
  rw [HomologicalComplex.exactAt_iff'
    (((DSMap.GammaA A X f).mapHomologicalComplex (ComplexShape.up ℤ)).obj C.obj)
    j (j + 1) (j + 1 + 1) (hprev j) (hnext j)]
  by_cases hj : j + 1 ≤ n₀
  · have hj' : j < n₀ := by omega
    have h0 : C.obj.d j (j + 1) = 0 := (hGE j hj').eq_of_src _ _
    have hex : (C.obj.sc' j (j + 1) (j + 1 + 1)).Exact :=
      (C.obj.exactAt_iff' j (j + 1) (j + 1 + 1) (hprev j) (hnext j)).mp (hac (j + 1))
    have hmono : Mono (C.obj.d (j + 1) (j + 1 + 1)) :=
      (ShortComplex.exact_iff_mono _
        (show (C.obj.sc' j (j + 1) (j + 1 + 1)).f = 0 from h0)).mp hex
    refine (ShortComplex.exact_iff_mono _ ?_).mpr ?_
    · show (DSMap.GammaA A X f).map (C.obj.d j (j + 1)) = 0
      rw [h0]
      exact Functor.map_zero _ _ _
    · have hmonoE : Mono ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
          (C.obj.d (j + 1) (j + 1 + 1))) :=
        mono_map_of_mono (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤))
          (C.obj.d (j + 1) (j + 1 + 1)) hmono
      exact mono_map_of_mono (ModuleCat.restrictScalars (DSMap.phi A X f))
        ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
          (C.obj.d (j + 1) (j + 1 + 1))) hmonoE
  · rw [not_le] at hj
    have hj' : n₀ ≤ j := by omega
    have hflk' : IsFlasqueMod (kernel (kap C.obj j)) :=
      IsFlasqueMod.of_iso (kernel_kap_iso C.obj j).symm (hZ j hj')
    have hS : (ShortComplex.kernelSequence (kap C.obj j)).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact (kap C.obj j))
        (by rw [ShortComplex.kernelSequence_f]; exact mono_kernel_ι (kap C.obj j))
        (by rw [ShortComplex.kernelSequence_g]; exact hκ j)
    haveI hEpiK : Epi ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
        (kap C.obj j)) := flasque_shortExact_epi hS hflk'
    have hfg : ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
        (C.obj.d j (j + 1))) ≫
        ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
          (C.obj.d (j + 1) (j + 1 + 1))) = 0 := by
      calc ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
              (C.obj.d j (j + 1))) ≫
            ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
              (C.obj.d (j + 1) (j + 1 + 1)))
          = (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
              (C.obj.d j (j + 1) ≫ C.obj.d (j + 1) (j + 1 + 1)) :=
            (Functor.map_comp _ _ _).symm
        _ = (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map 0 :=
            congrArg (fun t => (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map t)
              (C.obj.d_comp_d j (j + 1) (j + 1 + 1))
        _ = 0 := Functor.map_zero _ _ _
    have hK' : Epi (kernel.lift
        ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
          (C.obj.d (j + 1) (j + 1 + 1)))
        ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map (C.obj.d j (j + 1)))
        hfg) := by
      rw [← kernel_lift_map (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤))
        (C.obj.d (j + 1) (j + 1 + 1)) (C.obj.d j (j + 1))
        (C.obj.d_comp_d j (j + 1) (j + 1 + 1))]
      exact epi_comp' ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
        (kap C.obj j))
        (PreservesKernel.iso (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤))
          (C.obj.d (j + 1) (j + 1 + 1))).hom hEpiK
        (iso_hom_epi (PreservesKernel.iso (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤))
          (C.obj.d (j + 1) (j + 1 + 1))))
    rw [ShortComplex.exact_iff_epi_kernel_lift]
    have hisoE : Epi (PreservesKernel.iso (ModuleCat.restrictScalars (DSMap.phi A X f))
        ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
          (C.obj.d (j + 1) (j + 1 + 1)))).hom :=
      iso_hom_epi (PreservesKernel.iso (ModuleCat.restrictScalars (DSMap.phi A X f))
        ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
          (C.obj.d (j + 1) (j + 1 + 1))))
    have hfgA : ((DSMap.GammaA A X f).map (C.obj.d j (j + 1))) ≫
        ((DSMap.GammaA A X f).map (C.obj.d (j + 1) (j + 1 + 1))) = 0 := by
      calc ((DSMap.GammaA A X f).map (C.obj.d j (j + 1))) ≫
            ((DSMap.GammaA A X f).map (C.obj.d (j + 1) (j + 1 + 1)))
          = (DSMap.GammaA A X f).map (C.obj.d j (j + 1) ≫ C.obj.d (j + 1) (j + 1 + 1)) :=
            (Functor.map_comp _ _ _).symm
        _ = (DSMap.GammaA A X f).map 0 :=
            congrArg (fun t => (DSMap.GammaA A X f).map t)
              (C.obj.d_comp_d j (j + 1) (j + 1 + 1))
        _ = 0 := Functor.map_zero _ _ _
    have h2 : Epi (kernel.lift ((DSMap.GammaA A X f).map (C.obj.d (j + 1) (j + 1 + 1)))
        ((DSMap.GammaA A X f).map (C.obj.d j (j + 1))) hfgA) := by
      erw [← kernel_lift_map (ModuleCat.restrictScalars (DSMap.phi A X f))
        ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
          (C.obj.d (j + 1) (j + 1 + 1)))
        ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map (C.obj.d j (j + 1)))
        hfg]
      haveI hE1 : Epi ((ModuleCat.restrictScalars (DSMap.phi A X f)).map (kernel.lift
          ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
            (C.obj.d (j + 1) (j + 1 + 1)))
          ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
            (C.obj.d j (j + 1))) hfg)) :=
        restrictScalars_epi_map (DSMap.phi A X f) _
          (by
            rw [← kernel_lift_map (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤))
              (C.obj.d (j + 1) (j + 1 + 1)) (C.obj.d j (j + 1))
              (C.obj.d_comp_d j (j + 1) (j + 1 + 1))]
            exact epi_comp' ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
              (kap C.obj j))
              (PreservesKernel.iso (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤))
                (C.obj.d (j + 1) (j + 1 + 1))).hom hEpiK
              (iso_hom_epi (PreservesKernel.iso
                (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤))
                (C.obj.d (j + 1) (j + 1 + 1)))))
      exact epi_comp' ((ModuleCat.restrictScalars (DSMap.phi A X f)).map (kernel.lift
          ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
            (C.obj.d (j + 1) (j + 1 + 1)))
          ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
            (C.obj.d j (j + 1))) hfg))
        (PreservesKernel.iso (ModuleCat.restrictScalars (DSMap.phi A X f))
          ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
            (C.obj.d (j + 1) (j + 1 + 1)))).hom hE1 hisoE
    exact h2

end Work.DSG1
