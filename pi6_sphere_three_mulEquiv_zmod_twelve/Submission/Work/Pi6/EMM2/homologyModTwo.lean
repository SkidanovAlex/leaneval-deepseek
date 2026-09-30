import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.SSS.singularCoeffFG
import Submission.Work.StemsB.sphRatHomology
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

/-!
# Integral-to-mod-2 change of coefficients in degree `n+1`

If `H_n(X;ℤ) = 0` and `H_{n+1}(X;ℤ) ≅ ℤ/2`, then `H_{n+1}(X;ℤ/2) ≅ ℤ/2` as a `ℤ/2`-module.

The proof runs the long exact homology sequence of the short exact sequence of chain complexes
`0 → C_*(X;ℤ) --·2--> C_*(X;ℤ) --red--> C_*(X;ℤ/2) → 0`.  Since `2·H_{n+1}(X;ℤ) = 0`, the map
`H_{n+1}(X;ℤ) → H_{n+1}(X;ℤ)` induced by multiplication by `2` is zero, so the reduction
`H_{n+1}(X;ℤ) → H_{n+1}(X;ℤ/2)` is injective; since `H_n(X;ℤ) = 0` the connecting map
`H_{n+1}(X;ℤ/2) → H_n(X;ℤ)` is zero, so the reduction is surjective.  Hence it is an isomorphism
and `H_{n+1}(X;ℤ/2) ≅ H_{n+1}(X;ℤ) ≅ ℤ/2`.  Finally the resulting `ℤ`-linear isomorphism is
transported to a `ℤ/2`-linear one.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory

namespace Work.Pi6.EMM2

noncomputable section

/-- `ℤ/2` as a `ℤ`-module. -/
abbrev M2 : ModuleCat ℤ := ModuleCat.of ℤ (ZMod 2)

/-- `ℤ/2` as a `ℤ/2`-module. -/
abbrev R2 : ModuleCat (ZMod 2) := ModuleCat.of (ZMod 2) (ZMod 2)

/-- Restriction of scalars along `ℤ → ℤ/2`. -/
abbrev scZ : ModuleCat (ZMod 2) ⥤ ModuleCat ℤ :=
  ModuleCat.restrictScalars (Int.castRingHom (ZMod 2))

/-- The singular simplicial set of a space. -/
abbrev sing (X : Type) [TopologicalSpace X] : SSet := TopCat.toSSet.obj (TopCat.of X)

/-- The integral singular chains. -/
abbrev CZ (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat ℤ) ℕ :=
  (sing X).chainComplex (ModuleCat.of ℤ ℤ)

/-- The singular chains with `ℤ/2`-coefficients, read over `ℤ`. -/
abbrev C2 (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat ℤ) ℕ :=
  (sing X).chainComplex M2

/-- The singular chains with `ℤ/2`-coefficients. -/
abbrev CR (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat (ZMod 2)) ℕ :=
  (sing X).chainComplex R2

/-- The `ℤ`-chain complex underlying the mod-2 singular chains. -/
abbrev CN (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat ℤ) ℕ :=
  (scZ.mapHomologicalComplex (ComplexShape.down ℕ)).obj (CR X)

/-! ## The coefficient sequence `0 → ℤ --·2--> ℤ --red--> ℤ/2 → 0` -/

/-- Multiplication by `2` on `ℤ`, as a `ℤ`-module endomorphism. -/
def twoZ : (ModuleCat.of ℤ ℤ) ⟶ (ModuleCat.of ℤ ℤ) := (2 : ℤ) • 𝟙 _

/-- The reduction `ℤ → ℤ/2`. -/
noncomputable def redZ : (ModuleCat.of ℤ ℤ) ⟶ M2 :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (ZMod 2) 1)

lemma twoZ_hom (z : ℤ) : twoZ.hom z = 2 * z := by simp [twoZ]

lemma redZ_hom (z : ℤ) : redZ.hom z = (z : ZMod 2) := by
  rw [show redZ.hom z = (LinearMap.toSpanSingleton ℤ (ZMod 2) (1 : ZMod 2)) z from rfl,
    LinearMap.toSpanSingleton_apply]
  simp

lemma intCast_two_mul (z : ℤ) : ((2 * z : ℤ) : ZMod 2) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨z, rfl⟩

/-- Exactness of `ℤ --·2--> ℤ --red--> ℤ/2` in function form. -/
lemma coeffSES_exact : Function.Exact (twoZ.hom) (redZ.hom) := by
  rw [LinearMap.exact_iff]
  ext y
  rw [LinearMap.mem_ker, LinearMap.mem_range, redZ_hom]
  constructor
  · intro hy
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hy
    obtain ⟨k, hk⟩ := hy
    exact ⟨k, by rw [twoZ_hom]; exact hk.symm⟩
  · rintro ⟨x, hx⟩
    rw [← hx, twoZ_hom]
    exact intCast_two_mul x

lemma twoZ_injective_int : Function.Injective (fun z : ℤ => (2 : ℤ) * z) := by
  intro z w h
  change (2 : ℤ) * z = 2 * w at h
  omega

lemma twoZ_injective : Function.Injective (twoZ.hom) := by
  intro z w hzw
  rw [twoZ_hom z, twoZ_hom w] at hzw
  exact twoZ_injective_int hzw

lemma redZ_surjective : Function.Surjective (redZ.hom) := by
  intro y
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective (show ZMod 2 from y)
  exact ⟨k, by rw [redZ_hom]; exact hk⟩

/-- The mod-2 coefficient sequence `0 → ℤ --·2--> ℤ --red--> ℤ/2 → 0`. -/
def coeffSES : ShortComplex (ModuleCat ℤ) := ShortComplex.mk twoZ redZ (by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
    twoZ_hom, redZ_hom]
  exact intCast_two_mul z)

theorem coeffSES_shortExact : coeffSES.ShortExact := by
  refine ModuleCat.shortComplex_shortExact coeffSES ?_ ?_ ?_
  · rw [show coeffSES.f = twoZ from rfl, show coeffSES.g = redZ from rfl]
    exact coeffSES_exact
  · rw [show coeffSES.f = twoZ from rfl]
    exact twoZ_injective
  · rw [show coeffSES.g = redZ from rfl]
    exact redZ_surjective

/-! ## The short exact sequence of chain complexes -/

/-- `C_*(X;ℤ) --·2--> C_*(X;ℤ) --red--> C_*(X;ℤ/2)`. -/
def SESc (X : Type) [TopologicalSpace X] : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  Work.SSS.expTensShort (CZ X) coeffSES

theorem SESc_shortExact (X : Type) [TopologicalSpace X] : (SESc X).ShortExact := by
  haveI hfree : ∀ j, Module.Free ℤ ↥((CZ X).X j) := fun j => Work.SSS.sChains_free (sing X) j
  haveI hflat : ∀ j, Module.Flat ℤ ↥((CZ X).X j) := fun j => Module.Flat.of_free
  exact Work.SSS.expTensShort_shortExact coeffSES coeffSES_shortExact hflat

/-- The coefficient comparison: `ℤ/2` seen through restriction of scalars is `ℤ/2`. -/
def coeffIso : scZ.obj R2 ≅ M2 := by
  refine LinearEquiv.toModuleIso (X₁ := scZ.obj R2) (X₂ := M2) <|
    @AddEquiv.toLinearEquiv ℤ ↥(scZ.obj R2) ↥M2 _ _ _ (scZ.obj R2).isModule M2.isModule
      (AddEquiv.refl _) ?_
  intro c x
  have h : (scZ.obj R2).isModule = M2.isModule := Subsingleton.elim _ _
  rw [h]
  rfl

/-! ## Three auxiliary linear-algebra facts -/

/-- `homologyMap` is `ℤ`-linear in the chain map: it is the map of the additive functor
`homologyFunctor`. -/
theorem homologyMap_zsmul_aux {K L : ChainComplex (ModuleCat ℤ) ℕ} (a : ℤ) (φ : K ⟶ L) (i : ℕ) :
    HomologicalComplex.homologyMap (a • φ) i = a • HomologicalComplex.homologyMap φ i :=
  Functor.map_zsmul (F := HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) i)
    (f := φ) (r := a)

/-- `expTens K -` is `ℤ`-linear in the coefficient morphism. -/
theorem expTensHom_zsmul_aux (K : ChainComplex (ModuleCat ℤ) ℕ) (r : ℤ) {M N : ModuleCat ℤ}
    (f : M ⟶ N) :
    Work.SSS.expTensHom K (r • f) = r • Work.SSS.expTensHom K f := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.smul_f_apply, Work.SSS.expTensHom_f, Work.SSS.expTensHom_f]
  exact Functor.map_zsmul (F := tensorLeft (K.X n)) (f := f) (r := r)

/-- An isomorphism of `ℤ`-modules between the restrictions of scalars of two `ℤ/2`-modules is
already `ℤ/2`-linear, hence comes from an isomorphism of `ℤ/2`-modules. -/
theorem restrictScalarsIso_aux {A B : ModuleCat (ZMod 2)}
    (e : (ModuleCat.restrictScalars (Int.castRingHom (ZMod 2))).obj A ≅
      (ModuleCat.restrictScalars (Int.castRingHom (ZMod 2))).obj B) :
    Nonempty (A ≅ B) := by
  have hsmul : ∀ (a : ZMod 2) (x : ↥A),
      (e.hom.hom.toAddHom) (a • x) = a • (e.hom.hom.toAddHom) x := by
    intro a x
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective a
    subst hk
    exact e.hom.hom.map_smul k x
  refine ⟨LinearEquiv.toModuleIso (X₁ := A) (X₂ := B) (LinearEquiv.ofBijective ?_ ⟨?_, ?_⟩)⟩
  · exact @LinearMap.mk (ZMod 2) (ZMod 2) _ _ (RingHom.id (ZMod 2)) ↥A ↥B _ _
      A.isModule B.isModule e.hom.hom.toAddHom hsmul
  · exact (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  · exact (ModuleCat.epi_iff_surjective e.hom).mp inferInstance

/-! ## Two elementary linear-algebra facts -/

/-- `expTens K -` sends the identity of the coefficient module to the identity. -/
lemma expTensHom_id (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ) :
    Work.SSS.expTensHom K (𝟙 M) = 𝟙 (Work.SSS.expTens K M) := by
  apply HomologicalComplex.hom_ext
  intro j
  rw [Work.SSS.expTensHom_f, HomologicalComplex.id_f, MonoidalCategory.whiskerLeft_id]

/-- In a `ℤ`-module mapping injectively into `ℤ/2`, every element is killed by `2`. -/
lemma zsmul_two_eq_zero_of_injective {M : ModuleCat ℤ} (f : ↥M →ₗ[ℤ] ZMod 2)
    (hf : Function.Injective f) (x : ↥M) : (2 : ℤ) • x = 0 := by
  rw [two_zsmul]
  apply hf
  rw [map_add, map_zero]
  rw [← two_mul]
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2, zero_mul]

/-! ## The main computation -/

theorem homologyModTwo (X : Type) [TopologicalSpace X] (n : ℕ)
    (h1 : Subsingleton (Work.Pi6.HR ℤ X n))
    (h2 : Nonempty (Work.Pi6.HR ℤ X (n + 1) ≃ₗ[ℤ] ZMod 2)) :
    Nonempty (Work.Pi6.HR (ZMod 2) X (n + 1) ≅ ModuleCat.of (ZMod 2) (ZMod 2)) := by
  have hSE : (SESc X).ShortExact := SESc_shortExact X
  -- the identification `C_*(X;ℤ) ⊗ ℤ ≅ C_*(X;ℤ)`
  have eUnit : Work.SSS.expTens (CZ X) (ModuleCat.of ℤ ℤ) ≅ CZ X :=
    Work.SSS.expTensUnitIso (CZ X)
  have eH : ∀ k : ℕ, (SESc X).X₁.homology k ≅ (CZ X).homology k := fun k =>
    HomologicalComplex.homologyMapIso eUnit k
  haveI hCZsub : Subsingleton ↥((CZ X).homology n) := h1
  haveI hsub : Subsingleton ↥((SESc X).X₁.homology n) :=
    ⟨fun a b => (eH n).toLinearEquiv.injective (Subsingleton.elim _ _)⟩
  obtain ⟨e2⟩ := h2
  -- the two exactness statements of the long exact sequence
  have hEx2 : Function.Exact (HomologicalComplex.homologyMap (SESc X).f (n + 1)).hom
      (HomologicalComplex.homologyMap (SESc X).g (n + 1)).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hSE.homology_exact₂ (n + 1))
  have hij : (ComplexShape.down ℕ).Rel (n + 1) n := by
    rw [ComplexShape.down_Rel]
  have hEx3 : Function.Exact (HomologicalComplex.homologyMap (SESc X).g (n + 1)).hom
      (hSE.δ (n + 1) n hij).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hSE.homology_exact₃ (n + 1) n hij)
  -- `H_{n+1}` of the middle term has exponent `2` (it is `H_{n+1}(X;ℤ) ≅ ℤ/2`)
  have htwo : ∀ x : ↥((SESc X).X₂.homology (n + 1)), (2 : ℤ) • x = 0 := fun x =>
    zsmul_two_eq_zero_of_injective
      (e2.toLinearMap.comp (eH (n + 1)).toLinearEquiv.toLinearMap)
      (e2.injective.comp (eH (n + 1)).toLinearEquiv.injective) x
  -- the map `2· : H_{n+1}(X;ℤ) → H_{n+1}(X;ℤ)` is zero
  have hmu : HomologicalComplex.homologyMap (SESc X).f (n + 1) = 0 := by
    have hexp : Work.SSS.expTensHom (CZ X) twoZ
        = (2 : ℤ) • 𝟙 (Work.SSS.expTens (CZ X) (ModuleCat.of ℤ ℤ)) := by
      change Work.SSS.expTensHom (CZ X) ((2 : ℤ) • 𝟙 (ModuleCat.of ℤ ℤ))
        = (2 : ℤ) • 𝟙 (Work.SSS.expTens (CZ X) (ModuleCat.of ℤ ℤ))
      rw [expTensHom_zsmul_aux (CZ X) (2 : ℤ) (𝟙 (ModuleCat.of ℤ ℤ)),
        expTensHom_id]
    show HomologicalComplex.homologyMap (Work.SSS.expTensHom (CZ X) twoZ) (n + 1) = 0
    rw [hexp, homologyMap_zsmul_aux, HomologicalComplex.homologyMap_id]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    show (2 : ℤ) • x = 0
    exact htwo x
  -- injectivity and surjectivity of the reduction map
  have hinj : Function.Injective ⇑(HomologicalComplex.homologyMap (SESc X).g (n + 1)).hom := by
    intro x y hxy
    have hk : LinearMap.ker (HomologicalComplex.homologyMap (SESc X).g (n + 1)).hom
        = LinearMap.range (HomologicalComplex.homologyMap (SESc X).f (n + 1)).hom :=
      LinearMap.exact_iff.mp hEx2
    have hrange : LinearMap.range (HomologicalComplex.homologyMap (SESc X).f (n + 1)).hom
        = ⊥ := by
      rw [hmu, ModuleCat.hom_zero]
      exact LinearMap.range_zero
    have hmem : x - y ∈ LinearMap.ker (HomologicalComplex.homologyMap (SESc X).g (n + 1)).hom := by
      rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
    rw [hk, hrange] at hmem
    have hz : x - y = 0 := by simpa using hmem
    exact sub_eq_zero.mp hz
  have hsurj : Function.Surjective ⇑(HomologicalComplex.homologyMap (SESc X).g (n + 1)).hom := by
    intro y
    have hk : LinearMap.ker (hSE.δ (n + 1) n hij).hom
        = LinearMap.range (HomologicalComplex.homologyMap (SESc X).g (n + 1)).hom :=
      LinearMap.exact_iff.mp hEx3
    have hmem : y ∈ LinearMap.ker (hSE.δ (n + 1) n hij).hom := by
      rw [LinearMap.mem_ker]
      exact Subsingleton.elim _ _
    rw [hk] at hmem
    exact hmem
  -- the isomorphism `H_{n+1}(C_*(X;ℤ/2)) ≅ ℤ/2` over `ℤ`
  have gm : (SESc X).X₃.homology (n + 1) ≅ M2 :=
    LinearEquiv.toModuleIso
        (LinearEquiv.ofBijective (HomologicalComplex.homologyMap (SESc X).g (n + 1)).hom
          ⟨hinj, hsurj⟩).symm
      ≪≫ eH (n + 1) ≪≫ LinearEquiv.toModuleIso e2
  have eCE : C2 X ≅ (SESc X).X₃ := Work.SSS.chainCoeffExpIso (sing X) M2
  have step : (C2 X).homology (n + 1) ≅ M2 :=
    HomologicalComplex.homologyMapIso eCE (n + 1) ≪≫ gm
  have eCN : CN X ≅ C2 X :=
    Work.StemsB.SphRat.chainComplexBaseChange scZ (sing X) R2 ≪≫
      Work.StemsB.SphRat.chainComplexCoeffIso (sing X) coeffIso
  have eLet : scZ.obj ((CR X).homology (n + 1)) ≅ scZ.obj R2 :=
    ((Work.StemsB.SphRat.homologyMapBaseChange scZ (CR X) (n + 1)).some).symm
      ≪≫ HomologicalComplex.homologyMapIso eCN (n + 1) ≪≫ step ≪≫ coeffIso.symm
  exact restrictScalarsIso_aux eLet

end

end Work.Pi6.EMM2
