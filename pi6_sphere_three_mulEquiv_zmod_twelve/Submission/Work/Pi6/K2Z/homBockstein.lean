import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.SSS.ExpTensLES
import Submission.Work.SSS.singularCoeffFG
import Submission.Work.StemsB.sphRatHomology
import Submission.Work.Cohomology.singularChains_free
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

namespace Work.Pi6.K2Z

noncomputable section

/-! ## 0. Transporting exactness along additive equivalences -/

/-- Exactness is invariant under conjugation by additive equivalences. -/
lemma functionExact_congr {α β γ α' β' γ' : Type*} [AddCommMonoid α] [AddCommMonoid β]
    [AddCommMonoid γ] [AddCommMonoid α'] [AddCommMonoid β'] [AddCommMonoid γ']
    (eα : α' ≃+ α) (eβ : β' ≃+ β) (eγ : γ' ≃+ γ) (f : α →+ β) (g : β →+ γ) :
    Function.Exact f g ↔
      Function.Exact (fun x' => eβ.symm (f (eα x'))) (fun y' => eγ.symm (g (eβ y'))) := by
  have key : ∀ z : γ, eγ.symm z = 0 ↔ z = 0 := by
    intro z
    constructor
    · intro h; have := congrArg eγ h; simpa using this
    · intro h; rw [h, map_zero]
  rw [Function.Exact, Function.Exact]
  simp only [Set.mem_range]
  constructor
  · intro h y'
    rw [key, h (eβ y')]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨eα.symm x, by rw [eα.apply_symm_apply, hx, eβ.symm_apply_apply]⟩
    · rintro ⟨x', hx'⟩
      exact ⟨eα x', by rw [← hx', eβ.apply_symm_apply]⟩
  · intro h y
    have h' := h (eβ.symm y)
    rw [eβ.apply_symm_apply, key] at h'
    rw [h']
    constructor
    · rintro ⟨x', hx'⟩
      exact ⟨eα x', eβ.symm.injective hx'⟩
    · rintro ⟨x, hx⟩
      exact ⟨eα.symm x, by rw [eα.apply_symm_apply, hx]⟩

/-! ## 1. The coefficient sequence `0 → ℤ →·p ℤ → ℤ/p → 0` -/

/-- `ℤ/p` as a `ℤ`-module (restriction of scalars along `ℤ → ℤ/p`), presented so that its
underlying type is definitionally `ZMod p`. -/
abbrev Zp (p : ℕ) : ModuleCat ℤ :=
  @ModuleCat.of ℤ _ (ZMod p) _ (Module.compHom (ZMod p) (Int.castRingHom (ZMod p)))

/-- The reduction `ℤ → ℤ/p` as an additive map. -/
def redAddHom (p : ℕ) : (↥(𝟙_ (ModuleCat ℤ))) →ₙ+ (↥(Zp p)) where
  toFun := fun z => (z : ZMod p)
  map_add' := fun x y => Int.cast_add x y

/-- The reduction `ℤ → ℤ/p` as a map of `ℤ`-modules. -/
def redLin (p : ℕ) : @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) (↥(𝟙_ (ModuleCat ℤ))) (↥(Zp p)) _ _
    (𝟙_ (ModuleCat ℤ)).isModule (Zp p).isModule :=
  @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) _ _ _ _ (𝟙_ (ModuleCat ℤ)).isModule (Zp p).isModule
    (redAddHom p) (fun n x => by
      show ((n * x : ℤ) : ZMod p) = (n : ZMod p) * ((x : ℤ) : ZMod p)
      rw [Int.cast_mul])

/-- The reduction `ℤ → ℤ/p` as a morphism of `ℤ`-modules. -/
def redMap (p : ℕ) : (𝟙_ (ModuleCat ℤ)) ⟶ Zp p :=
  @ModuleCat.ofHom ℤ _ (↥(𝟙_ (ModuleCat ℤ))) (↥(Zp p)) _ _ _ (Zp p).isModule (redLin p)

/-- Multiplication by `p` on `ℤ`. -/
abbrev coeffF (p : ℕ) : (𝟙_ (ModuleCat ℤ)) ⟶ (𝟙_ (ModuleCat ℤ)) :=
  (p : ℤ) • 𝟙 (𝟙_ (ModuleCat ℤ))

lemma coeffF_apply (p : ℕ) (z : ℤ) : (coeffF p).hom z = (p : ℤ) * z := by
  rw [coeffF, ModuleCat.hom_smul]
  simp [zsmul_eq_mul]

lemma redMap_apply (p : ℕ) (z : ℤ) : (redMap p).hom z = (z : ZMod p) := rfl

lemma zeroHom_apply (p : ℕ) (z : ℤ) :
    (ModuleCat.Hom.hom (0 : (𝟙_ (ModuleCat ℤ)) ⟶ Zp p)) z = 0 := rfl

lemma natCast_prime_zmod_zero (p : ℕ) : ((p : ℤ) : ZMod p) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma coeffF_comp_redMap (p : ℕ) : (coeffF p) ≫ (redMap p) = 0 := by
  have hp0 := natCast_prime_zmod_zero p
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ (fun z => ?_)
  rw [ModuleCat.comp_apply, coeffF_apply, redMap_apply, zeroHom_apply, Int.cast_mul, hp0, zero_mul]

/-- The coefficient short complex `0 → ℤ →·p ℤ → ℤ/p → 0` as a short complex of `ℤ`-modules. -/
abbrev coeffSES (p : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (coeffF p) (redMap p) (coeffF_comp_redMap p)

lemma coeffSES_f (p : ℕ) : (coeffSES p).f = coeffF p := rfl
lemma coeffSES_g (p : ℕ) : (coeffSES p).g = redMap p := rfl

theorem coeffSES_shortExact (p : ℕ) (hp : p.Prime) : (coeffSES p).ShortExact := by
  have hf : ⇑(ConcreteCategory.hom (coeffSES p).f) = fun x : ℤ => (p : ℤ) * x := by
    funext x; exact coeffF_apply p x
  have hg : ⇑(ConcreteCategory.hom (coeffSES p).g) = fun y : ℤ => (y : ZMod p) := by
    funext y; exact redMap_apply p y
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact, hf, hg]
    show ∀ y : ℤ, ((y : ZMod p) = 0) ↔ ∃ x : ℤ, (p : ℤ) * x = y
    intro y
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · intro h
      obtain ⟨x, hx⟩ := dvd_def.mp h
      exact ⟨x, hx.symm⟩
    · rintro ⟨x, hx⟩
      exact dvd_def.mpr ⟨x, hx.symm⟩
  · rw [ModuleCat.mono_iff_injective]
    intro x y h
    have h' : (coeffF p).hom x = (coeffF p).hom y := h
    rw [coeffF_apply, coeffF_apply] at h'
    exact mul_left_cancel₀ (M₀ := ℤ) (by exact_mod_cast hp.ne_zero) h'
  · rw [ModuleCat.epi_iff_surjective]
    intro y
    obtain ⟨x, hx⟩ := ZMod.intCast_surjective (n := p) y
    exact ⟨x, by rw [← hx]; exact (redMap_apply p x).symm⟩

end

end Work.Pi6.K2Z

namespace Work.Pi6.K2Z

noncomputable section

/-! ## 2. The singular chains and the Bockstein short exact sequence -/

/-- The singular simplicial set of `X`. -/
abbrev bS (X : Type) [TopologicalSpace X] : SSet := TopCat.toSSet.obj (TopCat.of X)

/-- The integral singular chains of `X`. -/
abbrev bK (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat ℤ) ℕ :=
  Work.Cohomology.singularChains ℤ (TopCat.of X)

/-- The mod-`p` singular chains of `X`. -/
abbrev bL (p : ℕ) (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat (ZMod p)) ℕ :=
  (bS X).chainComplex (ModuleCat.of (ZMod p) (ZMod p))

/-- The restricted-scalars functor `(ℤ/p)`-modules → `ℤ`-modules. -/
abbrev rsf (p : ℕ) : ModuleCat (ZMod p) ⥤ ModuleCat ℤ :=
  ModuleCat.restrictScalars (Int.castRingHom (ZMod p))

/-- The Bockstein short exact sequence of chain complexes
`0 → C_*(X;ℤ) →·p C_*(X;ℤ) → C_*(X;ℤ/p) → 0` (the last term being the naive tensor
`C_*(X;ℤ) ⊗ ℤ/p`). -/
abbrev bShort (p : ℕ) (X : Type) [TopologicalSpace X] :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) where
  X₁ := Work.SSS.expTens (bK X) (𝟙_ (ModuleCat ℤ))
  X₂ := Work.SSS.expTens (bK X) (𝟙_ (ModuleCat ℤ))
  X₃ := Work.SSS.expTens (bK X) (Zp p)
  f := Work.SSS.expTensHom (bK X) (coeffF p)
  g := Work.SSS.expTensHom (bK X) (redMap p)
  zero := (Work.SSS.expTensShort (bK X) (coeffSES p)).zero

theorem bShort_shortExact (p : ℕ) (hp : p.Prime) (X : Type) [TopologicalSpace X] :
    (bShort p X).ShortExact := by
  haveI hfree : ∀ n, Module.Free ℤ (((bK X).X n)) :=
    fun n => Work.Cohomology.singularChains_free (TopCat.of X) n
  exact Work.SSS.expTensShort_shortExact (coeffSES p) (coeffSES_shortExact p hp)
    (fun n => Module.Flat.of_free)

/-! ### 3. Elementary lemmas about scalar multiples -/

/-- Whiskering on the left commutes with integer scalar multiples. -/
lemma whiskerLeft_zsmul {M N : ModuleCat ℤ} (r : ℤ) (f : M ⟶ N) (X : ModuleCat ℤ) :
    X ◁ (r • f) = r • (X ◁ f) :=
  Functor.map_zsmul (F := MonoidalCategory.tensorLeft X) (r := r) (f := f)

/-- Whiskering on the right commutes with integer scalar multiples. -/
lemma whiskerRight_zsmul {M N : ModuleCat ℤ} (r : ℤ) (f : M ⟶ N) (X : ModuleCat ℤ) :
    (r • f) ▷ X = r • (f ▷ X) :=
  Functor.map_zsmul (F := MonoidalCategory.tensorRight X) (r := r) (f := f)

/-- The `n`-th homology of the scalar multiple of the identity is the scalar multiple of the
identity. -/
lemma homologyMap_smul_id (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (a : ℤ) :
    homologyMap (a • 𝟙 K) n = a • 𝟙 (K.homology n) := by
  have h : homologyMap (a • 𝟙 K) n = a • homologyMap (𝟙 K) n :=
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map_smul a (𝟙 K)
  rw [HomologicalComplex.homologyMap_id] at h
  exact h

/-- Evaluating a scalar multiple of the identity. -/
lemma smul_id_apply {M : ModuleCat ℤ} (a : ℤ) (z : ↥M) :
    ((a • 𝟙 M).hom) z = a • z := rfl

/-! ### 4. The unit iso intertwines multiplication by `p` -/

/-- The unit isomorphism `C_*(X) ⊗ ℤ ≅ C_*(X)` intertwines `p`-multiplication. -/
lemma expTensHom_coeffF (p : ℕ) (X : Type) [TopologicalSpace X] :
    Work.SSS.expTensHom (bK X) (coeffF p) ≫ (Work.SSS.expTensUnitIso (bK X)).hom =
      (Work.SSS.expTensUnitIso (bK X)).hom ≫ ((p : ℤ) • 𝟙 (bK X)) := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, Work.SSS.expTensHom_f, HomologicalComplex.smul_f_apply,
    HomologicalComplex.id_f]
  rw [show (Work.SSS.expTensUnitIso (bK X)).hom.f n = (ρ_ ((bK X).X n)).hom from rfl]
  rw [whiskerLeft_zsmul, MonoidalCategory.whiskerLeft_id]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]

/-! ### 5. The isomorphisms relating the Bockstein sequence to the expected one -/

/-- The unit isomorphism `C_*(X;ℤ) ⊗ ℤ ≅ C_*(X;ℤ)` on homology. -/
abbrev eA (p : ℕ) (X : Type) [TopologicalSpace X] (n : ℕ) :
    ((bShort p X).X₁.homology n) ≅ ((bK X).homology n) :=
  (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
    (Work.SSS.expTensUnitIso (bK X))

/-- The identification of `H_n(C_*(X;ℤ) ⊗ ℤ/p)` with `H_n(X;ℤ/p)`. -/
abbrev eB (p : ℕ) (X : Type) [TopologicalSpace X] (n : ℕ) :
    ((bShort p X).X₃.homology n) ≅ (rsf p).obj ((bL p X).homology n) :=
  (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
      ((Work.SSS.chainCoeffExpIso (bS X) (Zp p)).symm) ≪≫
    (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
      ((Work.StemsB.SphRat.chainComplexBaseChange (rsf p) (bS X)
        (ModuleCat.of (ZMod p) (ZMod p))).symm) ≪≫
    (Work.StemsB.SphRat.homologyMapBaseChange (rsf p) (bL p X) n).some

/-- `eB` as an additive equivalence into `H_n(X;ℤ/p)`. -/
abbrev eBadd (p : ℕ) (X : Type) [TopologicalSpace X] (n : ℕ) :
    ((bShort p X).X₃.homology n) ≃+ Work.Pi6.HR (ZMod p) X n :=
  (eB p X n).toLinearEquiv.toAddEquiv.trans (AddEquiv.refl (↥(Work.Pi6.HR (ZMod p) X n)))

/-! ### 6. The Bockstein maps -/

/-- The reduction `H_n(X;ℤ) → H_n(X;ℤ/p)`. -/
def bockRed (p : ℕ) (X : Type) [TopologicalSpace X] (n : ℕ) :
    Work.Pi6.HR ℤ X n →+ Work.Pi6.HR (ZMod p) X n :=
  (eBadd p X n).toAddMonoidHom.comp
    (((homologyMap (bShort p X).g n).hom.toAddMonoidHom).comp
      ((eA p X n).toLinearEquiv.toAddEquiv.symm.toAddMonoidHom))

/-- The Bockstein connecting map `H_{n+1}(X;ℤ/p) → H_n(X;ℤ)`. -/
def bockDel (p : ℕ) (hp : p.Prime) (X : Type) [TopologicalSpace X] (n : ℕ) :
    Work.Pi6.HR (ZMod p) X (n + 1) →+ Work.Pi6.HR ℤ X n :=
  ((eA p X n).toLinearEquiv.toAddEquiv.toAddMonoidHom).comp
    ((((bShort_shortExact p hp X).δ (n + 1) n
        ((ComplexShape.down_Rel ℕ (n + 1) n).mpr rfl)).hom.toAddMonoidHom).comp
      ((eBadd p X (n + 1)).symm.toAddMonoidHom))

/-! ### 7. Exactness -/

/-- The unit isomorphism intertwines multiplication by `p` on homology. -/
lemma eA_conj (p : ℕ) (X : Type) [TopologicalSpace X] (n : ℕ)
    (y : ((bShort p X).X₁.homology n)) :
    (eA p X n).toLinearEquiv ((homologyMap (bShort p X).f n).hom y) =
      (p : ℤ) • ((eA p X n).toLinearEquiv y) := by
  have hcc : homologyMap (Work.SSS.expTensUnitIso (bK X)).hom n = (eA p X n).hom := rfl
  have hA : homologyMap (bShort p X).f n ≫ homologyMap (Work.SSS.expTensUnitIso (bK X)).hom n =
      homologyMap ((bShort p X).f ≫ (Work.SSS.expTensUnitIso (bK X)).hom) n :=
    (HomologicalComplex.homologyMap_comp (φ := (bShort p X).f)
      (ψ := (Work.SSS.expTensUnitIso (bK X)).hom) n).symm
  have hC : homologyMap ((bShort p X).f ≫ (Work.SSS.expTensUnitIso (bK X)).hom) n =
      homologyMap ((Work.SSS.expTensUnitIso (bK X)).hom ≫ ((p : ℤ) • 𝟙 (bK X))) n :=
    congrArg (fun φ => homologyMap φ n) (expTensHom_coeffF p X)
  have hB : homologyMap ((Work.SSS.expTensUnitIso (bK X)).hom ≫ ((p : ℤ) • 𝟙 (bK X))) n =
      homologyMap (Work.SSS.expTensUnitIso (bK X)).hom n ≫
        homologyMap ((p : ℤ) • 𝟙 (bK X)) n :=
    HomologicalComplex.homologyMap_comp _ _ n
  have hcomp := hA.trans (hC.trans hB)
  have h2 := congrArg (fun (φ : ((bShort p X).X₁.homology n) ⟶ ((bK X).homology n)) =>
      φ.hom y) hcomp
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h2
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h2
  rw [homologyMap_smul_id] at h2
  rw [smul_id_apply] at h2
  change (ModuleCat.Hom.hom (eA p X n).hom)
      ((ModuleCat.Hom.hom (homologyMap (bShort p X).f n)) y) =
    (p : ℤ) • (ModuleCat.Hom.hom (eA p X n).hom) y
  rw [← hcc]
  exact h2

lemma bockRed_exact (p : ℕ) (hp : p.Prime) (X : Type) [TopologicalSpace X] (n : ℕ) :
    Function.Exact (fun x : Work.Pi6.HR ℤ X n => (p : ℤ) • x) ⇑(bockRed p X n) := by
  have hex2 : Function.Exact (homologyMap (bShort p X).f n).hom
      (homologyMap (bShort p X).g n).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      ((bShort_shortExact p hp X).homology_exact₂ n)
  have h1 := (functionExact_congr
    (eα := (eA p X n).toLinearEquiv.toAddEquiv.symm)
    (eβ := (eA p X n).toLinearEquiv.toAddEquiv.symm)
    (eγ := (eBadd p X n).symm)
    (f := (homologyMap (bShort p X).f n).hom.toAddMonoidHom)
    (g := (homologyMap (bShort p X).g n).hom.toAddMonoidHom)).mp hex2
  rw [show (fun x' => (eA p X n).toLinearEquiv.toAddEquiv.symm.symm
        (((ModuleCat.Hom.hom (homologyMap (bShort p X).f n)).toAddMonoidHom)
          ((eA p X n).toLinearEquiv.toAddEquiv.symm x')))
      = (fun x : Work.Pi6.HR ℤ X n => (p : ℤ) • x) from by
    funext x'
    change (eA p X n).toLinearEquiv
      ((homologyMap (bShort p X).f n).hom ((eA p X n).toLinearEquiv.symm x')) =
        (p : ℤ) • x'
    rw [eA_conj p X n ((eA p X n).toLinearEquiv.symm x')]
    simp only [LinearEquiv.apply_symm_apply]] at h1
  rw [show (fun y' => (eBadd p X n).symm.symm
        (((ModuleCat.Hom.hom (homologyMap (bShort p X).g n)).toAddMonoidHom)
          ((eA p X n).toLinearEquiv.toAddEquiv.symm y')))
      = ⇑(bockRed p X n) from by funext y'; rfl] at h1
  exact h1

lemma bockRed_del_exact (p : ℕ) (hp : p.Prime) (X : Type) [TopologicalSpace X] (n : ℕ) :
    Function.Exact ⇑(bockRed p X (n + 1)) ⇑(bockDel p hp X n) := by
  have hij : (ComplexShape.down ℕ).Rel (n + 1) n := (ComplexShape.down_Rel ℕ (n + 1) n).mpr rfl
  have hex3 : Function.Exact (homologyMap (bShort p X).g (n + 1)).hom
      ((bShort_shortExact p hp X).δ (n + 1) n hij).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      ((bShort_shortExact p hp X).homology_exact₃ (n + 1) n hij)
  have h1 := (functionExact_congr
    (eα := (eA p X (n + 1)).toLinearEquiv.toAddEquiv.symm)
    (eβ := (eBadd p X (n + 1)).symm)
    (eγ := (eA p X n).toLinearEquiv.toAddEquiv.symm)
    (f := (homologyMap (bShort p X).g (n + 1)).hom.toAddMonoidHom)
    (g := ((bShort_shortExact p hp X).δ (n + 1) n hij).hom.toAddMonoidHom)).mp hex3
  rw [show (fun x' => (eBadd p X (n + 1)).symm.symm
        (((ModuleCat.Hom.hom (homologyMap (bShort p X).g (n + 1))).toAddMonoidHom)
          ((eA p X (n + 1)).toLinearEquiv.toAddEquiv.symm x')))
      = ⇑(bockRed p X (n + 1)) from by funext x'; rfl] at h1
  rw [show (fun y' => (eA p X n).toLinearEquiv.toAddEquiv.symm.symm
        (((ModuleCat.Hom.hom ((bShort_shortExact p hp X).δ (n + 1) n hij)).toAddMonoidHom)
          ((eBadd p X (n + 1)).symm y')))
      = ⇑(bockDel p hp X n) from by funext y'; rfl] at h1
  exact h1

lemma bockDel_exact (p : ℕ) (hp : p.Prime) (X : Type) [TopologicalSpace X] (n : ℕ) :
    Function.Exact ⇑(bockDel p hp X n) (fun x : Work.Pi6.HR ℤ X n => (p : ℤ) • x) := by
  have hij : (ComplexShape.down ℕ).Rel (n + 1) n := (ComplexShape.down_Rel ℕ (n + 1) n).mpr rfl
  have hex1 : Function.Exact ((bShort_shortExact p hp X).δ (n + 1) n hij).hom
      (homologyMap (bShort p X).f n).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      ((bShort_shortExact p hp X).homology_exact₁ (n + 1) n hij)
  have h1 := (functionExact_congr
    (eα := (eBadd p X (n + 1)).symm)
    (eβ := (eA p X n).toLinearEquiv.toAddEquiv.symm)
    (eγ := (eA p X n).toLinearEquiv.toAddEquiv.symm)
    (f := ((bShort_shortExact p hp X).δ (n + 1) n hij).hom.toAddMonoidHom)
    (g := (homologyMap (bShort p X).f n).hom.toAddMonoidHom)).mp hex1
  rw [show (fun x' => (eA p X n).toLinearEquiv.toAddEquiv.symm.symm
        (((ModuleCat.Hom.hom ((bShort_shortExact p hp X).δ (n + 1) n hij)).toAddMonoidHom)
          ((eBadd p X (n + 1)).symm x')))
      = ⇑(bockDel p hp X n) from by funext x'; rfl] at h1
  rw [show (fun y' => (eA p X n).toLinearEquiv.toAddEquiv.symm.symm
        (((ModuleCat.Hom.hom (homologyMap (bShort p X).f n)).toAddMonoidHom)
          ((eA p X n).toLinearEquiv.toAddEquiv.symm y')))
      = (fun x : Work.Pi6.HR ℤ X n => (p : ℤ) • x) from by
    funext y'
    change (eA p X n).toLinearEquiv
      ((homologyMap (bShort p X).f n).hom ((eA p X n).toLinearEquiv.symm y')) =
        (p : ℤ) • y'
    rw [eA_conj p X n ((eA p X n).toLinearEquiv.symm y')]
    simp only [LinearEquiv.apply_symm_apply]] at h1
  exact h1

/-- **The Bockstein long exact sequence.**  There are additive maps

* `red n : Hₙ(X;ℤ) →+ Hₙ(X;ℤ/p)`, the reduction mod `p`;
* `del n : Hₙ₊₁(X;ℤ/p) →+ Hₙ(X;ℤ)`, the Bockstein connecting map,

making `Hₙ₊₁(X;ℤ) --·p--> Hₙ₊₁(X;ℤ) --red--> Hₙ₊₁(X;ℤ/p) --del--> Hₙ(X;ℤ) --·p--> Hₙ(X;ℤ)`
exact at all three displayed spots, for every space `X` and every `n`. -/
theorem homBockstein (p : ℕ) (hp : p.Prime) :
    ∃ (red : ∀ {X : Type} [TopologicalSpace X] (n : ℕ), Work.Pi6.HR ℤ X n →+ Work.Pi6.HR (ZMod p) X n)
      (del : ∀ {X : Type} [TopologicalSpace X] (n : ℕ), Work.Pi6.HR (ZMod p) X (n + 1) →+ Work.Pi6.HR ℤ X n),
      (∀ (X : Type) [TopologicalSpace X] (n : ℕ),
        Function.Exact (fun x : Work.Pi6.HR ℤ X n => (p : ℤ) • x) ⇑(red (X := X) n)) ∧
      (∀ (X : Type) [TopologicalSpace X] (n : ℕ),
        Function.Exact ⇑(red (X := X) (n + 1)) ⇑(del (X := X) n)) ∧
      (∀ (X : Type) [TopologicalSpace X] (n : ℕ),
        Function.Exact ⇑(del (X := X) n) (fun x : Work.Pi6.HR ℤ X n => (p : ℤ) • x)) :=
  ⟨fun {X} _ n => bockRed p X n, fun {X} _ n => bockDel p hp X n,
    (fun X _ n => bockRed_exact p hp X n),
    (fun X _ n => bockRed_del_exact p hp X n),
    (fun X _ n => bockDel_exact p hp X n)⟩

end

end Work.Pi6.K2Z
