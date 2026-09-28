import Mathlib
import Submission.Work.Kunneth.Chapter
import Submission.Work.Serre.relEZDefs
import Submission.Work.Serre.relEZ_degreewise
import Submission.Work.Serre.relEZ_tpMapLin_exact
import Submission.Work.Serre.relEZ_tpMapLin_injective
import Submission.Work.Serre.relEZ_ezMapT_naturality
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.cokernelComponent
import Submission.Work.Kunneth.ezaw_ind_nat
import Submission.Work.Kunneth.ez_aw_homotopyT
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# The relative Eilenberg–Zilber homology isomorphism

The target `Work.Serre.relEZ_homology_iso` states that for a space `W` and a pair `(P,Q)` the
Koszul tensor product `C_*(W) ⊗_ℤ C_*(P,Q)` has the same homology as the relative chain complex of
the product pair `(W × P, W × Q)`.

The proof is the classical five-lemma argument, done twice, using the skeleton

* `S'` — the (cokernel) short exact sequence `0 ⟶ C(W)⊗C(Q) ⟶ C(W)⊗C(P) ⟶ coker ⟶ 0` of the
  tensor product of `C_*(W)` with the pair sequence of `(P,Q)` (projective, hence flat, so
  `tpC C -` is exact);
* `S` — the "relative Eilenberg–Zilber" short complex
  `0 ⟶ tpC C (C(Q)) ⟶ tpC C (C(P)) ⟶ tpC C (C(P,Q)) ⟶ 0`, which is short exact by the degreewise
  computation (flatness on the left, right exactness on the right);
* `S₂` — the pair sequence `0 ⟶ C(W×Q) ⟶ C(W×P) ⟶ C_*(W×P, W×Q) ⟶ 0` of the product.

The shuffle map `ezMapT` gives

* `φ : S' ⟶ S₂`, with `φ.τ₁` and `φ.τ₂` quasi-isomorphisms by Eilenberg–Zilber, hence `φ.τ₃` is a
  quasi-isomorphism by the five lemma (`HomologicalComplex.HomologySequence.quasiIso_τ₃`);
* `ψ : S' ⟶ S` induced by the identity on the first two terms, again a quasi-isomorphism on `τ₃`,
  which identifies the homology of the cokernel with that of `tpC C (C(P,Q))`.

Combining the two isomorphisms on homology gives the claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct MonoidalCategory

namespace Work.Serre

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

open Work.Kunneth in
/-- **The singular chains of a space are degreewise flat over `ℤ`.** -/
theorem flat_singularChains (X : TopCat) (n : ℕ) :
    Module.Flat ℤ ↥((Work.Cohomology.singularChains ℤ X).X n) := by
  haveI := Work.Cohomology.projective_singularChains X n
  exact Module.Flat.of_projective

/-- **The Eilenberg–Zilber shuffle map for topological spaces is a quasi-isomorphism.** -/
theorem quasiIso_ezMapT (X Y : TopCat) : QuasiIso (Work.Kunneth.ezMapT X Y) := by
  refine ⟨fun n => ?_⟩
  rw [quasiIsoAt_iff_isIso_homologyMap]
  obtain ⟨H₁⟩ := Work.Kunneth.ez_aw_homotopyT X Y
  obtain ⟨H₂⟩ := Work.Kunneth.aw_ez_homotopyT X Y
  let e : ((Work.Kunneth.tChain (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)).homology n) ≅
      ((Work.Kunneth.sChain (TopCat.toSSet.obj (X ⊗ Y))).homology n) :=
    { hom := homologyMap (Work.Kunneth.ezMapT X Y) n
      inv := homologyMap (Work.Kunneth.awMapT X Y) n
      hom_inv_id := by
        rw [← homologyMap_comp, H₁.homologyMap_eq n, homologyMap_id]
      inv_hom_id := by
        rw [← homologyMap_comp, H₂.homologyMap_eq n, homologyMap_id] }
  exact e.isIso_hom

/-! ## Degreewise facts about the cokernel projection -/

/-- **The projection to a cokernel of chain complexes is degreewise surjective.** -/
theorem cokernelπ_component_surjective {A B : ChainComplex (ModuleCat ℤ) ℕ} (f : A ⟶ B) (k : ℕ) :
    Function.Surjective (((cokernel.π f).f k).hom) := by
  intro y
  obtain ⟨u, hu⟩ := (ModuleCat.epi_iff_surjective _).mp
    (inferInstance : Epi (cokernel.π (f.f k))) ((Work.Cohomology.cokernelComponentIso f k).hom y)
  refine ⟨u, ?_⟩
  have hc : (Work.Cohomology.cokernelComponentIso f k).hom (((cokernel.π f).f k).hom u)
      = (cokernel.π (f.f k)).hom u := by
    have h := congrArg (fun (g : B.X k ⟶ cokernel (f.f k)) => ModuleCat.Hom.hom g u)
      (Work.Cohomology.cokernelComponentIso_canon f k)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  have h2 : (Work.Cohomology.cokernelComponentIso f k).hom (((cokernel.π f).f k).hom u)
      = (Work.Cohomology.cokernelComponentIso f k).hom y := by rw [hc, hu]
  exact (ModuleCat.mono_iff_injective _).mp inferInstance h2

/-- Degreewise injectivity of the inclusion of singular chains of a subspace. -/
theorem inclChains_component_injective (X : TopCat) (A : Set X) (k : ℕ) :
    Function.Injective (((Work.Cohomology.inclChains X A).f k).hom) := by
  have hspec := Work.Cohomology.chainRetract_spec ℤ X A k
  have key : ∀ x, (Work.Cohomology.chainRetract ℤ X A k).hom
      (((Work.Cohomology.inclChains X A).f k).hom x) = x := by
    intro x
    exact congrArg (fun g => ModuleCat.Hom.hom g x) hspec
  intro x y hxy
  have hx := key x
  have hy := key y
  rw [hxy] at hx
  exact hx.symm.trans hy

/-! ## The homeomorphism `W × ↥Q ≃ₜ ↥{x : W × P | x.2 ∈ Q}` -/

/-- The canonical homeomorphism `W × ↥Q ≃ₜ ↥{x : W × P | x.2 ∈ Q}`. -/
def prodSubtypeHomeo (W P : Type) [TopologicalSpace W] [TopologicalSpace P] (Q : Set P) :
    (W × ↥Q) ≃ₜ ↥{x : W × P | x.2 ∈ Q} where
  toFun z := ⟨(z.1, z.2.1), z.2.2⟩
  invFun z := (z.1.1, ⟨z.1.2, z.2⟩)
  left_inv z := rfl
  right_inv z := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The `TopCat` isomorphism induced by `prodSubtypeHomeo`. -/
def prodSubtypeTopIso (W P : Type) [TopologicalSpace W] [TopologicalSpace P] (Q : Set P) :
    TopCat.of (W × ↥Q) ≅ TopCat.of ↥{x : W × P | x.2 ∈ Q} :=
  TopCat.isoOfHomeo (prodSubtypeHomeo W P Q)

/-- The two inclusions of `W × ↥Q` into `W × P` agree. -/
theorem tensorHom_id_incl_eq (W P : Type) [TopologicalSpace W] [TopologicalSpace P] (Q : Set P) :
    MonoidalCategoryStruct.tensorHom (𝟙 (TopCat.of W))
        (Work.Cohomology.subtypeIncl (TopCat.of P) Q)
      = (prodSubtypeTopIso W P Q).hom ≫
        Work.Cohomology.subtypeIncl (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q} := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  simp only [TopCat.tensor_apply, TopCat.isoOfHomeo_hom, TopCat.ofHom_comp, TopCat.hom_ofHom,
    TopCat.ofHom_apply, TopCat.hom_comp, TopCat.id_app, ContinuousMap.comp_apply,
    Work.Cohomology.subtypeIncl, prodSubtypeTopIso, prodSubtypeHomeo]
  rfl

/-- `chainMap` of the identity, in the form of the simplicial chain map. -/
theorem chainMap_id_eq (X : TopCat) :
    SSet.chainComplexMap (TopCat.toSSet.map (𝟙 X)) Work.Kunneth.zz
      = 𝟙 (Work.Cohomology.singularChains ℤ X) :=
  Work.Cohomology.chainMap_id' X

/-! ## Surjectivity of the tensor product with a chain map -/

/-- **Surjectivity of the tensor product of a surjective chain map with a complex.** -/
theorem relEZ_tpMapLin_surjective (C : ChainComplex (ModuleCat ℤ) ℕ)
    {A B : ChainComplex (ModuleCat ℤ) ℕ} (f : A ⟶ B) (hf : ∀ n, Function.Surjective (f.f n).hom)
    (n : ℕ) : Function.Surjective
      (Work.Kunneth.tpMapLin C C A B (CategoryTheory.CategoryStruct.id C) f n) := by
  intro w
  have hcomp : ∀ pq : Work.Kunneth.tpIdx n, ∃ y : Work.Kunneth.tpSummand C A pq.1.1 pq.1.2,
      TensorProduct.map (LinearMap.id : ↥(C.X pq.1.1) →ₗ[ℤ] ↥(C.X pq.1.1))
        ((f.f pq.1.2).hom) y = w pq := by
    intro pq
    rw [← LinearMap.lTensor_def]
    exact LinearMap.lTensor_surjective _ (hf pq.1.2) (w pq)
  choose y hy using hcomp
  refine ⟨∑ pq, Work.Kunneth.tpLof C A n pq (y pq), ?_⟩
  rw [map_sum]
  rw [show (∑ pq : Work.Kunneth.tpIdx n,
        Work.Kunneth.tpMapLin C C A B (CategoryTheory.CategoryStruct.id C) f n
          (Work.Kunneth.tpLof C A n pq (y pq)))
      = ∑ pq : Work.Kunneth.tpIdx n, Work.Kunneth.tpLof C B n pq (w pq) from
    Finset.sum_congr rfl (fun pq _ => by
      rw [Work.Kunneth.tpMapLin_tpLof]
      congr 1
      rw [HomologicalComplex.id_f, ModuleCat.hom_id]
      exact hy pq)]
  exact Work.Serre.sum_lof_component w

/-! ## The two short exact sequences and the five lemma -/

/-- **The tensor product with a degreewise flat complex preserves the cokernel short exact
sequence.** -/
theorem tpMap_relChains_shortExact (C : ChainComplex (ModuleCat ℤ) ℕ)
    (hC : ∀ n, Module.Flat ℤ ↥(C.X n))
    {A B : ChainComplex (ModuleCat ℤ) ℕ} (f : A ⟶ B) (hf : ∀ n, Function.Injective (f.f n).hom)
    (hg : ∀ n, Function.Surjective (((cokernel.π f).f n).hom)) :
    (ShortComplex.mk (Work.Kunneth.tpMap C C A B (𝟙 C) f)
      (Work.Kunneth.tpMap C C B (cokernel f) (𝟙 C) (cokernel.π f))
      (by rw [Work.Kunneth.tpMap_comp, Category.id_comp, cokernel.condition, tpMap_zero_left])
      ).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun q => ?_)
  apply ModuleCat.shortComplex_shortExact
  · simp only [ShortComplex.map_f, ShortComplex.map_g, HomologicalComplex.eval_map,
      Work.Kunneth.tpMap_f, ModuleCat.hom_ofHom]
    exact relEZ_tpMapLin_exact C hC f q
  · simp only [ShortComplex.map_f, HomologicalComplex.eval_map, Work.Kunneth.tpMap_f,
      ModuleCat.hom_ofHom]
    exact relEZ_tpMapLin_injective C hC f hf q
  · simp only [ShortComplex.map_g, HomologicalComplex.eval_map, Work.Kunneth.tpMap_f,
      ModuleCat.hom_ofHom]
    exact relEZ_tpMapLin_surjective C (cokernel.π f) hg q

/-- The cokernel short exact sequence of `tpMap C C (𝟙 C) f` is short exact when that map is a
monomorphism. -/
theorem cokernel_tpMap_shortExact (C A B : ChainComplex (ModuleCat ℤ) ℕ) (f : A ⟶ B)
    (hmono : Mono (Work.Kunneth.tpMap C C A B (𝟙 C) f)) :
    (ShortComplex.mk (Work.Kunneth.tpMap C C A B (𝟙 C) f)
      (cokernel.π (Work.Kunneth.tpMap C C A B (𝟙 C) f))
      (cokernel.condition _)).ShortExact :=
  { exact := ShortComplex.exact_cokernel _
    mono_f := hmono
    epi_g := inferInstance }

/-- **The relative Eilenberg–Zilber homology isomorphism.** -/
theorem relEZ_homology_iso_core (W : Type) [TopologicalSpace W] (P : Type) [TopologicalSpace P]
    (Q : Set P) :
    ∀ n : ℕ, Nonempty
      (((Work.Kunneth.tpC (Work.Cohomology.singularChains ℤ (TopCat.of W))
          (Work.Cohomology.relChains (TopCat.of P) Q)).homology n)
        ≅ ((Work.Cohomology.relChains (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q}).homology n)) := by
  intro n
  let X : TopCat := TopCat.of W
  let Y : TopCat := TopCat.of P
  let Q' : TopCat := TopCat.of ↥Q
  let Z : TopCat := TopCat.of (W × P)
  let WQ : Set (W × P) := {x : W × P | x.2 ∈ Q}
  let C : ChainComplex (ModuleCat ℤ) ℕ := Work.Cohomology.singularChains ℤ X
  have hflat : ∀ k, Module.Flat ℤ ↥(C.X k) := fun k => flat_singularChains X k
  let f0 : Work.Cohomology.singularChains ℤ Q' ⟶ Work.Cohomology.singularChains ℤ Y :=
    Work.Cohomology.inclChains Y Q
  have hf0 : ∀ k, Function.Injective ((f0.f k).hom) := inclChains_component_injective Y Q
  have hf0s : ∀ k, Function.Surjective (((cokernel.π f0).f k).hom) :=
    cokernelπ_component_surjective f0
  -- the cokernel short exact sequence of the tensor product with the pair sequence of `(P,Q)`
  let Dtp : Work.Kunneth.tpC C (Work.Cohomology.singularChains ℤ Q') ⟶
      Work.Kunneth.tpC C (Work.Cohomology.singularChains ℤ Y) :=
    Work.Kunneth.tpMap C C (Work.Cohomology.singularChains ℤ Q')
      (Work.Cohomology.singularChains ℤ Y) (𝟙 C) f0
  let Sp : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk Dtp (cokernel.π Dtp) (cokernel.condition Dtp)
  have hmono : Mono Dtp := by
    refine mono_of_mono_f Dtp (fun k => ?_)
    rw [ModuleCat.mono_iff_injective]
    exact relEZ_tpMapLin_injective C hflat f0 hf0 k
  have hSp : Sp.ShortExact := cokernel_tpMap_shortExact C _ _ f0 hmono
  -- the relative Eilenberg-Zilber short complex
  let DtpD : Work.Kunneth.tpC C (Work.Cohomology.singularChains ℤ Y) ⟶
      Work.Kunneth.tpC C (cokernel f0) :=
    Work.Kunneth.tpMap C C (Work.Cohomology.singularChains ℤ Y) (cokernel f0) (𝟙 C)
      (cokernel.π f0)
  let S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk Dtp DtpD (by
      rw [Work.Kunneth.tpMap_comp, Category.id_comp, cokernel.condition, tpMap_zero_left])
  have hS : S.ShortExact := tpMap_relChains_shortExact C hflat f0 hf0 hf0s
  -- the pair sequence of the product
  let S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) := Work.Cohomology.hPairShort Z WQ
  have hS₂ : S₂.ShortExact := Work.Cohomology.hPairShort_shortExact Z WQ
  -- the Eilenberg-Zilber comparison
  let τ₁ : Sp.X₁ ⟶ S₂.X₁ := Work.Kunneth.ezMapT X Q' ≫
    Work.Cohomology.chainMap ℤ (TopCat.of (W × ↥Q)) (TopCat.of ↥WQ) (prodSubtypeTopIso W P Q).hom
  let τ₂ : Sp.X₂ ⟶ S₂.X₂ := Work.Kunneth.ezMapT X Y
  have hcomm₁₂ : τ₁ ≫ S₂.f = Sp.f ≫ τ₂ := by
    have hnat := relEZ_ezMapT_naturality X Q' X Y (𝟙 X) (Work.Cohomology.subtypeIncl Y Q)
    rw [chainMap_id_eq X] at hnat
    have hL : τ₁ ≫ S₂.f = Work.Kunneth.ezMapT X Q' ≫
        SSet.chainComplexMap (TopCat.toSSet.map (MonoidalCategoryStruct.tensorHom (𝟙 X)
          (Work.Cohomology.subtypeIncl Y Q))) Work.Kunneth.zz := by
      dsimp only [τ₁, S₂, Work.Cohomology.hPairShort, Work.Cohomology.inclChains]
      rw [Category.assoc, ← Work.Cohomology.chainMap_comp', ← tensorHom_id_incl_eq W P Q]
      rfl
    have hR : Sp.f ≫ τ₂ = Work.Kunneth.tpMap (Work.Kunneth.sChain (TopCat.toSSet.obj X))
        (Work.Kunneth.sChain (TopCat.toSSet.obj X)) (Work.Kunneth.sChain (TopCat.toSSet.obj Q'))
        (Work.Kunneth.sChain (TopCat.toSSet.obj Y)) (𝟙 (Work.Cohomology.singularChains ℤ X))
        (SSet.chainComplexMap (TopCat.toSSet.map (Work.Cohomology.subtypeIncl Y Q))
          Work.Kunneth.zz) ≫ Work.Kunneth.ezMapT X Y := rfl
    rw [hL, hR]
    exact hnat.symm
  -- the morphism of short complexes `Sp ⟶ S₂`
  let φτ₃ : Sp.X₃ ⟶ S₂.X₃ := cokernel.desc Sp.f (τ₂ ≫ S₂.g) (by
    rw [← Category.assoc, ← hcomm₁₂, Category.assoc, S₂.zero, comp_zero])
  let φ : Sp ⟶ S₂ :=
    { τ₁ := τ₁
      τ₂ := τ₂
      τ₃ := φτ₃
      comm₁₂ := hcomm₁₂
      comm₂₃ := (cokernel.π_desc Sp.f (τ₂ ≫ S₂.g) _).symm }
  -- the morphism of short complexes `Sp ⟶ S`
  let ψτ₃ : Sp.X₃ ⟶ S.X₃ := cokernel.desc Sp.f DtpD S.zero
  let ψ : Sp ⟶ S :=
    { τ₁ := 𝟙 Sp.X₁
      τ₂ := 𝟙 Sp.X₂
      τ₃ := ψτ₃
      comm₁₂ := by rw [Category.id_comp, Category.comp_id]
      comm₂₃ := (cokernel.π_desc Sp.f DtpD S.zero).symm }
  have hφ₁ : QuasiIso φ.τ₁ := by
    haveI : QuasiIso (Work.Kunneth.ezMapT X Q') := quasiIso_ezMapT X Q'
    haveI : QuasiIso (Work.Cohomology.chainMap ℤ (TopCat.of (W × ↥Q)) (TopCat.of ↥WQ)
        (prodSubtypeTopIso W P Q).hom) := inferInstance
    show QuasiIso (Work.Kunneth.ezMapT X Q' ≫ Work.Cohomology.chainMap ℤ
      (TopCat.of (W × ↥Q)) (TopCat.of ↥WQ) (prodSubtypeTopIso W P Q).hom)
    infer_instance
  have hφ₂ : QuasiIso φ.τ₂ := by
    show QuasiIso (Work.Kunneth.ezMapT X Y)
    exact quasiIso_ezMapT X Y
  have hψ₁ : QuasiIso ψ.τ₁ := by
    show QuasiIso (𝟙 Sp.X₁)
    infer_instance
  have hψ₂ : QuasiIso ψ.τ₂ := by
    show QuasiIso (𝟙 Sp.X₂)
    infer_instance
  have hφq : QuasiIso φ.τ₃ :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hSp hS₂ hφ₁ hφ₂
  have hψq : QuasiIso ψ.τ₃ :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃ ψ hSp hS hψ₁ hψ₂
  haveI : IsIso (homologyMap φ.τ₃ n) := inferInstance
  haveI : IsIso (homologyMap ψ.τ₃ n) := inferInstance
  exact ⟨(asIso (homologyMap ψ.τ₃ n)).symm ≪≫ (asIso (homologyMap φ.τ₃ n))⟩

end

end Work.Serre
