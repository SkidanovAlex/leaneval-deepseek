import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.pd_ab_defs

/-!
# A clash-free copy of the `A+B` short exact sequence and its long exact sequence

`Submission/Work/Cohomology/pdAB_shortExact.lean` declares a public helper `gen`
(`Work.Cohomology.gen`), and so does `Submission/Work/Cohomology/Sd_comm.lean`; the two clash, so
no module can import both `pdAB_shortExact` and the Mayer-Vietoris machinery.  The gluing of the
`Good` predicate (Hatcher's Lemma 3.36) needs the connecting map `pdABδ` of the `A+B` sequence
*and* the Mayer-Vietoris boundary `mvδ` in one file, so this module re-declares the two files

* `pdAB_shortExact` (the short exactness of the `A+B` sequence), and
* `pd_ab_les` (its long exact sequence, the connecting map and its elementwise description)

inside the namespace `Work.Cohomology.PDABClean`, verbatim (so that the public helper `gen`
becomes `Work.Cohomology.PDABClean.gen` and no longer clashes with `Sd_comm.gen`).

Nothing here is new mathematics; it is `pdAB_shortExact.lean` + `pd_ab_les.lean` with an extra
namespace.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Simplicial
open scoped Simplicial

namespace Work.Cohomology.PDABClean

noncomputable section

variable (X : TopCat) (A B : Set X) (n : ℕ)

/-- The inclusion `A ∩ B ↪ A`. -/
def pdInclAB_A : TopCat.of ↥(A ∩ B) ⟶ TopCat.of A :=
  TopCat.ofHom ⟨fun x => ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- Naturality of `TopCat.toSSetObjEquivT` in the space. -/
lemma pdToSSetObjEquiv_map_apply {X Y : TopCat} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ)
    (x : (TopCat.toSSet.obj X).obj n) (z : stdSimplex ℝ (Fin (n.unop.len + 1))) :
    TopCat.toSSetObjEquivT Y n ((TopCat.toSSet.map f).app n x) z
      = f (TopCat.toSSetObjEquivT X n x z) := rfl

/-- A simplex of `A` and a simplex of `B` that agree in `X` give a simplex of `A ∩ B`. -/
lemma simplex_mem_inter
    (σ : (TopCat.toSSet.obj (TopCat.of A)).obj (Opposite.op (SimplexCategory.mk n)))
    (τ : (TopCat.toSSet.obj (TopCat.of B)).obj (Opposite.op (SimplexCategory.mk n)))
    (h : (TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op (SimplexCategory.mk n)) σ
        = (TopCat.toSSet.map (subtypeIncl X B)).app (Opposite.op (SimplexCategory.mk n)) τ) :
    ∃ ρ : (TopCat.toSSet.obj (TopCat.of ↥(A ∩ B))).obj (Opposite.op (SimplexCategory.mk n)),
      (TopCat.toSSet.map (pdInclAB_A X A B)).app (Opposite.op (SimplexCategory.mk n)) ρ = σ := by
  classical
  let σc : C(stdSimplex ℝ (Fin (n+1)), ↥A) :=
    TopCat.toSSetObjEquivT (TopCat.of A) (Opposite.op (SimplexCategory.mk n)) σ
  let τc : C(stdSimplex ℝ (Fin (n+1)), ↥B) :=
    TopCat.toSSetObjEquivT (TopCat.of B) (Opposite.op (SimplexCategory.mk n)) τ
  have hmem : ∀ z : stdSimplex ℝ (Fin (n+1)), (σc z).1 ∈ B := by
    intro z
    have hh : (σc z).1 = (τc z).1 := by
      have h' : TopCat.toSSetObjEquivT X (Opposite.op (SimplexCategory.mk n))
            ((TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op (SimplexCategory.mk n)) σ) z
          = TopCat.toSSetObjEquivT X (Opposite.op (SimplexCategory.mk n))
            ((TopCat.toSSet.map (subtypeIncl X B)).app (Opposite.op (SimplexCategory.mk n)) τ) z :=
        congrArg (fun w => TopCat.toSSetObjEquivT X (Opposite.op (SimplexCategory.mk n)) w z) h
      rw [pdToSSetObjEquiv_map_apply, pdToSSetObjEquiv_map_apply] at h'
      exact h'
    rw [hh]
    exact (τc z).2
  have hcont : Continuous (fun z => (⟨(σc z).1, ⟨(σc z).2, hmem z⟩⟩ : ↥(A ∩ B))) :=
    (continuous_subtype_val.comp σc.continuous).subtype_mk (fun z => ⟨(σc z).2, hmem z⟩)
  let ρc : C(stdSimplex ℝ (Fin (n+1)), ↥(A ∩ B)) := ⟨fun z => ⟨(σc z).1, ⟨(σc z).2, hmem z⟩⟩, hcont⟩
  refine ⟨(TopCat.toSSetObjEquivT (TopCat.of ↥(A ∩ B))
      (Opposite.op (SimplexCategory.mk n))).symm ρc, ?_⟩
  apply (TopCat.toSSetObjEquivT (TopCat.of A) (Opposite.op (SimplexCategory.mk n))).injective
  ext z
  rw [pdToSSetObjEquiv_map_apply, Equiv.apply_symm_apply]
  rfl

set_option maxHeartbeats 1600000 in
lemma chainRetract_apply_pos
    (x : (TopCat.toSSet.obj (TopCat.of A)).obj (Opposite.op (SimplexCategory.mk n)))
    (y : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)))
    (h : (TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op (SimplexCategory.mk n)) x = y) :
    (TopCat.toSSet.obj X).ιChainComplex y ≫ chainRetract ℤ X A n
      = (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex x := by
  classical
  rw [chainRetract]
  refine (Cofan.IsColimit.fac ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
      (fun y => if hy : ∃ x', (TopCat.toSSet.map (subtypeIncl X A)).app
            (Opposite.op (SimplexCategory.mk n)) x' = y
              then (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex (Classical.choose hy) else 0)
      y).trans ?_
  rw [dif_pos ⟨x, h⟩]
  congr 1
  exact injective_toSSet_map (subtypeIncl X A) (subtypeIncl_injective X A) n
    ((Classical.choose_spec (⟨x, h⟩ : ∃ x',
      (TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op (SimplexCategory.mk n)) x' = y)).trans h.symm)

set_option maxHeartbeats 1600000 in
lemma chainRetract_apply_zero
    (y : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)))
    (h : ¬ ∃ x : (TopCat.toSSet.obj (TopCat.of A)).obj (Opposite.op (SimplexCategory.mk n)),
            (TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op (SimplexCategory.mk n)) x = y) :
    (TopCat.toSSet.obj X).ιChainComplex y ≫ chainRetract ℤ X A n = 0 := by
  classical
  rw [chainRetract]
  refine (Cofan.IsColimit.fac ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
      (fun y => if hy : ∃ x', (TopCat.toSSet.map (subtypeIncl X A)).app
            (Opposite.op (SimplexCategory.mk n)) x' = y
              then (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex (Classical.choose hy) else 0)
      y).trans ?_
  rw [dif_neg h]

/-- The chain map `C_n(A) ⟶ C_n(X)`. -/
def cMap (X : TopCat) (A : Set X) (n : ℕ) :
    (singularChains ℤ (TopCat.of A)).X n →ₗ[ℤ] (singularChains ℤ X).X n :=
  ((chainMap ℤ (TopCat.of A) X (subtypeIncl X A)).f n).hom

/-- The chain retraction `C_n(X) ⟶ C_n(A)`. -/
def cRetr (X : TopCat) (A : Set X) (n : ℕ) :
    (singularChains ℤ X).X n →ₗ[ℤ] (singularChains ℤ (TopCat.of A)).X n :=
  (chainRetract ℤ X A n).hom

lemma cRetr_comp_cMap (X : TopCat) (A : Set X) (n : ℕ) :
    (cRetr X A n).comp (cMap X A n) = LinearMap.id := by
  have h := congrArg ModuleCat.Hom.hom (chainRetract_spec ℤ X A n)
  rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
  simp only [cRetr, cMap]
  exact h

/-- The `n`-th component of the restriction `C^n(X) ⟶ C^n(A)`. -/
def restrComp (X : TopCat) (A : Set X) (n : ℕ) :
    dualChains ℤ X n ⟶ dualChains ℤ (TopCat.of A) n :=
  ModuleCat.ofHom ((cMap X A n).dualMap)

/-- Evaluation of `restrComp`. -/
lemma restrComp_apply (φ : (singularChains ℤ X).X n →ₗ[ℤ] ℤ)
    (x : (singularChains ℤ (TopCat.of A)).X n) :
    (restrComp X A n).hom φ x = φ ((cMap X A n) x) := by
  rw [restrComp, ModuleCat.hom_ofHom]
  exact LinearMap.dualMap_apply _ _ _

/-- Evaluation of `restrComp`, as a composition. -/
lemma restrComp_hom_eq (φ : (singularChains ℤ X).X n →ₗ[ℤ] ℤ) :
    (restrComp X A n).hom φ = φ.comp (cMap X A n) := by
  apply LinearMap.ext; intro x; rw [restrComp_apply]; rfl

/-- The section of `restrComp` obtained from the chain retraction `chainRetract`. -/
def sectComp (X : TopCat) (A : Set X) (n : ℕ) :
    dualChains ℤ (TopCat.of A) n ⟶ dualChains ℤ X n :=
  ModuleCat.ofHom ((cRetr X A n).dualMap)

/-- Evaluation of `sectComp`. -/
lemma sectComp_apply (g : (singularChains ℤ (TopCat.of A)).X n →ₗ[ℤ] ℤ)
    (x : (singularChains ℤ X).X n) :
    (sectComp X A n).hom g x = g ((cRetr X A n) x) := by
  rw [sectComp, ModuleCat.hom_ofHom]
  exact LinearMap.dualMap_apply _ _ _

/-- Evaluation of `sectComp`, as a composition. -/
lemma sectComp_hom_eq (g : (singularChains ℤ (TopCat.of A)).X n →ₗ[ℤ] ℤ) :
    (sectComp X A n).hom g = g.comp (cRetr X A n) := by
  apply LinearMap.ext; intro x; rw [sectComp_apply]; rfl

/-- `sectComp` is a section of `restrComp`. -/
lemma restrComp_sectComp (g : (singularChains ℤ (TopCat.of A)).X n →ₗ[ℤ] ℤ) :
    (restrComp X A n).hom ((sectComp X A n).hom g) = g := by
  apply LinearMap.ext
  intro x
  rw [restrComp_apply, sectComp_apply]
  have hx := LinearMap.congr_fun (cRetr_comp_cMap X A n) x
  rw [LinearMap.comp_apply, LinearMap.id_apply] at hx
  rw [hx]

/-- The degreewise component `restrComp` of the restriction is the restriction. -/
lemma restr_f_eq_restrComp : (restr ℤ X A).f n = restrComp X A n := rfl

/-- The generator of the singular chains of `X` corresponding to a simplex. -/
abbrev gen (X : TopCat) (n : ℕ) (y : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    ↑((singularChains ℤ X).X n) :=
  (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) y)).hom 1

/-- The chain retraction on a generator in the image of `A`. -/
lemma cRetr_gen_pos (x : (TopCat.toSSet.obj (TopCat.of A)).obj (Opposite.op (SimplexCategory.mk n)))
    (y : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)))
    (h : (TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op (SimplexCategory.mk n)) x = y) :
    (cRetr X A n) (gen X n y) = gen (TopCat.of A) n x := by
  have h2 := congrArg ModuleCat.Hom.hom (chainRetract_apply_pos X A n x y h)
  rw [ModuleCat.hom_comp] at h2
  simp only [cRetr, gen]
  exact LinearMap.congr_fun h2 1

/-- The chain retraction on a generator not in the image of `A`. -/
lemma cRetr_gen_zero (y : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)))
    (h : ¬ ∃ x : (TopCat.toSSet.obj (TopCat.of A)).obj (Opposite.op (SimplexCategory.mk n)),
            (TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op (SimplexCategory.mk n)) x = y) :
    (cRetr X A n) (gen X n y) = 0 := by
  have h2 := congrArg ModuleCat.Hom.hom (chainRetract_apply_zero X A n y h)
  rw [ModuleCat.hom_comp] at h2
  simp only [cRetr, gen]
  exact LinearMap.congr_fun h2 1

/-- The chain map on a generator. -/
lemma cMap_gen
    (y : (TopCat.toSSet.obj (TopCat.of A)).obj (Opposite.op (SimplexCategory.mk n))) :
    (cMap X A n) (gen (TopCat.of A) n y) = gen X n ((TopCat.toSSet.map (subtypeIncl X A)).app _ y) := by
  have h2 := congrArg ModuleCat.Hom.hom (SSet.ι_chainComplexMap_f
    (TopCat.toSSet.obj (TopCat.of A)) (TopCat.toSSet.obj X) (TopCat.toSSet.map (subtypeIncl X A))
    (ModuleCat.of ℤ ℤ) y)
  rw [ModuleCat.hom_comp] at h2
  simp only [cMap, gen, chainMap_f_eq]
  exact LinearMap.congr_fun h2 1

/-- The two inclusions into `X` agree: a simplex of `A ∩ B` gives the same simplex of `X`. -/
lemma inclAB_apply (ρ : (TopCat.toSSet.obj (TopCat.of ↥(A ∩ B))).obj
      (Opposite.op (SimplexCategory.mk n))) :
    (TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op (SimplexCategory.mk n))
        ((TopCat.toSSet.map (pdInclAB_A X A B)).app (Opposite.op (SimplexCategory.mk n)) ρ)
      = (TopCat.toSSet.map (subtypeIncl X (A ∩ B))).app
          (Opposite.op (SimplexCategory.mk n)) ρ := by
  have hcomp : pdInclAB_A X A B ≫ subtypeIncl X A = subtypeIncl X (A ∩ B) := by
    apply TopCat.ext; intro x; rfl
  rw [← hcomp, Functor.map_comp]
  rfl

/-- **The key lemma**: if a functional kills the chains in `A ∩ B`, then it kills
`C_n(A) → C_n(X) → C_n(A) → C_n(X) → C_n(B)` (the retraction of `A` applied to a chain of `B`). -/
lemma keyLemma (v : (singularChains ℤ X).X n →ₗ[ℤ] ℤ)
    (hv : v.comp (cMap X (A ∩ B) n) = 0) :
    v.comp ((cMap X A n).comp ((cRetr X A n).comp (cMap X B n))) = 0 := by
  classical
  set T := (cMap X A n).comp ((cRetr X A n).comp (cMap X B n)) with hT
  have hgen : ∀ τ : (TopCat.toSSet.obj (TopCat.of B)).obj (Opposite.op (SimplexCategory.mk n)),
      (v.comp T) (gen (TopCat.of B) n τ) = 0 := by
    intro τ
    rw [LinearMap.comp_apply, hT]
    simp only [LinearMap.comp_apply]
    set y := (TopCat.toSSet.map (subtypeIncl X B)).app (Opposite.op (SimplexCategory.mk n)) τ with hy
    have hcB : (cMap X B n) (gen (TopCat.of B) n τ) = gen X n y := by
      rw [cMap_gen]
    rw [hcB]
    by_cases h : ∃ σ : (TopCat.toSSet.obj (TopCat.of A)).obj (Opposite.op (SimplexCategory.mk n)),
        (TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op (SimplexCategory.mk n)) σ = y
    · obtain ⟨σ, hσ⟩ := h
      have hcR : (cRetr X A n) (gen X n y) = gen (TopCat.of A) n σ :=
        cRetr_gen_pos X A n σ y hσ
      rw [hcR]
      have hcA : (cMap X A n) (gen (TopCat.of A) n σ) = gen X n y := by
        rw [cMap_gen, hσ]
      rw [hcA]
      obtain ⟨ρ, hρ⟩ := simplex_mem_inter X A B n σ τ (hσ.trans hy)
      have hkey : gen X n y = (cMap X (A ∩ B) n) (gen (TopCat.of ↥(A ∩ B)) n ρ) := by
        rw [cMap_gen]
        congr 1
        rw [← hσ, ← hρ]
        exact (inclAB_apply X A B n ρ).symm
      rw [hkey]
      have := LinearMap.congr_fun hv (gen (TopCat.of ↥(A ∩ B)) n ρ)
      simpa [LinearMap.comp_apply] using this
    · have hcR : (cRetr X A n) (gen X n y) = 0 := cRetr_gen_zero X A n y h
      rw [hcR, map_zero, map_zero]
  have hzero : (ModuleCat.ofHom (v.comp T) :
      ((TopCat.toSSet.obj (TopCat.of B)).chainComplex (ModuleCat.of ℤ ℤ)).X n
        ⟶ ModuleCat.of ℤ ℤ) = 0 := by
    apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj (TopCat.of B))
      (R := ModuleCat.of ℤ ℤ) (n := n) (T := ModuleCat.of ℤ ℤ)
    intro τ
    rw [CategoryTheory.Limits.comp_zero]
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_zero]
    apply LinearMap.ext_ring
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    exact hgen τ
  have h2 := congrArg ModuleCat.Hom.hom hzero
  rwa [ModuleCat.hom_ofHom, ModuleCat.hom_zero] at h2


/-- The composite `(restrComp X B n) ∘ (sectComp X A n) ∘ (restrComp X A n)` is the composite
linear map `v ↦ v ∘ (cMap X A n ∘ (cRetr X A n ∘ cMap X B n))`. -/
lemma restrB_sectA_restrA (v : (singularChains ℤ X).X n →ₗ[ℤ] ℤ) :
    (restrComp X B n).hom ((sectComp X A n).hom ((restrComp X A n).hom v))
      = v.comp ((cMap X A n).comp ((cRetr X A n).comp (cMap X B n))) := by
  rw [restrComp_hom_eq, sectComp_hom_eq, restrComp_hom_eq, LinearMap.comp_assoc,
    LinearMap.comp_assoc]

/-- The key vanishing statement in the form needed below. -/
lemma restrB_sectA_restrA_eq_zero (v : (singularChains ℤ X).X n →ₗ[ℤ] ℤ)
    (hv : (restrComp X (A ∩ B) n).hom v = 0) :
    (restrComp X B n).hom ((sectComp X A n).hom ((restrComp X A n).hom v)) = 0 := by
  rw [restrB_sectA_restrA]
  refine keyLemma X A B n v ?_
  rw [← restrComp_hom_eq]
  exact hv

/-- `relMapLM` along the identity leaves the underlying cochain unchanged. -/
lemma relMapLM_id_coe {A₁ A₂ : Set X} (h : ∀ x ∈ A₁, x ∈ A₂) (n : ℕ)
    (x : relKern ℤ X A₂ n) :
    ((relMapLM ℤ A₁ A₂ (𝟙 X) h n x : relKern ℤ X A₁ n) : ↑((singularCochainComplex ℤ X).X n))
      = ↑x := by
  rw [relMapLM_coe]
  have h2 := congrArg (fun (φ : singularCochainComplex ℤ X ⟶ singularCochainComplex ℤ X) =>
      (φ.f n).hom) (dualChainMap_id ℤ X)
  rw [h2, HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]

/-- The underlying cochain of `(pdToInterA).f n x` is that of `x`. -/
lemma pdToInterA_coe (x : (relComplex ℤ X A).X n) :
    (show ↥(relKern ℤ X (A ∩ B) n) from (pdToInterA X A B).f n x).1 =
      (show ↥(relKern ℤ X A n) from x).1 :=
  relMapLM_id_coe (X := X) (A₁ := A ∩ B) (A₂ := A) (fun x hx => hx.1) n _

/-- The underlying cochain of `(pdToInterB).f n x` is that of `x`. -/
lemma pdToInterB_coe (x : (relComplex ℤ X B).X n) :
    (show ↥(relKern ℤ X (A ∩ B) n) from (pdToInterB X A B).f n x).1 =
      (show ↥(relKern ℤ X B n) from x).1 :=
  relMapLM_id_coe (X := X) (A₁ := A ∩ B) (A₂ := B) (fun x hx => hx.2) n _


/-- The first component of `pdBiprodToInter` on the `inl` summand. -/
lemma pdBiprodToInter_inl (y : (relComplex ℤ X A).X n) :
    (ModuleCat.Hom.hom ((pdBiprodToInter X A B).f n))
        ((ModuleCat.Hom.hom ((biprod.inl : relComplex ℤ X A ⟶
          relComplex ℤ X A ⊞ relComplex ℤ X B).f n)) y)
      = (ModuleCat.Hom.hom ((pdToInterA X A B).f n)) y := by
  have h := congrArg ModuleCat.Hom.hom
    (HomologicalComplex.biprod_inl_desc_f (pdToInterA X A B) (-(pdToInterB X A B)) n)
  rw [ModuleCat.hom_comp] at h
  exact LinearMap.congr_fun h y

/-- The second component of `pdBiprodToInter` on the `inr` summand. -/
lemma pdBiprodToInter_inr (y : (relComplex ℤ X B).X n) :
    (ModuleCat.Hom.hom ((pdBiprodToInter X A B).f n))
        ((ModuleCat.Hom.hom ((biprod.inr : relComplex ℤ X B ⟶
          relComplex ℤ X A ⊞ relComplex ℤ X B).f n)) y)
      = (ModuleCat.Hom.hom ((-(pdToInterB X A B)).f n)) y := by
  have h := congrArg ModuleCat.Hom.hom
    (HomologicalComplex.biprod_inr_desc_f (pdToInterA X A B) (-(pdToInterB X A B)) n)
  rw [ModuleCat.hom_comp] at h
  exact LinearMap.congr_fun h y

/-- The underlying cochain of the image of an `inl`-`inr` combination. -/
lemma pdBiprodToInter_coe (y₁ : (relComplex ℤ X A).X n) (y₂ : (relComplex ℤ X B).X n) :
    (show ↥(relKern ℤ X (A ∩ B) n) from
      (ModuleCat.Hom.hom ((pdBiprodToInter X A B).f n))
        ((ModuleCat.Hom.hom ((biprod.inl : relComplex ℤ X A ⟶
            relComplex ℤ X A ⊞ relComplex ℤ X B).f n)) y₁
          + (ModuleCat.Hom.hom ((biprod.inr : relComplex ℤ X B ⟶
            relComplex ℤ X A ⊞ relComplex ℤ X B).f n)) y₂)).1
      = (show ↥(relKern ℤ X A n) from y₁).1 - (show ↥(relKern ℤ X B n) from y₂).1 := by
  rw [map_add, pdBiprodToInter_inl, pdBiprodToInter_inr, HomologicalComplex.neg_f_apply]
  rw [Submodule.coe_add, ModuleCat.hom_neg, LinearMap.neg_apply, Submodule.coe_neg,
    pdToInterA_coe, pdToInterB_coe]
  abel

/-- **Surjectivity of the difference map** `C^n(X,A) ⊞ C^n(X,B) ⟶ C^n(X,A∩B)`. -/
lemma pdBiprodToInter_surj :
    Function.Surjective (ModuleCat.Hom.hom ((pdBiprodToInter X A B).f n)) := by
  intro p
  set v : ↑((singularCochainComplex ℤ X).X n) :=
    (show ↥(relKern ℤ X (A ∩ B) n) from p).1 with hv
  have hp : (restrComp X (A ∩ B) n).hom v = 0 :=
    (show ↥(relKern ℤ X (A ∩ B) n) from p).2
  set s : ↑((singularCochainComplex ℤ X).X n) :=
    (sectComp X A n).hom ((restrComp X A n).hom v) with hs
  have hsa : v - s ∈ relKern ℤ X A n := by
    show (restrComp X A n).hom (v - s) = 0
    rw [map_sub, hs, restrComp_sectComp, sub_self]
  have hsb : -s ∈ relKern ℤ X B n := by
    show (restrComp X B n).hom (-s) = 0
    rw [hs, map_neg, restrB_sectA_restrA_eq_zero X A B n v hp, neg_zero]
  refine ⟨(biprod.inl : relComplex ℤ X A ⟶ relComplex ℤ X A ⊞ relComplex ℤ X B).f n
      (⟨v - s, hsa⟩ : ↥(relKern ℤ X A n)) + (biprod.inr : relComplex ℤ X B ⟶
        relComplex ℤ X A ⊞ relComplex ℤ X B).f n (⟨-s, hsb⟩ : ↥(relKern ℤ X B n)), ?_⟩
  apply Subtype.ext
  rw [pdBiprodToInter_coe]
  rw [← hv]
  show (v - s) - (-s) = v
  abel


/-- The projections and inclusions of a biproduct of cochain complexes, on elements. -/
lemma pdBiprodFst_inl (a : (relComplex ℤ X A).X n) :
    (ModuleCat.Hom.hom ((biprod.fst : relComplex ℤ X A ⊞ relComplex ℤ X B ⟶
        relComplex ℤ X A).f n))
      ((ModuleCat.Hom.hom ((biprod.inl : relComplex ℤ X A ⟶
        relComplex ℤ X A ⊞ relComplex ℤ X B).f n)) a) = a := by
  have h := congrArg ModuleCat.Hom.hom
    (HomologicalComplex.biprod_inl_fst_f (K := relComplex ℤ X A) (L := relComplex ℤ X B) n)
  rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
  exact LinearMap.congr_fun h a

lemma pdBiprodFst_inr (b : (relComplex ℤ X B).X n) :
    (ModuleCat.Hom.hom ((biprod.fst : relComplex ℤ X A ⊞ relComplex ℤ X B ⟶
        relComplex ℤ X A).f n))
      ((ModuleCat.Hom.hom ((biprod.inr : relComplex ℤ X B ⟶
        relComplex ℤ X A ⊞ relComplex ℤ X B).f n)) b) = 0 := by
  have h := congrArg ModuleCat.Hom.hom
    (HomologicalComplex.biprod_inr_fst_f (K := relComplex ℤ X A) (L := relComplex ℤ X B) n)
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
  exact LinearMap.congr_fun h b

lemma pdBiprodSnd_inl (a : (relComplex ℤ X A).X n) :
    (ModuleCat.Hom.hom ((biprod.snd : relComplex ℤ X A ⊞ relComplex ℤ X B ⟶
        relComplex ℤ X B).f n))
      ((ModuleCat.Hom.hom ((biprod.inl : relComplex ℤ X A ⟶
        relComplex ℤ X A ⊞ relComplex ℤ X B).f n)) a) = 0 := by
  have h := congrArg ModuleCat.Hom.hom
    (HomologicalComplex.biprod_inl_snd_f (K := relComplex ℤ X A) (L := relComplex ℤ X B) n)
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
  exact LinearMap.congr_fun h a

lemma pdBiprodSnd_inr (b : (relComplex ℤ X B).X n) :
    (ModuleCat.Hom.hom ((biprod.snd : relComplex ℤ X A ⊞ relComplex ℤ X B ⟶
        relComplex ℤ X B).f n))
      ((ModuleCat.Hom.hom ((biprod.inr : relComplex ℤ X B ⟶
        relComplex ℤ X A ⊞ relComplex ℤ X B).f n)) b) = b := by
  have h := congrArg ModuleCat.Hom.hom
    (HomologicalComplex.biprod_inr_snd_f (K := relComplex ℤ X A) (L := relComplex ℤ X B) n)
  rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
  exact LinearMap.congr_fun h b

/-- Decomposition of an element of a biproduct into its two components. -/
lemma pdBiprod_total (y : (relComplex ℤ X A ⊞ relComplex ℤ X B).X n) :
    (ModuleCat.Hom.hom ((biprod.inl : relComplex ℤ X A ⟶
        relComplex ℤ X A ⊞ relComplex ℤ X B).f n))
        ((ModuleCat.Hom.hom ((biprod.fst : relComplex ℤ X A ⊞ relComplex ℤ X B ⟶
          relComplex ℤ X A).f n)) y)
      + (ModuleCat.Hom.hom ((biprod.inr : relComplex ℤ X B ⟶
        relComplex ℤ X A ⊞ relComplex ℤ X B).f n))
        ((ModuleCat.Hom.hom ((biprod.snd : relComplex ℤ X A ⊞ relComplex ℤ X B ⟶
          relComplex ℤ X B).f n)) y) = y := by
  have h := congrArg ModuleCat.Hom.hom
    (HomologicalComplex.biprod_total_f (K := relComplex ℤ X A) (L := relComplex ℤ X B) n)
  rw [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_id] at h
  exact LinearMap.congr_fun h y

/-- Two elements of a biproduct agree as soon as both components do. -/
lemma pdBiprod_ext {x y : (relComplex ℤ X A ⊞ relComplex ℤ X B).X n}
    (h₁ : (ModuleCat.Hom.hom ((biprod.fst : relComplex ℤ X A ⊞ relComplex ℤ X B ⟶
        relComplex ℤ X A).f n)) x
      = (ModuleCat.Hom.hom ((biprod.fst : relComplex ℤ X A ⊞ relComplex ℤ X B ⟶
        relComplex ℤ X A).f n)) y)
    (h₂ : (ModuleCat.Hom.hom ((biprod.snd : relComplex ℤ X A ⊞ relComplex ℤ X B ⟶
        relComplex ℤ X B).f n)) x
      = (ModuleCat.Hom.hom ((biprod.snd : relComplex ℤ X A ⊞ relComplex ℤ X B ⟶
        relComplex ℤ X B).f n)) y) : x = y := by
  rw [← pdBiprod_total X A B n x, ← pdBiprod_total X A B n y, h₁, h₂]

/-- The two components of `(pdABDiag).f n`. -/
lemma pdABDiag_fst (x : (pdABCoh X A B).X n) :
    (ModuleCat.Hom.hom ((biprod.fst : relComplex ℤ X A ⊞ relComplex ℤ X B ⟶
        relComplex ℤ X A).f n))
      ((ModuleCat.Hom.hom ((pdABDiag X A B).f n)) x)
      = (ModuleCat.Hom.hom ((pdABInclA X A B).f n)) x := by
  have h := congrArg ModuleCat.Hom.hom
    (HomologicalComplex.biprod_lift_fst_f (pdABInclA X A B) (pdABInclB X A B) n)
  rw [ModuleCat.hom_comp] at h
  exact LinearMap.congr_fun h x

lemma pdABDiag_snd (x : (pdABCoh X A B).X n) :
    (ModuleCat.Hom.hom ((biprod.snd : relComplex ℤ X A ⊞ relComplex ℤ X B ⟶
        relComplex ℤ X B).f n))
      ((ModuleCat.Hom.hom ((pdABDiag X A B).f n)) x)
      = (ModuleCat.Hom.hom ((pdABInclB X A B).f n)) x := by
  have h := congrArg ModuleCat.Hom.hom
    (HomologicalComplex.biprod_lift_snd_f (pdABInclA X A B) (pdABInclB X A B) n)
  rw [ModuleCat.hom_comp] at h
  exact LinearMap.congr_fun h x

/-- The action of `(pdABDiag).f n` on an element, in terms of the two inclusions. -/
lemma pdABDiag_apply (x : (pdABCoh X A B).X n) :
    (ModuleCat.Hom.hom ((pdABDiag X A B).f n)) x
      = (ModuleCat.Hom.hom ((biprod.inl : relComplex ℤ X A ⟶
            relComplex ℤ X A ⊞ relComplex ℤ X B).f n))
          ((ModuleCat.Hom.hom ((pdABInclA X A B).f n)) x)
        + (ModuleCat.Hom.hom ((biprod.inr : relComplex ℤ X B ⟶
            relComplex ℤ X A ⊞ relComplex ℤ X B).f n))
          ((ModuleCat.Hom.hom ((pdABInclB X A B).f n)) x) := by
  apply pdBiprod_ext X A B n
  · rw [map_add, pdBiprodFst_inl, pdBiprodFst_inr, add_zero]
    exact pdABDiag_fst X A B n x
  · rw [map_add, pdBiprodSnd_inl, pdBiprodSnd_inr, zero_add]
    exact pdABDiag_snd X A B n x

/-- The underlying cochain of `(pdABInclA).f n x` is that of `x`. -/
lemma pdABInclA_val (x : (pdABCoh X A B).X n) :
    ((show ↥(relKern ℤ X A n) from (pdABInclA X A B).f n x) :
        ↑((singularCochainComplex ℤ X).X n)) =
      (show ↥(pdABKern X A B n) from x).1 := rfl

/-- The inclusion `C^n(X,A+B) ⟶ C^n(X,A)` is injective. -/
lemma pdABInclA_injective : Function.Injective
    (ModuleCat.Hom.hom ((pdABInclA X A B).f n)) := by
  intro x y h
  apply Subtype.ext
  rw [← pdABInclA_val X A B n x, ← pdABInclA_val X A B n y, h]

/-- The diagonal `C^n(X,A+B) ⟶ C^n(X,A) ⊞ C^n(X,B)` is injective. -/
lemma pdABDiag_injective : Function.Injective
    (ModuleCat.Hom.hom ((pdABDiag X A B).f n)) := by
  intro x y h
  have h' : (ModuleCat.Hom.hom ((biprod.fst : relComplex ℤ X A ⊞ relComplex ℤ X B ⟶
        relComplex ℤ X A).f n)) ((ModuleCat.Hom.hom ((pdABDiag X A B).f n)) x)
      = (ModuleCat.Hom.hom ((biprod.fst : relComplex ℤ X A ⊞ relComplex ℤ X B ⟶
        relComplex ℤ X A).f n)) ((ModuleCat.Hom.hom ((pdABDiag X A B).f n)) y) := by
    rw [h]
  rw [pdABDiag_fst, pdABDiag_fst] at h'
  exact pdABInclA_injective X A B n h'

/-- The image of the diagonal is the kernel of the difference map. -/
lemma pdABDiag_comp_pdBiprodToInter_f :
    (pdABDiag X A B).f n ≫ (pdBiprodToInter X A B).f n = 0 := by
  rw [← HomologicalComplex.comp_f, pdABDiag_comp_pdBiprodToInter, HomologicalComplex.zero_f]

/-- The underlying cochain of the difference map applied to an `inl`-`inr` combination. -/
lemma pdToInterA_sub_pdToInterB_coe (y₁ : (relComplex ℤ X A).X n)
    (y₂ : (relComplex ℤ X B).X n) :
    (show ↥(relKern ℤ X (A ∩ B) n) from
      (ModuleCat.Hom.hom ((pdToInterA X A B).f n)) y₁
        + (ModuleCat.Hom.hom ((-(pdToInterB X A B)).f n)) y₂).1
      = (show ↥(relKern ℤ X A n) from y₁).1 - (show ↥(relKern ℤ X B n) from y₂).1 := by
  rw [Submodule.coe_add, HomologicalComplex.neg_f_apply, ModuleCat.hom_neg, LinearMap.neg_apply,
    Submodule.coe_neg, pdToInterA_coe, pdToInterB_coe]
  abel

/-- Exactness at the middle of the degreewise `A+B` sequence. -/
lemma pdAB_function_exact :
    Function.Exact (ModuleCat.Hom.hom ((pdABDiag X A B).f n))
      (ModuleCat.Hom.hom ((pdBiprodToInter X A B).f n)) := by
  intro y
  constructor
  · intro hy
    set y₁ : (relComplex ℤ X A).X n :=
      (ModuleCat.Hom.hom ((biprod.fst : relComplex ℤ X A ⊞ relComplex ℤ X B ⟶
        relComplex ℤ X A).f n)) y with hy₁
    set y₂ : (relComplex ℤ X B).X n :=
      (ModuleCat.Hom.hom ((biprod.snd : relComplex ℤ X A ⊞ relComplex ℤ X B ⟶
        relComplex ℤ X B).f n)) y with hy₂
    have hydecomp := pdBiprod_total X A B n y
    have hgy : (ModuleCat.Hom.hom ((pdBiprodToInter X A B).f n)) y
        = (ModuleCat.Hom.hom ((pdToInterA X A B).f n)) y₁
          + (ModuleCat.Hom.hom ((-(pdToInterB X A B)).f n)) y₂ := by
      rw [← hydecomp, map_add, pdBiprodToInter_inl, pdBiprodToInter_inr]
    have h0 : (ModuleCat.Hom.hom ((pdToInterA X A B).f n)) y₁
        + (ModuleCat.Hom.hom ((-(pdToInterB X A B)).f n)) y₂ = 0 := by
      rw [← hgy]; exact hy
    have hv : (show ↥(relKern ℤ X A n) from y₁).1
        = (show ↥(relKern ℤ X B n) from y₂).1 := by
      have h := congrArg (fun z => (show ↥(relKern ℤ X (A ∩ B) n) from z).1) h0
      rw [pdToInterA_sub_pdToInterB_coe] at h
      exact sub_eq_zero.mp h
    let x₀ : ↥(pdABKern X A B n) :=
      ⟨(show ↥(relKern ℤ X A n) from y₁).1,
        Submodule.mem_inf.mpr ⟨(show ↥(relKern ℤ X A n) from y₁).2, by
          rw [hv]; exact (show ↥(relKern ℤ X B n) from y₂).2⟩⟩
    refine ⟨x₀, ?_⟩
    have hA : (ModuleCat.Hom.hom ((pdABInclA X A B).f n)) x₀ = y₁ := by
      apply Subtype.ext
      rfl
    have hB : (ModuleCat.Hom.hom ((pdABInclB X A B).f n)) x₀ = y₂ := by
      apply Subtype.ext
      exact hv
    rw [pdABDiag_apply, hA, hB]
    exact hydecomp
  · rintro ⟨x, rfl⟩
    have h := congrArg ModuleCat.Hom.hom (pdABDiag_comp_pdBiprodToInter_f X A B n)
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact LinearMap.congr_fun h x

/-- **The degreewise `A+B` sequence is short exact.** -/
lemma pdAB_degreewise_shortExact :
    ((pdABShort X A B).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) n)).ShortExact :=
  ModuleCat.shortComplex_shortExact _
    (pdAB_function_exact X A B n) (pdABDiag_injective X A B n) (pdBiprodToInter_surj X A B n)

end

end Work.Cohomology.PDABClean

namespace Work.Cohomology.PDABClean

open CategoryTheory

/-- **The `A+B` short exact sequence of cochain complexes.** -/
theorem pdAB_shortExact (X : TopCat) (A B : Set X) :
    CategoryTheory.ShortComplex.ShortExact (Work.Cohomology.pdABShort X A B) := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact pdAB_degreewise_shortExact X A B n

end Work.Cohomology.PDABClean

namespace Work.Cohomology.PDABClean

noncomputable section

variable (X : TopCat) (A B : Set X)

/-! ## The two maps of the sequence -/

/-- The first map `C^*(X, A+B) ⟶ C^*(X,A) ⊞ C^*(X,B)` of the A+B sequence. -/
abbrev pdABf : pdABCoh X A B ⟶ relComplex ℤ X A ⊞ relComplex ℤ X B := pdABDiag X A B

/-- The second map `C^*(X,A) ⊞ C^*(X,B) ⟶ C^*(X, A∩B)` of the A+B sequence. -/
abbrev pdABg : relComplex ℤ X A ⊞ relComplex ℤ X B ⟶ relComplex ℤ X (A ∩ B) :=
  pdBiprodToInter X A B

/-- The A+B sequence is short exact. -/
theorem pdAB_shortExact' : (pdABShort X A B).ShortExact := pdAB_shortExact X A B

/-- **The connecting homomorphism of the A+B sequence**: `H^k(X, A∩B) ⟶ H^{k+1}(X, A+B)`. -/
noncomputable def pdABδ (k : ℕ) :
    (relComplex ℤ X (A ∩ B)).homology k ⟶ (pdABCoh X A B).homology (k + 1) :=
  (pdAB_shortExact X A B).δ k (k + 1) (by simp [ComplexShape.up_Rel])

/-- The connecting homomorphism followed by the first map of the sequence is zero. -/
theorem pdABδ_comp (k : ℕ) :
    pdABδ X A B k ≫ HomologicalComplex.homologyMap (pdABf X A B) (k + 1) = 0 :=
  (pdAB_shortExact X A B).δ_comp k (k + 1) (by simp [ComplexShape.up_Rel])

/-- The second map of the sequence followed by the connecting homomorphism is zero. -/
theorem pdAB_comp_δ (k : ℕ) :
    HomologicalComplex.homologyMap (pdABg X A B) k ≫ pdABδ X A B k = 0 :=
  (pdAB_shortExact X A B).comp_δ k (k + 1) (by simp [ComplexShape.up_Rel])

/-! ## Exactness -/

/-- Exactness of the A+B sequence at `H^{k+1}(X, A+B)`. -/
theorem pdAB_exact₁ (k : ℕ) :
    (ShortComplex.mk (pdABδ X A B k)
      (HomologicalComplex.homologyMap (pdABf X A B) (k + 1))
      (pdABδ_comp X A B k)).Exact :=
  (pdAB_shortExact X A B).homology_exact₁ k (k + 1) (by simp [ComplexShape.up_Rel])

/-- Exactness of the A+B sequence at `H^k(X,A) ⊞ H^k(X,B)`. -/
theorem pdAB_exact₂ (k : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (pdABf X A B) k)
      (HomologicalComplex.homologyMap (pdABg X A B) k)
      (by rw [← HomologicalComplex.homologyMap_comp,
        pdABDiag_comp_pdBiprodToInter, HomologicalComplex.homologyMap_zero])).Exact :=
  (pdAB_shortExact X A B).homology_exact₂ k

/-- Exactness of the A+B sequence at `H^k(X, A∩B)`. -/
theorem pdAB_exact₃ (k : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (pdABg X A B) k) (pdABδ X A B k)
      (pdAB_comp_δ X A B k)).Exact :=
  (pdAB_shortExact X A B).homology_exact₃ k (k + 1) (by simp [ComplexShape.up_Rel])

/-! ## The elementwise description of the connecting homomorphism -/

/-- **The elementwise description of the A+B connecting homomorphism** (abstract form): if
`x₃` is a cohomology class in degree `k` of `C^*(X, A∩B)` which lifts to the opcycle `x₂` of the
middle term, and `x₁` is an element of `C^{k+1}(X, A+B)` whose image under the first map is the
coboundary of `x₂`, then `x₃ ≫ δ = x₁ ≫ homologyπ`. -/
theorem pdABδ_eq' {k : ℕ} {T : ModuleCat ℤ}
    (x₃ : T ⟶ (relComplex ℤ X (A ∩ B)).homology k)
    (x₂ : T ⟶ (relComplex ℤ X A ⊞ relComplex ℤ X B).opcycles k)
    (x₁ : T ⟶ (pdABCoh X A B).cycles (k + 1))
    (h₂ : x₂ ≫ HomologicalComplex.opcyclesMap (pdABg X A B) k
      = x₃ ≫ (relComplex ℤ X (A ∩ B)).homologyι k)
    (h₁ : x₁ ≫ HomologicalComplex.cyclesMap (pdABf X A B) (k + 1)
      = x₂ ≫ (relComplex ℤ X A ⊞ relComplex ℤ X B).opcyclesToCycles k (k + 1)) :
    x₃ ≫ pdABδ X A B k = x₁ ≫ (pdABCoh X A B).homologyπ (k + 1) :=
  (pdAB_shortExact X A B).δ_eq' k (k + 1) (by simp [ComplexShape.up_Rel]) x₃ x₂ x₁ h₂ h₁


/-- If the diagonal image of `x₁` is a coboundary, then `x₁` is a cocycle. -/
theorem pdABCoh_d_eq_zero {k : ℕ} (x₁ : (pdABCoh X A B).X (k + 1))
    (φt : (relComplex ℤ X A ⊞ relComplex ℤ X B).X k)
    (hx₁ : (pdABDiag X A B).f (k + 1) x₁
      = (relComplex ℤ X A ⊞ relComplex ℤ X B).d k (k + 1) φt) :
    (pdABCoh X A B).d (k + 1) (k + 2) x₁ = 0 := by
  apply pdABDiag_injective X A B (k + 2)
  rw [map_zero]
  have hcomm := (pdABDiag X A B).comm (k + 1) (k + 2)
  have h2 := congrArg (fun (g : (pdABCoh X A B).X (k+1) ⟶
      (relComplex ℤ X A ⊞ relComplex ℤ X B).X (k+2)) => (ModuleCat.Hom.hom g) x₁) hcomm.symm
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [h2, hx₁]
  change (ModuleCat.Hom.hom ((relComplex ℤ X A ⊞ relComplex ℤ X B).d (k + 1) (k + 2)))
      ((ModuleCat.Hom.hom ((relComplex ℤ X A ⊞ relComplex ℤ X B).d k (k + 1))) φt) = 0
  have hdd : (ModuleCat.Hom.hom ((relComplex ℤ X A ⊞ relComplex ℤ X B).d k (k + 1) ≫
      (relComplex ℤ X A ⊞ relComplex ℤ X B).d (k + 1) (k + 2))) φt = 0 := by
    rw [HomologicalComplex.d_comp_d, ModuleCat.hom_zero, LinearMap.zero_apply]
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hdd

/-- **The elementwise description of the A+B connecting homomorphism** (concrete form): if
`φ` is a cocycle of `C^*(X, A∩B)`, `φt` a lift of it in `C^*(X,A) ⊞ C^*(X,B)`, and `x₁` an
element of `C^{k+1}(X,A+B)` with `f x₁ = d φt`, then `δ [φ] = [x₁]`. -/
theorem pdABδ_apply {k : ℕ} (φ : (relComplex ℤ X (A ∩ B)).X k)
    (hφd : (relComplex ℤ X (A ∩ B)).d k (k + 1) φ = 0)
    (φt : (relComplex ℤ X A ⊞ relComplex ℤ X B).X k)
    (hφt : (pdBiprodToInter X A B).f k φt = φ)
    (x₁ : (pdABCoh X A B).X (k + 1))
    (hx₁ : (pdABDiag X A B).f (k + 1) x₁
      = (relComplex ℤ X A ⊞ relComplex ℤ X B).d k (k + 1) φt) :
    pdABδ X A B k ((relComplex ℤ X (A ∩ B)).homologyπ k
        (HomologicalComplex.cyclesMk (relComplex ℤ X (A ∩ B)) φ (k + 1)
          ((ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk k (k + 1) rfl)) hφd))
      = (pdABCoh X A B).homologyπ (k + 1)
        (HomologicalComplex.cyclesMk (pdABCoh X A B) x₁ (k + 2)
          ((ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk (k + 1) (k + 2) rfl))
          (pdABCoh_d_eq_zero X A B x₁ φt hx₁)) := by
  have h := CategoryTheory.ShortComplex.ShortExact.δ_apply (pdAB_shortExact X A B) k (k + 1)
    (ComplexShape.up_mk k (k + 1) rfl) φ hφd φt hφt x₁ hx₁ (k + 2)
    ((ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk (k + 1) (k + 2) rfl))
  convert h using 2 <;> rfl

end

end Work.Cohomology.PDABClean

