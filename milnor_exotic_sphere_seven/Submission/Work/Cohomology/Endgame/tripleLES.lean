import Mathlib
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.Endgame.relComplexMapComp
import Submission.Work.Cohomology.PairSequence

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The long exact sequence of a triple `A ⊆ A' ⊆ X`

For `A ⊆ A' ⊆ X` the relative cochain complexes form a short exact sequence

`0 ⟶ C^*(X,A') ⟶ C^*(X,A) ⟶ C^*(A', A ∩ A') ⟶ 0`,

where

* the first map is the inclusion of pairs `(X,A) ⟶ (X,A')`, i.e. `C^*(X,A') ⊆ C^*(X,A)`;
* the second map is the pullback along the map of pairs `(A', A∩A') ⟶ (X,A)`.

Its homology long exact sequence contains the exact fragment

`Hⁿ(X,A') ⟶ Hⁿ(X,A) ⟶ Hⁿ(A', A∩A')`

at `Hⁿ(X,A)`.  Consequently, if both `Hⁿ(X,A')` and `Hⁿ(A', A∩A')` vanish then so does
`Hⁿ(X,A)`: this is `tripleLES`.

The short exactness is proved degreewise.  Injectivity and exactness are immediate from the
explicit description of the two maps on the kernels of the restriction maps; surjectivity is the
only substantive point: a cochain `β` on `A'` vanishing on `A ∩ A'` has to be the restriction of a
cochain on `X` vanishing on `A`.  For this one takes *any* extension `x₁` of `β` to `X`
(`surjective_restr`) and observes that `ρ_A x₁` is obtained from `β` by restricting to `A`; the key
lemma `key_aux` shows that this restriction vanishes: the inclusion `A ↪ A'` factors through the
identification `A → A ∩ A'` (`kappa`, `kappa_spec`), so the pullback along `A ↪ A'` factors through
the pullback along `A ∩ A' ↪ A'`, and `β` lies in the kernel of the latter.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology.Endgame

noncomputable section

/-- `A ∩ A'` as a subset of `A'`. -/
def A₁' (X : TopCat) (A A' : Set X) : Set ↥A' := (Subtype.val : ↥A' → X) ⁻¹' A

/-- The inclusion `A ⊆ A'` of subspaces. -/
def subIncl (X : TopCat) (A A' : Set X) (h : A ⊆ A') : TopCat.of A ⟶ TopCat.of A' :=
  TopCat.ofHom ⟨fun x => ⟨x.1, h x.2⟩, Continuous.subtype_mk continuous_subtype_val (fun x => h x.2)⟩

lemma subIncl_spec (X : TopCat) (A A' : Set X) (h : A ⊆ A') :
    subIncl X A A' h ≫ Work.Cohomology.subtypeIncl X A' = Work.Cohomology.subtypeIncl X A := by
  apply TopCat.ext; intro x; rfl

/-- `x ↦ (x,x)`, the identification `A → A ∩ A'`. -/
def kappa (X : TopCat) (A A' : Set X) (h : A ⊆ A') : TopCat.of A ⟶ TopCat.of (A₁' X A A') :=
  TopCat.ofHom ⟨fun x => ⟨⟨x.1, h x.2⟩, x.2⟩,
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val (fun x => h x.2))
      (fun x => x.2)⟩

lemma kappa_spec (X : TopCat) (A A' : Set X) (h : A ⊆ A') :
    kappa X A A' h ≫ Work.Cohomology.subtypeIncl (TopCat.of A') (A₁' X A A')
      = subIncl X A A' h := by
  apply TopCat.ext; intro x; rfl

lemma chainMap_comp (R : Type) [CommRing R] {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Work.Cohomology.chainMap R X Z (f ≫ g)
      = Work.Cohomology.chainMap R X Y f ≫ Work.Cohomology.chainMap R Y Z g :=
  CategoryTheory.Functor.map_comp _ f g

lemma chainMap_subIncl_eq (X : TopCat) (A A' : Set X) (h : A ⊆ A') :
    Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of A') (subIncl X A A' h)
      = Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of (A₁' X A A')) (kappa X A A' h)
        ≫ Work.Cohomology.chainMap ℤ (TopCat.of (A₁' X A A')) (TopCat.of A')
            (Work.Cohomology.subtypeIncl (TopCat.of A') (A₁' X A A')) := by
  rw [← chainMap_comp, kappa_spec]

lemma ker_dualMap_le_ker_dualMap_comp {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
    (u : M →ₗ[R] N) (v : N →ₗ[R] P) :
    LinearMap.ker v.dualMap ≤ LinearMap.ker (v.comp u).dualMap := by
  intro φ hφ
  rw [LinearMap.mem_ker] at hφ ⊢
  rw [LinearMap.ext_iff] at hφ ⊢
  intro y
  rw [LinearMap.dualMap_apply, LinearMap.comp_apply, ← LinearMap.dualMap_apply v φ (u y),
    hφ (u y), LinearMap.zero_apply, LinearMap.zero_apply]

/-- A cochain on `A'` vanishing on `A ∩ A'` restricts to zero on `A`. -/
lemma key_aux (X : TopCat) (A A' : Set X) (h : A ⊆ A') (n : ℕ)
    (β : ↑((Work.Cohomology.singularCochainComplex ℤ (TopCat.of A')).X n))
    (hβ : β ∈ Work.Cohomology.relKern ℤ (TopCat.of A') (A₁' X A A') n) :
    ((Work.Cohomology.dualChainMap ℤ (TopCat.of A) (TopCat.of A')
      (subIncl X A A' h)).f n).hom β = 0 := by
  have h1 : ((Work.Cohomology.chainMap ℤ (TopCat.of (A₁' X A A')) (TopCat.of A')
      (Work.Cohomology.subtypeIncl (TopCat.of A') (A₁' X A A'))).f n).hom.dualMap β = 0 := by
    rw [Work.Cohomology.relKern, Work.Cohomology.restr, LinearMap.mem_ker] at hβ
    rw [Work.Cohomology.dualChainMap_f_hom] at hβ
    exact hβ
  have hWu : ((Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of A')
        (subIncl X A A' h)).f n).hom
      = ((Work.Cohomology.chainMap ℤ (TopCat.of (A₁' X A A')) (TopCat.of A')
            (Work.Cohomology.subtypeIncl (TopCat.of A') (A₁' X A A'))).f n).hom.comp
        ((Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of (A₁' X A A'))
            (kappa X A A' h)).f n).hom := by
    rw [chainMap_subIncl_eq, HomologicalComplex.comp_f, ModuleCat.hom_comp]
  have h2 : (((Work.Cohomology.chainMap ℤ (TopCat.of (A₁' X A A')) (TopCat.of A')
            (Work.Cohomology.subtypeIncl (TopCat.of A') (A₁' X A A'))).f n).hom.comp
        ((Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of (A₁' X A A'))
            (kappa X A A' h)).f n).hom).dualMap β = 0 :=
    LinearMap.mem_ker.mp (ker_dualMap_le_ker_dualMap_comp _ _ (LinearMap.mem_ker.mpr h1))
  rw [Work.Cohomology.dualChainMap_f_hom, hWu]
  exact h2

/-- The membership needed to define the map `C^*(X,A) ⟶ C^*(A',A∩A')`. -/
lemma subIncl_mem (X : TopCat) (A A' : Set X) (h : A ⊆ A') :
    ∀ x ∈ A₁' X A A', (Work.Cohomology.subtypeIncl X A') x ∈ A := fun x hx => hx

/-- The first map of the triple sequence. -/
def tripleF (X : TopCat) (A A' : Set X) (h : A ⊆ A') :
    Work.Cohomology.relComplex ℤ X A' ⟶ Work.Cohomology.relComplex ℤ X A :=
  Work.Cohomology.relComplexMap ℤ (X₁ := X) (X₂ := X) A A' (𝟙 X) h

/-- The second map of the triple sequence. -/
def tripleG (X : TopCat) (A A' : Set X) (h : A ⊆ A') :
    Work.Cohomology.relComplex ℤ X A
      ⟶ Work.Cohomology.relComplex ℤ (TopCat.of A') (A₁' X A A') :=
  Work.Cohomology.relComplexMap ℤ (X₁ := TopCat.of A') (X₂ := X) (A₁' X A A') A
    (Work.Cohomology.subtypeIncl X A') (subIncl_mem X A A' h)

/-- The triple sequence is a complex. -/
lemma triple_comp_zero (X : TopCat) (A A' : Set X) (h : A ⊆ A') :
    tripleF X A A' h ≫ tripleG X A A' h = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f_apply]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  show ((Work.Cohomology.relMapLM ℤ (X₁ := TopCat.of A') (X₂ := X) (A₁' X A A') A
        (Work.Cohomology.subtypeIncl X A') (subIncl_mem X A A' h) n)
      ((Work.Cohomology.relMapLM ℤ (X₁ := X) (X₂ := X) A A' (𝟙 X) h n) x)).1 = 0
  simp only [Work.Cohomology.relMapLM_coe, Work.Cohomology.dualChainMap_id,
    HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]
  exact x.2

/-- The triple short complex `0 ⟶ C^*(X,A') ⟶ C^*(X,A) ⟶ C^*(A',A∩A') ⟶ 0`. -/
def tripleShort (X : TopCat) (A A' : Set X) (h : A ⊆ A') :
    ShortComplex (CochainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (tripleF X A A' h) (tripleG X A A' h) (triple_comp_zero X A A' h)

@[simp] lemma tripleShort_f (X : TopCat) (A A' : Set X) (h : A ⊆ A') :
    (tripleShort X A A' h).f = tripleF X A A' h := rfl

@[simp] lemma tripleShort_g (X : TopCat) (A A' : Set X) (h : A ⊆ A') :
    (tripleShort X A A' h).g = tripleG X A A' h := rfl

@[simp] lemma tripleF_f (X : TopCat) (A A' : Set X) (h : A ⊆ A') (n : ℕ) :
    (tripleF X A A' h).f n
      = ModuleCat.ofHom (Work.Cohomology.relMapLM ℤ (X₁ := X) (X₂ := X) A A' (𝟙 X) h n) :=
  Work.Cohomology.relComplexMap_f ℤ (X₁ := X) (X₂ := X) A A' (𝟙 X) h n

@[simp] lemma tripleG_f (X : TopCat) (A A' : Set X) (h : A ⊆ A') (n : ℕ) :
    (tripleG X A A' h).f n
      = ModuleCat.ofHom (Work.Cohomology.relMapLM ℤ (X₁ := TopCat.of A') (X₂ := X)
          (A₁' X A A') A (Work.Cohomology.subtypeIncl X A') (subIncl_mem X A A' h) n) :=
  Work.Cohomology.relComplexMap_f ℤ (X₁ := TopCat.of A') (X₂ := X) (A₁' X A A') A
    (Work.Cohomology.subtypeIncl X A') (subIncl_mem X A A' h) n

lemma relMapLM_id_coe (X : TopCat) (A A' : Set X) (h : A ⊆ A') (n : ℕ)
    (x : ↥(Work.Cohomology.relKern ℤ X A' n)) :
    ((Work.Cohomology.relMapLM ℤ (X₁ := X) (X₂ := X) A A' (𝟙 X) h n) x).1 = x.1 := by
  rw [Work.Cohomology.relMapLM_coe, Work.Cohomology.dualChainMap_id, HomologicalComplex.id_f,
    ModuleCat.hom_id, LinearMap.id_apply]

lemma relMapLM_id_injective (X : TopCat) (A A' : Set X) (h : A ⊆ A') (n : ℕ) :
    Function.Injective (Work.Cohomology.relMapLM ℤ (X₁ := X) (X₂ := X) A A' (𝟙 X) h n) := by
  intro a b hab
  have hh := congrArg (fun z => z.1) hab
  rw [relMapLM_id_coe, relMapLM_id_coe] at hh
  exact Subtype.ext hh

lemma relMapLM_g_surjective (X : TopCat) (A A' : Set X) (h : A ⊆ A') (n : ℕ) :
    Function.Surjective (Work.Cohomology.relMapLM ℤ (X₁ := TopCat.of A') (X₂ := X)
      (A₁' X A A') A (Work.Cohomology.subtypeIncl X A') (subIncl_mem X A A' h) n) := by
  intro β
  obtain ⟨x₁, hx₁⟩ := Work.Cohomology.surjective_restr ℤ X A' n β.1
  rw [Work.Cohomology.restr] at hx₁
  have hsq : Work.Cohomology.restr ℤ X A
      = Work.Cohomology.dualChainMap ℤ (TopCat.of A') X (Work.Cohomology.subtypeIncl X A')
        ≫ Work.Cohomology.dualChainMap ℤ (TopCat.of A) (TopCat.of A') (subIncl X A A' h) := by
    rw [Work.Cohomology.restr, ← Work.Cohomology.dualChainMap_comp, subIncl_spec]
  have hβA : (ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℤ (TopCat.of A) (TopCat.of A')
      (subIncl X A A' h)).f n)) β.1 = 0 := key_aux X A A' h n β.1 β.2
  have hzero : (ModuleCat.Hom.hom ((Work.Cohomology.restr ℤ X A).f n)) x₁ = 0 := by
    have h2 : (ModuleCat.Hom.hom ((Work.Cohomology.restr ℤ X A).f n)) x₁
        = (ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℤ (TopCat.of A) (TopCat.of A')
            (subIncl X A A' h)).f n))
          ((ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℤ (TopCat.of A') X
            (Work.Cohomology.subtypeIncl X A')).f n)) x₁) := by
      rw [hsq, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [h2, hx₁]
    exact hβA
  exact ⟨⟨x₁, hzero⟩, by
    apply Subtype.ext
    rw [Work.Cohomology.relMapLM_coe]
    exact hx₁⟩

lemma relMapLM_range_eq_ker (X : TopCat) (A A' : Set X) (h : A ⊆ A') (n : ℕ) :
    LinearMap.range (Work.Cohomology.relMapLM ℤ (X₁ := X) (X₂ := X) A A' (𝟙 X) h n)
      = LinearMap.ker (Work.Cohomology.relMapLM ℤ (X₁ := TopCat.of A') (X₂ := X)
          (A₁' X A A') A (Work.Cohomology.subtypeIncl X A') (subIncl_mem X A A' h) n) := by
  apply le_antisymm
  · intro y hy
    rw [LinearMap.mem_ker]
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    apply Subtype.ext
    show ((Work.Cohomology.relMapLM ℤ (X₁ := TopCat.of A') (X₂ := X) (A₁' X A A') A
        (Work.Cohomology.subtypeIncl X A') (subIncl_mem X A A' h) n)
      ((Work.Cohomology.relMapLM ℤ (X₁ := X) (X₂ := X) A A' (𝟙 X) h n) x)).1 = 0
    simp only [Work.Cohomology.relMapLM_coe, Work.Cohomology.dualChainMap_id,
      HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]
    exact x.2
  · intro y hy
    rw [LinearMap.mem_ker] at hy
    have hy1 : (ModuleCat.Hom.hom ((Work.Cohomology.restr ℤ X A').f n)) y.1 = 0 := by
      have h := congrArg (fun z => z.1) hy
      rw [Work.Cohomology.relMapLM_coe] at h
      simpa [Work.Cohomology.restr] using h
    refine LinearMap.mem_range.mpr ⟨⟨y.1, ?_⟩, ?_⟩
    · rw [Work.Cohomology.relKern, LinearMap.mem_ker]
      exact hy1
    · apply Subtype.ext
      rw [relMapLM_id_coe]

lemma tripleShort_shortExact (X : TopCat) (A A' : Set X) (h : A ⊆ A') :
    (tripleShort X A A' h).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker, ShortComplex.map_f, ShortComplex.map_g,
      HomologicalComplex.eval_map, HomologicalComplex.eval_map]
    simp only [tripleShort_f, tripleShort_g, tripleF_f, tripleG_f, ModuleCat.hom_ofHom]
    exact relMapLM_range_eq_ker X A A' h n
  · rw [ShortComplex.map_f, HomologicalComplex.eval_map, ModuleCat.mono_iff_injective]
    simp only [tripleShort_f, tripleF_f, ModuleCat.hom_ofHom]
    exact relMapLM_id_injective X A A' h n
  · rw [ShortComplex.map_g, HomologicalComplex.eval_map, ModuleCat.epi_iff_surjective]
    simp only [tripleShort_g, tripleG_f, ModuleCat.hom_ofHom]
    exact relMapLM_g_surjective X A A' h n

theorem tripleLES (X : TopCat) (A A' : Set X) (hAA' : A ⊆ A') (n : ℕ)
    (h1 : Subsingleton (Work.Cohomology.relCohomology ℤ X A' n))
    (h2 : Subsingleton (Work.Cohomology.relCohomology ℤ (TopCat.of {x : X // x ∈ A'})
      ((Subtype.val : {x : X // x ∈ A'} → X) ⁻¹' A) n)) :
    Subsingleton (Work.Cohomology.relCohomology ℤ X A n) := by
  have hS : (tripleShort X A A' hAA').ShortExact := tripleShort_shortExact X A A' hAA'
  have hex := hS.homology_exact₂ n
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
  have h1' : Subsingleton ↥((tripleShort X A A' hAA').X₁.homology n) := h1
  have hrange :
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (tripleShort X A A' hAA').f n)).range
        = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Submodule.mem_bot]
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx
    rw [← hy]
    have hy0 : y = 0 := @Subsingleton.elim _ h1' y 0
    rw [hy0, map_zero]
  have hker :
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (tripleShort X A A' hAA').g n)).ker
        = ⊥ := by
    rw [← hex]
    exact hrange
  have hinj : Function.Injective
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (tripleShort X A A' hAA').g n)) :=
    LinearMap.ker_eq_bot.mp hker
  have h2' : Subsingleton ↥((tripleShort X A A' hAA').X₃.homology n) := h2
  refine Subsingleton.intro (fun a b => ?_)
  exact hinj (@Subsingleton.elim _ h2'
    ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (tripleShort X A A' hAA').g n)) a)
    ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (tripleShort X A A' hAA').g n)) b))

end

end Work.Cohomology.Endgame
