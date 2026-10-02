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
# The long exact sequence of a triple, and the surjectivity of the triple map

For subsets `A ⊆ A' ⊆ X` of a topological space, the relative cochain complexes fit into the short
exact sequence of the triple

`0 ⟶ C^*(X,A') ⟶ C^*(X,A) ⟶ C^*(A', A'∩A) ⟶ 0`

(the first map the inclusion of the smaller relative complex, the second the pullback along the
inclusion `A' ⊆ X`).  Passing to cohomology gives the long exact sequence of the triple
`A ⊆ A' ⊆ X`, whose exactness in degree `n` at the middle group `H^n(A',A'∩A)` says that

`H^n(X,A) ⟶ H^n(A',A'∩A)`

has image `ker (H^n(A',A'∩A) ⟶ H^{n+1}(X,A'))`.  Consequently, if `H^{n+1}(X,A') = 0`, this map is
surjective: this is `tripleLESSurj`, the form in which the vanishing of a triple term is used in
the endgame of the exotic 7-sphere computation.

## Main results

* `relInclSet`, `relCohTripleShort` — the first map and the short complex of the triple;
* `relCohTriple_shortExact` — the short complex of a triple is short exact;
* `tripleLESSurj_aux`, `tripleLESSurj` — the map `H^n(X,A) ⟶ H^n(A',A'∩A)` is surjective when
  `H^{n+1}(X,A') = 0`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology.Endgame

noncomputable section

/-- The preimage of `A` in the subspace `A'`, i.e. the subset of `A'` on which the relative complex
of the pair `(A', A' ∩ A)` lives.  The inclusion `A' ↪ X` necessarily displays it in this form. -/
abbrev preA (X : TopCat) (A A' : Set X) : Set (TopCat.of A') :=
  (Subtype.val : {x : X // x ∈ A'} → X) ⁻¹' A

/-- The condition `∀ x ∈ preA X A A', x ∈ A` (so that `(A', A'∩A)` is a pair). -/
theorem hsubA (X : TopCat) (A A' : Set X) :
    ∀ x ∈ preA X A A', (ConcreteCategory.hom (Work.Cohomology.subtypeIncl X A')) x ∈ A :=
  fun x hx => by simp only [Work.Cohomology.subtypeIncl]; exact hx

/-! ## The inclusion of the smaller subset and the factorization of the restriction

The restriction `C^*(X) ⟶ C^*(A)` factors through `C^*(A')`: the inclusion `A ⊆ X` is the composite
of the "flattening" morphism `A ⟶ {a : A' | a ∈ A}` (of subspaces) followed by the inclusions
`{a : A' | a ∈ A} ⟶ A' ⟶ X`.  This is the only place where the two descriptions of `A` (as a
subset of `X` and as a subset of `A'`) have to be compared. -/

/-- The "flattening" morphism `A ⟶ {a : A' | a ∈ A}`, sending `a` to `a` regarded as an element of
`A'`.  It is a homeomorphism, but only the factorization below is needed. -/
def subtypeInclPre (X : TopCat) (A A' : Set X) (h : A ⊆ A') :
    TopCat.of A ⟶ TopCat.of (preA X A A') :=
  TopCat.ofHom ⟨fun a => ⟨⟨a.1, h a.2⟩, a.2⟩,
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val (fun a => h a.2))
      (fun a => a.2)⟩

/-- The factorization of the inclusion `A ⊆ X` through `A'`. -/
lemma subtypeInclPre_spec (X : TopCat) (A A' : Set X) (h : A ⊆ A') :
    subtypeInclPre X A A' h ≫ Work.Cohomology.subtypeIncl (TopCat.of A') (preA X A A')
      ≫ Work.Cohomology.subtypeIncl X A' = Work.Cohomology.subtypeIncl X A := by
  apply TopCat.ext; intro a; rfl

/-- The restriction `C^*(X) ⟶ C^*(A)` factors through the restriction to `A'`. -/
theorem restr_comp_eq (X : TopCat) (A A' : Set X) (h : A ⊆ A') :
    Work.Cohomology.restr ℤ X A
      = Work.Cohomology.restr ℤ X A' ≫
          (Work.Cohomology.restr ℤ (TopCat.of A') (preA X A A') ≫
          Work.Cohomology.dualChainMap ℤ (TopCat.of A) (TopCat.of (preA X A A'))
            (subtypeInclPre X A A' h)) := by
  rw [Work.Cohomology.restr, Work.Cohomology.restr, Work.Cohomology.restr]
  rw [← subtypeInclPre_spec X A A' h]
  rw [Work.Cohomology.dualChainMap_comp ℤ (f := subtypeInclPre X A A' h)
    (g := Work.Cohomology.subtypeIncl (TopCat.of A') (preA X A A')
      ≫ Work.Cohomology.subtypeIncl X A')]
  rw [Work.Cohomology.dualChainMap_comp ℤ (f := Work.Cohomology.subtypeIncl (TopCat.of A') (preA X A A'))
    (g := Work.Cohomology.subtypeIncl X A')]
  rw [Category.assoc]

/-- The evaluated form of `restr_comp_eq`. -/
theorem restr_comp_apply (X : TopCat) (A A' : Set X) (h : A ⊆ A') (n : ℕ)
    (x : (Work.Cohomology.singularCochainComplex ℤ X).X n) :
    ((Work.Cohomology.restr ℤ X A).f n).hom x
      = ((Work.Cohomology.dualChainMap ℤ (TopCat.of A) (TopCat.of (preA X A A'))
          (subtypeInclPre X A A' h)).f n).hom
        (((Work.Cohomology.restr ℤ (TopCat.of A') (preA X A A')).f n).hom
          (((Work.Cohomology.restr ℤ X A').f n).hom x)) := by
  rw [restr_comp_eq X A A' h, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]

/-! ## The relative cochains of nested pairs -/

/-- **The relative cochains are contravariantly monotone in the subspace**: for `A ⊆ A'` a cochain
of `X` vanishing on chains in `A'` vanishes on chains in `A`. -/
theorem relKern_mono (X : TopCat) (A A' : Set X) (h : A ⊆ A') (n : ℕ) :
    Work.Cohomology.relKern ℤ X A' n ≤ Work.Cohomology.relKern ℤ X A n := by
  intro x hx
  rw [Work.Cohomology.relKern, LinearMap.mem_ker] at hx ⊢
  rw [restr_comp_apply X A A' h n x, hx]
  simp

/-- **The restriction of a relative cochain to `A'` is surjective**: every cochain on `A'` that
vanishes on chains in `A` is the restriction of a cochain on `X` vanishing on chains in `A`.

Extend the cochain to `X` (possible on the level of cochains), and observe that the extension
automatically vanishes on chains in `A`, because it restricts to `0` on `A ⊆ A'`. -/
theorem relMapLM_surjective (X : TopCat) (A A' : Set X) (h : A ⊆ A')
    (hh : ∀ x ∈ preA X A A', (ConcreteCategory.hom (Work.Cohomology.subtypeIncl X A')) x ∈ A) (n : ℕ) :
    Function.Surjective (Work.Cohomology.relMapLM ℤ (preA X A A') A
      (Work.Cohomology.subtypeIncl X A') hh n) := by
  intro ψ
  obtain ⟨Φ, hΦ⟩ := Work.Cohomology.surjective_restr ℤ X A' n ψ.1
  refine ⟨⟨Φ, ?_⟩, ?_⟩
  · rw [Work.Cohomology.relKern, LinearMap.mem_ker]
    rw [restr_comp_apply X A A' h n Φ, hΦ]
    have hψ : ((Work.Cohomology.restr ℤ (TopCat.of A') (preA X A A')).f n).hom (↑ψ) = 0 := ψ.2
    rw [hψ]
    simp
  · apply Subtype.ext
    rw [Work.Cohomology.relMapLM_coe]
    rw [Work.Cohomology.restr] at hΦ
    exact hΦ

/-! ## The inclusion `C^*(X,A') ⟶ C^*(X,A)` -/

/-- The degreewise inclusion of the relative cochains of `(X,A')` into those of `(X,A)`. -/
def relInclSetHom (X : TopCat) (A A' : Set X) (h : A ⊆ A') (n : ℕ) :
    (Work.Cohomology.relComplex ℤ X A').X n ⟶ (Work.Cohomology.relComplex ℤ X A).X n :=
  ModuleCat.ofHom (Submodule.inclusion (relKern_mono X A A' h n))

@[simp] theorem relInclSetHom_val (X : TopCat) (A A' : Set X) (h : A ⊆ A') (n : ℕ)
    (x : (Work.Cohomology.relComplex ℤ X A').X n) :
    ((relInclSetHom X A A' h n).hom x).1 = x.1 := rfl

@[simp] theorem relInclSetHom_val_conc (X : TopCat) (A A' : Set X) (h : A ⊆ A') (n : ℕ)
    (x : (Work.Cohomology.relComplex ℤ X A').X n) :
    (ConcreteCategory.hom (relInclSetHom X A A' h n) x).1 = x.1 := rfl

/-- The differential of the relative complex, evaluated on the underlying cochains. -/
@[simp] theorem relComplex_d_val (X : TopCat) (A : Set X) (n : ℕ)
    (x : (Work.Cohomology.relComplex ℤ X A).X n) :
    (((Work.Cohomology.relComplex ℤ X A).d n (n+1)).hom x).1
      = ((Work.Cohomology.singularCochainComplex ℤ X).d n (n+1)).hom x.1 := by
  rw [Work.Cohomology.relComplex_d]
  rfl

/-- The map of relative complexes of a nested pair, evaluated on the underlying cochains. -/
@[simp] theorem relComplexMap_f_val (X : TopCat) (A A' : Set X) (h : A ⊆ A')
    (hh : ∀ x ∈ preA X A A', (ConcreteCategory.hom (Work.Cohomology.subtypeIncl X A')) x ∈ A) (n : ℕ)
    (y : (Work.Cohomology.relComplex ℤ X A).X n) :
    (((Work.Cohomology.relComplexMap ℤ (preA X A A') A (Work.Cohomology.subtypeIncl X A')
        hh).f n).hom y).1
      = ((Work.Cohomology.dualChainMap ℤ (TopCat.of A') X (Work.Cohomology.subtypeIncl X A')).f n).hom y.1 := rfl

@[simp] theorem relComplexMap_f_val_conc (X : TopCat) (A A' : Set X) (h : A ⊆ A')
    (hh : ∀ x ∈ preA X A A', (ConcreteCategory.hom (Work.Cohomology.subtypeIncl X A')) x ∈ A) (n : ℕ)
    (y : (Work.Cohomology.relComplex ℤ X A).X n) :
    (ConcreteCategory.hom ((Work.Cohomology.relComplexMap ℤ (preA X A A') A
        (Work.Cohomology.subtypeIncl X A') hh).f n) y).1
      = ((Work.Cohomology.dualChainMap ℤ (TopCat.of A') X (Work.Cohomology.subtypeIncl X A')).f n).hom y.1 := rfl

/-- The relative `n`-cochains of `(X,A)` are those vanishing on `A`. -/
@[simp] theorem relKern_mem (X : TopCat) (A : Set X) (n : ℕ)
    (x : (Work.Cohomology.relComplex ℤ X A).X n) :
    ((Work.Cohomology.restr ℤ X A).f n).hom x.1 = 0 := x.2

/-- The relative `n`-cochains of `(X,A)` are the kernel of the pullback along `A ↪ X`. -/
@[simp] theorem relKern_mem_dual (X : TopCat) (A : Set X) (n : ℕ)
    (x : (Work.Cohomology.relComplex ℤ X A).X n) :
    ((Work.Cohomology.dualChainMap ℤ (TopCat.of A) X (Work.Cohomology.subtypeIncl X A)).f n).hom x.1 = 0 := by
  have h := relKern_mem X A n x
  rwa [Work.Cohomology.restr] at h

/-- The same statement for an element of the subtype `relKern`. -/
@[simp] theorem relKern_mem_dual' (X : TopCat) (A : Set X) (n : ℕ)
    (x : Work.Cohomology.relKern ℤ X A n) :
    ((Work.Cohomology.dualChainMap ℤ (TopCat.of A) X (Work.Cohomology.subtypeIncl X A)).f n).hom
      (x : (Work.Cohomology.singularCochainComplex ℤ X).X n) = 0 := by
  have h : ((Work.Cohomology.restr ℤ X A).f n).hom
      (x : (Work.Cohomology.singularCochainComplex ℤ X).X n) = 0 := x.2
  rwa [Work.Cohomology.restr] at h

/-- Membership in the kernel of the pullback is membership in the relative cochains. -/
theorem mem_relKern_dual (X : TopCat) (A : Set X) (n : ℕ)
    (x : (Work.Cohomology.singularCochainComplex ℤ X).X n)
    (hx : ((Work.Cohomology.dualChainMap ℤ (TopCat.of A) X (Work.Cohomology.subtypeIncl X A)).f n).hom x = 0) :
    x ∈ Work.Cohomology.relKern ℤ X A n := hx

@[simp] theorem relMapLM_val (X : TopCat) (A A' : Set X) (h : A ⊆ A')
    (hh : ∀ x ∈ preA X A A', (ConcreteCategory.hom (Work.Cohomology.subtypeIncl X A')) x ∈ A) (n : ℕ)
    (x : (Work.Cohomology.relComplex ℤ X A).X n) :
    (((Work.Cohomology.relMapLM ℤ (preA X A A') A (Work.Cohomology.subtypeIncl X A')
        hh n) x).1)
      = ((Work.Cohomology.dualChainMap ℤ (TopCat.of A') X (Work.Cohomology.subtypeIncl X A')).f n).hom x.1 := rfl

/-- **The inclusion of the relative cochain complexes of a nested pair.** -/
def relInclSet (X : TopCat) (A A' : Set X) (h : A ⊆ A') :
    Work.Cohomology.relComplex ℤ X A' ⟶ Work.Cohomology.relComplex ℤ X A :=
  CochainComplex.ofHom (fun n => relInclSetHom X A A' h n) (fun n => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
    rw [Work.Cohomology.relComplex_d, Work.Cohomology.relComplex_d]
    apply Subtype.ext
    show ((Work.Cohomology.singularCochainComplex ℤ X).d n (n+1)).hom x.1
      = ((Work.Cohomology.singularCochainComplex ℤ X).d n (n+1)).hom x.1
    rfl)

@[simp] theorem relInclSet_f (X : TopCat) (A A' : Set X) (h : A ⊆ A') (n : ℕ) :
    (relInclSet X A A' h).f n = relInclSetHom X A A' h n := rfl

/-- **The inclusion of relative cochains is the kernel of the restriction to `A'`.** -/
theorem relInclSetHom_range (X : TopCat) (A A' : Set X) (h : A ⊆ A')
    (hh : ∀ x ∈ preA X A A', (ConcreteCategory.hom (Work.Cohomology.subtypeIncl X A')) x ∈ A) (n : ℕ) :
    LinearMap.range (Submodule.inclusion (relKern_mono X A A' h n))
      = LinearMap.ker (Work.Cohomology.relMapLM ℤ (preA X A A') A (Work.Cohomology.subtypeIncl X A')
          hh n) := by
  ext φ
  constructor
  · rintro ⟨ψ, rfl⟩
    apply Subtype.ext
    rw [Work.Cohomology.relMapLM_coe, Submodule.coe_inclusion]
    rw [relKern_mem_dual' X A' n ψ]
    rfl
  · intro hφ
    refine ⟨⟨φ.1, ?_⟩, ?_⟩
    · refine mem_relKern_dual X A' n φ.1 ?_
      have h := congrArg Subtype.val hφ
      rw [Work.Cohomology.relMapLM_coe] at h
      simpa [Submodule.coe_zero] using h
    · apply Subtype.ext
      rw [Submodule.coe_inclusion]

/-- **The composite `C^*(X,A') ⟶ C^*(X,A) ⟶ C^*(A',A)` is zero**: a cochain vanishing on chains in
`A'` pulls back to a cochain on `A'` vanishing on all chains, in particular the zero cochain. -/
theorem relInclSet_comp_relComplexMap (X : TopCat) (A A' : Set X) (h : A ⊆ A')
    (hh : ∀ x ∈ preA X A A', (ConcreteCategory.hom (Work.Cohomology.subtypeIncl X A')) x ∈ A) :
    relInclSet X A A' h ≫ Work.Cohomology.relComplexMap ℤ (preA X A A') A
        (Work.Cohomology.subtypeIncl X A') hh = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f_apply]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
  apply Subtype.ext
  rw [relInclSet_f X A A' h, relComplexMap_f_val X A A' h hh n, relInclSetHom_val X A A' h n]
  simpa using relKern_mem_dual X A' n x

/-! ## The short exact sequence of the triple -/

/-- **The short complex of the triple `A ⊆ A' ⊆ X`**:
`0 ⟶ C^*(X,A') ⟶ C^*(X,A) ⟶ C^*(A', A'∩A) ⟶ 0`. -/
def relCohTripleShort (X : TopCat) (A A' : Set X) (h : A ⊆ A')
    (hh : ∀ x ∈ preA X A A', (ConcreteCategory.hom (Work.Cohomology.subtypeIncl X A')) x ∈ A) :
    ShortComplex (CochainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (relInclSet X A A' h)
    (Work.Cohomology.relComplexMap ℤ (preA X A A') A (Work.Cohomology.subtypeIncl X A') hh)
    (relInclSet_comp_relComplexMap X A A' h hh)

/-- The degreewise injectivity of the first map of the triple sequence, in the "concrete" form in
which the goals appear. -/
theorem relInclSetHom_inj_P (X : TopCat) (A A' : Set X) (h : A ⊆ A') (n : ℕ) :
    Function.Injective (ConcreteCategory.hom (relInclSetHom X A A' h n)) :=
  Submodule.inclusion_injective (relKern_mono X A A' h n)

/-- The degreewise surjectivity of the second map of the triple sequence. -/
theorem relComplexMap_f_surj_P (X : TopCat) (A A' : Set X) (h : A ⊆ A')
    (hh : ∀ x ∈ preA X A A', (ConcreteCategory.hom (Work.Cohomology.subtypeIncl X A')) x ∈ A) (n : ℕ) :
    Function.Surjective (ConcreteCategory.hom ((Work.Cohomology.relComplexMap ℤ (preA X A A') A
        (Work.Cohomology.subtypeIncl X A') hh).f n)) :=
  relMapLM_surjective X A A' h hh n

/-- The degreewise exactness of the triple sequence, in the "concrete" form in which the goals
appear. -/
theorem relInclSetHom_range_P (X : TopCat) (A A' : Set X) (h : A ⊆ A')
    (hh : ∀ x ∈ preA X A A', (ConcreteCategory.hom (Work.Cohomology.subtypeIncl X A')) x ∈ A) (n : ℕ) :
    LinearMap.range (relInclSetHom X A A' h n).hom
      = LinearMap.ker (((Work.Cohomology.relComplexMap ℤ (preA X A A') A
          (Work.Cohomology.subtypeIncl X A') hh).f n).hom) :=
  relInclSetHom_range X A A' h hh n

/-- **The short complex of a triple of subsets is short exact.** -/
theorem relCohTriple_shortExact (X : TopCat) (A A' : Set X) (h : A ⊆ A')
    (hh : ∀ x ∈ preA X A A', (ConcreteCategory.hom (Work.Cohomology.subtypeIncl X A')) x ∈ A) :
    (relCohTripleShort X A A' h hh).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker, ShortComplex.map_f, ShortComplex.map_g,
      HomologicalComplex.eval_map, HomologicalComplex.eval_map]
    simp only [relCohTripleShort]
    exact relInclSetHom_range_P X A A' h hh n
  · rw [ModuleCat.mono_iff_injective, ShortComplex.map_f, HomologicalComplex.eval_map]
    simp only [relCohTripleShort]
    exact relInclSetHom_inj_P X A A' h n
  · rw [ModuleCat.epi_iff_surjective, ShortComplex.map_g, HomologicalComplex.eval_map]
    simp only [relCohTripleShort]
    exact relComplexMap_f_surj_P X A A' h hh n

/-- **The triple long exact sequence: the map `H^n(X,A) ⟶ H^n(A',A'∩A)` is surjective when the
next term `H^{n+1}(X,A')` of the triple sequence vanishes.**

Exactness of the long exact sequence of the triple at `H^n(A',A'∩A)` identifies the image of
`H^n(X,A) ⟶ H^n(A',A'∩A)` with the kernel of the connecting map
`H^n(A',A'∩A) ⟶ H^{n+1}(X,A')`; the latter is zero because its target is a subsingleton. -/
theorem tripleLESSurj_aux (X : TopCat) (A A' : Set X) (hAA' : A ⊆ A')
    (hh : ∀ x ∈ preA X A A', (ConcreteCategory.hom (Work.Cohomology.subtypeIncl X A')) x ∈ A) (n : ℕ)
    (hzero : Subsingleton (Work.Cohomology.relCohomology ℤ X A' (n+1))) :
    Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap ℤ (preA X A A') A (Work.Cohomology.subtypeIncl X A') hh) n)) := by
  have hS : (relCohTripleShort X A A' hAA' hh).ShortExact := relCohTriple_shortExact X A A' hAA' hh
  have hij : (ComplexShape.up ℕ).Rel n (n+1) := by simp [ComplexShape.up]
  have hker : LinearMap.ker ((hS.δ n (n+1) hij).hom) = ⊤ := by
    rw [LinearMap.ker_eq_top]
    apply LinearMap.ext
    intro x
    exact hzero.allEq _ _
  have hrange : LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relCohTripleShort X A A' hAA' hh).g n)) = ⊤ := by
    have hex := hS.homology_exact₃ n (n+1) hij
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
    rw [hex, hker]
  intro y
  have hy : y ∈ LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relCohTripleShort X A A' hAA' hh).g n)) := by
    rw [hrange]; exact Submodule.mem_top
  simp only [relCohTripleShort] at hy
  exact hy

/-- **The triple long exact sequence: the map `H^n(X,A) ⟶ H^n(A',A'∩A)` is surjective when the
next term `H^{n+1}(X,A')` of the triple sequence vanishes.** -/
theorem tripleLESSurj (X : TopCat) (A A' : Set X) (hAA' : A ⊆ A') (n : ℕ)
    (hzero : Subsingleton (Work.Cohomology.relCohomology ℤ X A' (n+1))) :
    Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap ℤ ((Subtype.val : {x : X // x ∈ A'} → X) ⁻¹' A) A (Work.Cohomology.subtypeIncl X A')
        (fun x hx => by simp only [Work.Cohomology.subtypeIncl]; exact hx)) n)) :=
  tripleLESSurj_aux X A A' hAA'
    (fun x hx => by simp only [Work.Cohomology.subtypeIncl]; exact hx) n hzero

end

end Work.Cohomology.Endgame
