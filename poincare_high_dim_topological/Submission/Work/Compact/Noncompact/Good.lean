import Mathlib
import Submission.Work.Compact.Noncompact.Basic
import Submission.Work.Cohomology.excision
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Cohomology.smallLift_cov

/-!
# Hatcher's Lemma 3.27: definitions and bookkeeping

This file sets up the vocabulary for the proof of Hatcher, *Algebraic Topology*, Lemma 3.27
(and hence of the `i = n` case of Proposition 3.29): for a connected `n`-manifold `M` (`n ≥ 1`)
the localization map `Hₙ(M; ℤ) → Hₙ(M, M∖{x}; ℤ)` detects top classes.

## The "goodness" predicate

`Work.Compact.Noncompact.GoodC k X A` is the **chain-level form of Hatcher 3.27 for `A` in
dimension `k+1`**: with `X` the ambient space and `A ⊆ X`,

* `A` is compact;
* (uniqueness, degree `k+1`) if `z` is a relative `(k+1)`-cycle for `A` (its boundary is supported
  in `Aᶜ`) which is *locally trivial* on `A` (for every `x ∈ A` it differs from a boundary by a
  chain supported in `{x}ᶜ`), then `z` itself differs from a boundary by a chain supported in `Aᶜ`;
* (vanishing, degrees `> k+1`) if `z` is a relative cycle for `A` of degree `k+j+2`, then `z`
  differs from a boundary by a chain supported in `Aᶜ`.

This is the chain-level reformulation of "the map `H_{k+1}(X ‖ A) → ∏_{x∈A} H_{k+1}(X ‖ x)` is
injective" together with "`H_i(X ‖ A) = 0` for `i > k+1`", and it is the form in which the
Mayer–Vietoris step and the final support argument are carried out.  The passage between the two
forms is `Work.Compact.Noncompact.HatClass` (see `Submission/Work/Compact/Noncompact/HatClass.lean`).

## Notation

* `Ch X k` — the singular `k`-chains of `X` with `ℤ` coefficients;
* `bdry X k` — the boundary `C_{k+1}(X) → C_k(X)` as a linear map;
* `suppS X S k` — the submodule of `k`-chains supported in `S ⊆ X` (i.e. in the image of the
  chain map `C_k(S) → C_k(X)`);
* `hatH X A k` — Hatcher's `H_k(X ‖ A) = H_k(X, X∖A) = H_k(C_*(X)/C_*(Aᶜ))`.
-/

namespace Work.Compact.Noncompact

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

/-- The singular `k`-chains of `X` with `ℤ` coefficients. -/
abbrev Ch (X : TopCat) (k : ℕ) := (Work.Cohomology.singularChains ℤ X).X k

/-- The singular boundary `C_{k+1}(X) → C_k(X)`, as a linear map. -/
abbrev bdry (X : TopCat) (k : ℕ) : Ch X (k + 1) →ₗ[ℤ] Ch X k :=
  ((Work.Cohomology.singularChains ℤ X).d (k + 1) k).hom

/-- The submodule of `k`-chains of `X` supported in a subset `S ⊆ X`: the image of the map
`C_k(S) → C_k(X)` induced by the inclusion. -/
abbrev suppS (X : TopCat) (S : Set X) (k : ℕ) : Submodule ℤ (Ch X k) :=
  LinearMap.range (((Work.Cohomology.inclChains X S).f k).hom)

/-- Hatcher's `H_k(X ‖ A) = H_k(X, X∖A)`: the `k`-th homology of the relative chains
`C_*(X)/C_*(Aᶜ)`. -/
abbrev hatH (X : TopCat) (A : Set X) (k : ℕ) : ModuleCat ℤ :=
  (RC X (Aᶜ)).homology k

/-- The restriction `H_k(X ‖ B) → H_k(X ‖ A)` for `A ⊆ B`. -/
abbrev hatRes {X : TopCat} {A B : Set X} (h : A ⊆ B) (k : ℕ) :
    hatH X B k ⟶ hatH X A k :=
  relMapHom (X := X) (Set.compl_subset_compl.mpr h) k

/-- **The vanishing part of Hatcher's Lemma 3.27.**  `GoodV k X A` says that `A` is compact and
that `H_j(X, X∖A) = 0` for every `j > k+1`. -/
def GoodV (k : ℕ) (X : TopCat) (A : Set X) : Prop :=
  IsCompact A ∧ ∀ j : ℕ, k + 1 < j → IsZero (hatH X A j)

/-- **Hatcher's Lemma 3.27 for the set `A`, in dimension `k+1`.**  `GoodC k X A` says that `A` is
compact, that a class in `H_{k+1}(X, X∖A)` whose localizations at all points of `A` vanish is zero
(Hatcher's 3.27(a), uniqueness), and that `H_j(X, X∖A) = 0` for all `j > k+1` (3.27(b)). -/
def GoodC (k : ℕ) (X : TopCat) (A : Set X) : Prop :=
  IsCompact A ∧
    (∀ u : hatH X A (k + 1),
      (∀ x (hx : x ∈ A), hatRes (X := X) (B := A) (Set.singleton_subset_iff.mpr hx) (k + 1) u
        = 0) → u = 0) ∧
    (∀ j : ℕ, k + 1 < j → IsZero (hatH X A j))

/-- `A` is a compact subset of the source of a chart of `M` (a "piece in one Euclidean chart"). -/
def IsInChart (n : ℕ) {M : Type} [TopologicalSpace M] (A : Set M) : Prop :=
  ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)), IsCompact A ∧ A ⊆ e.source

/-- The singular `k`-simplices of `X`, as simplices of the singular simplicial set. -/
abbrev SimplexT (X : TopCat) (k : ℕ) : Type :=
  (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk k))

/-- The generator of the singular `k`-chains of `X` associated with a singular simplex. -/
abbrev genC (X : TopCat) (k : ℕ) (σ : SimplexT X k) : Ch X k :=
  Work.Cohomology.gen X k σ

/-- The image of a singular simplex, as a subset of `X`. -/
def SimplexSet {X : TopCat} {k : ℕ} (σ : SimplexT X k) : Set X :=
  Set.range (fun z : stdSimplex ℝ (Fin (k + 1)) =>
    Work.Homology.toSSetObjEquiv' X (Opposite.op (SimplexCategory.mk k)) σ z)

variable {X : TopCat}

/-- Functoriality of the singular chain map in the continuous map. -/
lemma chainMap_comp {Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Work.Cohomology.chainMap ℤ X Y f ≫ Work.Cohomology.chainMap ℤ Y Z g
      = Work.Cohomology.chainMap ℤ X Z (f ≫ g) :=
  (Functor.map_comp _ _ _).symm

/-- Monotonicity of the "supported in" submodule. -/
lemma suppS_mono {S T : Set X} (h : S ⊆ T) (k : ℕ) : suppS X S k ≤ suppS X T k := by
  rintro c ⟨c', rfl⟩
  refine ⟨(Work.Cohomology.chainMap ℤ (TopCat.of S) (TopCat.of T) (inclSet h)).f k c', ?_⟩
  have h2 : Work.Cohomology.chainMap ℤ (TopCat.of S) X (Work.Cohomology.subtypeIncl X S)
      = Work.Cohomology.chainMap ℤ (TopCat.of S) (TopCat.of T) (inclSet h)
        ≫ Work.Cohomology.chainMap ℤ (TopCat.of T) X (Work.Cohomology.subtypeIncl X T) := by
    rw [chainMap_comp, inclSet_comp]
  have h1 : (Work.Cohomology.inclChains X S).f k
      = (Work.Cohomology.chainMap ℤ (TopCat.of S) (TopCat.of T) (inclSet h)).f k
        ≫ (Work.Cohomology.inclChains X T).f k := by
    have h3 := congrArg (fun (φ : Work.Cohomology.singularChains ℤ (TopCat.of S) ⟶
        Work.Cohomology.singularChains ℤ X) => φ.f k) h2
    rw [HomologicalComplex.comp_f] at h3
    exact h3
  rw [h1]
  rfl

/-- The boundary of a chain supported in `S` is supported in `S`. -/
lemma bdry_mem_suppS {S : Set X} (k : ℕ) {c : Ch X (k + 1)}
    (hc : c ∈ suppS X S (k + 1)) : bdry X k c ∈ suppS X S k := by
  obtain ⟨c', rfl⟩ := hc
  refine ⟨(bdry (TopCat.of S) k) c', ?_⟩
  have hcomm := HomologicalComplex.Hom.comm (Work.Cohomology.inclChains X S) (k + 1) k
  have h := congrArg (fun (f : Ch (TopCat.of S) (k + 1) ⟶ Ch X k) => f c') hcomm
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at h
  exact h.symm

/-! ## The restriction maps of Hatcher's `H_{k+1}(X ‖ A)` -/

/-- The map `cokernel.map` depends only on its two arguments, not on the proof of compatibility. -/
theorem cokernel_map_eq_of_proof {C : Type*} [Category C] [HasZeroMorphisms C] {X Y X' Y' : C}
    (f : X ⟶ Y) [HasCokernel f] (f' : X' ⟶ Y') [HasCokernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
    (w₁ w₂ : f ≫ q = p ≫ f') : cokernel.map f f' p q w₁ = cokernel.map f f' p q w₂ :=
  congrArg (cokernel.map f f' p q) (Subsingleton.elim w₁ w₂)

/-- `relMap` depends only on the two sets, not on the proof of the inclusion. -/
theorem relMap_eq_of_subset_eq {X : TopCat} {A B : Set X} (h₁ h₂ : A ⊆ B) :
    relMap h₁ = relMap h₂ := by
  refine (cancel_epi (cokernel.π (Work.Cohomology.inclChains X A))).1 ?_
  simp only [cokernel_π_relMap, Category.id_comp]

/-- `relMapHom` depends only on the two sets, not on the proof of the inclusion. -/
theorem relMapHom_eq_of_subset_eq {X : TopCat} {A B : Set X} (h₁ h₂ : A ⊆ B) (k : ℕ) :
    relMapHom h₁ k = relMapHom h₂ k := by
  show HomologicalComplex.homologyMap (relMap h₁) k
    = HomologicalComplex.homologyMap (relMap h₂) k
  rw [relMap_eq_of_subset_eq h₁ h₂]

/-- The restriction maps are functorial: `hatRes (refl A) = id`. -/
theorem hatRes_rfl {X : TopCat} (A : Set X) (k : ℕ) :
    hatRes (X := X) (subset_refl A) k = 𝟙 (hatH X A k) := by
  show relMapHom (Set.compl_subset_compl.mpr (subset_refl A)) k = 𝟙 (hatH X A k)
  rw [relMapHom_eq_of_subset_eq (Set.compl_subset_compl.mpr (subset_refl A)) (subset_refl Aᶜ)]
  exact relMapHom_rfl k

/-- The restriction maps are functorial: `hatRes` is contravariant. -/
theorem hatRes_comp {X : TopCat} {A B C : Set X} (h₁ : A ⊆ B) (h₂ : B ⊆ C) (k : ℕ) :
    hatRes (X := X) h₂ k ≫ hatRes (X := X) h₁ k = hatRes (X := X) (h₁.trans h₂) k := by
  show relMapHom (Set.compl_subset_compl.mpr h₂) k ≫ relMapHom (Set.compl_subset_compl.mpr h₁) k
    = relMapHom (Set.compl_subset_compl.mpr (h₁.trans h₂)) k
  rw [relMapHom_comp]

/-! ## The class of a relative cycle in `H_{k+1}(X, X∖S)` -/

/-- The projection of a chain of the total complex of a pair which is killed on the subspace. -/
theorem cokernel_f_apply_eq_zero_of_mem_range {C D : ChainComplex (ModuleCat ℤ) ℕ} (f : C ⟶ D)
    (k : ℕ) {y : D.X k} (hy : y ∈ LinearMap.range ((f.f k).hom)) :
    ((cokernel.π f).f k) y = 0 := by
  obtain ⟨x, rfl⟩ := hy
  have h0 := congrArg (fun (φ : C ⟶ cokernel f) => φ.f k) (cokernel.condition f)
  rw [HomologicalComplex.zero_f, HomologicalComplex.comp_f] at h0
  rw [← ModuleCat.comp_apply, h0]
  simp

/-- The image of a chain in the relative quotient complex `C_*(X)/C_*(S)`. -/
abbrev hatQ {X : TopCat} (S : Set X) (k : ℕ) (z : Ch X (k + 1)) :
    (RC X S).X (k + 1) :=
  ((cokernel.π (Work.Cohomology.inclChains X S)).f (k + 1)) z

/-- The image of a chain supported in `S` vanishes in the quotient complex `C_*(X)/C_*(S)`. -/
theorem hatQ_eq_zero_of_mem_suppS {X : TopCat} {S : Set X} {k : ℕ} {y : Ch X (k + 1)}
    (hy : y ∈ suppS X S (k + 1)) : hatQ S k y = 0 :=
  cokernel_f_apply_eq_zero_of_mem_range (Work.Cohomology.inclChains X S) (k + 1) hy

/-- The singleton morphism `ℤ → C_{k+1}(X)/C_{k+1}(S)` sending `1` to the image of `z`. -/
noncomputable abbrev hatSingleton {X : TopCat} (S : Set X) (k : ℕ) (z : Ch X (k + 1)) :
    ModuleCat.of ℤ ℤ ⟶ (RC X S).X (k + 1) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ((RC X S).X (k + 1))
    (hatQ S k z))

/-- **A relative cycle condition.**  If the boundary of `z` is supported in `S`, the image of `z`
in the quotient complex `C_*(X)/C_*(S)` is a cycle. -/
theorem hatSingleton_comp_d {X : TopCat} (S : Set X) (k : ℕ) (z : Ch X (k + 1))
    (hz : bdry X k z ∈ suppS X S k) :
    hatSingleton S k z ≫ (RC X S).d (k + 1) k = 0 := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero, ModuleCat.hom_ofHom]
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, one_smul,
    LinearMap.zero_apply]
  have hcomm := HomologicalComplex.Hom.comm (cokernel.π (Work.Cohomology.inclChains X S))
    (k + 1) k
  have h2 := congrArg ModuleCat.Hom.hom hcomm
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h2
  have h3 := DFunLike.congr_fun h2 z
  simp only [LinearMap.comp_apply] at h3
  change ModuleCat.Hom.hom ((cokernel (Work.Cohomology.inclChains X S)).d (k + 1) k)
    (ModuleCat.Hom.hom ((cokernel.π (Work.Cohomology.inclChains X S)).f (k + 1)) z) = 0
  rw [h3]
  exact cokernel_f_apply_eq_zero_of_mem_range (Work.Cohomology.inclChains X S) k hz

/-- The cycle in `C_*(X)/C_*(S)` determined by a relative cycle `z`. -/
noncomputable abbrev hatCycHom {X : TopCat} (S : Set X) (k : ℕ) (z : Ch X (k + 1))
    (hz : bdry X k z ∈ suppS X S k) :
    ModuleCat.of ℤ ℤ ⟶ (RC X S).cycles (k + 1) :=
  (RC X S).liftCycles (hatSingleton S k z) k
    ((ComplexShape.down ℕ).next_eq' (i := k + 1) (j := k) rfl) (hatSingleton_comp_d S k z hz)

/-- The underlying chain of the cycle `hatCycHom`. -/
theorem iCycles_hatCycHom {X : TopCat} (S : Set X) (k : ℕ) (z : Ch X (k + 1))
    (hz : bdry X k z ∈ suppS X S k) :
    hatCycHom S k z hz ≫ (RC X S).iCycles (k + 1)
      = hatSingleton S k z :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- The class in `H_{k+1}(X, X∖S)` of a relative cycle, as a morphism out of `ℤ`. -/
noncomputable abbrev hatClassHom {X : TopCat} (S : Set X) (k : ℕ) (z : Ch X (k + 1))
    (hz : bdry X k z ∈ suppS X S k) :
    ModuleCat.of ℤ ℤ ⟶ (RC X S).homology (k + 1) :=
  hatCycHom S k z hz ≫ (RC X S).homologyπ (k + 1)

/-- The class in `H_{k+1}(X, X∖S)` of a relative cycle `z` (a chain whose boundary is supported
in `S`). -/
noncomputable abbrev hatClass {X : TopCat} (S : Set X) (k : ℕ) (z : Ch X (k + 1))
    (hz : bdry X k z ∈ suppS X S k) : (RC X S).homology (k + 1) :=
  (hatClassHom S k z hz).hom 1

end

end Work.Compact.Noncompact
