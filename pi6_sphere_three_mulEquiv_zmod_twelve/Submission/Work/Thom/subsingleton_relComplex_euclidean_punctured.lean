import Mathlib
import Submission.Work.Thom.EucCube
import Submission.Work.Thom.Cohomology
import Submission.Work.Cohomology.homotopyEquiv
import Submission.Work.Cohomology.isIso_homologyMap_tau1
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.exists_relComplexMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000

/-!
# The vanishing of `H^m(W × ℝⁿ, W × (ℝⁿ∖0))` below degree `n`, cleanly

This file proves `Work.Thom.subsingleton_relComplex_euclidean_punctured`: from the vanishing of
the relative cohomology of the *cube* pair `(W × [-1,1]ⁿ, W × ∂[-1,1]ⁿ)` below degree `n` one
deduces the vanishing of the relative cohomology of the *punctured Euclidean* pair
`(W × ℝⁿ, W × (ℝⁿ∖0))` below degree `n`.

The reduction is through two homotopy equivalences of pairs

* the coordinate clamp `ℝⁿ → [-1,1]ⁿ`, which is a homotopy equivalence of pairs
  `(ℝⁿ, ℝⁿ∖0) → ([-1,1]ⁿ, [-1,1]ⁿ∖0)`;
* the radial retraction of the punctured cube `[-1,1]ⁿ∖0` onto its boundary `∂[-1,1]ⁿ`;

each of which induces an isomorphism on relative cohomology.

Because of the `dualZ` clash described in `Submission/Work/Thom/CLEAN_TOOLS.md`, the two general
tools used by the reduction (the five lemma for the relative cochain complex of a pair, and its
consequence that a homotopy equivalence of pairs induces a bijection on relative cohomology)
cannot be imported from `Submission/Work/Thom/relCohomology_prod_contractible.lean` /
`Submission/Work/Thom/bijective_relCohMap_of_homotopyEquiv.lean`.  They are therefore re-proved
here from the clean tools (`Work.Cohomology.pairShort`, `pairShort_shortExact`,
`Work.Cohomology.isIso_homologyMap_tau1`, `Work.Cohomology.homotopyEquiv`) in the namespace
`Work.Thom.EuclCleanInfra`.
-/

namespace Work.Thom

namespace EuclCleanInfra

open CategoryTheory AlgebraicTopology

noncomputable section

/-- The map on relative cochains of a map of pairs is compatible with the inclusion of the relative
cochains into the absolute ones. -/
theorem relComplexMap_comp_relIncl_local {R : Type} [CommRing R] {X₁ X₂ : TopCat} (A₁ : Set X₁)
    (A₂ : Set X₂) (f : X₁ ⟶ X₂) (h : ∀ x ∈ A₁, f x ∈ A₂) :
    Work.Cohomology.relComplexMap R A₁ A₂ f h ≫ Work.Cohomology.relIncl R X₁ A₁ =
      Work.Cohomology.relIncl R X₂ A₂ ≫ Work.Cohomology.dualChainMap R X₁ X₂ f := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Work.Cohomology.relComplexMap_f,
    Work.Cohomology.relIncl_f, Work.Cohomology.relIncl_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Work.Cohomology.relMapLM_coe R A₁ A₂ f h n x

/-- **The five lemma for the relative cochain complex of a pair.**  If a map of pairs
`f : (X₁,A₁) → (X₂,A₂)` induces an isomorphism on the absolute cohomology of `X` and of `A`
(in every degree), then it induces an isomorphism on the relative cohomology of the pair in every
degree.  This is `Work.Cohomology.isIso_homologyMap_tau1` applied to the morphism of short exact
sequences `pairShort R X₂ A₂ ⟶ pairShort R X₁ A₁` of `0 ⟶ C^*(–,–) ⟶ C^*(–) ⟶ C^*(A) ⟶ 0`. -/
theorem isIso_homologyMap_relComplexMap {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂)
    (f : X₁ ⟶ X₂) (h : ∀ x ∈ A₁, (ConcreteCategory.hom f) x ∈ A₂) (R : Type) [CommRing R] :
    (∀ m, CategoryTheory.IsIso
        (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap R X₁ X₂ f) m)) →
      (∀ m, CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap R
        (TopCat.of A₁) (TopCat.of A₂) (Work.Cohomology.relMapSub A₁ A₂ f h)) m)) →
      ∀ n, CategoryTheory.IsIso
        (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap R A₁ A₂ f h) n) := by
  intro hf hg n
  let S₁ : ShortComplex (CochainComplex (ModuleCat R) ℕ) := Work.Cohomology.pairShort R X₂ A₂
  let S₂ : ShortComplex (CochainComplex (ModuleCat R) ℕ) := Work.Cohomology.pairShort R X₁ A₁
  have hS₁ : S₁.ShortExact := Work.Cohomology.pairShort_shortExact R X₂ A₂
  have hS₂ : S₂.ShortExact := Work.Cohomology.pairShort_shortExact R X₁ A₁
  let φ : S₁ ⟶ S₂ :=
    { τ₁ := Work.Cohomology.relComplexMap R A₁ A₂ f h
      τ₂ := Work.Cohomology.dualChainMap R X₁ X₂ f
      τ₃ := Work.Cohomology.dualChainMap R (TopCat.of A₁) (TopCat.of A₂)
              (Work.Cohomology.relMapSub A₁ A₂ f h)
      comm₁₂ := by
        change Work.Cohomology.relComplexMap R A₁ A₂ f h ≫ Work.Cohomology.relIncl R X₁ A₁
          = Work.Cohomology.relIncl R X₂ A₂ ≫ Work.Cohomology.dualChainMap R X₁ X₂ f
        exact relComplexMap_comp_relIncl_local A₁ A₂ f h
      comm₂₃ := by
        change Work.Cohomology.dualChainMap R X₁ X₂ f ≫ Work.Cohomology.restr R X₁ A₁
          = Work.Cohomology.restr R X₂ A₂ ≫ Work.Cohomology.dualChainMap R (TopCat.of A₁)
              (TopCat.of A₂) (Work.Cohomology.relMapSub A₁ A₂ f h)
        exact Work.Cohomology.dualChainMap_restr_comp R A₁ A₂ f h }
  have hkey := Work.Cohomology.isIso_homologyMap_tau1 R φ hS₁ hS₂ hf hg n
  have hτ : φ.τ₁ = Work.Cohomology.relComplexMap R A₁ A₂ f h := rfl
  rwa [hτ] at hkey

/-- If `f : C(X,Y)` is the underlying map of a homotopy equivalence `e : X ≃ₕ Y`, then `f` induces
an isomorphism on singular cohomology in every degree — equivalently, on the homology of the
dual (cochain) complex.  This is `Work.Cohomology.homotopyEquiv` together with the fact that
`Work.Cohomology.singularCohomologyMap` is *defined* as the map induced on the homology of
`Work.Cohomology.dualChainMap`. -/
theorem isIso_dualChainMap_of_homotopyEquiv {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (e : ContinuousMap.HomotopyEquiv X Y)
    (he : ⇑e.toFun = ⇑f) (R : Type) [CommRing R] (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.dualChainMap R (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) n) := by
  have hfe : (TopCat.ofHom f : TopCat.of X ⟶ TopCat.of Y) = TopCat.ofHom e.toFun := by
    ext x
    exact (congrFun he x).symm
  rw [hfe]
  exact Work.Cohomology.homotopyEquiv R (TopCat.of X) (TopCat.of Y) (TopCat.ofHom e.toFun)
    (TopCat.ofHom e.invFun) e.left_inv.some e.right_inv.some n

/-- **A homotopy equivalence of pairs induces a bijection on relative cohomology.**

If `f : X → Y` is a homotopy equivalence (`e1`) which restricts — up to the identification
`he2` — to a homotopy equivalence `A → B` of the subspaces (`e2`), then the pullback of relative
cohomology `H^n(Y,B;ℤ) → H^n(X,A;ℤ)` is a bijection in every degree.

The proof applies the five lemma `isIso_homologyMap_relComplexMap` to the morphism
`pairShort ℤ Y B ⟶ pairShort ℤ X A` of short exact sequences of pairs; its two outer components
are isomorphisms on homology because they are induced by the homotopy equivalences `e1` and `e2`
(`isIso_dualChainMap_of_homotopyEquiv`). -/
theorem bijective_relCohMap_of_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : ∀ x ∈ A, f x ∈ B)
    (e1 : ContinuousMap.HomotopyEquiv X Y) (he1 : ⇑e1.toFun = ⇑f)
    (e2 : ContinuousMap.HomotopyEquiv ↥A ↥B)
    (he2 : ∀ q : ↥A, ((e2.toFun q : ↥B) : Y) = f (q : X)) :
    ∀ n, Function.Bijective (relCohMap f A B hf ℤ n).hom := by
  intro n
  have hf' : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.dualChainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) k) :=
    fun k => isIso_dualChainMap_of_homotopyEquiv f e1 he1 ℤ k
  have hsub : Work.Cohomology.relMapSub A B (TopCat.ofHom f) hf = TopCat.ofHom e2.toFun := by
    ext q
    simp only [Work.Cohomology.relMapSub]
    exact (he2 q).symm
  have hg' : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.dualChainMap ℤ (TopCat.of ↥A) (TopCat.of ↥B)
        (Work.Cohomology.relMapSub A B (TopCat.ofHom f) hf)) k) := by
    intro k
    rw [hsub]
    exact isIso_dualChainMap_of_homotopyEquiv e2.toFun e2 rfl ℤ k
  have hIso : CategoryTheory.IsIso (relCohMap f A B hf ℤ n) :=
    isIso_homologyMap_relComplexMap (X₁ := TopCat.of X) (X₂ := TopCat.of Y)
      A B (TopCat.ofHom f) hf ℤ hf' hg' n
  exact (ConcreteCategory.isIso_iff_bijective (relCohMap f A B hf ℤ n)).mp hIso

end

end EuclCleanInfra

end Work.Thom

namespace Work.Thom
namespace EuclPunctClean

noncomputable section

/-! ## The coordinate clamp -/

/-- Coordinate-wise clamping into the cube: `x ↦ (min 1 (max (-1) (x i)))ᵢ`. -/
def clampFun (n : ℕ) (x : Fin n → ℝ) : Fin n → ℝ := fun i => min 1 (max (-1) (x i))

theorem clampFun_apply (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    clampFun n x i = min 1 (max (-1) (x i)) := rfl

theorem clampFun_mem_euCube (n : ℕ) (x : Fin n → ℝ) : clampFun n x ∈ euCube n := by
  intro i
  rw [clampFun_apply, abs_le]
  exact ⟨le_min (by norm_num) (le_max_left (-1) (x i)), min_le_left 1 (max (-1) (x i))⟩

theorem clampFun_eq_self {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ euCube n) :
    clampFun n x = x := by
  funext i
  obtain ⟨h1, h2⟩ := abs_le.mp (hx i)
  rw [clampFun_apply, max_eq_right h1, min_eq_right h2]

theorem clampFun_pos {n : ℕ} {x : Fin n → ℝ} {i : Fin n} (h : 0 < x i) :
    0 < clampFun n x i := by
  rw [clampFun_apply]
  have hge : (-1 : ℝ) ≤ x i := by linarith
  rw [max_eq_right hge]
  by_cases h1 : (1 : ℝ) ≤ x i
  · rw [min_eq_left h1]; norm_num
  · rw [min_eq_right (le_of_lt (lt_of_not_ge h1))]
    exact h

theorem clampFun_neg {n : ℕ} {x : Fin n → ℝ} {i : Fin n} (h : x i < 0) :
    clampFun n x i < 0 := by
  rw [clampFun_apply]
  by_cases h1 : x i ≤ (-1 : ℝ)
  · rw [max_eq_left h1, min_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]; norm_num
  · rw [max_eq_right (le_of_lt (lt_of_not_ge h1)), min_eq_right (by linarith : x i ≤ 1)]
    exact h

theorem clampFun_eq_zero_iff (n : ℕ) (x : Fin n → ℝ) : clampFun n x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext i
    have hi0 : clampFun n x i = 0 := by
      have := congrFun h i
      simpa using this
    by_contra hi
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · exact absurd hi0 (ne_of_lt (clampFun_neg hlt))
    · exact absurd hi0 (ne_of_gt (clampFun_pos hgt))
  · rintro rfl
    funext i
    simp only [clampFun_apply, Pi.zero_apply, max_eq_right (by norm_num : (-1 : ℝ) ≤ 0),
      min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

theorem clampFun_ne_zero {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) : clampFun n x ≠ 0 :=
  fun h => hx ((clampFun_eq_zero_iff n x).mp h)

theorem continuous_clampFun (n : ℕ) : Continuous (clampFun n) := by
  refine continuous_pi (fun i => ?_)
  show Continuous fun x : Fin n → ℝ => min 1 (max (-1) (x i))
  exact continuous_const.min (continuous_const.max (continuous_apply i))

/-- The clamp as a continuous endomorphism of `ℝⁿ`. -/
def clampCM (n : ℕ) : C(Fin n → ℝ, Fin n → ℝ) := ⟨clampFun n, continuous_clampFun n⟩

/-- The clamp as a continuous map into the cube. -/
def clampToCube (n : ℕ) : C(Fin n → ℝ, ↥(euCube n)) :=
  ⟨fun x => ⟨clampFun n x, clampFun_mem_euCube n x⟩,
    Continuous.subtype_mk (continuous_clampFun n) (fun x => clampFun_mem_euCube n x)⟩

/-- The inclusion of the cube in `ℝⁿ`. -/
def cubeIncl (n : ℕ) : C(↥(euCube n), Fin n → ℝ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem cubeIncl_comp_clampToCube (n : ℕ) :
    (cubeIncl n).comp (clampToCube n) = clampCM n := rfl

theorem clampToCube_comp_cubeIncl (n : ℕ) :
    (clampToCube n).comp (cubeIncl n) = ContinuousMap.id ↥(euCube n) := by
  apply ContinuousMap.ext
  intro x
  exact Subtype.ext (clampFun_eq_self x.2)

/-! ## The straight line to the clamp -/

/-- The linear interpolation between `x` and its clamp. -/
def lineFun (n : ℕ) (t : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (1 - t) * x i + t * clampFun n x i

theorem lineFun_apply (n : ℕ) (t : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    lineFun n t x i = (1 - t) * x i + t * clampFun n x i := rfl

theorem lineFun_zero (n : ℕ) (x : Fin n → ℝ) : lineFun n 0 x = x := by
  funext i
  rw [lineFun_apply]
  simp

theorem lineFun_one (n : ℕ) (x : Fin n → ℝ) : lineFun n 1 x = clampFun n x := by
  funext i
  rw [lineFun_apply]
  simp

theorem lineFun_eq_self_of_mem {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ euCube n) (t : ℝ) :
    lineFun n t x = x := by
  funext i
  rw [lineFun_apply, clampFun_eq_self hx]
  ring

theorem lineFun_ne_zero {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {x : Fin n → ℝ}
    (hx : x ≠ 0) : lineFun n t x ≠ 0 := by
  intro h
  apply hx
  funext i
  have hi : (1 - t) * x i + t * clampFun n x i = 0 := by
    have := congrFun h i
    rwa [lineFun_apply] at this
  rcases lt_trichotomy (x i) 0 with hlt | heq | hgt
  · have hc : clampFun n x i < 0 := clampFun_neg hlt
    rcases lt_or_eq_of_le ht1 with ht1' | ht1'
    · have h1 : (1 - t) * x i < 0 := mul_neg_of_pos_of_neg (by linarith) hlt
      have h2 : t * clampFun n x i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hc.le
      linarith
    · rw [ht1'] at hi
      simp at hi
      exact absurd hi (ne_of_lt hc)
  · exact heq
  · have hc : 0 < clampFun n x i := clampFun_pos hgt
    rcases lt_or_eq_of_le ht1 with ht1' | ht1'
    · have h1 : 0 < (1 - t) * x i := mul_pos (by linarith) hgt
      have h2 : 0 ≤ t * clampFun n x i := mul_nonneg ht0 hc.le
      linarith
    · rw [ht1'] at hi
      simp at hi
      exact absurd hi (ne_of_gt hc)

theorem continuous_lineFun (n : ℕ) :
    Continuous fun p : ℝ × (Fin n → ℝ) => lineFun n p.1 p.2 := by
  refine continuous_pi (fun i => ?_)
  simp only [lineFun_apply]
  exact ((continuous_const.sub continuous_fst).mul ((continuous_apply i).comp continuous_snd)).add
    (continuous_fst.mul ((continuous_apply i).comp ((continuous_clampFun n).comp continuous_snd)))

/-- The straight-line homotopy, written with the time reversed so that it runs from the clamp to
the identity. -/
def clampHomotopyCM (n : ℕ) : C(unitInterval × (Fin n → ℝ), Fin n → ℝ) :=
  ⟨fun p => lineFun n (1 - (p.1 : ℝ)) p.2,
    (continuous_lineFun n).comp
      (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).prodMk
        continuous_snd))⟩

theorem clampHomotopyCM_apply (n : ℕ) (t : unitInterval) (x : Fin n → ℝ) :
    clampHomotopyCM n (t, x) = lineFun n (1 - (t : ℝ)) x := rfl

/-- The straight-line homotopy from `cubeIncl ∘ clampToCube` to the identity of `ℝⁿ`: `x` travels
linearly to its clamp. -/
def clampToIdHomotopy (n : ℕ) :
    ((cubeIncl n).comp (clampToCube n)).Homotopy (ContinuousMap.id (Fin n → ℝ)) :=
  ContinuousMap.Homotopy.mk (clampHomotopyCM n)
    (fun x => by
      show lineFun n (1 - ((0 : unitInterval) : ℝ)) x = clampFun n x
      rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero]
      exact lineFun_one n x)
    (fun x => by
      show lineFun n (1 - ((1 : unitInterval) : ℝ)) x = x
      rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, sub_self]
      exact lineFun_zero n x)

theorem clampToIdHomotopy_toFun (n : ℕ) (t : unitInterval) (x : Fin n → ℝ) :
    (clampToIdHomotopy n).toFun (t, x) = lineFun n (1 - (t : ℝ)) x := rfl

theorem clampToIdHomotopy_preserves (n : ℕ) (t : unitInterval) (x : Fin n → ℝ) (hx : x ≠ 0) :
    (clampToIdHomotopy n).toFun (t, x) ≠ 0 := by
  rw [clampToIdHomotopy_toFun]
  exact lineFun_ne_zero (by linarith [t.2.2]) (by linarith [t.2.1]) hx

/-- The clamp is a homotopy equivalence `ℝⁿ ≃ [-1,1]ⁿ`, with homotopy inverse the inclusion. -/
def clampEquiv (n : ℕ) : ContinuousMap.HomotopyEquiv (Fin n → ℝ) ↥(euCube n) where
  toFun := clampToCube n
  invFun := cubeIncl n
  left_inv := ⟨clampToIdHomotopy n⟩
  right_inv := by
    have h : (clampToCube n).comp (cubeIncl n) = ContinuousMap.id ↥(euCube n) :=
      clampToCube_comp_cubeIncl n
    simpa only [h] using ContinuousMap.Homotopic.refl (ContinuousMap.id ↥(euCube n))

/-! ## Pairs of the form `(W × Z, W × S)` -/

/-- The complement of the origin in the fibre `ℝⁿ`. -/
def punctFibre (n : ℕ) : Set (Fin n → ℝ) := {x | x ≠ 0}

/-- The complement of the origin in the cube. -/
def punctCubeFibre (n : ℕ) : Set ↥(euCube n) := {x | (x : Fin n → ℝ) ≠ 0}

/-- The complement of the origin in `W × ℝⁿ`. -/
def punctSpace (W : Type) (n : ℕ) : Set (W × (Fin n → ℝ)) := {p | p.2 ∈ punctFibre n}

/-- The complement of the origin in the cube `W × [-1,1]ⁿ`. -/
def punctCube (W : Type) (n : ℕ) : Set (W × ↥(euCube n)) := {p | p.2 ∈ punctCubeFibre n}

/-- The boundary of the cube `W × [-1,1]ⁿ`. -/
def bdryCube (W : Type) (n : ℕ) : Set (W × ↥(euCube n)) :=
  {p | (p.2 : Fin n → ℝ) ∈ euCubeBdry n}

theorem mem_punctSpace {W : Type} {n : ℕ} {p : W × (Fin n → ℝ)} :
    p ∈ punctSpace W n ↔ (p.2 : Fin n → ℝ) ≠ 0 := Iff.rfl

theorem mem_punctCube {W : Type} {n : ℕ} {p : W × ↥(euCube n)} :
    p ∈ punctCube W n ↔ (p.2 : Fin n → ℝ) ≠ 0 := Iff.rfl

theorem mem_bdryCube {W : Type} {n : ℕ} {p : W × ↥(euCube n)} :
    p ∈ bdryCube W n ↔ (p.2 : Fin n → ℝ) ∈ euCubeBdry n := Iff.rfl

theorem ne_zero_of_mem_euCubeBdry {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ euCubeBdry n) :
    x ≠ 0 := by
  intro h0
  obtain ⟨-, i, hi⟩ := hx
  rw [h0] at hi
  simp at hi

theorem bdryCube_subset_punctCube (W : Type) [TopologicalSpace W] (n : ℕ) :
    bdryCube W n ⊆ punctCube W n := fun p hp => ne_zero_of_mem_euCubeBdry hp

/-- A map `f : Z₁ → Z₂` induces a map of the pairs `(W × Z₁, W × S₁) → (W × Z₂, W × S₂)`: it acts
by the identity on `W`. -/
def subtypeProdMap {W Z₁ Z₂ : Type*} [TopologicalSpace W] [TopologicalSpace Z₁]
    [TopologicalSpace Z₂] (S₁ : Set Z₁) (S₂ : Set Z₂) (f : C(Z₁, Z₂))
    (hf : ∀ x ∈ S₁, f x ∈ S₂) :
    C(↥{p : W × Z₁ | p.2 ∈ S₁}, ↥{p : W × Z₂ | p.2 ∈ S₂}) :=
  ⟨fun p => ⟨(p.1.1, f p.1.2), hf _ p.2⟩,
    Continuous.subtype_mk
      ((continuous_fst.comp continuous_subtype_val).prodMk
        (f.continuous.comp (continuous_snd.comp continuous_subtype_val)))
      (fun p => hf _ p.2)⟩

/-- The self map of `↥{p : W × Z | p.2 ∈ S}` induced by a self map of `Z` preserving `S`. -/
def subtypeProdSelfMap {W Z : Type*} [TopologicalSpace W] [TopologicalSpace Z] (S : Set Z)
    (f : C(Z, Z)) (hf : ∀ x ∈ S, f x ∈ S) :
    C(↥{p : W × Z | p.2 ∈ S}, ↥{p : W × Z | p.2 ∈ S}) :=
  subtypeProdMap S S f hf

/-- The time-dependent self map of `↥{p : W × Z | p.2 ∈ S}` induced by a homotopy on `Z`. -/
def subtypeProdSelfMapCM {W Z : Type*} [TopologicalSpace W] [TopologicalSpace Z] (S : Set Z)
    (H : C(↑unitInterval × Z, Z)) (hH : ∀ (t : unitInterval) (x : Z), x ∈ S → H (t, x) ∈ S) :
    C(↑unitInterval × ↥{p : W × Z | p.2 ∈ S}, ↥{p : W × Z | p.2 ∈ S}) :=
  ⟨fun p => ⟨(p.2.1.1, H (p.1, p.2.1.2)), hH p.1 p.2.1.2 p.2.2⟩, by
    refine Continuous.subtype_mk (f := fun p : ↑unitInterval × ↥{p : W × Z | p.2 ∈ S} =>
      (p.2.1.1, H (p.1, p.2.1.2))) ?_ (fun p => hH p.1 p.2.1.2 p.2.2)
    exact (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk
      (H.continuous.comp (continuous_fst.prodMk
        (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))))⟩

/-- The composite of the two induced maps of pairs is induced by the composite map of the fibres. -/
theorem subtypeProdMap_comp_eq_selfMap {W Z₁ Z₂ : Type*} [TopologicalSpace W]
    [TopologicalSpace Z₁] [TopologicalSpace Z₂] {S₁ : Set Z₁} {S₂ : Set Z₂} {f : C(Z₁, Z₂)}
    {g : C(Z₂, Z₁)} (hf : ∀ x ∈ S₁, f x ∈ S₂) (hg : ∀ x ∈ S₂, g x ∈ S₁) :
    (subtypeProdMap (W := W) S₂ S₁ g hg).comp (subtypeProdMap (W := W) S₁ S₂ f hf)
      = subtypeProdSelfMap (W := W) S₁ (g.comp f) (fun x hx => hg _ (hf x hx)) := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  simp only [subtypeProdMap, subtypeProdSelfMap, ContinuousMap.comp_apply, ContinuousMap.coe_mk]

/-- **Homotopies descend to the pairs `(W × Z, W × S)`**: if `H` is a homotopy from `g ∘ f` to the
identity of `Z₁` which preserves `S₁`, then the induced self map of `↥{p : W × Z₁ | p.2 ∈ S₁}` is
homotopic to the identity. -/
theorem subtypeProdSelfMap_homotopic_id {W Z : Type*} [TopologicalSpace W] [TopologicalSpace Z]
    {S : Set Z} {f : C(Z, Z)} (hf : ∀ x ∈ S, f x ∈ S) (H : f.Homotopy (ContinuousMap.id Z))
    (hH : ∀ (t : unitInterval) (x : Z), x ∈ S → H.toFun (t, x) ∈ S) :
    (subtypeProdSelfMap S f hf).Homotopic (ContinuousMap.id ↥{p : W × Z | p.2 ∈ S}) := by
  refine ⟨ContinuousMap.Homotopy.mk (subtypeProdSelfMapCM S H.toContinuousMap hH) ?_ ?_⟩
  · intro q
    apply Subtype.ext
    exact Prod.ext rfl (H.map_zero_left q.1.2)
  · intro q
    apply Subtype.ext
    exact Prod.ext rfl (H.map_one_left q.1.2)

/-- The degenerate case: if `f ∘ g` is the identity on `Z₂`, then the induced map of pairs composed
with its inverse is the identity. -/
theorem subtypeProdMap_comp_subtypeProdMap_eq {W Z₁ Z₂ : Type*} [TopologicalSpace W]
    [TopologicalSpace Z₁] [TopologicalSpace Z₂] {S₁ : Set Z₁} {S₂ : Set Z₂} {f : C(Z₁, Z₂)}
    {g : C(Z₂, Z₁)} (hf : ∀ x ∈ S₁, f x ∈ S₂) (hg : ∀ x ∈ S₂, g x ∈ S₁)
    (heq : f.comp g = ContinuousMap.id Z₂) :
    ((subtypeProdMap (W := W) S₁ S₂ f hf).comp (subtypeProdMap (W := W) S₂ S₁ g hg)).Homotopic
      (ContinuousMap.id ↥{p : W × Z₂ | p.2 ∈ S₂}) := by
  have hval : ∀ x : Z₂, f (g x) = x := fun x => DFunLike.congr_fun heq x
  have hmap : (subtypeProdMap S₁ S₂ f hf).comp (subtypeProdMap S₂ S₁ g hg)
      = ContinuousMap.id ↥{p : W × Z₂ | p.2 ∈ S₂} := by
    apply ContinuousMap.ext
    intro p
    apply Subtype.ext
    simp only [subtypeProdMap, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
    exact Prod.ext rfl (hval p.1.2)
  exact hmap.symm ▸ ContinuousMap.Homotopic.refl (ContinuousMap.id ↥{p : W × Z₂ | p.2 ∈ S₂})

/-! ## Step one: the clamp `ℝⁿ → [-1,1]ⁿ` -/

theorem clampToCube_mem_punctCubeFibre {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) :
    clampToCube n x ∈ punctCubeFibre n := clampFun_ne_zero hx

theorem cubeIncl_mem_punctFibre {n : ℕ} {x : ↥(euCube n)} (hx : x ∈ punctCubeFibre n) :
    cubeIncl n x ∈ punctFibre n := hx

/-- **The clamp is a homotopy equivalence of the punctured pairs.** -/
def punctEquiv (W : Type) [TopologicalSpace W] (n : ℕ) :
    ContinuousMap.HomotopyEquiv ↥(punctSpace W n) ↥(punctCube W n) where
  toFun := subtypeProdMap (punctFibre n) (punctCubeFibre n) (clampToCube n)
    (fun x hx => clampToCube_mem_punctCubeFibre hx)
  invFun := subtypeProdMap (punctCubeFibre n) (punctFibre n) (cubeIncl n)
    (fun x hx => cubeIncl_mem_punctFibre hx)
  left_inv := by
    rw [subtypeProdMap_comp_eq_selfMap (S₁ := punctFibre n) (S₂ := punctCubeFibre n)
      (f := clampToCube n) (g := cubeIncl n)
      (fun x hx => clampToCube_mem_punctCubeFibre hx)
      (fun x hx => cubeIncl_mem_punctFibre hx)]
    exact subtypeProdSelfMap_homotopic_id
      (f := (cubeIncl n).comp (clampToCube n))
      (fun x hx => cubeIncl_mem_punctFibre (clampToCube_mem_punctCubeFibre hx))
      (clampToIdHomotopy n) (fun t x hx => clampToIdHomotopy_preserves n t x hx)
  right_inv := subtypeProdMap_comp_subtypeProdMap_eq (S₁ := punctFibre n)
    (S₂ := punctCubeFibre n) (f := clampToCube n) (g := cubeIncl n)
    (fun x hx => clampToCube_mem_punctCubeFibre hx)
    (fun x hx => cubeIncl_mem_punctFibre hx) (clampToCube_comp_cubeIncl n)

/-- The clamp map of pairs `(W × ℝⁿ, W × (ℝⁿ∖0)) → (W × [-1,1]ⁿ, W × ([-1,1]ⁿ∖0))`. -/
def clampPair (W : Type) [TopologicalSpace W] (n : ℕ) :
    C(W × (Fin n → ℝ), W × ↥(euCube n)) :=
  (ContinuousMap.id W).prodMap (clampToCube n)

/-- The clamp as a map of the pairs `(W × ℝⁿ, W × (ℝⁿ∖0)) → (W × [-1,1]ⁿ, W × ([-1,1]ⁿ∖0))` on
relative cohomology (note the contravariance). -/
def clampRelMap (W : Type) [TopologicalSpace W] (n m : ℕ) :
    RelCoh ℤ m (W × ↥(euCube n)) (punctCube W n) ⟶
      RelCoh ℤ m (W × (Fin n → ℝ)) (punctSpace W n) :=
  relCohMap (clampPair W n) (punctSpace W n) (punctCube W n)
    (fun p hp => clampFun_ne_zero hp) ℤ m

/-- **The clamp induces a bijection on relative cohomology.** -/
theorem bijective_relCohMap_clamp (W : Type) [TopologicalSpace W] (n m : ℕ) :
    Function.Bijective (clampRelMap W n m).hom :=
  Work.Thom.EuclCleanInfra.bijective_relCohMap_of_homotopyEquiv (punctSpace W n) (punctCube W n) (clampPair W n) _
    ((ContinuousMap.HomotopyEquiv.refl W).prodCongr (clampEquiv n)) rfl
    (punctEquiv W n) (fun q => rfl) m

/-! ## Step two: the radial retraction of the punctured cube onto its boundary -/

/-- The `L∞` norm of `x : ℝⁿ`, the maximum of the absolute values of its coordinates. -/
def cubeMax (n : ℕ) (hn : 1 ≤ n) (x : Fin n → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n)).sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => |x i|)

theorem le_cubeMax (n : ℕ) (hn : 1 ≤ n) (x : Fin n → ℝ) (i : Fin n) :
    |x i| ≤ cubeMax n hn x :=
  Finset.le_sup' (fun i => |x i|) (Finset.mem_univ i)

theorem continuous_cubeMax (n : ℕ) (hn : 1 ≤ n) : Continuous (cubeMax n hn) := by
  have h : Continuous ((Finset.univ : Finset (Fin n)).sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
      (fun i => fun x : Fin n → ℝ => |x i|)) :=
    Continuous.finset_sup' _ (fun i _ => (continuous_apply i).abs)
  have heq : ((Finset.univ : Finset (Fin n)).sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
      (fun i => fun x : Fin n → ℝ => |x i|)) = cubeMax n hn := by
    funext x
    exact Finset.sup'_apply _ _ x
  simpa only [heq] using h

theorem cubeMax_pos (n : ℕ) (hn : 1 ≤ n) {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < cubeMax n hn x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact lt_of_lt_of_le (abs_pos.mpr (by simpa using hi)) (le_cubeMax n hn x i)

theorem cubeMax_le_one (n : ℕ) (hn : 1 ≤ n) {x : Fin n → ℝ} (hx : x ∈ euCube n) :
    cubeMax n hn x ≤ 1 :=
  Finset.sup'_le _ (fun i => |x i|) (fun i _ => hx i)

theorem cubeMax_eq_one_of_mem_bdry (n : ℕ) (hn : 1 ≤ n) {x : Fin n → ℝ}
    (hx : x ∈ euCubeBdry n) : cubeMax n hn x = 1 := by
  obtain ⟨hx1, i, hi⟩ := hx
  refine le_antisymm (cubeMax_le_one n hn hx1) ?_
  rw [← hi]
  exact le_cubeMax n hn x i

/-- The radial projection `x ↦ x / (maxᵢ |xᵢ|)` of the punctured cube towards its boundary. -/
def radialFun (n : ℕ) (hn : 1 ≤ n) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i / cubeMax n hn x

theorem radialFun_mem_euCube (n : ℕ) (hn : 1 ≤ n) {x : Fin n → ℝ} (hx : x ∈ euCube n)
    (hx0 : x ≠ 0) : radialFun n hn x ∈ euCube n := by
  intro i
  rw [radialFun, abs_div, abs_of_pos (cubeMax_pos n hn hx0), div_le_one (cubeMax_pos n hn hx0)]
  exact le_cubeMax n hn x i

theorem radialFun_mem_bdry (n : ℕ) (hn : 1 ≤ n) {x : Fin n → ℝ} (hx : x ∈ euCube n)
    (hx0 : x ≠ 0) : radialFun n hn x ∈ euCubeBdry n := by
  refine ⟨radialFun_mem_euCube n hn hx hx0, ?_⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Fin n)))
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => |x i|)
  have hi' : cubeMax n hn x = |x i| := hi
  exact ⟨i, by
    rw [radialFun, abs_div, abs_of_pos (cubeMax_pos n hn hx0), ← hi',
      div_self (ne_of_gt (cubeMax_pos n hn hx0))]⟩

theorem radialFun_ne_zero (n : ℕ) (hn : 1 ≤ n) {x : Fin n → ℝ} (hx : x ≠ 0) :
    radialFun n hn x ≠ 0 := by
  intro h
  apply hx
  funext i
  have hi : x i / cubeMax n hn x = 0 := by
    have h2 := congrFun h i
    simpa only [radialFun, Pi.zero_apply] using h2
  exact (div_eq_zero_iff.mp hi).resolve_right (ne_of_gt (cubeMax_pos n hn hx))

theorem radialFun_eq_self_of_mem_bdry (n : ℕ) (hn : 1 ≤ n) {x : Fin n → ℝ}
    (hx : x ∈ euCubeBdry n) : radialFun n hn x = x := by
  funext i
  rw [radialFun, cubeMax_eq_one_of_mem_bdry n hn hx, div_one]

/-- The coefficient of the straight line from `x` to its radial projection. -/
def radialCoeff (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  1 - t + t / cubeMax n hn x

/-- The straight line from `x` to the radial projection `radialFun x`. -/
def radialLine (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i * radialCoeff n hn t x

theorem radialCoeff_pos (n : ℕ) (hn : 1 ≤ n) {t : ℝ} {x : Fin n → ℝ} (ht0 : 0 ≤ t)
    (hx : x ∈ euCube n) (hx0 : x ≠ 0) : 0 < radialCoeff n hn t x := by
  have hM := cubeMax_pos n hn hx0
  have hle : 1 ≤ 1 / cubeMax n hn x := one_le_one_div hM (cubeMax_le_one n hn hx)
  have ht : t ≤ t / cubeMax n hn x := by
    calc t = t * 1 := (mul_one t).symm
      _ ≤ t * (1 / cubeMax n hn x) := mul_le_mul_of_nonneg_left hle ht0
      _ = t / cubeMax n hn x := by ring
  rw [radialCoeff]
  linarith

theorem radialCoeff_mul_cubeMax_le_one (n : ℕ) (hn : 1 ≤ n) {t : ℝ} {x : Fin n → ℝ}
    (ht1 : t ≤ 1) (hx : x ∈ euCube n) (hx0 : x ≠ 0) :
    radialCoeff n hn t x * cubeMax n hn x ≤ 1 := by
  have hM := cubeMax_pos n hn hx0
  have hM1 := cubeMax_le_one n hn hx
  have hdiv : t / cubeMax n hn x * cubeMax n hn x = t := div_mul_cancel₀ t (ne_of_gt hM)
  have h1 : (1 - t) * cubeMax n hn x ≤ (1 - t) * 1 :=
    mul_le_mul_of_nonneg_left hM1 (by linarith)
  calc radialCoeff n hn t x * cubeMax n hn x
      = (1 - t) * cubeMax n hn x + t := by rw [radialCoeff, add_mul, hdiv]
    _ ≤ (1 - t) * 1 + t := by linarith
    _ = 1 := by ring

theorem radialLine_mem_euCube (n : ℕ) (hn : 1 ≤ n) {t : ℝ} {x : Fin n → ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hx : x ∈ euCube n) (hx0 : x ≠ 0) : radialLine n hn t x ∈ euCube n := by
  intro i
  have hc := radialCoeff_pos n hn ht0 hx hx0
  rw [radialLine, abs_mul, abs_of_pos hc]
  calc |x i| * radialCoeff n hn t x
      ≤ cubeMax n hn x * radialCoeff n hn t x :=
        mul_le_mul_of_nonneg_right (le_cubeMax n hn x i) (le_of_lt hc)
    _ = radialCoeff n hn t x * cubeMax n hn x := by ring
    _ ≤ 1 := radialCoeff_mul_cubeMax_le_one n hn ht1 hx hx0

theorem radialLine_ne_zero (n : ℕ) (hn : 1 ≤ n) {t : ℝ} {x : Fin n → ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hx : x ∈ euCube n) (hx0 : x ≠ 0) : radialLine n hn t x ≠ 0 := by
  intro h
  apply hx0
  funext i
  have hi : x i * radialCoeff n hn t x = 0 := by
    have h2 := congrFun h i
    simpa only [radialLine, Pi.zero_apply] using h2
  exact (mul_eq_zero.mp hi).resolve_right (ne_of_gt (radialCoeff_pos n hn ht0 hx hx0))

theorem radialLine_zero (n : ℕ) (hn : 1 ≤ n) (x : Fin n → ℝ) : radialLine n hn 0 x = x := by
  funext i
  rw [radialLine, radialCoeff]
  simp

theorem radialLine_one (n : ℕ) (hn : 1 ≤ n) (x : Fin n → ℝ) :
    radialLine n hn 1 x = radialFun n hn x := by
  funext i
  rw [radialLine, radialCoeff, radialFun]
  simp [div_eq_mul_inv]

/-! ## Step two: the pair `(W × ∂[-1,1]ⁿ, W × ([-1,1]ⁿ∖0))` -/

/-- The underlying vector of a point of the punctured cube. -/
def punctCubeVal (W : Type) [TopologicalSpace W] (n : ℕ) : C(↥(punctCube W n), Fin n → ℝ) :=
  ⟨fun q => (q.1.2 : Fin n → ℝ),
    continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)⟩

theorem punctCubeVal_mem_cube (W : Type) [TopologicalSpace W] (n : ℕ) (q : ↥(punctCube W n)) :
    punctCubeVal W n q ∈ euCube n := q.1.2.2

theorem punctCubeVal_ne_zero (W : Type) [TopologicalSpace W] (n : ℕ) (q : ↥(punctCube W n)) :
    punctCubeVal W n q ≠ 0 := q.2

theorem continuous_of_radialFun (W : Type) [TopologicalSpace W] (n : ℕ) (hn : 1 ≤ n) :
    Continuous fun q : ↥(punctCube W n) => radialFun n hn (punctCubeVal W n q) := by
  refine continuous_pi (fun i => ?_)
  simp only [radialFun]
  exact (((continuous_apply i).comp (punctCubeVal W n).continuous).div
    ((continuous_cubeMax n hn).comp (punctCubeVal W n).continuous)
    (fun q => ne_of_gt (cubeMax_pos n hn (punctCubeVal_ne_zero W n q))))

theorem continuous_of_radialLine (W : Type) [TopologicalSpace W] (n : ℕ) (hn : 1 ≤ n) :
    Continuous fun p : ↑unitInterval × ↥(punctCube W n) =>
      radialLine n hn (p.1 : ℝ) (punctCubeVal W n p.2) := by
  refine continuous_pi (fun i => ?_)
  simp only [radialLine, radialCoeff]
  have ht : Continuous fun p : ↑unitInterval × ↥(punctCube W n) => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous fun p : ↑unitInterval × ↥(punctCube W n) => punctCubeVal W n p.2 :=
    (punctCubeVal W n).continuous.comp continuous_snd
  have hM : Continuous fun p : ↑unitInterval × ↥(punctCube W n) =>
      cubeMax n hn (punctCubeVal W n p.2) := (continuous_cubeMax n hn).comp hx
  have hne : ∀ p : ↑unitInterval × ↥(punctCube W n),
      cubeMax n hn (punctCubeVal W n p.2) ≠ 0 :=
    fun p => ne_of_gt (cubeMax_pos n hn (punctCubeVal_ne_zero W n p.2))
  exact (((continuous_apply i).comp hx).mul ((continuous_const.sub ht).add (ht.div hM hne)))

/-- The radial projection of the punctured cube onto its boundary. -/
def radialCubeMap (W : Type) [TopologicalSpace W] (n : ℕ) (hn : 1 ≤ n) :
    C(↥(punctCube W n), ↥(bdryCube W n)) :=
  ⟨fun q => ⟨(q.1.1, ⟨radialFun n hn (punctCubeVal W n q),
      radialFun_mem_euCube n hn (punctCubeVal_mem_cube W n q) (punctCubeVal_ne_zero W n q)⟩),
      radialFun_mem_bdry n hn (punctCubeVal_mem_cube W n q) (punctCubeVal_ne_zero W n q)⟩, by
    have h1 : Continuous fun q : ↥(punctCube W n) => q.1.1 :=
      continuous_fst.comp continuous_subtype_val
    have h2 : Continuous fun q : ↥(punctCube W n) =>
        (⟨radialFun n hn (punctCubeVal W n q),
          radialFun_mem_euCube n hn (punctCubeVal_mem_cube W n q)
            (punctCubeVal_ne_zero W n q)⟩ : ↥(euCube n)) :=
      Continuous.subtype_mk (continuous_of_radialFun W n hn)
        (fun q : ↥(punctCube W n) => radialFun_mem_euCube n hn (punctCubeVal_mem_cube W n q)
          (punctCubeVal_ne_zero W n q))
    exact Continuous.subtype_mk (h1.prodMk h2)
      (fun q : ↥(punctCube W n) => radialFun_mem_bdry n hn (punctCubeVal_mem_cube W n q)
        (punctCubeVal_ne_zero W n q))⟩

/-- The inclusion of the boundary of the cube in the punctured cube. -/
def bdryIncl (W : Type) [TopologicalSpace W] (n : ℕ) :
    C(↥(bdryCube W n), ↥(punctCube W n)) :=
  ⟨fun q => ⟨q.1, bdryCube_subset_punctCube W n q.2⟩,
    Continuous.subtype_mk continuous_subtype_val (fun q => bdryCube_subset_punctCube W n q.2)⟩

/-- The time-dependent map of the radial deformation retraction of the punctured cube onto its
boundary. -/
def radialCubeHomCM (W : Type) [TopologicalSpace W] (n : ℕ) (hn : 1 ≤ n) :
    C(↑unitInterval × ↥(punctCube W n), ↥(punctCube W n)) :=
  ⟨fun p => ⟨(p.2.1.1, ⟨radialLine n hn (p.1 : ℝ) (punctCubeVal W n p.2),
      radialLine_mem_euCube n hn p.1.2.1 p.1.2.2 (punctCubeVal_mem_cube W n p.2)
        (punctCubeVal_ne_zero W n p.2)⟩),
      radialLine_ne_zero n hn p.1.2.1 p.1.2.2 (punctCubeVal_mem_cube W n p.2)
        (punctCubeVal_ne_zero W n p.2)⟩, by
    have h1 : Continuous fun p : ↑unitInterval × ↥(punctCube W n) => p.2.1.1 :=
      (continuous_fst.comp continuous_subtype_val).comp continuous_snd
    have h2 : Continuous fun p : ↑unitInterval × ↥(punctCube W n) =>
        (⟨radialLine n hn (p.1 : ℝ) (punctCubeVal W n p.2),
          radialLine_mem_euCube n hn p.1.2.1 p.1.2.2 (punctCubeVal_mem_cube W n p.2)
            (punctCubeVal_ne_zero W n p.2)⟩ : ↥(euCube n)) :=
      Continuous.subtype_mk (continuous_of_radialLine W n hn)
        (fun p : ↑unitInterval × ↥(punctCube W n) =>
          radialLine_mem_euCube n hn p.1.2.1 p.1.2.2 (punctCubeVal_mem_cube W n p.2)
            (punctCubeVal_ne_zero W n p.2))
    exact Continuous.subtype_mk (h1.prodMk h2)
      (fun p : ↑unitInterval × ↥(punctCube W n) =>
        radialLine_ne_zero n hn p.1.2.1 p.1.2.2 (punctCubeVal_mem_cube W n p.2)
          (punctCubeVal_ne_zero W n p.2))⟩

/-- The radial deformation retraction of the punctured cube onto its boundary, as a homotopy from
the identity to the composite `bdryIncl ∘ radialCubeMap`. -/
def radialCubeInclHomotopy (W : Type) [TopologicalSpace W] (n : ℕ) (hn : 1 ≤ n) :
    (ContinuousMap.id ↥(punctCube W n)).Homotopy
      ((bdryIncl W n).comp (radialCubeMap W n hn)) :=
  ContinuousMap.Homotopy.mk (radialCubeHomCM W n hn)
    (fun q => by
      apply Subtype.ext
      exact Prod.ext rfl (Subtype.ext (radialLine_zero n hn (punctCubeVal W n q))))
    (fun q => by
      apply Subtype.ext
      exact Prod.ext rfl (Subtype.ext (radialLine_one n hn (punctCubeVal W n q))))

/-- **The boundary of the cube is a deformation retract of the punctured cube.** -/
def punctBdryEquiv (W : Type) [TopologicalSpace W] (n : ℕ) (hn : 1 ≤ n) :
    ContinuousMap.HomotopyEquiv ↥(bdryCube W n) ↥(punctCube W n) where
  toFun := bdryIncl W n
  invFun := radialCubeMap W n hn
  left_inv := by
    have h : (radialCubeMap W n hn).comp (bdryIncl W n) = ContinuousMap.id ↥(bdryCube W n) := by
      apply ContinuousMap.ext
      intro q
      apply Subtype.ext
      exact Prod.ext rfl (Subtype.ext (radialFun_eq_self_of_mem_bdry n hn q.2))
    exact h.symm ▸ ContinuousMap.Homotopic.refl (ContinuousMap.id ↥(bdryCube W n))
  right_inv := ⟨(radialCubeInclHomotopy W n hn).symm⟩

/-- **The inclusion of the boundary pair in the punctured cube induces a bijection on relative
cohomology.** -/
theorem bijective_relCohMap_bdry_punct (W : Type) [TopologicalSpace W] (n : ℕ) (hn : 1 ≤ n)
    (m : ℕ) :
    Function.Bijective
      ((relCohMap (ContinuousMap.id (W × ↥(euCube n))) (bdryCube W n) (punctCube W n)
        (fun p hp => bdryCube_subset_punctCube W n hp) ℤ m).hom) :=
  Work.Thom.EuclCleanInfra.bijective_relCohMap_of_homotopyEquiv (bdryCube W n) (punctCube W n)
    (ContinuousMap.id (W × ↥(euCube n))) (fun p hp => bdryCube_subset_punctCube W n hp)
    (ContinuousMap.HomotopyEquiv.refl (W × ↥(euCube n))) rfl (punctBdryEquiv W n hn)
    (fun q => rfl) m

/-- A subsingleton is transported backwards along an injective map. -/
theorem subsingleton_of_injective {α β : Type*} (f : α → β) (hf : Function.Injective f)
    [Subsingleton β] : Subsingleton α :=
  ⟨fun a b => hf (Subsingleton.elim (f a) (f b))⟩

/-- A subsingleton is transported forwards along a surjective map. -/
theorem subsingleton_of_surjective {α β : Type*} (f : α → β) (hf : Function.Surjective f)
    [Subsingleton α] : Subsingleton β :=
  ⟨fun a b => by
    obtain ⟨x, rfl⟩ := hf a
    obtain ⟨y, rfl⟩ := hf b
    rw [Subsingleton.elim x y]⟩

end

end EuclPunctClean

/-- **The vanishing theorem for the Euclidean pair, from the vanishing theorem for the cube pair.**

If the relative cohomology of the pair `(W × [-1,1]ⁿ, W × ∂[-1,1]ⁿ)` vanishes below degree `n` (for
every `W`), then the same holds for the pair `(W × ℝⁿ, W × (ℝⁿ∖0))`:
* the coordinate clamp and the radial projection of the punctured cube onto its boundary are both
  homotopy equivalences of pairs, so they induce bijections on relative cohomology
  (`Work.Thom.EuclPunctClean.bijective_relCohMap_clamp`, `Work.Thom.EuclPunctClean.bijective_relCohMap_bdry_punct`);
* a subsingleton is transported along an injective, resp. surjective, map. -/
theorem subsingleton_relComplex_euclidean_punctured
    (hCube : ∀ (n : ℕ) (W : Type) [TopologicalSpace W] (m : ℕ), m < n →
      Subsingleton ((Work.Cohomology.relComplex ℤ (TopCat.of (W × ↥(Work.Thom.euCube n)))
        {p : W × ↥(Work.Thom.euCube n) | (p.2 : Fin n → ℝ) ∈ Work.Thom.euCubeBdry n}).homology m))
    (n : ℕ) (W : Type) [TopologicalSpace W] (m : ℕ) (hm : m < n) :
    Subsingleton ((Work.Cohomology.relComplex ℤ (TopCat.of (W × (Fin n → ℝ)))
      {p : W × (Fin n → ℝ) | (p.2 : Fin n → ℝ) ≠ 0}).homology m) := by
  have hn : 1 ≤ n := by omega
  -- the hypothesis, in the notation of this file
  have hBdry : Subsingleton (RelCoh ℤ m (W × ↥(euCube n)) (EuclPunctClean.bdryCube W n)) :=
    hCube n W m hm
  -- the boundary of the cube is a deformation retract of the punctured cube
  have hbijBdry := EuclPunctClean.bijective_relCohMap_bdry_punct W n hn m
  have hPunct : Subsingleton (RelCoh ℤ m (W × ↥(euCube n)) (EuclPunctClean.punctCube W n)) :=
    EuclPunctClean.subsingleton_of_injective _ hbijBdry.injective
  -- the clamp compares the punctured cube with the punctured Euclidean space
  have hbijClamp := EuclPunctClean.bijective_relCohMap_clamp W n m
  have hSpace : Subsingleton (RelCoh ℤ m (W × (Fin n → ℝ)) (EuclPunctClean.punctSpace W n)) :=
    EuclPunctClean.subsingleton_of_surjective _ hbijClamp.surjective
  exact hSpace

end Work.Thom
