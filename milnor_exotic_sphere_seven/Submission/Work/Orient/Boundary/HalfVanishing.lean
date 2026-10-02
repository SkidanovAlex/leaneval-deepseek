import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Cohomology.relChains_vanishing_compact_specific
import Submission.Work.Cohomology.relChainsMapOf_comp
import Submission.Work.Cohomology.homologyTwoCover
import Submission.Work.Orient.Boundary.HalfCover

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `H_i(W, W∖A) = 0` above the dimension, for `W` charted by the half-space

This file proves `Work.Orient.HalfVanishingProp`, i.e. Hatcher's Lemma 3.27 (b) for a space
charted in the half-space model `𝓡∂ (n+1)`: for a compact `A` and `i > n+1` the relative singular
homology `H_i(W, W∖A)` vanishes.

## The route

1. **The Euclidean ingredient** (`Work.Cohomology.relChains_vanishing_compact_specific`): for an
   *open* subset `I ⊆ ℝᴺ` and a compact `K ⊆ I`, the group `H_j(I, I∖K)` vanishes for `j > N`.
2. **The half-space flat model**: for `U ⊆ 𝓡∂ m` open and `D ⊆ U` compact, `H_j(U, U∖D) = 0` for
   `j > m`.  This is deduced from the Euclidean statement by *doubling*: the fold map
   `foldMap : ℝᵐ → 𝓡∂ m`, `x ↦ (x₀ ↦ |x₀|)`, has `foldMap ⁻¹' U` open in `ℝᵐ` and
   `foldMap ⁻¹' D` compact, and the inclusion `U ↪ foldMap ⁻¹' U` together with the fold form a
   retraction of pairs; hence `H_j(U, U∖D)` is a direct summand of `H_j(foldMap ⁻¹' U, …) = 0`.
3. **Chart pieces**: a compact `C` inside the source of a chart `e` of `W` is handled by excision
   plus the chart homeomorphism, giving the flat model on `e.target`.
4. **Finite covers**: `exists_halfBallPiece_cover` (below, from `exists_halfBall_subset` of
   `Submission/Work/Orient/Boundary/HalfCover.lean`) covers a compact set by finitely many
   coordinate half-balls, and the Mayer–Vietoris step `Work.Cohomology.isZero_relChains_union`
   (valid for any `T2` space) finishes the induction over the cover.
-/

namespace Work.Orient.Boundary

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-! ## 1. Maps of pairs, and the retraction principle -/

/-- **The restriction of a map to a pair of subspaces**, `(X,A) → (Y,B)`. -/
def pairRestrict {X Y : TopCat} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : ∀ a ∈ A, f.hom a ∈ B) : TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨fun a => ⟨f.hom a.1, h a.1 a.2⟩,
    Continuous.subtype_mk (f.hom.continuous.comp continuous_subtype_val) (fun a => h a.1 a.2)⟩

/-- The compatibility of `pairRestrict` with the inclusions of the pairs. -/
theorem pairRestrict_subtypeIncl {X Y : TopCat} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : ∀ a ∈ A, f.hom a ∈ B) :
    Work.Cohomology.subtypeIncl X A ≫ f = pairRestrict f h ≫ Work.Cohomology.subtypeIncl Y B := by
  ext a
  rfl

/-- The restriction of a retraction of pairs to the subspaces is the identity. -/
theorem pairRestrict_comp_eq_id {X Y : TopCat} {A : Set X} {B : Set Y} (f : X ⟶ Y) (g : Y ⟶ X)
    (hf : ∀ a ∈ A, f.hom a ∈ B) (hg : ∀ b ∈ B, g.hom b ∈ A) (hgf : f ≫ g = 𝟙 X) :
    pairRestrict f hf ≫ pairRestrict g hg = 𝟙 (TopCat.of A) := by
  ext a
  exact congrArg (fun (k : X ⟶ X) => k.hom a.1) hgf

/-- The map of relative chain complexes induced by the identity pair is the identity. -/
theorem relChainsMapOf_id {X : TopCat} (A : Set X)
    (w : Work.Cohomology.subtypeIncl X A ≫ 𝟙 X = 𝟙 (TopCat.of A) ≫ Work.Cohomology.subtypeIncl X A) :
    Work.Cohomology.relChainsMapOf X X A A (𝟙 X) (𝟙 (TopCat.of A)) w
      = 𝟙 (Work.Cohomology.relChains X A) := by
  unfold Work.Cohomology.relChainsMapOf
  simp only [Work.Cohomology.chainMap, CategoryTheory.Functor.map_id]
  exact cokernel.map_id _ _ _

/-- The same, with the two maps exhibited as equal to the identities. -/
theorem relChainsMapOf_id_of {X : TopCat} {A : Set X} (f : X ⟶ X) (g' : TopCat.of A ⟶ TopCat.of A)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g' ≫ Work.Cohomology.subtypeIncl X A)
    (hf : f = 𝟙 X) (hg : g' = 𝟙 (TopCat.of A)) :
    Work.Cohomology.relChainsMapOf X X A A f g' w = 𝟙 (Work.Cohomology.relChains X A) := by
  subst hf
  subst hg
  exact relChainsMapOf_id A w

/-- **Retraction principle.**  If a map of pairs `(X,A) → (Y,B)` admits a retraction of pairs with
`f ≫ g = 𝟙 X`, then `H_i(X,A)` is a direct summand of `H_i(Y,B)`; in particular it vanishes as soon
as `H_i(Y,B)` does. -/
theorem isZero_relChains_of_retract {X Y : TopCat} {A : Set X} {B : Set Y} {i : ℕ}
    (f : X ⟶ Y) (g : Y ⟶ X) (hf : ∀ a ∈ A, f.hom a ∈ B) (hg : ∀ b ∈ B, g.hom b ∈ A)
    (hgf : f ≫ g = 𝟙 X) (h : IsZero ((Work.Cohomology.relChains Y B).homology i)) :
    IsZero ((Work.Cohomology.relChains X A).homology i) := by
  have hw : Work.Cohomology.subtypeIncl X A ≫ f = pairRestrict f hf ≫ Work.Cohomology.subtypeIncl Y B :=
    pairRestrict_subtypeIncl f hf
  have hw' : Work.Cohomology.subtypeIncl Y B ≫ g = pairRestrict g hg ≫ Work.Cohomology.subtypeIncl X A :=
    pairRestrict_subtypeIncl g hg
  have hcomp' : pairRestrict f hf ≫ pairRestrict g hg = 𝟙 (TopCat.of A) :=
    pairRestrict_comp_eq_id f g hf hg hgf
  have hw'' : Work.Cohomology.subtypeIncl X A ≫ (f ≫ g)
      = (pairRestrict f hf ≫ pairRestrict g hg) ≫ Work.Cohomology.subtypeIncl X A := by
    calc Work.Cohomology.subtypeIncl X A ≫ (f ≫ g)
        = (Work.Cohomology.subtypeIncl X A ≫ f) ≫ g := (Category.assoc _ _ _).symm
      _ = (pairRestrict f hf ≫ Work.Cohomology.subtypeIncl Y B) ≫ g := by rw [hw]
      _ = pairRestrict f hf ≫ (Work.Cohomology.subtypeIncl Y B ≫ g) := Category.assoc _ _ _
      _ = pairRestrict f hf ≫ (pairRestrict g hg ≫ Work.Cohomology.subtypeIncl X A) := by rw [hw']
      _ = (pairRestrict f hf ≫ pairRestrict g hg) ≫ Work.Cohomology.subtypeIncl X A :=
            (Category.assoc _ _ _).symm
  have hcomp : Work.Cohomology.relChainsMapOf X Y A B f (pairRestrict f hf) hw ≫
      Work.Cohomology.relChainsMapOf Y X B A g (pairRestrict g hg) hw'
      = 𝟙 (Work.Cohomology.relChains X A) := by
    rw [Work.Cohomology.relChainsMapOf_comp A B A f (pairRestrict f hf) hw g (pairRestrict g hg)
      hw' hw'']
    exact relChainsMapOf_id_of (f := f ≫ g) (g' := pairRestrict f hf ≫ pairRestrict g hg)
      hw'' hgf hcomp'
  have hhom : HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf X Y A B f (pairRestrict f hf) hw) i ≫
      HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf Y X B A g (pairRestrict g hg) hw') i
      = 𝟙 ((Work.Cohomology.relChains X A).homology i) := by
    rw [← HomologicalComplex.homologyMap_comp, hcomp, HomologicalComplex.homologyMap_id]
  refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => ?_⟩
  haveI : Subsingleton ((Work.Cohomology.relChains Y B).homology i) :=
    ModuleCat.isZero_iff_subsingleton.mp h
  have hz : ∀ c : (Work.Cohomology.relChains X A).homology i, c = 0 := by
    intro c
    have h1 : HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf X Y A B f (pairRestrict f hf) hw) i c = 0 :=
      Subsingleton.elim _ _
    have h2 : c = HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf Y X B A g (pairRestrict g hg) hw') i
        (HomologicalComplex.homologyMap
          (Work.Cohomology.relChainsMapOf X Y A B f (pairRestrict f hf) hw) i c) := by
      have h3 := congrArg (fun (k : (Work.Cohomology.relChains X A).homology i ⟶
          (Work.Cohomology.relChains X A).homology i) => k c) hhom
      simpa using h3.symm
    rw [h2, h1, map_zero]
  rw [hz a, hz b]

/-! ## 2. The flat model: open subsets of the half-space -/

section Flat

variable {m : ℕ} [NeZero m]

/-- **Reflection of the ambient Euclidean space** in the hyperplane `x 0 = 0`. -/
def reflectE (x : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  x - (2 * x 0) • EuclideanSpace.single 0 1

theorem continuous_reflectE : Continuous (reflectE (m := m)) := by
  have h : reflectE (m := m) = fun x : EuclideanSpace ℝ (Fin m) =>
      x - (2 * x 0) • EuclideanSpace.single (0 : Fin m) (1 : ℝ) := rfl
  rw [h]
  exact Continuous.sub continuous_id
    (Continuous.smul (continuous_const.mul (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) 0))
      continuous_const)

theorem reflectE_coord (x : EuclideanSpace ℝ (Fin m)) : (reflectE x) 0 = -(x 0) := by
  show (x - (2 * x 0) • EuclideanSpace.single (0 : Fin m) (1 : ℝ)) 0 = -(x 0)
  rw [PiLp.sub_apply, PiLp.smul_apply, PiLp.single_eq_same]
  ring

theorem reflectE_coord_ne (x : EuclideanSpace ℝ (Fin m)) {j : Fin m} (hj : j ≠ 0) :
    (reflectE x) j = x j := by
  show (x - (2 * x 0) • EuclideanSpace.single (0 : Fin m) (1 : ℝ)) j = x j
  rw [PiLp.sub_apply, PiLp.smul_apply,
    PiLp.single_eq_of_ne (p := 2) (i := (0 : Fin m)) (by simpa using hj)]
  ring

theorem reflectE_involutive (x : EuclideanSpace ℝ (Fin m)) : reflectE (reflectE x) = x := by
  ext j
  rcases eq_or_ne j 0 with rfl | hj
  · rw [reflectE_coord, reflectE_coord]; ring
  · rw [reflectE_coord_ne _ hj, reflectE_coord_ne _ hj]

/-- **The fold of the ambient space onto the half-space**: the coordinate `0` is replaced by its
absolute value.  It retracts the ambient space onto the half-space. -/
def foldMap (x : EuclideanSpace ℝ (Fin m)) : EuclideanHalfSpace m :=
  ⟨x - (2 * min (x 0) 0) • EuclideanSpace.single 0 1, by
    have h : (x - (2 * min (x 0) 0) • EuclideanSpace.single (0 : Fin m) (1 : ℝ)) 0
        = x 0 - 2 * min (x 0) 0 := by
      rw [PiLp.sub_apply, PiLp.smul_apply, PiLp.single_eq_same]
      ring
    rw [h]
    rcases le_total 0 (x 0) with hm | hm
    · rw [min_eq_right hm]; linarith
    · rw [min_eq_left hm]; linarith⟩

theorem continuous_foldMap : Continuous (foldMap (m := m)) := by
  have hmin : Continuous fun x : EuclideanSpace ℝ (Fin m) => min (x 0) 0 :=
    (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) 0).min continuous_const
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin m) =>
      x - (2 * min (x 0) 0) • EuclideanSpace.single (0 : Fin m) (1 : ℝ) :=
    Continuous.sub continuous_id ((continuous_const.mul hmin).smul continuous_const)
  exact hcont.subtype_mk _

theorem foldMap_coord (x : EuclideanSpace ℝ (Fin m)) :
    (foldMap x).1 0 = x 0 - 2 * min (x 0) 0 := by
  show (x - (2 * min (x 0) 0) • EuclideanSpace.single (0 : Fin m) (1 : ℝ)) 0 = _
  rw [PiLp.sub_apply, PiLp.smul_apply, PiLp.single_eq_same]
  ring

theorem foldMap_of_nonneg {x : EuclideanSpace ℝ (Fin m)} (hx : 0 ≤ x 0) :
    foldMap x = ⟨x, hx⟩ := by
  apply Subtype.ext
  show x - (2 * min (x 0) 0) • EuclideanSpace.single (0 : Fin m) (1 : ℝ) = x
  rw [min_eq_right hx]
  simp

theorem reflectE_nonneg {x : EuclideanSpace ℝ (Fin m)} (hx : x 0 ≤ 0) : 0 ≤ (reflectE x) 0 := by
  rw [reflectE_coord]; linarith

theorem foldMap_of_nonpos {x : EuclideanSpace ℝ (Fin m)} (hx : x 0 ≤ 0) :
    foldMap x = ⟨reflectE x, reflectE_nonneg hx⟩ := by
  apply Subtype.ext
  show x - (2 * min (x 0) 0) • EuclideanSpace.single (0 : Fin m) (1 : ℝ) = reflectE x
  rw [min_eq_left hx]
  rfl

theorem foldMap_coe_self (u : EuclideanHalfSpace m) : foldMap (Subtype.val u) = u := by
  rw [foldMap_of_nonneg (x := Subtype.val u) u.2]
  rfl

theorem foldMap_reflectE {d : EuclideanSpace ℝ (Fin m)} (hd : 0 ≤ d 0) :
    foldMap (reflectE d) = ⟨d, hd⟩ := by
  have h1 : (reflectE d) 0 = -(d 0) := reflectE_coord d
  have hmin : min ((reflectE d) 0) 0 = (reflectE d) 0 := min_eq_left (by rw [h1]; linarith)
  apply Subtype.ext
  show reflectE d - (2 * min ((reflectE d) 0) 0) • EuclideanSpace.single (0 : Fin m) (1 : ℝ) = d
  rw [hmin, h1, reflectE,
    show (2 * (-(d 0))) = -(2 * (d 0)) from by ring, neg_smul, sub_neg_eq_add, sub_add_cancel]

theorem foldMap_preimage (D : Set (EuclideanHalfSpace m)) :
    foldMap ⁻¹' D = Subtype.val '' D ∪ reflectE '' (Subtype.val '' D) := by
  ext x
  constructor
  · intro hx
    rcases le_total 0 (x 0) with h0 | h0
    · exact Or.inl ⟨foldMap x, hx, congrArg Subtype.val (foldMap_of_nonneg h0)⟩
    · refine Or.inr ⟨reflectE x, ⟨foldMap x, hx, congrArg Subtype.val (foldMap_of_nonpos h0)⟩,
        reflectE_involutive x⟩
  · intro hx
    rcases hx with ⟨d, hdD, rfl⟩ | ⟨d, ⟨v, hvD, rfl⟩, rfl⟩
    · change foldMap (Subtype.val d) ∈ D
      rw [foldMap_coe_self]; exact hdD
    · change foldMap (reflectE (Subtype.val v)) ∈ D
      rw [foldMap_reflectE v.2]; exact hvD

theorem isCompact_foldMap_preimage {D : Set (EuclideanHalfSpace m)}
    (hD : IsCompact D) : IsCompact (foldMap ⁻¹' D) := by
  rw [foldMap_preimage]
  exact (hD.image continuous_subtype_val).union
    ((hD.image continuous_subtype_val).image continuous_reflectE)

/-- **The flat model of the half-space**: for `U` open in `𝓡∂ m` and `D ⊆ U` compact, the relative
homology `H_i(U, U∖D)` vanishes above the dimension `m`.

The proof doubles the half-space: the fold map `foldMap : ℝᵐ → 𝓡∂ m` is a retraction, and the
preimage of the pair `(U,D)` is a pair `(U',D')` of an open and a compact subset of `ℝᵐ`; the
inclusion `U ↪ U'` and the fold give a retraction of pairs, so `H_i(U, U∖D)` is a direct summand of
`H_i(U', U'∖D')`, which vanishes by the Euclidean statement. -/
theorem halfspace_relChains_vanishing (hm : 1 ≤ m)
    (U : Set (EuclideanHalfSpace m)) (hU : IsOpen U)
    (D : Set (EuclideanHalfSpace m)) (hDU : D ⊆ U) (hDc : IsCompact D)
    (i : ℕ) (hi : m < i) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥U)
      (Work.Cohomology.pdRelSub (M := TopCat.of (EuclideanHalfSpace m)) U D)).homology i) := by
  set U' : Set (EuclideanSpace ℝ (Fin m)) := foldMap ⁻¹' U with hU'def
  set D' : Set (EuclideanSpace ℝ (Fin m)) := foldMap ⁻¹' D with hD'def
  have hU'open : IsOpen U' := hU.preimage continuous_foldMap
  have hD'cpt : IsCompact D' := isCompact_foldMap_preimage hDc
  have hD'U' : D' ⊆ U' := fun x hx => hDU hx
  have heuc : IsZero ((Work.Cohomology.relChains (TopCat.of ↥U')
      (Work.Cohomology.pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin m))) U' D')).homology i) :=
    Work.Cohomology.relChains_vanishing_compact_specific hm U' hU'open D' hD'U' hD'cpt i hi
  have hins : ∀ u : ↥U, foldMap (Subtype.val (u : EuclideanHalfSpace m)) ∈ U :=
    fun u => by rw [foldMap_coe_self]; exact u.2
  let f : TopCat.of ↥U ⟶ TopCat.of ↥U' :=
    TopCat.ofHom ⟨fun u => ⟨Subtype.val (u : EuclideanHalfSpace m), hins u⟩,
      Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _⟩
  let g : TopCat.of ↥U' ⟶ TopCat.of ↥U :=
    TopCat.ofHom ⟨fun x => ⟨foldMap (x : EuclideanSpace ℝ (Fin m)), x.2⟩,
      Continuous.subtype_mk (continuous_foldMap.comp continuous_subtype_val) _⟩
  have hf : ∀ a ∈ Work.Cohomology.pdRelSub (M := TopCat.of (EuclideanHalfSpace m)) U D,
      f.hom a ∈ Work.Cohomology.pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin m))) U' D' := by
    intro a ha
    change foldMap (Subtype.val (f.hom a) : EuclideanSpace ℝ (Fin m)) ∉ D
    have h1 : (Subtype.val (f.hom a) : EuclideanSpace ℝ (Fin m))
        = Subtype.val (a : EuclideanHalfSpace m) := rfl
    rw [h1, foldMap_coe_self]
    exact ha
  have hg : ∀ b ∈ Work.Cohomology.pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin m))) U' D',
      g.hom b ∈ Work.Cohomology.pdRelSub (M := TopCat.of (EuclideanHalfSpace m)) U D := by
    intro b hb
    change foldMap (Subtype.val b : EuclideanSpace ℝ (Fin m)) ∉ D
    exact hb
  have hgf : f ≫ g = 𝟙 (TopCat.of ↥U) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro u
    exact Subtype.ext (foldMap_coe_self (u : EuclideanHalfSpace m))
  exact isZero_relChains_of_retract f g hf hg hgf heuc

end Flat

/-! ## 3. Compact sets inside the source of a chart -/

/-- **A compact set inside the source of a chart**: the relative homology `H_i(W, W∖C)` vanishes
above the dimension.  Excision replaces `W` by the chart source, the chart homeomorphism by the
chart target, and the flat model of the half-space finishes. -/
theorem isZero_relChains_of_subset_chartSource {n : ℕ} {W : TopCat} [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] (z : W) {C : Set W}
    (hCsrc : C ⊆ (chartAt (EuclideanHalfSpace (n + 1)) z).source) (hCc : IsCompact C)
    (i : ℕ) (hi : n + 1 < i) :
    IsZero ((Work.Cohomology.relChains W Cᶜ).homology i) := by
  set e := chartAt (EuclideanHalfSpace (n + 1)) z with he
  have hAopen : IsOpen (Cᶜ : Set W) := hCc.isClosed.isOpen_compl
  have hcov : e.source ∪ (Cᶜ : Set W) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases h : y ∈ C
    · exact Or.inl (hCsrc h)
    · exact Or.inr h
  obtain ⟨e1⟩ := excision_iso W e.source (Cᶜ : Set W) e.open_source hAopen hcov i
  have hAB : ∀ y : ↥e.source, (y ∈ {y : ↥e.source | (y : W) ∈ (Cᶜ : Set W)})
      ↔ e.toHomeomorphSourceTarget y
          ∈ Work.Cohomology.pdRelSub (M := TopCat.of (EuclideanHalfSpace (n + 1))) e.target
              (e '' C) := by
    intro y
    show ((y : W) ∉ C) ↔ ¬ ((e.toHomeomorphSourceTarget y : EuclideanHalfSpace (n + 1)) ∈ e '' C)
    constructor
    · intro hy hmem
      obtain ⟨c, hcC, hce⟩ := hmem
      have hcs : c ∈ e.source := hCsrc hcC
      have hcy : c = y := e.toPartialEquiv.injOn hcs y.2 hce
      exact hy (hcy ▸ hcC)
    · intro hy hyC
      exact hy ⟨y, hyC, rfl⟩
  obtain ⟨e2⟩ := homeoRelChainsIso e.toHomeomorphSourceTarget
    {y : ↥e.source | (y : W) ∈ (Cᶜ : Set W)}
    (Work.Cohomology.pdRelSub (M := TopCat.of (EuclideanHalfSpace (n + 1))) e.target (e '' C)) hAB i
  have hsub : e '' C ⊆ e.target := by
    rintro y ⟨c, hc, rfl⟩
    exact e.map_source (hCsrc hc)
  have hcpt : IsCompact (e '' C) := hCc.image_of_continuousOn (e.continuousOn.mono hCsrc)
  have hflat : IsZero ((Work.Cohomology.relChains (TopCat.of ↥e.target)
      (Work.Cohomology.pdRelSub (M := TopCat.of (EuclideanHalfSpace (n + 1))) e.target (e '' C))).homology i) :=
    halfspace_relChains_vanishing (m := n + 1) (by omega) e.target e.open_target (e '' C) hsub hcpt i hi
  exact IsZero.of_iso (IsZero.of_iso hflat e2) e1.symm

/-! ## 4. The finite-cover induction -/

/-- **The Mayer–Vietoris induction over a finite closed cover.**  If every compact set contained in
one of the closed pieces `K a` has vanishing relative homology above `m`, then so does every compact
set contained in a finite union of the pieces. -/
theorem isZero_relChains_of_cover_finset {M : TopCat} [T2Space M] {m : ℕ} {ι : Type} [DecidableEq ι]
    (K : ι → Set M) (hKcl : ∀ a, IsClosed (K a))
    (hbase : ∀ (a : ι) (C : Set M), IsCompact C → C ⊆ K a → ∀ i, m < i →
      IsZero ((Work.Cohomology.relChains M Cᶜ).homology i)) :
    ∀ (t : Finset ι) (C : Set M), IsCompact C → C ⊆ ⋃ a ∈ t, K a →
      ∀ i, m < i → IsZero ((Work.Cohomology.relChains M Cᶜ).homology i) := by
  classical
  intro t
  induction t using Finset.induction_on with
  | empty =>
      intro C _ hcov i _
      have hC : C = (∅ : Set M) := by
        refine Set.subset_empty_iff.mp ?_
        intro x hx
        simpa using hcov hx
      rw [hC, Set.compl_empty]
      exact Work.Cohomology.isZero_relChains_univ M i
  | insert a s has ih =>
      intro C hCc hcov i hi
      have hKacl : IsClosed (K a) := hKcl a
      have hKscl : IsClosed (⋃ b ∈ s, K b) :=
        Set.Finite.isClosed_biUnion s.finite_toSet (fun b _ => hKcl b)
      have hC1 : IsCompact (C ∩ ⋃ b ∈ s, K b) := hCc.inter_right hKscl
      have hC2 : IsCompact (C ∩ K a) := hCc.inter_right hKacl
      have hsub1 : C ∩ (⋃ b ∈ s, K b) ⊆ ⋃ b ∈ s, K b := Set.inter_subset_right
      have h1 : IsZero ((Work.Cohomology.relChains M (C ∩ ⋃ b ∈ s, K b)ᶜ).homology i) :=
        ih (C ∩ ⋃ b ∈ s, K b) hC1 hsub1 i hi
      have h1' : IsZero ((Work.Cohomology.relChains M (C ∩ ⋃ b ∈ s, K b)ᶜ).homology (i + 1)) :=
        ih (C ∩ ⋃ b ∈ s, K b) hC1 hsub1 (i + 1) (by omega)
      have h2 : IsZero ((Work.Cohomology.relChains M (C ∩ K a)ᶜ).homology i) :=
        hbase a (C ∩ K a) hC2 Set.inter_subset_right i hi
      have h3 : IsZero
          ((Work.Cohomology.relChains M ((C ∩ ⋃ b ∈ s, K b) ∩ (C ∩ K a))ᶜ).homology i) :=
        hbase a _ (hC1.inter hC2) (fun x hx => hx.2.2) i hi
      have h3' : IsZero
          ((Work.Cohomology.relChains M ((C ∩ ⋃ b ∈ s, K b) ∩ (C ∩ K a))ᶜ).homology (i + 1)) :=
        hbase a _ (hC1.inter hC2) (fun x hx => hx.2.2) (i + 1) (by omega)
      have hmain := Work.Cohomology.isZero_relChains_union (M := M)
        (K := C ∩ ⋃ b ∈ s, K b) (L := C ∩ K a) hC1.isClosed hC2.isClosed i h1 h1' h2 h3 h3'
      have hset : (C ∩ ⋃ b ∈ s, K b) ∪ (C ∩ K a) = C := by
        have h2 : (C ∩ ⋃ b ∈ s, K b) ∪ (C ∩ K a)
            = C ∩ ((⋃ b ∈ s, K b) ∪ K a) := by
          rw [← Set.inter_union_distrib_left C (⋃ b ∈ s, K b) (K a)]
        rw [h2, Set.union_comm (⋃ b ∈ s, K b) (K a), ← Finset.set_biUnion_insert a s K]
        exact Set.inter_eq_left.mpr hcov
      rwa [hset] at hmain

/-! ## 5. The cover by coordinate half-balls, and the theorem -/

/-- **A compact set is covered by finitely many coordinate half-balls** (no avoidance condition, and
in every universe). -/
theorem exists_halfBallPiece_cover {n : ℕ} (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] {A : Set W} (hA : IsCompact A) :
    ∃ (m : ℕ) (z : Fin m → W) (r : Fin m → ℝ),
      (∀ i, 0 < r i) ∧ (∀ i, halfBallGood (n + 1) W (z i) (r i)) ∧
      A ⊆ ⋃ i, halfBallPiece (n + 1) W (z i) (r i) := by
  classical
  have key : ∀ a : W, ∃ rr : ℝ, 0 < rr ∧ halfBallGood (n + 1) W a rr := by
    intro a
    obtain ⟨rr, hrr, hgood, -⟩ :=
      exists_halfBall_subset n (U := Set.univ) isOpen_univ (Set.mem_univ a)
    exact ⟨rr, hrr, hgood⟩
  choose r hr hgood using key
  let U : W → Set W := fun a => (chartAt (EuclideanHalfSpace (n + 1)) a) ⁻¹'
      (halfIncl (n + 1) ⁻¹'
        Metric.ball (halfIncl (n + 1) ((chartAt (EuclideanHalfSpace (n + 1)) a) a)) (r a / 2))
      ∩ (chartAt (EuclideanHalfSpace (n + 1)) a).source
  have hUopen : ∀ a, IsOpen (U a) := by
    intro a
    show IsOpen ((chartAt (EuclideanHalfSpace (n + 1)) a) ⁻¹'
      (halfIncl (n + 1) ⁻¹'
        Metric.ball (halfIncl (n + 1) ((chartAt (EuclideanHalfSpace (n + 1)) a) a)) (r a / 2))
      ∩ (chartAt (EuclideanHalfSpace (n + 1)) a).source)
    rw [Set.inter_comm]
    exact (chartAt (EuclideanHalfSpace (n + 1)) a).isOpen_inter_preimage
      (Metric.isOpen_ball.preimage continuous_subtype_val)
  have hUsub : ∀ a, U a ⊆ halfBallPiece (n + 1) W a (r a) := by
    intro a y hy
    exact ⟨Metric.ball_subset_closedBall hy.1, hy.2⟩
  have hUself : ∀ a, a ∈ U a := by
    intro a
    refine ⟨?_, mem_chart_source _ a⟩
    show halfIncl (n + 1) ((chartAt (EuclideanHalfSpace (n + 1)) a) a)
      ∈ Metric.ball (halfIncl (n + 1) ((chartAt (EuclideanHalfSpace (n + 1)) a) a)) (r a / 2)
    exact Metric.mem_ball_self (by linarith [hr a])
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover U hUopen
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hUself x⟩)
  refine ⟨t.card, fun i => ((t.equivFin.symm i : ↥t) : W),
    fun i => r ((t.equivFin.symm i : ↥t) : W), fun i => hr _, fun i => hgood _, ?_⟩
  intro x hx
  obtain ⟨a, hat, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
  refine Set.mem_iUnion.mpr ⟨t.equivFin ⟨a, hat⟩, ?_⟩
  show x ∈ halfBallPiece (n + 1) W ((t.equivFin.symm (t.equivFin ⟨a, hat⟩) : ↥t) : W)
    (r ((t.equivFin.symm (t.equivFin ⟨a, hat⟩) : ↥t) : W))
  rw [Equiv.symm_apply_apply]
  exact hUsub a hxa

/-- **Hatcher 3.27(b) for the half-space model**: for a space `W` charted in dimension `n+1` by the
half-space, a compact subset `A` and `i > n+1`, the relative singular homology `H_i(W, W∖A)`
vanishes.  This is `Work.Orient.HalfVanishingProp n`. -/
theorem HalfVanishing (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] (A : Set W) (hA : IsCompact A)
    (i : ℕ) (hi : n + 1 < i) :
    CategoryTheory.Limits.IsZero (Work.Orient.RelH W i A) := by
  obtain ⟨m, z, r, hr, hgood, hcov⟩ := exists_halfBallPiece_cover (n := n) W hA
  have hKcl : ∀ a : Fin m, IsClosed (halfBallPiece (n + 1) W (z a) (r a)) := fun a =>
    (IsCoordHalfBall.isCompact (n := n + 1) ⟨z a, r a, hr a, hgood a, rfl⟩).isClosed
  have hbase : ∀ (a : Fin m) (C : Set W), IsCompact C →
      C ⊆ halfBallPiece (n + 1) W (z a) (r a) → ∀ i, n + 1 < i →
      IsZero ((Work.Cohomology.relChains W Cᶜ).homology i) := by
    intro a C hCc hCK i hi
    exact isZero_relChains_of_subset_chartSource (n := n) (W := W) (z a)
      (hCK.trans Set.inter_subset_right) hCc i hi
  have hcov' : A ⊆ ⋃ a ∈ (Finset.univ : Finset (Fin m)),
      halfBallPiece (n + 1) W (z a) (r a) := by
    intro x hx
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hcov hx)
    exact Set.mem_iUnion₂.mpr ⟨a, Finset.mem_univ a, ha⟩
  exact isZero_relChains_of_cover_finset (M := W) (m := n + 1)
    (fun a : Fin m => halfBallPiece (n + 1) W (z a) (r a)) hKcl hbase Finset.univ A hA hcov' i hi

end -- section
end Work.Orient.Boundary
