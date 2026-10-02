import Mathlib
import Submission.Work.Orient.Defs
import Submission.Work.Orient.Port.Hatcher
import Submission.Work.Orient.Port.Hatcher2
import Submission.Work.ThomBordism.convexCover
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.relChains_empty_homology_iso
import Submission.Work.Cohomology.relChains_vanishing_of_compact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# ORIENT: fundamental classes of compact manifolds without boundary

The main theorems of the ORIENT chapter for a compact `n`-manifold `M` without boundary
(`ChartedSpace (EuclideanSpace ℝ (Fin n)) M`, `n ≥ 1`, `CompactSpace`, `T2Space`):

* `Work.Orient.eq_zero_of_locClass_eq_zero` — **uniqueness** (Hatcher 3.27(a)): a class of `H_n(M)`
  whose local class vanishes everywhere is zero;
* `Work.Orient.eq_zero_of_locClass_eq_zero_at` — for **connected** `M` one point suffices;
* `Work.Orient.exists_fundClass_of_isOrientFamily` — **existence** from an orientation;
* `Work.Orient.generates_of_isFundClass`, `Work.Orient.span_singleton_eq_top_of_isFundClass` — a
  fundamental class generates `H_n(M) ≅ ℤ` (connected `M`);
* `Work.Orient.isFundClass_of_span_singleton_eq_top` — conversely, on an orientable connected `M` a
  generator of `H_n(M)` is a fundamental class.

The proofs use the ported Hatcher machinery `Submission/Work/Orient/Port/Hatcher.lean`
(`unionZero`, `compactZero`, `existsLift`), `Work.ThomBordism.convexCover`, `excludedMV`, and the
passage between the "excluded set" model `RelH M n A` and `H_n(M)` given by `relHUnivIso` below.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.Orient

noncomputable section

variable {n : ℕ}

/-! ## Transport of the excluded set -/

/-- **Restriction commutes with a transport of the excluded sets.** -/
theorem resRelH_eqToIso {M : TopCat} {n : ℕ} {B B' D D' : Set M} (hB : B = B') (hD : D = D')
    (h : D ⊆ B) (h' : D' ⊆ B') (v : RelH M n B) :
    resRelH M n h' ((eqToIso (congrArg (fun S : Set M => RelH M n S) hB)).hom v)
      = (eqToIso (congrArg (fun S : Set M => RelH M n S) hD)).hom (resRelH M n h v) := by
  subst hB
  subst hD
  simp only [eqToIso_refl, Iso.refl_hom, CategoryTheory.id_apply,
    Work.Orient.Port.RelHmap_congr_h M n h' h]

/-- **The relabelling of the excluded set commutes with the projection of the pair.** -/
theorem eqToIso_inv_relCokerMap {M : TopCat} {n : ℕ} {A A' B : Set M} (hA : A = A')
    (h : A ⊆ B) (h' : A' ⊆ B) (v : (Work.Cohomology.relChains M A').homology n) :
    HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap M A B h) n
        ((eqToIso (congrArg (fun S : Set M => (Work.Cohomology.relChains M S).homology n) hA)).inv v)
      = HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap M A' B h') n v := by
  subst hA
  simp only [eqToIso_refl, Iso.refl_inv, CategoryTheory.id_apply,
    Work.ThomBordism.relCokerMap_congr_h h' h]

/-- A restriction of an inclusion `A ⊆ A` is the identity linear map. -/
theorem RelHmap_self' {M : TopCat} {n : ℕ} {A : Set M} (h : A ⊆ A) :
    resRelH M n h = LinearMap.id :=
  Work.Orient.Port.RelHmap_self M n h

/-- The restriction map is injective whenever the two excluded sets are equal. -/
theorem resRelH_injective_of_eq {M : TopCat} {n : ℕ} {A B : Set M} (hAB : A = B) (h : A ⊆ B) :
    Function.Injective (resRelH M n h) := by
  subst hAB
  rw [RelHmap_self']
  exact fun a b hab => hab

/-! ## The model of `H_n(M)` as the excluded set `univ` -/

/-- **The canonical isomorphism `RelH M n univ ≅ H_n(M)`**: the relative homology of the pair
`(M, M∖univ) = (M,∅)` is the absolute homology. -/
noncomputable def relHUnivIso (M : TopCat) (n : ℕ) :
    RelH M n (Set.univ : Set M) ≅ (Work.Cohomology.singularChains ℤ M).homology n := by
  haveI := Work.Cohomology.relChains_empty_homology_iso M n
  exact eqToIso (congrArg (fun S : Set M => (Work.Cohomology.relChains M S).homology n)
      Set.compl_univ) ≪≫
    (asIso (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains M (∅ : Set M))) n)).symm

/-- **The inverse of `relHUnivIso` is compatible with the localisation maps.** -/
theorem relHUnivIso_inv_restrict (M : TopCat) (n : ℕ)
    (c : (Work.Cohomology.singularChains ℤ M).homology n) (x : M)
    (h : ({x} : Set M) ⊆ Set.univ) :
    resRelH M n h ((relHUnivIso M n).inv c) = locClass M n c x := by
  haveI := Work.Cohomology.relChains_empty_homology_iso M n
  have hcomp : (relHUnivIso M n).inv
      = (HomologicalComplex.homologyMap (cokernel.π (Work.Cohomology.inclChains M (∅ : Set M))) n) ≫
        (eqToIso (congrArg (fun S : Set M => (Work.Cohomology.relChains M S).homology n)
          Set.compl_univ)).inv := rfl
  rw [locClass_eq_relClass, relClass, Work.Cohomology.relLocClass_singleton, hcomp]
  simp only [ModuleCat.comp_apply]
  have hkey := eqToIso_inv_relCokerMap (M := M) (n := n)
    (A := (Set.univ : Set M)ᶜ) (A' := (∅ : Set M)) (B := ({x} : Set M)ᶜ) Set.compl_univ
    (Set.compl_subset_compl.mpr h) (Set.empty_subset _)
    ((HomologicalComplex.homologyMap (cokernel.π (Work.Cohomology.inclChains M (∅ : Set M))) n) c)
  show HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap M (Set.univ : Set M)ᶜ
      ({x} : Set M)ᶜ (Set.compl_subset_compl.mpr h)) n
      ((ConcreteCategory.hom ((eqToIso (congrArg
        (fun S : Set M => (Work.Cohomology.relChains M S).homology n) Set.compl_univ)).inv))
        ((ConcreteCategory.hom (HomologicalComplex.homologyMap
          (cokernel.π (Work.Cohomology.inclChains M (∅ : Set M))) n)) c))
    = HomologicalComplex.homologyMap
        (cokernel.π (Work.Cohomology.inclChains M ({x} : Set M)ᶜ)) n c
  rw [hkey]
  rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp,
    Work.Cohomology.relCokerMap_comp_π]

/-! ## Gluing over a finite cover by coordinate balls -/

/-! ## Uniqueness -/

/-- **Uniqueness** (Hatcher 3.27(a)): a class of `H_n(M)` whose local class vanishes at every point
is zero. -/
theorem eq_zero_of_locClass_eq_zero (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (c : (Work.Cohomology.singularChains ℤ M).homology n)
    (h : ∀ x : M, locClass M n c x = 0) : c = 0 := by
  have hv : (relHUnivIso M n).inv c = 0 := by
    refine Work.Orient.Port.compactZero n hn M isCompact_univ ((relHUnivIso M n).inv c) ?_
    intro x hx
    rw [relHUnivIso_inv_restrict M n c x (Set.singleton_subset_iff.mpr hx)]
    exact h x
  calc c = (relHUnivIso M n).hom ((relHUnivIso M n).inv c) := (Iso.inv_hom_id_apply _ _).symm
    _ = 0 := by rw [hv, map_zero]

/-- **Uniqueness, equality form**: a class of `H_n(M)` is determined by its local classes. -/
theorem eq_of_locClass_eq (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (c c' : (Work.Cohomology.singularChains ℤ M).homology n)
    (h : ∀ x : M, locClass M n c x = locClass M n c' x) : c = c' := by
  have h0 : ∀ x : M, locClass M n (c - c') x = 0 := by
    intro x
    rw [locClass_sub, h x, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_locClass_eq_zero n hn M (c - c') h0)

/-! ## One point suffices on a connected manifold -/

/-- A coordinate ball around any point, which is a neighbourhood of it. -/
theorem exists_isCoordBall_mem_nhds (n : ℕ) (M : TopCat) [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (y : M) :
    ∃ K : Set M, IsCoordBall n M K ∧ y ∈ K ∧ K ∈ 𝓝 y := by
  set e := chartAt (EuclideanSpace ℝ (Fin n)) y with he
  have hy : y ∈ e.source := mem_chart_source (EuclideanSpace ℝ (Fin n)) y
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp e.open_target (e y) (e.map_source hy)
  refine ⟨e ⁻¹' Metric.closedBall (e y) (r / 2) ∩ e.source, ⟨y, r, hr, hsub, rfl⟩, ?_, ?_⟩
  · refine Set.mem_inter ?_ hy
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_self]
    linarith
  · have hopen : IsOpen (e ⁻¹' Metric.ball (e y) (r / 2) ∩ e.source) := by
      rw [Set.inter_comm]
      exact e.isOpen_inter_preimage Metric.isOpen_ball
    have hmem : y ∈ e ⁻¹' Metric.ball (e y) (r / 2) ∩ e.source := by
      refine Set.mem_inter ?_ hy
      rw [Set.mem_preimage, Metric.mem_ball, dist_self]
      linarith
    refine Filter.mem_of_superset (hopen.mem_nhds hmem) ?_
    intro z hz
    exact Set.mem_inter (Metric.ball_subset_closedBall hz.1) hz.2

/-- **The localisation at a coordinate ball vanishes iff the local class does**, at any of its
points. -/
theorem relClass_eq_zero_iff_locClass_eq_zero {M : TopCat} [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (hn : 1 ≤ n)
    {c : (Work.Cohomology.singularChains ℤ M).homology n} {K : Set M}
    (hK : IsCoordBall n M K) {y : M} (hy : y ∈ K) :
    relClass M n c K = 0 ↔ locClass M n c y = 0 := by
  haveI := Work.ThomBordism.IsCoordBall.isIso_restrict hn hK hy
  have hinj : Function.Injective (resRelH M n (Set.singleton_subset_iff.mpr hy)) := by
    intro u v huv
    exact (ModuleCat.mono_iff_injective (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap M Kᶜ ({y} : Set M)ᶜ
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy))) n)).mp inferInstance huv
  constructor
  · intro h
    have h1 : resRelH M n (Set.singleton_subset_iff.mpr hy) (relClass M n c K) = 0 := by
      rw [h]
      exact map_zero _
    rwa [relClass_restrict M n c hy] at h1
  · intro h
    refine hinj ?_
    rw [relClass_restrict M n c hy, map_zero]
    exact h

/-- **On a connected manifold, one point suffices** (Hatcher 3.27): a class of `H_n(M)` whose local
class vanishes at one point is zero (the set where it vanishes is clopen). -/
theorem eq_zero_of_locClass_eq_zero_at (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M]
    [T2Space M] [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (c : (Work.Cohomology.singularChains ℤ M).homology n) (x : M)
    (h : locClass M n c x = 0) : c = 0 := by
  have hclopen : IsClopen {y : M | locClass M n c y = 0} := by
    constructor
    · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro y hy
      obtain ⟨K, hK, hyK, hKn⟩ := exists_isCoordBall_mem_nhds n M y
      filter_upwards [hKn] with z hz
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
      intro hz0
      exact hy ((relClass_eq_zero_iff_locClass_eq_zero hn hK hyK).mp
        ((relClass_eq_zero_iff_locClass_eq_zero hn hK hz).mpr hz0))
    · rw [isOpen_iff_mem_nhds]
      intro y hy
      obtain ⟨K, hK, hyK, hKn⟩ := exists_isCoordBall_mem_nhds n M y
      filter_upwards [hKn] with z hz
      exact (relClass_eq_zero_iff_locClass_eq_zero hn hK hz).mp
        ((relClass_eq_zero_iff_locClass_eq_zero hn hK hyK).mpr hy)
  rcases isClopen_iff.mp hclopen with h0 | h0
  · have hx : x ∉ ({y : M | locClass M n c y = 0} : Set M) := by
      rw [h0]
      exact Set.notMem_empty x
    exact absurd h hx
  · refine eq_zero_of_locClass_eq_zero n hn M c (fun y => ?_)
    have : y ∈ ({y : M | locClass M n c y = 0} : Set M) := by rw [h0]; trivial
    exact this

/-! ## A fundamental class generates `H_n(M)` -/

/-- **A fundamental class is nonzero** (on a nonempty manifold): its local class is a generator of
the local group `H_n(M, M∖{x}) ≅ ℤ`, which is nontrivial. -/
theorem IsFundClass.ne_zero {M : TopCat} {n : ℕ} [Nonempty M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (hn : 1 ≤ n)
    {c : (Work.Cohomology.singularChains ℤ M).homology n} (h : IsFundClass M n c) : c ≠ 0 := by
  intro hc
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  have h0 : Submodule.span ℤ ({locClass M n c x} : Set (LocH M n x)) = ⊥ := by
    rw [hc, locClass_zero, Submodule.span_singleton_eq_bot]
  have htop : (⊥ : Submodule ℤ (LocH M n x)) = ⊤ := by rw [← h0]; exact h x
  haveI : Subsingleton (LocH M n x) := by
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ (⊥ : Submodule ℤ (LocH M n x)) := by rw [htop]; exact Submodule.mem_top
    have hb : b ∈ (⊥ : Submodule ℤ (LocH M n x)) := by rw [htop]; exact Submodule.mem_top
    rw [Submodule.mem_bot] at ha hb
    rw [ha, hb]
  obtain ⟨e⟩ := Work.Cohomology.localHomology n hn (M : Type) x
  have h2 : (ConcreteCategory.hom e.inv) (1 : ℤ) = 0 := Subsingleton.elim _ _
  have h3 := Iso.inv_hom_id_apply e (1 : ℤ)
  rw [h2, map_zero] at h3
  exact one_ne_zero h3.symm

/-- **A fundamental class generates `H_n(M)`** (for connected `M`): the localisation map at any point
is injective with image the cyclic group generated by the local class, so `H_n(M) ≅ ℤ` is generated
by the fundamental class. -/
theorem span_singleton_eq_top_of_isFundClass (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M]
    [T2Space M] [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (c : (Work.Cohomology.singularChains ℤ M).homology n) (hc : IsFundClass M n c) :
    Submodule.span ℤ ({c} : Set ((Work.Cohomology.singularChains ℤ M).homology n)) = ⊤ := by
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  set φ : (Work.Cohomology.singularChains ℤ M).homology n →ₗ[ℤ] LocH M n x :=
    (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains M {y : M | y ≠ x})) n).hom with hφ
  have hφc : φ c = locClass M n c x := rfl
  have hinj : Function.Injective φ := by
    intro u v huv
    have h1 : φ (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have h2 : locClass M n (u - v) x = 0 := h1
    exact sub_eq_zero.mp (eq_zero_of_locClass_eq_zero_at n hn M (u - v) x h2)
  rw [Submodule.eq_top_iff']
  intro d
  have hd : φ d ∈ Submodule.map φ (Submodule.span ℤ ({c} : Set _)) := by
    rw [Submodule.map_span, Set.image_singleton, hφc, hc x]
    exact Submodule.mem_top
  rw [Submodule.mem_map] at hd
  obtain ⟨y, hy, hxy⟩ := hd
  rwa [← hinj hxy]

/-! ## Existence of the fundamental class -/

/-- **Existence**: every orientation (a locally consistent family of local generators,
`Work.Orient.IsOrientFamily`) is the family of local classes of a fundamental class. -/
theorem exists_fundClass_of_isOrientFamily (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (γ : (x : M) → LocH M n x) (hγ : IsOrientFamily n M γ) :
    ∃ c : (Work.Cohomology.singularChains ℤ M).homology n,
      (∀ x : M, locClass M n c x = γ x) ∧ IsFundClass M n c := by
  classical
  obtain ⟨m, K, hcover, -, -, -, hIsCB⟩ := Work.ThomBordism.convexCover n hn M
  have hK : ∀ i : Fin m, IsCoordBall n M (K i) := fun i => hIsCB i
  choose a ha using fun i => hγ.2 (K i) (hK i)
  obtain ⟨γ₀, hγ₀⟩ := Work.Orient.Port.coverGlue n hn M (Finset.univ : Finset (Fin m)) K
    (fun i _ => hK i) a (fun i _ j _ x hx => by rw [ha i x hx.1, ha j x hx.2])
  have hU : (⋃ i ∈ (Finset.univ : Finset (Fin m)), K i) = Set.univ := by
    rw [show (⋃ i ∈ (Finset.univ : Finset (Fin m)), K i) = (⋃ i, K i) from by ext y; simp]
    exact hcover
  -- the global class
  set v : RelH M n (Set.univ : Set M) :=
    (eqToIso (congrArg (fun S : Set M => RelH M n S) hU)).hom γ₀ with hv
  set c : (Work.Cohomology.singularChains ℤ M).homology n := (relHUnivIso M n).hom v with hcdef
  have hloc : ∀ x : M, locClass M n c x = γ x := by
    intro x
    have hxU : x ∈ ⋃ i ∈ (Finset.univ : Finset (Fin m)), K i := by rw [hU]; trivial
    have h1 : locClass M n c x = resRelH M n
        (Set.singleton_subset_iff.mpr (Set.mem_univ x)) ((relHUnivIso M n).inv c) :=
      (relHUnivIso_inv_restrict M n c x (Set.singleton_subset_iff.mpr (Set.mem_univ x))).symm
    rw [h1]
    have h2 : (relHUnivIso M n).inv c = v := by
      rw [hcdef, Iso.hom_inv_id_apply]
    rw [h2, hv]
    have hcast := resRelH_eqToIso (M := M) (n := n)
      (B := (⋃ i ∈ (Finset.univ : Finset (Fin m)), K i)) (B' := Set.univ)
      (D := ({x} : Set M)) (D' := ({x} : Set M)) hU rfl
      (Set.singleton_subset_iff.mpr hxU) (Set.singleton_subset_iff.mpr (Set.mem_univ x)) γ₀
    simp only [eqToIso_refl, Iso.refl_hom, CategoryTheory.id_apply] at hcast
    rw [hcast]
    obtain ⟨i, -, hxi⟩ := Set.mem_iUnion₂.mp hxU
    have hfac : Work.ThomBordism.RelHmap M n (Set.singleton_subset_iff.mpr hxU) γ₀
        = Work.ThomBordism.RelHmap M n (Set.singleton_subset_iff.mpr hxi)
            (Work.ThomBordism.RelHmap M n
              (Set.subset_biUnion_of_mem (Finset.mem_univ i)) γ₀) := by
      rw [show Work.ThomBordism.RelHmap M n (Set.singleton_subset_iff.mpr hxi)
            (Work.ThomBordism.RelHmap M n
              (Set.subset_biUnion_of_mem (Finset.mem_univ i)) γ₀)
          = ((Work.ThomBordism.RelHmap M n (Set.singleton_subset_iff.mpr hxi)).comp
              (Work.ThomBordism.RelHmap M n
                (Set.subset_biUnion_of_mem (Finset.mem_univ i)))) γ₀ from rfl]
      rw [Work.Orient.Port.RelHmap_comp' M n (Set.singleton_subset_iff.mpr hxi)
        (Set.subset_biUnion_of_mem (Finset.mem_univ i)) (Set.singleton_subset_iff.mpr hxU)]
      rfl
    rw [hfac, hγ₀ i (Finset.mem_univ i), ha i x hxi]
  refine ⟨c, hloc, fun x => ?_⟩
  rw [hloc x]
  exact hγ.1 x

/-- **A generator of `H_n(M)` is a fundamental class** (on an orientable connected `M`): the
localisation map at a point is surjective (its source is generated by the fundamental class `c₀` and
its image is generated by the local class of `c₀`), hence the local class of `c` generates as well. -/
theorem isFundClass_of_span_singleton_eq_top (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M]
    [T2Space M] [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (hM : ∃ γ : (x : M) → LocH M n x, IsOrientFamily n M γ)
    (c : (Work.Cohomology.singularChains ℤ M).homology n)
    (h : Submodule.span ℤ ({c} : Set ((Work.Cohomology.singularChains ℤ M).homology n)) = ⊤) :
    IsFundClass M n c := by
  obtain ⟨c₀, -, hc₀f⟩ := exists_fundClass_of_isOrientFamily n hn M _ hM.choose_spec
  have hgen₀ := span_singleton_eq_top_of_isFundClass n hn M c₀ hc₀f
  intro x
  set φ : (Work.Cohomology.singularChains ℤ M).homology n →ₗ[ℤ] LocH M n x :=
    (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains M {y : M | y ≠ x})) n).hom with hφ
  have hφc : φ c = locClass M n c x := rfl
  have hφc₀ : φ c₀ = locClass M n c₀ x := rfl
  have hsurj : Function.Surjective φ := by
    refine LinearMap.range_eq_top.mp ?_
    rw [← Submodule.map_top, ← hgen₀, Submodule.map_span, Set.image_singleton, hφc₀]
    exact hc₀f x
  have hmap : Submodule.map φ (Submodule.span ℤ ({c} : Set _)) = ⊤ := by
    rw [h, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hsurj
  rw [Submodule.map_span, Set.image_singleton] at hmap
  rwa [hφc] at hmap

end
end Work.Orient
