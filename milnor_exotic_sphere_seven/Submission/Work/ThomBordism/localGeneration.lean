import Mathlib
import Submission.Work.ThomBordism.localGenDefs
import Submission.Work.ThomBordism.localGenAux
import Submission.Work.ThomBordism.excludedMV
import Submission.Work.ThomBordism.convexLocalIso
import Submission.Work.ThomBordism.convexCover
import Submission.Work.Cohomology.isZero_relSubPunctured
import Submission.Work.Cohomology.capped_localDegree_generator
import Submission.Work.Cohomology.pd_triple
import Submission.Work.Cohomology.relChainsPairModel
import Submission.Work.Cohomology.homologyTwoCover
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.relChains_vanishing_of_compact
import Submission.Work.Cohomology.homology_vanishing_relative_compact
import Submission.Work.Cohomology.relChains_empty_homology_iso
import Submission.Work.Cohomology.euclidean_top_homology_vanishing
import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.Cohomology.local_generator_ball
import Submission.Work.Cohomology.localClass_point_injective
import Submission.Work.Cohomology.local_generator_convex

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Local generation of a global generator of `H_n(M) ≅ ℤ`

For a compact connected `n`-manifold `M` (charted in `ℝ^n`, `n ≥ 1`) and a class
`c ∈ H_n(M; ℤ)` which generates `H_n(M; ℤ)`, the image of `c` in the local group
`H_n(M, M∖{x}; ℤ) ≅ ℤ` generates for every `x ∈ M` (`Work.ThomBordism.localGeneration`).

The proof has three ingredients.

* The map `H_n(M) → H_n(M, M∖univ)` (the localisation at the empty excluded set) is an
  isomorphism; this is read off from the long exact sequence of the pair `(M, M∖univ)`, whose
  first term vanishes because `M∖univ` is empty.
* The *index* of `c` at a point, `Ind x = |ptIso x (α_x)|`, is locally constant (two isomorphisms
  of a `ℤ`-module with `ℤ` differ by a unit, so the absolute value is well defined) and hence
  constant on the connected `M`; write it `m`.  Over every coordinate ball the class `c` is `m`
  times a generator, and these "roots" are consistent because the local groups are torsion free.
* Gluing the roots over a finite cover by coordinate balls (`coverGlue`, an induction using the
  Mayer–Vietoris exactness `excludedMV` and the uniqueness `compactZero`) yields a global class
  `γ` with `m • γ = c`; since `H_n(M) = ℤ·c`, `γ = b • c`, so `(m * b - 1) • c = 0`, and evaluation
  at a point shows `m * b = 1`, whence `m = 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped ZeroObject

namespace Work.ThomBordism

noncomputable section

variable {n : ℕ}

/-! ## The local classes in the `RelH` spelling -/

/-- The class of `c ∈ H_n(M)` at the excluded set `K`, in the `RelH` spelling. -/
abbrev relClass (M : TopCat) (n : ℕ) (c : (Work.Cohomology.singularChains ℤ M).homology n)
    (K : Set M) : RelH M n K :=
  Work.Cohomology.relLocClass M n c K

/-- The local class of `c` at the point `x`. -/
abbrev locClass (M : TopCat) (n : ℕ) (c : (Work.Cohomology.singularChains ℤ M).homology n)
    (x : M) : RelH M n ({x} : Set M) :=
  Work.Cohomology.relLocClass M n c {x}

/-- Restriction of the class at `univ` to a point. -/
theorem relClass_univ_restrict (M : TopCat) (n : ℕ)
    (c : (Work.Cohomology.singularChains ℤ M).homology n) (x : M) :
    RelHmap M n (Set.singleton_subset_iff.mpr (Set.mem_univ x)) (relClass M n c Set.univ)
      = locClass M n c x :=
  Work.Cohomology.relLocClass_restrict M n c (Set.singleton_subset_iff.mpr (Set.mem_univ x))

/-- Restriction of the class at a set `K` containing `x` to the point `x`. -/
theorem relClass_restrict (M : TopCat) (n : ℕ)
    (c : (Work.Cohomology.singularChains ℤ M).homology n) {K : Set M} {x : M} (hx : x ∈ K) :
    RelHmap M n (Set.singleton_subset_iff.mpr hx) (relClass M n c K) = locClass M n c x :=
  Work.Cohomology.relLocClass_restrict M n c (Set.singleton_subset_iff.mpr hx)

/-- The local classes are additive in the global class. -/
theorem relClass_add (M : TopCat) (n : ℕ) (K : Set M)
    (c c' : (Work.Cohomology.singularChains ℤ M).homology n) :
    relClass M n (c + c') K = relClass M n c K + relClass M n c' K :=
  map_add _ _ _

/-- The local classes are `ℤ`-linear in the global class. -/
theorem relClass_zsmul (M : TopCat) (n : ℕ) (K : Set M) (k : ℤ)
    (c : (Work.Cohomology.singularChains ℤ M).homology n) :
    relClass M n (k • c) K = k • relClass M n c K :=
  map_zsmul _ _ _

/-- The local class of `0` vanishes. -/
theorem relClass_zero (M : TopCat) (n : ℕ) (K : Set M) :
    relClass M n (0 : (Work.Cohomology.singularChains ℤ M).homology n) K = 0 :=
  map_zero _

/-! ## Elementary module theory over `ℤ` -/

/-- Two isomorphisms of a `ℤ`-module with `ℤ` have the same `natAbs` on every element. -/
theorem natAbs_eq_of_linearEquiv_int {A : Type*} [AddCommGroup A] [Module ℤ A]
    (e₁ e₂ : A ≃ₗ[ℤ] ℤ) (v : A) : (e₁ v).natAbs = (e₂ v).natAbs := by
  have hmul : ∀ (φ : ℤ →ₗ[ℤ] ℤ) (n : ℤ), φ n = n * φ 1 := by
    intro φ n
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [map_add, ih]
      ring
    | pred k ih =>
      rw [map_sub, ih]
      ring
  have h1 : ∀ a : A, e₂ a = e₁ a * (e₂ (e₁.symm 1)) := by
    intro a
    have h2 : e₂ a = ((e₂ : A →ₗ[ℤ] ℤ).comp (e₁.symm : ℤ →ₗ[ℤ] A)) (e₁ a) := by
      simp [LinearMap.comp_apply]
    rw [h2, hmul ((e₂ : A →ₗ[ℤ] ℤ).comp (e₁.symm : ℤ →ₗ[ℤ] A)) (e₁ a)]
    simp
  have hunit : (e₂ (e₁.symm 1)).natAbs = 1 := by
    obtain ⟨a, ha⟩ := e₂.surjective 1
    have h3 : e₁ a * (e₂ (e₁.symm 1)) = 1 := by rw [← h1 a, ha]
    have h4 : (e₁ a).natAbs * (e₂ (e₁.symm 1)).natAbs = 1 := by
      rw [← Int.natAbs_mul, h3]
      rfl
    exact Nat.eq_one_of_mul_eq_one_left h4
  rw [h1 v, Int.natAbs_mul, hunit, mul_one]

/-- The generator `e.symm 1` of a `ℤ`-module isomorphic to `ℤ` generates. -/
theorem span_symm_one_eq_top {A : Type*} [AddCommGroup A] [Module ℤ A] (e : A ≃ₗ[ℤ] ℤ) :
    Submodule.span ℤ ({e.symm 1} : Set A) = ⊤ := by
  have hmaps : Submodule.map (e : A →ₗ[ℤ] ℤ) (Submodule.span ℤ ({e.symm 1} : Set A)) = ⊤ := by
    rw [Submodule.map_span]
    have himg : (e : A →ₗ[ℤ] ℤ) '' ({e.symm 1} : Set A) = ({(1 : ℤ)} : Set ℤ) := by
      rw [Set.image_singleton]
      simp
    rw [himg, Submodule.eq_top_iff']
    intro m
    exact Submodule.mem_span_singleton.mpr ⟨m, by simp⟩
  have hc : Submodule.comap (e : A →ₗ[ℤ] ℤ) (Submodule.map (e : A →ₗ[ℤ] ℤ)
      (Submodule.span ℤ ({e.symm 1} : Set A))) = Submodule.span ℤ ({e.symm 1} : Set A) := by
    rw [Submodule.comap_map_eq, LinearMap.ker_eq_bot.mpr e.injective, sup_bot_eq]
  rw [hmaps, Submodule.comap_top] at hc
  exact hc.symm

/-- The generator `-e.symm 1` also generates. -/
theorem span_symm_neg_one_eq_top {A : Type*} [AddCommGroup A] [Module ℤ A] (e : A ≃ₗ[ℤ] ℤ) :
    Submodule.span ℤ ({e.symm (-1)} : Set A) = ⊤ := by
  have h : e.symm (-1) = -(e.symm 1) := map_neg e.symm 1
  rw [h]
  have hset : ({-(e.symm 1)} : Set A) = -({e.symm 1} : Set A) := by ext x; simp
  rw [hset, Submodule.span_neg]
  exact span_symm_one_eq_top e

/-- A generator of a module whose span is everything is nonzero. -/
theorem ne_zero_of_span_singleton_eq_top {A : Type*} [AddCommGroup A] [Module ℤ A]
    {v : A} (h : Submodule.span ℤ ({v} : Set A) = ⊤) (hnt : Nontrivial A) : v ≠ 0 := by
  intro hv
  have hbot : Submodule.span ℤ ({v} : Set A) = ⊥ := by
    rw [hv]
    exact Submodule.span_singleton_eq_bot.mpr rfl
  haveI : Subsingleton A :=
    ⟨fun x y => by
      have hx : x ∈ (⊥ : Submodule ℤ A) := by
        rw [hbot.symm.trans h]
        exact Submodule.mem_top
      have hy : y ∈ (⊥ : Submodule ℤ A) := by
        rw [hbot.symm.trans h]
        exact Submodule.mem_top
      rw [Submodule.mem_bot] at hx hy
      rw [hx, hy]⟩
  exact not_subsingleton A inferInstance

/-! ## The index of a local class at a point -/

/-- A chosen isomorphism of the local group at `x` with `ℤ`. -/
noncomputable def ptIso (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) :
    RelH M n ({x} : Set M) ≃ₗ[ℤ] ℤ :=
  (Classical.choice (RelH_point_iso n hn M x)).toLinearEquiv

/-- The local group at a point is nontrivial. -/
theorem nontrivial_relH_point (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) :
    Nontrivial (RelH M n ({x} : Set M)) :=
  ⟨(ptIso n hn M x).symm 0, (ptIso n hn M x).symm 1,
    fun h => by simpa using congrArg (ptIso n hn M x) h⟩

/-- **The index of the local class at a point**: the class `α_x` generates `mℤ` for this `m`. -/
noncomputable def Ind (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (c : (Work.Cohomology.singularChains ℤ M).homology n) (x : M) : ℕ :=
  (ptIso n hn M x (locClass M n c x)).natAbs

/-- The restriction out of a coordinate ball is a bijection. -/
theorem ballBij {M : TopCat} [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (hn : 1 ≤ n) {K : Set M}
    (hK : IsCoordBall n M K) {x : M} (hx : x ∈ K) :
    Function.Bijective (RelHmap M n (Set.singleton_subset_iff.mpr hx)) := by
  haveI := IsCoordBall.isIso_restrict (M := M) hn hK hx
  exact ⟨(ModuleCat.mono_iff_injective _).mp inferInstance,
    (ModuleCat.epi_iff_surjective _).mp inferInstance⟩

/-- The restriction out of a coordinate ball, as a linear equivalence. -/
noncomputable def ballEquiv {M : TopCat} [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (hn : 1 ≤ n) {K : Set M}
    (hK : IsCoordBall n M K) {x : M} (hx : x ∈ K) :
    RelH M n K ≃ₗ[ℤ] RelH M n ({x} : Set M) :=
  LinearEquiv.ofBijective (RelHmap M n (Set.singleton_subset_iff.mpr hx)) (ballBij hn hK hx)

/-- The linear equivalence `ballEquiv` is the restriction map. -/
theorem ballEquiv_apply {M : TopCat} [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (hn : 1 ≤ n) {K : Set M}
    (hK : IsCoordBall n M K) {x : M} (hx : x ∈ K) (w : RelH M n K) :
    ballEquiv (n := n) hn hK hx w = RelHmap M n (Set.singleton_subset_iff.mpr hx) w := by
  show (LinearEquiv.ofBijective (RelHmap M n (Set.singleton_subset_iff.mpr hx)) _) w = _
  exact LinearEquiv.ofBijective_apply _ w

/-- The index is locally constant: it agrees at all points of a coordinate ball. -/
theorem Ind_eq_of_mem (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (c : (Work.Cohomology.singularChains ℤ M).homology n) {K : Set M}
    (hK : IsCoordBall n M K) {x y : M} (hx : x ∈ K) (hy : y ∈ K) :
    Ind n hn M c x = Ind n hn M c y := by
  have hb₁ : ballEquiv (n := n) hn hK hx (relClass M n c K) = locClass M n c x := by
    rw [ballEquiv_apply, relClass_restrict M n c hx]
  have hb₂ : ballEquiv (n := n) hn hK hy (relClass M n c K) = locClass M n c y := by
    rw [ballEquiv_apply, relClass_restrict M n c hy]
  have h₁ : (ballEquiv (n := n) hn hK hx |>.trans (ptIso n hn M x)) (relClass M n c K)
      = ptIso n hn M x (locClass M n c x) := by
    rw [LinearEquiv.trans_apply, hb₁]
  have h₂ : (ballEquiv (n := n) hn hK hy |>.trans (ptIso n hn M y)) (relClass M n c K)
      = ptIso n hn M y (locClass M n c y) := by
    rw [LinearEquiv.trans_apply, hb₂]
  show (ptIso n hn M x (locClass M n c x)).natAbs = (ptIso n hn M y (locClass M n c y)).natAbs
  rw [← h₁, ← h₂]
  exact natAbs_eq_of_linearEquiv_int _ _ (relClass M n c K)

/-- **The index is constant** on a compact connected manifold. -/
theorem exists_Ind_eq (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (c : (Work.Cohomology.singularChains ℤ M).homology n) :
    ∃ k : ℕ, ∀ x : M, Ind n hn M c x = k := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨1, fun x => (hM.false x).elim⟩
  · haveI : PreconnectedSpace M := ConnectedSpace.toPreconnectedSpace
    obtain ⟨x₀⟩ := hM
    obtain ⟨m, K, hcover, hinner, hcpt, hne, hcb⟩ := convexCover n hn M
    have hS : IsClopen {x : M | Ind n hn M c x = Ind n hn M c x₀} := by
      constructor
      · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
        intro y hy
        obtain ⟨i, hyi⟩ := hinner y
        refine Filter.mem_of_superset (isOpen_interior.mem_nhds hyi) ?_
        intro z hz
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
        rw [Ind_eq_of_mem n hn M c (hcb i) (interior_subset hz) (interior_subset hyi)]
        exact hy
      · rw [isOpen_iff_mem_nhds]
        intro y hy
        obtain ⟨i, hyi⟩ := hinner y
        refine Filter.mem_of_superset (isOpen_interior.mem_nhds hyi) ?_
        intro z hz
        simp only [Set.mem_ofPred_eq]
        rw [Ind_eq_of_mem n hn M c (hcb i) (interior_subset hz) (interior_subset hyi)]
        exact hy
    rcases isClopen_iff.mp hS with h | h
    · have hx₀ : x₀ ∈ ({x : M | Ind n hn M c x = Ind n hn M c x₀} : Set M) := rfl
      rw [h] at hx₀
      exact absurd hx₀ (Set.notMem_empty x₀)
    · refine ⟨Ind n hn M c x₀, ?_⟩
      intro x
      have hx : x ∈ ({x : M | Ind n hn M c x = Ind n hn M c x₀} : Set M) := by
        rw [h]; trivial
      exact hx

/-- **The root of the local class at a point**: if the index is `m`, the local class is `m` times
a generator of the local group (with `m` read as an integer). -/
theorem exists_root (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (c : (Work.Cohomology.singularChains ℤ M).homology n) (m : ℕ)
    (hm : ∀ x : M, Ind n hn M c x = m) (x : M) :
    ∃ v : RelH M n ({x} : Set M), (m : ℤ) • v = locClass M n c x ∧
      Submodule.span ℤ ({v} : Set (RelH M n ({x} : Set M))) = ⊤ := by
  have hk : (ptIso n hn M x (locClass M n c x)).natAbs = m := hm x
  rcases Int.natAbs_eq_iff.mp hk with h | h
  · refine ⟨(ptIso n hn M x).symm 1, ?_, span_symm_one_eq_top _⟩
    apply (ptIso n hn M x).injective
    calc (ptIso n hn M x) ((m : ℤ) • (ptIso n hn M x).symm 1)
        = (m : ℤ) • (ptIso n hn M x) ((ptIso n hn M x).symm 1) := map_zsmul _ _ _
      _ = (m : ℤ) := by rw [LinearEquiv.apply_symm_apply]; simp
      _ = ptIso n hn M x (locClass M n c x) := h.symm
  · refine ⟨(ptIso n hn M x).symm (-1), ?_, span_symm_neg_one_eq_top _⟩
    apply (ptIso n hn M x).injective
    calc (ptIso n hn M x) ((m : ℤ) • (ptIso n hn M x).symm (-1))
        = (m : ℤ) • (ptIso n hn M x) ((ptIso n hn M x).symm (-1)) := map_zsmul _ _ _
      _ = (m : ℤ) • (-1 : ℤ) := by rw [LinearEquiv.apply_symm_apply]
      _ = -(m : ℤ) := by ring
      _ = ptIso n hn M x (locClass M n c x) := h.symm

/-! ## Two rewriting lemmas for the restrictions -/

/-- Restriction of a restriction to a point. -/
theorem relHmap_point_comp {M : TopCat} {A B : Set M} (h : A ⊆ B) {x : M} (hxA : x ∈ A)
    (hxB : x ∈ B) (a : RelH M n B) :
    RelHmap M n (Set.singleton_subset_iff.mpr hxA) (RelHmap M n h a)
      = RelHmap M n (Set.singleton_subset_iff.mpr hxB) a := by
  calc RelHmap M n (Set.singleton_subset_iff.mpr hxA) (RelHmap M n h a)
      = ((RelHmap M n (Set.singleton_subset_iff.mpr hxA)).comp (RelHmap M n h)) a := by
        rw [LinearMap.comp_apply]
    _ = RelHmap M n (Set.singleton_subset_iff.mpr (h hxA)) a := by
        rw [← RelHmap_point_fac M n h hxA]
    _ = RelHmap M n (Set.singleton_subset_iff.mpr hxB) a :=
        congrArg (fun f => f a) (RelHmap_congr_h M n
          (Set.singleton_subset_iff.mpr (h hxA)) (Set.singleton_subset_iff.mpr hxB))

/-- Composition of two restrictions. -/
theorem relHmap_comp2 {M : TopCat} {A B C : Set M} (h₁ : A ⊆ B) (h₂ : B ⊆ C)
    (u : RelH M n C) :
    RelHmap M n (h₁.trans h₂) u = RelHmap M n h₁ (RelHmap M n h₂ u) := by
  rw [← LinearMap.comp_apply, RelHmap_comp' M n h₁ h₂ (h₁.trans h₂)]

/-! ## Gluing classes over a finite cover by coordinate balls -/

/-- **Gluing**: classes on the pieces of a finite cover by coordinate balls which agree at every
point of the pairwise intersections are the restrictions of one class on the union. -/
theorem coverGlue (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {ι : Type} (s : Finset ι) (K : ι → Set M)
    (hK : ∀ i ∈ s, IsCoordBall n M (K i)) (ζ : ∀ i, RelH M n (K i))
    (hglue : ∀ i ∈ s, ∀ j ∈ s, ∀ (x : M) (hx : x ∈ K i ∩ K j),
      RelHmap M n (Set.singleton_subset_iff.mpr hx.1) (ζ i)
        = RelHmap M n (Set.singleton_subset_iff.mpr hx.2) (ζ j)) :
    ∃ γ : RelH M n (⋃ i ∈ s, K i), ∀ (i : ι) (hi : i ∈ s)
      (h : K i ⊆ ⋃ i' ∈ s, K i'), RelHmap M n h γ = ζ i := by
  classical
  have key : ∀ s : Finset ι, (∀ i ∈ s, IsCoordBall n M (K i)) →
      (∀ i ∈ s, ∀ j ∈ s, ∀ (x : M) (hx : x ∈ K i ∩ K j),
        RelHmap M n (Set.singleton_subset_iff.mpr hx.1) (ζ i)
          = RelHmap M n (Set.singleton_subset_iff.mpr hx.2) (ζ j)) →
      ∃ γ : RelH M n (⋃ i ∈ s, K i), ∀ (i : ι) (hi : i ∈ s)
        (h : K i ⊆ ⋃ i' ∈ s, K i'), RelHmap M n h γ = ζ i := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro hKs hgs
      exact ⟨0, fun i hi _ => absurd hi (Finset.notMem_empty i)⟩
    · intro a t hat ih hKs hgs
      have hKt : ∀ i ∈ t, IsCoordBall n M (K i) :=
        fun i hi => hKs i (Finset.mem_insert_of_mem hi)
      have hgt : ∀ i ∈ t, ∀ j ∈ t, ∀ (x : M) (hx : x ∈ K i ∩ K j),
          RelHmap M n (Set.singleton_subset_iff.mpr hx.1) (ζ i)
            = RelHmap M n (Set.singleton_subset_iff.mpr hx.2) (ζ j) :=
        fun i hi j hj x hx =>
          hgs i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) x hx
      obtain ⟨γt, hγt⟩ := ih hKt hgt
      rw [Finset.set_biUnion_insert]
      have hKa : IsCoordBall n M (K a) := hKs a (Finset.mem_insert_self a t)
      have hLcl : IsClosed (⋃ i ∈ t, K i) :=
        Set.Finite.isClosed_biUnion t.finite_toSet (fun i hi => (hKt i hi).isClosed)
      have hInt : IsCompact (K a ∩ ⋃ i ∈ t, K i) := (hKa.isClosed.inter hLcl).isCompact
      have hzero : IsZero ((Work.Cohomology.relChains M (K a ∩ ⋃ i ∈ t, K i)ᶜ).homology (n+1)) :=
        Work.Cohomology.relChains_vanishing_of_compact hn (K a ∩ ⋃ i ∈ t, K i) hInt (n+1)
          (by omega)
      have hagree : RelHmap M n (Set.inter_subset_left : K a ∩ ⋃ i ∈ t, K i ⊆ K a) (ζ a)
          = RelHmap M n
            (Set.inter_subset_right : K a ∩ ⋃ i ∈ t, K i ⊆ ⋃ i ∈ t, K i) γt := by
        refine sub_eq_zero.mp (compactZero n hn M hInt _ (fun x hx => ?_))
        have hxa : x ∈ K a := hx.1
        have hxL : x ∈ ⋃ i ∈ t, K i := hx.2
        obtain ⟨i, hi, hxKi⟩ := Set.mem_iUnion₂.mp hxL
        have e1 : RelHmap M n (Set.singleton_subset_iff.mpr hxa) (ζ a)
            = RelHmap M n (Set.singleton_subset_iff.mpr hxKi) (ζ i) :=
          hgs a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi) x ⟨hxa, hxKi⟩
        have e2 : RelHmap M n (Set.singleton_subset_iff.mpr hxKi) (ζ i)
            = RelHmap M n (Set.singleton_subset_iff.mpr hxL) γt := by
          calc RelHmap M n (Set.singleton_subset_iff.mpr hxKi) (ζ i)
              = RelHmap M n (Set.singleton_subset_iff.mpr hxKi)
                  (RelHmap M n (Set.subset_biUnion_of_mem hi) γt) :=
                congrArg (fun w => RelHmap M n (Set.singleton_subset_iff.mpr hxKi) w)
                  (hγt i hi (Set.subset_biUnion_of_mem hi)).symm
            _ = RelHmap M n (Set.singleton_subset_iff.mpr hxL) γt :=
                relHmap_point_comp (Set.subset_biUnion_of_mem hi) hxKi hxL γt
        have hd1 : RelHmap M n (Set.singleton_subset_iff.mpr hx)
              (RelHmap M n (Set.inter_subset_left : K a ∩ ⋃ i ∈ t, K i ⊆ K a) (ζ a))
            = RelHmap M n (Set.singleton_subset_iff.mpr hxa) (ζ a) :=
          relHmap_point_comp (Set.inter_subset_left : K a ∩ ⋃ i ∈ t, K i ⊆ K a) hx hxa (ζ a)
        have hd2 : RelHmap M n (Set.singleton_subset_iff.mpr hx)
              (RelHmap M n
                (Set.inter_subset_right : K a ∩ ⋃ i ∈ t, K i ⊆ ⋃ i ∈ t, K i) γt)
            = RelHmap M n (Set.singleton_subset_iff.mpr hxL) γt :=
          relHmap_point_comp
            (Set.inter_subset_right : K a ∩ ⋃ i ∈ t, K i ⊆ ⋃ i ∈ t, K i) hx hxL γt
        calc RelHmap M n (Set.singleton_subset_iff.mpr hx)
              (RelHmap M n (Set.inter_subset_left : K a ∩ ⋃ i ∈ t, K i ⊆ K a) (ζ a)
                - RelHmap M n
                  (Set.inter_subset_right : K a ∩ ⋃ i ∈ t, K i ⊆ ⋃ i ∈ t, K i) γt)
            = RelHmap M n (Set.singleton_subset_iff.mpr hx)
                (RelHmap M n (Set.inter_subset_left : K a ∩ ⋃ i ∈ t, K i ⊆ K a) (ζ a))
              - RelHmap M n (Set.singleton_subset_iff.mpr hx)
                (RelHmap M n
                  (Set.inter_subset_right : K a ∩ ⋃ i ∈ t, K i ⊆ ⋃ i ∈ t, K i) γt) :=
              map_sub _ _ _
          _ = RelHmap M n (Set.singleton_subset_iff.mpr hxa) (ζ a)
              - RelHmap M n (Set.singleton_subset_iff.mpr hxL) γt := by rw [hd1, hd2]
          _ = 0 := sub_eq_zero.mpr (e1.trans e2)
      obtain ⟨u, hu1, hu2⟩ := (excludedMV n M (K a) (⋃ i ∈ t, K i)
        hKa.isClosed hLcl hzero).2 (ζ a) γt hagree
      have hu1' : RelHmap M n
          (Set.subset_union_left : K a ⊆ K a ∪ ⋃ i ∈ t, K i) u = ζ a := hu1
      have hu2' : RelHmap M n
          (Set.subset_union_right : (⋃ i ∈ t, K i) ⊆ K a ∪ ⋃ i ∈ t, K i) u = γt := hu2
      refine ⟨u, ?_⟩
      intro i hi h
      rcases Finset.mem_insert.mp hi with rfl | hi
      · rw [RelHmap_congr_h M n h (Set.subset_union_left)]
        exact hu1'
      · have hKU : K i ⊆ (⋃ i' ∈ t, K i') := Set.subset_biUnion_of_mem hi
        rw [RelHmap_congr_h M n h (hKU.trans Set.subset_union_right),
          relHmap_comp2 hKU (Set.subset_union_right : (⋃ i ∈ t, K i) ⊆ K a ∪ ⋃ i ∈ t, K i) u,
          hu2']
        exact hγt i hi hKU
  exact key s hK hglue

/-! ## The localisation at the empty excluded set -/

instance isEmpty_compl_univ (M : TopCat) : IsEmpty (↥(Set.univ : Set M)ᶜ) :=
  ⟨fun x => x.2 trivial⟩

/-- **The localisation map `H_n(M) → H_n(M, M∖univ)` is injective.** -/
theorem relClass_univ_injective (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {c d : (Work.Cohomology.singularChains ℤ M).homology n}
    (h : relClass M n c (Set.univ : Set M) = relClass M n d (Set.univ : Set M)) : c = d := by
  have hZ : IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of (↥(Set.univ : Set M)ᶜ))).homology n) :=
    Work.Cohomology.isZero_homology_of_isEmpty_aux _ n
  have hex : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains M ((Set.univ : Set M)ᶜ)) n)).range =
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (cokernel.π (Work.Cohomology.inclChains M ((Set.univ : Set M)ᶜ))) n)).ker :=
    (Work.Cohomology.hPair_exact₂ M (Set.univ : Set M)ᶜ n).moduleCat_range_eq_ker
  have h0 : HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains M ((Set.univ : Set M)ᶜ)) n = 0 :=
    IsZero.eq_zero_of_src hZ _
  have hrange : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains M ((Set.univ : Set M)ᶜ)) n)).range = ⊥ := by
    rw [h0]
    exact LinearMap.range_zero
  rw [hrange] at hex
  have hinj := LinearMap.ker_eq_bot.mp hex.symm
  have hcd : c - d = 0 := by
    apply hinj
    rw [map_sub, map_zero]
    exact sub_eq_zero.mpr (show (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (cokernel.π (Work.Cohomology.inclChains M ((Set.univ : Set M)ᶜ))) n)) c
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (cokernel.π (Work.Cohomology.inclChains M ((Set.univ : Set M)ᶜ))) n)) d from h)
  exact sub_eq_zero.mp hcd

/-- **The class at the empty excluded set is nonzero** if the class is. -/
theorem relClass_univ_ne_zero (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {c : (Work.Cohomology.singularChains ℤ M).homology n} (hc : c ≠ 0) :
    relClass M n c Set.univ ≠ 0 := by
  intro h0
  refine hc (relClass_univ_injective n hn M ?_)
  rw [h0, relClass_zero]

/-- **The localisation map `H_n(M) → H_n(M, M∖univ)` is surjective.** -/
theorem relClass_univ_surjective (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    Function.Surjective (fun c : (Work.Cohomology.singularChains ℤ M).homology n =>
      relClass M n c Set.univ) := by
  have hZ : IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of (↥(Set.univ : Set M)ᶜ))).homology (n - 1)) :=
    Work.Cohomology.isZero_homology_of_isEmpty_aux _ (n - 1)
  have hδ : ModuleCat.Hom.hom (Work.Cohomology.hPairδ M ((Set.univ : Set M)ᶜ) (n - 1)) = 0 := by
    haveI : Subsingleton ↥((Work.Cohomology.singularChains ℤ
      (TopCat.of (↥(Set.univ : Set M)ᶜ))).homology (n - 1)) :=
      ModuleCat.subsingleton_of_isZero hZ
    exact Subsingleton.elim _ _
  have hex : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains M ((Set.univ : Set M)ᶜ))) (n - 1 + 1))).range =
      (ModuleCat.Hom.hom (Work.Cohomology.hPairδ M ((Set.univ : Set M)ᶜ) (n - 1))).ker :=
    (Work.Cohomology.hPair_exact₃ M (Set.univ : Set M)ᶜ (n - 1)).moduleCat_range_eq_ker
  rw [hδ, LinearMap.ker_zero] at hex
  have hnat : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [hnat] at hex
  intro y
  obtain ⟨c, hc⟩ := LinearMap.range_eq_top.mp hex y
  exact ⟨c, hc⟩

/-- Multiplication by a nonzero integer on a local group is injective (torsion freeness). -/
theorem relH_smul_injective (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) (m : ℤ)
    (hm : m ≠ 0) :
    Function.Injective (fun v : RelH M n ({x} : Set M) => m • v) := by
  intro a b h
  have hab : m • a = m • b := h
  have h2 : m • (a - b) = 0 := by
    have hsplit : m • (a - b) = m • a - m • b := by
      rw [sub_eq_add_neg, zsmul_add, zsmul_neg, sub_eq_add_neg]
    rw [hsplit, hab, sub_self]
  exact sub_eq_zero.mp (RelH_point_torsion_free n hn M x m (a - b) h2 hm)

/-! ## The main theorem -/

theorem localGeneration (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (c : (Work.Cohomology.singularChains ℤ M).homology n)
    (hgen : Submodule.span ℤ {c} = ⊤) (hc0 : c ≠ 0) :
    ∀ x : M, Submodule.span ℤ {Work.Cohomology.relLocClass M n c {x}} = ⊤ := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · intro x
    exact (hM.false x).elim
  · -- the constant index `m` and the roots
    obtain ⟨m, hm⟩ := exists_Ind_eq n hn M c
    have hroot : ∀ x : M, ∃ v : RelH M n ({x} : Set M), (m : ℤ) • v = locClass M n c x ∧
        Submodule.span ℤ ({v} : Set (RelH M n ({x} : Set M))) = ⊤ :=
      fun x => exists_root n hn M c m hm x
    let root : (x : M) → RelH M n ({x} : Set M) := fun x => Classical.choose (hroot x)
    have root_spec : ∀ x : M, (m : ℤ) • root x = locClass M n c x ∧
        Submodule.span ℤ ({root x} : Set (RelH M n ({x} : Set M))) = ⊤ :=
      fun x => Classical.choose_spec (hroot x)
    -- `m ≠ 0`
    have hm0 : m ≠ 0 := by
      intro hm0'
      have hα : ∀ x : M, locClass M n c x = 0 := by
        intro x
        have h1 : Ind n hn M c x = 0 := by rw [hm x, hm0']
        have h2 : ptIso n hn M x (locClass M n c x) = 0 := Int.natAbs_eq_zero.mp h1
        exact (ptIso n hn M x).injective (by rw [h2, map_zero])
      have hU : relClass M n c Set.univ = 0 := by
        refine compactZero n hn M isCompact_univ _ (fun x hx => ?_)
        rw [relClass_univ_restrict]
        exact hα x
      exact relClass_univ_ne_zero n hn M hc0 hU
    -- a finite cover by coordinate balls
    obtain ⟨mm, K, hcover, hinner, hcpt, hne, hcb⟩ := convexCover n hn M
    let ctr : (i : Fin mm) → M := fun i => Classical.choose (hne i)
    have hctr : ∀ i, ctr i ∈ K i := fun i => Classical.choose_spec (hne i)
    -- the root class on each piece
    have hpiece : ∀ i : Fin mm, ∃ w : RelH M n (K i),
        (∀ y (hy : y ∈ K i), RelHmap M n (Set.singleton_subset_iff.mpr hy) w = root y) ∧
        (m : ℤ) • w = relClass M n c (K i) := by
      intro i
      set w : RelH M n (K i) := (ballEquiv (n := n) hn (hcb i) (hctr i)).symm (root (ctr i)) with hw
      have hw2 : (m : ℤ) • w = relClass M n c (K i) := by
        apply (ballEquiv (n := n) hn (hcb i) (hctr i)).injective
        calc (ballEquiv (n := n) hn (hcb i) (hctr i)) ((m : ℤ) • w)
            = (m : ℤ) • (ballEquiv (n := n) hn (hcb i) (hctr i)) w := map_zsmul _ _ _
          _ = (m : ℤ) • root (ctr i) := by rw [hw, LinearEquiv.apply_symm_apply]
          _ = locClass M n c (ctr i) := (root_spec (ctr i)).1
          _ = (ballEquiv (n := n) hn (hcb i) (hctr i)) (relClass M n c (K i)) := by
              rw [ballEquiv_apply, ← relClass_restrict M n c (hctr i)]
      refine ⟨w, ?_, hw2⟩
      intro y hy
      have h2 : (m : ℤ) • (RelHmap M n (Set.singleton_subset_iff.mpr hy) w)
          = locClass M n c y := by
        calc (m : ℤ) • (RelHmap M n (Set.singleton_subset_iff.mpr hy) w)
            = RelHmap M n (Set.singleton_subset_iff.mpr hy) ((m : ℤ) • w) :=
              (map_zsmul (RelHmap M n (Set.singleton_subset_iff.mpr hy)) (m : ℤ) w).symm
          _ = RelHmap M n (Set.singleton_subset_iff.mpr hy) (relClass M n c (K i)) := by
              rw [hw2]
          _ = locClass M n c y := relClass_restrict M n c hy
      have h3 : (m : ℤ) • root y = locClass M n c y := (root_spec y).1
      exact relH_smul_injective n hn M y (m : ℤ) (by exact_mod_cast hm0) (h2.trans h3.symm)
    let ζ : (i : Fin mm) → RelH M n (K i) := fun i => Classical.choose (hpiece i)
    have ζ_spec : ∀ i, (∀ y (hy : y ∈ K i),
          RelHmap M n (Set.singleton_subset_iff.mpr hy) (ζ i) = root y) ∧
        (m : ℤ) • ζ i = relClass M n c (K i) :=
      fun i => Classical.choose_spec (hpiece i)
    -- glue the roots
    obtain ⟨γ, hγ⟩ := coverGlue n hn M (Finset.univ : Finset (Fin mm)) K
      (fun i _ => hcb i) ζ
      (fun i _ j _ x hx => by rw [(ζ_spec i).1 x hx.1, (ζ_spec j).1 x hx.2])
    -- the union is everything
    have hUnion : (⋃ i ∈ (Finset.univ : Finset (Fin mm)), K i) = Set.univ := by
      rw [show (⋃ i ∈ (Finset.univ : Finset (Fin mm)), K i) = (⋃ i, K i) from by ext x; simp]
      exact hcover
    let γU : RelH M n (Set.univ : Set M) :=
      RelHmap M n (fun x _ => by rw [hUnion]; trivial) γ
    have hγU : ∀ x : M,
        RelHmap M n (Set.singleton_subset_iff.mpr (Set.mem_univ x)) γU = root x := by
      intro x
      have hxU : x ∈ ⋃ i ∈ (Finset.univ : Finset (Fin mm)), K i := by rw [hUnion]; trivial
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxU
      have h1 : RelHmap M n (Set.singleton_subset_iff.mpr (Set.mem_univ x)) γU
          = RelHmap M n (Set.singleton_subset_iff.mpr hxU) γ := by
        have h1a : γU = RelHmap M n (fun _ _ => by rw [hUnion]; trivial) γ := rfl
        rw [h1a, (relHmap_comp2 (Set.singleton_subset_iff.mpr (Set.mem_univ x))
          (fun _ _ => by rw [hUnion]; trivial) γ).symm,
          RelHmap_congr_h M n _ (Set.singleton_subset_iff.mpr hxU)]
      have h2 : RelHmap M n (Set.singleton_subset_iff.mpr hxU) γ
          = RelHmap M n (Set.singleton_subset_iff.mpr hxi)
              (RelHmap M n (Set.subset_biUnion_of_mem hi) γ) := by
        have h2a := relHmap_comp2 (Set.singleton_subset_iff.mpr hxi)
          (Set.subset_biUnion_of_mem hi) γ
        rw [RelHmap_congr_h M n _ (Set.singleton_subset_iff.mpr hxU)] at h2a
        exact h2a
      rw [h1, h2]
      exact congrArg (fun v => RelHmap M n (Set.singleton_subset_iff.mpr hxi) v)
        (hγ i hi (Set.subset_biUnion_of_mem hi)) |>.trans ((ζ_spec i).1 x hxi)
    -- `m • γU = c`
    have hmain : (m : ℤ) • γU = relClass M n c Set.univ := by
      refine sub_eq_zero.mp (compactZero n hn M isCompact_univ _
        (fun x hx => ?_))
      rw [RelHmap_congr_h M n (Set.singleton_subset_iff.mpr hx)
        (Set.singleton_subset_iff.mpr (Set.mem_univ x))]
      calc RelHmap M n (Set.singleton_subset_iff.mpr (Set.mem_univ x))
            ((m : ℤ) • γU - relClass M n c Set.univ)
          = RelHmap M n (Set.singleton_subset_iff.mpr (Set.mem_univ x)) ((m : ℤ) • γU)
            - RelHmap M n (Set.singleton_subset_iff.mpr (Set.mem_univ x))
              (relClass M n c Set.univ) := map_sub _ _ _
        _ = (m : ℤ) • (RelHmap M n (Set.singleton_subset_iff.mpr (Set.mem_univ x)) γU)
            - RelHmap M n (Set.singleton_subset_iff.mpr (Set.mem_univ x))
              (relClass M n c Set.univ) := by
              rw [show RelHmap M n (Set.singleton_subset_iff.mpr (Set.mem_univ x)) ((m : ℤ) • γU)
                = (m : ℤ) • (RelHmap M n (Set.singleton_subset_iff.mpr (Set.mem_univ x)) γU)
                from map_zsmul _ _ _]
        _ = (m : ℤ) • root x - locClass M n c x := by
              rw [hγU x, relClass_univ_restrict M n c x]
        _ = 0 := by rw [(root_spec x).1, sub_self]
    -- `γU` is a multiple of `c`
    obtain ⟨b, hb⟩ : ∃ b : ℤ, γU = b • relClass M n c Set.univ := by
      have hf0 : Function.Surjective (fun v : (Work.Cohomology.singularChains ℤ M).homology n =>
          relClass M n v Set.univ) := relClass_univ_surjective n hn M
      let L : (Work.Cohomology.singularChains ℤ M).homology n →ₗ[ℤ] RelH M n Set.univ :=
        (HomologicalComplex.homologyMap
          (cokernel.π (Work.Cohomology.inclChains M (Set.univᶜ))) n).hom
      have hL : ∀ v, L v = relClass M n v Set.univ := fun v => rfl
      have hf : Function.Surjective L := fun y => by
        obtain ⟨v, hv⟩ := hf0 y
        exact ⟨v, by rw [hL v]; exact hv⟩
      have huniv : Submodule.map L
          (⊤ : Submodule ℤ ((Work.Cohomology.singularChains ℤ M).homology n)) = ⊤ := by
        rw [Submodule.map_top, LinearMap.range_eq_top]
        exact hf
      have hspanL : Submodule.span ℤ ({relClass M n c Set.univ} : Set (RelH M n Set.univ))
          = Submodule.map L (Submodule.span ℤ
              ({c} : Set ((Work.Cohomology.singularChains ℤ M).homology n))) := by
        rw [Submodule.map_span]
        congr 1
        rw [Set.image_singleton, hL c]
      have hspan : Submodule.span ℤ ({relClass M n c Set.univ} : Set (RelH M n Set.univ)) = ⊤ := by
        rw [hspanL, hgen, huniv]
      have hmem : γU ∈ Submodule.span ℤ ({relClass M n c Set.univ} : Set (RelH M n Set.univ)) := by
        rw [hspan]
        exact Submodule.mem_top
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hmem
      exact ⟨b, hb.symm.trans (Int.cast_smul_eq_zsmul ℤ b (relClass M n c Set.univ))⟩
    -- the algebra: evaluate `m • γU = c` and `γU = b • c` at one point
    obtain ⟨x₀⟩ := hM
    have hloc : root x₀ = (b * (m : ℤ)) • root x₀ := by
      calc root x₀ = RelHmap M n (Set.singleton_subset_iff.mpr (Set.mem_univ x₀)) γU :=
            (hγU x₀).symm
        _ = RelHmap M n (Set.singleton_subset_iff.mpr (Set.mem_univ x₀))
              (b • relClass M n c Set.univ) := by rw [hb]
        _ = b • (RelHmap M n (Set.singleton_subset_iff.mpr (Set.mem_univ x₀))
              (relClass M n c Set.univ)) :=
            (show RelHmap M n (Set.singleton_subset_iff.mpr (Set.mem_univ x₀))
                (b • relClass M n c Set.univ)
              = b • (RelHmap M n (Set.singleton_subset_iff.mpr (Set.mem_univ x₀))
                (relClass M n c Set.univ)) from map_zsmul _ _ _)
        _ = b • locClass M n c x₀ := by rw [relClass_univ_restrict M n c x₀]
        _ = b • ((m : ℤ) • root x₀) := by rw [← (root_spec x₀).1]
        _ = (b * (m : ℤ)) • root x₀ := (mul_smul b (m : ℤ) (root x₀)).symm
    have hv : root x₀ ≠ 0 :=
      ne_zero_of_span_singleton_eq_top (root_spec x₀).2 (nontrivial_relH_point n hn M x₀)
    have hb1 : b * (m : ℤ) = 1 := by
      have hlocZ : ptIso n hn M x₀ (root x₀)
          = (b * (m : ℤ)) * (ptIso n hn M x₀ (root x₀)) := by
        calc ptIso n hn M x₀ (root x₀)
            = ptIso n hn M x₀ ((b * (m : ℤ)) • root x₀) := congrArg _ hloc
          _ = (b * (m : ℤ)) • ptIso n hn M x₀ (root x₀) := map_zsmul _ _ _
          _ = (b * (m : ℤ)) * ptIso n hn M x₀ (root x₀) := by rw [smul_eq_mul]
      have hzne : ptIso n hn M x₀ (root x₀) ≠ 0 :=
        fun h0 => hv ((ptIso n hn M x₀).injective (by rw [h0, map_zero]))
      have hz0 : (1 - b * (m : ℤ)) * (ptIso n hn M x₀ (root x₀)) = 0 := by
        rw [sub_mul, one_mul, ← hlocZ, sub_self]
      rcases mul_eq_zero.mp hz0 with h | h
      · linarith
      · exact absurd h hzne
    have hm1 : m = 1 := by
      have hmb : (m : ℤ) * b = 1 := by rw [mul_comm]; exact hb1
      have h1 : ((m : ℤ)).natAbs = 1 := by
        have h2 : ((m : ℤ) * b).natAbs = 1 := by rw [hmb]; rfl
        rw [Int.natAbs_mul] at h2
        exact Nat.eq_one_of_mul_eq_one_right h2
      simpa using h1
    -- conclusion
    intro x
    have hx : locClass M n c x = root x :=
      (root_spec x).1.symm.trans (by rw [hm1, Nat.cast_one, one_zsmul])
    have h2 : Submodule.span ℤ ({locClass M n c x} : Set (RelH M n ({x} : Set M))) = ⊤ := by
      rw [hx]
      exact (root_spec x).2
    simpa only [locClass] using h2

end

end Work.ThomBordism
