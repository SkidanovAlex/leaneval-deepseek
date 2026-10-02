import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.ThomBordism.localGeneration
import Submission.Work.Stems.HurewiczSphere
import Submission.Work.Tubular.convexLocalIso_free

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A coherent family of local generators on Euclidean space

`Work.Tubular.exists_halfOrientationFamily_euclidean`: for `N ≥ 1`, Euclidean space `ℝ^N` carries a
family `γ y ∈ H_N(ℝ^N, ℝ^N∖{y})` of generators of the local groups which is *coherent*: for every
compact `K ⊆ ℝ^N` there is a class `a ∈ H_N(ℝ^N, ℝ^N∖K)` whose localisation at every point of `K`
is `γ y`.

This is the flat model of an orientation, in the "all compact sets" form used when orienting chart
domains of a manifold.

## The construction

`ℝ^N` is charted over itself, with `chartAt _ z = OpenPartialHomeomorph.refl`, so the closed balls
`B k = {‖y‖ ≤ k+1}` are coordinate balls (`IsCoordBall`).  The key input is that the localisation
out of a coordinate ball is an isomorphism (`Work.Tubular.convexLocalIso_free`, the
compactness-free form of `Work.ThomBordism.convexLocalIso`):

  `H_N(ℝ^N, ℝ^N∖B) → H_N(ℝ^N, ℝ^N∖{x})`,   `x ∈ B`,

which is an isomorphism.  Consequences, `B` a coordinate ball:

* *existence*: lifting a fixed generator `g ∈ H_N(ℝ^N, ℝ^N∖{0})` along the isomorphism at `0` gives
  a class `a_k` over `B k` whose localisation at **every** `y ∈ B k` is a generator (an isomorphism
  carries generators to generators);
* *compatibility*: for `B ⊆ B'` the classes `a_k`, `a_{k'}` are the *canonical* lifts of the same
  `g`, so restricting `a_{k'}` to `B k` and applying the (injective) localisation at `0` shows
  `a_{k'}|_{B k} = a_k` — no orientation sign has to be adjusted.

The family is `γ y = ` localisation of `a_{k(y)}` at `y` for any `k(y)` with `y ∈ B k(y)`;
well-definedness is the compatibility above, and the coherence over an arbitrary compact `K` is
obtained by taking `k` with `K ⊆ B k` and restricting `a_k`.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.Tubular

noncomputable section

/-! ## Two elementary facts about generators over `ℤ` -/

/-- The image of a generator under a surjective `ℤ`-linear map generates. -/
theorem span_singleton_eq_top_of_surjective {A B : Type*} [AddCommGroup A] [Module ℤ A]
    [AddCommGroup B] [Module ℤ B] (φ : A →ₗ[ℤ] B) (hφ : Function.Surjective φ) (v : A)
    (hv : Submodule.span ℤ ({v} : Set A) = ⊤) :
    Submodule.span ℤ ({φ v} : Set B) = ⊤ := by
  have h : Submodule.span ℤ ({φ v} : Set B) = Submodule.map φ (Submodule.span ℤ ({v} : Set A)) := by
    rw [Submodule.map_span]
    congr 1
    ext x
    constructor
    · intro hx
      exact ⟨v, Set.mem_singleton_iff.mpr rfl, (Set.mem_singleton_iff.mp hx).symm⟩
    · rintro ⟨y, hy, rfl⟩
      rw [Set.mem_singleton_iff.mp hy]
      exact Set.mem_singleton_iff.mpr rfl
  rw [h, hv, Submodule.map_top, LinearMap.range_eq_top.mpr hφ]

/-- `1` generates `ℤ`. -/
theorem span_one_int : Submodule.span ℤ ({(1 : ℤ)} : Set ℤ) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro m
  exact Submodule.mem_span_singleton.mpr ⟨m, by simp⟩


/-! ## The family of local generators of Euclidean space -/

/-- **A coherent family of local generators of `ℝ^N`** (`N ≥ 1`): a family `γ y` of generators of
the local groups together with, for every compact `K`, a class of `H_N(ℝ^N, ℝ^N∖K)` whose
localisation at every `y ∈ K` is `γ y`. -/
theorem exists_halfOrientationFamily_euclidean (N : ℕ) (hN : 1 ≤ N) :
    ∃ γ : ∀ y : EuclideanSpace ℝ (Fin N),
        Work.Orient.LocH (TopCat.of (EuclideanSpace ℝ (Fin N))) N y,
      (∀ y, Submodule.span ℤ ({γ y} :
          Set (Work.Orient.LocH (TopCat.of (EuclideanSpace ℝ (Fin N))) N y)) = ⊤) ∧
      ∀ K : Set (EuclideanSpace ℝ (Fin N)), IsCompact K →
        ∃ a : Work.Orient.RelH (TopCat.of (EuclideanSpace ℝ (Fin N))) N K,
          ∀ (y : EuclideanSpace ℝ (Fin N)) (hy : y ∈ K),
            Work.Orient.resRelH (TopCat.of (EuclideanSpace ℝ (Fin N))) N
              (Set.singleton_subset_iff.mpr hy) a = γ y := by
  classical
  let M : TopCat := TopCat.of (EuclideanSpace ℝ (Fin N))
  let B : ℕ → Set M := fun k =>
    (chartAt (EuclideanSpace ℝ (Fin N)) (0 : EuclideanSpace ℝ (Fin N))) ⁻¹'
        Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin N)) (0 : EuclideanSpace ℝ (Fin N))) 0)
          ((2 * ((k : ℝ) + 1)) / 2)
      ∩ (chartAt (EuclideanSpace ℝ (Fin N)) (0 : EuclideanSpace ℝ (Fin N))).source
  have hBcoord : ∀ k : ℕ, Work.ThomBordism.IsCoordBall N M (B k) := by
    intro k
    exact ⟨0, 2 * ((k : ℝ) + 1), by positivity, Set.subset_univ _, rfl⟩
  have memB : ∀ (k : ℕ) (y : EuclideanSpace ℝ (Fin N)),
      y ∈ B k ↔ dist y 0 ≤ (2 * ((k : ℝ) + 1)) / 2 := by
    intro k y
    simp only [B, chartAt_self_eq, OpenPartialHomeomorph.refl_source, Set.inter_univ,
      OpenPartialHomeomorph.refl_apply, Set.mem_preimage, Metric.mem_closedBall]
    exact Iff.rfl
  have h0B : ∀ k : ℕ, (0 : EuclideanSpace ℝ (Fin N)) ∈ B k := by
    intro k
    rw [memB]
    simp only [dist_self]
    positivity
  have hBsub : ∀ {k k' : ℕ}, k ≤ k' → B k ⊆ B k' := by
    intro k k' hle y hy
    simp only [memB] at hy ⊢
    have hk : (k : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hle
    linarith
  have hiso : ∀ k : ℕ, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap M (B k)ᶜ ({0} : Set M)ᶜ
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr (h0B k)))) N) := by
    intro k
    exact convexLocalIso_free N hN M (0 : EuclideanSpace ℝ (Fin N)) (2 * ((k : ℝ) + 1))
      (by positivity) (by simp) (0 : EuclideanSpace ℝ (Fin N)) (h0B k)
  have hbij0 : ∀ k : ℕ, Function.Bijective (Work.ThomBordism.RelHmap M N
      (Set.singleton_subset_iff.mpr (h0B k))) := by
    intro k
    haveI := hiso k
    exact ⟨(ModuleCat.mono_iff_injective _).mp inferInstance,
      (ModuleCat.epi_iff_surjective _).mp inferInstance⟩
  let L : ∀ k : ℕ, Work.ThomBordism.RelH M N (B k) ≃ₗ[ℤ]
      Work.ThomBordism.RelH M N ({0} : Set M) :=
    fun k => LinearEquiv.ofBijective (Work.ThomBordism.RelHmap M N
      (Set.singleton_subset_iff.mpr (h0B k))) (hbij0 k)
  obtain ⟨E0⟩ := Work.Cohomology.localHomology N hN (EuclideanSpace ℝ (Fin N)) 0
  let g : Work.ThomBordism.RelH M N ({0} : Set M) := ModuleCat.Hom.hom E0.inv 1
  have hg : Submodule.span ℤ ({g} : Set (Work.ThomBordism.RelH M N ({0} : Set M))) = ⊤ := by
    have hsurj : Function.Surjective (ModuleCat.Hom.hom E0.inv) :=
      (ModuleCat.epi_iff_surjective E0.inv).mp inferInstance
    have h1 := span_singleton_eq_top_of_surjective (ModuleCat.Hom.hom E0.inv) hsurj (1 : ℤ)
      span_one_int
    simpa only [g] using h1
  let a : ∀ k : ℕ, Work.ThomBordism.RelH M N (B k) := fun k => (L k).symm g
  have a_spec : ∀ k : ℕ, Work.ThomBordism.RelHmap M N
      (Set.singleton_subset_iff.mpr (h0B k)) (a k) = g := by
    intro k
    exact (L k).apply_symm_apply g
  have gen_loc : ∀ (k : ℕ) (y : EuclideanSpace ℝ (Fin N)) (hy : y ∈ B k),
      Submodule.span ℤ ({(Work.ThomBordism.RelHmap M N
        (Set.singleton_subset_iff.mpr hy) (a k))} :
        Set (Work.ThomBordism.RelH M N ({y} : Set M))) = ⊤ := by
    intro k y hy
    have hisoy : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relCokerMap M (B k)ᶜ ({y} : Set M)ᶜ
          (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy))) N) :=
      convexLocalIso_free N hN M (0 : EuclideanSpace ℝ (Fin N)) (2 * ((k : ℝ) + 1))
        (by positivity) (by simp) y hy
    have hsurj1 : Function.Surjective (Work.ThomBordism.RelHmap M N
        (Set.singleton_subset_iff.mpr hy)) := by
      haveI := hisoy
      exact (ModuleCat.epi_iff_surjective _).mp inferInstance
    have hsurjL : Function.Surjective ((L k).symm : Work.ThomBordism.RelH M N ({0} : Set M) →ₗ[ℤ]
        Work.ThomBordism.RelH M N (B k)) := (L k).symm.surjective
    have hcomp : Function.Surjective ((Work.ThomBordism.RelHmap M N
        (Set.singleton_subset_iff.mpr hy)).comp
        ((L k).symm : Work.ThomBordism.RelH M N ({0} : Set M) →ₗ[ℤ]
          Work.ThomBordism.RelH M N (B k))) := hsurj1.comp hsurjL
    have h := span_singleton_eq_top_of_surjective _ hcomp g hg
    have hval : ((Work.ThomBordism.RelHmap M N (Set.singleton_subset_iff.mpr hy)).comp
        ((L k).symm : Work.ThomBordism.RelH M N ({0} : Set M) →ₗ[ℤ]
          Work.ThomBordism.RelH M N (B k))) g
        = Work.ThomBordism.RelHmap M N (Set.singleton_subset_iff.mpr hy) (a k) := by
      simp only [LinearMap.comp_apply]
      rfl
    rwa [hval] at h
  have compat : ∀ {k k' : ℕ} (hle : k ≤ k') (hBB : B k ⊆ B k'),
      Work.ThomBordism.RelHmap M N hBB (a k') = a k := by
    intro k k' hle hBB
    apply (hbij0 k).1
    have h1 : Work.ThomBordism.RelHmap M N (Set.singleton_subset_iff.mpr (h0B k))
        (Work.ThomBordism.RelHmap M N hBB (a k'))
        = Work.ThomBordism.RelHmap M N (Set.singleton_subset_iff.mpr (h0B k')) (a k') := by
      rw [← LinearMap.comp_apply, Work.ThomBordism.RelHmap_comp' M N
        (Set.singleton_subset_iff.mpr (h0B k)) hBB (Set.singleton_subset_iff.mpr (h0B k'))]
    rw [h1, a_spec k', a_spec k]
  have hmem : ∀ y : EuclideanSpace ℝ (Fin N), ∃ k : ℕ, y ∈ B k := by
    intro y
    refine ⟨⌈‖y‖⌉₊, ?_⟩
    rw [memB]
    have h1 : ‖y‖ ≤ ((⌈‖y‖⌉₊ : ℕ) : ℝ) := Nat.le_ceil ‖y‖
    have h2 : dist y 0 = ‖y‖ := by rw [dist_eq_norm, sub_zero]
    rw [h2]
    linarith
  let kOf : EuclideanSpace ℝ (Fin N) → ℕ := fun y => Classical.choose (hmem y)
  have hkOf : ∀ y : EuclideanSpace ℝ (Fin N), y ∈ B (kOf y) :=
    fun y => Classical.choose_spec (hmem y)
  let γ : ∀ y : EuclideanSpace ℝ (Fin N), Work.Orient.LocH M N y :=
    fun y => Work.ThomBordism.RelHmap M N (Set.singleton_subset_iff.mpr (hkOf y)) (a (kOf y))
  have γ_eq : ∀ (k : ℕ) (y : EuclideanSpace ℝ (Fin N)) (hy : y ∈ B k),
      Work.ThomBordism.RelHmap M N (Set.singleton_subset_iff.mpr hy) (a k) = γ y := by
    intro k y hy
    rcases le_total k (kOf y) with hle | hle
    · have hBB : B k ⊆ B (kOf y) := hBsub hle
      have hpf := Work.ThomBordism.RelHmap_point_fac M N hBB hy
      have step1 : Work.ThomBordism.RelHmap M N (Set.singleton_subset_iff.mpr hy) (a k)
          = Work.ThomBordism.RelHmap M N (Set.singleton_subset_iff.mpr hy)
              (Work.ThomBordism.RelHmap M N hBB (a (kOf y))) := by
        rw [compat hle hBB]
      have step2 : Work.ThomBordism.RelHmap M N (Set.singleton_subset_iff.mpr hy)
              (Work.ThomBordism.RelHmap M N hBB (a (kOf y)))
          = Work.ThomBordism.RelHmap M N (Set.singleton_subset_iff.mpr (hBB hy))
              (a (kOf y)) :=
        ((LinearMap.comp_apply _ _ _).symm).trans
          (LinearMap.congr_fun hpf.symm (a (kOf y)))
      have step3 : Work.ThomBordism.RelHmap M N
              (Set.singleton_subset_iff.mpr (hBB hy)) (a (kOf y))
          = Work.ThomBordism.RelHmap M N
              (Set.singleton_subset_iff.mpr (hkOf y)) (a (kOf y)) :=
        LinearMap.congr_fun (Work.ThomBordism.RelHmap_congr_h M N
          (Set.singleton_subset_iff.mpr (hBB hy))
          (Set.singleton_subset_iff.mpr (hkOf y))) (a (kOf y))
      exact step1.trans (step2.trans (step3.trans rfl))
    · have hBB : B (kOf y) ⊆ B k := hBsub hle
      have hA : Work.ThomBordism.RelHmap M N (Set.singleton_subset_iff.mpr hy) (a k)
          = Work.ThomBordism.RelHmap M N
              (Set.singleton_subset_iff.mpr (hBB (hkOf y))) (a k) :=
        LinearMap.congr_fun (Work.ThomBordism.RelHmap_congr_h M N
          (Set.singleton_subset_iff.mpr hy)
          (Set.singleton_subset_iff.mpr (hBB (hkOf y)))) (a k)
      have hB : Work.ThomBordism.RelHmap M N
              (Set.singleton_subset_iff.mpr (hBB (hkOf y))) (a k)
          = Work.ThomBordism.RelHmap M N (Set.singleton_subset_iff.mpr (hkOf y))
              (Work.ThomBordism.RelHmap M N hBB (a k)) :=
        (LinearMap.congr_fun (Work.ThomBordism.RelHmap_point_fac M N hBB (hkOf y)) (a k)).trans
          (LinearMap.comp_apply _ _ _)
      have hC : Work.ThomBordism.RelHmap M N (Set.singleton_subset_iff.mpr (hkOf y))
              (Work.ThomBordism.RelHmap M N hBB (a k))
          = Work.ThomBordism.RelHmap M N (Set.singleton_subset_iff.mpr (hkOf y)) (a (kOf y)) := by
        rw [compat hle hBB]
      exact hA.trans (hB.trans (hC.trans rfl))
  refine ⟨γ, ?_, ?_⟩
  · intro y
    change Submodule.span ℤ ({(Work.ThomBordism.RelHmap M N
      (Set.singleton_subset_iff.mpr (hkOf y)) (a (kOf y)))} :
      Set (Work.ThomBordism.RelH M N ({y} : Set M))) = ⊤
    exact gen_loc (kOf y) y (hkOf y)
  · intro K hK
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin N))
    obtain ⟨k, hk⟩ : ∃ k : ℕ, R ≤ ((k : ℕ) : ℝ) + 1 :=
      ⟨⌈R⌉₊, by have := Nat.le_ceil R; linarith⟩
    have hKB : K ⊆ B k := by
      intro y hy
      rw [memB]
      have h1 : dist y 0 ≤ R := by
        have := hR hy
        rwa [Metric.mem_closedBall] at this
      linarith
    refine ⟨Work.ThomBordism.RelHmap M N hKB (a k), ?_⟩
    intro y hy
    change Work.ThomBordism.RelHmap M N (Set.singleton_subset_iff.mpr hy)
        (Work.ThomBordism.RelHmap M N hKB (a k)) = γ y
    rw [← LinearMap.comp_apply, ← Work.ThomBordism.RelHmap_point_fac M N hKB hy]
    exact γ_eq k y (hKB hy)

end

end Work.Tubular
