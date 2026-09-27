import Mathlib
import Submission.Work.Whitney.DoublePoint
import Submission.Work.Noncompact.proper_immersion_transverse
import Submission.Work.Embedding.finite_double_points_of_transverse

/-!
# A proper self-transverse immersion into `ℝ^{2n}` has finite fibres and isolated double points

Let `h : M → ℝ^{2n}` be a smooth immersion (injective `mfderiv` everywhere) of a smooth `n`-manifold
`M` (Hausdorff, no boundary) whose *proper*, and whose (ordered) double points are **transverse**
(`range (mfderiv h x) ⊔ range (mfderiv h y) = ⊤` whenever `x ≠ y` and `h x = h y`).  This file
proves the three finiteness/isolation statements used by the "push the double points to infinity"
step of the non-compact Whitney embedding theorem:

1. `∀ y, (h ⁻¹' {y}).Finite` — every fibre of `h` is finite.  The fibre is compact (properness) and
   every one of its points is isolated in it (local injectivity of an immersion), so the compact set
   is finite.
2. `Work.Whitney.doubleSet h` is **discrete** (each point has an open neighbourhood meeting the
   double point set only in that point).  This is `Work.Embedding.exists_isolated_double_point`:
   transversality makes the difference map `(x,y) ↦ h x - h y` a local diffeomorphism.
3. For every compact `K ⊆ M` the set `{x | ∃ y ≠ x, h y = h x} ∩ K` of points of `K` that share a
   value with another point is finite.  Indeed `doubleSet h ∩ (K × M)` is compact (it sits inside
   `K × h ⁻¹' (h '' K)`) and discrete, hence finite, and the set in question is its image under the
   first projection.
-/

namespace Work.Noncompact

open scoped Manifold ContDiff
open Topology Set

/-- **A compact set whose points are all isolated in it is finite.**  (For a compact space this is
`Work.Embedding.finite_of_isClosed_forall_isolated` applied to the whole space; the general version
is stated for the compact set itself, viewed as a compact topological space.) -/
theorem finite_of_isCompact_forall_isolated {X : Type*} [TopologicalSpace X] {C : Set X}
    (hC : IsCompact C) (hiso : ∀ p ∈ C, ∃ U : Set X, IsOpen U ∧ p ∈ U ∧ U ∩ C ⊆ {p}) :
    C.Finite := by
  classical
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hiso' : ∀ p ∈ (Set.univ : Set C),
      ∃ W : Set C, IsOpen W ∧ p ∈ W ∧ W ∩ (Set.univ : Set C) ⊆ {p} := by
    intro p _
    obtain ⟨U, hUo, hpU, hUC⟩ := hiso p.1 p.2
    refine ⟨Subtype.val ⁻¹' U, hUo.preimage continuous_subtype_val, hpU, ?_⟩
    rintro q ⟨hqU, -⟩
    exact Subtype.ext (Set.mem_singleton_iff.mp (hUC ⟨hqU, q.2⟩))
  have hfin : (Set.univ : Set C).Finite :=
    Work.Embedding.finite_of_isClosed_forall_isolated isClosed_univ hiso'
  have h2 : (Subtype.val '' (Set.univ : Set C)).Finite := hfin.image Subtype.val
  rwa [Set.image_univ, Subtype.range_coe] at h2

/-- **Fibres of a proper immersion are finite.**  -/
theorem finite_preimage_of_isProperMap_of_injective_mfderiv {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (h : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hh : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ h) (hprop : IsProperMap h)
    (himm : ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) h x)) :
    ∀ y : EuclideanSpace ℝ (Fin (2 * n)), (h ⁻¹' {y}).Finite := by
  intro y
  have hloc := Work.Embedding.immersion_locally_injective h hh himm
  refine finite_of_isCompact_forall_isolated (hprop.isCompact_preimage isCompact_singleton) ?_
  intro x hx
  obtain ⟨U, hUo, hxU, hInj⟩ := hloc x
  refine ⟨U, hUo, hxU, ?_⟩
  rintro z ⟨hzU, hzfib⟩
  have hzy : h z = y := hzfib
  have hxy : h x = y := hx
  exact Set.mem_singleton_iff.mpr (hInj hzU hxU (by rw [hzy, hxy]))

theorem finite_preimages_and_discrete_doubleSet {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M]
    (h : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hh : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    (hprop : IsProperMap h)
    (himm : ∀ x, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) h x))
    (htr : ∀ x y, x ≠ y → h x = h y →
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) h x).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) h y).range = ⊤) :
    (∀ y : EuclideanSpace ℝ (Fin (2 * n)), (h ⁻¹' {y}).Finite) ∧
    (∀ p : M × M, p ∈ Work.Whitney.doubleSet h →
      ∃ U : Set (M × M), IsOpen U ∧ p ∈ U ∧ U ∩ Work.Whitney.doubleSet h = {p}) ∧
    (∀ K : Set M, IsCompact K →
      ({x : M | ∃ y : M, y ≠ x ∧ h y = h x} ∩ K).Finite) := by
  classical
  have hcont : Continuous h := hh.continuous
  have hloc : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ Set.InjOn h U :=
    Work.Embedding.immersion_locally_injective h hh himm
  have hclosedD : IsClosed (Work.Whitney.doubleSet h) :=
    Work.Embedding.isClosed_doubleSet_of_locallyInjective h hcont hloc
  -- the double point set is discrete: transversality isolates every double point
  have hdiscr : ∀ p : M × M, p ∈ Work.Whitney.doubleSet h →
      ∃ U : Set (M × M), IsOpen U ∧ p ∈ U ∧ U ∩ Work.Whitney.doubleSet h = {p} := by
    intro p hp
    obtain ⟨U, V, hUo, hVo, hxU, hyV, -, hmain⟩ :=
      Work.Embedding.exists_isolated_double_point h hh hp.1 hp.2 (htr p.1 p.2 hp.1 hp.2)
    refine ⟨U ×ˢ V, hUo.prod hVo, ⟨hxU, hyV⟩, ?_⟩
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨⟨hxU, hyV⟩, hp⟩, ?_⟩
    rintro q ⟨⟨hqU, hqV⟩, hqD⟩
    exact Prod.ext (hmain q.1 hqU q.2 hqV hqD.2).1 (hmain q.1 hqU q.2 hqV hqD.2).2
  refine ⟨finite_preimage_of_isProperMap_of_injective_mfderiv h hh hprop himm, hdiscr, ?_⟩
  -- points of a compact set sharing a value with another point
  intro K hK
  have hKc : IsCompact (K ×ˢ (h ⁻¹' (h '' K))) :=
    hK.prod (hprop.isCompact_preimage (hK.image hcont))
  have hsub : Work.Whitney.doubleSet h ∩ (K ×ˢ (Set.univ : Set M)) ⊆
      K ×ˢ (h ⁻¹' (h '' K)) := by
    rintro p ⟨hpD, hpK, -⟩
    refine ⟨hpK, ?_⟩
    exact ⟨p.1, hpK, hpD.2⟩
  have hcl : IsClosed (Work.Whitney.doubleSet h ∩ (K ×ˢ (Set.univ : Set M))) :=
    hclosedD.inter (hK.isClosed.prod isClosed_univ)
  have hcomp : IsCompact (Work.Whitney.doubleSet h ∩ (K ×ˢ (Set.univ : Set M))) :=
    hKc.of_isClosed_subset hcl hsub
  have hfinC : (Work.Whitney.doubleSet h ∩ (K ×ˢ (Set.univ : Set M))).Finite := by
    refine finite_of_isCompact_forall_isolated hcomp fun p hp => ?_
    obtain ⟨U, hUo, hpU, hUsing⟩ := hdiscr p hp.1
    exact ⟨U, hUo, hpU, fun q hq => by
      have : q ∈ U ∩ Work.Whitney.doubleSet h := ⟨hq.1, hq.2.1⟩
      rwa [hUsing] at this⟩
  have hset : (fun p : M × M => p.1) '' (Work.Whitney.doubleSet h ∩ (K ×ˢ (Set.univ : Set M)))
      = ({x : M | ∃ y : M, y ≠ x ∧ h y = h x} ∩ K) := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p.2, hp.1.1.symm, hp.1.2.symm⟩, hp.2.1⟩
    · rintro ⟨⟨y, hyx, hyh⟩, hxK⟩
      exact ⟨(x, y), ⟨⟨hyx.symm, hyh.symm⟩, hxK, trivial⟩, rfl⟩
  rw [← hset]
  exact hfinC.image _

end Work.Noncompact
