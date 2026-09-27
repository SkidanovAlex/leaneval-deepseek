import Mathlib
import Submission.Work.ManifoldParity.Defs
import Submission.Work.ManifoldParity.GraphManifold
import Submission.Work.ManifoldParity.GraphInclusion
import Submission.Work.ManifoldParity.OpensInclusion
import Submission.Work.ManifoldParity.CircleParam

/-!
# Every locally-graph compact set is a finite union of periodic smooth curves

`Work.ManifoldParity.exists_circle_parametrization`: a compact set `K ⊆ ℝⁿ` which is locally the
graph of a smooth function over some coordinate axis is a compact `1`-dimensional manifold, hence a
finite disjoint union of circles, each of which is parametrised by a periodic smooth immersion with
nowhere vanishing derivative.
-/

open scoped Manifold Topology

namespace Work.ManifoldParity

theorem exists_circle_parametrization {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K)
    (hgra : ∀ x ∈ K, ∃ (i : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
        (η : ℝ → EuclideanSpace ℝ (Fin n)),
        IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧
          (∀ t, (η t) i = 0) ∧
          ∀ y ∈ U, (y ∈ K ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i)))
    : ∃ (m : ℕ) (γ : Fin m → ℝ → EuclideanSpace ℝ (Fin n)) (T : Fin m → ℝ),
        (∀ j, 0 < T j) ∧
        (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (γ j)) ∧
        (∀ j, Function.Periodic (γ j) (T j)) ∧
        (∀ j t, fderiv ℝ (γ j) t (1:ℝ) ≠ 0) ∧
        (∀ j, ∀ a b : ℝ, γ j a = γ j b → ∃ k : ℤ, a = b + k * T j) ∧
        (K = ⋃ j, Set.range (γ j)) := by
  classical
  have hgra' : HasLocalGraphCharts K := by
    intro x hx
    obtain ⟨i, U, η, h1, h2, h3, h4, h5⟩ := hgra x hx
    exact ⟨i, U, η, ⟨h1, h3, h4, h5⟩, h2⟩
  letI : ChartedSpace ME1 ↥K := graphChartedSpace K hgra'
  haveI hgr : HasGroupoid ↥K (contDiffGroupoid ((⊤ : ℕ∞) : WithTop ℕ∞)
      (modelWithCornersSelf ℝ ME1)) := hasGroupoid_graph K hgra'
  haveI hism : IsManifold (modelWithCornersSelf ℝ ME1) ((⊤ : ℕ∞) : WithTop ℕ∞) ↥K :=
    IsManifold.mk' _ _ _
  haveI hcpt : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  have hcomp_open := isOpen_connectedComponent_graph K hgra'
  -- finitely many components
  obtain ⟨s, hs⟩ := (isCompact_univ_iff.mpr hcpt).elim_finite_subcover
    (fun x : ↥K => connectedComponent x) (fun x => hcomp_open x)
    (by intro z _; exact Set.mem_iUnion.mpr ⟨z, mem_connectedComponent⟩)
  -- a periodic parametrisation of the component of each point
  choose gam TT hprops using exists_periodic_param_component K hgra' hK
  -- enumerate the finite covering family
  let pick : Fin s.card → ↥K := fun j => ((Finset.equivFin s).symm j).1
  refine ⟨s.card, fun j t => ((gam (pick j) t : ↥K) : EuclideanSpace ℝ (Fin n)),
    fun j => TT (pick j), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- positivity of the period
    intro j
    exact (hprops (pick j)).1
  · -- smoothness
    intro j
    rw [← contMDiff_iff_contDiff]
    exact (contMDiff_subtype_val_graph K hgra').comp (hprops (pick j)).2.1
  · -- periodicity
    intro j
    exact (hprops (pick j)).2.2.1.comp _
  · -- nonvanishing derivative
    intro j t
    have hchain : mfderiv (modelWithCornersSelf ℝ ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (fun s : ℝ => ((gam (pick j) s : ↥K) : EuclideanSpace ℝ (Fin n))) t
        = (mfderiv (modelWithCornersSelf ℝ ME1) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            (Subtype.val : ↥K → EuclideanSpace ℝ (Fin n)) (gam (pick j) t)) ∘SL
          (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ME1)
            (gam (pick j)) t) :=
      mfderiv_comp t
        ((contMDiff_subtype_val_graph K hgra').contMDiffAt.mdifferentiableAt (by simp))
        ((hprops (pick j)).2.1.contMDiffAt.mdifferentiableAt (by simp))
    intro hv
    have hv' : (mfderiv (modelWithCornersSelf ℝ ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (fun s : ℝ => ((gam (pick j) s : ↥K) : EuclideanSpace ℝ (Fin n))) t) 1 = 0 := by
      rw [mfderiv_eq_fderiv]
      exact hv
    rw [hchain] at hv'
    simp only [ContinuousLinearMap.comp_apply] at hv'
    have hinner : (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ME1)
        (gam (pick j)) t) 1 = 0 :=
      mfderiv_subtype_val_injective K hgra' (gam (pick j) t) (by rw [hv', map_zero])
    exact (hprops (pick j)).2.2.2.1 t hinner
  · -- injectivity modulo the period
    intro j a b hab
    exact (hprops (pick j)).2.2.2.2.1 a b (Subtype.ext hab)
  · -- the union is `K`
    ext z
    constructor
    · intro hz
      have hzin : (⟨z, hz⟩ : ↥K) ∈ ⋃ x ∈ s, connectedComponent x := hs (Set.mem_univ _)
      simp only [Set.mem_iUnion, exists_prop] at hzin
      obtain ⟨x, hxs, hxcomp⟩ := hzin
      set j : Fin s.card := Finset.equivFin s ⟨x, hxs⟩ with hj
      have hpick : pick j = x := by
        show ((Finset.equivFin s).symm (Finset.equivFin s ⟨x, hxs⟩)).1 = x
        rw [Equiv.symm_apply_apply]
      have hmem : (⟨z, hz⟩ : ↥K) ∈ Set.range (gam x) := by
        rw [(hprops x).2.2.2.2.2]
        exact hxcomp
      obtain ⟨t, ht⟩ := hmem
      refine Set.mem_iUnion.mpr ⟨j, ⟨t, ?_⟩⟩
      show ((gam (pick j) t : ↥K) : EuclideanSpace ℝ (Fin n)) = z
      rw [hpick, ht]
    · intro hz
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
      obtain ⟨t, ht⟩ := hj
      rw [← ht]
      exact (gam (pick j) t : ↥K).2

end Work.ManifoldParity
