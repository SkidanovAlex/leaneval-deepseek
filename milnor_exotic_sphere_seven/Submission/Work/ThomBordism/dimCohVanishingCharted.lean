/-
# The cohomological dimension bound for a compact charted space

For a compact Hausdorff space `M` charted over `ℝ^N` and every degree `n > N`, the singular
cohomology `Hⁿ(M; ℤ)` vanishes: a compact `N`-dimensional manifold has cohomological dimension
`N`.

The proof covers `M` by finitely many chart sources (`N ≥ 1`), each of which is an open subset of
`M` carried by its chart onto an open subset of `ℝ^N`, so that its cohomology vanishes above `N`
(`Work.ThomBordism.singCoh_vanishing_open_subset_chart`, which uses the Euclidean dimension bound
`Work.Cohomology.euclidean_open_cohomology_vanishing`); the vanishing is then accumulated over the
finite cover by the Mayer–Vietoris step
`Work.ThomBordism.subsingleton_singCoh_biUnion`.  The case `N = 0` is the degenerate one: a
charted space over `ℝ^0` is discrete, hence — being compact — a finite discrete space, and a
singleton is contractible, so the same accumulation over the finite cover by the singletons
applies.
-/
import Mathlib
import Submission.Work.Cohomology.euclidean_open_cohomology_vanishing
import Submission.Work.Cohomology.mv_shortExact
import Submission.Work.ThomBordism.DimCohAux.Basic
import Submission.Work.ThomBordism.DimCohAux.Accum

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism

noncomputable section

/-! ## The case `N = 0`: a finite discrete space -/

/-- A charted space over `ℝ^0` is discrete. -/
theorem discreteTopology_of_charted_zero_aux (M : TopCat)
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M] : DiscreteTopology M := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro x
  have hsub : (chartAt (EuclideanSpace ℝ (Fin 0)) x).source ⊆ {x} := by
    intro y hy
    rw [Set.mem_singleton_iff]
    have h1 : (chartAt (EuclideanSpace ℝ (Fin 0)) x) y
        = (chartAt (EuclideanSpace ℝ (Fin 0)) x) x := Subsingleton.elim _ _
    exact (chartAt (EuclideanSpace ℝ (Fin 0)) x).injOn hy (mem_chart_source _ x) h1
  have heq : (chartAt (EuclideanSpace ℝ (Fin 0)) x).source = {x} :=
    Set.Subset.antisymm hsub (Set.singleton_subset_iff.mpr (mem_chart_source _ x))
  exact heq ▸ (chartAt (EuclideanSpace ℝ (Fin 0)) x).open_source

/-- **The dimension vanishing for `N = 0`.**  A compact charted space over `ℝ^0` is a finite
discrete space, so its cohomology vanishes in every positive degree. -/
theorem dimCohVanishingCharted_zero (M : TopCat) [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M] (n : ℕ) (hn : 0 < n) :
    Subsingleton ((Work.Cohomology.singularCochainComplex ℤ M).homology n) := by
  classical
  haveI hdisc : DiscreteTopology M := discreteTopology_of_charted_zero_aux M
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : M => ({x} : Set M))
    (fun x => isOpen_discrete ({x} : Set M))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, Set.mem_singleton x⟩)
  have hpiece : ∀ x : M, ∀ k, 0 < k →
      Subsingleton (singCoh (TopCat.of ↥({x} : Set M)) k) := by
    intro x k hk
    have hz := Work.Cohomology.contractible ℤ (TopCat.of ↥({x} : Set M)) (k - 1)
    rw [Nat.sub_add_cancel hk] at hz
    exact ModuleCat.subsingleton_of_isZero hz
  have hinter : ∀ (u : Finset M) (x : M), x ∉ u → ∀ k, 0 ≤ k →
      Subsingleton (singCoh (TopCat.of ↥(({x} : Set M) ∩ ⋃ j ∈ (u : Set M), {j})) k) := by
    intro u x hxu k _
    have hsub : ({x} : Set M) ∩ ⋃ j ∈ (u : Set M), {j} = (∅ : Set M) := by
      rw [show (⋃ j ∈ (u : Set M), ({j} : Set M)) = (u : Set M) by ext y; simp]
      ext y
      constructor
      · intro hy
        rw [Set.mem_inter_iff, Set.mem_singleton_iff] at hy
        exact absurd (hy.1 ▸ hy.2) hxu
      · intro hy
        exact absurd hy (by simp)
    rw [hsub]
    haveI : IsEmpty (↥(TopCat.of (∅ : Set M))) := ⟨fun y => y.2⟩
    exact ModuleCat.subsingleton_of_isZero (Work.Cohomology.isZero_homology_of_isZero_X_cochain k
      (Work.Cohomology.isZero_singularCochainComplex_of_isEmpty (TopCat.of (∅ : Set M)) k))
  have h := subsingleton_singCoh_biUnion (fun x : M => ({x} : Set M)) 0
    (fun x => isOpen_discrete ({x} : Set M)) hpiece hinter t n hn
  have hcov : (⋃ x ∈ (t : Set M), ({x} : Set M)) = (Set.univ : Set M) := by
    apply Set.eq_univ_iff_forall.mpr
    intro y
    exact ht (Set.mem_univ y)
  rw [hcov] at h
  exact subsingleton_singCoh_of_homeo (Homeomorph.Set.univ M).symm n h

/-! ## The case `N ≥ 1`: a finite cover by chart sources -/

/-- **The dimension vanishing for `N ≥ 1`.**  Cover `M` by finitely many chart sources and
accumulate the local vanishing by Mayer–Vietoris. -/
theorem dimCohVanishingCharted_pos {N : ℕ} (hN : 1 ≤ N) (M : TopCat) [CompactSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin N)) M] (n : ℕ) (hn : N < n) :
    Subsingleton ((Work.Cohomology.singularCochainComplex ℤ M).homology n) := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun z : M => (chartAt (EuclideanSpace ℝ (Fin N)) z).source)
    (fun z => (chartAt (EuclideanSpace ℝ (Fin N)) z).open_source)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, mem_chart_source (EuclideanSpace ℝ (Fin N)) x⟩)
  have hpiece : ∀ z : M, ∀ k, N < k →
      Subsingleton (singCoh (TopCat.of ↥((chartAt (EuclideanSpace ℝ (Fin N)) z).source)) k) :=
    fun z k hk => singCoh_vanishing_open_subset_chart hN z
      (chartAt (EuclideanSpace ℝ (Fin N)) z).source
      (chartAt (EuclideanSpace ℝ (Fin N)) z).open_source (fun _ hx => hx) k (le_of_lt hk)
  have hinter : ∀ (u : Finset M) (z : M), z ∉ u → ∀ k, N ≤ k →
      Subsingleton (singCoh (TopCat.of ↥((chartAt (EuclideanSpace ℝ (Fin N)) z).source
        ∩ ⋃ j ∈ (u : Set M), (chartAt (EuclideanSpace ℝ (Fin N)) j).source)) k) := by
    intro u z _ k hk
    exact singCoh_vanishing_open_subset_chart hN z _
      ((chartAt (EuclideanSpace ℝ (Fin N)) z).open_source.inter
        (isOpen_biUnion (fun j _ => (chartAt (EuclideanSpace ℝ (Fin N)) j).open_source)))
      Set.inter_subset_left k hk
  have h := subsingleton_singCoh_biUnion
    (fun z : M => (chartAt (EuclideanSpace ℝ (Fin N)) z).source) N
    (fun z => (chartAt (EuclideanSpace ℝ (Fin N)) z).open_source) hpiece hinter t n hn
  have hcov : (⋃ z ∈ (t : Set M), (chartAt (EuclideanSpace ℝ (Fin N)) z).source)
      = (Set.univ : Set M) := by
    apply Set.eq_univ_iff_forall.mpr
    intro y
    exact ht (Set.mem_univ y)
  rw [hcov] at h
  exact subsingleton_singCoh_of_homeo (Homeomorph.Set.univ M).symm n h

end

end Work.ThomBordism

namespace Work.ThomBordism

theorem dimCohVanishingCharted {N : ℕ} (M : TopCat) [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M] (n : ℕ) (hn : N < n) :
    Subsingleton ((Work.Cohomology.singularCochainComplex ℤ M).homology n) := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    exact dimCohVanishingCharted_zero M n hn
  · exact dimCohVanishingCharted_pos hN M n hn

end Work.ThomBordism
