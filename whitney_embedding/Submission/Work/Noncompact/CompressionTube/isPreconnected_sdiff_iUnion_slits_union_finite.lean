import Mathlib
import Submission.Work.Noncompact.CompressionTube.spike_removal_finite
import Submission.Work.Whitney.PathTools.isPathConnected_sdiff_finite_of_isOpen

/-!
# Removing finitely many free-ended slits and a finite set

`spike_removal_finite` removes finitely many pairwise disjoint "slits with a free end"
`σ j '' Ioc 0 1 ⊆ C` (with `σ j 0 ∉ C`) from an open preconnected `C` of an `n`-manifold, `n ≥ 2`.
Here the same statement is combined with the removal of a *finite set* `F ⊆ C`
(`Work.Whitney.PathTools.isPathConnected_sdiff_finite_of_isOpen`), which is the form in which the
level step of the spine recursion consumes it: `C` is the routing carrier, the slits are the other
strands' spikes, and `F` the finite avoid set.
-/

set_option linter.unusedSectionVars false

namespace Work.Noncompact.CompressionTube

open Set Topology

/-- **Finitely many free-ended slits and a finite set do not disconnect.** -/
theorem isPreconnected_sdiff_iUnion_slits_union_finite {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {C : Set M} (hC : IsOpen C) (hCc : IsPreconnected C)
    {k : ℕ} {σ : Fin k → ℝ → M} (hσc : ∀ j, Continuous (σ j))
    (hσinj : ∀ j, Set.InjOn (σ j) (Set.Icc (0:ℝ) 1))
    (hσC : ∀ j, σ j '' Set.Ioc (0:ℝ) 1 ⊆ C) (hσ0 : ∀ j, σ j 0 ∉ C)
    (hdisj : ∀ j j', j ≠ j' → Disjoint (σ j '' Set.Icc (0:ℝ) 1) (σ j' '' Set.Icc (0:ℝ) 1))
    {F : Set M} (hF : F.Finite) (hFC : F ⊆ C) :
    IsPreconnected (C \ ((⋃ j, σ j '' Set.Ioc (0:ℝ) 1) ∪ F)) := by
  classical
  haveI : LocallyPathConnectedSpace M :=
    Work.Whitney.PathTools.locallyPathConnectedSpace_chartedSpace (n := n)
  have hspike : IsPreconnected (C \ ⋃ j, σ j '' Set.Ioc (0:ℝ) 1) :=
    spike_removal_finite hn hC hCc hσc hσinj hσC hσ0 hdisj
  have hopen : IsOpen (C \ ⋃ j, σ j '' Set.Ioc (0:ℝ) 1) := by
    rw [sdiff_iUnion_Ioc_eq_sdiff_iUnion_Icc (C := C) (σ := σ) hσ0]
    exact hC.sdiff (isCompact_iUnion fun j => isCompact_Icc.image (hσc j)).isClosed
  by_cases hne : (C \ ⋃ j, σ j '' Set.Ioc (0:ℝ) 1).Nonempty
  · have hpc : IsPathConnected (C \ ⋃ j, σ j '' Set.Ioc (0:ℝ) 1) :=
      hopen.isConnected_iff_isPathConnected.mp ⟨hne, hspike⟩
    have hfin : (F ∩ (C \ ⋃ j, σ j '' Set.Ioc (0:ℝ) 1)).Finite := hF.inter_of_left _
    have hres := Work.Whitney.PathTools.isPathConnected_sdiff_finite_of_isOpen hn hopen hpc
      hfin inter_subset_right
    have heq : (C \ ⋃ j, σ j '' Set.Ioc (0:ℝ) 1) \
          (F ∩ (C \ ⋃ j, σ j '' Set.Ioc (0:ℝ) 1))
        = C \ ((⋃ j, σ j '' Set.Ioc (0:ℝ) 1) ∪ F) := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_union, Set.mem_iUnion]
      tauto
    rw [heq] at hres
    exact hres.isConnected.isPreconnected
  · have hsub : C ⊆ ⋃ j, σ j '' Set.Ioc (0:ℝ) 1 :=
      Set.sdiff_eq_empty.mp (Set.not_nonempty_iff_eq_empty.mp hne)
    have hempty : C \ ((⋃ j, σ j '' Set.Ioc (0:ℝ) 1) ∪ F) = ∅ :=
      Set.sdiff_eq_empty.mpr (hsub.trans Set.subset_union_left)
    rw [hempty]
    exact isPreconnected_empty

end Work.Noncompact.CompressionTube
