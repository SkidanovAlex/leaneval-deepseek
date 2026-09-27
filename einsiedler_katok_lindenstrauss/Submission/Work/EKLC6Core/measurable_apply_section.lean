import Mathlib
import Submission.Work.EKLCompLeaf.measurable_apply_inter_isCompact
import Submission.Work.EKLCompLeaf.measurable_nu
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLContract.Defs

/-!
# Measurability of the section map of a weakly measurable family of measures

Let `κ : τ → Measure SL₃(ℝ)` be a family of measures such that

* for every compactly supported continuous `f : SL₃(ℝ) → ℝ`, the function
  `x ↦ ∫ g, f g ∂(κ x)` is measurable (weak measurability);
* every `κ x` is finite on compact sets.

Then for every measurable `T ⊆ τ × SL₃(ℝ)` the section map
`x ↦ κ x {g | (x, g) ∈ T}` is measurable — this is exactly the statement that `x ↦ κ x`
is a kernel and that the section operation preserves measurability.

## Proof

The space `SL₃(ℝ)` is σ-compact, so `Work.EKLCompLeaf.measurable_apply_inter_isCompact`
(with the cofinal cover of compact sets) yields measurability of `x ↦ κ x s` for *every*
Borel `s ⊆ SL₃(ℝ)`: `s` is the increasing union of the `s ∩ K n` (`K n` compact) and
`κ x s = ⨆ n, κ x (s ∩ K n)`.  Hence `κ` is a genuine kernel
(`MeasureTheory.Measure.measurable_of_measurable_coe`).

It remains to pass from boxes to all measurable subsets of `τ × SL₃(ℝ)`.  Fix a
measurable partition `A n` of `SL₃(ℝ)` (built from the compact cover `K0`:
`A n = K0 n \ ⋃_{m<n} K0 m`) such that `κ x (A n) < ∞` for all `x, n`.  Then each
restriction `κ.restrict (A n)` is a kernel whose values are *finite* measures, and
`Kernel.measurable_kernel_prodMk_left_of_finite` shows that
`x ↦ (κ.restrict (A n)) x (Prod.mk x ⁻¹' T)` is measurable.  Finally
`κ x (Prod.mk x ⁻¹' T) = ∑' n, (κ.restrict (A n)) x (Prod.mk x ⁻¹' T)` by countable
additivity of `κ x` along the partition, and a countable sum of measurable functions is
measurable.
-/

namespace Work.EKLC6Core

theorem measurable_apply_section {τ : Type*} [MeasurableSpace τ]
    {κ : τ → MeasureTheory.Measure Work.EKLContract.SL3}
    (hmeas : ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
      Measurable fun x => ∫ g, f g ∂(κ x))
    (hν : ∀ x : τ, MeasureTheory.IsFiniteMeasureOnCompacts (κ x))
    {T : Set (τ × Work.EKLContract.SL3)} (hT : MeasurableSet T) :
    Measurable fun x => κ x (Prod.mk x ⁻¹' T) := by
  classical
  -- ## A countable cover of `SL₃(ℝ)` by compact sets.
  obtain ⟨K0, hK0c, hK0union⟩ :=
    SigmaCompactSpace.exists_compact_covering (X := Work.EKLContract.SL3)
  -- ## A measurable partition into pieces of finite `κ x`-measure.
  set A : ℕ → Set Work.EKLContract.SL3 :=
    fun n => K0 n \ ⋃ m ∈ Finset.range n, K0 m with hAdef
  have hAmeas : ∀ n, MeasurableSet (A n) := by
    intro n
    rw [hAdef]
    exact (hK0c n).measurableSet.diff
      (Finset.measurableSet_biUnion (Finset.range n) (fun m _ => (hK0c m).measurableSet))
  have hAsub : ∀ n, A n ⊆ K0 n := by intro n; rw [hAdef]; exact Set.sdiff_subset
  have hAfin : ∀ x n, κ x (A n) < ⊤ := fun x n =>
    lt_of_le_of_lt (MeasureTheory.measure_mono (hAsub n))
      ((hν x).lt_top_of_isCompact (hK0c n))
  have hAdisj : Pairwise (Function.onFun Disjoint A) := by
    intro i j hij
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro x hxi hxj
    rw [hAdef] at hxi hxj
    rw [Set.mem_sdiff] at hxi hxj
    rcases lt_or_gt_of_ne hij with h | h
    · exact hxj.2 (Set.mem_biUnion (Finset.mem_range.mpr h) hxi.1)
    · exact hxi.2 (Set.mem_biUnion (Finset.mem_range.mpr h) hxj.1)
  have hAuniv : (⋃ n, A n) = Set.univ := by
    refine Set.eq_univ_of_forall (fun x => ?_)
    have hx : x ∈ ⋃ n, K0 n := by rw [hK0union]; trivial
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    have hpx : ∃ k, x ∈ K0 k := ⟨n, hn⟩
    refine Set.mem_iUnion.mpr ⟨Nat.find hpx, ?_⟩
    rw [hAdef, Set.mem_sdiff]
    refine ⟨Nat.find_spec hpx, fun hmem => ?_⟩
    obtain ⟨m, hm, hxm⟩ := Set.mem_iUnion₂.mp hmem
    exact Nat.find_min hpx (Finset.mem_range.mp hm) hxm
  -- ## `x ↦ κ x s` is measurable for every Borel `s`.
  have hcoemes : ∀ s : Set Work.EKLContract.SL3, MeasurableSet s →
      Measurable fun x => κ x s := by
    intro s hs
    have hunion : (⋃ n, (s ∩ A n)) = s := by
      refine le_antisymm (Set.iUnion_subset (fun n => Set.inter_subset_left))
        (fun x hx => ?_)
      have : x ∈ ⋃ n, A n := by rw [hAuniv]; trivial
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp this
      exact Set.mem_iUnion.mpr ⟨n, ⟨hx, hn⟩⟩
    have key : (fun x => κ x s) = fun x => ∑' n, κ x (s ∩ A n) := by
      funext x
      conv_lhs => rw [← hunion]
      exact MeasureTheory.measure_iUnion
        (fun i j hij => (hAdisj hij).mono Set.inter_subset_right Set.inter_subset_right)
        (fun n => hs.inter (hAmeas n))
    rw [key]
    refine Measurable.tsum (fun n => ?_)
    have hB : MeasurableSet (s ∩ A n) := hs.inter (hAmeas n)
    have h1 : Measurable fun x => κ x ((s ∩ A n) ∩ K0 n) :=
      Work.EKLCompLeaf.measurable_apply_inter_isCompact hmeas hν (hK0c n) (s ∩ A n) hB
    have h2 : (s ∩ A n) ∩ K0 n = s ∩ A n :=
      Set.inter_eq_left.mpr (Set.inter_subset_right.trans (hAsub n))
    rwa [h2] at h1
  -- ## `κ` is a kernel.
  let κk : ProbabilityTheory.Kernel τ Work.EKLContract.SL3 :=
    ⟨κ, MeasureTheory.Measure.measurable_of_measurable_coe κ hcoemes⟩
  -- ## Each restricted kernel takes finite measures.
  have hfinfun : ∀ n x,
      MeasureTheory.IsFiniteMeasure ((κk.restrict (hAmeas n)) x) := by
    intro n x
    rw [ProbabilityTheory.Kernel.restrict_apply, ProbabilityTheory.Kernel.coe_mk]
    exact ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact hAfin x n⟩
  -- ## The section mass is the sum of the masses on the pieces of the partition.
  have hkey : (fun x => κ x (Prod.mk x ⁻¹' T)) =
      fun x => ∑' n, (κk.restrict (hAmeas n)) x (Prod.mk x ⁻¹' T) := by
    funext x
    have hS : MeasurableSet (Prod.mk x ⁻¹' T) := hT.preimage measurable_prodMk_left
    have hunion : (⋃ n, (Prod.mk x ⁻¹' T ∩ A n)) = Prod.mk x ⁻¹' T := by
      refine le_antisymm (Set.iUnion_subset (fun n => Set.inter_subset_left))
        (fun g hg => ?_)
      have : g ∈ ⋃ n, A n := by rw [hAuniv]; trivial
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp this
      exact Set.mem_iUnion.mpr ⟨n, ⟨hg, hn⟩⟩
    conv_lhs => rw [← hunion]
    rw [MeasureTheory.measure_iUnion
      (fun i j hij => (hAdisj hij).mono Set.inter_subset_right Set.inter_subset_right)
      (fun n => hS.inter (hAmeas n))]
    refine tsum_congr (fun n => ?_)
    rw [ProbabilityTheory.Kernel.restrict_apply, ProbabilityTheory.Kernel.coe_mk,
      MeasureTheory.Measure.restrict_apply hS]
  rw [hkey]
  exact Measurable.tsum (fun n =>
    ProbabilityTheory.Kernel.measurable_kernel_prodMk_left_of_finite hT (hfinfun n))

end Work.EKLC6Core
