import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

set_option linter.style.haveILetI false

namespace Commons.Topology.Metric

open Filter Set

/-- An equicontinuous family with a uniform Hölder-type bound `dist (f i x) (f i y) ≤ M * √(dist x y)`
(with `0 ≤ M`) is equicontinuous. -/
lemma equicontinuous_of_dist_bound {X : Type*} [PseudoMetricSpace X] {E : Type*} [PseudoMetricSpace E]
    {ι : Type*} {f : ι → X → E} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ i (x y : X), dist (f i x) (f i y) ≤ M * Real.sqrt (dist x y)) :
    Equicontinuous f := by
  intro x₀
  rw [_root_.Metric.equicontinuousAt_iff]
  intro ε hε
  have hM1 : (0 : ℝ) < M + 1 := by linarith
  have hc : 0 < ε / (M + 1) := div_pos hε hM1
  refine ⟨min 1 ((ε / (M + 1)) ^ 2), lt_min one_pos (pow_pos hc 2), ?_⟩
  intro x hx i
  rw [dist_comm] at hx
  have hsqrt : Real.sqrt (min 1 ((ε / (M + 1)) ^ 2)) ≤ ε / (M + 1) := by
    calc Real.sqrt (min 1 ((ε / (M + 1)) ^ 2))
        ≤ Real.sqrt ((ε / (M + 1)) ^ 2) := Real.sqrt_le_sqrt (min_le_right _ _)
      _ = ε / (M + 1) := Real.sqrt_sq hc.le
  have hbound : M * Real.sqrt (dist x₀ x) ≤ M * (ε / (M + 1)) :=
    mul_le_mul_of_nonneg_left ((Real.sqrt_le_sqrt (le_of_lt hx)).trans hsqrt) hM
  have hratio : M / (M + 1) < 1 := by
    rw [div_lt_one hM1]; linarith
  have hlast : M * (ε / (M + 1)) < ε := by
    calc M * (ε / (M + 1)) = ε * (M / (M + 1)) := by ring
      _ < ε * 1 := mul_lt_mul_of_pos_left hratio hε
      _ = ε := by ring
  exact lt_of_le_of_lt ((h i x₀ x).trans hbound) hlast

theorem exists_tendstoUniformlyOn_subseq_of_holder_of_properSpace {E : Type*}
    [PseudoMetricSpace E] [CompleteSpace E] [ProperSpace E] {F : ℕ → ℝ → E} {M a b : ℝ}
    (hab : a ≤ b) (hM : 0 ≤ M)
    (hcont : ∀ n, ContinuousOn (F n) (Set.Icc a b))
    (hholder : ∀ n (s : ℝ), s ∈ Set.Icc a b → ∀ t ∈ Set.Icc a b,
      dist (F n s) (F n t) ≤ M * Real.sqrt |s - t|)
    (hbd : ∃ x₀ : E, ∀ n, F n a = x₀) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℝ → E, ContinuousOn g (Set.Icc a b) ∧
      TendstoUniformlyOn (fun k => F (φ k)) g atTop (Set.Icc a b) := by
  obtain ⟨x₀, hx₀⟩ := hbd
  have ha : a ∈ Set.Icc a b := left_mem_Icc.mpr hab
  haveI : CompactSpace ↥(Set.Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  set R : ℝ := M * Real.sqrt (b - a) with hR
  -- Every value `F n s` lies in the closed ball of radius `R` around `x₀`.
  have hball : ∀ n (x : ↥(Set.Icc a b)), dist (F n (x : ℝ)) x₀ ≤ R := by
    intro n x
    have hx : (x : ℝ) ∈ Set.Icc a b := x.property
    rw [← hx₀ n, hR]
    calc dist (F n (x : ℝ)) (F n a)
        ≤ M * Real.sqrt |(x : ℝ) - a| := hholder n (x : ℝ) hx a ha
      _ ≤ M * Real.sqrt (b - a) := by
          refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hM
          rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
          exact sub_le_sub_right hx.2 a
  -- Package the functions as bounded continuous functions on the compact interval.
  let G : ℕ → BoundedContinuousFunction ↥(Set.Icc a b) E := fun n =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun x => F n (x : ℝ), (continuousOn_iff_continuous_domRestrict).mp (hcont n)⟩
  have G_apply : ∀ n (x : ↥(Set.Icc a b)), G n x = F n (x : ℝ) := fun n x =>
    BoundedContinuousFunction.mkOfCompact_apply _ _
  have hcont_eval : ∀ x : ↥(Set.Icc a b),
      Continuous fun f : BoundedContinuousFunction ↥(Set.Icc a b) E => f x :=
    fun x => (continuous_apply x).comp BoundedContinuousFunction.continuous_coe
  -- The closed set of bounded continuous functions with values in the closed ball ...
  have hS1 : IsClosed (⋂ x : ↥(Set.Icc a b),
      {f : BoundedContinuousFunction ↥(Set.Icc a b) E | f x ∈ Metric.closedBall x₀ R}) :=
    isClosed_iInter fun x => Metric.isClosed_closedBall.preimage (hcont_eval x)
  -- ... and the closed set satisfying the uniform Hölder bound.
  have hS2 : IsClosed (⋂ x : ↥(Set.Icc a b), ⋂ y : ↥(Set.Icc a b),
      {f : BoundedContinuousFunction ↥(Set.Icc a b) E |
        dist (f x) (f y) ≤ M * Real.sqrt (dist x y)}) :=
    isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le ((hcont_eval x).dist (hcont_eval y)) continuous_const
  have hG1 : ∀ n, G n ∈ (⋂ x : ↥(Set.Icc a b),
      {f : BoundedContinuousFunction ↥(Set.Icc a b) E | f x ∈ Metric.closedBall x₀ R}) := by
    intro n
    rw [Set.mem_iInter]
    intro x
    simpa only [Set.mem_ofPred_eq, G_apply, Metric.mem_closedBall] using hball n x
  have hG2 : ∀ n, G n ∈ (⋂ x : ↥(Set.Icc a b), ⋂ y : ↥(Set.Icc a b),
      {f : BoundedContinuousFunction ↥(Set.Icc a b) E |
        dist (f x) (f y) ≤ M * Real.sqrt (dist x y)}) := by
    intro n
    rw [Set.mem_iInter]
    intro x
    rw [Set.mem_iInter]
    intro y
    show dist ((G n) x) ((G n) y) ≤ M * Real.sqrt (dist x y)
    rw [G_apply, G_apply, Subtype.dist_eq, Real.dist_eq]
    exact hholder n (x : ℝ) x.property (y : ℝ) y.property
  -- Arzelà–Ascoli: the intersection is compact.
  have hcpt : IsCompact ((⋂ x : ↥(Set.Icc a b),
        {f : BoundedContinuousFunction ↥(Set.Icc a b) E | f x ∈ Metric.closedBall x₀ R}) ∩
      (⋂ x : ↥(Set.Icc a b), ⋂ y : ↥(Set.Icc a b),
        {f : BoundedContinuousFunction ↥(Set.Icc a b) E |
          dist (f x) (f y) ≤ M * Real.sqrt (dist x y)})) :=
    BoundedContinuousFunction.arzela_ascoli₂ (Metric.closedBall x₀ R) (isCompact_closedBall x₀ R) _
      (hS1.inter hS2)
      (fun f x hf => Set.mem_iInter.mp hf.1 x)
      (equicontinuous_of_dist_bound hM fun i x y => Set.mem_iInter.mp (Set.mem_iInter.mp i.2.2 x) y)
  -- Extract a uniformly convergent subsequence.
  obtain ⟨g, -, φ, hφ, hconv⟩ := hcpt.tendsto_subseq fun n => ⟨hG1 n, hG2 n⟩
  -- Extend the limit to all of ℝ and conclude.
  let g' : ℝ → E := fun t => g (Set.projIcc a b hab t)
  refine ⟨φ, hφ, g', ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have heq : (Set.Icc a b).domRestrict g' = fun x : ↥(Set.Icc a b) => g x := by
      funext x
      change g (Set.projIcc a b hab (x : ℝ)) = g x
      rw [Set.projIcc_of_mem hab x.property]
    rw [heq]
    exact g.continuous_toFun
  · rw [_root_.Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [_root_.Metric.tendsto_nhds.mp hconv ε hε] with k hk
    intro x hx
    have hgx : g' x = g ⟨x, hx⟩ := by
      change g (Set.projIcc a b hab x) = g ⟨x, hx⟩
      rw [Set.projIcc_of_mem hab hx]
    have hFx : G (φ k) ⟨x, hx⟩ = F (φ k) x := G_apply (φ k) ⟨x, hx⟩
    rw [hgx, ← hFx, dist_comm]
    exact lt_of_le_of_lt (BoundedContinuousFunction.dist_coe_le_dist (⟨x, hx⟩ : ↥(Set.Icc a b))) hk

end Commons.Topology.Metric