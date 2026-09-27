import Mathlib
import Submission.Work.Noncompact.CompressionTube.flat_frontier
import Submission.Work.Noncompact.CompressionTube.clean_exit_of_flat

/-!
# Clean crossing of a chart ball, and of finite unions of chart balls

`CleanCrossingIn E S z` (`clean_exit_of_flat.lean`) is the flatness input of the clean-exit level
step.  This file proves it for the configurations that the *good points* of a finite union of
chart balls provide:

* `cleanCrossingIn_homeoBall`: a single chart ball `φ.symm '' closedBall c r` (the preimage under a
  chart `φ` of a Euclidean closed ball, with the ball inside the chart target) is cleanly crossable
  at any of its points, with respect to any open carrier through that point.  The crossing arc is
  the straight segment in the chart, transported by `φ.symm`.
* `cleanCrossingIn_chartBall`: the same for the chart at a point `x` of `M`.
* `cleanCrossingIn_unique_atom`: if `z` lies in exactly one member of a finite family of closed
  chart balls while lying in its union, then the union is cleanly crossable at `z` — a neighbourhood
  of `z` misses all the other atoms, so the situation is that of the single ball.

These are the "good points" of the flat-refinement scheme: the *bad* points of a finite union of
chart balls are those where two of the balls' boundaries meet.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Noncompact.CompressionTube

open Set Topology Metric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

variable {x z : M} {c : EuclideanSpace ℝ (Fin n)} {r : ℝ}

/-- The closed ball of a chart: the preimage of a Euclidean closed ball under `φ.symm`. -/
noncomputable def homeoBall (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) : Set M :=
  φ.symm '' closedBall c r

/-- The closed ball of the chart at `x`. -/
noncomputable def chartBall (x : M) (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) : Set M :=
  homeoBall (chartAt (EuclideanSpace ℝ (Fin n)) x) c r

/-- A set which is a finite union of chart balls (the "atoms" of the good-point scheme). -/
def IsChartBallUnion (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (S : Set M) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (x : ι → M) (c : ι → EuclideanSpace ℝ (Fin n)) (r : ι → ℝ),
    (∀ i, closedBall (c i) (r i) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).target) ∧
    S = ⋃ i, chartBall (n := n) (x i) (c i) (r i)


/-- **The single chart ball is cleanly crossable.**  The crossing arc is the straight segment in
the chart: the chart is a homeomorphism onto its target, so the segment between two points of a
Euclidean ball lies in the ball, and the parameter set where the segment meets the ball is an
initial segment by convexity. -/
theorem cleanCrossingIn_homeoBall {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {c : EuclideanSpace ℝ (Fin n)} {r : ℝ} (htgt : closedBall c r ⊆ φ.target)
    {z : M} (hzA : z ∈ homeoBall φ c r) {E : Set M} (hE : IsOpen E) (hzE : z ∈ E) :
    CleanCrossingIn E (homeoBall φ c r) z := by
  classical
  obtain ⟨y0, hy0B, hy0eq⟩ := hzA
  have hy0t : y0 ∈ φ.target := htgt hy0B
  have hztgt : φ z ∈ φ.target := by rw [← hy0eq, φ.right_inv hy0t]; exact hy0t
  have hzsrc : z ∈ φ.source := by rw [← hy0eq]; exact φ.map_target hy0t
  -- a radius small enough that the ball sits in the target and its `φ.symm`-image sits in `E`
  have hnhds : φ.symm ⁻¹' E ∈ 𝓝 (φ z) :=
    (φ.continuousAt_symm hztgt).preimage_mem_nhds (hE.mem_nhds (by rw [φ.left_inv hzsrc]; exact hzE))
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hnhds
  obtain ⟨ρ', hρ'pos, hρ'tgt⟩ := Metric.mem_nhds_iff.mp (φ.open_target.mem_nhds hztgt)
  set R : ℝ := min ρ ρ' with hRdef
  have hRpos : 0 < R := lt_min hρpos hρ'pos
  have hRE : ball (φ z) R ⊆ φ.symm ⁻¹' E := fun y hy => hρsub (ball_subset_ball (min_le_left _ _) hy)
  have hRtgt : ball (φ z) R ⊆ φ.target := fun y hy => hρ'tgt (ball_subset_ball (min_le_right _ _) hy)
  refine ⟨φ.source ∩ φ ⁻¹' ball (φ z) R, ?_, ?_, ?_, ?_⟩
  · exact φ.continuousOn.isOpen_inter_preimage φ.open_source Metric.isOpen_ball
  · -- `U ⊆ E`
    rintro p ⟨hps, hpb⟩
    have hpE : φ.symm (φ p) ∈ E := hRE hpb
    rwa [φ.left_inv hps] at hpE
  · exact ⟨hzsrc, mem_ball_self hRpos⟩
  · -- the crossing
    intro p hp q hq
    obtain ⟨hpU, hpint⟩ := hp
    obtain ⟨hqU, hqS⟩ := hq
    have hp3 : φ p ∈ closedBall c r := by
      obtain ⟨y, hyB, hyeq⟩ := interior_subset hpint
      have : φ p = y := by rw [← hyeq]; exact φ.right_inv (htgt hyB)
      rwa [this]
    have hq3 : φ q ∉ closedBall c r := by
      intro hcon
      exact hqS ⟨φ q, hcon, φ.left_inv hqU.1⟩
    obtain ⟨s, hs, hseg1, hseg2⟩ := cleanCrossing_segment_closedBall hp3 hq3
    -- the clamped straight segment in the chart
    set cl : ℝ → ℝ := fun t => max 0 (min t 1) with hcldef
    have hclc : Continuous cl := by
      rw [hcldef]; exact continuous_const.max (continuous_id.min continuous_const)
    have hclmem : ∀ t : ℝ, cl t ∈ Icc (0 : ℝ) 1 := by
      intro t
      rw [hcldef]; simp only
      exact ⟨le_max_left _ _, max_le (le_of_lt one_pos) (min_le_right _ _)⟩
    have hclid : ∀ t ∈ Icc (0 : ℝ) 1, cl t = t := by
      intro t ht
      rw [hcldef]; simp only
      rw [min_eq_left ht.2, max_eq_right ht.1]
    set σ : ℝ → EuclideanSpace ℝ (Fin n) :=
      fun t => (1 - cl t) • φ p + cl t • φ q with hσdef
    have hσc : Continuous σ := by
      rw [hσdef]
      exact ((continuous_const.sub hclc).smul continuous_const).add (hclc.smul continuous_const)
    have hσball : ∀ t : ℝ, σ t ∈ ball (φ z) R := by
      intro t
      have ha : (0 : ℝ) ≤ 1 - cl t := sub_nonneg.mpr (hclmem t).2
      have hb : (0 : ℝ) ≤ cl t := (hclmem t).1
      have hab : (1 - cl t) + cl t = 1 := by ring
      have := convex_ball (φ z) R hpU.2 hqU.2 ha hb hab
      simpa only [hσdef] using this
    have hσt_tgt : ∀ t : ℝ, σ t ∈ φ.target := fun t => hRtgt (hσball t)
    refine ⟨s, fun t => φ.symm (σ t), ?_, ?_, ?_, ?_, ?_, hs, ?_, ?_⟩
    · -- continuity of `φ.symm ∘ σ`
      rw [continuous_iff_continuousAt]
      intro t
      exact (φ.continuousAt_symm (hσt_tgt t)).comp hσc.continuousAt
    · -- `α 0 = p`
      show φ.symm (σ 0) = p
      rw [hσdef]
      simp only [hclid 0 (by norm_num), sub_zero, one_smul, zero_smul, add_zero]
      exact φ.left_inv hpU.1
    · -- `α 1 = q`
      show φ.symm (σ 1) = q
      rw [hσdef]
      simp only [hclid 1 (by norm_num), sub_self, zero_smul, one_smul, zero_add]
      exact φ.left_inv hqU.1
    · -- the image lies in `U`
      rintro _ ⟨t, -, rfl⟩
      refine ⟨φ.map_target (hσt_tgt t), ?_⟩
      show φ (φ.symm (σ t)) ∈ ball (φ z) R
      rw [φ.right_inv (hσt_tgt t)]
      exact hσball t
    · -- injectivity
      intro a ha b hb hab
      have hσab : σ a = σ b :=
        (PartialEquiv.injOn φ.symm.toPartialEquiv) (hσt_tgt a) (hσt_tgt b) hab
      rw [hσdef] at hσab
      simp only at hσab
      rw [hclid a ha, hclid b hb] at hσab
      have hpq : φ p ≠ φ q := by
        intro h
        exact hq3 (h ▸ hp3)
      have hdiff : φ q - φ p ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
      have hzero : (a - b) • (φ q - φ p) = 0 := by
        have h2 : (1 - a) • φ p + a • φ q - ((1 - b) • φ p + b • φ q) = 0 := by
          rw [hσab, sub_self]
        have h3 : (1 - a) • φ p + a • φ q - ((1 - b) • φ p + b • φ q)
            = (a - b) • (φ q - φ p) := by module
        rw [← h3]; exact h2
      have : a - b = 0 := (smul_eq_zero.mp hzero).resolve_right hdiff
      linarith
    · -- the `S`-part
      intro t ht
      change φ.symm (σ t) ∈ homeoBall φ c r
      have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, le_trans ht.2 hs.2⟩
      have hclt : σ t = (1 - t) • φ p + t • φ q := by
        rw [hσdef]; simp only [hclid t htI]
      rw [hclt]
      exact ⟨(1 - t) • φ p + t • φ q, hseg1 t ht, rfl⟩
    · -- outside `S`
      intro t ht hmem
      have hmem' : φ.symm (σ t) ∈ homeoBall φ c r := hmem
      obtain ⟨y, hyB, hyeq⟩ := hmem'
      have htI : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt (lt_of_le_of_lt hs.1 ht.1), ht.2⟩
      have hkey : (1 - t) • φ p + t • φ q = y := by
        have h1 : φ (φ.symm (σ t)) = φ (φ.symm y) := by rw [hyeq]
        rw [φ.right_inv (hσt_tgt t), φ.right_inv (htgt hyB)] at h1
        rw [hσdef] at h1
        simpa only [hclid t htI] using h1
      exact hseg2 t ht (hkey ▸ hyB)

/-- **The chart ball is closed.**  (Only used to produce the neighbourhood avoiding the other
atoms of a finite family.) -/
theorem isClosed_homeoBall [T2Space M] {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {c : EuclideanSpace ℝ (Fin n)} {r : ℝ} (htgt : closedBall c r ⊆ φ.target) :
    IsClosed (homeoBall φ c r) := by
  have hcont : ContinuousOn (↑φ.symm) (closedBall c r) := fun y hy => (φ.continuousAt_symm (htgt hy)).continuousWithinAt
  exact (isCompact_closedBall c r).image_of_continuousOn hcont |>.isClosed

/-- **The unique-atom lemma.**  If a point `z` lies in the atom `A i0` of a finite family and an
open neighbourhood `W` of `z` misses all the other atoms, then the union of the family is cleanly
crossable at `z` as soon as the single atom `A i0` is cleanly crossable in the shrunken carrier
`E ∩ W`: the crossing arc of the single atom stays in its neighbourhood, which is inside `W`, hence
misses all the other atoms. -/
theorem cleanCrossingIn_iUnion_of_unique {ι : Type*} [Fintype ι] {A : ι → Set M} {i0 : ι}
    {W : Set M} (hW : IsOpen W) (hzW : z ∈ W)
    (hWdisj : ∀ i, i ≠ i0 → Disjoint W (A i))
    {E : Set M} (hE : IsOpen E) (hzE : z ∈ E)
    (hcross : CleanCrossingIn (E ∩ W) (A i0) z) :
    CleanCrossingIn E (⋃ i, A i) z := by
  classical
  obtain ⟨U, hUopen, hUE, hzU, hprop⟩ := hcross
  have hUsub : U ∩ (⋃ i, A i) ⊆ A i0 := by
    intro y hy
    obtain ⟨hyU, hyA⟩ := hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hyA
    by_cases h : i = i0
    · rwa [h] at hi
    · exact absurd (Set.disjoint_left.mp (hWdisj i h) (hUE hyU).2 hi) (by simp)
  refine ⟨U, hUopen, fun y hy => (hUE hy).1, hzU, ?_⟩
  intro p hp q hq
  obtain ⟨hpU, hpint⟩ := hp
  obtain ⟨hqU, hqS⟩ := hq
  have hpnhds : U ∩ interior (⋃ i, A i) ∈ 𝓝 p :=
    (hUopen.inter isOpen_interior).mem_nhds ⟨hpU, hpint⟩
  have hpA : p ∈ interior (A i0) :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hpnhds
      (fun y hy => hUsub ⟨hy.1, interior_subset hy.2⟩))
  have hqA : q ∉ A i0 := fun h => hqS (Set.mem_iUnion.mpr ⟨i0, h⟩)
  obtain ⟨s, α, hαc, hα0, hα1, hαimg, hαinj, hs, hαS, hαS'⟩ := hprop p ⟨hpU, hpA⟩ q ⟨hqU, hqA⟩
  refine ⟨s, α, hαc, hα0, hα1, ?_, hαinj, hs, ?_, ?_⟩
  · intro y hy
    exact hαimg hy
  · intro t ht
    exact Set.mem_iUnion.mpr ⟨i0, hαS t ht⟩
  · intro t ht hmem
    have hαtU : α t ∈ U := hαimg ⟨t, ⟨le_of_lt (lt_of_le_of_lt hs.1 ht.1), ht.2⟩, rfl⟩
    have hαtW : α t ∈ W := (hUE hαtU).2
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
    by_cases h : i = i0
    · exact hαS' t ht (by rwa [h] at hi)
    · exact Set.disjoint_left.mp (hWdisj i h) hαtW hi

/-- **The unique-atom lemma for chart balls.**  If `z` lies in exactly one member of a finite
family of chart balls, then the union of the family is cleanly crossable at `z`.  This is the
"good point" input of the level step: the bad points of a finite union of chart balls are those
where two of the balls' boundaries meet. -/
theorem cleanCrossingIn_iUnion_chartBall {ι : Type*} [Fintype ι] [T2Space M]
    {x : ι → M} {c : ι → EuclideanSpace ℝ (Fin n)} {r : ι → ℝ} {i0 : ι}
    (htgt : ∀ i, closedBall (c i) (r i) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).target)
    (hzA : z ∈ chartBall (x i0) (c i0) (r i0))
    {E : Set M} (hE : IsOpen E) (hzE : z ∈ E)
    (hz : ∀ i, i ≠ i0 → z ∉ chartBall (x i) (c i) (r i)) :
    CleanCrossingIn E (⋃ i, chartBall (x i) (c i) (r i)) z := by
  classical
  -- the other atoms together form a closed set missing `z`
  set W : Set M := (⋃ i : {i : ι // i ≠ i0}, chartBall (x i.1) (c i.1) (r i.1))ᶜ with hWdef
  have hWopen : IsOpen W := by
    rw [hWdef, isOpen_compl_iff]
    exact isClosed_iUnion_of_finite (fun i => isClosed_homeoBall (htgt i.1))
  have hzW : z ∈ W := by
    rw [hWdef]
    simp only [mem_compl_iff, mem_iUnion, Subtype.exists, not_exists]
    exact fun i hi hzi => hz i hi hzi
  have hWdisj : ∀ i, i ≠ i0 → Disjoint W (chartBall (x i) (c i) (r i)) := by
    intro i hi
    rw [Set.disjoint_left]
    intro y hyW hyA
    rw [hWdef] at hyW
    exact hyW (Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hyA⟩)
  refine cleanCrossingIn_iUnion_of_unique (A := fun i => chartBall (x i) (c i) (r i))
    hWopen hzW hWdisj hE hzE ?_
  exact cleanCrossingIn_homeoBall (htgt i0) hzA (hE.inter hWopen) ⟨hzE, hzW⟩

/-- **The chart ball at a point is cleanly crossable.** -/
theorem cleanCrossingIn_chartBall {x z : M} {c : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (htgt : closedBall c r ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) x).target)
    (hzA : z ∈ chartBall x c r) {E : Set M} (hE : IsOpen E) (hzE : z ∈ E) :
    CleanCrossingIn E (chartBall x c r) z :=
  cleanCrossingIn_homeoBall htgt hzA hE hzE

end Work.Noncompact.CompressionTube
