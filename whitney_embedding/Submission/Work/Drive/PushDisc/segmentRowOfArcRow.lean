import Mathlib
import Submission.Work.Drive.PushDisc.asymSignTransport

namespace Work.Drive.PushDisc

/-- **A straight segment row of a chart extends past the ends of an arc row.**

If `γ₁` runs, in the chart `c`, along the standard segment
`splitE k ((2t-1, 0))`, `t ∈ [0,1]` (i.e. along `{splitE k (x, 0) : x ∈ [-1,1]}`), and stays in
`U₁ = c.source`, then some uniform enlargement of the parameter interval `[-1,1]` is still contained
in the chart's target, hence every `splitE k (x, 0)` with `|x| ≤ 1 + δ₀` has a preimage in `U₁`.

The point is that `c.target` is *open* and contains the compact image of the arc, so a full
neighbourhood of that compact arc lies in the target; the map `x ↦ splitE k (x, 0)` is the line
`x • splitE k (1, 0)`, so a uniform bound on `|x - clamp x|` supplies the required `δ₀`. -/
theorem segmentRowOfArcRow {n k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (U₁ : Set M) (hU₁o : IsOpen U₁)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hcsrc : c.source = U₁)
    (γ₁ : ℝ → M) (hγ₁arc : γ₁ '' Set.Icc (0 : ℝ) 1 ⊆ U₁)
    (harc : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      c (γ₁ t) = Work.Drive.PushDisc.splitE k ((2 * t - 1 : ℝ), (0 : EuclideanSpace ℝ (Fin k)))) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ x : ℝ, |x| ≤ 1 + δ₀ →
      ∃ z : M, z ∈ U₁ ∧ c z = Work.Drive.PushDisc.splitE k (x, (0 : EuclideanSpace ℝ (Fin k))) := by
  -- the straight row as a function of its parameter
  let f : ℝ → EuclideanSpace ℝ (Fin (k + 1)) :=
    fun x => Work.Drive.PushDisc.splitE k (x, (0 : EuclideanSpace ℝ (Fin k)))
  have hlin : ∀ x : ℝ, f x = x • f 1 := by
    intro x
    have h1 : (x, (0 : EuclideanSpace ℝ (Fin k))) =
        x • ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) := by
      ext <;> simp
    show Work.Drive.PushDisc.splitE k (x, (0 : EuclideanSpace ℝ (Fin k))) = x • f 1
    rw [h1, map_smul]
  have hcont : Continuous f := by
    rw [show f = fun x : ℝ => x • f 1 from funext hlin]
    exact continuous_id.smul continuous_const
  -- the arc row lies in the chart's target
  have hSsub : f '' Set.Icc (-1 : ℝ) 1 ⊆ c.target := by
    rintro z ⟨x, hx, rfl⟩
    have ht : (x + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hmemsrc : γ₁ ((x + 1) / 2) ∈ c.source := by
      rw [hcsrc]; exact hγ₁arc ⟨_, ht, rfl⟩
    have h := c.map_source hmemsrc
    rw [harc _ ht] at h
    have hx' : x = 2 * ((x + 1) / 2) - 1 := by ring
    show f x ∈ c.target
    show Work.Drive.PushDisc.splitE k (x, (0 : EuclideanSpace ℝ (Fin k))) ∈ c.target
    rw [hx']
    exact h
  -- a uniform neighbourhood of the compact arc sits in the open target
  obtain ⟨δ, hδpos, hδ⟩ :=
    (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).image hcont |>.exists_thickening_subset_open
      c.open_target hSsub
  have hδpos' : (0 : ℝ) < ‖f 1‖ + 1 := by positivity
  have hδ₀pos : 0 < min 1 (δ / (‖f 1‖ + 1)) := lt_min one_pos (div_pos hδpos hδpos')
  refine ⟨min 1 (δ / (‖f 1‖ + 1)), hδ₀pos, ?_⟩
  intro x hx
  have hδ₀le : min 1 (δ / (‖f 1‖ + 1)) ≤ δ / (‖f 1‖ + 1) := min_le_right _ _
  have hmem : f x ∈ Metric.thickening δ (f '' Set.Icc (-1 : ℝ) 1) := by
    rw [Metric.mem_thickening_iff]
    -- clamp the parameter into the interval
    set y : ℝ := max (-1) (min 1 x) with hy
    have hyIcc : y ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
    refine ⟨f y, ⟨y, hyIcc, rfl⟩, ?_⟩
    have hxy : |x - y| ≤ min 1 (δ / (‖f 1‖ + 1)) := by
      rcases lt_or_ge x 1 with h1 | h1
      · rcases lt_or_ge (-1 : ℝ) x with h2 | h2
        · have hyx : y = x := by simp [hy, min_eq_right h1.le, max_eq_right h2.le]
          rw [hyx, sub_self, abs_zero]
          exact hδ₀pos.le
        · have hyx : y = -1 := by simp [hy, min_eq_right h1.le, max_eq_left h2]
          have hx0 : x ≤ 0 := by linarith
          have habs : |x| = -x := abs_of_nonpos hx0
          have hle : -x ≤ 1 + min 1 (δ / (‖f 1‖ + 1)) := by rwa [habs] at hx
          rw [hyx]
          have h2' : x - (-1) ≤ 0 := by linarith
          rw [abs_of_nonpos h2']
          linarith
      · have hyx : y = 1 := by simp [hy, min_eq_left h1]
        have hx0 : 0 ≤ x := by linarith
        have habs : |x| = x := abs_of_nonneg hx0
        have hle : x ≤ 1 + min 1 (δ / (‖f 1‖ + 1)) := by rwa [habs] at hx
        rw [hyx]
        have h2' : 0 ≤ x - 1 := by linarith
        rw [abs_of_nonneg h2']
        linarith
    rw [dist_eq_norm]
    have hsub : f x - f y = f (x - y) := by
      show Work.Drive.PushDisc.splitE k (x, (0 : EuclideanSpace ℝ (Fin k))) -
        Work.Drive.PushDisc.splitE k (y, (0 : EuclideanSpace ℝ (Fin k))) = f (x - y)
      rw [← map_sub]
      congr 1
      simp
    have hnorm : ‖f (x - y)‖ = |x - y| * ‖f 1‖ := by
      rw [show f (x - y) = (x - y) • f 1 from hlin (x - y), norm_smul, Real.norm_eq_abs]
    rw [hsub, hnorm]
    have hle : |x - y| * ‖f 1‖ ≤ (δ / (‖f 1‖ + 1)) * ‖f 1‖ :=
      mul_le_mul_of_nonneg_right (hxy.trans hδ₀le) (norm_nonneg _)
    refine lt_of_le_of_lt hle ?_
    rw [div_mul_eq_mul_div, div_lt_iff₀ hδpos']
    nlinarith [norm_nonneg (f 1), hδpos]
  have hmem' : f x ∈ c.target := hδ hmem
  refine ⟨c.symm (f x), ?_, ?_⟩
  · rw [← hcsrc]; exact c.map_target hmem'
  · exact c.right_inv hmem'

end Work.Drive.PushDisc
