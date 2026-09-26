import Mathlib
import Submission.Work.Drive.oFatDefs
import Submission.Work.Drive.reparam_slice_knot

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **`OFatR r ρ` is closed in the plane** (`ρ > 0`).  Indeed `OFatR r ρ` is the set of strip
points `q = (x,y)` with `0 < y < period` admitting a `u` with `x + ρ ≤ u ≤ x + y - ρ` and
`r u ∈ openSegment ℝ (r x) (r (x+y))`.  For a convergent sequence `q_n → q` of such points one takes
a convergent subsequence of the (bounded) middles `u_n ∈ [q_n.1 + ρ, q_n.1 + q_n.2 - ρ]`; its limit
`v` satisfies `q.1 + ρ ≤ v ≤ q.1 + q.2 - ρ` and `r v ∈ segment ℝ (r q.1) (r (q.1 + q.2))`
(closedness of the closed segment).  Since `v` is strictly between `q.1` and `q.1 + q.2`
(`ρ > 0`, so `q.2 ≥ 2ρ`) and `r` is injective on a period, `r v` is neither `r q.1` nor
`r (q.1+q.2)`, so it lies in the *open* segment; and `q.2 ≥ 2ρ > 0`, `q.2 < period` (the case
`q.2 = period` would force `r v = r q.1`, impossible).  Hence `q ∈ OFatR r ρ`.

`ρ > 0` is essential: for `ρ = 0` the limit middle may fall on an endpoint. -/
theorem isClosed_OFatR
    {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {ρ : ℝ} (hρ : 0 < ρ) :
    IsClosed (Work.Drive.OFatR r ρ) := by
  classical
  have hP : (0 : ℝ) < period := by rw [period]; positivity
  rw [← closure_subset_iff_isClosed]
  intro q hq
  rw [Metric.mem_closure_iff] at hq
  -- a sequence in `OFatR r ρ` converging to `q`
  have hseq : ∀ n : ℕ, ∃ y : ℝ × ℝ, y ∈ Work.Drive.OFatR r ρ ∧ dist y q < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨y, hy, hd⟩ := hq (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨y, hy, by rwa [dist_comm] at hd⟩
  choose qn hqn_mem hqn_dist using hseq
  have hqn_spec (n : ℕ) : 0 < (qn n).2 ∧ (qn n).2 < period ∧ ∃ u : ℝ,
      (qn n).1 + ρ ≤ u ∧ u ≤ (qn n).1 + (qn n).2 - ρ ∧
      r u ∈ openSegment ℝ (r (qn n).1) (r ((qn n).1 + (qn n).2)) :=
    Work.Drive.mem_OFatR_iff.mp (hqn_mem n)
  have hqn_fst (n : ℕ) : |(qn n).1 - q.1| < 1 := by
    have h1 : dist (qn n).1 q.1 ≤ dist (qn n) q := by
      rw [Prod.dist_eq]; exact le_max_left _ _
    rw [Real.dist_eq] at h1
    have h2 : dist (qn n) q < 1 := by
      refine lt_of_lt_of_le (hqn_dist n) ?_
      rw [div_le_one (by positivity)]
      simp
    linarith
  -- middles and their convex-combination parameters, chosen jointly
  have hcomb : ∀ n : ℕ, ∃ p : ℝ × ℝ, p.2 ∈ Set.Ioo (0 : ℝ) 1 ∧
      (qn n).1 + ρ ≤ p.1 ∧ p.1 ≤ (qn n).1 + (qn n).2 - ρ ∧
      (1 - p.2) • r (qn n).1 + p.2 • r ((qn n).1 + (qn n).2) = r p.1 := by
    intro n
    obtain ⟨u, hu1, hu2, hu3⟩ := (hqn_spec n).2.2
    rw [openSegment_eq_image] at hu3
    obtain ⟨θ, hθ, hθeq⟩ := hu3
    exact ⟨(u, θ), hθ, hu1, hu2, hθeq⟩
  choose p hp using hcomb
  have hdist : Filter.Tendsto (fun n => dist (qn n) q) Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => dist_nonneg) (fun n => le_of_lt (hqn_dist n))
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Filter.Tendsto qn Filter.atTop (nhds q) :=
    tendsto_iff_dist_tendsto_zero.mpr hdist
  -- the middles and parameters are bounded, hence have a convergent subsequence
  have hZK : ∀ n : ℕ, p n ∈ Set.Icc (q.1 - 1 + ρ) (q.1 + 1 + period - ρ) ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro n
    have his : |(qn n).1 - q.1| < 1 := hqn_fst n
    rw [abs_lt] at his
    have hq2hi : (qn n).2 < period := (hqn_spec n).2.1
    exact ⟨⟨by linarith [(hp n).2.1], by linarith [(hp n).2.2.1]⟩,
           ⟨le_of_lt (hp n).1.1, le_of_lt (hp n).1.2⟩⟩
  have hKcompact : IsCompact (Set.Icc (q.1 - 1 + ρ) (q.1 + 1 + period - ρ) ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨zv, hzv, φ, hφmono, hzlim⟩ := hKcompact.tendsto_subseq (x := p) hZK
  have hz1 : Filter.Tendsto (fun n => (p (φ n)).1) Filter.atTop (nhds zv.1) :=
    (continuous_fst.tendsto zv).comp hzlim
  have hz2 : Filter.Tendsto (fun n => (p (φ n)).2) Filter.atTop (nhds zv.2) :=
    (continuous_snd.tendsto zv).comp hzlim
  have hQlim : Filter.Tendsto (fun n => qn (φ n)) Filter.atTop (nhds q) :=
    hlim.comp hφmono.tendsto_atTop
  have hQ1 : Filter.Tendsto (fun n => (qn (φ n)).1) Filter.atTop (nhds q.1) :=
    (continuous_fst.tendsto q).comp hQlim
  have hQ2 : Filter.Tendsto (fun n => (qn (φ n)).2) Filter.atTop (nhds q.2) :=
    (continuous_snd.tendsto q).comp hQlim
  have hQ12 : Filter.Tendsto (fun n => (qn (φ n)).1 + (qn (φ n)).2) Filter.atTop
      (nhds (q.1 + q.2)) := hQ1.add hQ2
  -- pass the bounds to the limit
  have hq2_pos : 0 < q.2 := by
    have h2ρ : 2 * ρ ≤ q.2 :=
      le_of_tendsto_of_tendsto' tendsto_const_nhds hQ2
        (fun n => by linarith [(hp (φ n)).2.1, (hp (φ n)).2.2.1])
    linarith
  have hq2_le : q.2 ≤ period :=
    le_of_tendsto_of_tendsto' hQ2 tendsto_const_nhds
      (fun n => le_of_lt (hqn_spec (φ n)).2.1)
  have hv_low : q.1 + ρ ≤ zv.1 :=
    le_of_tendsto_of_tendsto' (hQ1.add tendsto_const_nhds) hz1 (fun n => (hp (φ n)).2.1)
  have hv_high : zv.1 ≤ q.1 + q.2 - ρ :=
    le_of_tendsto_of_tendsto' hz1 (hQ12.sub tendsto_const_nhds) (fun n => (hp (φ n)).2.2.1)
  have hq1_lt : q.1 < zv.1 := by linarith
  have hzv_lt : zv.1 < q.1 + period := by linarith
  have hinj : Set.InjOn r (Set.Ico q.1 (q.1 + period)) :=
    Work.Drive.injOn_Ico_add_period hP hr.periodic hr.injective_on_period
  have hv_mem : zv.1 ∈ Set.Ico q.1 (q.1 + period) := ⟨le_of_lt hq1_lt, hzv_lt⟩
  have hq1_mem : q.1 ∈ Set.Ico q.1 (q.1 + period) := ⟨le_rfl, by linarith⟩
  -- the limit of the convex-combination identity
  have hrhs : Filter.Tendsto
      (fun n => (1 - (p (φ n)).2) • r ((qn (φ n)).1) + (p (φ n)).2 • r ((qn (φ n)).1 + (qn (φ n)).2))
      Filter.atTop (nhds ((1 - zv.2) • r q.1 + zv.2 • r (q.1 + q.2))) := by
    have h1 : Filter.Tendsto (fun n => 1 - (p (φ n)).2) Filter.atTop (nhds (1 - zv.2)) :=
      tendsto_const_nhds.sub hz2
    have h2 : Filter.Tendsto (fun n => r ((qn (φ n)).1)) Filter.atTop (nhds (r q.1)) :=
      (hr.smooth.continuous.tendsto q.1).comp hQ1
    have h3 : Filter.Tendsto (fun n => r ((qn (φ n)).1 + (qn (φ n)).2)) Filter.atTop
        (nhds (r (q.1 + q.2))) :=
      (hr.smooth.continuous.tendsto (q.1 + q.2)).comp hQ12
    exact (h1.smul h2).add (hz2.smul h3)
  have hmain : r zv.1 = (1 - zv.2) • r q.1 + zv.2 • r (q.1 + q.2) := by
    refine tendsto_nhds_unique ((hr.smooth.continuous.tendsto zv.1).comp hz1) ?_
    exact Filter.Tendsto.congr (fun n => (hp (φ n)).2.2.2) hrhs
  -- the chord length is strictly below the period
  have hq2_lt : q.2 < period := by
    rcases lt_or_ge q.2 period with h | h
    · exact h
    · exfalso
      have hq2eq : q.2 = period := le_antisymm hq2_le h
      have hEq : r zv.1 = r q.1 := by
        rw [hmain, hq2eq, hr.periodic q.1, ← add_smul]
        simp
      have := hinj hv_mem hq1_mem hEq
      linarith
  have hq12_mem : q.1 + q.2 ∈ Set.Ico q.1 (q.1 + period) := ⟨by linarith, by linarith⟩
  -- the parameter is strictly inside `(0,1)`: the middle is not an endpoint of the chord
  have hz2_pos : 0 < zv.2 := by
    rcases eq_or_lt_of_le hzv.2.1 with h | h
    · exfalso
      have hEq : r zv.1 = r q.1 := by rw [hmain, ← h]; simp
      have := hinj hv_mem hq1_mem hEq
      linarith
    · exact h
  have hz2_lt_one : zv.2 < 1 := by
    rcases eq_or_lt_of_le hzv.2.2 with h | h
    · exfalso
      have hEq : r zv.1 = r (q.1 + q.2) := by rw [hmain, h]; simp
      have := hinj hv_mem hq12_mem hEq
      linarith
    · exact h
  have hopen : r zv.1 ∈ openSegment ℝ (r q.1) (r (q.1 + q.2)) := by
    rw [openSegment_eq_image, Set.mem_image]
    exact ⟨zv.2, ⟨hz2_pos, hz2_lt_one⟩, hmain.symm⟩
  exact ⟨hq2_pos, hq2_lt, zv.1, hv_low, hv_high, hopen⟩

end Work.Drive
