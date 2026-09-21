import Mathlib
import Submission.Work.OddEnvelope.Profile

/-!
# Continuity of the envelope profile on the closed interval `[-1,1]`

The profile `envelopeProfile h x y` is `0` outside `[-1,1]`, equal to `1` at `0` and equal to the
two branches `envelopeRight h y` (on `(0,1)`) resp. `envelopeLeft h x` (on `(-1,0)`) in between.
This file proves that it is continuous on the closed interval `[-1,1]`.

Continuity on the open interval `(-1,1)` is a hypothesis (it also follows from
`envelopeProfile_contDiffOn`); the only content is the two endpoints, where one must show that
both branches tend to `0`.  Along `t → 1⁻` the inverse slope `σ(t)` (the unique positive slope
with `y σ = t`) tends to `0`, because `y` is strictly decreasing with `y σ → 1` as `σ → 0⁺`; and
the perturbation `h` vanishes for small slopes, so the branch `σ t * t + h (σ t)` tends to
`0 * 1 + 0 = 0`.  The left endpoint is the same computation with `t` replaced by `-t`, the curve
`x` and the reflected perturbation `-h`.
-/

namespace Work.OddEnvelope.Basic

open Set Filter
open scoped Topology ContDiff

/-! ### The limit of the right branch at `t = 1` -/

/-- Along `t → 1⁻`, the inverse slope `σ(t)` (the unique positive slope with `c σ = t`) tends to
`0`.  Indeed `σ(t) < ε` as soon as `t > c ε`, and `c ε < 1`. -/
lemma IsEnvelopeBranch.tendsto_slopeRight_at_one {p c : ℝ → ℝ} (hb : IsEnvelopeBranch p c) :
    Tendsto (slopeRight c) (𝓝[Set.Ioo (0 : ℝ) 1] 1) (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb0
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact lt_trans hb0 (hb.toIsChordCurve.slopeRight_pos ht)
  · intro b hb0
    have hcb : c b < 1 := hb.toIsChordCurve.lt_one hb0
    have hmem : Set.Ioi (c b) ∈ 𝓝[Set.Ioo (0 : ℝ) 1] 1 :=
      nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hcb)
    filter_upwards [self_mem_nhdsWithin, hmem] with t ht htb
    have hσpos : 0 < slopeRight c t := hb.toIsChordCurve.slopeRight_pos ht
    have hσt : c (slopeRight c t) = t := hb.toIsChordCurve.slopeRight_eq ht
    exact (hb.toIsChordCurve.strictAntiOn.lt_iff_gt hb0 hσpos).mp (by rw [hσt]; exact htb)

/-- The right branch of the envelope tends to `0` at the right end of the body: for `t → 1⁻` the
slope `σ(t)` tends to `0`, so `σ(t) * t → 0`, and the perturbation term vanishes because `h`
vanishes for small slopes. -/
lemma IsEnvelopeBranch.tendsto_envelopeRight_at_one {p c : ℝ → ℝ} (hb : IsEnvelopeBranch p c) :
    Tendsto (envelopeRight p c) (𝓝[Set.Ioo (0 : ℝ) 1] 1) (𝓝 0) := by
  have hσ := IsEnvelopeBranch.tendsto_slopeRight_at_one hb
  have hzero : ∀ᶠ t in 𝓝[Set.Ioo (0 : ℝ) 1] 1, slopeRight c t < 1 - 2 * tau :=
    hσ.eventually (Iio_mem_nhds one_sub_two_tau_pos)
  have hmain : Tendsto (fun t : ℝ => slopeRight c t * t) (𝓝[Set.Ioo (0 : ℝ) 1] 1) (𝓝 0) := by
    have hid : Tendsto (fun t : ℝ => t) (𝓝[Set.Ioo (0 : ℝ) 1] 1) (𝓝 1) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    simpa using hσ.mul hid
  refine Filter.Tendsto.congr' ?_ hmain
  filter_upwards [hzero, self_mem_nhdsWithin] with t ht hI
  rw [envelopeRight,
    hb.vanish_p (slopeRight c t) (hb.toIsChordCurve.slopeRight_pos hI) ht, add_zero]

/-! ### The limit of the left branch at `t = -1` -/

/-- The left branch of the envelope tends to `0` at the left end of the body.  It is the right
branch construction applied to `x`, the reflected perturbation `-h` and the reflected variable
`t ↦ -t`. -/
lemma IsEnvelopeCurve.tendsto_envelopeLeft_at_neg_one {h x y : ℝ → ℝ}
    (H : IsEnvelopeCurve h x y) :
    Tendsto (envelopeLeft h x) (𝓝[Set.Ioo (-1 : ℝ) 0] (-1)) (𝓝 0) := by
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[Set.Ioo (-1 : ℝ) 0] (-1))
      (𝓝[Set.Ioo (0 : ℝ) 1] 1) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa using (continuous_neg.continuousWithinAt
        (s := Set.Ioo (-1 : ℝ) 0) (x := (-1 : ℝ))).tendsto
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine Filter.Tendsto.congr' ?_
    ((IsEnvelopeBranch.tendsto_envelopeRight_at_one H.isEnvelopeBranch_left).comp hneg)
  filter_upwards with t
  exact (envelopeLeft_eq_negH h x t).symm

/-! ### The two endpoint filters -/

/-- Near `1`, membership in `[-1,1]` is membership in `(0,1] ∪ {1}`. -/
lemma eventuallyEq_Icc_insert_one :
    (Set.Icc (-1 : ℝ) 1) =ᶠ[𝓝 (1 : ℝ)] (insert (1 : ℝ) (Set.Ioo (0 : ℝ) 1) : Set ℝ) := by
  filter_upwards [Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ) < 1)] with s hs
  have hs' : |s - 1| < 1 := by
    rw [Metric.mem_ball, Real.dist_eq] at hs
    simpa using hs
  rw [abs_lt] at hs'
  obtain ⟨hs1, hs2⟩ := hs'
  have hspos : 0 < s := by linarith
  refine propext (Iff.intro ?_ ?_)
  · intro h
    change s ∈ Set.Icc (-1 : ℝ) 1 at h
    change s ∈ insert (1 : ℝ) (Set.Ioo (0 : ℝ) 1)
    rw [Set.mem_Icc] at h
    rw [Set.mem_insert_iff, Set.mem_Ioo]
    rcases eq_or_lt_of_le h.2 with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨hspos, h'⟩
  · intro h
    change s ∈ insert (1 : ℝ) (Set.Ioo (0 : ℝ) 1) at h
    change s ∈ Set.Icc (-1 : ℝ) 1
    rw [Set.mem_insert_iff, Set.mem_Ioo] at h
    rw [Set.mem_Icc]
    rcases h with rfl | ⟨h1, h2⟩
    · exact ⟨by norm_num, le_rfl⟩
    · exact ⟨by linarith, le_of_lt h2⟩

/-- Near `-1`, membership in `[-1,1]` is membership in `[-1,0) ∪ {-1}`. -/
lemma eventuallyEq_Icc_insert_neg_one :
    (Set.Icc (-1 : ℝ) 1) =ᶠ[𝓝 (-1 : ℝ)] (insert (-1 : ℝ) (Set.Ioo (-1 : ℝ) 0) : Set ℝ) := by
  filter_upwards [Metric.ball_mem_nhds (-1 : ℝ) (by norm_num : (0 : ℝ) < 1)] with s hs
  have hs' : |s + 1| < 1 := by
    rw [Metric.mem_ball, Real.dist_eq] at hs
    simpa using hs
  rw [abs_lt] at hs'
  obtain ⟨hs1, hs2⟩ := hs'
  have hsneg : s < 0 := by linarith
  refine propext (Iff.intro ?_ ?_)
  · intro h
    change s ∈ Set.Icc (-1 : ℝ) 1 at h
    change s ∈ insert (-1 : ℝ) (Set.Ioo (-1 : ℝ) 0)
    rw [Set.mem_Icc] at h
    rw [Set.mem_insert_iff, Set.mem_Ioo]
    rcases eq_or_lt_of_le h.1 with h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr ⟨h', hsneg⟩
  · intro h
    change s ∈ insert (-1 : ℝ) (Set.Ioo (-1 : ℝ) 0) at h
    change s ∈ Set.Icc (-1 : ℝ) 1
    rw [Set.mem_insert_iff, Set.mem_Ioo] at h
    rw [Set.mem_Icc]
    rcases h with rfl | ⟨h1, h2⟩
    · exact ⟨le_rfl, by norm_num⟩
    · exact ⟨le_of_lt h1, le_of_lt (by linarith : s < (1 : ℝ))⟩

/-! ### The theorem -/

theorem continuousOn_envelopeProfile {h x y : ℝ → ℝ} (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hf : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (Work.OddEnvelope.envelopeProfile h x y)
      (Set.Ioo (-1 : ℝ) 1)) :
    ContinuousOn (Work.OddEnvelope.envelopeProfile h x y) (Set.Icc (-1 : ℝ) 1) := by
  intro t ht
  rcases lt_trichotomy t (-1) with hlt | heq | hgt
  · exact absurd ht.1 (not_le.mpr hlt)
  · -- the left endpoint `t = -1`
    rw [heq]
    have hfilters : 𝓝[Set.Icc (-1 : ℝ) 1] (-1)
        = 𝓝[insert (-1 : ℝ) (Set.Ioo (-1 : ℝ) 0)] (-1) :=
      nhdsWithin_eq_iff_eventuallyEq.mpr eventuallyEq_Icc_insert_neg_one
    have hcont : ContinuousWithinAt (envelopeProfile h x y) (Set.Ioo (-1 : ℝ) 0) (-1) := by
      rw [ContinuousWithinAt, envelopeProfile_left_end]
      refine Filter.Tendsto.congr' ?_ (IsEnvelopeCurve.tendsto_envelopeLeft_at_neg_one H)
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (envelopeProfile_of_neg hs).symm
    have hins : ContinuousWithinAt (envelopeProfile h x y)
        (insert (-1 : ℝ) (Set.Ioo (-1 : ℝ) 0)) (-1) :=
      continuousWithinAt_insert_self.mpr hcont
    change Tendsto (envelopeProfile h x y) (𝓝[Set.Icc (-1 : ℝ) 1] (-1))
      (𝓝 ((envelopeProfile h x y) (-1)))
    rw [hfilters]
    exact hins
  · rcases lt_trichotomy t 1 with hlt1 | heq1 | hgt1
    · -- an interior point
      have hmem : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hgt, hlt1⟩
      have hmemIcc : Set.Icc (-1 : ℝ) 1 ∈ 𝓝 t :=
        mem_of_superset (isOpen_Ioo.mem_nhds hmem) Set.Ioo_subset_Icc_self
      have hmemIoo : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 t := isOpen_Ioo.mem_nhds hmem
      rw [continuousWithinAt_iff_continuousAt hmemIcc,
        ← continuousWithinAt_iff_continuousAt hmemIoo]
      exact hf.continuousOn t hmem
    · -- the right endpoint `t = 1`
      rw [heq1]
      have hfilters : 𝓝[Set.Icc (-1 : ℝ) 1] (1 : ℝ)
          = 𝓝[insert (1 : ℝ) (Set.Ioo (0 : ℝ) 1)] 1 :=
        nhdsWithin_eq_iff_eventuallyEq.mpr eventuallyEq_Icc_insert_one
      have hcont : ContinuousWithinAt (envelopeProfile h x y) (Set.Ioo (0 : ℝ) 1) 1 := by
        rw [ContinuousWithinAt, envelopeProfile_right_end]
        refine Filter.Tendsto.congr' ?_
          (IsEnvelopeBranch.tendsto_envelopeRight_at_one H.isEnvelopeBranch_right)
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact (envelopeProfile_of_pos hs).symm
      have hins : ContinuousWithinAt (envelopeProfile h x y)
          (insert (1 : ℝ) (Set.Ioo (0 : ℝ) 1)) 1 :=
        continuousWithinAt_insert_self.mpr hcont
      change Tendsto (envelopeProfile h x y) (𝓝[Set.Icc (-1 : ℝ) 1] (1 : ℝ))
        (𝓝 ((envelopeProfile h x y) 1))
      rw [hfilters]
      exact hins
    · exact absurd ht.2 (not_le.mpr hgt1)

end Work.OddEnvelope.Basic
