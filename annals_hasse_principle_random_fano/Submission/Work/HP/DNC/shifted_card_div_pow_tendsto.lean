import Mathlib

namespace Work.HP.DNC

open MeasureTheory BoxIntegral Filter
open scoped Topology Pointwise Classical

variable {ι : Type*}

noncomputable section

section Basic

variable [Fintype ι]

/-- `(ν + v)/n` lies in the closed unit box indexed by `ν` (this uses `0 ≤ v i ≤ 1`). -/
theorem shifted_tag_mem_Icc (n : ℕ) [NeZero n] {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (ν : ι → ℤ) :
    (fun i => ((ν i : ℝ) + v i) / n) ∈
      BoxIntegral.Box.Icc (BoxIntegral.unitPartition.box n ν) := by
  rw [BoxIntegral.Box.Icc_eq_pi, Set.mem_univ_pi]
  intro i
  rw [Set.mem_Icc]
  constructor
  · simp only [BoxIntegral.unitPartition.box_lower]
    exact div_le_div_of_nonneg_right (by linarith [(hv i).1]) (Nat.cast_nonneg n)
  · simp only [BoxIntegral.unitPartition.box_upper]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    push_cast
    linarith [(hv i).2]

/-- The `v`-shifted refinement of `BoxIntegral.unitPartition.prepartition n B`: the boxes are the
same as those of the unit partition of `B`, but the tag attached to the box with index `ν` is the
shifted point `fun i => (ν i + v i)/n`. -/
def shiftedPrepartition (n : ℕ) [NeZero n] (B : BoxIntegral.Box ι) (v : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) : BoxIntegral.TaggedPrepartition B := by
  classical
  exact
    { toPrepartition := (BoxIntegral.unitPartition.prepartition n B).toPrepartition
      tag I := if h : ∃ ν ∈ BoxIntegral.unitPartition.admissibleIndex n B,
          I = BoxIntegral.unitPartition.box n ν
        then fun i => ((h.choose i : ℝ) + v i) / n
        else B.exists_mem.choose
      tag_mem_Icc I := by
        by_cases h : ∃ ν ∈ BoxIntegral.unitPartition.admissibleIndex n B,
            I = BoxIntegral.unitPartition.box n ν
        · rw [dite_eq_left h]
          exact BoxIntegral.Box.le_iff_Icc.mp
            (BoxIntegral.unitPartition.mem_admissibleIndex_iff.mp h.choose_spec.1)
            (shifted_tag_mem_Icc n hv h.choose)
        · rw [dite_eq_right h]
          exact BoxIntegral.Box.coe_subset_Icc B.exists_mem.choose_spec }

theorem shiftedPrepartition_toPrepartition (n : ℕ) [NeZero n] (B : BoxIntegral.Box ι)
    (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) :
    (shiftedPrepartition n B v hv).toPrepartition =
      (BoxIntegral.unitPartition.prepartition n B).toPrepartition := rfl

@[simp]
theorem shiftedPrepartition_boxes (n : ℕ) [NeZero n] (B : BoxIntegral.Box ι) (v : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) :
    (shiftedPrepartition n B v hv).boxes =
      (BoxIntegral.unitPartition.prepartition n B).boxes := rfl

theorem shiftedPrepartition_tag (n : ℕ) [NeZero n] {B : BoxIntegral.Box ι} {v : ι → ℝ}
    {hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1} {ν : ι → ℤ}
    (hν : ν ∈ BoxIntegral.unitPartition.admissibleIndex n B) :
    (shiftedPrepartition n B v hv).tag (BoxIntegral.unitPartition.box n ν) =
      fun i => ((ν i : ℝ) + v i) / n := by
  classical
  dsimp only [shiftedPrepartition]
  have hex : ∃ ν' ∈ BoxIntegral.unitPartition.admissibleIndex n B,
      BoxIntegral.unitPartition.box n ν = BoxIntegral.unitPartition.box n ν' := ⟨ν, hν, rfl⟩
  rw [dite_eq_left hex]
  funext i
  rw [show hex.choose = ν from
    (BoxIntegral.unitPartition.box_injective n hex.choose_spec.2).symm]

theorem shiftedPrepartition_isHenstock (n : ℕ) [NeZero n] (B : BoxIntegral.Box ι) (v : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) :
    (shiftedPrepartition n B v hv).IsHenstock := by
  intro I hI
  have hI' : I ∈ (BoxIntegral.unitPartition.prepartition n B).boxes := by
    rw [← shiftedPrepartition_boxes]
    exact hI
  obtain ⟨ν, hν, rfl⟩ := BoxIntegral.unitPartition.mem_prepartition_boxes_iff.mp hI'
  rw [shiftedPrepartition_tag n hν]
  exact shifted_tag_mem_Icc n hv ν

theorem shiftedPrepartition_isSubordinate (n : ℕ) [NeZero n] (B : BoxIntegral.Box ι)
    (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) {r : ℝ} (hr : 0 < r) (hn : 1 / (n : ℝ) ≤ r) :
    (shiftedPrepartition n B v hv).IsSubordinate (fun _ => ⟨r, hr⟩) := by
  intro J hJ
  have hJ' : J ∈ (BoxIntegral.unitPartition.prepartition n B).boxes := by
    rw [← shiftedPrepartition_boxes]
    exact hJ
  obtain ⟨ν, hν, rfl⟩ := BoxIntegral.unitPartition.mem_prepartition_boxes_iff.mp hJ'
  rw [shiftedPrepartition_tag n hν]
  refine fun x hx =>
    le_trans (Metric.dist_le_diam_of_mem (BoxIntegral.Box.isBounded_Icc _) hx ?_) ?_
  · exact shifted_tag_mem_Icc n hv ν
  · exact le_trans (BoxIntegral.unitPartition.diam_boxIcc n ν) hn

theorem shiftedPrepartition_isPartition (n : ℕ) [NeZero n] (B : BoxIntegral.Box ι)
    (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (hB : BoxIntegral.hasIntegralVertices B) :
    (shiftedPrepartition n B v hv).IsPartition := by
  show (shiftedPrepartition n B v hv).toPrepartition.IsPartition
  rw [shiftedPrepartition_toPrepartition]
  exact BoxIntegral.unitPartition.prepartition_isPartition n hB

/-- The value of the box-additive volume of a unit box applied to `1`. -/
theorem volume_toBoxAdditive_box_one (n : ℕ) [NeZero n] (ν : ι → ℤ) :
    (MeasureTheory.volume.toBoxAdditive.toSMul (BoxIntegral.unitPartition.box n ν)) (1 : ℝ)
      = 1 / (n : ℝ) ^ Fintype.card ι := by
  rw [BoxIntegral.BoxAdditiveMap.toSMul_apply, MeasureTheory.Measure.toBoxAdditive_apply,
    MeasureTheory.Measure.real_def, smul_eq_mul, mul_one]
  rw [BoxIntegral.unitPartition.volume_box]
  rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_pow, ENNReal.toReal_natCast]

/-- The integral sum of the indicator of `s` over the shifted unit partition of `B` is the number
of admissible indices whose shifted tag lies in `s`, divided by `n ^ card ι`. -/
theorem integralSum_shifted_eq_filter (n : ℕ) [NeZero n] (B : BoxIntegral.Box ι) (v : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (s : Set (ι → ℝ)) :
    BoxIntegral.integralSum (s.indicator fun _ => (1 : ℝ))
        MeasureTheory.volume.toBoxAdditive.toSMul (shiftedPrepartition n B v hv)
      = ((BoxIntegral.unitPartition.admissibleIndex n B).filter
            (fun ν => (fun i => ((ν i : ℝ) + v i) / n) ∈ s)).card
          / (n : ℝ) ^ Fintype.card ι := by
  classical
  have hterm : ∀ ν ∈ BoxIntegral.unitPartition.admissibleIndex n B,
      (MeasureTheory.volume.toBoxAdditive.toSMul (BoxIntegral.unitPartition.box n ν))
          (s.indicator (fun _ => (1 : ℝ))
            ((shiftedPrepartition n B v hv).tag (BoxIntegral.unitPartition.box n ν)))
        = (if (fun i => ((ν i : ℝ) + v i) / n) ∈ s then (1 : ℝ) else 0)
            / (n : ℝ) ^ Fintype.card ι := by
    intro ν hν
    rw [shiftedPrepartition_tag n hν]
    by_cases h : (fun i => ((ν i : ℝ) + v i) / n) ∈ s
    · rw [Set.indicator_of_mem h, ite_eq_left h, volume_toBoxAdditive_box_one n ν]
    · rw [Set.indicator_of_notMem h, ite_eq_right h, map_zero, zero_div]
  have hboxes : (shiftedPrepartition n B v hv).boxes
      = (BoxIntegral.unitPartition.admissibleIndex n B).image
          (BoxIntegral.unitPartition.box n) := by
    rw [shiftedPrepartition_boxes]
    rfl
  rw [BoxIntegral.integralSum, hboxes, Finset.sum_image]
  · rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, Finset.sum_boole]
  · intro a _ b _ hab
    exact BoxIntegral.unitPartition.box_injective n hab

/-- If every shifted tag lying in `s` has an admissible index, then the integral sum of the
indicator of `s` over the shifted partition is `#{z | (z + v)/n ∈ s} / n ^ card ι`. -/
theorem integralSum_shifted_eq_ncard (n : ℕ) [NeZero n] (B : BoxIntegral.Box ι) (v : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (s : Set (ι → ℝ))
    (hmem : ∀ z : ι → ℤ, (fun i => ((z i : ℝ) + v i) / n) ∈ s →
      z ∈ BoxIntegral.unitPartition.admissibleIndex n B) :
    BoxIntegral.integralSum (s.indicator fun _ => (1 : ℝ))
        MeasureTheory.volume.toBoxAdditive.toSMul (shiftedPrepartition n B v hv)
      = (({z : ι → ℤ | (fun i => ((z i : ℝ) + v i) / n) ∈ s} : Set (ι → ℤ)).ncard : ℝ)
          / (n : ℝ) ^ Fintype.card ι := by
  classical
  rw [integralSum_shifted_eq_filter n B v hv s]
  have hset : ({z : ι → ℤ | (fun i => ((z i : ℝ) + v i) / n) ∈ s} : Set (ι → ℤ))
      = ↑((BoxIntegral.unitPartition.admissibleIndex n B).filter
            (fun ν => (fun i => ((ν i : ℝ) + v i) / n) ∈ s)) := by
    ext z
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter]
    exact ⟨fun h => ⟨hmem z h, h⟩, fun h => h.2⟩
  rw [hset, Set.ncard_coe_finset]

/-- If every point of `s` is at distance at most `1` (in the sup metric) from `B`, then any index
`z` whose shifted tag lies in `s` is admissible for `B`. -/
theorem mem_admissibleIndex_of_shifted_mem {n : ℕ} [NeZero n] {B : BoxIntegral.Box ι}
    {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) {s : Set (ι → ℝ)}
    (hT : s + Metric.closedBall (0 : ι → ℝ) 1 ⊆ (↑B : Set (ι → ℝ)))
    (hn : 1 ≤ n) {z : ι → ℤ} (hz : (fun i => ((z i : ℝ) + v i) / n) ∈ s) :
    z ∈ BoxIntegral.unitPartition.admissibleIndex n B := by
  rw [BoxIntegral.unitPartition.mem_admissibleIndex_iff, ← BoxIntegral.Box.coe_subset_coe]
  intro x hx
  have htag : (fun i => ((z i : ℝ) + v i) / n) ∈
      BoxIntegral.Box.Icc (BoxIntegral.unitPartition.box n z) := shifted_tag_mem_Icc n hv z
  have hxI : x ∈ BoxIntegral.Box.Icc (BoxIntegral.unitPartition.box n z) :=
    BoxIntegral.Box.coe_subset_Icc hx
  have hdist : dist x (fun i => ((z i : ℝ) + v i) / n) ≤ 1 := by
    have h1 := Metric.dist_le_diam_of_mem
      (BoxIntegral.Box.isBounded_Icc (BoxIntegral.unitPartition.box n z)) hxI htag
    have h2 := BoxIntegral.unitPartition.diam_boxIcc n z
    have h3 : (1 : ℝ) / (n : ℝ) ≤ 1 := by
      rw [div_le_iff₀ (Nat.cast_pos.mpr (NeZero.pos n)), one_mul]
      exact_mod_cast hn
    linarith
  have hb : x - (fun i => ((z i : ℝ) + v i) / n) ∈ Metric.closedBall (0 : ι → ℝ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm]
    exact hdist
  have hxeq : x = (fun i => ((z i : ℝ) + v i) / n)
      + (x - (fun i => ((z i : ℝ) + v i) / n)) := by abel
  rw [hxeq]
  exact hT (Set.add_mem_add hz hb)

end Basic

/-- Shifted lattice-point count (the `v`-shifted analogue of Mathlib's
`tendsto_card_div_pow_atTop_volume`). Route: take a box `B` with integral vertices strictly
containing `s` with a positive margin, and use `BoxIntegral.hasIntegral_iff` for the Riemann
integrability of `Set.indicator s 1` on `B`. For each `n` build the tagged prepartition of `B` whose
boxes are the `unitPartition.box n ν` contained in `B` but whose tags are the *shifted* points
`fun i => (ν i + v i)/n`. Since `0 ≤ v i ≤ 1`, the shifted tag lies in `Box.Icc (box n ν)` so the
prepartition is Henstock, and `Icc (box n ν) ⊆ closedBall (tag) (1/n)`, so it is subordinate to any
function `≥ 1/n`. Its integral sum is exactly `(1/n^card ι) * #{z | (z + v)/n ∈ s}` (for `n ≥ 1`
and `s` at distance `≥ 1` from the boundary of `B`). Letting `ε → 0` gives the claim. -/
theorem shifted_card_div_pow_tendsto {ι : Type*} [Fintype ι] {s : Set (ι → ℝ)}
    (hs₁ : Bornology.IsBounded s) (hs₂ : MeasurableSet s)
    (hs₃ : MeasureTheory.volume (frontier s) = 0)
    (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) :
    Filter.Tendsto (fun n : ℕ =>
        (({z : ι → ℤ | (fun i => ((z i : ℝ) + v i) / n) ∈ s} : Set (ι → ℤ)).ncard : ℝ) /
          (n : ℝ) ^ Fintype.card ι) Filter.atTop (nhds (MeasureTheory.volume s).toReal) := by
  classical
  have hTb : Bornology.IsBounded (s + Metric.closedBall (0 : ι → ℝ) 1) :=
    hs₁.add Metric.isBounded_closedBall
  obtain ⟨B, hBint, hBsub⟩ := BoxIntegral.le_hasIntegralVertices_of_isBounded hTb
  have hsB : s ⊆ (↑B : Set (ι → ℝ)) := by
    intro x hx
    exact hBsub (by
      have hzero : (0 : ι → ℝ) ∈ Metric.closedBall (0 : ι → ℝ) 1 := by
        rw [Metric.mem_closedBall, dist_self]; norm_num
      have hx' : x = x + 0 := (add_zero x).symm
      rw [hx']
      exact Set.add_mem_add hx hzero)
  have hfbd : ∃ C : ℝ, ∀ x ∈ BoxIntegral.Box.Icc B,
      ‖(s.indicator fun _ => (1 : ℝ)) x‖ ≤ C := by
    refine ⟨1, fun x _ => ?_⟩
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem hxs]; simp
    · rw [Set.indicator_of_notMem hxs]; simp
  have hfcont : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (ι → ℝ)),
      ContinuousAt (s.indicator fun _ => (1 : ℝ)) x := by
    filter_upwards [(MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hs₃)] with x hx
    exact (continuous_const (y := (1 : ℝ))).continuousOn.continuousAt_indicator hx
  have hint : ∫ x in (↑B : Set (ι → ℝ)), (s.indicator fun _ => (1 : ℝ)) x
      = (MeasureTheory.volume s).toReal := by
    rw [MeasureTheory.setIntegral_indicator hs₂, MeasureTheory.setIntegral_const]
    have hBs : (↑B : Set (ι → ℝ)) ∩ s = s := Set.inter_eq_right.mpr hsB
    rw [hBs, MeasureTheory.Measure.real_def, smul_eq_mul, mul_one]
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨r, hr₁, hr₂⟩ := (BoxIntegral.hasIntegral_iff.mp
      (MeasureTheory.AEContinuous.hasBoxIntegral
        (MeasureTheory.volume : MeasureTheory.Measure (ι → ℝ))
        hfbd hfcont BoxIntegral.IntegrationParams.Riemann)) (ε / 2) (half_pos hε)
  refine ⟨⌈((r 0 0 : ℝ))⁻¹⌉₊, fun n hn => ?_⟩
  have hnpos : 0 < n :=
    (Nat.ceil_pos.mpr (inv_pos.mpr (r 0 0).prop)).trans_le hn
  have hnez : NeZero n := ⟨Nat.ne_zero_iff_zero_lt.mpr hnpos⟩
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hsub : (shiftedPrepartition n B v hv).IsSubordinate
      (fun _ => ⟨(r 0 0 : ℝ), (r 0 0).prop⟩) := by
    apply shiftedPrepartition_isSubordinate n B v hv (r 0 0).prop
    rw [one_div, inv_le_comm₀ (Nat.cast_pos.mpr hnpos) (r 0 0).prop]
    exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn)
  have hsub' : (shiftedPrepartition n B v hv).IsSubordinate (r 0) :=
    hsub.mono' fun J _ => le_of_eq (by
      rw [show r 0 (BoxIntegral.TaggedPrepartition.tag (shiftedPrepartition n B v hv) J)
        = r 0 0 from hr₁ 0 rfl _])
  have hhen : (shiftedPrepartition n B v hv).IsHenstock := shiftedPrepartition_isHenstock n B v hv
  have hpart : (shiftedPrepartition n B v hv).IsPartition :=
    shiftedPrepartition_isPartition n B v hv hBint
  have hmem := hr₂ 0 (shiftedPrepartition n B v hv)
      ⟨hsub', fun _ => hhen, fun h => by
          simp only [BoxIntegral.IntegrationParams.Riemann, Bool.false_eq_true] at h,
        fun h => by
          simp only [BoxIntegral.IntegrationParams.Riemann, Bool.false_eq_true] at h⟩ hpart
  have hsum := integralSum_shifted_eq_ncard n B v hv s
      (fun z hz => mem_admissibleIndex_of_shifted_mem hv hBsub hn1 hz)
  have hgoal : dist ((({z : ι → ℤ | (fun i => ((z i : ℝ) + v i) / n) ∈ s}
          : Set (ι → ℤ)).ncard : ℝ) / (n : ℝ) ^ Fintype.card ι)
        ((MeasureTheory.volume s).toReal)
      = dist (BoxIntegral.integralSum (s.indicator fun _ => (1 : ℝ))
            MeasureTheory.volume.toBoxAdditive.toSMul (shiftedPrepartition n B v hv))
          (∫ x in (↑B : Set (ι → ℝ)), (s.indicator fun _ => (1 : ℝ)) x) := by
    rw [hsum, hint]
  rw [hgoal]
  exact lt_of_le_of_lt hmem (half_lt_self hε)

end

end Work.HP.DNC
