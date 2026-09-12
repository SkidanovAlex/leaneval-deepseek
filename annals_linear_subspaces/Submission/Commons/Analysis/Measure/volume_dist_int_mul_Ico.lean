import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Int.Star
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular

namespace Commons.Analysis.Measure

open MeasureTheory Set

/-- For `y : ℝ`, the distance of `(y : AddCircle 1)` to `0` is `< δ` exactly when `y` is at
distance `< δ` from some integer. -/
private lemma norm_coe_addCircle_one_lt_iff (y : ℝ) (δ : ℝ) :
    ‖(y : AddCircle (1:ℝ))‖ < δ ↔ ∃ b : ℤ, |y - (b : ℝ)| < δ := by
  rw [QuotientAddGroup.norm_mk (S := AddSubgroup.zmultiples (1:ℝ))]
  rw [Metric.infDist_lt_iff
    (show (AddSubgroup.zmultiples (1:ℝ) : Set ℝ).Nonempty from ⟨0, by simp⟩)]
  constructor
  · rintro ⟨z, hz, hzd⟩
    obtain ⟨b, hb⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
    refine ⟨b, ?_⟩
    rw [← hb] at hzd
    simpa [Real.dist_eq, zsmul_eq_mul] using hzd
  · rintro ⟨b, hb⟩
    refine ⟨(b : ℝ), ?_, ?_⟩
    · exact (AddSubgroup.mem_zmultiples_iff.mpr ⟨b, by simp⟩ :
        ((b:ℤ):ℝ) ∈ AddSubgroup.zmultiples (1:ℝ))
    · simpa [Real.dist_eq] using hb

/-- The measure of the set of `t ∈ [0,1)` such that `t + c` is within `δ` of an integer, for
`δ ≤ 1/2`, equals `2δ`.  This is the "circle" computation, done via the additive circle. -/
private lemma volume_circle_Ico (c δ : ℝ) (hδ : δ ≤ 1 / 2) :
    volume {t : ℝ | t ∈ Ico (0:ℝ) 1 ∧ ‖((t + c : ℝ) : AddCircle (1:ℝ))‖ < δ}
      = ENNReal.ofReal (2 * δ) := by
  set B : Set (AddCircle (1:ℝ)) := Metric.ball (-((c : ℝ) : AddCircle (1:ℝ))) δ with hB
  have hBmeas : MeasurableSet B := measurableSet_ball
  have hdist : ∀ t : ℝ, dist (t : AddCircle (1:ℝ)) (-((c:ℝ) : AddCircle (1:ℝ)))
      = ‖((t + c : ℝ) : AddCircle (1:ℝ))‖ := by
    intro t
    rw [dist_eq_norm, sub_neg_eq_add, ← AddCircle.coe_add]
  have hset : {t : ℝ | t ∈ Ico (0:ℝ) 1 ∧ ‖((t + c : ℝ) : AddCircle (1:ℝ))‖ < δ}
      = ((↑) : ℝ → AddCircle (1:ℝ)) ⁻¹' B ∩ Ico (0:ℝ) 1 := by
    ext t
    simp only [Set.mem_ofPred_eq, mem_inter_iff, mem_preimage, hB]
    rw [Metric.mem_ball, hdist t]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [hset]
  have hcongr : volume.restrict (Ico (0:ℝ) 1) = volume.restrict (Ioc (0:ℝ) 1) :=
    MeasureTheory.restrict_Ico_eq_restrict_Ioc (μ := (volume : Measure ℝ))
  have h1 : volume (((↑) : ℝ → AddCircle (1:ℝ)) ⁻¹' B ∩ Ico (0:ℝ) 1)
          = volume (((↑) : ℝ → AddCircle (1:ℝ)) ⁻¹' B ∩ Ioc (0:ℝ) 1) := by
    rw [← Measure.restrict_apply' measurableSet_Ico, hcongr,
      Measure.restrict_apply' measurableSet_Ioc]
  rw [h1]
  have hmap : Measure.map ((↑) : ℝ → AddCircle (1:ℝ)) (volume.restrict (Ioc (0:ℝ) 1))
      = volume := by
    have := (AddCircle.measurePreserving_mk (T := 1) (0:ℝ)).map_eq
    simpa using this
  have hcoe_meas : Measurable ((↑) : ℝ → AddCircle (1:ℝ)) :=
    ((AddCircle.measurePreserving_mk (T := 1) (0:ℝ)).measurable)
  have h2 : volume (((↑) : ℝ → AddCircle (1:ℝ)) ⁻¹' B ∩ Ioc (0:ℝ) 1) = volume B := by
    rw [← Measure.restrict_apply' measurableSet_Ioc, ← hmap,
      Measure.map_apply hcoe_meas hBmeas]
  rw [h2, hB]
  rw [← measure_congr
    (AddCircle.closedBall_ae_eq_ball (x := -((c:ℝ) : AddCircle (1:ℝ))) (ε := δ))]
  rw [AddCircle.volume_closedBall (1:ℝ) δ]
  rw [min_eq_right (by linarith)]

/-- If `F ⊆ ℝ` is invariant under `y ↦ y + 1` then so is it under `y ↦ y + n` for `n : ℕ`. -/
private lemma mem_add_nat_iff {F : Set ℝ} (hF : ∀ y, y ∈ F ↔ y + 1 ∈ F) (n : ℕ) (y : ℝ) :
    (y + (n:ℝ)) ∈ F ↔ y ∈ F := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hcast : (y + ((k+1 : ℕ) : ℝ)) = (y + (k:ℝ)) + 1 := by push_cast; ring
    rw [hcast, ← hF (y + (k:ℝ)), ih]

/-- For a `1`-periodic measurable set `F`, the measure of `F ∩ [0,n)` is `n` times the measure
of `F ∩ [0,1)`. -/
private lemma volume_inter_Ico_nat_mul (F : Set ℝ) (hF : ∀ y, y ∈ F ↔ y + 1 ∈ F)
    (hFmeas : MeasurableSet F) (n : ℕ) :
    volume (F ∩ Ico (0:ℝ) (n:ℝ)) = n • volume (F ∩ Ico (0:ℝ) 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hsplit : F ∩ Ico (0:ℝ) ((k+1 : ℕ) : ℝ)
        = (F ∩ Ico (0:ℝ) (k:ℝ)) ∪ (F ∩ Ico (k:ℝ) (k+1:ℝ)) := by
      ext x
      simp only [mem_inter_iff, mem_Ico, mem_union, Nat.cast_succ]
      constructor
      · rintro ⟨hxF, h0, hlt⟩
        rcases lt_or_ge x (k:ℝ) with h | h
        · exact Or.inl ⟨hxF, h0, h⟩
        · exact Or.inr ⟨hxF, h, by linarith⟩
      · rintro (⟨hxF, h0, hlt⟩ | ⟨hxF, hge, hlt⟩)
        · exact ⟨hxF, h0, by linarith⟩
        · exact ⟨hxF, by linarith [show (0:ℝ) ≤ (k:ℝ) from Nat.cast_nonneg k], hlt⟩
    have hdisj : Disjoint (F ∩ Ico (0:ℝ) (k:ℝ)) (F ∩ Ico (k:ℝ) (k+1:ℝ)) := by
      rw [Set.disjoint_left]
      rintro x ⟨-, hx1, hx2⟩ ⟨-, hy1, hy2⟩
      linarith
    have hshift : volume (F ∩ Ico (k:ℝ) (k+1:ℝ)) = volume (F ∩ Ico (0:ℝ) 1) := by
      have key : (fun y : ℝ => y + (k:ℝ)) ⁻¹' (F ∩ Ico (k:ℝ) (k+1:ℝ))
          = F ∩ Ico (0:ℝ) 1 := by
        ext y
        simp only [mem_preimage, mem_inter_iff, mem_Ico]
        constructor
        · rintro ⟨hyF, h1, h2⟩
          exact ⟨(mem_add_nat_iff hF k y).mp hyF, by linarith, by linarith⟩
        · rintro ⟨hyF, h0, h1⟩
          exact ⟨(mem_add_nat_iff hF k y).mpr hyF, by linarith, by linarith⟩
      have hpre := measure_preimage_add_right (μ := volume) (k:ℝ)
        (F ∩ Ico (k:ℝ) (k+1:ℝ))
      rw [key] at hpre
      exact hpre.symm
    rw [hsplit, measure_union hdisj (hFmeas.inter measurableSet_Ico), ih, hshift, succ_nsmul]

/-- The main computation for a positive integer multiple: for `1 ≤ n`, the measure of the set of
`x ∈ [0,1)` with `n x + c` within `δ` of an integer is `2δ`. -/
private lemma volume_nat_mul_Ico (n : ℕ) (hn : 1 ≤ n) (c δ : ℝ) (hδ1 : δ ≤ 1 / 2) :
    volume {x : ℝ | x ∈ Ico (0:ℝ) 1 ∧ ∃ b : ℤ, |(n:ℝ) * x + c - (b:ℝ)| < δ}
      = ENNReal.ofReal (2 * δ) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  set F : Set ℝ := {y : ℝ | ‖((y + c : ℝ) : AddCircle (1:ℝ))‖ < δ} with hF
  have hFmeas : MeasurableSet F := by
    have hcont : Continuous fun y : ℝ => ‖((y + c : ℝ) : AddCircle (1:ℝ))‖ := by fun_prop
    exact (isOpen_lt hcont continuous_const).measurableSet
  have hFper : ∀ y, y ∈ F ↔ y + 1 ∈ F := by
    intro y
    have hper : ((1:ℝ) : AddCircle (1:ℝ)) = 0 := AddCircle.coe_period (1:ℝ)
    have hyc : ((y + 1 + c : ℝ) : AddCircle (1:ℝ)) = ((y + c : ℝ) : AddCircle (1:ℝ)) := by
      rw [show (y + 1 + c : ℝ) = (y + c) + 1 by ring, AddCircle.coe_add, hper, add_zero]
    rw [hF]
    simp only [Set.mem_ofPred_eq, hyc]
  have hmul : ∀ x : ℝ, (n:ℝ) * x ∈ Ico (0:ℝ) (n:ℝ) ↔ x ∈ Ico (0:ℝ) 1 := by
    intro x
    rw [mem_Ico, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(mul_nonneg_iff_of_pos_left hnpos).mp h1, ?_⟩
      nlinarith
    · rintro ⟨h1, h2⟩
      refine ⟨(mul_nonneg_iff_of_pos_left hnpos).mpr h1, ?_⟩
      nlinarith
  have hS : {x : ℝ | x ∈ Ico (0:ℝ) 1 ∧ ∃ b : ℤ, |(n:ℝ) * x + c - (b:ℝ)| < δ}
      = (fun x : ℝ => (n:ℝ) * x) ⁻¹' (F ∩ Ico (0:ℝ) (n:ℝ)) := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_preimage, mem_inter_iff]
    rw [hF]
    simp only [Set.mem_ofPred_eq]
    rw [norm_coe_addCircle_one_lt_iff ((n:ℝ) * x + c) δ]
    constructor
    · rintro ⟨hx1, hb⟩
      exact ⟨hb, (hmul x).mpr hx1⟩
    · rintro ⟨hb, hx2⟩
      exact ⟨(hmul x).mp hx2, hb⟩
  have hcirc : volume (F ∩ Ico (0:ℝ) 1) = ENNReal.ofReal (2 * δ) := by
    rw [hF]
    rw [show {y : ℝ | ‖((y + c : ℝ) : AddCircle (1:ℝ))‖ < δ} ∩ Ico (0:ℝ) 1
        = {t : ℝ | t ∈ Ico (0:ℝ) 1 ∧ ‖((t + c : ℝ) : AddCircle (1:ℝ))‖ < δ} from by
      ext t; simp only [Set.mem_ofPred_eq, mem_inter_iff]; tauto]
    exact volume_circle_Ico c δ hδ1
  rw [hS, Real.volume_preimage_mul_left (ne_of_gt hnpos),
      volume_inter_Ico_nat_mul F hFper hFmeas n, hcirc]
  rw [abs_of_pos (inv_pos.mpr hnpos), nsmul_eq_mul, ← ENNReal.ofReal_natCast n, ← mul_assoc,
      ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hnpos)), inv_mul_cancel₀ (ne_of_gt hnpos),
      ENNReal.ofReal_one, one_mul]

theorem volume_dist_int_mul_Ico (a : ℤ) (c δ : ℝ) (ha : a ≠ 0) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) :
    MeasureTheory.volume {x : ℝ | x ∈ Set.Ico (0:ℝ) 1 ∧
      ∃ b : ℤ, |(a : ℝ) * x + c - (b : ℝ)| < δ} = ENNReal.ofReal (2 * δ) := by
  have _hδ0 : 0 ≤ δ := hδ0
  have hn1 : 1 ≤ a.natAbs := by
    have : 0 < a.natAbs := Int.natAbs_pos.mpr ha
    omega
  rcases lt_trichotomy a 0 with hneg | hzero | hpos
  · -- `a < 0`
    have hN : (((a.natAbs : ℕ)) : ℝ) = -(a : ℝ) := by
      have h : (((a.natAbs : ℕ)) : ℤ) = -a := by
        rw [← Int.natAbs_neg a]
        exact Int.natAbs_of_nonneg (by linarith : (0:ℤ) ≤ -a)
      rw [← Int.cast_natCast (R := ℝ), h, Int.cast_neg]
    have ha_eq : (a : ℝ) = -(((a.natAbs : ℕ)) : ℝ) := by linarith
    have hset : {x : ℝ | x ∈ Ico (0:ℝ) 1 ∧ ∃ b : ℤ, |(a : ℝ) * x + c - (b : ℝ)| < δ}
        = {x : ℝ | x ∈ Ico (0:ℝ) 1 ∧
            ∃ b : ℤ, |(((a.natAbs : ℕ)) : ℝ) * x + (-c) - (b : ℝ)| < δ} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hx, b, hb⟩
        refine ⟨hx, -b, ?_⟩
        rw [ha_eq] at hb
        have heq : (-(((a.natAbs : ℕ)) : ℝ)) * x + c - (b : ℝ)
            = -(((((a.natAbs : ℕ)) : ℝ)) * x + (-c) - (((-b : ℤ)) : ℝ)) := by
          push_cast; ring
        rw [heq, abs_neg] at hb
        exact hb
      · rintro ⟨hx, b, hb⟩
        refine ⟨hx, -b, ?_⟩
        rw [ha_eq]
        have heq : (-(((a.natAbs : ℕ)) : ℝ)) * x + c - (((-b : ℤ)) : ℝ)
            = -(((((a.natAbs : ℕ)) : ℝ)) * x + (-c) - (b : ℝ)) := by
          push_cast; ring
        rw [heq, abs_neg]
        exact hb
    rw [hset]
    exact volume_nat_mul_Ico a.natAbs hn1 (-c) δ hδ1
  · exact absurd hzero ha
  · -- `0 < a`
    have hN : (((a.natAbs : ℕ)) : ℝ) = (a : ℝ) := by
      have h : (((a.natAbs : ℕ)) : ℤ) = a := Int.natAbs_of_nonneg hpos.le
      rw [← Int.cast_natCast (R := ℝ), h]
    have hset : {x : ℝ | x ∈ Ico (0:ℝ) 1 ∧ ∃ b : ℤ, |(a : ℝ) * x + c - (b : ℝ)| < δ}
        = {x : ℝ | x ∈ Ico (0:ℝ) 1 ∧
            ∃ b : ℤ, |(((a.natAbs : ℕ)) : ℝ) * x + c - (b : ℝ)| < δ} := by
      rw [hN]
    rw [hset]
    exact volume_nat_mul_Ico a.natAbs hn1 c δ hδ1

end Commons.Analysis.Measure