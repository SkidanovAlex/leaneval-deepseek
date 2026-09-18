import Mathlib.NumberTheory.WellApproximable
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular

open MeasureTheory Set Metric
open scoped ENNReal Topology Pointwise

namespace Commons.NumberTheory.DuffinSchaeffer

/-- For `0 < a < q` the point `a / q` on the unit circle has norm at least `1 / q`. -/
private lemma norm_coe_div_natCast_ge (q a : ℕ) (ha_pos : 0 < a) (ha_lt : a < q) :
    (1 : ℝ) / (q : ℝ) ≤ ‖(((a : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)‖ := by
  have hnorm : ‖(((a : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)‖ =
      ((min (a % q) (q - a % q) : ℕ) : ℝ) / (q : ℝ) := by
    simpa using (AddCircle.norm_div_natCast (p := (1 : ℝ)) (m := a) (n := q))
  rw [hnorm]
  have haq : 0 < q := lt_of_le_of_lt (Nat.zero_le a) ha_lt
  have hmin : (1 : ℕ) ≤ min (a % q) (q - a % q) := by
    rw [Nat.mod_eq_of_lt ha_lt]
    have hqa : 1 ≤ q - a := by omega
    exact le_min ha_pos hqa
  have hminR : (1 : ℝ) ≤ ((min (a % q) (q - a % q) : ℕ) : ℝ) := by
    exact_mod_cast hmin
  have hqR : 0 < (q : ℝ) := by exact_mod_cast haq
  exact (div_le_div_iff₀ hqR hqR).2 (mul_le_mul_of_nonneg_right hminR hqR.le)

/-- If `m < m' < q` then the distance between `m / q` and `m' / q` on the unit circle is at
least `1 / q`. -/
private lemma dist_coe_div_natCast_ge_of_lt (q m m' : ℕ) (_hm : m < q) (hm' : m' < q)
    (hmm' : m < m') :
    (1 : ℝ) / (q : ℝ) ≤
      dist (((m : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)
        (((m' : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) := by
  let a := m' - m
  have ha_pos : 0 < a := Nat.sub_pos_of_lt hmm'
  have ha_lt : a < q := by
    calc
      a = m' - m := rfl
      _ ≤ m' := Nat.sub_le m' m
      _ < q := hm'
  have hcast : (m' : ℝ) - (m : ℝ) = (a : ℝ) := by
    dsimp [a]
    exact (Nat.cast_sub (Nat.le_of_lt hmm')).symm
  have hdiff : ((m' : ℝ) / (q : ℝ) : ℝ) - ((m : ℝ) / (q : ℝ) : ℝ) = (a : ℝ) / (q : ℝ) := by
    rw [← sub_div]
    rw [hcast]
  rw [dist_eq_norm]
  rw [← neg_sub]
  rw [norm_neg]
  rw [show (((m' : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) - (((m : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) =
      (((a : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) by
    rw [← AddCircle.coe_sub]
    exact congrArg (fun t : ℝ => (t : UnitAddCircle)) hdiff]
  exact norm_coe_div_natCast_ge q a ha_pos ha_lt

/-- Distinct reduced fractions with the same denominator `q` are at least `1 / q` apart on the
unit circle. -/
private lemma dist_coe_div_natCast_ge (q m m' : ℕ) (hm : m < q) (hm' : m' < q) (hne : m ≠ m') :
    (1 : ℝ) / (q : ℝ) ≤
      dist (((m : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)
        (((m' : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) := by
  rcases lt_or_gt_of_ne hne with hmm' | hm'm
  · exact dist_coe_div_natCast_ge_of_lt q m m' hm hm' hmm'
  · rw [dist_comm]
    exact dist_coe_div_natCast_ge_of_lt q m' m hm' hm hm'm

/-- The volume of a ball in the unit circle of radius `r` is `2r`, provided `2r ≤ 1`. -/
private lemma volume_ball_eq_ofReal_two_mul (x : UnitAddCircle) {r : ℝ} (hr : 2 * r ≤ 1) :
    volume (ball x r) = ENNReal.ofReal (2 * r) := by
  calc
    volume (ball x r) = volume (closedBall x r) := by
      exact (MeasureTheory.measure_congr
        (AddCircle.closedBall_ae_eq_ball (T := (1 : ℝ)) (x := x) (ε := r))).symm
    _ = ENNReal.ofReal (min (1 : ℝ) (2 * r)) := by
      simpa using (AddCircle.volume_closedBall (T := (1 : ℝ)) (x := x) (ε := r))
    _ = ENNReal.ofReal (2 * r) := by rw [min_eq_right hr]

/-- A ball of radius `r ≤ δ` around the reduced fraction `m / q` is contained in the order-`q`
approximation set. -/
private lemma ball_subset_approxAddOrderOf {q : ℕ} (hq : 0 < q) {m : ℕ} (hm : m < q)
    (hgc : m.gcd q = 1) {δ r : ℝ} (hrδ : r ≤ δ) :
    ball (((m : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) r ⊆ approxAddOrderOf UnitAddCircle q δ := by
  intro x hx
  rw [UnitAddCircle.mem_approxAddOrderOf_iff hq]
  refine ⟨m, hm, hgc, ?_⟩
  have hx' : ‖x - (((m : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)‖ < r := by
    simpa [dist_eq_norm, Metric.mem_ball] using hx
  exact lt_of_lt_of_le hx' hrδ

/-- Arithmetic: `φ(q) * ofReal (2r) = ofReal (2 * φ(q) * r)`. -/
private lemma totient_ofReal_mul_two_mul (n : ℕ) (r : ℝ) :
    ((n.totient : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 * r) = ENNReal.ofReal (2 * (n.totient : ℝ) * r) := by
  rw [show 2 * (n.totient : ℝ) * r = 2 * ((n.totient : ℝ) * r) by ring]
  conv_rhs => rw [ENNReal.ofReal_mul zero_le_two]
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  simp only [ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_mul zero_le_two]
  rw [← mul_assoc]
  rw [mul_comm (↑n.totient : ℝ≥0∞) (ENNReal.ofReal (2 : ℝ))]
  rw [mul_assoc]

theorem approxAddOrderOf_volume_ge_min (q : ℕ) (δ : ℝ) :
    ENNReal.ofReal (2 * (q.totient : ℝ) * min δ (1 / (2 * (q : ℝ)))) ≤
      MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δ) := by
  let r : ℝ := min δ (1 / (2 * (q : ℝ)))
  have hr_le_δ : r ≤ δ := min_le_left _ _
  change ENNReal.ofReal (2 * (q.totient : ℝ) * r) ≤
    MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δ)
  by_cases hq0 : q = 0
  · subst q
    simp
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    by_cases hr0 : r ≤ 0
    · have hle0 : 2 * (q.totient : ℝ) * r ≤ 0 := by
        have ht : 0 ≤ (q.totient : ℝ) := by exact_mod_cast Nat.zero_le _
        have htwo : 0 ≤ (2 : ℝ) := by norm_num
        exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg htwo ht) hr0
      have hof : ENNReal.ofReal (2 * (q.totient : ℝ) * r) = 0 := ENNReal.ofReal_eq_zero.mpr hle0
      rw [hof]
      exact zero_le
    · have hr_pos : 0 < r := lt_of_not_ge hr0
      have hr_le_half : r ≤ 1 / (2 * (q : ℝ)) := min_le_right _ _
      let F := (Finset.range q).filter (fun m : ℕ => m.gcd q = 1)
      let c : ℕ → UnitAddCircle := fun m => (((m : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)
      let B : ℕ → Set UnitAddCircle := fun m => ball (c m) r
      have h2r_le_one : 2 * r ≤ 1 := by
        have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
        have hqR1 : (1 : ℝ) ≤ (q : ℝ) := by
          exact_mod_cast (Nat.succ_le_iff.mpr hq)
        have hle2 : 2 * r ≤ 2 * (1 / (2 * (q : ℝ))) := by
          exact mul_le_mul_of_nonneg_left hr_le_half (by norm_num)
        have hfrac : 2 * (1 / (2 * (q : ℝ))) = 1 / (q : ℝ) := by
          field_simp [hqR.ne']
        rw [hfrac] at hle2
        have hle3 : (1 : ℝ) / (q : ℝ) ≤ 1 := by
          exact (div_le_iff₀ hqR).2 (by simpa using hqR1)
        exact le_trans hle2 hle3
      -- containment of the union of balls
      have hsubset : (⋃ m ∈ F, B m) ⊆ approxAddOrderOf UnitAddCircle q δ := by
        intro x hx
        rcases mem_iUnion₂.mp hx with ⟨m, hmF, hmx⟩
        have hBsub : B m ⊆ approxAddOrderOf UnitAddCircle q δ := by
          have hmq : m < q := by simpa [F] using (Finset.mem_filter.mp hmF).1
          have hgc : m.gcd q = 1 := by simpa [F] using (Finset.mem_filter.mp hmF).2
          simpa [B, c] using ball_subset_approxAddOrderOf (q := q) hq hmq hgc hr_le_δ
        exact hBsub hmx
      -- pairwise disjointness of the balls
      have hdisj : Set.PairwiseDisjoint (↑F : Set ℕ) B := by
        intro m hm m' hm' hne
        have hmq : m < q ∧ m.gcd q = 1 := by
          have h := Finset.mem_filter.mp (Finset.mem_coe.mp hm)
          simpa [F] using h
        have hm'q : m' < q ∧ m'.gcd q = 1 := by
          have h := Finset.mem_filter.mp (Finset.mem_coe.mp hm')
          simpa [F] using h
        have hd : (1 : ℝ) / (q : ℝ) ≤ dist (c m) (c m') := by
          simpa [c] using dist_coe_div_natCast_ge q m m' hmq.1 hm'q.1 hne
        have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
        have hle2 : 2 * r ≤ 2 * (1 / (2 * (q : ℝ))) := by
          exact mul_le_mul_of_nonneg_left hr_le_half (by norm_num)
        have hfrac : 2 * (1 / (2 * (q : ℝ))) = 1 / (q : ℝ) := by
          field_simp [hqR.ne']
        have h2r : 2 * r ≤ (1 : ℝ) / (q : ℝ) := by
          rwa [← hfrac]
        have hrr : r + r ≤ dist (c m) (c m') := by nlinarith [h2r, hd]
        exact ball_disjoint_ball hrr
      -- measure of each ball
      have hvolb : ∀ m ∈ F, volume (B m) = ENNReal.ofReal (2 * r) := by
        intro m hm
        simpa [B, c] using volume_ball_eq_ofReal_two_mul (c m) h2r_le_one
      have hmeas : ∀ m ∈ F, MeasurableSet (B m) := by
        intro m hm
        exact measurableSet_ball
      have hvolF : volume (⋃ m ∈ F, B m) = ∑ m ∈ F, volume (B m) :=
        MeasureTheory.measure_biUnion_finset hdisj hmeas
      have hvolsum : (∑ m ∈ F, volume (B m)) = ENNReal.ofReal (2 * (q.totient : ℝ) * r) := by
        calc
          (∑ m ∈ F, volume (B m)) = ∑ m ∈ F, ENNReal.ofReal (2 * r) := by
            exact Finset.sum_congr rfl (fun m hm => hvolb m hm)
          _ = ENNReal.ofReal (2 * (q.totient : ℝ) * r) := by
            have hcard : F.card = q.totient := by
              dsimp [F]
              rw [Nat.totient_eq_card_coprime]
              congr 1
              apply Finset.filter_congr
              intro m hm
              exact (Nat.coprime_iff_gcd_eq_one.symm).trans Nat.coprime_comm
            rw [Finset.sum_const]
            rw [nsmul_eq_mul]
            rw [hcard]
            exact totient_ofReal_mul_two_mul q r
      -- assemble
      have hmain : ENNReal.ofReal (2 * (q.totient : ℝ) * r) ≤
          MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δ) := by
        calc
          ENNReal.ofReal (2 * (q.totient : ℝ) * r) = ∑ m ∈ F, volume (B m) := hvolsum.symm
          _ = volume (⋃ m ∈ F, B m) := hvolF.symm
          _ ≤ MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δ) :=
            measure_mono (μ := (volume : Measure UnitAddCircle)) hsubset
      exact hmain

end Commons.NumberTheory.DuffinSchaeffer