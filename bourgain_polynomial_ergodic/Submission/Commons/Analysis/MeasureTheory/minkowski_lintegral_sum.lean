import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.MeanInequalities

open MeasureTheory
open scoped ENNReal

namespace Commons.Analysis.MeasureTheory

/-- **Hölder's inequality for finite sums** of `ℝ≥0∞`-valued functions. -/
theorem ennreal_finset_sum_mul_le_holder {ι : Type*} (t : Finset ι) (x y : ι → ℝ≥0∞) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    ∑ i ∈ t, x i * y i ≤ (∑ i ∈ t, x i ^ p) ^ (1 / p) * (∑ i ∈ t, y i ^ q) ^ (1 / q) := by
  letI : MeasurableSpace ι := ⊤
  have hxy := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count.restrict (t : Set ι)) hpq
    (f := x) (g := y) AEMeasurable.of_discrete AEMeasurable.of_discrete
  rw [lintegral_finset] at hxy
  rw [lintegral_finset] at hxy
  rw [lintegral_finset] at hxy
  simpa using hxy

/-- For `a ≠ ⊤` and `1 < p`, `a ^ p = a ^ (p - 1) * a`. -/
lemma rpow_pred_mul_loc {a : ℝ≥0∞} {p : ℝ} (ha : a ≠ ⊤) (hp : 1 < p) :
    a ^ p = a ^ (p - 1) * a := by
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [ENNReal.zero_rpow_of_pos (by linarith : (0:ℝ) < p),
        ENNReal.zero_rpow_of_pos (by linarith : (0:ℝ) < p - 1), zero_mul]
  · have h := ENNReal.rpow_add (x := a) (p - 1) 1 ha0 ha
    rw [ENNReal.rpow_one] at h
    rw [← h, sub_add_cancel]

theorem minkowski_lintegral_sum {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {ι : Type*} (t : Finset ι) (F : ι → α → ENNReal) (p : ℝ) (hp : 1 ≤ p)
    (hF : ∀ i, AEMeasurable (F i) μ) :
    ENNReal.rpow (Finset.sum t (fun i => ENNReal.rpow (MeasureTheory.lintegral μ (fun a => F i a)) p)) (1 / p)
      ≤ MeasureTheory.lintegral μ (fun a => ENNReal.rpow (Finset.sum t (fun i => ENNReal.rpow (F i a) p)) (1 / p)) := by
  rcases eq_or_lt_of_le hp with hp1 | hp1
  · -- p = 1
    rw [← hp1]
    rw [one_div_one]
    change (∑ i ∈ t, (∫⁻ a, F i a ∂μ) ^ (1:ℝ)) ^ (1:ℝ)
        ≤ ∫⁻ a, (∑ i ∈ t, (F i a) ^ (1:ℝ)) ^ (1:ℝ) ∂μ
    simp only [ENNReal.rpow_one]
    rw [lintegral_finsetSum' t (fun i _ => hF i)]
  · -- 1 < p
    let G : ι → ℝ≥0∞ := fun i => ∫⁻ a, F i a ∂μ
    let S : ℝ≥0∞ := ∑ i ∈ t, (G i) ^ p
    let H : α → ℝ≥0∞ := fun a => ∑ i ∈ t, (F i a) ^ p
    let R : ℝ≥0∞ := ∫⁻ a, (H a) ^ (1 / p) ∂μ
    set q : ℝ := p / (p - 1) with hq
    have hpq : p.HolderConjugate q := by
      rw [Real.holderConjugate_iff]
      refine ⟨hp1, ?_⟩
      rw [hq, inv_div]
      field_simp
      ring
    have hsub : (p - 1) * q = p := hpq.sub_one_mul_conj
    have hinv : 1 / p + 1 / q = 1 := by
      rw [one_div, one_div]
      exact hpq.inv_add_inv_eq_one
    have hp_pos : 0 < p := lt_trans zero_lt_one hp1
    have hq_pos : 0 < q := by rw [hq]; exact div_pos hp_pos (by linarith)
    have h1p_pos : 0 < 1 / p := div_pos one_pos hp_pos
    have h1q_pos : 0 < 1 / q := div_pos one_pos hq_pos
    suffices hmain : S ^ (1 / p) ≤ R by
      exact hmain
    rcases eq_top_or_lt_top S with hStop | hSlt
    · -- S = ⊤
      have hStop' : (∑ i ∈ t, (G i) ^ p) = ⊤ := hStop
      obtain ⟨i, hi, hipt⟩ := ENNReal.sum_eq_top.mp hStop'
      have hRtop : R = ⊤ := by
        refine le_antisymm le_top ?_
        have hGtop : G i = ⊤ := by
          rcases (ENNReal.rpow_eq_top_iff.mp hipt) with ⟨_, hpneg⟩ | ⟨htop, _⟩
          · exact absurd hpneg (not_lt.mpr hp_pos.le)
          · exact htop
        calc R = ∫⁻ a, (H a) ^ (1 / p) ∂μ := rfl
          _ ≥ ∫⁻ a, F i a ∂μ := by
              apply lintegral_mono
              intro a
              have hle : (F i a) ^ p ≤ H a := by
                dsimp only [H]
                exact Finset.single_le_sum (f := fun j => (F j a) ^ p) (fun _ _ => zero_le) hi
              have heq : F i a = ((F i a) ^ p) ^ (1 / p) := by
                rw [← ENNReal.rpow_mul, mul_one_div_cancel hp_pos.ne', ENNReal.rpow_one]
              rw [heq]
              exact ENNReal.rpow_le_rpow hle h1p_pos.le
          _ = G i := rfl
          _ = ⊤ := hGtop
      rw [hRtop]
      exact le_top
    · -- S ≠ ⊤
      have hG_ne_top : ∀ i ∈ t, G i ≠ ⊤ := by
        intro i hi hGi
        apply hSlt.ne
        have h1 : (G i) ^ p = ⊤ := by
          rw [hGi, ENNReal.top_rpow_of_pos hp_pos]
        have hle : (G i) ^ p ≤ S := by
          dsimp only [S]
          exact Finset.single_le_sum (f := fun j => (G j) ^ p) (fun _ _ => zero_le) hi
        exact top_le_iff.mp (h1 ▸ hle)
      rcases eq_zero_or_pos S with hS0 | hSpos
      · rw [hS0, ENNReal.zero_rpow_of_pos h1p_pos]
        exact zero_le
      · have hSnetop : S ≠ ⊤ := hSlt.ne
        have hSq_ne_top : S ^ (1 / q) ≠ ⊤ :=
          ENNReal.rpow_ne_top_of_nonneg h1q_pos.le hSnetop
        have hSq_ne_zero : S ^ (1 / q) ≠ 0 := (ENNReal.rpow_pos hSpos hSnetop).ne'
        have hpoint : ∀ a, (∑ i ∈ t, (G i) ^ (p - 1) * F i a) ≤ S ^ (1 / q) * (H a) ^ (1 / p) := by
          intro a
          have hhold := ennreal_finset_sum_mul_le_holder t (fun i => (G i) ^ (p - 1))
            (fun i => F i a) hpq.symm
          have h1 : (∑ i ∈ t, ((G i) ^ (p - 1)) ^ q) = S := by
            dsimp only [S]
            apply Finset.sum_congr rfl
            intro i _
            rw [← ENNReal.rpow_mul, hsub]
          have h2 : (∑ i ∈ t, (F i a) ^ p) = H a := rfl
          rwa [h1, h2] at hhold
        have hcore : S ≤ S ^ (1 / q) * R := by
          calc S = ∑ i ∈ t, (G i) ^ (p - 1) * (G i) := by
                dsimp only [S]
                apply Finset.sum_congr rfl
                intro i hi
                exact rpow_pred_mul_loc (hG_ne_top i hi) hp1
            _ = ∑ i ∈ t, (G i) ^ (p - 1) * ∫⁻ a, F i a ∂μ := rfl
            _ = ∑ i ∈ t, ∫⁻ a, (G i) ^ (p - 1) * F i a ∂μ := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [lintegral_const_mul' ((G i) ^ (p - 1)) (fun a => F i a)
                  (ENNReal.rpow_ne_top_of_nonneg (by linarith : (0:ℝ) ≤ p - 1) (hG_ne_top i hi))]
            _ = ∫⁻ a, ∑ i ∈ t, (G i) ^ (p - 1) * F i a ∂μ :=
                (lintegral_finsetSum' t (fun i _ => (hF i).const_mul ((G i) ^ (p - 1)))).symm
            _ ≤ ∫⁻ a, S ^ (1 / q) * (H a) ^ (1 / p) ∂μ := lintegral_mono hpoint
            _ = S ^ (1 / q) * ∫⁻ a, (H a) ^ (1 / p) ∂μ :=
                lintegral_const_mul' _ _ hSq_ne_top
            _ = S ^ (1 / q) * R := rfl
        have hSsq : S = S ^ (1 / p) * S ^ (1 / q) := by
          rw [← ENNReal.rpow_add (1 / p) (1 / q) hSpos.ne' hSnetop, hinv, ENNReal.rpow_one]
        have hcancel : S ^ (1 / p) * S ^ (1 / q) ≤ S ^ (1 / q) * R := by
          rw [hSsq.symm]
          exact hcore
        have hcancel' : S ^ (1 / q) * S ^ (1 / p) ≤ S ^ (1 / q) * R := by
          rw [mul_comm (S ^ (1 / q)) (S ^ (1 / p))]
          exact hcancel
        exact (ENNReal.mul_le_mul_iff_right hSq_ne_zero hSq_ne_top).mp hcancel'

end Commons.Analysis.MeasureTheory