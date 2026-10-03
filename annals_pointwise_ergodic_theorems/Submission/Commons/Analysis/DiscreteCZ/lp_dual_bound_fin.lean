import Mathlib.Analysis.Normed.Module.HahnBanach
import Submission.Commons.Analysis.DiscreteCZ.norm_tsum_apply_le_eLpNorm_mul
import Submission.Commons.Analysis.DiscreteCZ.sum_dual_pairing
import Submission.Commons.Analysis.DiscreteCZ.eLpNorm_count_eq_tsum

set_option maxHeartbeats 1600000

namespace Commons.Analysis.DiscreteCZ

open MeasureTheory ENNReal
open scoped ENNReal BigOperators

local notation "countZ" => (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)

/-- For `1 < p`, the real numbers `p` and `p / (p - 1)` are Hölder conjugates. -/
lemma holderConjugate_div {p : ℝ} (hp : 1 < p) : Real.HolderConjugate p (p / (p - 1)) := by
  rw [Real.holderConjugate_iff]
  refine ⟨hp, ?_⟩
  have h2 : p - 1 ≠ 0 := ne_of_gt (by linarith)
  have h1 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  field_simp
  ring

/-- The norm of a real number embedded in `ℂ`. -/
lemma norm_ofReal_complex (r : ℝ) : ‖(r:ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← pow_two, Real.sqrt_sq_eq_abs]

theorem lp_dual_bound_fin {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {K : ℤ → ℂ} {p c : ℝ} (hp : 1 < p) (hc : 0 < c)
    (hdual : ∀ Φ : ℤ → (H →L[ℂ] ℂ), Summable (fun n : ℤ => ‖Φ n‖ ^ (p / (p - 1))) →
      MeasureTheory.eLpNorm (fun y : ℤ => ∑' x : ℤ, K (x - y) • Φ x)
          (ENNReal.ofReal (p / (p - 1))) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal c * MeasureTheory.eLpNorm Φ (ENNReal.ofReal (p / (p - 1)))
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ))
    (f : ℤ → H) (t : Finset ℤ) (hf : ∀ x : ℤ, x ∉ t → f x = 0) :
    MeasureTheory.eLpNorm (fun x : ℤ => ∑' y : ℤ, K (x - y) • f y) (ENNReal.ofReal p)
        (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ≤ ENNReal.ofReal c * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
          (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  classical
  have hp1 : (0:ℝ) < p := lt_trans zero_lt_one hp
  have hp1m : (0:ℝ) < p - 1 := by linarith
  set p' : ℝ := p / (p - 1) with hp'def
  have hp'pos : 0 < p' := by rw [hp'def]; exact div_pos hp1 hp1m
  have hp'ne : p' ≠ 0 := ne_of_gt hp'pos
  have hconj : Real.HolderConjugate p p' := by rw [hp'def]; exact holderConjugate_div hp
  set Tf : ℤ → H := fun x => ∑' y : ℤ, K (x - y) • f y with hTfdef
  have key : ∀ s : Finset ℤ,
      (∑ x ∈ s, ‖Tf x‖ₑ ^ p) ≤ (ENNReal.ofReal c * eLpNorm f (ENNReal.ofReal p) countZ) ^ p := by
    intro s
    let ψ : ℤ → (H →L[ℂ] ℂ) := fun x =>
      if hx : ‖Tf x‖ = 0 then 0 else Classical.choose (exists_dual_vector ℂ (Tf x) hx)
    have hψnorm : ∀ x, ‖ψ x‖ = if ‖Tf x‖ = 0 then 0 else 1 := by
      intro x
      by_cases hx : ‖Tf x‖ = 0
      · have hz : ψ x = 0 := by simp only [ψ]; rw [dif_pos hx]
        rw [hz, norm_zero, if_pos hx]
      · have hz : ψ x = Classical.choose (exists_dual_vector ℂ (Tf x) hx) := by
          simp only [ψ]; rw [dif_neg hx]
        rw [hz, if_neg hx]
        exact (Classical.choose_spec (exists_dual_vector ℂ (Tf x) hx)).1
    have hψapply : ∀ x, ‖Tf x‖ ≠ 0 → ψ x (Tf x) = (‖Tf x‖ : ℂ) := by
      intro x hx
      have hz : ψ x = Classical.choose (exists_dual_vector ℂ (Tf x) hx) := by
        simp only [ψ]; rw [dif_neg hx]
      rw [hz]
      exact (Classical.choose_spec (exists_dual_vector ℂ (Tf x) hx)).2
    let Φ : ℤ → (H →L[ℂ] ℂ) := fun x =>
      if x ∈ s then ((‖Tf x‖ ^ (p - 1) : ℝ) : ℂ) • ψ x else 0
    have hΦsupp : ∀ x, x ∉ s → Φ x = 0 := by
      intro x hx
      simp only [Φ]; rw [if_neg hx]
    have hΦval : ∀ x ∈ s, Φ x = ((‖Tf x‖ ^ (p - 1) : ℝ) : ℂ) • ψ x := by
      intro x hx; simp only [Φ]; rw [if_pos hx]
    have hΦnorm : ∀ x ∈ s, ‖Φ x‖ = ‖Tf x‖ ^ (p - 1) := by
      intro x hx
      rw [hΦval x hx, norm_smul, norm_ofReal_complex,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), hψnorm x]
      by_cases hx0 : ‖Tf x‖ = 0
      · rw [if_pos hx0, hx0, Real.zero_rpow (ne_of_gt hp1m)]; simp
      · rw [if_neg hx0, mul_one]
    have hΦapply : ∀ x ∈ s, Φ x (Tf x) = ((‖Tf x‖ ^ p : ℝ) : ℂ) := by
      intro x hx
      rw [hΦval x hx, smul_apply]
      by_cases hx0 : ‖Tf x‖ = 0
      · have hz : ψ x = 0 := by simp only [ψ]; rw [dif_pos hx0]
        rw [hz, zero_apply, hx0, Real.zero_rpow (ne_of_gt hp1m), Real.zero_rpow (ne_of_gt hp1)]
        simp
      · rw [hψapply x hx0, smul_eq_mul, ← Complex.ofReal_mul]
        congr 1
        have hpp : ‖Tf x‖ ^ p = ‖Tf x‖ ^ (p - 1) * ‖Tf x‖ := by
          conv_lhs => rw [show p = (p - 1) + 1 by ring]
          rw [Real.rpow_add (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx0)), Real.rpow_one]
        rw [hpp]
    have hAeq : (∑ x ∈ s, ‖Tf x‖ₑ ^ p) = ‖∑ x ∈ s, Φ x (Tf x)‖ₑ := by
      have hR : (0:ℝ) ≤ ∑ x ∈ s, ‖Tf x‖ ^ p :=
        Finset.sum_nonneg (fun x _ => Real.rpow_nonneg (norm_nonneg _) _)
      have hsum_eq : (∑ x ∈ s, Φ x (Tf x)) = (((∑ x ∈ s, ‖Tf x‖ ^ p) : ℝ) : ℂ) := by
        rw [Finset.sum_congr rfl (fun x hx => hΦapply x hx), Complex.ofReal_sum]
      rw [hsum_eq, ← ofReal_norm, norm_ofReal_complex, abs_of_nonneg hR,
          ENNReal.ofReal_sum_of_nonneg (fun x _ => Real.rpow_nonneg (norm_nonneg _) _)]
      apply Finset.sum_congr rfl
      intro x hx
      rw [← ofReal_norm (Tf x), ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (Tf x)) hp1.le]
    have hcn : (∑ x ∈ s, Φ x (Tf x))
        = ∑' y : ℤ, (fun y : ℤ => ∑' x : ℤ, K (x - y) • Φ x) y (f y) := by
      have hTf : ∀ x : ℤ, Tf x = ∑ y ∈ t, K (x - y) • f y := by
        intro x
        rw [hTfdef]
        exact tsum_eq_sum (fun y hy => by rw [hf y hy, smul_zero])
      calc (∑ x ∈ s, Φ x (Tf x))
          = ∑ x ∈ s, Φ x (∑ y ∈ t, K (x - y) • f y) := by
              apply Finset.sum_congr rfl; intro x _; rw [hTf x]
        _ = ∑ y ∈ t, (∑ x ∈ s, K (x - y) • Φ x) (f y) :=
              sum_dual_pairing K Φ f s t hf hΦsupp
        _ = ∑' y : ℤ, (fun y : ℤ => ∑' x : ℤ, K (x - y) • Φ x) y (f y) := by
              rw [tsum_eq_sum (s := t)
                    (f := fun y : ℤ => (∑' x : ℤ, K (x - y) • Φ x) (f y))
                    (fun y hy => by rw [hf y hy, map_zero])]
              apply Finset.sum_congr rfl
              intro y _
              exact congrArg (fun L : (H →L[ℂ] ℂ) => L (f y))
                (tsum_eq_sum (s := s) (f := fun x : ℤ => K (x - y) • Φ x)
                    (fun x hx => by rw [hΦsupp x hx]; ext v; simp)).symm
    have hΦsummable : Summable (fun n : ℤ => ‖Φ n‖ ^ p') := by
      apply summable_of_ne_finset_zero (s := s)
      intro n hn
      rw [hΦsupp n hn, norm_zero, Real.zero_rpow hp'ne]
    have hbound1 : ‖∑' y : ℤ, (fun y : ℤ => ∑' x : ℤ, K (x - y) • Φ x) y (f y)‖ₑ
        ≤ (ENNReal.ofReal c * eLpNorm Φ (ENNReal.ofReal p') countZ)
            * eLpNorm f (ENNReal.ofReal p) countZ := by
      have hh := norm_tsum_apply_le_eLpNorm_mul
        (fun y : ℤ => ∑' x : ℤ, K (x - y) • Φ x) f hconj
      calc ‖∑' y : ℤ, (fun y : ℤ => ∑' x : ℤ, K (x - y) • Φ x) y (f y)‖ₑ
          ≤ eLpNorm (fun y : ℤ => ∑' x : ℤ, K (x - y) • Φ x) (ENNReal.ofReal p') countZ
              * eLpNorm f (ENNReal.ofReal p) countZ := hh
        _ ≤ (ENNReal.ofReal c * eLpNorm Φ (ENNReal.ofReal p') countZ)
              * eLpNorm f (ENNReal.ofReal p) countZ := by
              gcongr
              exact hdual Φ hΦsummable
    have hΦLp : eLpNorm Φ (ENNReal.ofReal p') countZ = (∑ x ∈ s, ‖Tf x‖ₑ ^ p) ^ (1 / p') := by
      rw [eLpNorm_count_eq_tsum hp'pos Φ]
      congr 1
      rw [tsum_eq_sum (s := s) (f := fun x : ℤ => ‖Φ x‖ₑ ^ p')
            (fun x hx => by
              rw [hΦsupp x hx, ← ofReal_norm, norm_zero, ENNReal.ofReal_zero,
                  ENNReal.zero_rpow_of_pos hp'pos])]
      apply Finset.sum_congr rfl
      intro x hx
      rw [← ofReal_norm (Φ x), hΦnorm x hx,
          ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hp'pos.le,
          ← ofReal_norm (Tf x), ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (Tf x)) hp1.le]
      congr 1
      rw [← Real.rpow_mul (norm_nonneg (Tf x))]
      congr 1
      rw [hp'def]
      field_simp
    set A : ℝ≥0∞ := ∑ x ∈ s, ‖Tf x‖ₑ ^ p with hAdef
    change A ≤ (ENNReal.ofReal c * eLpNorm f (ENNReal.ofReal p) countZ) ^ p
    have hAfin : A < ∞ := by
      rw [hAdef, ENNReal.sum_lt_top]
      intro x hx
      rw [← ofReal_norm (Tf x), ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (Tf x)) hp1.le]
      exact ENNReal.ofReal_lt_top
    have hAle : A ≤ (ENNReal.ofReal c * eLpNorm f (ENNReal.ofReal p) countZ) * A ^ (1 / p') := by
      calc A = ‖∑ x ∈ s, Φ x (Tf x)‖ₑ := hAeq
        _ = ‖∑' y : ℤ, (fun y : ℤ => ∑' x : ℤ, K (x - y) • Φ x) y (f y)‖ₑ := by rw [hcn]
        _ ≤ (ENNReal.ofReal c * eLpNorm Φ (ENNReal.ofReal p') countZ)
              * eLpNorm f (ENNReal.ofReal p) countZ := hbound1
        _ = (ENNReal.ofReal c * eLpNorm f (ENNReal.ofReal p) countZ) * A ^ (1 / p') := by
              rw [hΦLp]
              exact mul_right_comm _ _ _
    by_cases hA0 : A = 0
    · simp [hA0]
    · have hApos : 0 < A := pos_iff_ne_zero.mpr hA0
      have hAne : A ≠ ∞ := ne_of_lt hAfin
      have hA'ne0 : A ^ (1 / p') ≠ 0 := ne_of_gt (ENNReal.rpow_pos hApos hAne)
      have hA'netop : A ^ (1 / p') ≠ ∞ := by
        intro h
        rw [ENNReal.rpow_eq_top_iff] at h
        rcases h with ⟨h, _⟩ | ⟨h, _⟩
        · exact hA0 h
        · exact hAne h
      have hstep : A ^ (1 / p) ≤ ENNReal.ofReal c * eLpNorm f (ENNReal.ofReal p) countZ := by
        have h1 : A ^ (1 / p) * A ^ (1 / p')
            ≤ (ENNReal.ofReal c * eLpNorm f (ENNReal.ofReal p) countZ) * A ^ (1 / p') := by
          rw [← ENNReal.rpow_add (1 / p) (1 / p') hA0 hAne,
              show 1 / p + 1 / p' = 1 by rw [hp'def]; field_simp; ring,
              ENNReal.rpow_one]
          exact hAle
        exact (ENNReal.mul_le_mul_iff_left hA'ne0 hA'netop).mp h1
      calc A = (A ^ (1 / p)) ^ p := by
              rw [← ENNReal.rpow_mul,
                  show (1 / p) * p = 1 by rw [one_div, inv_mul_cancel₀ (ne_of_gt hp1)],
                  ENNReal.rpow_one]
        _ ≤ (ENNReal.ofReal c * eLpNorm f (ENNReal.ofReal p) countZ) ^ p :=
              ENNReal.rpow_le_rpow hstep hp1.le
  have hsum : (∑' x : ℤ, ‖Tf x‖ₑ ^ p)
      ≤ (ENNReal.ofReal c * eLpNorm f (ENNReal.ofReal p) countZ) ^ p := by
    rw [ENNReal.tsum_eq_iSup_sum]
    exact iSup_le key
  calc eLpNorm Tf (ENNReal.ofReal p) countZ
      = (∑' x : ℤ, ‖Tf x‖ₑ ^ p) ^ (1 / p) := eLpNorm_count_eq_tsum hp1 Tf
    _ ≤ ((ENNReal.ofReal c * eLpNorm f (ENNReal.ofReal p) countZ) ^ p) ^ (1 / p) :=
          ENNReal.rpow_le_rpow hsum (by positivity)
    _ = ENNReal.ofReal c * eLpNorm f (ENNReal.ofReal p) countZ := by
          rw [← ENNReal.rpow_mul,
              show p * (1 / p) = 1 by rw [one_div, mul_inv_cancel₀ (ne_of_gt hp1)],
              ENNReal.rpow_one]

end Commons.Analysis.DiscreteCZ