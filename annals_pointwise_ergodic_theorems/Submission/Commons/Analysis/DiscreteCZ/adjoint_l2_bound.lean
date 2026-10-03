import Mathlib
import Submission.Commons.Analysis.DiscreteCZ.eLpNorm_count_eq_tsum
import Submission.Commons.Analysis.DiscreteCZ.norm_tsum_apply_le_eLpNorm_mul
import Submission.Commons.Analysis.Hilbert.discrete_hilbert_transform_lp
import Submission.Port.Aesm

open MeasureTheory ENNReal
open scoped ENNReal BigOperators

namespace Commons.Analysis.DiscreteCZ

lemma exists_phased_norming_element {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (φ : H →L[ℂ] ℂ) :
    ∃ h : H, ∃ r : ℝ, ‖h‖ ≤ 1 ∧ 0 ≤ r ∧ φ h = (r : ℂ) ∧ ‖φ‖ ≤ 2 * r := by
  by_cases hφ : ‖φ‖ = 0
  · exact ⟨0, 0, by simp, le_refl 0, by simp, by simp [hφ]⟩
  · have hpos : 0 < ‖φ‖ := lt_of_le_of_ne (norm_nonneg φ) (Ne.symm hφ)
    have hlt : ∃ x : H, ‖x‖ ≤ 1 ∧ ‖φ‖ / 2 < ‖φ x‖ := by
      by_contra hcon
      push_neg at hcon
      have hbound : ∀ x : H, ‖φ x‖ ≤ (‖φ‖ / 2) * ‖x‖ := by
        intro x
        rcases eq_or_ne x 0 with hx | hx
        · subst hx; simp
        · have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
          have h1 : ‖(((‖x‖⁻¹ : ℝ)) : ℂ) • x‖ ≤ 1 := by
            rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (by positivity), inv_mul_cancel₀ hnx]
          have h2 := hcon _ h1
          rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by positivity)] at h2
          calc ‖φ x‖ = ‖x‖ * (‖x‖⁻¹ * ‖φ x‖) := by
                rw [← mul_assoc, mul_inv_cancel₀ hnx, one_mul]
            _ ≤ ‖x‖ * (‖φ‖ / 2) := mul_le_mul_of_nonneg_left h2 (norm_nonneg x)
            _ = (‖φ‖ / 2) * ‖x‖ := by ring
      have hle := ContinuousLinearMap.opNorm_le_bound φ (by positivity) hbound
      linarith
    obtain ⟨x, hx1, hx2⟩ := hlt
    have hu : φ x ≠ 0 := by
      intro h0
      have : ‖φ x‖ = 0 := by rw [h0]; simp
      linarith [hpos]
    have hnormu : 0 < ‖φ x‖ := norm_pos_iff.mpr hu
    refine ⟨(((‖φ x‖ : ℝ) : ℂ) / (φ x)) • x, ‖φ x‖, ?_, norm_nonneg _, ?_, ?_⟩
    · rw [norm_smul, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), div_self (ne_of_gt hnormu), one_mul]
      exact hx1
    · rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hu]
    · linarith

lemma finset_pairing_bound {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (Φ : ℤ → (H →L[ℂ] ℂ)) (E : ENNReal)
    (hpair : ∀ f : ℤ → H, (∃ s : Finset ℤ, ∀ x, x ∉ s → f x = 0) →
      ‖∑' x : ℤ, Φ x (f x)‖ₑ ≤ E * eLpNorm f 2 (Measure.count : Measure ℤ))
    (s : Finset ℤ) :
    ∑ x ∈ s, ‖Φ x‖ₑ ^ 2 ≤ (2 * E) ^ 2 := by
  classical
  have key : ∀ x ∈ s, ∃ h : H, ∃ r : ℝ, ‖h‖ ≤ 1 ∧ 0 ≤ r ∧ Φ x h = (r : ℂ) ∧ ‖Φ x‖ ≤ 2 * r :=
    fun x _ => exists_phased_norming_element (Φ x)
  choose h r hh hr hphi hnorm using key
  let hs : ℤ → H := fun x => if hx : x ∈ s then h x hx else 0
  let rs : ℤ → ℝ := fun x => if hx : x ∈ s then r x hx else 0
  have hs_eq : ∀ x (hx : x ∈ s), hs x = h x hx := fun x hx => dif_pos hx
  have rs_eq : ∀ x (hx : x ∈ s), rs x = r x hx := fun x hx => dif_pos hx
  have hs_le : ∀ x, ‖hs x‖ ≤ 1 := by
    intro x; by_cases hx : x ∈ s
    · rw [hs_eq x hx]; exact hh x hx
    · simp only [hs, dif_neg hx, norm_zero]; norm_num
  have rs_nonneg : ∀ x, 0 ≤ rs x := by
    intro x; by_cases hx : x ∈ s
    · rw [rs_eq x hx]; exact hr x hx
    · simp only [rs, dif_neg hx]; norm_num
  have hs_phi : ∀ x (hx : x ∈ s), Φ x (hs x) = (rs x : ℂ) := by
    intro x hx; rw [hs_eq x hx, rs_eq x hx]; exact hphi x hx
  have hs_gnorm : ∀ x (hx : x ∈ s), ‖Φ x‖ ≤ 2 * rs x := by
    intro x hx; rw [rs_eq x hx]; exact hnorm x hx
  set A : ℝ := ∑ x ∈ s, ‖Φ x‖ ^ 2 with hA
  set B : ℝ := Real.sqrt A with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun x _ => sq_nonneg _)
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hBB : B ^ 2 = A := Real.sq_sqrt hA0
  have hsumA : ∑ x ∈ s, ‖Φ x‖ₑ ^ 2 = ENNReal.ofReal A := by
    rw [hA, ENNReal.ofReal_sum_of_nonneg (fun x _ => sq_nonneg _)]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg (Φ x)) 2]
  rcases eq_or_ne B 0 with hBz | hBnz
  · have hAz : A = 0 := by rw [← hBB, hBz]; ring
    rw [hsumA, hAz]
    simp
  · have hBpos : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hBnz)
    let f : ℤ → H := fun x => if hx : x ∈ s then (((‖Φ x‖ / B : ℝ)) : ℂ) • hs x else 0
    have hfsupp : ∀ x, x ∉ s → f x = 0 := fun x hx => by simp only [f]; exact dif_neg hx
    have hfnorm : ∀ x, ‖f x‖ ≤ ‖Φ x‖ / B := by
      intro x
      by_cases hx : x ∈ s
      · simp only [f, hx, dif_pos]
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        calc (‖Φ x‖ / B) * ‖hs x‖ ≤ (‖Φ x‖ / B) * 1 :=
              mul_le_mul_of_nonneg_left (hs_le x) (by positivity)
          _ = ‖Φ x‖ / B := by ring
      · simp only [f, hx, dif_neg, not_false_iff, norm_zero]
        exact div_nonneg (norm_nonneg _) hB0
    have heLp_f : eLpNorm f 2 (Measure.count : Measure ℤ) ≤ 1 := by
      have hsum_eq : ∑' x : ℤ, ‖f x‖ₑ ^ (2:ℝ) = ∑ x ∈ s, ‖f x‖ₑ ^ (2:ℝ) :=
        tsum_eq_sum (fun x hx => by rw [hfsupp x hx]; simp)
      rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by rw [ENNReal.ofReal_ofNat],
          eLpNorm_count_eq_tsum (show (0:ℝ) < 2 by norm_num), hsum_eq]
      have hconv : ∑ x ∈ s, ‖f x‖ₑ ^ (2:ℝ) = ENNReal.ofReal (∑ x ∈ s, ‖f x‖ ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => sq_nonneg _)]
        apply Finset.sum_congr rfl; intro x hx
        rw [← ofReal_norm, ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg (f x)) 2]
      have hle1 : ∑ x ∈ s, ‖f x‖ₑ ^ (2:ℝ) ≤ 1 := by
        rw [hconv, ← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        have h1 : ∑ x ∈ s, ‖f x‖ ^ 2 ≤ ∑ x ∈ s, (‖Φ x‖ / B) ^ 2 :=
          Finset.sum_le_sum (fun x hx => by
            nlinarith [norm_nonneg (f x), hfnorm x, div_nonneg (norm_nonneg (Φ x)) hB0])
        have h2 : ∑ x ∈ s, (‖Φ x‖ / B) ^ 2 = 1 := by
          rw [show ∑ x ∈ s, (‖Φ x‖ / B) ^ 2 = ∑ x ∈ s, ‖Φ x‖ ^ 2 / B ^ 2 by
                apply Finset.sum_congr rfl; intro x hx
                rw [div_pow]]
          rw [← Finset.sum_div, ← hA, ← hBB, div_self (pow_ne_zero 2 hBnz)]
        linarith
      calc (∑ x ∈ s, ‖f x‖ₑ ^ (2:ℝ)) ^ (1/2) ≤ 1 ^ (1/2) := ENNReal.rpow_le_rpow hle1 (by norm_num)
        _ = 1 := ENNReal.one_rpow _
    have hpair_low : ENNReal.ofReal (B/2) ≤ E := by
      have hsum_eq : ∑' x : ℤ, Φ x (f x) = ∑ x ∈ s, Φ x (f x) :=
        tsum_eq_sum (fun x hx => by rw [hfsupp x hx, map_zero])
      have hsumas : ∑ x ∈ s, Φ x (f x) = ((∑ x ∈ s, (‖Φ x‖ / B) * rs x : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        apply Finset.sum_congr rfl
        intro x hx
        simp only [f, hx, dif_pos]
        rw [map_smul, smul_eq_mul, hs_phi x hx, ← Complex.ofReal_mul]
      have hnorm_sum : ‖∑ x ∈ s, Φ x (f x)‖ = ∑ x ∈ s, (‖Φ x‖ / B) * rs x := by
        rw [hsumas, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Finset.sum_nonneg (fun x hx =>
            mul_nonneg (div_nonneg (norm_nonneg _) hB0) (rs_nonneg x)))]
      have hlow : B/2 ≤ ∑ x ∈ s, (‖Φ x‖ / B) * rs x := by
        have hstep : B/2 = ∑ x ∈ s, (‖Φ x‖ / B) * (‖Φ x‖ / 2) := by
          rw [show ∑ x ∈ s, (‖Φ x‖ / B) * (‖Φ x‖ / 2) = ∑ x ∈ s, ‖Φ x‖ ^ 2 / (2*B) by
                apply Finset.sum_congr rfl; intro x hx
                field_simp [hBnz]]
          rw [← Finset.sum_div, ← hA, ← hBB]
          field_simp [hBnz]
        rw [hstep]
        exact Finset.sum_le_sum (fun x hx =>
          mul_le_mul_of_nonneg_left (by linarith [hs_gnorm x hx])
            (div_nonneg (norm_nonneg _) hB0))
      have h1 : ENNReal.ofReal (B/2) ≤ ‖∑' x : ℤ, Φ x (f x)‖ₑ := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (by rw [hsum_eq, hnorm_sum]; exact hlow)
      have h2 : ‖∑' x : ℤ, Φ x (f x)‖ₑ ≤ E := by
        have hp := hpair f ⟨s, hfsupp⟩
        calc ‖∑' x : ℤ, Φ x (f x)‖ₑ ≤ E * eLpNorm f 2 (Measure.count : Measure ℤ) := hp
          _ ≤ E * 1 := by gcongr
          _ = E := mul_one E
      exact h1.trans h2
    have hB2E : ENNReal.ofReal B ≤ 2 * E := by
      have hcoe : ENNReal.ofReal B = 2 * ENNReal.ofReal (B/2) := by
        conv_lhs => rw [show B = 2*(B/2) by ring]
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
      rw [hcoe]
      calc (2:ENNReal) * ENNReal.ofReal (B/2) = ENNReal.ofReal (B/2) * 2 := mul_comm _ _
        _ ≤ E * 2 := mul_le_mul_left hpair_low 2
        _ = 2 * E := mul_comm _ _
    have hAeq : ENNReal.ofReal A = (ENNReal.ofReal B) ^ 2 := by
      rw [← hBB, ENNReal.ofReal_pow hB0 2]
    rw [hsumA, hAeq]
    exact pow_le_pow_left₀ (by positivity : (0:ℝ≥0∞) ≤ ENNReal.ofReal B) hB2E 2

lemma eLpNorm_two_le_two_mul_of_pairing_bound {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (Φ : ℤ → (H →L[ℂ] ℂ)) (E : ENNReal)
    (hpair : ∀ f : ℤ → H, (∃ s : Finset ℤ, ∀ x, x ∉ s → f x = 0) →
      ‖∑' x : ℤ, Φ x (f x)‖ₑ ≤ E * eLpNorm f 2 (Measure.count : Measure ℤ)) :
    eLpNorm Φ 2 (Measure.count : Measure ℤ) ≤ 2 * E := by
  have heq : eLpNorm Φ 2 (Measure.count : Measure ℤ)
      = (∑' x : ℤ, ‖Φ x‖ₑ ^ (2:ℝ)) ^ (1/2 : ℝ) := by
    rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by rw [ENNReal.ofReal_ofNat],
        eLpNorm_count_eq_tsum (show (0:ℝ) < 2 by norm_num)]
  rw [heq]
  have htsum : ∑' x : ℤ, ‖Φ x‖ₑ ^ (2:ℝ) ≤ (2*E) ^ (2:ℝ) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro s
    have hf := finset_pairing_bound Φ E hpair s
    rw [show (∑ x ∈ s, ‖Φ x‖ₑ ^ (2:ℝ)) = ∑ x ∈ s, ‖Φ x‖ₑ ^ (2:ℕ) by
          apply Finset.sum_congr rfl; intro x hx; rw [ENNReal.rpow_two],
        show (2*E) ^ (2:ℝ) = (2*E) ^ (2:ℕ) by rw [ENNReal.rpow_two]]
    exact hf
  calc (∑' x : ℤ, ‖Φ x‖ₑ ^ (2:ℝ)) ^ (1/2 : ℝ) ≤ ((2*E) ^ (2:ℝ)) ^ (1/2 : ℝ) :=
        ENNReal.rpow_le_rpow htsum (by norm_num)
    _ = 2*E := by
        rw [← ENNReal.rpow_mul, show (2:ℝ) * (1/2) = 1 by norm_num, ENNReal.rpow_one]


lemma eLpNorm_two_count_lt_top_iff {E : Type*} [NormedAddCommGroup E] (u : ℤ → E) :
    eLpNorm u 2 (Measure.count : Measure ℤ) < ⊤ ↔ Summable (fun x : ℤ => ‖u x‖ ^ 2) := by
  have hcoe : eLpNorm u 2 (Measure.count : Measure ℤ)
      = (∑' x : ℤ, ‖u x‖ₑ ^ (2:ℝ)) ^ (1/2 : ℝ) := by
    rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by rw [ENNReal.ofReal_ofNat],
        eLpNorm_count_eq_tsum (show (0:ℝ) < 2 by norm_num)]
  rw [hcoe, ENNReal.rpow_lt_top_iff_of_pos (show (0:ℝ) < 1/2 by norm_num)]
  have hconv : ∑' x : ℤ, ‖u x‖ₑ ^ (2:ℝ) = ∑' x : ℤ, ENNReal.ofReal (‖u x‖ ^ 2) := by
    apply tsum_congr; intro x
    rw [← ofReal_norm, ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg (u x)) 2]
  rw [hconv]
  exact Commons.Analysis.Hilbert.tsum_ofReal_lt_top_iff_summable (fun x => sq_nonneg _)

lemma eLpNorm_two_count_zero {E : Type*} [NormedAddCommGroup E] :
    eLpNorm (0 : ℤ → E) 2 (Measure.count : Measure ℤ) = 0 := eLpNorm_zero

lemma summable_smul_shift {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (K : ℤ → ℂ) (Ψ : ℤ → (H →L[ℂ] ℂ)) (c : ℤ)
    (hK : Summable (fun y : ℤ => ‖K y‖ ^ 2)) (hΨ : Summable (fun y : ℤ => ‖Ψ y‖ ^ 2)) :
    Summable (fun x : ℤ => K (x - c) • Ψ x) := by
  have hKa : Summable (fun x : ℤ => ‖K (x - c)‖ ^ 2) :=
    hK.comp_injective (fun a b h => by omega)
  have hsum : Summable (fun x : ℤ => ‖K (x - c)‖ * ‖Ψ x‖) := by
    have h2 : Summable (fun x : ℤ => ‖K (x - c)‖ ^ 2 + ‖Ψ x‖ ^ 2) := hKa.add hΨ
    refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_) h2
    nlinarith [sq_nonneg (‖K (x - c)‖ - ‖Ψ x‖)]
  exact Summable.of_norm_bounded hsum (fun x => le_of_eq (norm_smul _ _))

theorem adjoint_l2_bound {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (K : ℤ → ℂ) (A2 : ℝ) (hA2 : 0 < A2)
    (hstrong : ∀ f : ℤ → H, Summable f →
      MeasureTheory.eLpNorm (fun x : ℤ => ∑' y : ℤ, K (x - y) • f y) 2
          (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal A2 * MeasureTheory.eLpNorm f 2 (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)) :
    ∀ Ψ : ℤ → (H →L[ℂ] ℂ), Summable Ψ →
      MeasureTheory.eLpNorm (fun y : ℤ => ∑' x : ℤ, K (x - y) • Ψ x) 2
          (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal (2 * A2) * MeasureTheory.eLpNorm Ψ 2 (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  intro Ψ hΨ
  by_cases hH : Subsingleton H
  · have hzero : ∀ x, Ψ x = 0 := fun x => ContinuousLinearMap.ext (fun v => by
      rw [Subsingleton.elim v 0]; simp)
    have hw : (fun y : ℤ => ∑' x : ℤ, K (x - y) • Ψ x) = 0 := by
      funext y
      have hc : (∑' x : ℤ, K (x - y) • Ψ x) = ∑' x : ℤ, (0 : H →L[ℂ] ℂ) := by
        apply tsum_congr; intro x
        rw [hzero x]
        ext v
        simp only [smul_apply, zero_apply, smul_eq_mul, mul_zero]
      rw [hc]
      exact tsum_zero
    rw [hw, eLpNorm_two_count_zero (E := H →L[ℂ] ℂ)]
    exact zero_le
  · haveI : Nontrivial H := not_subsingleton_iff_nontrivial.mp hH
    obtain ⟨a0, b0, hab0⟩ := exists_pair_ne H
    have hk2 : Summable (fun x : ℤ => ‖K x‖ ^ 2) := by
      obtain ⟨w0, hw0⟩ : ∃ w0 : H, w0 ≠ 0 := ⟨a0 - b0, sub_ne_zero.mpr hab0⟩
      have hnorm0 : ‖w0‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
      set e : H := ((‖w0‖⁻¹ : ℝ) : ℂ) • w0 with hedef
      have he1 : ‖e‖ = 1 := by
        rw [hedef, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity), inv_mul_cancel₀ hnorm0]
      set f0 : ℤ → H := (fun x => if x = 0 then e else 0) with hf0def
      have hf0_0 : f0 0 = e := by rw [hf0def]; simp
      have hf0_ne : ∀ y, y ≠ 0 → f0 y = 0 := by intro y hy; rw [hf0def]; simp [hy]
      have hf0sum : Summable f0 := summable_of_ne_finset_zero (s := {0}) (fun b hb => by
        rw [Finset.mem_singleton] at hb; exact hf0_ne b hb)
      have hb0' := hstrong f0 hf0sum
      have hL : (fun x : ℤ => ∑' y : ℤ, K (x - y) • f0 y) = fun x => K x • e := by
        funext x
        rw [tsum_eq_single 0 (fun y hy => by rw [hf0_ne y hy, smul_zero])]
        rw [hf0_0, sub_zero]
      rw [hL] at hb0'
      have hR : eLpNorm f0 2 (Measure.count : Measure ℤ) = 1 := by
        have hcoe : eLpNorm f0 2 (Measure.count : Measure ℤ)
            = (∑' x : ℤ, ‖f0 x‖ₑ ^ (2:ℝ)) ^ (1/2 : ℝ) := by
          rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by rw [ENNReal.ofReal_ofNat],
              eLpNorm_count_eq_tsum (show (0:ℝ) < 2 by norm_num)]
        rw [hcoe]
        have h1 : ∑' x : ℤ, ‖f0 x‖ₑ ^ (2:ℝ) = 1 := by
          rw [tsum_eq_single 0 (fun y hy => by rw [hf0_ne y hy]; simp)]
          rw [hf0_0, ← ofReal_norm, he1]; simp
        rw [h1]; simp
      rw [hR, mul_one] at hb0'
      have hKe : eLpNorm (fun x : ℤ => K x • e) 2 (Measure.count : Measure ℤ)
          = eLpNorm K 2 (Measure.count : Measure ℤ) := by
        apply le_antisymm
        · exact eLpNorm_mono (hf := by pw_aesm) (fun x => by rw [norm_smul, he1, mul_one])
        · exact eLpNorm_mono (hf := by pw_aesm) (fun x => by rw [norm_smul, he1, mul_one])
      rw [hKe] at hb0'
      exact (eLpNorm_two_count_lt_top_iff K).mp (lt_of_le_of_lt hb0' ENNReal.ofReal_lt_top)
    by_cases hΨtop : eLpNorm Ψ 2 (Measure.count : Measure ℤ) = ⊤
    · rw [hΨtop, mul_top (by positivity : ENNReal.ofReal (2 * A2) ≠ 0)]
      exact le_top
    · have hΨ2 : Summable (fun x : ℤ => ‖Ψ x‖ ^ 2) :=
        (eLpNorm_two_count_lt_top_iff Ψ).mp (lt_top_iff_ne_top.mpr hΨtop)
      have hpair : ∀ f : ℤ → H, (∃ s : Finset ℤ, ∀ x, x ∉ s → f x = 0) →
          ‖∑' x : ℤ, (∑' y : ℤ, K (y - x) • Ψ y) (f x)‖ₑ
            ≤ (ENNReal.ofReal A2 * eLpNorm Ψ 2 (Measure.count : Measure ℤ))
              * eLpNorm f 2 (Measure.count : Measure ℤ) := by
        intro f ⟨s, hfs⟩
        have hFsumm : Summable f := summable_of_ne_finset_zero hfs
        set g : ℤ → H := fun x => ∑ y ∈ s, K (x - y) • f y with hgdef
        have hg_eq : g = fun x => ∑' y : ℤ, K (x - y) • f y := by
          funext x
          rw [hgdef, tsum_eq_sum (s := s) (fun y hy => by rw [hfs y hy, smul_zero])]
        have hg_bd : eLpNorm g 2 (Measure.count : Measure ℤ)
            ≤ ENNReal.ofReal A2 * eLpNorm f 2 (Measure.count : Measure ℤ) := by
          rw [hg_eq]; exact hstrong f hFsumm
        have hident : ∑' y : ℤ, (∑' z : ℤ, K (z - y) • Ψ z) (f y)
            = ∑' x : ℤ, Ψ x (g x) := by
          have step1 : ∑' y : ℤ, (∑' z : ℤ, K (z - y) • Ψ z) (f y)
              = ∑ y ∈ s, (∑' z : ℤ, K (z - y) • Ψ z) (f y) :=
            tsum_eq_sum (fun y hy => by rw [hfs y hy, map_zero])
          rw [step1]
          have step2 : ∀ y ∈ s, (∑' z : ℤ, K (z - y) • Ψ z) (f y)
              = ∑' z : ℤ, (K (z - y) • Ψ z) (f y) := by
            intro y hy
            rw [← ContinuousLinearMap.apply_apply (f y) (∑' z : ℤ, K (z - y) • Ψ z),
              ContinuousLinearMap.map_tsum ((ContinuousLinearMap.apply ℂ ℂ) (f y))
                (summable_smul_shift K Ψ y hk2 hΨ2)]
            simp only [ContinuousLinearMap.apply_apply]
          rw [Finset.sum_congr rfl step2]
          rw [← Summable.tsum_finsetSum (f := fun (y : ℤ) (z : ℤ) => (K (z - y) • Ψ z) (f y)) (s := s)]
          · apply tsum_congr; intro x
            rw [hgdef, map_sum]
            apply Finset.sum_congr rfl; intro y hy
            rw [smul_apply, map_smul]
          · intro y hy
            exact (summable_smul_shift K Ψ y hk2 hΨ2).map (ContinuousLinearMap.apply ℂ ℂ (f y))
              (ContinuousLinearMap.continuous _)
        calc ‖∑' x : ℤ, (∑' y : ℤ, K (y - x) • Ψ y) (f x)‖ₑ
            = ‖∑' x : ℤ, Ψ x (g x)‖ₑ := by rw [hident]
          _ ≤ eLpNorm Ψ 2 (Measure.count : Measure ℤ) * eLpNorm g 2 (Measure.count : Measure ℤ) := by
              have h := norm_tsum_apply_le_eLpNorm_mul Ψ g
                (show (2:ℝ).HolderConjugate 2 by rw [Real.holderConjugate_iff]; norm_num)
              simpa only [ENNReal.ofReal_ofNat] using h
          _ ≤ eLpNorm Ψ 2 (Measure.count : Measure ℤ)
                * (ENNReal.ofReal A2 * eLpNorm f 2 (Measure.count : Measure ℤ)) := by
              gcongr
          _ = (ENNReal.ofReal A2 * eLpNorm Ψ 2 (Measure.count : Measure ℤ))
                * eLpNorm f 2 (Measure.count : Measure ℤ) := by ring
      have hfin := eLpNorm_two_le_two_mul_of_pairing_bound
        (fun y : ℤ => ∑' x : ℤ, K (x - y) • Ψ x)
        (ENNReal.ofReal A2 * eLpNorm Ψ 2 (Measure.count : Measure ℤ)) hpair
      have harith : 2 * (ENNReal.ofReal A2 * eLpNorm Ψ 2 (Measure.count : Measure ℤ))
          = ENNReal.ofReal (2 * A2) * eLpNorm Ψ 2 (Measure.count : Measure ℤ) := by
        rw [← mul_assoc]
        congr 1
        rw [← ENNReal.ofReal_ofNat (2), ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      rw [harith] at hfin
      exact hfin

end Commons.Analysis.DiscreteCZ
