import Mathlib
import Submission.Commons.NumberTheory.BombieriVinogradov.sum_charSup_le_log_mul_primitive
import Submission.Commons.NumberTheory.BombieriVinogradov.siegel_walfisz_chi_range
import Submission.Commons.NumberTheory.BombieriVinogradov.vaughan_mean_value_sqrt
import Submission.Commons.NumberTheory.BombieriVinogradov.character_sum_primitive_reduction
import Submission.Commons.NumberTheory.BombieriVinogradov.abel_tail_sum_le
import Submission.Commons.NumberTheory.BombieriVinogradov.vaughan_type1_lambda2_estimate
import Submission.Commons.Analysis.Asymptotics.le_log_rpow_eventually

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

open scoped BigOperators
open Finset Filter
open Classical
open Commons.Analysis.Asymptotics

namespace Commons.NumberTheory.BombieriVinogradov

noncomputable section

/-- The primitive characters mod `q`. -/
def primChars (q : ℕ) : Finset (DirichletCharacter ℂ q) :=
  Finset.univ.filter (fun ψ : DirichletCharacter ℂ q => ψ.IsPrimitive)

/-- `Σ_{χ mod q, χ ≠ 1} ‖Σ_{n ≤ x} Λ(n) χ(n)‖`. -/
def npSum (x q : ℕ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ q, if χ = 1 then 0 else ‖chiSum q χ x‖

lemma npSum_eq (x q : ℕ) :
    npSum x q = (∑ χ : DirichletCharacter ℂ q, ‖chiSum q χ x‖) - ‖chiSum q 1 x‖ := by
  unfold npSum
  have h1 : ∀ χ : DirichletCharacter ℂ q, (if χ = 1 then 0 else ‖chiSum q χ x‖)
      = ‖chiSum q χ x‖ - (if χ = 1 then ‖chiSum q 1 x‖ else 0) := by
    intro χ
    by_cases h : χ = 1
    · subst h; simp
    · simp [h]
  rw [Finset.sum_congr rfl (fun χ _ => h1 χ), Finset.sum_sub_distrib]
  have hsum : (∑ χ : DirichletCharacter ℂ q, (if χ = 1 then ‖chiSum q 1 x‖ else 0))
      = ‖chiSum q 1 x‖ := by
    rw [Finset.sum_ite_eq']
    simp
  rw [hsum]

/-- The primitive-character sum appearing on the right of the Bombieri–Vinogradov reduction. -/
def primSumQ (x Q : ℕ) : ℝ :=
  ∑ c ∈ Finset.Icc 2 Q, ((c.totient : ℕ) : ℝ)⁻¹ * ∑ ψ ∈ primChars c, ‖chiSum c ψ x‖

lemma primSumQ_nonneg (x Q : ℕ) : 0 ≤ primSumQ x Q := by
  unfold primSumQ
  apply Finset.sum_nonneg
  intro c _
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro ψ _
  exact norm_nonneg _

/-- Each primitive non-principal character mod `q ≥ 2` is not the principal character. -/
lemma isPrimitive_ne_one {q : ℕ} [NeZero q] (hq : 2 ≤ q) {ψ : DirichletCharacter ℂ q} (h : ψ.IsPrimitive) :
    ψ ≠ 1 := by
  intro h1
  have hc : ψ.conductor = 1 := (DirichletCharacter.eq_one_iff_conductor_eq_one (χ := ψ)).mp h1
  have hcq : ψ.conductor = q := (DirichletCharacter.isPrimitive_def ψ).mp h
  omega

/-- Polylog is eventually dominated by any power (with an explicit constant). -/
lemma eventually_log_pow_mul_rpow_le (n : ℕ) (a : ℝ) (ha : 0 < a) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℕ in Filter.atTop, c * (Real.log (x : ℝ)) ^ n ≤ (x : ℝ) ^ a := by
  have h : (fun y : ℝ => Real.log y ^ n) =o[Filter.atTop] fun y : ℝ => y ^ a := by
    simpa only [Real.rpow_natCast] using isLittleO_log_rpow_rpow_atTop (n : ℝ) ha
  have h3 := h.comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [h3.def (inv_pos.mpr hc), Filter.eventually_ge_atTop (1 : ℕ)] with N hN hN1
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  have hN' : (Real.log (N : ℝ)) ^ n ≤ c⁻¹ * (N : ℝ) ^ a := by
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog n),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) a)] using hN
  calc c * (Real.log (N : ℝ)) ^ n ≤ c * (c⁻¹ * (N : ℝ) ^ a) := mul_le_mul_of_nonneg_left hN' hc.le
    _ = (N : ℝ) ^ a := by field_simp

/-- `Σ_{p ≤ N} 1/√p ≤ 2√N`. -/
lemma sum_inv_sqrt_Icc_le (N : ℕ) :
    (∑ p ∈ Finset.Icc 1 N, (1 : ℝ) / Real.sqrt (p : ℝ)) ≤ 2 * Real.sqrt (N : ℝ) := by
  have hterm : ∀ p ∈ Finset.Icc 1 N,
      (1 : ℝ) / Real.sqrt (p : ℝ) ≤ 2 * (Real.sqrt (p : ℝ) - Real.sqrt (((p - 1 : ℕ) : ℝ))) := by
    intro p hp
    rw [Finset.mem_Icc] at hp
    have hp1 : 1 ≤ p := hp.1
    have hspos : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < p))
    have hnn : 0 ≤ Real.sqrt (((p - 1 : ℕ) : ℝ)) := Real.sqrt_nonneg _
    have hpos_sum : 0 < Real.sqrt (p : ℝ) + Real.sqrt (((p - 1 : ℕ) : ℝ)) := by linarith
    have hsq : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) := by
      rw [← sq, Real.sq_sqrt (by positivity)]
    have hsq' : Real.sqrt (((p - 1 : ℕ) : ℝ)) * Real.sqrt (((p - 1 : ℕ) : ℝ)) = (((p - 1 : ℕ) : ℝ)) := by
      rw [← sq, Real.sq_sqrt (by positivity)]
    have hcast : (((p - 1 : ℕ) : ℝ)) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ p)]; norm_num
    have hdiff : Real.sqrt (p : ℝ) - Real.sqrt (((p - 1 : ℕ) : ℝ))
        = 1 / (Real.sqrt (p : ℝ) + Real.sqrt (((p - 1 : ℕ) : ℝ))) := by
      rw [eq_div_iff (ne_of_gt hpos_sum)]
      nlinarith [hsq, hsq', hcast]
    have hle : Real.sqrt (p : ℝ) + Real.sqrt (((p - 1 : ℕ) : ℝ)) ≤ 2 * Real.sqrt (p : ℝ) := by
      have h1 : Real.sqrt (((p - 1 : ℕ) : ℝ)) ≤ Real.sqrt (p : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast (show (p - 1 : ℕ) ≤ p by omega))
      linarith
    rw [div_le_iff₀ hspos, hdiff]
    have hle2 : (1 : ℝ) ≤ 2 * Real.sqrt (p : ℝ)
        / (Real.sqrt (p : ℝ) + Real.sqrt (((p - 1 : ℕ) : ℝ))) := by
      rw [le_div_iff₀ hpos_sum]; linarith
    calc (1 : ℝ) ≤ 2 * Real.sqrt (p : ℝ) / (Real.sqrt (p : ℝ) + Real.sqrt (((p - 1 : ℕ) : ℝ))) := hle2
      _ = 2 * (1 / (Real.sqrt (p : ℝ) + Real.sqrt (((p - 1 : ℕ) : ℝ)))) * Real.sqrt (p : ℝ) := by ring
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    rw [Finset.Icc_eq_empty (by omega : ¬ (1 ≤ 0)), Finset.sum_empty]
    simp
  · calc (∑ p ∈ Finset.Icc 1 N, (1 : ℝ) / Real.sqrt (p : ℝ))
        ≤ ∑ p ∈ Finset.Icc 1 N, 2 * (Real.sqrt (p : ℝ) - Real.sqrt (((p - 1 : ℕ) : ℝ))) :=
          Finset.sum_le_sum hterm
      _ = 2 * ∑ p ∈ Finset.Icc 1 N, (Real.sqrt (p : ℝ) - Real.sqrt (((p - 1 : ℕ) : ℝ))) := by
          rw [Finset.mul_sum]
      _ = 2 * Real.sqrt (N : ℝ) := by
          congr 1
          have hte : (∑ p ∈ Finset.Icc 1 N,
                (Real.sqrt (p : ℝ) - Real.sqrt (((p - 1 : ℕ) : ℝ))))
              = ∑ p ∈ Finset.Icc 1 N,
                ((fun i : ℕ => Real.sqrt (((i - 1 : ℕ) : ℝ))) (p + 1)
                  - (fun i : ℕ => Real.sqrt (((i - 1 : ℕ) : ℝ))) p) := by
            apply Finset.sum_congr rfl
            intro p hp
            simp only
            rw [show ((p + 1 - 1 : ℕ)) = p by omega]
          rw [hte, Finset.sum_Icc_sub (by omega : 1 ≤ N) (fun i : ℕ => Real.sqrt (((i - 1 : ℕ) : ℝ)))]
          simp


/-- **Small-moduli (Siegel–Walfisz) part** of the primitive character sum. -/
lemma primSumQ_small (A₀ B₀ : ℝ) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (∑ q ∈ Finset.Icc 2 ⌊(Real.log (x : ℝ)) ^ B₀⌋₊,
        ((q.totient : ℕ) : ℝ)⁻¹ * ∑ ψ ∈ primChars q, ‖chiSum q ψ x‖)
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A₀ := by
  obtain hSW := siegel_walfisz_chi_range (A₀ + B₀ + 2) B₀ (by linarith) hB₀
  have hex1 : ∀ᶠ x : ℕ in Filter.atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 1)
  filter_upwards [hSW, hex1] with x hSWx hlog1
  set L : ℝ := Real.log (x : ℝ) with hL
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hlog1
  have hxnn : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hden : 0 < L ^ (A₀ + B₀ + 2) := Real.rpow_pos_of_pos hLpos _
  have hdenpos : 0 < L ^ A₀ := Real.rpow_pos_of_pos hLpos _
  have hterm : ∀ q ∈ Finset.Icc 2 ⌊L ^ B₀⌋₊,
      ((q.totient : ℕ) : ℝ)⁻¹ * ∑ ψ ∈ primChars q, ‖chiSum q ψ x‖
        ≤ (x : ℝ) / L ^ (A₀ + B₀ + 2) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    obtain ⟨hq2, hqR⟩ := hq
    haveI : NeZero q := ⟨by omega⟩
    have hqphi : 0 < (q.totient : ℝ) := by
      have : 0 < q.totient := Nat.totient_pos.mpr (by omega)
      exact_mod_cast this
    have hbound : ∀ ψ ∈ primChars q, ‖chiSum q ψ x‖ ≤ (x : ℝ) / L ^ (A₀ + B₀ + 2) := by
      intro ψ hψ
      rw [primChars, Finset.mem_filter] at hψ
      have hprim : ψ.IsPrimitive := hψ.2
      have hne : ψ ≠ 1 := isPrimitive_ne_one hq2 hprim
      have hqle : q ≤ ⌊L ^ B₀⌋₊ := hqR
      have hres := hSWx (q := q) hqle ψ hprim hne
      simpa only [chiSum, hL] using hres
    have hsum : (∑ ψ ∈ primChars q, ‖chiSum q ψ x‖)
        ≤ (primChars q).card * ((x : ℝ) / L ^ (A₀ + B₀ + 2)) := by
      calc (∑ ψ ∈ primChars q, ‖chiSum q ψ x‖)
          ≤ ∑ _ψ ∈ primChars q, ((x : ℝ) / L ^ (A₀ + B₀ + 2)) := Finset.sum_le_sum hbound
        _ = (primChars q).card * ((x : ℝ) / L ^ (A₀ + B₀ + 2)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((primChars q).card : ℝ) ≤ (q.totient : ℝ) := by
      have hq : (primChars q).card ≤ q.totient := by
        have h := card_primitive_le_totient q
        rw [primChars]
        exact h
      exact_mod_cast hq
    have hstep : ((q.totient : ℕ) : ℝ)⁻¹ * (∑ ψ ∈ primChars q, ‖chiSum q ψ x‖)
        ≤ ((q.totient : ℕ) : ℝ)⁻¹ * ((q.totient : ℝ) * ((x : ℝ) / L ^ (A₀ + B₀ + 2))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact le_trans hsum (mul_le_mul_of_nonneg_right hcard (by positivity))
    calc ((q.totient : ℕ) : ℝ)⁻¹ * (∑ ψ ∈ primChars q, ‖chiSum q ψ x‖)
        ≤ ((q.totient : ℕ) : ℝ)⁻¹ * ((q.totient : ℝ) * ((x : ℝ) / L ^ (A₀ + B₀ + 2))) := hstep
      _ = (x : ℝ) / L ^ (A₀ + B₀ + 2) := by
          field_simp
  calc (∑ q ∈ Finset.Icc 2 ⌊L ^ B₀⌋₊, ((q.totient : ℕ) : ℝ)⁻¹ * ∑ ψ ∈ primChars q, ‖chiSum q ψ x‖)
      ≤ ∑ _q ∈ Finset.Icc 2 ⌊L ^ B₀⌋₊, (x : ℝ) / L ^ (A₀ + B₀ + 2) := Finset.sum_le_sum hterm
    _ = ((Finset.Icc 2 ⌊L ^ B₀⌋₊).card : ℝ) * ((x : ℝ) / L ^ (A₀ + B₀ + 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (L ^ B₀) * ((x : ℝ) / L ^ (A₀ + B₀ + 2)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have h1 : ((Finset.Icc 2 ⌊L ^ B₀⌋₊).card : ℝ) ≤ ((⌊L ^ B₀⌋₊ : ℕ) : ℝ) := by
          rw [Nat.card_Icc]
          have : (⌊L ^ B₀⌋₊ + 1 - 2 : ℕ) ≤ ⌊L ^ B₀⌋₊ := by omega
          exact_mod_cast this
        exact le_trans h1 (Nat.floor_le (Real.rpow_nonneg hLpos.le B₀))
    _ = (x : ℝ) * (L ^ B₀ / L ^ (A₀ + B₀ + 2)) := by ring
    _ ≤ (x : ℝ) / L ^ A₀ := by
        rw [show (x : ℝ) / L ^ A₀ = (x : ℝ) * ((L ^ A₀)⁻¹) by rw [div_eq_mul_inv]]
        apply mul_le_mul_of_nonneg_left _ hxnn
        have hExp : L ^ (-(A₀ + 2)) ≤ L ^ (-A₀) :=
          Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
        rw [Real.rpow_neg hLpos.le, Real.rpow_neg hLpos.le] at hExp
        rw [show L ^ B₀ / L ^ (A₀ + B₀ + 2) = L ^ (-(A₀ + 2)) by
              rw [← Real.rpow_sub hLpos]; congr 1; ring, Real.rpow_neg hLpos.le]
        exact hExp

end

/-- **Large-moduli part** of the primitive character sum, via summation by parts and the
Vaughan mean-value theorem. -/
lemma primSumQ_large (Cm Km : ℝ) (hCm : 0 < Cm) (hKm : 0 < Km)
    (hMVT : ∀ x Q : ℕ, 4 ≤ x → 1 ≤ Q → Q ^ 2 ≤ x →
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) * ∑ ψ ∈ primChars q, ‖chiSum q ψ x‖)
        ≤ Cm * ((x : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)
            + (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) + (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ))
          * (Real.log ((x : ℝ) + 2)) ^ Km)
    (A : ℝ) (hA : 0 < A) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (∑ q ∈ Finset.Ioc ⌊(Real.log (x : ℝ)) ^ (4 * (⌈Km + A⌉₊ + 5) + 200)⌋₊
          ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ (4 * (⌈Km + A⌉₊ + 5) + 200)⌋₊,
        ((q.totient : ℕ) : ℝ)⁻¹ * ∑ ψ ∈ primChars q, ‖chiSum q ψ x‖)
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  set Ka : ℕ := ⌈Km + A⌉₊ + 5 with hKa
  set B : ℕ := 4 * Ka + 200 with hB
  set Kc : ℕ := ⌈Km⌉₊ + 1 with hKc
  set κ : ℝ := 64 * Cm * (2 : ℝ) ^ Kc + 64 with hκ
  have hκpos : 0 < κ := by rw [hκ]; positivity
  have hCκ : Cm * (2 : ℝ) ^ Kc ≤ κ := by
    rw [hκ]
    nlinarith [hCm, pow_pos (show (0 : ℝ) < 2 by norm_num) Kc]
  have hKcK : Km ≤ (Kc : ℝ) := by
    rw [hKc]; push_cast
    linarith [Nat.le_ceil Km]
  have hKa_ge : Km + A + 5 ≤ (Ka : ℝ) := by
    rw [hKa]; push_cast
    linarith [Nat.le_ceil (Km + A)]
  have hKaA : A + 1 ≤ (Ka : ℝ) := by linarith [hKa_ge, hKm]
  have hB_ge : (Kc : ℝ) + A + 200 ≤ (B : ℝ) := by
    have hceil : ⌈Km⌉₊ ≤ ⌈Km + A⌉₊ := Nat.ceil_mono (by linarith)
    rw [hB, hKc, hKa]; push_cast
    have h5 : ((⌈Km⌉₊ : ℕ) : ℝ) ≤ ((⌈Km + A⌉₊ : ℕ) : ℝ) := by exact_mod_cast hceil
    have h7 : A ≤ ((⌈Km + A⌉₊ : ℕ) : ℝ) := le_trans (by linarith : A ≤ Km + A) (Nat.le_ceil _)
    have h8 : (0 : ℝ) ≤ ((⌈Km + A⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [h5, h7, h8]
  have hL2 : ∀ᶠ x : ℕ in Filter.atTop, (2 : ℝ) ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 2)
  have hx4 : ∀ᶠ x : ℕ in Filter.atTop, 4 ≤ x := Filter.eventually_ge_atTop 4
  have hF1 : ∀ᶠ x : ℕ in Filter.atTop, κ ≤ (Real.log (x : ℝ)) ^ 100 := by
    have h := le_log_rpow_eventually (b := (100 : ℝ)) (c := κ) (by norm_num) hκpos.le
    simpa [Real.rpow_natCast] using h
  have hF2 : ∀ᶠ x : ℕ in Filter.atTop,
      64 * κ * (Real.log (x : ℝ)) ^ (B + Kc + Ka) ≤ (x : ℝ) ^ (1 / 2 : ℝ) := by
    have h := eventually_log_pow_mul_rpow_le (B + Kc + Ka) (1 / 2 : ℝ) (by norm_num) (64 * κ)
      (by positivity)
    simpa only [mul_assoc] using h
  have hF3 : ∀ᶠ x : ℕ in Filter.atTop,
      48 * κ * (Real.log (x : ℝ)) ^ (Kc + Ka) ≤ (x : ℝ) ^ (1 / 12 : ℝ) := by
    have h := eventually_log_pow_mul_rpow_le (Kc + Ka) (1 / 12 : ℝ) (by norm_num) (48 * κ)
      (by positivity)
    simpa only [mul_assoc] using h
  have hF4 : ∀ᶠ x : ℕ in Filter.atTop,
      32 * κ * (Real.log (x : ℝ)) ^ (Kc + 1 + Ka) ≤ (x : ℝ) ^ (1 / 6 : ℝ) := by
    have h := eventually_log_pow_mul_rpow_le (Kc + 1 + Ka) (1 / 6 : ℝ) (by norm_num) (32 * κ)
      (by positivity)
    simpa only [mul_assoc] using h
  have hF5 : ∀ᶠ x : ℕ in Filter.atTop, 2 * (Real.log (x : ℝ)) ^ B ≤ Real.sqrt (x : ℝ) := by
    have h := eventually_log_pow_mul_rpow_le B (1 / 2 : ℝ) (by norm_num) (2 : ℝ) (by norm_num)
    filter_upwards [h] with x hx
    rw [Real.sqrt_eq_rpow]; exact hx
  have hF6 : ∀ᶠ x : ℕ in Filter.atTop, (Real.log (x : ℝ)) ^ (2 * B) ≤ Real.sqrt (x : ℝ) := by
    have h := eventually_log_pow_mul_rpow_le (2 * B) (1 / 2 : ℝ) (by norm_num) (1 : ℝ) (by norm_num)
    filter_upwards [h] with x hx
    rw [Real.sqrt_eq_rpow]; simpa using hx
  have hF7 : ∀ᶠ x : ℕ in Filter.atTop, (2 : ℝ) ≤ (Real.log (x : ℝ)) ^ B := by
    have h := le_log_rpow_eventually (b := (B : ℝ)) (c := (2 : ℝ)) (by positivity) (by norm_num)
    simpa [Real.rpow_natCast] using h
  filter_upwards [hL2, hx4, hF1, hF2, hF3, hF4, hF5, hF6, hF7] with x hL2 hx4 hF1 hF2 hF3 hF4 hF5 hF6 hF7
  set L : ℝ := Real.log (x : ℝ) with hLdef
  have hLpos : 0 < L := by linarith
  have hLnn : 0 ≤ L := le_of_lt hLpos
  have hL1 : 1 ≤ L := by linarith
  have hxnn : 0 ≤ (x : ℝ) := Nat.cast_nonneg x
  have hxpos : 0 < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx2r : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 2 ≤ x)
  have hsqrt_pos : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr hxpos
  have hsq_sqrt : Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) = (x : ℝ) := by
    rw [← sq, Real.sq_sqrt hxnn]
  have hLBpos : 0 < L ^ B := pow_pos hLpos B
  have hLKa_pos : 0 < L ^ Ka := pow_pos hLpos Ka
  have hLKB_pos : 0 < L ^ Kc := pow_pos hLpos Kc
  set Q : ℕ := ⌊Real.sqrt (x : ℝ) / L ^ B⌋₊ with hQdef
  set R : ℕ := ⌊L ^ B⌋₊ with hRdef
  have hy2 : 2 ≤ Real.sqrt (x : ℝ) / L ^ B := by
    rw [le_div_iff₀ hLBpos]; linarith [hF5]
  have hQ1 : 1 ≤ Q := by
    rw [hQdef]
    apply Nat.le_floor
    push_cast
    linarith [hy2]
  have hQpos : 0 < Q := lt_of_lt_of_le Nat.zero_lt_one hQ1
  have hQz : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQpos
  have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQz
  have hQy_le : (Q : ℝ) ≤ Real.sqrt (x : ℝ) / L ^ B := by
    rw [hQdef]; exact Nat.floor_le (by positivity)
  have hQy_ge : Real.sqrt (x : ℝ) / (2 * L ^ B) ≤ (Q : ℝ) := by
    have h1 : Real.sqrt (x : ℝ) / L ^ B < (Q : ℝ) + 1 := by
      rw [hQdef]; exact Nat.lt_floor_add_one _
    have h2 : Real.sqrt (x : ℝ) / (2 * L ^ B) = Real.sqrt (x : ℝ) / L ^ B / 2 := by
      rw [div_mul_eq_div_div]; ring
    rw [h2]; linarith
  have hQ2x : Q ^ 2 ≤ x := by
    have h1 : (Q : ℝ) ≤ Real.sqrt (x : ℝ) := by
      refine le_trans hQy_le ?_
      rw [div_le_iff₀ hLBpos]
      nlinarith [Real.sqrt_nonneg (x : ℝ), one_le_pow₀ hL1 (n := B)]
    have h2 : ((Q : ℝ)) ^ 2 ≤ (x : ℝ) := by
      have hs := Real.sq_sqrt hxnn
      nlinarith [h1, Real.sqrt_nonneg (x : ℝ), hs]
    exact_mod_cast h2
  have hR1 : 1 ≤ R := by
    rw [hRdef]; apply Nat.le_floor; push_cast; linarith [hF7]
  have hR2 : 2 ≤ R := by
    rw [hRdef]; apply Nat.le_floor; push_cast; linarith [hF7]
  have hRge : L ^ B / 2 ≤ (R : ℝ) := by
    have h1 : L ^ B < (R : ℝ) + 1 := by rw [hRdef]; exact Nat.lt_floor_add_one _
    linarith [hF7]
  have hRQ : R ≤ Q := by
    rw [hRdef, hQdef]
    apply Nat.floor_mono
    rw [le_div_iff₀ hLBpos]
    calc L ^ B * L ^ B = L ^ (2 * B) := by rw [← pow_add]; ring_nf
      _ ≤ Real.sqrt (x : ℝ) := hF6
  have hlogKm : Cm * (Real.log ((x : ℝ) + 2)) ^ Km ≤ κ * L ^ Kc := by
    have h1 : Real.log ((x : ℝ) + 2) ≤ 2 * L := by
      rw [hLdef]
      have h1a : (x : ℝ) + 2 ≤ (x : ℝ) ^ 2 := by nlinarith [hx2r]
      have h1b : 0 < (x : ℝ) + 2 := by positivity
      calc Real.log ((x : ℝ) + 2) ≤ Real.log ((x : ℝ) ^ 2) := Real.log_le_log h1b h1a
        _ = 2 * Real.log (x : ℝ) := by rw [Real.log_pow]; norm_num
    have h1nn : 0 ≤ Real.log ((x : ℝ) + 2) := Real.log_nonneg (by linarith)
    have h2 : (Real.log ((x : ℝ) + 2)) ^ Km ≤ (2 * L) ^ (Kc : ℝ) :=
      le_trans (Real.rpow_le_rpow h1nn h1 hKm.le)
        (Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ 2 * L) hKcK)
    have h3 : (2 * L) ^ (Kc : ℝ) = (2 : ℝ) ^ Kc * L ^ Kc := by
      rw [Real.mul_rpow (by norm_num) hLnn, Real.rpow_natCast, Real.rpow_natCast]
    have h4 : Cm * ((2 : ℝ) ^ Kc * L ^ Kc) ≤ κ * L ^ Kc := by
      rw [show Cm * ((2 : ℝ) ^ Kc * L ^ Kc) = (Cm * (2 : ℝ) ^ Kc) * L ^ Kc by ring]
      exact mul_le_mul_of_nonneg_right hCκ (le_of_lt hLKB_pos)
    calc Cm * (Real.log ((x : ℝ) + 2)) ^ Km ≤ Cm * ((2 : ℝ) ^ Kc * L ^ Kc) :=
          mul_le_mul_of_nonneg_left (le_trans h2 (le_of_eq h3)) hCm.le
      _ ≤ κ * L ^ Kc := h4
  have hsqrtQ : Real.sqrt (Q : ℝ) ≤ (x : ℝ) ^ (1 / 4 : ℝ) := by
    have h1 : (Q : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) := by
      refine le_trans hQy_le ?_
      rw [div_le_iff₀ hLBpos, Real.sqrt_eq_rpow]
      nlinarith [one_le_pow₀ hL1 (n := B), Real.rpow_nonneg hxnn (1 / 2 : ℝ)]
    calc Real.sqrt (Q : ℝ) = (Q : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
      _ ≤ ((x : ℝ) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg Q) h1 (by norm_num)
      _ = (x : ℝ) ^ (1 / 4 : ℝ) := by rw [← Real.rpow_mul hxnn]; norm_num
  set f : ℕ → ℝ := fun q => ((q.totient : ℕ) : ℝ)⁻¹ * ∑ ψ ∈ primChars q, ‖chiSum q ψ x‖ with hfdef
  set S : ℕ → ℝ := fun t => ∑ q ∈ Finset.Icc 1 t,
      ((q : ℝ) / (q.totient : ℝ)) * ∑ ψ ∈ primChars q, ‖chiSum q ψ x‖ with hSdef
  have hSnn : ∀ t, 0 ≤ S t := by
    intro t; simp only [hSdef]
    apply Finset.sum_nonneg
    intro q _
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun ψ _ => norm_nonneg _))
  have hSid : ∀ q, 1 ≤ q → S q = S (q - 1) + (q : ℝ) * f q := by
    intro q hq
    have htop := Finset.sum_Icc_succ_top (a := 1) (b := q - 1) (by omega)
        (fun r => ((r : ℝ) / (r.totient : ℝ)) * ∑ ψ ∈ primChars r, ‖chiSum r ψ x‖)
    rw [Nat.sub_add_cancel hq] at htop
    simp only [hSdef, hfdef]
    rw [htop]
    congr 1
    rw [div_eq_mul_inv]
    ring
  have hSbound : ∀ t, 1 ≤ t → t ≤ Q → S t ≤ κ * L ^ Kc * ((x : ℝ) + (t : ℝ) ^ 2 * Real.sqrt (x : ℝ)
      + (x : ℝ) ^ (5 / 6 : ℝ) * (t : ℝ) + (x : ℝ) ^ (2 / 3 : ℝ) * (t : ℝ) ^ (3 / 2 : ℝ)) := by
    intro t ht1 ht
    have ht2 : t ^ 2 ≤ x := le_trans (Nat.pow_le_pow_left ht 2) hQ2x
    have h := hMVT x t (by omega) ht1 ht2
    calc S t ≤ Cm * ((x : ℝ) + (t : ℝ) ^ 2 * Real.sqrt (x : ℝ) + (x : ℝ) ^ (5 / 6 : ℝ) * (t : ℝ)
          + (x : ℝ) ^ (2 / 3 : ℝ) * (t : ℝ) ^ (3 / 2 : ℝ)) * (Real.log ((x : ℝ) + 2)) ^ Km := h
      _ = (Cm * (Real.log ((x : ℝ) + 2)) ^ Km) * ((x : ℝ) + (t : ℝ) ^ 2 * Real.sqrt (x : ℝ)
          + (x : ℝ) ^ (5 / 6 : ℝ) * (t : ℝ) + (x : ℝ) ^ (2 / 3 : ℝ) * (t : ℝ) ^ (3 / 2 : ℝ)) := by
          ring
      _ ≤ (κ * L ^ Kc) * ((x : ℝ) + (t : ℝ) ^ 2 * Real.sqrt (x : ℝ)
          + (x : ℝ) ^ (5 / 6 : ℝ) * (t : ℝ) + (x : ℝ) ^ (2 / 3 : ℝ) * (t : ℝ) ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hlogKm (by positivity)
      _ = κ * L ^ Kc * ((x : ℝ) + (t : ℝ) ^ 2 * Real.sqrt (x : ℝ)
          + (x : ℝ) ^ (5 / 6 : ℝ) * (t : ℝ) + (x : ℝ) ^ (2 / 3 : ℝ) * (t : ℝ) ^ (3 / 2 : ℝ)) := by
          ring
  have hf_eq : (∑ q ∈ Finset.Ioc R Q, f q)
      = ∑ q ∈ Finset.Ioc R Q, (S q - S (q - 1)) / (q : ℝ) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mem_Ioc] at hq
    have hq1 : 1 ≤ q := by omega
    have hq0 : ((q : ℝ)) ≠ 0 := by
      have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
      linarith
    have hid := hSid q hq1
    rw [hid, add_sub_cancel_left, mul_div_cancel_left₀ (f q) hq0]
  have habel := sum_Ioc_sub_div_le S hSnn R Q hR1 hRQ
  have hSQ : S Q / (Q : ℝ) ≤ κ * L ^ Kc * (2 * Real.sqrt (x : ℝ) * L ^ B
      + (x : ℝ) / L ^ B + (x : ℝ) ^ (5 / 6 : ℝ) + (x : ℝ) ^ (11 / 12 : ℝ)) := by
    have hbound := hSbound Q hQ1 le_rfl
    have hstep : S Q / (Q : ℝ) ≤ (κ * L ^ Kc) * (((x : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)
        + (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) + (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ))
        / (Q : ℝ)) := by
      have h0 := div_le_div_of_nonneg_right hbound (le_of_lt hQz)
      rwa [← mul_div_assoc'] at h0
    refine le_trans hstep (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have e1 : (x : ℝ) / (Q : ℝ) ≤ 2 * Real.sqrt (x : ℝ) * L ^ B := by
      rw [div_le_iff₀ hQz]
      have h3 : Real.sqrt (x : ℝ) ≤ (Q : ℝ) * (2 * L ^ B) := by
        have h4 := hQy_ge
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * L ^ B)] at h4
        linarith
      nlinarith [h3, hsq_sqrt, Real.sqrt_nonneg (x : ℝ), hLBpos.le]
    have e2 : (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ) / (Q : ℝ) ≤ (x : ℝ) / L ^ B := by
      have hQ2 : (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ) / (Q : ℝ) = (Q : ℝ) * Real.sqrt (x : ℝ) := by
        field_simp <;> ring
      rw [hQ2, le_div_iff₀ hLBpos]
      have h4 : (Q : ℝ) * L ^ B ≤ Real.sqrt (x : ℝ) := by
        have h5 := hQy_le
        rw [le_div_iff₀ hLBpos] at h5
        exact h5
      nlinarith [mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg (x : ℝ)), hsq_sqrt]
    have e3 : (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) / (Q : ℝ) ≤ (x : ℝ) ^ (5 / 6 : ℝ) := by
      rw [mul_div_assoc, div_self hQne, mul_one]
    have e4 : (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) / (Q : ℝ) ≤ (x : ℝ) ^ (11 / 12 : ℝ) := by
      have hQ32 : (Q : ℝ) ^ (3 / 2 : ℝ) / (Q : ℝ) = Real.sqrt (Q : ℝ) := by
        have hsplit : (Q : ℝ) ^ (3 / 2 : ℝ) = (Q : ℝ) ^ (1 : ℝ) * (Q : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add hQz]; norm_num
        rw [hsplit, Real.rpow_one, Real.sqrt_eq_rpow]
        field_simp <;> ring
      have hrew : (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) / (Q : ℝ)
          = (x : ℝ) ^ (2 / 3 : ℝ) * Real.sqrt (Q : ℝ) := by
        rw [← mul_div_assoc', hQ32]
      rw [hrew]
      calc (x : ℝ) ^ (2 / 3 : ℝ) * Real.sqrt (Q : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ) * (x : ℝ) ^ (1 / 4 : ℝ) :=
            mul_le_mul_of_nonneg_left hsqrtQ (Real.rpow_nonneg hxnn _)
        _ = (x : ℝ) ^ (11 / 12 : ℝ) := by rw [← Real.rpow_add hxpos]; norm_num
    have hsplit2 : ((x : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ) + (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ)
        + (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ)) / (Q : ℝ)
        = (x : ℝ) / (Q : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ) / (Q : ℝ)
          + (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) / (Q : ℝ)
          + (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) / (Q : ℝ) := by
      rw [add_div, add_div, add_div]
    rw [hsplit2]
    linarith [e1, e2, e3, e4]
  have hps : (∑ p ∈ Finset.Icc R (Q - 1), S p / ((p : ℝ) * ((p + 1 : ℕ) : ℝ)))
      ≤ κ * L ^ Kc * (2 * (x : ℝ) / L ^ B + (x : ℝ) / L ^ B
          + (x : ℝ) ^ (5 / 6 : ℝ) * L + 2 * (x : ℝ) ^ (11 / 12 : ℝ)) := by
    have hstep : ∀ p ∈ Finset.Icc R (Q - 1), S p / ((p : ℝ) * ((p + 1 : ℕ) : ℝ))
        ≤ κ * L ^ Kc * ((x : ℝ) / ((p : ℝ) * ((p + 1 : ℕ) : ℝ))
            + Real.sqrt (x : ℝ) * (p : ℝ) / ((p : ℝ) + 1)
            + (x : ℝ) ^ (5 / 6 : ℝ) / ((p : ℝ) + 1)
            + (x : ℝ) ^ (2 / 3 : ℝ) * Real.sqrt (p : ℝ) / ((p : ℝ) + 1)) := by
      intro p hp
      rw [Finset.mem_Icc] at hp
      have hpQ : p ≤ Q := by omega
      have hp1 : 1 ≤ p := le_trans hR1 hp.1
      have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
      have hp1pos : (0 : ℝ) < (p : ℝ) + 1 := by linarith
      have hden : (0 : ℝ) < (p : ℝ) * ((p : ℝ) + 1) := by positivity
      have hpc : ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 := by push_cast; ring
      rw [hpc]
      have hSp := hSbound p hp1 hpQ
      have hkey : ((x : ℝ) + (p : ℝ) ^ 2 * Real.sqrt (x : ℝ) + (x : ℝ) ^ (5 / 6 : ℝ) * (p : ℝ)
            + (x : ℝ) ^ (2 / 3 : ℝ) * (p : ℝ) ^ (3 / 2 : ℝ)) / ((p : ℝ) * ((p : ℝ) + 1))
          = (x : ℝ) / ((p : ℝ) * ((p : ℝ) + 1)) + Real.sqrt (x : ℝ) * (p : ℝ) / ((p : ℝ) + 1)
            + (x : ℝ) ^ (5 / 6 : ℝ) / ((p : ℝ) + 1)
            + (x : ℝ) ^ (2 / 3 : ℝ) * Real.sqrt (p : ℝ) / ((p : ℝ) + 1) := by
        have hp32 : (p : ℝ) ^ (3 / 2 : ℝ) = (p : ℝ) * (p : ℝ) ^ (1 / 2 : ℝ) := by
          rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hppos, Real.rpow_one]
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, hp32]
        field_simp <;> ring
      calc S p / ((p : ℝ) * ((p : ℝ) + 1))
          ≤ (κ * L ^ Kc) * (((x : ℝ) + (p : ℝ) ^ 2 * Real.sqrt (x : ℝ)
              + (x : ℝ) ^ (5 / 6 : ℝ) * (p : ℝ)
              + (x : ℝ) ^ (2 / 3 : ℝ) * (p : ℝ) ^ (3 / 2 : ℝ))
              / ((p : ℝ) * ((p : ℝ) + 1))) := by
            have h0 := div_le_div_of_nonneg_right hSp (le_of_lt hden)
            rwa [← mul_div_assoc'] at h0
        _ = κ * L ^ Kc * ((x : ℝ) / ((p : ℝ) * ((p : ℝ) + 1)) + Real.sqrt (x : ℝ) * (p : ℝ) / ((p : ℝ) + 1)
              + (x : ℝ) ^ (5 / 6 : ℝ) / ((p : ℝ) + 1)
              + (x : ℝ) ^ (2 / 3 : ℝ) * Real.sqrt (p : ℝ) / ((p : ℝ) + 1)) := by
            rw [hkey]
    have hsum := Finset.sum_le_sum hstep
    rw [← Finset.mul_sum] at hsum
    refine le_trans hsum (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hb1 : (∑ p ∈ Finset.Icc R (Q - 1), (x : ℝ) / ((p : ℝ) * ((p + 1 : ℕ) : ℝ)))
        ≤ 2 * (x : ℝ) / L ^ B := by
      have h1 : (∑ p ∈ Finset.Icc R (Q - 1), (x : ℝ) / ((p : ℝ) * ((p + 1 : ℕ) : ℝ)))
          = (x : ℝ) * ∑ p ∈ Finset.Icc R (Q - 1), 1 / ((p : ℝ) * ((p + 1 : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p hp; ring
      rw [h1]
      have h2 : (∑ p ∈ Finset.Icc R (Q - 1), 1 / ((p : ℝ) * ((p + 1 : ℕ) : ℝ))) ≤ 2 / L ^ B := by
        have h3 : (∑ p ∈ Finset.Icc R (Q - 1), 1 / ((p : ℝ) * ((p + 1 : ℕ) : ℝ))) ≤ 1 / (R : ℝ) :=
          sum_Icc_inv_mul_succ_le_inv R (Q - 1) hR1
        calc _ ≤ 1 / (R : ℝ) := h3
          _ ≤ 2 / L ^ B := by
              rw [div_le_div_iff₀ (by positivity) (by positivity)]
              linarith [hRge]
      calc (x : ℝ) * (∑ p ∈ Finset.Icc R (Q - 1), 1 / ((p : ℝ) * ((p + 1 : ℕ) : ℝ)))
          ≤ (x : ℝ) * (2 / L ^ B) := mul_le_mul_of_nonneg_left h2 hxnn
        _ = 2 * (x : ℝ) / L ^ B := by ring
    have hb2 : (∑ p ∈ Finset.Icc R (Q - 1), Real.sqrt (x : ℝ) * (p : ℝ) / ((p : ℝ) + 1))
        ≤ (x : ℝ) / L ^ B := by
      have h1 : ∀ p ∈ Finset.Icc R (Q - 1),
          Real.sqrt (x : ℝ) * (p : ℝ) / ((p : ℝ) + 1) ≤ Real.sqrt (x : ℝ) := by
        intro p hp
        rw [Finset.mem_Icc] at hp
        have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (le_trans hR1 hp.1)
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) + 1)]
        nlinarith [Real.sqrt_nonneg (x : ℝ), hp1]
      calc (∑ p ∈ Finset.Icc R (Q - 1), Real.sqrt (x : ℝ) * (p : ℝ) / ((p : ℝ) + 1))
          ≤ ∑ _p ∈ Finset.Icc R (Q - 1), Real.sqrt (x : ℝ) := Finset.sum_le_sum h1
        _ = ((Finset.Icc R (Q - 1)).card : ℝ) * Real.sqrt (x : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (Q : ℝ) * Real.sqrt (x : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
            have hc : (Finset.Icc R (Q - 1)).card ≤ Q := by rw [Nat.card_Icc]; omega
            exact_mod_cast hc
        _ ≤ (x : ℝ) / L ^ B := by
            calc (Q : ℝ) * Real.sqrt (x : ℝ) ≤ (Real.sqrt (x : ℝ) / L ^ B) * Real.sqrt (x : ℝ) :=
                  mul_le_mul_of_nonneg_right hQy_le (Real.sqrt_nonneg _)
              _ = (x : ℝ) / L ^ B := by rw [div_mul_eq_mul_div, hsq_sqrt]
    have hb3 : (∑ p ∈ Finset.Icc R (Q - 1), (x : ℝ) ^ (5 / 6 : ℝ) / ((p : ℝ) + 1))
        ≤ (x : ℝ) ^ (5 / 6 : ℝ) * L := by
      rcases Nat.eq_zero_or_pos (Q - 1 - R + 1) with hz | hz
      · have hem : Finset.Icc R (Q - 1) = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
        rw [hem, Finset.sum_empty]
        exact mul_nonneg (Real.rpow_nonneg hxnn _) hLnn
      · have h1 : (∑ p ∈ Finset.Icc R (Q - 1), (x : ℝ) ^ (5 / 6 : ℝ) / ((p : ℝ) + 1))
            = (x : ℝ) ^ (5 / 6 : ℝ) * ∑ p ∈ Finset.Icc R (Q - 1), 1 / ((p : ℝ) + 1) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p hp; ring
        rw [h1]
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hxnn _)
        have h2 : (∑ p ∈ Finset.Icc R (Q - 1), 1 / ((p : ℝ) + 1))
            ≤ Real.log (((Q - 1 : ℕ) : ℝ) + 1) - Real.log (R : ℝ) := by
          have h2' := sum_Icc_inv_succ_le_log R (Q - 1) hR1 (by omega : R ≤ (Q - 1) + 1)
          simpa only [Nat.cast_add, Nat.cast_one] using h2'
        have h3 : Real.log (((Q - 1 : ℕ) : ℝ) + 1) ≤ L := by
          have h4 : (((Q - 1 : ℕ) : ℝ) + 1) = (Q : ℝ) := by
            rw [Nat.cast_sub hQ1, Nat.cast_one]; ring
          rw [h4]
          calc Real.log (Q : ℝ) ≤ Real.log (Real.sqrt (x : ℝ)) :=
                Real.log_le_log (by positivity) (by
                  refine le_trans hQy_le ?_
                  rw [div_le_iff₀ hLBpos]
                  nlinarith [one_le_pow₀ hL1 (n := B)])
            _ = L / 2 := by rw [Real.log_sqrt hxnn, hLdef]
            _ ≤ L := by linarith
        have h5 : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast hR1)
        linarith [h2, h3, h5]
    have hb4 : (∑ p ∈ Finset.Icc R (Q - 1), (x : ℝ) ^ (2 / 3 : ℝ) * Real.sqrt (p : ℝ) / ((p : ℝ) + 1))
        ≤ 2 * (x : ℝ) ^ (11 / 12 : ℝ) := by
      have h1 : ∀ p ∈ Finset.Icc R (Q - 1), (x : ℝ) ^ (2 / 3 : ℝ) * Real.sqrt (p : ℝ) / ((p : ℝ) + 1)
          ≤ (x : ℝ) ^ (2 / 3 : ℝ) * (1 / Real.sqrt (p : ℝ)) := by
        intro p hp
        rw [Finset.mem_Icc] at hp
        have hp1 : 1 ≤ p := le_trans hR1 hp.1
        have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
        have hsp : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hppos
        have hx23 : (0 : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg hxnn _
        have hkey : Real.sqrt (p : ℝ) / ((p : ℝ) + 1) ≤ 1 / Real.sqrt (p : ℝ) := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) + 1)]
          rw [show (1 : ℝ) / Real.sqrt (p : ℝ) * ((p : ℝ) + 1)
              = ((p : ℝ) + 1) / Real.sqrt (p : ℝ) by ring]
          rw [le_div_iff₀ hsp, Real.mul_self_sqrt (le_of_lt hppos)]
          linarith
        calc (x : ℝ) ^ (2 / 3 : ℝ) * Real.sqrt (p : ℝ) / ((p : ℝ) + 1)
            = (x : ℝ) ^ (2 / 3 : ℝ) * (Real.sqrt (p : ℝ) / ((p : ℝ) + 1)) := by ring
          _ ≤ (x : ℝ) ^ (2 / 3 : ℝ) * (1 / Real.sqrt (p : ℝ)) :=
              mul_le_mul_of_nonneg_left hkey hx23
      calc (∑ p ∈ Finset.Icc R (Q - 1), (x : ℝ) ^ (2 / 3 : ℝ) * Real.sqrt (p : ℝ) / ((p : ℝ) + 1))
          ≤ ∑ p ∈ Finset.Icc R (Q - 1), (x : ℝ) ^ (2 / 3 : ℝ) * (1 / Real.sqrt (p : ℝ)) :=
            Finset.sum_le_sum h1
        _ = (x : ℝ) ^ (2 / 3 : ℝ) * ∑ p ∈ Finset.Icc R (Q - 1), 1 / Real.sqrt (p : ℝ) := by
            rw [Finset.mul_sum]
        _ ≤ (x : ℝ) ^ (2 / 3 : ℝ) * (2 * Real.sqrt (Q : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hxnn _)
            have h2 : (∑ p ∈ Finset.Icc R (Q - 1), 1 / Real.sqrt (p : ℝ))
                ≤ ∑ p ∈ Finset.Icc 1 (Q - 1), 1 / Real.sqrt (p : ℝ) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro p hp; rw [Finset.mem_Icc] at hp ⊢; omega
              · intro p _ _; positivity
            calc (∑ p ∈ Finset.Icc R (Q - 1), 1 / Real.sqrt (p : ℝ))
                ≤ ∑ p ∈ Finset.Icc 1 (Q - 1), 1 / Real.sqrt (p : ℝ) := h2
              _ ≤ 2 * Real.sqrt ((Q - 1 : ℕ) : ℝ) := sum_inv_sqrt_Icc_le (Q - 1)
              _ ≤ 2 * Real.sqrt (Q : ℝ) := by
                  apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt _) (by norm_num)
                  exact_mod_cast (Nat.sub_le Q 1)
        _ ≤ (x : ℝ) ^ (2 / 3 : ℝ) * (2 * (x : ℝ) ^ (1 / 4 : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hxnn _)
            linarith [hsqrtQ]
        _ = 2 * (x : ℝ) ^ (11 / 12 : ℝ) := by
            rw [show (x : ℝ) ^ (2 / 3 : ℝ) * (2 * (x : ℝ) ^ (1 / 4 : ℝ))
                = 2 * ((x : ℝ) ^ (2 / 3 : ℝ) * (x : ℝ) ^ (1 / 4 : ℝ)) by ring,
                ← Real.rpow_add hxpos]; norm_num
    linarith [hb1, hb2, hb3, hb4]
  have hpowKa : ∀ {c : ℝ}, c ≤ 2 → c ≤ L ^ ((Ka : ℝ) - A) := by
    intro c hc
    calc c ≤ (2 : ℝ) := hc
      _ ≤ L ^ (1 : ℝ) := by simpa using hL2
      _ ≤ L ^ ((Ka : ℝ) - A) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [hKa_ge, hKm])
  have hLa : 2 * L ^ A ≤ L ^ Ka := by
    have hpow : (2 : ℝ) ≤ L ^ ((Ka : ℝ) - A) := hpowKa le_rfl
    rw [(Real.rpow_natCast L Ka).symm,
      show (Ka : ℝ) = A + ((Ka : ℝ) - A) by ring, Real.rpow_add hLpos]
    nlinarith [hpow, Real.rpow_pos_of_pos hLpos A]
  have hk1 : κ * L ^ Kc * (2 * Real.sqrt (x : ℝ) * L ^ B) ≤ (x : ℝ) / (L ^ A) / 16 := by
    have hA1 : κ * L ^ (B + Kc + Ka) ≤ (x : ℝ) ^ (1 / 2 : ℝ) / 64 := by linarith [hF2]
    have h2 : κ * L ^ (B + Kc) = κ * L ^ (B + Kc + Ka) / L ^ Ka := by
      rw [show L ^ (B + Kc + Ka) = L ^ (B + Kc) * L ^ Ka by rw [← pow_add]]
      field_simp <;> ring
    have h3 : κ * L ^ (B + Kc) ≤ (x : ℝ) ^ (1 / 2 : ℝ) / L ^ Ka / 64 := by
      rw [h2]
      calc κ * L ^ (B + Kc + Ka) / L ^ Ka ≤ ((x : ℝ) ^ (1 / 2 : ℝ) / 64) / L ^ Ka :=
            div_le_div_of_nonneg_right hA1 (by positivity)
        _ = (x : ℝ) ^ (1 / 2 : ℝ) / L ^ Ka / 64 := by ring
    have hp : L ^ Kc * L ^ B = L ^ (B + Kc) := by rw [← pow_add, Nat.add_comm]
    calc κ * L ^ Kc * (2 * Real.sqrt (x : ℝ) * L ^ B)
        = κ * (2 * Real.sqrt (x : ℝ)) * (L ^ Kc * L ^ B) := by ring
      _ = κ * (2 * Real.sqrt (x : ℝ)) * L ^ (B + Kc) := by rw [hp]
      _ = 2 * Real.sqrt (x : ℝ) * (κ * L ^ (B + Kc)) := by ring
      _ ≤ 2 * Real.sqrt (x : ℝ) * ((x : ℝ) ^ (1 / 2 : ℝ) / L ^ Ka / 64) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (x : ℝ) / (L ^ Ka * 32) := by
          rw [Real.sqrt_eq_rpow]
          have hx12 : (x : ℝ) ^ (1 / 2 : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) = (x : ℝ) := by
            rw [← Real.rpow_add hxpos]; norm_num
          have he : 2 * (x : ℝ) ^ (1 / 2 : ℝ) * ((x : ℝ) ^ (1 / 2 : ℝ) / L ^ Ka / 64)
              = (2 * ((x : ℝ) ^ (1 / 2 : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ))) / (L ^ Ka * 64) := by
            rw [div_div]; ring
          rw [he, hx12]
          rw [show 2 * (x : ℝ) / (L ^ Ka * 64) = (x : ℝ) / (L ^ Ka * 32) by field_simp <;> ring]
      _ ≤ (x : ℝ) / (L ^ A * 16) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hxnn, hLa, Real.rpow_pos_of_pos hLpos A]
      _ = (x : ℝ) / (L ^ A) / 16 := by rw [div_div]
  have hk2 : κ * L ^ Kc * (2 * (x : ℝ) / L ^ B) ≤ (x : ℝ) / (L ^ A) / 16 := by
    have h1 : κ * L ^ Kc / L ^ B ≤ L ^ (-(A) - 100) := by
      have hsplit : κ * L ^ Kc / L ^ B = κ * L ^ ((Kc : ℝ) - (B : ℝ)) := by
        rw [← mul_div_assoc']
        congr 1
        rw [(Real.rpow_natCast L Kc).symm, (Real.rpow_natCast L B).symm, ← Real.rpow_sub hLpos]
      rw [hsplit]
      have h2 : κ ≤ L ^ (100 : ℝ) := by
        have hc : (L : ℝ) ^ (100 : ℝ) = L ^ 100 := by
          have : (100 : ℝ) = ((100 : ℕ) : ℝ) := by norm_num
          rw [this, Real.rpow_natCast]
        rw [hc]; exact hF1
      calc κ * L ^ ((Kc : ℝ) - (B : ℝ)) ≤ L ^ (100 : ℝ) * L ^ ((Kc : ℝ) - (B : ℝ)) :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hLnn _)
        _ = L ^ ((100 : ℝ) + ((Kc : ℝ) - (B : ℝ))) := by rw [← Real.rpow_add hLpos]
        _ ≤ L ^ (-(A) - 100) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [hB_ge])
    calc κ * L ^ Kc * (2 * (x : ℝ) / L ^ B) = 2 * (x : ℝ) * (κ * L ^ Kc / L ^ B) := by ring
      _ ≤ 2 * (x : ℝ) * L ^ (-(A) - 100) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * (x : ℝ) / (L ^ A * L ^ (100 : ℝ)) := by
          rw [show -(A) - 100 = (-(A)) + (-(100 : ℝ)) by ring, Real.rpow_add hLpos,
            Real.rpow_neg hLpos.le, Real.rpow_neg hLpos.le]
          ring
      _ ≤ (x : ℝ) / (L ^ A) / 16 := by
          rw [show (x : ℝ) / (L ^ A) / 16 = (x : ℝ) / (L ^ A * 16) by rw [div_div]]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h4 : (32 : ℝ) ≤ L ^ (100 : ℝ) := by
            have h4' : (32 : ℝ) ≤ L ^ 100 := by
              calc (32 : ℝ) ≤ (2 : ℝ) ^ 100 := by norm_num
                _ ≤ L ^ 100 := pow_le_pow_left₀ (by norm_num) hL2 100
            have hc : (L : ℝ) ^ (100 : ℝ) = L ^ 100 := by
              have : (100 : ℝ) = ((100 : ℕ) : ℝ) := by norm_num
              rw [this, Real.rpow_natCast]
            rw [hc]; exact h4'
          have h5 : (32 : ℝ) * ((x : ℝ) * L ^ A) ≤ L ^ (100 : ℝ) * ((x : ℝ) * L ^ A) :=
            mul_le_mul_of_nonneg_right h4 (by positivity)
          nlinarith [h5]
  have hk3 : κ * L ^ Kc * (3 * (x : ℝ) ^ (11 / 12 : ℝ)) ≤ (x : ℝ) / (L ^ A) / 16 := by
    have h1 : κ * L ^ Kc ≤ (x : ℝ) ^ (1 / 12 : ℝ) / L ^ Ka / 48 := by
      have h2 : 48 * κ * L ^ (Kc + Ka) = 48 * κ * L ^ Kc * L ^ Ka := by rw [pow_add]; ring
      have h3 : 48 * κ * L ^ Kc ≤ (x : ℝ) ^ (1 / 12 : ℝ) / L ^ Ka := by
        have h4 : 48 * κ * L ^ (Kc + Ka) / L ^ Ka ≤ (x : ℝ) ^ (1 / 12 : ℝ) / L ^ Ka :=
          div_le_div_of_nonneg_right hF3 (by positivity)
        rwa [h2, mul_div_assoc, div_self (ne_of_gt hLKa_pos), mul_one] at h4
      rw [show κ * L ^ Kc = 48 * κ * L ^ Kc / 48 by ring]
      exact div_le_div_of_nonneg_right h3 (by norm_num)
    calc κ * L ^ Kc * (3 * (x : ℝ) ^ (11 / 12 : ℝ))
        ≤ ((x : ℝ) ^ (1 / 12 : ℝ) / L ^ Ka / 48) * (3 * (x : ℝ) ^ (11 / 12 : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 3 * (x : ℝ) / (L ^ Ka * 48) := by
          have hx1 : (x : ℝ) ^ (1 / 12 : ℝ) * (x : ℝ) ^ (11 / 12 : ℝ) = (x : ℝ) := by
            rw [← Real.rpow_add hxpos]; norm_num
          have he : ((x : ℝ) ^ (1 / 12 : ℝ) / L ^ Ka / 48) * (3 * (x : ℝ) ^ (11 / 12 : ℝ))
              = (3 * ((x : ℝ) ^ (1 / 12 : ℝ) * (x : ℝ) ^ (11 / 12 : ℝ))) / (L ^ Ka * 48) := by
            rw [div_div]; ring
          rw [he, hx1]
      _ ≤ (x : ℝ) / (L ^ A) / 16 := by
          rw [show (x : ℝ) / (L ^ A) / 16 = (x : ℝ) / (L ^ A * 16) by rw [div_div]]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hxnn, hLa, Real.rpow_pos_of_pos hLpos A]
  have hk4 : κ * L ^ Kc * ((x : ℝ) ^ (5 / 6 : ℝ) * (1 + L)) ≤ (x : ℝ) / (L ^ A) / 16 := by
    have h1 : κ * L ^ Kc * (1 + L) ≤ 2 * κ * L ^ (Kc + 1) := by
      have hlt : (1 + L) ≤ 2 * L := by linarith
      calc κ * L ^ Kc * (1 + L) ≤ κ * L ^ Kc * (2 * L) := mul_le_mul_of_nonneg_left hlt (by positivity)
        _ = 2 * κ * L ^ (Kc + 1) := by rw [pow_succ]; ring
    have h2 : 2 * κ * L ^ (Kc + 1) ≤ (x : ℝ) ^ (1 / 6 : ℝ) / L ^ Ka / 16 := by
      have h3 : 32 * κ * L ^ (Kc + 1 + Ka) = 32 * κ * L ^ (Kc + 1) * L ^ Ka := by rw [pow_add]; ring
      have h4 : 32 * κ * L ^ (Kc + 1) ≤ (x : ℝ) ^ (1 / 6 : ℝ) / L ^ Ka := by
        have h5 : 32 * κ * L ^ (Kc + 1 + Ka) / L ^ Ka ≤ (x : ℝ) ^ (1 / 6 : ℝ) / L ^ Ka :=
          div_le_div_of_nonneg_right hF4 (by positivity)
        rwa [h3, mul_div_assoc, div_self (ne_of_gt hLKa_pos), mul_one] at h5
      rw [show 2 * κ * L ^ (Kc + 1) = 32 * κ * L ^ (Kc + 1) / 16 by ring]
      exact div_le_div_of_nonneg_right h4 (by norm_num)
    calc κ * L ^ Kc * ((x : ℝ) ^ (5 / 6 : ℝ) * (1 + L))
        = (x : ℝ) ^ (5 / 6 : ℝ) * (κ * L ^ Kc * (1 + L)) := by ring
      _ ≤ (x : ℝ) ^ (5 / 6 : ℝ) * (2 * κ * L ^ (Kc + 1)) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hxnn _)
      _ ≤ (x : ℝ) ^ (5 / 6 : ℝ) * ((x : ℝ) ^ (1 / 6 : ℝ) / L ^ Ka / 16) :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hxnn _)
      _ = (x : ℝ) / (L ^ Ka * 16) := by
          have hx16 : (x : ℝ) ^ (5 / 6 : ℝ) * (x : ℝ) ^ (1 / 6 : ℝ) = (x : ℝ) := by
            rw [← Real.rpow_add hxpos]; norm_num
          have he : (x : ℝ) ^ (5 / 6 : ℝ) * ((x : ℝ) ^ (1 / 6 : ℝ) / L ^ Ka / 16)
              = ((x : ℝ) ^ (5 / 6 : ℝ) * (x : ℝ) ^ (1 / 6 : ℝ)) / (L ^ Ka * 16) := by
            rw [div_div]; ring
          rw [he, hx16]
      _ ≤ (x : ℝ) / (L ^ A) / 16 := by
          rw [show (x : ℝ) / (L ^ A) / 16 = (x : ℝ) / (L ^ A * 16) by rw [div_div]]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hxnn, hLa, Real.rpow_pos_of_pos hLpos A]
  have hcomb : S Q / (Q : ℝ) + (∑ p ∈ Finset.Icc R (Q - 1), S p / ((p : ℝ) * ((p + 1 : ℕ) : ℝ)))
      ≤ (x : ℝ) / (L ^ A) := by
    have hsum : S Q / (Q : ℝ) + (∑ p ∈ Finset.Icc R (Q - 1), S p / ((p : ℝ) * ((p + 1 : ℕ) : ℝ)))
        ≤ κ * L ^ Kc * (2 * Real.sqrt (x : ℝ) * L ^ B + (x : ℝ) / L ^ B + (x : ℝ) ^ (5 / 6 : ℝ)
            + (x : ℝ) ^ (11 / 12 : ℝ))
          + κ * L ^ Kc * (2 * (x : ℝ) / L ^ B + (x : ℝ) / L ^ B + (x : ℝ) ^ (5 / 6 : ℝ) * L
            + 2 * (x : ℝ) ^ (11 / 12 : ℝ)) := add_le_add hSQ hps
    have hall : κ * L ^ Kc * (2 * Real.sqrt (x : ℝ) * L ^ B) + κ * L ^ Kc * (2 * (x : ℝ) / L ^ B)
        + κ * L ^ Kc * (2 * (x : ℝ) / L ^ B) + κ * L ^ Kc * (3 * (x : ℝ) ^ (11 / 12 : ℝ))
        + κ * L ^ Kc * ((x : ℝ) ^ (5 / 6 : ℝ) * (1 + L)) ≤ (x : ℝ) / (L ^ A) := by
      have hsum5 : κ * L ^ Kc * (2 * Real.sqrt (x : ℝ) * L ^ B) + κ * L ^ Kc * (2 * (x : ℝ) / L ^ B)
          + κ * L ^ Kc * (2 * (x : ℝ) / L ^ B) + κ * L ^ Kc * (3 * (x : ℝ) ^ (11 / 12 : ℝ))
          + κ * L ^ Kc * ((x : ℝ) ^ (5 / 6 : ℝ) * (1 + L))
          ≤ (x : ℝ) / (L ^ A) / 16 + (x : ℝ) / (L ^ A) / 16 + (x : ℝ) / (L ^ A) / 16
            + (x : ℝ) / (L ^ A) / 16 + (x : ℝ) / (L ^ A) / 16 := by
        linarith [hk1, hk2, hk3, hk4]
      refine le_trans hsum5 ?_
      have hfin : (x : ℝ) / (L ^ A) / 16 * 5 ≤ (x : ℝ) / (L ^ A) := by
        have hLA : (0 : ℝ) < L ^ A := Real.rpow_pos_of_pos hLpos A
        field_simp <;> nlinarith [hxnn]
      calc (x : ℝ) / (L ^ A) / 16 + (x : ℝ) / (L ^ A) / 16 + (x : ℝ) / (L ^ A) / 16
            + (x : ℝ) / (L ^ A) / 16 + (x : ℝ) / (L ^ A) / 16
          = (x : ℝ) / (L ^ A) / 16 * 5 := by ring
        _ ≤ (x : ℝ) / (L ^ A) := hfin
    have hid : κ * L ^ Kc * (2 * Real.sqrt (x : ℝ) * L ^ B + (x : ℝ) / L ^ B
          + (x : ℝ) ^ (5 / 6 : ℝ) + (x : ℝ) ^ (11 / 12 : ℝ))
        + κ * L ^ Kc * (2 * (x : ℝ) / L ^ B + (x : ℝ) / L ^ B + (x : ℝ) ^ (5 / 6 : ℝ) * L
          + 2 * (x : ℝ) ^ (11 / 12 : ℝ))
        = κ * L ^ Kc * (2 * Real.sqrt (x : ℝ) * L ^ B) + κ * L ^ Kc * (2 * (x : ℝ) / L ^ B)
          + κ * L ^ Kc * (2 * (x : ℝ) / L ^ B) + κ * L ^ Kc * (3 * (x : ℝ) ^ (11 / 12 : ℝ))
          + κ * L ^ Kc * ((x : ℝ) ^ (5 / 6 : ℝ) * (1 + L)) := by ring
    exact le_trans (le_trans hsum (le_of_eq hid)) hall
  calc (∑ q ∈ Finset.Ioc R Q, f q)
      = ∑ q ∈ Finset.Ioc R Q, (S q - S (q - 1)) / (q : ℝ) := hf_eq
    _ ≤ S Q / (Q : ℝ) + (∑ p ∈ Finset.Icc R (Q - 1), S p / ((p : ℝ) * ((p + 1 : ℕ) : ℝ))) := habel
    _ ≤ (x : ℝ) / (L ^ A) := hcomb

end Commons.NumberTheory.BombieriVinogradov

namespace Commons.NumberTheory.BombieriVinogradov

/-- Polylog is eventually dominated by any positive power (real-exponent version). -/
lemma eventually_const_mul_rpow_le_rpow (b a c : ℝ) (hc : 0 < c) (ha : 0 < a) :
    ∀ᶠ x : ℕ in Filter.atTop, c * (Real.log (x : ℝ)) ^ b ≤ (x : ℝ) ^ a := by
  have h : (fun y : ℝ => Real.log y ^ b) =o[Filter.atTop] (fun y : ℝ => y ^ a) :=
    isLittleO_log_rpow_rpow_atTop b ha
  have h3 := h.comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [h3.def (inv_pos.mpr hc), Filter.eventually_ge_atTop (1 : ℕ)] with N hN hN1
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  have hN' : (Real.log (N : ℝ)) ^ b ≤ c⁻¹ * (N : ℝ) ^ a := by
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog b),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) a)] using hN
  calc c * (Real.log (N : ℝ)) ^ b ≤ c * (c⁻¹ * (N : ℝ) ^ a) := mul_le_mul_of_nonneg_left hN' hc.le
    _ = (N : ℝ) ^ a := by field_simp

/-- **Small + large moduli combine**: the primitive-character sum up to `√x/(log x)^B`
is `≤ x/(log x)^A`. -/
lemma primSumQ_bound (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in Filter.atTop,
      primSumQ x ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ ≤
        (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  obtain ⟨Cm, Km, hCm, hKm, hMVT⟩ := vaughan_mean_value_sqrt
  set A' : ℝ := A + 2 with hA'def
  have hA' : 0 < A' := by rw [hA'def]; linarith
  set M : ℕ := 4 * (⌈Km + A'⌉₊ + 5) + 200 with hMdef
  refine ⟨(M : ℝ), by positivity, ?_⟩
  simp only [Real.rpow_natCast]
  have hlarge := primSumQ_large Cm Km hCm hKm hMVT A' hA'
  have hsmall := primSumQ_small A' (M : ℝ) hA' (by positivity)
  have hL2 : ∀ᶠ x : ℕ in Filter.atTop, (2 : ℝ) ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 2)
  have hx4 : ∀ᶠ x : ℕ in Filter.atTop, 4 ≤ x := Filter.eventually_ge_atTop 4
  have hsmall' : ∀ᶠ x : ℕ in Filter.atTop,
      primSumQ x ⌊(Real.log (x : ℝ)) ^ M⌋₊ ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A' := by
    filter_upwards [hsmall] with x hx
    simp only [Real.rpow_natCast] at hx
    exact hx
  have hR2 : ∀ᶠ x : ℕ in Filter.atTop, 2 ≤ ⌊(Real.log (x : ℝ)) ^ M⌋₊ := by
    have h : ∀ᶠ x : ℕ in Filter.atTop, (2 : ℝ) ≤ (Real.log (x : ℝ)) ^ M := by
      have h0 := le_log_rpow_eventually (b := (M : ℝ)) (c := (2 : ℝ)) (by positivity) (by norm_num)
      simpa [Real.rpow_natCast] using h0
    filter_upwards [h] with x hx
    apply Nat.le_floor
    push_cast
    exact hx
  have hReq : ∀ᶠ x : ℕ in Filter.atTop,
      ⌊(Real.log (x : ℝ)) ^ M⌋₊ ≤ ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ M⌋₊ := by
    have h : ∀ᶠ x : ℕ in Filter.atTop,
        (Real.log (x : ℝ)) ^ M ≤ Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ M := by
      have h0 := eventually_log_pow_mul_rpow_le (2 * M) (1 / 2 : ℝ) (by norm_num) (1 : ℝ)
        (by norm_num)
      have h1 : ∀ᶠ x : ℕ in Filter.atTop, (1 : ℝ) ≤ Real.log (x : ℝ) :=
        tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 1)
      filter_upwards [h0, h1] with x hx hx1
      have hLp : 0 < Real.log (x : ℝ) := lt_of_lt_of_le one_pos hx1
      rw [Real.sqrt_eq_rpow, le_div_iff₀ (pow_pos hLp M)]
      rw [← pow_add]
      have hMN : M + M = 2 * M := by ring
      rw [hMN]
      simpa using hx
    filter_upwards [h] with x hx
    exact Nat.floor_mono hx
  filter_upwards [hsmall', hlarge, hL2, hx4, hR2, hReq] with
    x hsmallx hlargex hlog2 hx4x hR2x hReqx
  set L : ℝ := Real.log (x : ℝ) with hLdef
  set Q : ℕ := ⌊Real.sqrt (x : ℝ) / L ^ M⌋₊ with hQdef
  set R : ℕ := ⌊L ^ M⌋₊ with hRdef
  have hLpos : 0 < L := by linarith
  have hLnn : 0 ≤ L := le_of_lt hLpos
  have hL1 : 1 ≤ L := by linarith
  have hxnn : 0 ≤ (x : ℝ) := Nat.cast_nonneg x
  have hunion : Finset.Icc 2 Q = Finset.Icc 2 R ∪ Finset.Ioc R Q := by
    ext a
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 2 R) (Finset.Ioc R Q) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_Icc] at ha
    simp only [Finset.mem_Ioc] at ha'
    omega
  have hdec : primSumQ x Q = primSumQ x R
      + ∑ q ∈ Finset.Ioc R Q, ((q.totient : ℕ) : ℝ)⁻¹ * ∑ ψ ∈ primChars q, ‖chiSum q ψ x‖ := by
    unfold primSumQ
    rw [hunion, Finset.sum_union hdisj]
  rw [hdec]
  have hhead : primSumQ x R ≤ (x : ℝ) / L ^ A' := hsmallx
  have htail : (∑ q ∈ Finset.Ioc R Q, ((q.totient : ℕ) : ℝ)⁻¹ * ∑ ψ ∈ primChars q, ‖chiSum q ψ x‖)
      ≤ (x : ℝ) / L ^ A' := hlargex
  refine le_trans (add_le_add hhead htail) ?_
  rw [hA'def]
  have h2LA : 2 * L ^ A ≤ L ^ (A + 2) := by
    have hL2sq : (2 : ℝ) ≤ L ^ (2 : ℝ) := by
      calc (2 : ℝ) ≤ L ^ (1 : ℝ) := by simpa [Real.rpow_one] using hlog2
        _ ≤ L ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    rw [Real.rpow_add hLpos]
    nlinarith [hL2sq, Real.rpow_nonneg hLnn A]
  rw [← add_div,
    div_le_div_iff₀ (Real.rpow_pos_of_pos hLpos _) (Real.rpow_pos_of_pos hLpos A)]
  nlinarith [h2LA, hxnn]

theorem bombieri_vinogradov_characterSum :
    ∀ A : ℝ, 0 < A →
    ∃ B : ℝ, 0 < B ∧
    ∀ᶠ x : ℕ in Filter.atTop,
      (∑ q ∈ Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊,
        (Nat.totient q : ℝ)⁻¹ *
          ((∑ χ : DirichletCharacter ℂ q,
              ‖∑ n ∈ Finset.range (x + 1),
                (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q))‖)
            - ‖∑ n ∈ Finset.range (x + 1),
                (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
                  * (1 : DirichletCharacter ℂ q) (n : ZMod q))‖))
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  intro A hA
  set K : ℕ := ⌈A⌉₊ + 4 with hKdef
  have hKA4 : A + 4 ≤ (K : ℝ) := by rw [hKdef]; push_cast; linarith [Nat.le_ceil A]
  obtain ⟨B, hBpos, hBV⟩ := primSumQ_bound (K : ℝ) (by positivity)
  refine ⟨B, hBpos, ?_⟩
  obtain ⟨C, hCpos, hCred⟩ := character_sum_primitive_reduction
  have hL2 : ∀ᶠ x : ℕ in Filter.atTop, (2 : ℝ) ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 2)
  have hx4 : ∀ᶠ x : ℕ in Filter.atTop, 4 ≤ x := Filter.eventually_ge_atTop 4
  have h8C2 : ∀ᶠ x : ℕ in Filter.atTop, 8 * C ≤ (Real.log (x : ℝ)) ^ 2 := by
    have h0 := le_log_rpow_eventually (b := (2 : ℝ)) (c := 8 * C) (by norm_num) (by positivity)
    simpa [Real.rpow_natCast] using h0
  have h16C : ∀ᶠ x : ℕ in Filter.atTop,
      16 * C * (Real.log (x : ℝ)) ^ (A + 3) ≤ Real.sqrt (x : ℝ) := by
    have h0 := eventually_const_mul_rpow_le_rpow (A + 3) (1 / 2 : ℝ) (16 * C)
      (by positivity) (by norm_num)
    filter_upwards [h0] with x hx
    rwa [Real.sqrt_eq_rpow]
  have hB1 : ∀ᶠ x : ℕ in Filter.atTop, 1 ≤ ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ := by
    have h0 : ∀ᶠ x : ℕ in Filter.atTop,
        (2 : ℝ) * (Real.log (x : ℝ)) ^ B ≤ Real.sqrt (x : ℝ) := by
      have h1 := eventually_const_mul_rpow_le_rpow B (1 / 2 : ℝ) (2 : ℝ) (by norm_num) (by norm_num)
      filter_upwards [h1] with x hx
      rwa [Real.sqrt_eq_rpow]
    filter_upwards [h0, hL2] with x hx hlog2
    have hLBpos : 0 < (Real.log (x : ℝ)) ^ B :=
      Real.rpow_pos_of_pos (by linarith : 0 < Real.log (x : ℝ)) B
    have hLBnn : 0 ≤ (Real.log (x : ℝ)) ^ B := le_of_lt hLBpos
    apply Nat.le_floor
    push_cast
    rw [le_div_iff₀ hLBpos]
    linarith
  have hQle : ∀ᶠ x : ℕ in Filter.atTop,
      (((⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ : ℕ)) : ℝ) ≤ Real.sqrt (x : ℝ) := by
    filter_upwards [hL2] with x hlog2
    have hLB : 0 < (Real.log (x : ℝ)) ^ B :=
      Real.rpow_pos_of_pos (by linarith : 0 < Real.log (x : ℝ)) B
    have h1 : ((⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ : ℕ) : ℝ)
        ≤ Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B := Nat.floor_le (by positivity)
    calc (((⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ : ℕ)) : ℝ)
        ≤ Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B := h1
      _ ≤ Real.sqrt (x : ℝ) := by
          rw [div_le_iff₀ hLB]
          have h2 : (1 : ℝ) ≤ (Real.log (x : ℝ)) ^ B :=
            Real.one_le_rpow (by linarith) hBpos.le
          nlinarith [h2, Real.sqrt_nonneg (x : ℝ)]
  have hlogQ : ∀ᶠ x : ℕ in Filter.atTop,
      Real.log (2 * (((⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ : ℕ)) : ℝ) + 2)
        ≤ 2 * Real.log (x : ℝ) := by
    filter_upwards [hQle, hx4] with x hQlex hx4x
    have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
    have hxnn : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
    have hsqrt : Real.sqrt (x : ℝ) ≤ (x : ℝ) := by
      have h1 : (1 : ℝ) ≤ Real.sqrt (x : ℝ) := Real.one_le_sqrt.mpr hx1
      calc Real.sqrt (x : ℝ) = Real.sqrt (x : ℝ) * 1 := by ring
        _ ≤ Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) :=
            mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
        _ = (x : ℝ) := Real.mul_self_sqrt hxnn
    have h1 : 2 * ((⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ : ℕ) : ℝ) + 2
        ≤ (x : ℝ) ^ 2 := by
      have hx4r : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx4x
      nlinarith [hQlex, hsqrt]
    have h2 : 0 < 2 * ((⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ : ℕ) : ℝ) + 2 := by
      positivity
    calc Real.log (2 * ((⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ : ℕ) : ℝ) + 2)
        ≤ Real.log ((x : ℝ) ^ 2) := Real.log_le_log h2 h1
      _ = 2 * Real.log (x : ℝ) := by rw [Real.log_pow]; norm_num
  have hlogx : ∀ᶠ x : ℕ in Filter.atTop, Real.log ((x : ℝ) + 2) ≤ 2 * Real.log (x : ℝ) := by
    filter_upwards [hx4] with x hx4x
    have hx4r : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx4x
    have h1 : (x : ℝ) + 2 ≤ (x : ℝ) ^ 2 := by nlinarith
    have h2 : 0 < (x : ℝ) + 2 := by linarith
    calc Real.log ((x : ℝ) + 2) ≤ Real.log ((x : ℝ) ^ 2) := Real.log_le_log h2 h1
      _ = 2 * Real.log (x : ℝ) := by rw [Real.log_pow]; norm_num
  filter_upwards [hBV, hL2, hx4, h8C2, h16C, hB1, hQle, hlogQ, hlogx] with
    x hBVx hlog2 hx4x h8C2x h16Cx hB1x hQlex hlogQx hlogxx
  set L : ℝ := Real.log (x : ℝ) with hLdef
  set Q : ℕ := ⌊Real.sqrt (x : ℝ) / L ^ B⌋₊ with hQdef
  set Lq : ℝ := Real.log (2 * (Q : ℝ) + 2) with hLqdef
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hLnn : 0 ≤ L := le_of_lt hLpos
  have hxnn : 0 ≤ (x : ℝ) := Nat.cast_nonneg x
  have hsq_sqrt : Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) = (x : ℝ) := by
    rw [← sq, Real.sq_sqrt hxnn]
  have hLqnn : 0 ≤ Lq :=
    Real.log_nonneg (by have h : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q; linarith)
  have hlogx2nn : 0 ≤ Real.log ((x : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hLHS : (∑ q ∈ Finset.Icc 1 Q,
        (Nat.totient q : ℝ)⁻¹ *
          ((∑ χ : DirichletCharacter ℂ q,
              ‖∑ n ∈ Finset.range (x + 1),
                (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q))‖)
            - ‖∑ n ∈ Finset.range (x + 1),
                (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
                  * (1 : DirichletCharacter ℂ q) (n : ZMod q))‖))
      = ∑ q ∈ Finset.Icc 1 Q, (Nat.totient q : ℝ)⁻¹ * npSum x q := by
    apply Finset.sum_congr rfl
    intro q hq
    congr 1
    rw [npSum_eq]
    simp only [chiSum]
  rw [hLHS]
  have hCred_x := hCred x Q hB1x
  have hT1 : C * Lq ^ 2 * primSumQ x Q ≤ (x : ℝ) / (2 * L ^ A) := by
    have hLq2 : Lq ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ hLqnn hlogQx 2
    have hCL2 : C * Lq ^ 2 ≤ 4 * C * L ^ 2 := by
      calc C * Lq ^ 2 ≤ C * (2 * L) ^ 2 := mul_le_mul_of_nonneg_left hLq2 hCpos.le
        _ = 4 * C * L ^ 2 := by ring
    have h8CA : 8 * C * L ^ 2 * L ^ A ≤ L ^ (K : ℝ) := by
      have h4 : L ^ 2 * L ^ 2 = L ^ 4 := by rw [← pow_add]
      have h6 : L ^ 4 = L ^ (4 : ℝ) := by
        rw [← Real.rpow_natCast L 4]; congr 1
      calc 8 * C * L ^ 2 * L ^ A = (8 * C) * (L ^ 2 * L ^ A) := by ring
        _ ≤ (L ^ 2) * (L ^ 2 * L ^ A) :=
            mul_le_mul_of_nonneg_right h8C2x (by positivity)
        _ = L ^ 2 * L ^ 2 * L ^ A := by ring
        _ = L ^ 4 * L ^ A := by rw [h4]
        _ = L ^ (4 : ℝ) * L ^ A := by rw [h6]
        _ = L ^ (4 + A) := by rw [← Real.rpow_add hLpos]
        _ ≤ L ^ (K : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [hKA4])
    calc C * Lq ^ 2 * primSumQ x Q
        ≤ (4 * C * L ^ 2) * ((x : ℝ) / L ^ (K : ℝ)) :=
          mul_le_mul hCL2 hBVx (primSumQ_nonneg x Q) (by positivity)
      _ = 4 * C * L ^ 2 * ((x : ℝ) / L ^ (K : ℝ)) := by ring
      _ ≤ (x : ℝ) / (2 * L ^ A) := by
          rw [mul_div_assoc',
            div_le_div_iff₀ (Real.rpow_pos_of_pos hLpos (K : ℝ)) (by positivity : (0 : ℝ) < 2 * L ^ A)]
          calc 4 * C * L ^ 2 * (x : ℝ) * (2 * L ^ A) = x * (8 * C * L ^ 2 * L ^ A) := by ring
            _ ≤ x * L ^ (K : ℝ) := mul_le_mul_of_nonneg_left h8CA hxnn
  have hT2 : C * (Q : ℝ) * Lq ^ 2 * Real.log ((x : ℝ) + 2) ≤ (x : ℝ) / (2 * L ^ A) := by
    have hLq2 : Lq ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ hLqnn hlogQx 2
    have hnn : 0 ≤ Lq ^ 2 * Real.log ((x : ℝ) + 2) :=
      mul_nonneg (sq_nonneg Lq) hlogx2nn
    have h4 : Lq ^ 2 * Real.log ((x : ℝ) + 2) ≤ (2 * L) ^ 2 * (2 * L) :=
      mul_le_mul hLq2 hlogxx hlogx2nn (by positivity)
    have h5 : C * (Q : ℝ) * (Lq ^ 2 * Real.log ((x : ℝ) + 2))
        ≤ (C * Real.sqrt (x : ℝ)) * ((2 * L) ^ 2 * (2 * L)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hQlex hCpos.le) h4 hnn (by positivity)
    calc C * (Q : ℝ) * Lq ^ 2 * Real.log ((x : ℝ) + 2)
        = C * (Q : ℝ) * (Lq ^ 2 * Real.log ((x : ℝ) + 2)) := by ring
      _ ≤ (C * Real.sqrt (x : ℝ)) * ((2 * L) ^ 2 * (2 * L)) := h5
      _ = 8 * C * Real.sqrt (x : ℝ) * L ^ 3 := by ring
      _ ≤ (x : ℝ) / (2 * L ^ A) := by
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * L ^ A)]
          have h16 : 16 * C * L ^ (3 + A) ≤ Real.sqrt (x : ℝ) := by
            have h := h16Cx
            rwa [show A + 3 = 3 + A by ring] at h
          have hL3 : L ^ 3 = L ^ (3 : ℝ) := by
            rw [← Real.rpow_natCast L 3]; congr 1
          have he : 8 * C * Real.sqrt (x : ℝ) * L ^ 3 * (2 * L ^ A)
              = 16 * C * L ^ (3 + A) * Real.sqrt (x : ℝ) := by
            calc 8 * C * Real.sqrt (x : ℝ) * L ^ 3 * (2 * L ^ A)
                = 16 * C * Real.sqrt (x : ℝ) * (L ^ 3 * L ^ A) := by ring
              _ = 16 * C * Real.sqrt (x : ℝ) * (L ^ (3 : ℝ) * L ^ A) := by rw [hL3]
              _ = 16 * C * Real.sqrt (x : ℝ) * L ^ (3 + A) := by rw [← Real.rpow_add hLpos]
              _ = 16 * C * L ^ (3 + A) * Real.sqrt (x : ℝ) := by ring
          rw [he]
          calc 16 * C * L ^ (3 + A) * Real.sqrt (x : ℝ)
              = (16 * C * L ^ (3 + A)) * Real.sqrt (x : ℝ) := by ring
            _ ≤ Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) :=
                mul_le_mul_of_nonneg_right h16 (Real.sqrt_nonneg _)
            _ = (x : ℝ) := hsq_sqrt
  refine le_trans hCred_x (le_trans (add_le_add hT1 hT2) ?_)
  rw [← add_div,
    div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * L ^ A) (Real.rpow_pos_of_pos hLpos A)]
  nlinarith [hxnn]

end Commons.NumberTheory.BombieriVinogradov
