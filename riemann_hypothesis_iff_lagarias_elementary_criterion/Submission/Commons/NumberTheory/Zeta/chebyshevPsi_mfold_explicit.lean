import Mathlib
import Submission.Commons.NumberTheory.Zeta.psi_integral_lower_bound

open Complex MeasureTheory intervalIntegral Filter
open scoped Real Topology BigOperators

noncomputable section

set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.Zeta

/-! ## Inlined zero-sum machinery

The commons modules `tiltedZeroSum_finset_rh_bound` and `psi_mfold_tiltedZeroSum_rh_bound` are
not importable together with `chebyshevPsi_at_height_farLeft_neg` (both declare the constant
`rectInt_model_multi_pole`).  We only need their statements, so we reproduce them here on top of
`zeroSum_finset_le_beta`, which *is* compatible. -/

/-- Under RH, a zero `ρ` of `ζ₁` with `1/4 < re ρ < 2` has real part `1/2`. -/
lemma re_half_of_zeta1_zero (h : RiemannHypothesis) {ρ : ℂ}
    (hρ : riemannZeta₁ ρ = 0) (h1 : (1 / 4 : ℝ) < ρ.re) (_h2 : ρ.re < 2) :
    ρ.re = 1 / 2 := by
  have hρne1 : ρ ≠ 1 := by
    intro hh
    rw [hh, riemannZeta₁_one] at hρ
    exact one_ne_zero hρ
  have hz : riemannZeta ρ = 0 := by
    rw [riemannZeta_eq_inv_sub_mul hρne1, hρ, mul_zero]
  refine h ρ hz ?_ hρne1
  rintro ⟨n, hn⟩
  rw [hn] at h1
  have hre : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by
    rw [Complex.mul_re]; simp
  rw [hre] at h1
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- Multiplicity-augmented `β`-sum bound for a finite set of zeros of `ζ₁`. -/
lemma zeta1Order_sum_le_beta (h : RiemannHypothesis) {R : ℝ} (hR : 0 ≤ R) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, riemannZeta₁ ρ = 0 ∧ ‖ρ‖ ≤ R ∧ (1 / 4 : ℝ) < ρ.re ∧ ρ.re < 2) :
    S.sum (fun ρ => (zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2)
      ≤ 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) := by
  have hb := zeroSum_finset_le_beta h R hR S hS
  refine le_trans (le_of_eq ?_) hb
  refine Finset.sum_congr rfl (fun ρ hρ => ?_)
  obtain ⟨hζ, hρR, hre, hre2⟩ := hS ρ hρ
  have hspec := Classical.choose_spec (zeta1_logDeriv_pole_removal ρ hζ)
  have hζo : zeta1Order ρ = Classical.choose (zeta1_logDeriv_pole_removal ρ hζ) := by
    unfold zeta1Order
    rw [dif_pos hζ]
  have h1 : (zeta1Order ρ : ℤ) = (MeromorphicOn.divisor (fun z : ℂ =>
      (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z)
        (Metric.closedBall 0 R)) ρ := by
    rw [hζo]
    exact divisor_xi_eq_logDeriv_pole_order hR hζ hρR hre hre2 hspec.1 hspec.2
  have h2 : (zeta1Order ρ : ℝ) = (((MeromorphicOn.divisor (fun z : ℂ =>
      (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z)
        (Metric.closedBall 0 R)) ρ : ℤ) : ℝ) := by
    rw [← h1]; norm_num
  rw [h2]

/-- Tilted pair zero-sum bound. -/
lemma tiltedZeroSum_pair_bound (h : RiemannHypothesis) (S : Finset ℂ) (x : ℝ)
    (hS : ∀ ρ ∈ S, riemannZeta₁ ρ = 0 ∧ (1 / 4 : ℝ) < ρ.re ∧ ρ.re < 2) (hx : 1 ≤ x) :
    ‖S.sum (fun ρ => (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / (ρ * (ρ + 1)))‖
      ≤ (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) * Real.sqrt x := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hterm : ∀ ρ ∈ S,
      ‖(zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / (ρ * (ρ + 1))‖
        ≤ (zeta1Order ρ : ℝ) * Real.sqrt x / ‖ρ‖ ^ 2 := by
    intro ρ hρ
    obtain ⟨hz1, hre1, hre2⟩ := hS ρ hρ
    have hhalf : ρ.re = 1 / 2 := re_half_of_zeta1_zero h hz1 hre1 hre2
    have hρne0 : ρ ≠ 0 := by rintro rfl; norm_num at hhalf
    have hsq : ‖ρ + 1‖ ^ 2 = ‖ρ‖ ^ 2 + 2 := by
      have hh := Complex.normSq_add ρ 1
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_one] at hh
      simp at hh
      rw [hh, hhalf]; ring
    have hle_norm : ‖ρ‖ ≤ ‖ρ + 1‖ := by
      have hsqle : ‖ρ‖ ^ 2 ≤ ‖ρ + 1‖ ^ 2 := by linarith [hsq]
      have := (sq_le_sq.mp hsqle)
      simpa [abs_of_nonneg (norm_nonneg _)] using this
    rw [norm_div, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos ρ, hhalf,
        ← Real.sqrt_eq_rpow, Complex.norm_natCast]
    apply div_le_div_of_nonneg_left
    · positivity
    · exact pow_pos (norm_pos_iff.mpr hρne0) 2
    · have h2 : ‖ρ‖ * ‖ρ‖ ≤ ‖ρ‖ * ‖ρ + 1‖ :=
        mul_le_mul_of_nonneg_left hle_norm (norm_nonneg ρ)
      calc ‖ρ‖ ^ 2 = ‖ρ‖ * ‖ρ‖ := by ring
        _ ≤ ‖ρ‖ * ‖ρ + 1‖ := h2
  have hsum_bound : ‖S.sum (fun ρ =>
        (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / (ρ * (ρ + 1)))‖
      ≤ S.sum (fun ρ => (zeta1Order ρ : ℝ) * Real.sqrt x / ‖ρ‖ ^ 2) :=
    le_trans (norm_sum_le S _) (Finset.sum_le_sum hterm)
  have hfactor : S.sum (fun ρ =>
        (zeta1Order ρ : ℝ) * Real.sqrt x / ‖ρ‖ ^ 2)
      = Real.sqrt x * S.sum (fun ρ => (zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ hρ
    ring
  let R : ℝ := S.sum (fun ρ => ‖ρ‖) + 1
  have hR : 0 ≤ R := by
    have : 0 ≤ S.sum (fun ρ => ‖ρ‖) := Finset.sum_nonneg (fun ρ _ => norm_nonneg ρ)
    simp only [R]; linarith
  have hSR : ∀ ρ ∈ S, riemannZeta₁ ρ = 0 ∧ ‖ρ‖ ≤ R ∧ (1 / 4 : ℝ) < ρ.re ∧ ρ.re < 2 := by
    intro ρ hρ
    obtain ⟨hz1, hre1, hre2⟩ := hS ρ hρ
    refine ⟨hz1, ?_, hre1, hre2⟩
    have hsingle : ‖ρ‖ ≤ S.sum (fun σ => ‖σ‖) :=
      Finset.single_le_sum (fun σ _ => norm_nonneg σ) hρ
    simp only [R]; linarith
  have hbound := zeta1Order_sum_le_beta h hR S hSR
  calc ‖S.sum (fun ρ => (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / (ρ * (ρ + 1)))‖
      ≤ S.sum (fun ρ => (zeta1Order ρ : ℝ) * Real.sqrt x / ‖ρ‖ ^ 2) := hsum_bound
    _ = Real.sqrt x * S.sum (fun ρ => (zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2) := hfactor
    _ ≤ Real.sqrt x * (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg x)
    _ = (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) * Real.sqrt x := by ring

lemma norm_le_norm_add_natCast_half {ρ : ℂ} (hρ : ρ.re = 1 / 2) (k : ℕ) :
    ‖ρ‖ ≤ ‖ρ + (k : ℂ)‖ := by
  have hsq : ‖ρ + (k : ℂ)‖ ^ 2 = ‖ρ‖ ^ 2 + (k : ℝ) * k + k := by
    have hh := Complex.normSq_add ρ (k : ℂ)
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_natCast] at hh
    have hre : (ρ * (starRingEnd ℂ) (k : ℂ)).re = (k : ℝ) * ρ.re := by
      rw [Complex.mul_re, Complex.conj_natCast]; simp; ring
    rw [hh, hre, hρ]; ring
  have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hle : ‖ρ‖ ^ 2 ≤ ‖ρ + (k : ℂ)‖ ^ 2 := by rw [hsq]; nlinarith
  simpa [abs_of_nonneg (norm_nonneg _)] using sq_le_sq.mp hle

lemma pow_norm_le_prod_range_half {ρ : ℂ} (hρ : ρ.re = 1 / 2) (m : ℕ) :
    ‖ρ‖ ^ (m + 1) ≤ (Finset.range (m + 1)).prod (fun k => ‖ρ + (k : ℂ)‖) := by
  calc ‖ρ‖ ^ (m + 1) = ∏ _k ∈ Finset.range (m + 1), ‖ρ‖ := by
        rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ k ∈ Finset.range (m + 1), ‖ρ + (k : ℂ)‖ :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun k _ => norm_le_norm_add_natCast_half hρ k)

lemma two_pow_pred_le_factorial_of_one_le {m : ℕ} (hm : 1 ≤ m) : 2 ^ (m - 1) ≤ Nat.factorial m := by
  rcases lt_or_eq_of_le hm with h | h
  · have h2 : 2 ≤ m := h
    have hh := Nat.factorial_mul_pow_sub_le_factorial (n := 2) h2
    have hpow : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
      have : m - 1 = m - 2 + 1 := by omega
      rw [this, pow_succ]; ring
    rw [hpow]; simpa using hh
  · subst h; norm_num

lemma norm_mfold_term_le {ρ : ℂ} {x : ℝ} (hxpos : 0 < x) (m : ℕ) (hm : 1 ≤ m)
    (hhalf : ρ.re = 1 / 2) :
    ‖(zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ((Finset.range (m + 1)).prod (fun k => ρ + k))‖
      ≤ (Nat.factorial m : ℝ) * ((zeta1Order ρ : ℝ) * Real.sqrt x / ‖ρ‖ ^ 2) := by
  have hnorm_ge : (1 / 2 : ℝ) ≤ ‖ρ‖ := by
    have h := Complex.abs_re_le_norm ρ
    rw [hhalf] at h; simpa using h
  have hρpos : 0 < ‖ρ‖ := by linarith
  have hprod : ‖ρ‖ ^ (m + 1) ≤ ‖(Finset.range (m + 1)).prod (fun k => ρ + (k : ℂ))‖ := by
    rw [norm_prod]
    exact pow_norm_le_prod_range_half hhalf m
  have hfac : ‖ρ‖ ^ 2 ≤ (Nat.factorial m : ℝ) * ‖ρ‖ ^ (m + 1) := by
    have h1 : (1 : ℝ) ≤ (Nat.factorial m : ℝ) * ‖ρ‖ ^ (m - 1) := by
      have hA : (2 : ℝ) ^ (m - 1) ≤ (Nat.factorial m : ℝ) := by
        exact_mod_cast two_pow_pred_le_factorial_of_one_le hm
      have hB : ((1 : ℝ) / 2) ^ (m - 1) ≤ ‖ρ‖ ^ (m - 1) :=
        pow_le_pow_left₀ (by norm_num) hnorm_ge (m - 1)
      have hC : (2 : ℝ) ^ (m - 1) * ((1 : ℝ) / 2) ^ (m - 1)
          ≤ (Nat.factorial m : ℝ) * ‖ρ‖ ^ (m - 1) :=
        mul_le_mul hA hB (by positivity) (by positivity)
      have hD : (2 : ℝ) ^ (m - 1) * ((1 : ℝ) / 2) ^ (m - 1) = 1 := by
        rw [← mul_pow]; norm_num
      rw [hD] at hC; linarith
    have hpow : ‖ρ‖ ^ 2 * ‖ρ‖ ^ (m - 1) = ‖ρ‖ ^ (m + 1) := by
      rw [← pow_add, show 2 + (m - 1) = m + 1 from by omega]
    calc ‖ρ‖ ^ 2 = ‖ρ‖ ^ 2 * 1 := by ring
      _ ≤ ‖ρ‖ ^ 2 * ((Nat.factorial m : ℝ) * ‖ρ‖ ^ (m - 1)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (Nat.factorial m : ℝ) * (‖ρ‖ ^ 2 * ‖ρ‖ ^ (m - 1)) := by ring
      _ = (Nat.factorial m : ℝ) * ‖ρ‖ ^ (m + 1) := by rw [hpow]
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos ρ, hhalf,
      ← Real.sqrt_eq_rpow, Complex.norm_natCast]
  have hA : (0 : ℝ) ≤ (zeta1Order ρ : ℝ) * Real.sqrt x := by positivity
  calc (zeta1Order ρ : ℝ) * Real.sqrt x /
        ‖(Finset.range (m + 1)).prod (fun k => ρ + (k : ℂ))‖
      ≤ (zeta1Order ρ : ℝ) * Real.sqrt x / ‖ρ‖ ^ (m + 1) :=
        div_le_div_of_nonneg_left hA (pow_pos hρpos (m + 1)) hprod
    _ ≤ (Nat.factorial m : ℝ) * ((zeta1Order ρ : ℝ) * Real.sqrt x / ‖ρ‖ ^ 2) := by
        conv_rhs => rw [← mul_div_assoc]
        refine (div_le_div_iff₀ (pow_pos hρpos (m + 1)) (pow_pos hρpos 2)).mpr ?_
        calc (zeta1Order ρ : ℝ) * Real.sqrt x * ‖ρ‖ ^ 2
            ≤ (zeta1Order ρ : ℝ) * Real.sqrt x * ((Nat.factorial m : ℝ) * ‖ρ‖ ^ (m + 1)) :=
              mul_le_mul_of_nonneg_left hfac hA
          _ = (Nat.factorial m : ℝ) * ((zeta1Order ρ : ℝ) * Real.sqrt x) * ‖ρ‖ ^ (m + 1) := by ring

/-- `m`-fold tilted zero-sum bound. -/
lemma psi_mfold_tiltedZeroSum_bound (h : RiemannHypothesis) (m : ℕ) (hm : 1 ≤ m) (S : Finset ℂ)
    (x : ℝ) (hS : ∀ ρ ∈ S, riemannZeta₁ ρ = 0 ∧ (1 / 4 : ℝ) < ρ.re ∧ ρ.re < 2) (hx : 1 ≤ x) :
    ‖S.sum (fun ρ => (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ /
        ((Finset.range (m + 1)).prod (fun k => ρ + k)))‖
      ≤ (Nat.factorial m : ℝ) * (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) *
          Real.sqrt x := by
  classical
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hterm : ∀ ρ ∈ S,
      ‖(zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ /
        ((Finset.range (m + 1)).prod (fun k => ρ + k))‖
      ≤ (Nat.factorial m : ℝ) * ((zeta1Order ρ : ℝ) * Real.sqrt x / ‖ρ‖ ^ 2) := by
    intro ρ hρ
    obtain ⟨hz1, hre1, hre2⟩ := hS ρ hρ
    exact norm_mfold_term_le hxpos m hm (re_half_of_zeta1_zero h hz1 hre1 hre2)
  have hsum : ‖S.sum (fun ρ => (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ /
        ((Finset.range (m + 1)).prod (fun k => ρ + k)))‖
      ≤ S.sum (fun ρ => (Nat.factorial m : ℝ) *
          ((zeta1Order ρ : ℝ) * Real.sqrt x / ‖ρ‖ ^ 2)) :=
    le_trans (norm_sum_le S _) (Finset.sum_le_sum hterm)
  let R : ℝ := S.sum (fun ρ => ‖ρ‖) + 1
  have hR : 0 ≤ R := by
    have : 0 ≤ S.sum (fun ρ => ‖ρ‖) := Finset.sum_nonneg (fun ρ _ => norm_nonneg ρ)
    simp only [R]; linarith
  have hSR : ∀ ρ ∈ S, riemannZeta₁ ρ = 0 ∧ ‖ρ‖ ≤ R ∧ (1 / 4 : ℝ) < ρ.re ∧ ρ.re < 2 := by
    intro ρ hρ
    obtain ⟨hz1, hre1, hre2⟩ := hS ρ hρ
    refine ⟨hz1, ?_, hre1, hre2⟩
    have hsingle : ‖ρ‖ ≤ S.sum (fun σ => ‖σ‖) :=
      Finset.single_le_sum (fun σ _ => norm_nonneg σ) hρ
    simp only [R]; linarith
  have hbound := zeta1Order_sum_le_beta h hR S hSR
  have hfactor : S.sum (fun ρ => (Nat.factorial m : ℝ) *
        ((zeta1Order ρ : ℝ) * Real.sqrt x / ‖ρ‖ ^ 2))
      = (Nat.factorial m : ℝ) * Real.sqrt x *
        S.sum (fun ρ => (zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ _; ring
  calc ‖S.sum (fun ρ => (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ /
          ((Finset.range (m + 1)).prod (fun k => ρ + k)))‖
      ≤ S.sum (fun ρ => (Nat.factorial m : ℝ) *
          ((zeta1Order ρ : ℝ) * Real.sqrt x / ‖ρ‖ ^ 2)) := hsum
    _ = (Nat.factorial m : ℝ) * Real.sqrt x *
          S.sum (fun ρ => (zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2) := hfactor
    _ ≤ (Nat.factorial m : ℝ) * Real.sqrt x *
          (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (Nat.factorial m : ℝ) * (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) *
          Real.sqrt x := by ring

/-- Gamma ratio: `Γ(ρ + m + 1) = (ρ+1)···(ρ+m) · Γ(ρ+1)` for `0 < Re ρ`. -/
lemma Gamma_add_nat_mul_eq (ρ : ℂ) (hρ : 0 < ρ.re) (m : ℕ) :
    Complex.Gamma (ρ + (m:ℂ) + 1) =
      ((Finset.range m).prod (fun k => ρ + (k+1))) * Complex.Gamma (ρ + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hne : ρ + (m:ℂ) + 1 ≠ 0 := by
        intro h
        have hre : (ρ + (m:ℂ) + 1).re = ρ.re + m + 1 := by simp
        have h0 : (ρ + (m:ℂ) + 1).re = 0 := by rw [h]; simp
        rw [hre] at h0
        have : (0:ℝ) ≤ m := Nat.cast_nonneg m
        nlinarith [hρ]
      rw [show ρ + ((m+1:ℕ):ℂ) + 1 = (ρ + (m:ℂ) + 1) + 1 by push_cast; ring,
        Complex.Gamma_add_one _ hne, ih]
      rw [Finset.prod_range_succ]
      ring

/-- Beta integral evaluation: `Β(ρ+1, m) = (m-1)! / ((ρ+1)···(ρ+m))`. -/
lemma betaIntegral_eq (ρ : ℂ) (hρ : 0 < ρ.re) (m : ℕ) (hm : 1 ≤ m) :
    Complex.betaIntegral (ρ + 1) (m:ℂ) =
      (Nat.factorial (m-1) : ℂ) / ((Finset.range m).prod (fun k => ρ + (k+1))) := by
  have hmre : 0 < ((m:ℂ)).re := by simpa using (show (0:ℝ) < m from by exact_mod_cast hm)
  have hρ1 : 0 < (ρ+1).re := by
    simp only [Complex.add_re, Complex.one_re]; linarith
  have hkey := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := ρ+1) (t := (m:ℂ)) hρ1 hmre
  have hGm : Complex.Gamma (m:ℂ) = ((Nat.factorial (m-1)) : ℂ) := by
    have hmeq : (m:ℂ) = ((m-1:ℕ):ℂ) + 1 := by rw [Nat.cast_pred hm]; ring
    rw [hmeq, Complex.Gamma_nat_eq_factorial]
  have hP := Gamma_add_nat_mul_eq ρ hρ m
  have hsum : (ρ+1) + (m:ℂ) = ρ + (m:ℂ) + 1 := by ring
  rw [hGm, hsum, hP] at hkey
  have hP0 : ((Finset.range m).prod (fun k => ρ + ((k:ℂ)+1))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k hk h0
    have hre : (ρ + ((k:ℂ)+1)).re = ρ.re + (k:ℝ) + 1 := by
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]; ring
    have : (ρ + ((k:ℂ)+1)).re = 0 := by rw [h0]; simp
    rw [hre] at this
    have : (0:ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [hρ]
  have hG1 : Complex.Gamma (ρ+1) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro k hk
    have hre : (ρ+1).re = ρ.re + 1 := by simp
    have : (ρ+1).re = -(k:ℝ) := by rw [hk]; simp
    rw [hre] at this
    nlinarith [hρ]
  have hkey2 : Complex.Gamma (ρ+1) * (Nat.factorial (m-1) : ℂ) =
      Complex.Gamma (ρ+1) *
        (((Finset.range m).prod (fun k => ρ + (k+1))) * Complex.betaIntegral (ρ+1) (m:ℂ)) := by
    rw [hkey]; ring
  have hfinal : (Nat.factorial (m-1) : ℂ) =
      ((Finset.range m).prod (fun k => ρ + (k+1))) * Complex.betaIntegral (ρ+1) (m:ℂ) :=
    mul_left_cancel₀ hG1 hkey2
  rw [hfinal]
  field_simp

/-- `∫_0^x t^ρ (x-t)^{m-1} dt = x^{ρ+m} Β(ρ+1, m)`. -/
lemma integral_cpow_mul_sub_pow (ρ : ℂ) (hρ : 0 < ρ.re) (m : ℕ) (hm : 1 ≤ m) {x : ℝ}
    (hx : 0 < x) :
    ∫ t in (0:ℝ)..x, (t:ℂ)^ρ * ((x:ℂ) - (t:ℂ))^(m-1)
      = (x:ℂ)^(ρ + (m:ℂ)) * Complex.betaIntegral (ρ+1) (m:ℂ) := by
  have hcast : ((m:ℂ) - 1) = ((m-1:ℕ):ℂ) := by
    simpa using (Nat.cast_sub hm).symm
  have hcast2 : ((ρ+1:ℂ) - 1) = ρ := by ring
  have hscaled := Complex.betaIntegral_scaled (ρ+1) (m:ℂ) hx
  rw [hcast2, hcast] at hscaled
  have hgoal : ∫ t in (0:ℝ)..x, (t:ℂ)^ρ * ((x:ℂ) - (t:ℂ))^(m-1)
      = ∫ t in (0:ℝ)..x, (t:ℂ)^ρ * ((x:ℂ) - (t:ℂ))^(((m-1:ℕ):ℂ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [cpow_natCast]
  rw [hgoal, hscaled, show ρ + 1 + (m:ℂ) - 1 = ρ + (m:ℂ) by ring]

/-- `∫_0^x (1-t/x)^{m-1} t^ρ dt = x^{ρ+1} Β(ρ+1, m)`. -/
lemma integral_one_sub_div_pow (ρ : ℂ) (hρ : 0 < ρ.re) (m : ℕ) (hm : 1 ≤ m) {x : ℝ}
    (hx : 0 < x) :
    ∫ t in (0:ℝ)..x, ((1 - (t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ
      = (x:ℂ)^(ρ+1) * Complex.betaIntegral (ρ+1) (m:ℂ) := by
  have hxne : (x:ℂ) ≠ 0 := by
    simpa using (ofReal_ne_zero.mpr hx.ne')
  have hpoint : ∀ t : ℝ, ((1 - (t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ
      = ((x:ℂ)^(m-1))⁻¹ * ((t:ℂ)^ρ * ((x:ℂ)-(t:ℂ))^(m-1)) := by
    intro t
    have h1 : (1 - (t:ℂ)/(x:ℂ)) = ((x:ℂ) - (t:ℂ)) * (x:ℂ)⁻¹ := by field_simp
    rw [h1, mul_pow, inv_pow]
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hpoint t)]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_cpow_mul_sub_pow ρ hρ m hm hx]
  have hsplit : (x:ℂ)^(ρ + (m:ℂ)) = (x:ℂ)^(m-1) * (x:ℂ)^(ρ+1) := by
    rw [show ρ + (m:ℂ) = ((m-1:ℕ):ℂ) + (ρ+1) by push_cast [Nat.cast_sub hm]; ring,
      Complex.cpow_add _ _ hxne, cpow_natCast]
  rw [hsplit]
  rw [← mul_assoc (((x:ℂ)^(m-1))⁻¹) ((x:ℂ)^(m-1) * (x:ℂ)^(ρ+1))
        (Complex.betaIntegral (ρ+1) (m:ℂ))]
  have hred : ((x:ℂ)^(m-1))⁻¹ * ((x:ℂ)^(m-1) * (x:ℂ)^(ρ+1)) = (x:ℂ)^(ρ+1) := by
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hxne), one_mul]
  rw [hred]

/-- `∫_n^x (1 - t/x)^{m-1} dt = (x/m) (1 - n/x)^m`. -/
lemma integral_one_sub_div_pow_Icc (m : ℕ) (hm : 1 ≤ m) {n x : ℝ} (hn : 0 ≤ n) (hnx : n ≤ x)
    (hx : 0 < x) :
    ∫ t in n..x, ((1 - (t:ℂ)/(x:ℂ))^(m-1))
      = ((x:ℂ)/(m:ℂ)) * (1 - (n:ℂ)/(x:ℂ))^m := by
  have hxne : (x:ℂ) ≠ 0 := by simpa using (ofReal_ne_zero.mpr hx.ne')
  have hmne : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : m ≠ 0)
  have hderiv : ∀ t ∈ Set.uIcc n x,
      HasDerivAt (fun t : ℝ => -((x:ℂ)/(m:ℂ)) * (1 - (t:ℂ)/(x:ℂ))^m)
        ((1 - (t:ℂ)/(x:ℂ))^(m-1)) t := by
    intro t ht
    have hbase : HasDerivAt (fun t : ℝ => (1:ℂ) - (t:ℂ) * (x:ℂ)⁻¹) (-(x:ℂ)⁻¹) t := by
      have h1 : HasDerivAt (fun t : ℝ => (t:ℂ) * (x:ℂ)⁻¹) ((x:ℂ)⁻¹) t := by
        simpa using ((hasDerivAt_id t).ofReal_comp).mul_const ((x:ℂ)⁻¹)
      have h2 : HasDerivAt (fun t : ℝ => (1:ℂ) - (t:ℂ) * (x:ℂ)⁻¹) (0 - (x:ℂ)⁻¹) t :=
        (hasDerivAt_const (x := t) (c := (1:ℂ))).sub h1
      simpa using h2
    have hcm := (hbase.pow m).const_mul (-((x:ℂ)/(m:ℂ)))
    have hfun : (fun y : ℝ => -((x:ℂ)/(m:ℂ)) * (1 - (y:ℂ)/(x:ℂ))^m)
        = fun y : ℝ => -((x:ℂ)/(m:ℂ)) * ((fun t : ℝ => (1:ℂ) - (t:ℂ) * (x:ℂ)⁻¹)^m) y := by
      funext y; simp only [Pi.pow_apply, div_eq_mul_inv]
    have hder : (-((x:ℂ)/(m:ℂ)) * ((m:ℂ) * (1 - (t:ℂ) * (x:ℂ)⁻¹)^(m-1) * (-(x:ℂ)⁻¹)))
        = (1 - (t:ℂ)/(x:ℂ))^(m-1) := by
      rw [div_eq_mul_inv]
      field_simp
    rw [← hfun, hder] at hcm
    exact hcm
  have hcont : ContinuousOn (fun t : ℝ => (1 - (t:ℂ)/(x:ℂ))^(m-1)) (Set.uIcc n x) := by
    apply ContinuousOn.pow
    apply ContinuousOn.sub continuousOn_const
    exact (continuous_ofReal.div_const (x:ℂ)).continuousOn
  have hint : IntervalIntegrable (fun t : ℝ => (1 - (t:ℂ)/(x:ℂ))^(m-1)) volume n x :=
    hcont.intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hx1 : (1 - (x:ℂ)/(x:ℂ)) = 0 := by rw [div_self hxne]; ring
  rw [hx1, zero_pow (by omega : m ≠ 0)]
  ring

lemma integral_indicator_Ici_kernel (m : ℕ) {n x : ℝ} (hn : 0 ≤ n) (hnx : n ≤ x) (hx : 0 < x)
    (c : ℂ) :
    ∫ t in (0:ℝ)..x, (Set.Ici (n:ℝ)).indicator
        (fun t => ((1 - (t:ℂ)/(x:ℂ))^(m-1)) * c) t
      = c * ∫ t in n..x, ((1 - (t:ℂ)/(x:ℂ))^(m-1)) := by
  rw [intervalIntegral.integral_of_le (le_of_lt hx),
      MeasureTheory.setIntegral_indicator measurableSet_Ici]
  have hset : ((Set.Ioc (0:ℝ) x ∩ Set.Ici (n:ℝ) : Set ℝ)) =ᵐ[volume] (Set.Ioc n x : Set ℝ) := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · refine Set.Finite.measure_zero ?_ volume
      refine (Set.finite_singleton n).subset ?_
      intro t ht
      rw [Set.mem_diff, Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Ioc] at ht
      obtain ⟨⟨⟨h0t, htx⟩, hnt⟩, hnot⟩ := ht
      rw [Set.mem_singleton_iff]
      have hle : t ≤ n := by
        by_contra hc
        rw [not_le] at hc
        exact hnot ⟨hc, htx⟩
      exact le_antisymm hle hnt
    · refine Set.Finite.measure_zero ?_ volume
      refine (Set.finite_singleton n).subset ?_
      intro t ht
      rw [Set.mem_diff, Set.mem_Ioc] at ht
      obtain ⟨⟨hnt, htx⟩, hnot⟩ := ht
      have hmem : t ∈ Set.Ioc (0:ℝ) x ∩ Set.Ici (n:ℝ) := by
        rw [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici]
        exact ⟨⟨by linarith, htx⟩, le_of_lt hnt⟩
      exact absurd hmem hnot
  rw [MeasureTheory.setIntegral_congr_set hset]
  rw [show (fun t : ℝ => ((1 - (t:ℂ)/(x:ℂ))^(m-1)) * c)
      = fun t : ℝ => c * ((1 - (t:ℂ)/(x:ℂ))^(m-1)) by funext t; ring]
  rw [MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le hnx]

/-- `ψ(t)` is the sum of `Λ(n)` over `n ≤ t`, written with `Ioc 0 ⌊x⌋₊`. -/
lemma psi_eq_sum_ite {x t : ℝ} (ht : t ∈ Set.Icc 0 x) :
    Chebyshev.psi t = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        (if (n:ℝ) ≤ t then ArithmeticFunction.vonMangoldt n else 0) := by
  have htt0 : (0:ℝ) ≤ t := ht.1
  have hle : ⌊t⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono ht.2
  have h1 : Chebyshev.psi t = ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n := by
    rw [Chebyshev.psi_eq_psi_coe_floor, Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    rw [show Finset.Icc 0 ⌊t⌋₊ = insert 0 (Finset.Ioc 0 ⌊t⌋₊) by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega]
    rw [Finset.sum_insert (by simp [Finset.mem_Ioc]),
      show (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 from ArithmeticFunction.map_zero]
    simp
  rw [h1, ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hn0, hnt⟩
      exact ⟨⟨hn0, le_trans hnt hle⟩, le_trans (by exact_mod_cast hnt) (Nat.floor_le htt0)⟩
    · rintro ⟨⟨hn0, hnN⟩, hnt⟩
      exact ⟨hn0, Nat.le_floor hnt⟩
  · intro n hn; rfl

/-- `∑_{n ≤ x} Λ(n) (1-n/x)^m = (m/x) ∫_0^x (1-t/x)^{m-1} ψ(t) dt`. -/
lemma psi_mfold_sum_eq_integral (m : ℕ) (hm : 1 ≤ m) {x : ℝ} (hx : 0 < x) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℂ) / (x : ℂ)) ^ m)
      = ((m : ℂ) / (x : ℂ)) *
          ∫ t in (0 : ℝ)..x, ((1 - (t : ℂ) / (x : ℂ)) ^ (m - 1)) *
            ((Chebyshev.psi t : ℝ) : ℂ) := by
  have hx0 : (0:ℝ) ≤ x := le_of_lt hx
  have hxne : (x:ℂ) ≠ 0 := by simpa using (ofReal_ne_zero.mpr hx.ne')
  have hmne : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : m ≠ 0)
  set N : ℕ := ⌊x⌋₊ with hNdef
  have hNx : ((N:ℕ):ℝ) ≤ x := by rw [hNdef]; exact Nat.floor_le hx0
  have hcont : Continuous (fun t : ℝ => (1 - (t:ℂ)/(x:ℂ))^(m-1)) := by fun_prop
  suffices hI : ∫ t in (0:ℝ)..x, ((1 - (t:ℂ)/(x:ℂ))^(m-1)) * ((Chebyshev.psi t : ℝ):ℂ)
      = ((x:ℂ)/(m:ℂ)) * (∑ n ∈ Finset.Ioc 0 N,
          ((ArithmeticFunction.vonMangoldt n : ℝ):ℂ) * (1 - (n:ℂ)/(x:ℂ))^m) by
    rw [hI, hNdef]
    field_simp
  have e1 : ∫ t in (0:ℝ)..x, ((1 - (t:ℂ)/(x:ℂ))^(m-1)) * ((Chebyshev.psi t : ℝ):ℂ)
      = ∫ t in (0:ℝ)..x, ∑ n ∈ Finset.Ioc 0 N,
          (((1 - (t:ℂ)/(x:ℂ))^(m-1)) *
            (if (n:ℝ) ≤ t then ((ArithmeticFunction.vonMangoldt n : ℝ):ℂ) else 0)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx0] at ht
    show ((1 - (t:ℂ)/(x:ℂ))^(m-1)) * ((Chebyshev.psi t : ℝ):ℂ) = _
    rw [psi_eq_sum_ite ht, Complex.ofReal_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : (n:ℝ) ≤ t <;> simp [h]
  have e2 : ∫ t in (0:ℝ)..x, ∑ n ∈ Finset.Ioc 0 N,
          (((1 - (t:ℂ)/(x:ℂ))^(m-1)) *
            (if (n:ℝ) ≤ t then ((ArithmeticFunction.vonMangoldt n : ℝ):ℂ) else 0))
      = ∑ n ∈ Finset.Ioc 0 N, ((ArithmeticFunction.vonMangoldt n : ℝ):ℂ) *
          ∫ t in (n:ℝ)..x, ((1 - (t:ℂ)/(x:ℂ))^(m-1)) := by
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n hn
      obtain ⟨hn0', hnN⟩ := Finset.mem_Ioc.mp hn
      have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
      have hnx : (n:ℝ) ≤ x := le_trans (by exact_mod_cast hnN) hNx
      have hfuneq : (fun t : ℝ => ((1 - (t:ℂ)/(x:ℂ))^(m-1)) *
            (if (n:ℝ) ≤ t then ((ArithmeticFunction.vonMangoldt n : ℝ):ℂ) else 0))
          = fun t : ℝ => (Set.Ici (n:ℝ)).indicator
              (fun t => ((1 - (t:ℂ)/(x:ℂ))^(m-1)) * ((ArithmeticFunction.vonMangoldt n : ℝ):ℂ)) t := by
        funext t; rw [Set.indicator_apply]; by_cases h : (n:ℝ) ≤ t <;> simp [h]
      rw [hfuneq, integral_indicator_Ici_kernel m hn0 hnx hx]
    · intro n hn
      obtain ⟨hn0', hnN⟩ := Finset.mem_Ioc.mp hn
      have hfuneq : (fun t : ℝ => ((1 - (t:ℂ)/(x:ℂ))^(m-1)) *
            (if (n:ℝ) ≤ t then ((ArithmeticFunction.vonMangoldt n : ℝ):ℂ) else 0))
          = fun t : ℝ => (Set.Ici (n:ℝ)).indicator
              (fun t => ((1 - (t:ℂ)/(x:ℂ))^(m-1)) * ((ArithmeticFunction.vonMangoldt n : ℝ):ℂ)) t := by
        funext t; rw [Set.indicator_apply]; by_cases h : (n:ℝ) ≤ t <;> simp [h]
      rw [hfuneq]
      have hc : Continuous (fun _ : ℝ => ((ArithmeticFunction.vonMangoldt n : ℝ):ℂ)) :=
        continuous_const
      have h := (hcont.mul hc).intervalIntegrable (μ := volume) 0 x
      exact ⟨h.1.indicator measurableSet_Ici, h.2.indicator measurableSet_Ici⟩
  rw [e1, e2]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn0', hnN⟩ := Finset.mem_Ioc.mp hn
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hnx : (n:ℝ) ≤ x := le_trans (by exact_mod_cast hnN) hNx
  rw [integral_one_sub_div_pow_Icc m hm hn0 hnx hx]
  push_cast
  ring

lemma prod_range_add_two_cast (m : ℕ) :
    (∏ k ∈ Finset.range m, ((1:ℂ) + ((k:ℂ) + 1))) = (Nat.factorial (m+1) : ℂ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.prod_range_succ, ih]
      have hterm : (1:ℂ) + ((m:ℂ) + 1) = ((m+2:ℕ):ℂ) := by push_cast; ring
      rw [hterm]
      have hfac : (Nat.factorial (m+2) : ℂ) = ((m+2:ℕ):ℂ) * (Nat.factorial (m+1) : ℂ) := by
        have hs : Nat.factorial (m+2) = (m+2) * Nat.factorial (m+1) := by
          have := Nat.factorial_succ (m+1)
          simpa [Nat.add_assoc] using this
        rw [hs]; push_cast; ring
      rw [hfac]; ring

lemma factorial_ratio (m : ℕ) (hm : 1 ≤ m) :
    (Nat.factorial (m-1) : ℂ) / (Nat.factorial (m+1) : ℂ)
      = 1/((m:ℂ) * ((m+1:ℕ):ℂ)) := by
  have hfac : (Nat.factorial (m+1) : ℂ)
      = ((m:ℂ) * ((m+1:ℕ):ℂ)) * (Nat.factorial (m-1) : ℂ) := by
    have h1 : Nat.factorial (m+1) = (m+1) * Nat.factorial m := Nat.factorial_succ m
    have h2 : Nat.factorial m = m * Nat.factorial (m-1) := by
      conv_lhs => rw [show m = (m-1)+1 by omega]
      rw [Nat.factorial_succ]
      congr 1
      omega
    rw [h1, h2]; push_cast; ring
  rw [hfac]
  have hfne : (Nat.factorial (m-1) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (m-1)
  field_simp

lemma betaIntegral_two (m : ℕ) (hm : 1 ≤ m) :
    Complex.betaIntegral 2 (m:ℂ) = 1/((m:ℂ)*((m+1:ℕ):ℂ)) := by
  have h := betaIntegral_eq (1:ℂ) (by norm_num) m hm
  rw [show (1:ℂ)+1 = 2 by norm_num] at h
  rw [h, prod_range_add_two_cast m]
  exact factorial_ratio m hm

lemma integral_one_sub_div_pow_zero (m : ℕ) (hm : 1 ≤ m) {x : ℝ} (hx : 0 < x) :
    ∫ t in (0:ℝ)..x, ((1 - (t:ℂ)/(x:ℂ))^(m-1)) = (x:ℂ)/(m:ℂ) := by
  rw [integral_one_sub_div_pow_Icc m hm (le_refl 0) (le_of_lt hx) hx]
  simp

lemma integral_one_sub_div_pow_succ (m : ℕ) {x : ℝ} (hx : 0 < x) :
    ∫ t in (0:ℝ)..x, ((1 - (t:ℂ)/(x:ℂ))^m) = (x:ℂ)/(((m+1:ℕ)):ℂ) := by
  have h := integral_one_sub_div_pow_Icc (m+1) (by omega) (le_refl 0) (le_of_lt hx) hx
  rw [show ((m+1:ℕ) - 1) = m by omega] at h
  rw [h]
  simp

lemma integral_one_sub_div_pow_one (m : ℕ) (hm : 1 ≤ m) {x : ℝ} (hx : 0 < x) :
    ∫ t in (0:ℝ)..x, ((1 - (t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)
      = (x:ℂ)^2/((m:ℂ)*((m+1:ℕ):ℂ)) := by
  have h := integral_one_sub_div_pow (1:ℂ) (by norm_num) m hm hx
  simp only [Complex.cpow_one] at h
  have hc : ((1:ℂ) + 1) = 2 := by norm_num
  rw [h, hc, betaIntegral_two m hm]
  have hx2 : (x:ℂ) ^ (2:ℂ) = (x:ℂ)^2 := by
    rw [show (2:ℂ) = ((2:ℕ):ℂ) by norm_num, Complex.cpow_natCast]
  rw [hx2, div_eq_mul_inv]
  ring_nf

lemma exists_good_height_mfold (h : RiemannHypothesis) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∃ Tp δ : ℝ,
      5 ≤ Tp ∧ x ≤ Tp ^ 2 ∧ 0 < δ ∧
      1 ≤ (2 * c + 2) * (Real.log (Tp + 3) + 1) * δ ∧
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - Tp|) ∧
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ Tp ∧ ρ.im ≠ -Tp) ∧
      x ^ (1/2:ℝ) * (Real.log x) ^ 3 ≤ Tp ∧
      Tp ≤ x ^ (1/2:ℝ) * (Real.log x) ^ 3 + 1 := by
  obtain ⟨c, hcp, hcw⟩ := riemannZeta_ordinate_window h
  refine ⟨c, hcp, ?_⟩
  have hev : ∀ᶠ x : ℝ in atTop, (3:ℝ) ≤ x ∧ (1000:ℝ) ≤ Real.log x := by
    filter_upwards [eventually_ge_atTop (3:ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000:ℝ))] with x hx hlog
    exact ⟨hx, hlog⟩
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨x₀, ?_⟩
  intro x hx
  obtain ⟨hx3, hlog1000⟩ := hx₀ x hx
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := by linarith
  set T : ℝ := x ^ (1/2:ℝ) * (Real.log x) ^ 3 with hT
  have hT5 : 5 ≤ T := by
    rw [hT]
    have hlog3 : (1000:ℝ)^3 ≤ (Real.log x)^3 := pow_le_pow_left₀ (by norm_num) hlog1000 3
    have hx12 : (1:ℝ) ≤ x^(1/2:ℝ) := by
      calc (1:ℝ) = 1^(1/2:ℝ) := by simp
        _ ≤ x^(1/2:ℝ) := Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
    have hx12pos : 0 ≤ x^(1/2:ℝ) := Real.rpow_nonneg (by linarith) _
    nlinarith [hlog3, hx12, hx12pos]
  have hTpos : 0 < T := by linarith
  obtain ⟨S, hSsub, hScard, hSmem⟩ := hcw T hT5
  set n : ℕ := ⌊c * (Real.log T + 1)⌋₊ + 1 with hn
  have hn1 : 1 ≤ n := by rw [hn]; omega
  have hcard : S.card ≤ n := by
    rw [hn]
    have := Nat.le_floor hScard
    omega
  obtain ⟨Tp, hTTp, hTp_le, hgap⟩ := Commons.Analysis.Real.exists_gap_height T hn1 S hcard hSsub
  have hTp5 : 5 ≤ Tp := le_trans hT5 hTTp
  have hTp0 : 0 < Tp := by linarith
  have hlogT1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hTpos]
    exact le_trans Real.exp_one_lt_three.le (by linarith)
  have hnle : (n:ℝ) ≤ c*(Real.log T+1) + 1 := by
    rw [hn]
    have h0 : (0:ℝ) ≤ c*(Real.log T+1) := by
      have : 0 ≤ Real.log T := le_trans zero_le_one hlogT1
      positivity
    have h1 := Nat.floor_le h0
    push_cast
    linarith
  have hlogTp : Real.log T ≤ Real.log (Tp + 3) := Real.log_le_log hTpos (by linarith)
  have hlogTp1 : 1 ≤ Real.log (Tp + 3) := le_trans hlogT1 hlogTp
  have hδpos : (0:ℝ) < 1/(2*(n:ℝ)+2) := by positivity
  refine ⟨Tp, 1/(2*(n:ℝ)+2), hTp5, ?_, hδpos, ?_, ?_, ?_, ?_, ?_⟩
  · -- x ≤ Tp^2
    have hsq : T^2 = x * (Real.log x)^6 := by
      rw [hT, mul_pow]
      rw [show (x^(1/2:ℝ))^2 = x by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hxpos)]
        norm_num,
        show ((Real.log x)^3)^2 = (Real.log x)^6 by ring]
    have hxlog6 : x * 1 ≤ x * (Real.log x)^6 := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hxpos)
      calc (1:ℝ) = 1^6 := by ring
        _ ≤ (Real.log x)^6 := pow_le_pow_left₀ (by norm_num) (by linarith) 6
    have : T^2 ≤ Tp^2 := by
      apply pow_le_pow_left₀ (by linarith) hTTp 2
    rw [hsq] at this
    linarith
  · -- 1 ≤ (2c+2)(log(Tp+3)+1) δ
    have hCpos : (0:ℝ) < 2*(n:ℝ)+2 := by positivity
    rw [one_div]
    have key : (2*(n:ℝ)+2) ≤ (2*c+2)*(Real.log (Tp+3)+1) := by
      nlinarith [hnle, hlogTp, hlogTp1, hcp]
    calc (1:ℝ) = (2*(n:ℝ)+2) * (2*(n:ℝ)+2)⁻¹ := by
          rw [mul_inv_cancel₀ (ne_of_gt hCpos)]
      _ ≤ ((2*c+2)*(Real.log (Tp+3)+1)) * (2*(n:ℝ)+2)⁻¹ :=
            mul_le_mul_of_nonneg_right key (by positivity)
      _ = (2*c+2)*(Real.log (Tp+3)+1) * (2*(n:ℝ)+2)⁻¹ := by ring
  · -- gap
    intro ρ hρ
    by_cases him : ρ.im = 0
    · rw [him, zero_sub, abs_neg, abs_of_pos hTp0]
      have hle1 : (1:ℝ)/(2*(n:ℝ)+2) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
        linarith
      linarith
    · have h1 : ρ ≠ 1 := by
        intro hh; rw [hh, riemannZeta₁_one] at hρ; exact one_ne_zero hρ
      have hz : riemannZeta ρ = 0 := by rw [riemannZeta_eq_inv_sub_mul h1, hρ, mul_zero]
      have hre : ρ.re = 1/2 := by
        refine h ρ hz ?_ h1
        rintro ⟨k, hk⟩
        rw [hk] at him
        simp at him
      by_cases hrange : Tp - 1 ≤ ρ.im ∧ ρ.im ≤ Tp + 1
      · have hmem : ρ.im ∈ S := hSmem ρ hz hre (by linarith [hrange.1, hTTp])
            (by linarith [hrange.2, hTp_le])
        have := hgap ρ.im hmem
        rwa [abs_sub_comm] at this
      · have hlt : ρ.im < Tp - 1 ∨ Tp + 1 < ρ.im := by
          by_contra hc
          push_neg at hc
          exact hrange ⟨hc.1, hc.2⟩
        have habs : (1:ℝ) ≤ |ρ.im - Tp| := by
          rcases hlt with h | h
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        have hle1 : (1:ℝ)/(2*(n:ℝ)+2) ≤ 1 := by
          rw [div_le_one (by positivity)]
          have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
          linarith
        linarith
  · -- no zero at ±Tp
    have hneTp : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1/2 → ρ.im ≠ Tp := by
      intro ρ hz hre him
      have hmem : ρ.im ∈ S := hSmem ρ hz hre (by rw [him]; linarith) (by rw [him]; linarith)
      have h2 := hgap ρ.im hmem
      rw [him, sub_self, abs_zero] at h2
      have : (0:ℝ) < 1/(2*(n:ℝ)+2) := by positivity
      linarith
    intro ρ hz1
    have hρ1 : ρ ≠ 1 := by
      intro h1; rw [h1, riemannZeta₁_one] at hz1; exact one_ne_zero hz1
    have hz : riemannZeta ρ = 0 := by rw [riemannZeta_eq_inv_sub_mul hρ1, hz1, mul_zero]
    constructor
    · intro him
      have hnotT : ¬∃ k : ℕ, ρ = -2 * (k + 1 : ℂ) := by
        rintro ⟨k, hk⟩
        have h0 : ρ.im = 0 := by rw [hk]; simp
        rw [him] at h0
        linarith [hTp5]
      exact hneTp ρ hz (h ρ hz hnotT hρ1) him
    · intro him
      have hz' : riemannZeta (starRingEnd ℂ ρ) = 0 := by
        rw [riemannZeta_conj ρ, hz, map_zero]
      have hre' : (starRingEnd ℂ ρ).re = 1 / 2 := by
        have hnotT : ¬∃ k : ℕ, ρ = -2 * (k + 1 : ℂ) := by
          rintro ⟨k, hk⟩
          have h0 : ρ.im = 0 := by rw [hk]; simp
          rw [him] at h0
          linarith [hTp5]
        rw [Complex.conj_re]
        exact h ρ hz hnotT hρ1
      have him' : (starRingEnd ℂ ρ).im = Tp := by rw [Complex.conj_im, him, neg_neg]
      exact hneTp _ hz' hre' him'
  · exact hTTp
  · exact hTp_le

lemma intervalIntegrable_Kc_psi (m : ℕ) {x : ℝ} (hx : 0 < x) :
    IntervalIntegrable (fun t : ℝ => ((1 - (t:ℂ)/(x:ℂ))^(m-1)) * ((Chebyshev.psi t : ℝ):ℂ))
      volume 0 x := by
  have hcont : Continuous (fun t : ℝ => (1 - (t:ℂ)/(x:ℂ))^(m-1)) := by fun_prop
  have hmeas : Measurable (fun t : ℝ => ((Chebyshev.psi t : ℝ):ℂ)) :=
    Complex.measurable_ofReal.comp Chebyshev.psi_mono.measurable
  constructor
  · refine MeasureTheory.Integrable.of_bound ?_ (Chebyshev.psi x) ?_
    · exact (hcont.measurable.mul hmeas).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : (0:ℝ) < t := ht.1
      have htx : t ≤ x := ht.2
      have hnormK : ‖((1:ℂ) - (t:ℂ)/(x:ℂ))^(m-1)‖ ≤ 1 := by
        rw [norm_pow]
        apply pow_le_one₀ (norm_nonneg _)
        have hcast : ((1:ℂ) - (t:ℂ)/(x:ℂ)) = (((1 - t/x : ℝ)):ℂ) := by push_cast; ring
        have hnormr : ‖(((1 - t/x : ℝ)):ℂ)‖ = |1 - t/x| := by
          rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]
        rw [hcast, hnormr,
          abs_of_nonneg (sub_nonneg.mpr (by rw [div_le_one hx]; exact htx))]
        exact sub_le_self _ (div_nonneg (le_of_lt ht0) (le_of_lt hx))
      have hnormψ : ‖((Chebyshev.psi t : ℝ):ℂ)‖ ≤ Chebyshev.psi x := by
        have hnormψ : ‖((Chebyshev.psi t : ℝ):ℂ)‖ = |Chebyshev.psi t| := by
          rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]
        rw [hnormψ, abs_of_nonneg (Chebyshev.psi_nonneg t)]
        exact Chebyshev.psi_mono htx
      rw [norm_mul]
      calc ‖((1:ℂ) - (t:ℂ)/(x:ℂ))^(m-1)‖ * ‖((Chebyshev.psi t : ℝ):ℂ)‖
          ≤ 1 * Chebyshev.psi x := mul_le_mul hnormK hnormψ (norm_nonneg _) (by norm_num)
        _ = Chebyshev.psi x := one_mul _
  · rw [Set.Ioc_eq_empty_of_le (le_of_lt hx)]
    exact integrableOn_empty

theorem chebyshevPsi_mfold_explicit (h : RiemannHypothesis) (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (1 - (n : ℂ) / (x : ℂ)) ^ m
        - ((x : ℂ) / (m + 1) - (Real.log (2 * Real.pi) : ℂ))‖ ≤ C * Real.sqrt x := by
  classical
  obtain ⟨Cfar, C₂, D, hCfarp, hC₂p, hDp, Xfraw, hXfraw⟩ := chebyshevPsi_at_height_farLeft_neg h
  obtain ⟨c, hcp, Xh, hheight⟩ := exists_good_height_mfold h
  set Xf : ℝ := max Xfraw 1 with hXfdef
  have hXf1 : (1:ℝ) ≤ Xf := le_max_right _ _
  have hXfge : Xfraw ≤ Xf := le_max_left _ _
  have hXfpos : (0:ℝ) < Xf := by linarith
  set β : ℝ := 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) with hβdef
  have hβnn : 0 ≤ β := by
    have h0 := psi_mfold_tiltedZeroSum_bound h 2 (by norm_num) ∅ 1 (by simp) (le_refl 1)
    rw [Finset.sum_empty, norm_zero, Real.sqrt_one, mul_one] at h0
    have hfac : (Nat.factorial 2 : ℝ) = 2 := by norm_num
    rw [hfac] at h0
    show (0:ℝ) ≤ β
    rw [hβdef]; linarith
  set K : ℝ := 2*c+2 with hKdef
  have hK1 : 1 ≤ K := by rw [hKdef]; linarith
  set G₀ : ℝ := Chebyshev.psi Xf + Xf + 2 with hG₀def
  have hG₀nn : 0 ≤ G₀ := by rw [hG₀def]; have := Chebyshev.psi_nonneg Xf; linarith
  set C : ℝ := (Nat.factorial m : ℝ)^2 * β + m * G₀ * Xf + 8 * (m:ℝ) * Xf * Cfar * K
      + (m:ℝ) * Xf * (4 * C₂ + 8) + 16 * (m:ℝ) * D * Xf^(-(1/2:ℝ))
      + 8 * (m:ℝ) * β * Xf^(3/2:ℝ) + 1 with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    have h1 : 0 ≤ (Nat.factorial m : ℝ)^2 * β := by positivity
    have h4 : 0 ≤ 8 * (m:ℝ) * β * Xf^(3/2:ℝ) := by positivity
    have h5 : 0 ≤ m * G₀ * Xf := by positivity
    have h6 : 0 ≤ 8 * (m:ℝ) * Xf * Cfar * K := by positivity
    have h7 : 0 ≤ (m:ℝ) * Xf * (4 * C₂ + 8) := by positivity
    have h8 : 0 ≤ 16 * (m:ℝ) * D * Xf^(-(1/2:ℝ)) := by positivity
    linarith
  refine ⟨C, hCpos, ?_⟩
  have hev : ∀ᶠ x : ℝ in atTop,
      Xf ≤ x ∧ Xh ≤ x ∧ (1:ℝ) ≤ x ∧ (65536:ℝ) ≤ x ∧ Real.log x ≤ x^(1/8:ℝ) ∧ 1 ≤ Real.log x := by
    have hlog8 : ∀ᶠ x : ℝ in atTop, Real.log x ≤ x^(1/8:ℝ) := by
      have h1 : (fun x : ℝ => Real.log x) =o[atTop] (fun x : ℝ => x^(1/8:ℝ)) :=
        isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/8)
      filter_upwards [h1.eventuallyLE, eventually_ge_atTop (1:ℝ)] with x hx hx1
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
        abs_of_nonneg (Real.rpow_nonneg (le_trans zero_le_one hx1) _)] at hx
      exact hx
    filter_upwards [eventually_ge_atTop Xf, eventually_ge_atTop Xh, eventually_ge_atTop (1:ℝ),
      eventually_ge_atTop (65536:ℝ), hlog8,
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨x₀, ?_⟩
  intro x hx
  obtain ⟨hxXf, hxXh, hx1, hxbig, hlog8, hlog1⟩ := hx₀ x hx
  have hxpos : 0 < x := by linarith
  have hx0 : (0:ℝ) ≤ x := le_of_lt hxpos
  -- the height
  obtain ⟨Tp, δ, hTp5, hxTp2, hδpos, hKδ, hgap, hgood, hTpge, hTple⟩ := hheight x hxXh
  have hTppos : 0 < Tp := by linarith
  have hx18 : (4:ℝ) ≤ x^(1/8:ℝ) := by
    have hh := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ (65536:ℝ)) hxbig (by norm_num : (0:ℝ) ≤ 1/8)
    have h16 : (65536:ℝ)^(1/8:ℝ) = 4 := by
      rw [show (65536:ℝ) = 2^16 by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rwa [h16] at hh
  have hx18b : (2:ℝ) ≤ x^(1/8:ℝ) := by linarith
  have hlog3 : (Real.log x)^3 ≤ x^(3/8:ℝ) := by
    calc (Real.log x)^3 ≤ (x^(1/8:ℝ))^3 := pow_le_pow_left₀ (by linarith) hlog8 3
      _ = x^(3/8:ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  have hmul3 : x^(1/2:ℝ) * (Real.log x)^3 ≤ x^(7/8:ℝ) := by
    have h3 : x^(1/2:ℝ) * x^(3/8:ℝ) = x^(7/8:ℝ) := by
      rw [← Real.rpow_add hxpos]; norm_num
    have h4 : x^(1/2:ℝ) * (Real.log x)^3 ≤ x^(1/2:ℝ) * x^(3/8:ℝ) :=
      mul_le_mul_of_nonneg_left hlog3 (by positivity)
    linarith [h3 ▸ h4]
  have hx78 : x^(7/8:ℝ) ≤ x / 2 := by
    have h2 : x^(7/8:ℝ) = x * x^(-(1/8):ℝ) := by
      rw [show (7/8:ℝ) = 1 + (-(1/8)) by norm_num, Real.rpow_add hxpos, Real.rpow_one]
    rw [h2]
    have h3 : x^(-(1/8):ℝ) ≤ (1:ℝ)/2 := by
      rw [Real.rpow_neg hx0, ← one_div]
      exact one_div_le_one_div_of_le (by norm_num) hx18b
    nlinarith [hxpos]
  have hTp3x : Tp + 3 ≤ x := by
    have h4 : x^(1/2:ℝ) * (Real.log x)^3 + 4 ≤ x := by linarith [hmul3, hx78, hxbig]
    linarith [hTple, h4]
  have hTp3pos : 0 < Tp + 3 := by linarith
  have hlogTp_le : Real.log (Tp + 3) ≤ Real.log x := Real.log_le_log hTp3pos hTp3x
  have hlogTp1 : Real.log (Tp + 3) + 1 ≤ 2 * Real.log x := by linarith [hlogTp_le, hlog1]
  -- the zero set
  have hR : (0:ℝ) ≤ 2 + |Tp| := by positivity
  set Z : Finset ℂ := (zetaZeroBallFin (2 + |Tp|) (by positivity)).filter
      (fun ρ => ρ.re = 1/2 ∧ |ρ.im| < Tp) with hZdef
  have hZspec : ∀ ρ ∈ Z, riemannZeta₁ ρ = 0 ∧ (1/4:ℝ) < ρ.re ∧ ρ.re < 2 := by
    intro ρ hρ
    rw [hZdef, Finset.mem_filter] at hρ
    obtain ⟨hρb, hre, him⟩ := hρ
    obtain ⟨_, hζ⟩ := (zetaZeroBallFin_spec (2 + |Tp|) (by positivity) ρ).mp hρb
    exact ⟨hζ, by rw [hre]; norm_num, by rw [hre]; norm_num⟩
  have hZhalf : ∀ ρ ∈ Z, ρ.re = 1/2 := fun ρ hρ =>
    re_half_of_zeta1_zero h (hZspec ρ hρ).1 (hZspec ρ hρ).2.1 (hZspec ρ hρ).2.2
  have hZR : ∀ ρ ∈ Z, ‖ρ‖ ≤ 2 + |Tp| := by
    intro ρ hρ
    rw [hZdef, Finset.mem_filter] at hρ
    obtain ⟨hρb, _, _⟩ := hρ
    have hb := ((zetaZeroBallFin_spec (2 + |Tp|) (by positivity) ρ).mp hρb).1
    simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hb
  -- Step A
  have hSA : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ):ℂ) * (1-(n:ℂ)/(x:ℂ))^m)
      = ((m:ℂ)/(x:ℂ)) * ∫ t in (0:ℝ)..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ((Chebyshev.psi t:ℝ):ℂ) :=
    psi_mfold_sum_eq_integral m (by omega) hxpos
  have hψII : IntervalIntegrable (fun t : ℝ => ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ((Chebyshev.psi t:ℝ):ℂ))
      volume 0 x := intervalIntegrable_Kc_psi m hxpos
  -- polynomial part
  have hKt : ∫ t in (0:ℝ)..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)
      = (x:ℂ)^2/((m:ℂ)*((m+1:ℕ):ℂ)) := integral_one_sub_div_pow_one m (by omega) hxpos
  have hK1int : ∫ t in (0:ℝ)..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) = (x:ℂ)/(m:ℂ) :=
    integral_one_sub_div_pow_zero m (by omega) hxpos
  have hcontKc : Continuous (fun t : ℝ => (1-(t:ℂ)/(x:ℂ))^(m-1)) :=
    (continuous_const.sub (continuous_ofReal.div_const (x:ℂ))).pow (m-1)
  have hIIpol : IntervalIntegrable (fun t : ℝ => ((1-(t:ℂ)/(x:ℂ))^(m-1)) *
      ((t:ℂ) - ((Real.log (2*Real.pi)):ℂ))) volume 0 x :=
    (hcontKc.mul (continuous_ofReal.sub continuous_const)).intervalIntegrable 0 x
  have hpol : ((m:ℂ)/(x:ℂ)) * ∫ t in (0:ℝ)..x,
        ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ((t:ℂ) - ((Real.log (2*Real.pi)):ℂ))
      = (x:ℂ)/(m+1) - ((Real.log (2*Real.pi)):ℂ) := by
    have hIIt : IntervalIntegrable (fun t : ℝ => ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)) volume 0 x :=
      (hcontKc.mul continuous_ofReal).intervalIntegrable 0 x
    have hIIc : IntervalIntegrable (fun t : ℝ => ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ((Real.log (2*Real.pi)):ℂ))
        volume 0 x :=
      (hcontKc.mul continuous_const).intervalIntegrable 0 x
    have hsplit : (∫ t in (0:ℝ)..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ((t:ℂ) - ((Real.log (2*Real.pi)):ℂ)))
        = ∫ t in (0:ℝ)..x, (((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)
            - ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ((Real.log (2*Real.pi)):ℂ)) := by
      apply intervalIntegral.integral_congr; intro t ht; ring
    rw [hsplit, intervalIntegral.integral_sub hIIt hIIc, intervalIntegral.integral_mul_const, hKt, hK1int]
    have hmne : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hxne : (x:ℂ) ≠ 0 := by simpa using (ofReal_ne_zero.mpr hxpos.ne')
    field_simp
    push_cast
    ring
  -- g-integral
  have hge : (∫ t in (0:ℝ)..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ((Chebyshev.psi t:ℝ):ℂ))
      - (∫ t in (0:ℝ)..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ((t:ℂ) - ((Real.log (2*Real.pi)):ℂ)))
      = ∫ t in (0:ℝ)..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) *
          (((Chebyshev.psi t:ℝ):ℂ) - (t:ℂ) + ((Real.log (2*Real.pi)):ℂ)) := by
    rw [← intervalIntegral.integral_sub hψII hIIpol]
    apply intervalIntegral.integral_congr; intro t ht; ring
  have hmain_id : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ):ℂ) * (1-(n:ℂ)/(x:ℂ))^m)
      - ((x:ℂ)/(m+1) - ((Real.log (2*Real.pi)):ℂ))
      = ((m:ℂ)/(x:ℂ)) * ∫ t in (0:ℝ)..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) *
          (((Chebyshev.psi t:ℝ):ℂ) - (t:ℂ) + ((Real.log (2*Real.pi)):ℂ)) := by
    rw [hSA, ← hpol, ← hge]; ring
  set Sig : ℝ → ℂ := fun t => ∑ ρ ∈ Z, (zeta1Order ρ : ℂ) * (t:ℂ)^ρ / ρ with hSigdef
  set ggf : ℝ → ℂ := fun t => ((Chebyshev.psi t:ℝ):ℂ) - (t:ℂ) + ((Real.log (2*Real.pi)):ℂ) with hggf
  have hfar : ∀ t : ℝ, Xf ≤ t → t ≤ x →
      ‖ggf t + Sig t‖ ≤
        Cfar * (t * (Real.log (Tp+3)+1)^3 / Tp) * K
        + C₂ * ((Real.log (Tp+3)+1) * (min 1 (2*t/(Tp*|t - (⌊t⌋₊:ℝ)|))
            + min 1 (2*t/(Tp*|t - ((⌊t⌋₊:ℝ)+1)|))))
        + (if ((⌊t⌋₊:ℝ) = t) then 4*(Real.log (Tp+3)+1) else 0)
        + D * (t^(-(3/2:ℝ)) * (Real.log (Tp+3)+1)^4) := by
    intro t htXf htx
    have ht1 : 1 ≤ t := le_trans hXf1 htXf
    have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg ht1
    have hb : (1/2:ℝ) < 1 + 1/Real.log t := by
      have : 0 ≤ 1/Real.log t := div_nonneg zero_le_one hlogt0
      linarith
    have hft := hXfraw t (le_trans hXfge htXf) Tp δ K hTp5 (by linarith) hδpos hK1 hKδ hgap hgood
    rw [zRectZeros_eq_filter h (by positivity) (by norm_num : (-2:ℝ) < -(3/2))
      (by norm_num : (-(3/2):ℝ) < 1/2) hb] at hft
    have hlogeq : Complex.log (2 * (Real.pi:ℂ)) = ((Real.log (2*Real.pi)):ℂ) := by
      rw [show (2 * (Real.pi:ℂ)) = ((2*Real.pi:ℝ):ℂ) by push_cast; ring,
        Complex.ofReal_log (by positivity)]
    rw [hlogeq] at hft
    have heq : ggf t + Sig t
        = ((Chebyshev.psi t:ℝ):ℂ) - ((t:ℂ) - ((Real.log (2*Real.pi)):ℂ)
            - ∑ ρ ∈ Z, (zeta1Order ρ : ℂ) * (t:ℂ)^ρ / ρ) := by
      rw [hggf, hSigdef]; ring
    rw [heq]
    exact hft
  have hIIggf : IntervalIntegrable (fun t : ℝ => ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ggf t) volume 0 x := by
    refine IntervalIntegrable.congr ?_ (hψII.sub hIIpol)
    intro t ht; rw [hggf]; ring
  have hIIggfXf : IntervalIntegrable (fun t : ℝ => ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ggf t) volume 0 Xf :=
    hIIggf.mono_set (by
      rw [Set.uIcc_of_le hx0]
      intro t ht
      rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ Xf)] at ht
      exact ⟨ht.1, le_trans ht.2 hxXf⟩)
  have hIIggfXfx : IntervalIntegrable (fun t : ℝ => ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ggf t) volume Xf x :=
    hIIggf.mono_set (by
      rw [Set.uIcc_of_le hx0]
      intro t ht
      rw [Set.uIcc_of_le hxXf] at ht
      exact ⟨le_trans (le_of_lt hXfpos) ht.1, ht.2⟩)
  have hsplit : (∫ t in (0:ℝ)..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ggf t)
      = (∫ t in (0:ℝ)..Xf, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ggf t)
        + (∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ggf t) :=
    (intervalIntegral.integral_add_adjacent_intervals hIIggfXf hIIggfXfx).symm
  have hbnd0 : ‖∫ t in (0:ℝ)..Xf, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ggf t‖ ≤ G₀ * Xf := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := Xf) (C := G₀)
      (f := fun t : ℝ => ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ggf t) ?_
    · rwa [sub_zero, abs_of_nonneg (le_of_lt hXfpos)] at h
    · intro t ht
      rw [Set.uIoc_of_le (by linarith : (0:ℝ) ≤ Xf)] at ht
      have ht0 : 0 < t := ht.1
      have htx : t ≤ x := le_trans ht.2 hxXf
      have hnormK : ‖((1:ℂ) - (t:ℂ)/(x:ℂ))^(m-1)‖ ≤ 1 := by
        rw [norm_pow]
        apply pow_le_one₀ (norm_nonneg _)
        have hcast : ((1:ℂ) - (t:ℂ)/(x:ℂ)) = (((1 - t/x : ℝ)):ℂ) := by push_cast; ring
        have hnr : ‖(((1 - t/x : ℝ)):ℂ)‖ = |1 - t/x| := by
          rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]
        rw [hcast, hnr, abs_of_nonneg (sub_nonneg.mpr (by rw [div_le_one hxpos]; exact htx))]
        exact sub_le_self _ (div_nonneg (le_of_lt ht0) (le_of_lt hxpos))
      have hnormg : ‖ggf t‖ ≤ G₀ := by
        rw [hggf]
        have hnr (r : ℝ) : ‖((r:ℝ):ℂ)‖ = |r| := by
          rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]
        have h1 : ‖((Chebyshev.psi t:ℝ):ℂ)‖ ≤ Chebyshev.psi Xf := by
          rw [hnr, abs_of_nonneg (Chebyshev.psi_nonneg t)]
          exact Chebyshev.psi_mono ht.2
        have h2 : ‖(t:ℂ)‖ ≤ Xf := by
          rw [hnr, abs_of_nonneg (le_of_lt ht0)]
          exact ht.2
        have h3 : ‖((Real.log (2*Real.pi)):ℂ)‖ ≤ 2 := by
          rw [hnr, abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
          exact log_two_pi_le_two
        calc ‖((Chebyshev.psi t:ℝ):ℂ) - (t:ℂ) + ((Real.log (2*Real.pi)):ℂ)‖
            ≤ ‖((Chebyshev.psi t:ℝ):ℂ) - (t:ℂ)‖ + ‖((Real.log (2*Real.pi)):ℂ)‖ := norm_add_le _ _
          _ ≤ (‖((Chebyshev.psi t:ℝ):ℂ)‖ + ‖(t:ℂ)‖) + 2 := by
              have := norm_sub_le ((Chebyshev.psi t:ℝ):ℂ) (t:ℂ); linarith
          _ ≤ (Chebyshev.psi Xf + Xf) + 2 := by linarith
          _ = G₀ := by rw [hG₀def]
      rw [norm_mul]
      calc ‖((1:ℂ) - (t:ℂ)/(x:ℂ))^(m-1)‖ * ‖ggf t‖ ≤ 1 * G₀ :=
            mul_le_mul hnormK hnormg (norm_nonneg _) (by linarith)
        _ = G₀ := one_mul _
  have hIIsig : IntervalIntegrable (fun t : ℝ => ((1-(t:ℂ)/(x:ℂ))^(m-1)) * Sig t) volume Xf x := by
    apply Continuous.intervalIntegrable
    rw [hSigdef]
    apply Continuous.mul hcontKc
    apply continuous_finsetSum
    intro ρ hρ
    have hρz : 0 < ρ.re := by have := (hZspec ρ hρ).2.1; linarith
    exact (continuous_const.mul (continuous_ofReal_cpow_const hρz)).div_const ρ
  have hIIeex : IntervalIntegrable (fun t : ℝ => ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (ggf t + Sig t))
      volume Xf x :=
    (hIIggfXfx.add hIIsig).congr (fun t _ => by ring)
  have hggf_split : (∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ggf t)
      = (∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (ggf t + Sig t))
        - (∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * Sig t) := by
    have h1 : (∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (ggf t + Sig t))
        = (∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ggf t)
          + (∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * Sig t) := by
      rw [show (fun t : ℝ => ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (ggf t + Sig t))
          = (fun t : ℝ => ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ggf t
              + ((1-(t:ℂ)/(x:ℂ))^(m-1)) * Sig t) by funext t; ring]
      exact intervalIntegral.integral_add hIIggfXfx hIIsig
    rw [h1]; ring
  have hee_bnd : ‖∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (ggf t + Sig t)‖
      ≤ 8*Cfar*K*(Real.log x)^3/Tp * (x^2/2)
        + (4*C₂*(Real.log x) + 8*(Real.log x) + 16*D*Xf^(-(3/2:ℝ))*(Real.log x)^4) * x := by
    set Aa : ℝ := 8*Cfar*K*(Real.log x)^3/Tp with hAadef
    set Ll : ℝ := 4*C₂*(Real.log x) + 8*(Real.log x) + 16*D*Xf^(-(3/2:ℝ))*(Real.log x)^4 with hLldef
    have hAa_nn : 0 ≤ Aa := by rw [hAadef]; positivity
    have hLl_nn : 0 ≤ Ll := by rw [hLldef]; positivity
    have hgb : IntervalIntegrable (fun t : ℝ => Aa * t + Ll) volume Xf x :=
      ((continuous_const.mul continuous_id).add continuous_const).intervalIntegrable _ _
    have hpoint : ∀ᵐ t : ℝ ∂volume, t ∈ Set.Ioc Xf x →
        ‖((1-(t:ℂ)/(x:ℂ))^(m-1)) * (ggf t + Sig t)‖ ≤ Aa * t + Ll := by
      filter_upwards with t ht
      have ht0 : 0 < t := lt_of_lt_of_le hXfpos (le_of_lt ht.1)
      have htx : t ≤ x := ht.2
      have hnormK : ‖((1:ℂ) - (t:ℂ)/(x:ℂ))^(m-1)‖ ≤ 1 := by
        rw [norm_pow]
        apply pow_le_one₀ (norm_nonneg _)
        have hcast : ((1:ℂ) - (t:ℂ)/(x:ℂ)) = (((1 - t/x : ℝ)):ℂ) := by push_cast; ring
        have hnr : ‖(((1 - t/x : ℝ)):ℂ)‖ = |1 - t/x| := by
          rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]
        rw [hcast, hnr, abs_of_nonneg (sub_nonneg.mpr (by rw [div_le_one hxpos]; exact htx))]
        exact sub_le_self _ (div_nonneg (le_of_lt ht0) (le_of_lt hxpos))
      have herr := hfar t (le_of_lt ht.1) htx
      have hlog2 : (Real.log (Tp+3)+1)^3 ≤ 8*(Real.log x)^3 := by
        have h0 : (0:ℝ) ≤ Real.log (Tp+3)+1 := by
          have := Real.log_nonneg (by linarith : (1:ℝ) ≤ Tp+3); linarith
        calc (Real.log (Tp+3)+1)^3 ≤ (2*Real.log x)^3 := pow_le_pow_left₀ h0 hlogTp1 3
          _ = 8*(Real.log x)^3 := by ring
      have hmin : min 1 (2*t/(Tp*|t - (⌊t⌋₊:ℝ)|)) + min 1 (2*t/(Tp*|t - ((⌊t⌋₊:ℝ)+1)|)) ≤ 2 := by
        have h1 : min 1 (2*t/(Tp*|t - (⌊t⌋₊:ℝ)|)) ≤ 1 := min_le_left _ _
        have h2 : min 1 (2*t/(Tp*|t - ((⌊t⌋₊:ℝ)+1)|)) ≤ 1 := min_le_left _ _
        linarith
      have hif : (if ((⌊t⌋₊:ℝ) = t) then 4*(Real.log (Tp+3)+1) else 0) ≤ 8*Real.log x := by
        split_ifs with hh
        · linarith [hlogTp1, hlog1]
        · linarith [hlog1]
      have ht3 : t^(-(3/2:ℝ)) ≤ Xf^(-(3/2:ℝ)) := by
        rw [Real.rpow_neg (le_of_lt ht0), Real.rpow_neg (le_of_lt hXfpos)]
        exact (inv_le_inv₀ (Real.rpow_pos_of_pos ht0 _) (Real.rpow_pos_of_pos hXfpos _)).mpr
          (Real.rpow_le_rpow (le_of_lt hXfpos) (le_of_lt ht.1) (by norm_num))
      have htlog : (Real.log (Tp+3)+1)^4 ≤ 16*(Real.log x)^4 := by
        have h0 : (0:ℝ) ≤ Real.log (Tp+3)+1 := by
          have := Real.log_nonneg (by linarith : (1:ℝ) ≤ Tp+3); linarith
        calc (Real.log (Tp+3)+1)^4 ≤ (2*Real.log x)^4 := pow_le_pow_left₀ h0 hlogTp1 4
          _ = 16*(Real.log x)^4 := by ring
      have herr2 : ‖ggf t + Sig t‖ ≤ Aa * t + Ll := by
        rw [hAadef, hLldef]
        refine le_trans herr ?_
        have h1 : Cfar * (t * (Real.log (Tp+3)+1)^3 / Tp) * K ≤ 8*Cfar*K*(Real.log x)^3/Tp * t := by
          have hKnn : 0 ≤ K := by linarith [hK1]
          rw [show Cfar * (t * (Real.log (Tp+3)+1)^3 / Tp) * K
              = Cfar*K*(Real.log (Tp+3)+1)^3/Tp * t by ring]
          have hCK : Cfar*K*(Real.log (Tp+3)+1)^3 ≤ Cfar*K*(8*(Real.log x)^3) :=
            mul_le_mul_of_nonneg_left hlog2 (by positivity)
          have hd : Cfar*K*(Real.log (Tp+3)+1)^3/Tp ≤ Cfar*K*(8*(Real.log x)^3)/Tp :=
            div_le_div_of_nonneg_right hCK (le_of_lt hTppos)
          calc Cfar*K*(Real.log (Tp+3)+1)^3/Tp * t
              ≤ Cfar*K*(8*(Real.log x)^3)/Tp * t :=
                mul_le_mul_of_nonneg_right hd (le_of_lt ht0)
            _ = 8*Cfar*K*(Real.log x)^3/Tp * t := by ring
        have h2 : C₂ * ((Real.log (Tp+3)+1) * (min 1 (2*t/(Tp*|t - (⌊t⌋₊:ℝ)|))
              + min 1 (2*t/(Tp*|t - ((⌊t⌋₊:ℝ)+1)|)))) ≤ 4*C₂*(Real.log x) := by
          have hCn : 0 ≤ C₂ := le_of_lt hC₂p
          have h0 : (0:ℝ) ≤ Real.log (Tp+3)+1 := by
            have := Real.log_nonneg (by linarith : (1:ℝ) ≤ Tp+3); linarith
          have hmm : (Real.log (Tp+3)+1) * (min 1 (2*t/(Tp*|t - (⌊t⌋₊:ℝ)|))
              + min 1 (2*t/(Tp*|t - ((⌊t⌋₊:ℝ)+1)|))) ≤ (Real.log (Tp+3)+1)*2 :=
            mul_le_mul_of_nonneg_left hmin h0
          calc C₂ * ((Real.log (Tp+3)+1) * (min 1 (2*t/(Tp*|t - (⌊t⌋₊:ℝ)|))
                + min 1 (2*t/(Tp*|t - ((⌊t⌋₊:ℝ)+1)|))))
              ≤ C₂ * ((Real.log (Tp+3)+1)*2) := mul_le_mul_of_nonneg_left hmm hCn
            _ ≤ C₂ * (2*(2*Real.log x)) := by
                apply mul_le_mul_of_nonneg_left _ hCn; linarith [hlogTp1]
            _ = 4*C₂*(Real.log x) := by ring
        have h4 : D * (t^(-(3/2:ℝ)) * (Real.log (Tp+3)+1)^4)
            ≤ 16*D*Xf^(-(3/2:ℝ))*(Real.log x)^4 := by
          have hDn : 0 ≤ D := le_of_lt hDp
          have hXfnn : 0 ≤ Xf^(-(3/2:ℝ)) := le_of_lt (Real.rpow_pos_of_pos hXfpos _)
          calc D * (t^(-(3/2:ℝ)) * (Real.log (Tp+3)+1)^4)
              ≤ D * (Xf^(-(3/2:ℝ)) * (16*(Real.log x)^4)) := by
                apply mul_le_mul_of_nonneg_left _ hDn
                exact mul_le_mul ht3 htlog (by positivity) hXfnn
            _ = 16*D*Xf^(-(3/2:ℝ))*(Real.log x)^4 := by ring
        linarith [h1, h2, hif, h4]
      rw [norm_mul]
      calc ‖((1:ℂ) - (t:ℂ)/(x:ℂ))^(m-1)‖ * ‖ggf t + Sig t‖
          ≤ 1 * (Aa * t + Ll) := mul_le_mul hnormK herr2 (norm_nonneg _) (by norm_num)
        _ = Aa * t + Ll := one_mul _
    have hbound := intervalIntegral.norm_integral_le_of_norm_le (a := Xf) (b := x) hxXf
      (f := fun t : ℝ => ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (ggf t + Sig t)) hpoint hgb
    refine le_trans hbound ?_
    have hint : ∫ t in Xf..x, (Aa * t + Ll) = Aa * (x^2/2 - Xf^2/2) + Ll * (x - Xf) := by
      have h1 : IntervalIntegrable (fun t : ℝ => Aa * t) volume Xf x :=
        (continuous_const.mul continuous_id).intervalIntegrable _ _
      have h2 : IntervalIntegrable (fun _ : ℝ => Ll) volume Xf x := intervalIntegrable_const
      have h3 : (∫ t in Xf..x, (Aa * t + Ll))
          = (∫ t in Xf..x, Aa * t) + (∫ t in Xf..x, Ll) := by
        rw [show (fun t : ℝ => Aa * t + Ll) = ((fun t : ℝ => Aa * t) + (fun _ : ℝ => Ll)) by rfl]
        exact intervalIntegral.integral_add h1 h2
      rw [h3, intervalIntegral.integral_const_mul, integral_id,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [hint, hAadef, hLldef]
    nlinarith [sq_nonneg Xf, le_of_lt hXfpos, sq_nonneg x]
  have hsum2 : (∑ ρ ∈ Z, (zeta1Order ρ : ℝ)/‖ρ‖^2) ≤ β :=
    zeta1Order_sum_le_beta h hR Z (fun ρ hρ =>
      ⟨(hZspec ρ hρ).1, hZR ρ hρ, (hZspec ρ hρ).2.1, (hZspec ρ hρ).2.2⟩)
  have hinv_rho : (∑ ρ ∈ Z, (zeta1Order ρ : ℝ)/‖ρ‖) ≤ 3*Tp*β := by
    have hterm : ∀ ρ ∈ Z, (zeta1Order ρ : ℝ)/‖ρ‖ ≤ 3*Tp*((zeta1Order ρ : ℝ)/‖ρ‖^2) := by
      intro ρ hρ
      have hnorm : ‖ρ‖ ≤ 3*Tp := by
        have h := hZR ρ hρ
        rw [abs_of_pos hTppos] at h
        linarith [hTp5]
      have hre : ρ.re = 1/2 := hZhalf ρ hρ
      have hpos : 0 < ‖ρ‖ := by
        have h := Complex.abs_re_le_norm ρ
        rw [hre] at h
        have : (1/2:ℝ) ≤ ‖ρ‖ := by simpa using h
        linarith
      have hnn : 0 ≤ (zeta1Order ρ : ℝ) := by positivity
      have hgoal : (‖ρ‖)⁻¹ ≤ 3*Tp * (‖ρ‖^2)⁻¹ := by
        rw [inv_le_iff_one_le_mul₀ hpos]
        rw [show 3*Tp*(‖ρ‖^2)⁻¹*‖ρ‖ = 3*Tp/‖ρ‖ by field_simp]
        rw [le_div_iff₀ hpos]; linarith
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc (zeta1Order ρ : ℝ) * (‖ρ‖)⁻¹ ≤ (zeta1Order ρ : ℝ) * (3*Tp*(‖ρ‖^2)⁻¹) :=
            mul_le_mul_of_nonneg_left hgoal hnn
        _ = 3*Tp * ((zeta1Order ρ : ℝ) * (‖ρ‖^2)⁻¹) := by ring
    calc (∑ ρ ∈ Z, (zeta1Order ρ : ℝ)/‖ρ‖)
        = ∑ ρ ∈ Z, (zeta1Order ρ : ℝ)*(‖ρ‖)⁻¹ := by
          apply Finset.sum_congr rfl; intro ρ hρ; rw [div_eq_mul_inv]
      _ ≤ ∑ ρ ∈ Z, 3*Tp*((zeta1Order ρ : ℝ)/‖ρ‖^2) := Finset.sum_le_sum hterm
      _ = 3*Tp * ∑ ρ ∈ Z, ((zeta1Order ρ : ℝ)/‖ρ‖^2) := by rw [Finset.mul_sum]
      _ ≤ 3*Tp*β := mul_le_mul_of_nonneg_left hsum2 (by positivity)
  have hInt_cpow : ∀ ρ ∈ Z, ‖∫ t in (0:ℝ)..Xf, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ‖ ≤ Xf^(3/2:ℝ) := by
    intro ρ hρ
    have hre12 : ρ.re = 1/2 := hZhalf ρ hρ
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := Xf)
      (C := Xf^(1/2:ℝ)) (f := fun t : ℝ => ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ) ?_
    · rw [sub_zero, abs_of_nonneg (le_of_lt hXfpos)] at hb
      calc ‖∫ t in (0:ℝ)..Xf, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ‖ ≤ Xf^(1/2:ℝ) * Xf := hb
        _ = Xf^(3/2:ℝ) := by
            have hh : Xf^(1/2:ℝ) * Xf^(1:ℝ) = Xf^(3/2:ℝ) := by
              rw [← Real.rpow_add hXfpos]; norm_num
            rwa [Real.rpow_one] at hh
    · intro t ht
      rw [Set.uIoc_of_le (le_of_lt hXfpos)] at ht
      have ht0 : 0 < t := ht.1
      have htXf : t ≤ Xf := ht.2
      have hnormK : ‖((1:ℂ) - (t:ℂ)/(x:ℂ))^(m-1)‖ ≤ 1 := by
        rw [norm_pow]
        apply pow_le_one₀ (norm_nonneg _)
        have hcast : ((1:ℂ) - (t:ℂ)/(x:ℂ)) = (((1 - t/x : ℝ)):ℂ) := by push_cast; ring
        have hnr : ‖(((1 - t/x : ℝ)):ℂ)‖ = |1 - t/x| := by
          rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]
        rw [hcast, hnr, abs_of_nonneg (sub_nonneg.mpr (by
          rw [div_le_one hxpos]; exact le_trans htXf hxXf))]
        exact sub_le_self _ (div_nonneg (le_of_lt ht0) (le_of_lt hxpos))
      have hnormc : ‖(t:ℂ)^ρ‖ = t^(1/2:ℝ) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0, hre12]
      rw [norm_mul, hnormc]
      have ht12 : t^(1/2:ℝ) ≤ Xf^(1/2:ℝ) :=
        Real.rpow_le_rpow (le_of_lt ht0) htXf (by norm_num)
      calc ‖((1:ℂ) - (t:ℂ)/(x:ℂ))^(m-1)‖ * t^(1/2:ℝ)
          ≤ 1 * Xf^(1/2:ℝ) := mul_le_mul hnormK ht12 (by positivity) (by linarith)
        _ = Xf^(1/2:ℝ) := one_mul _
  -- the exact value of the Sig integral
  have hfact : (Nat.factorial m : ℂ) = (m:ℂ) * (Nat.factorial (m-1) : ℂ) := by
    have h := Nat.factorial_succ (m-1)
    have hm1 : (m-1)+1 = m := by omega
    rw [hm1] at h
    rw [h]; push_cast; ring
  have hsig : ((m:ℂ)/(x:ℂ)) * (∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * Sig t)
      = (Nat.factorial m : ℂ) * (∑ ρ ∈ Z, (zeta1Order ρ : ℂ) * (x:ℂ)^ρ
            / ((Finset.range (m+1)).prod (fun k => (ρ:ℂ) + (k:ℂ))))
        - ((m:ℂ)/(x:ℂ)) * (∑ ρ ∈ Z, ((zeta1Order ρ : ℂ)/ρ) *
            (∫ t in (0:ℝ)..Xf, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ)) := by
    rw [hSigdef]
    have hsum_int : (∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) *
          (∑ ρ ∈ Z, (zeta1Order ρ : ℂ) * (t:ℂ)^ρ / ρ))
        = ∑ ρ ∈ Z, (∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) *
            ((zeta1Order ρ : ℂ) * (t:ℂ)^ρ / ρ)) := by
      rw [show (fun t : ℝ => ((1-(t:ℂ)/(x:ℂ))^(m-1)) *
            (∑ ρ ∈ Z, (zeta1Order ρ : ℂ) * (t:ℂ)^ρ / ρ))
          = (fun t : ℝ => ∑ ρ ∈ Z, ((1-(t:ℂ)/(x:ℂ))^(m-1)) *
              ((zeta1Order ρ : ℂ) * (t:ℂ)^ρ / ρ)) by funext t; rw [Finset.mul_sum]]
      exact intervalIntegral.integral_finsetSum (μ := volume) (a := Xf) (b := x) (fun ρ hρ => by
        have hρz : 0 < ρ.re := by have := (hZspec ρ hρ).2.1; linarith
        have hc : Continuous (fun t : ℝ => ((1-(t:ℂ)/(x:ℂ))^(m-1)) *
            ((zeta1Order ρ : ℂ) * (t:ℂ)^ρ / ρ)) := by
          apply Continuous.mul hcontKc
          exact (continuous_const.mul (continuous_ofReal_cpow_const hρz)).div_const ρ
        exact hc.intervalIntegrable (μ := volume) Xf x)
    rw [hsum_int, Finset.mul_sum]
    have hper : ∀ ρ ∈ Z, ((m:ℂ)/(x:ℂ)) *
          (∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ((zeta1Order ρ : ℂ) * (t:ℂ)^ρ / ρ))
        = (Nat.factorial m : ℂ) * ((zeta1Order ρ : ℂ) * (x:ℂ)^ρ
              / ((Finset.range (m+1)).prod (fun k => (ρ:ℂ) + (k:ℂ))))
          - ((m:ℂ)/(x:ℂ)) * (((zeta1Order ρ : ℂ)/ρ) *
              (∫ t in (0:ℝ)..Xf, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ)) := by
      intro ρ hρ
      have hρz : 0 < ρ.re := by have := (hZspec ρ hρ).2.1; linarith
      have hρne : ρ ≠ 0 := by rintro rfl; norm_num at hρz
      have hII1 : IntervalIntegrable (fun t : ℝ => ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ) volume 0 x :=
        (hcontKc.mul (continuous_ofReal_cpow_const hρz)).intervalIntegrable 0 x
      have hII2 : IntervalIntegrable (fun t : ℝ => ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ) volume 0 Xf :=
        hII1.mono_set (by
          rw [Set.uIcc_of_le hx0]
          intro t ht
          rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ Xf)] at ht
          exact ⟨ht.1, le_trans ht.2 hxXf⟩)
      have hadj : (∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ)
          = (∫ t in (0:ℝ)..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ)
            - (∫ t in (0:ℝ)..Xf, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ) :=
        (intervalIntegral.integral_interval_sub_left hII1 hII2).symm
      have h0x : (∫ t in (0:ℝ)..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ)
          = (x:ℂ)^(ρ+1) * ((Nat.factorial (m-1) : ℂ)
              / ((Finset.range m).prod (fun k => ρ + ((k:ℂ)+1)))) := by
        rw [integral_one_sub_div_pow ρ hρz m (by omega) hxpos,
          betaIntegral_eq ρ hρz m (by omega)]
      have hprod : ((Finset.range (m+1)).prod (fun k => (ρ:ℂ) + (k:ℂ)))
          = ρ * ((Finset.range m).prod (fun k => ρ + ((k:ℂ)+1))) := by
        rw [Finset.prod_range_succ']
        simp only [Nat.cast_add, Nat.cast_one, add_zero]
        ring
      rw [show (fun t : ℝ => ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ((zeta1Order ρ : ℂ) * (t:ℂ)^ρ / ρ))
          = (fun t : ℝ => ((zeta1Order ρ : ℂ)/ρ) * (((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ)) by
        funext t; ring]
      rw [intervalIntegral.integral_const_mul, hadj, h0x, hprod]
      have hmne : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hxne : (x:ℂ) ≠ 0 := by simpa using (ofReal_ne_zero.mpr hxpos.ne')
      rw [Complex.cpow_add ρ 1 hxne, Complex.cpow_one, hfact]
      field_simp
      try ring
    have hR : (Nat.factorial m : ℂ) * (∑ ρ ∈ Z, (zeta1Order ρ : ℂ) * (x:ℂ)^ρ
            / ((Finset.range (m+1)).prod (fun k => (ρ:ℂ) + (k:ℂ))))
        - ((m:ℂ)/(x:ℂ)) * (∑ ρ ∈ Z, ((zeta1Order ρ : ℂ)/ρ) *
            (∫ t in (0:ℝ)..Xf, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ))
        = ∑ ρ ∈ Z, ((Nat.factorial m : ℂ) * ((zeta1Order ρ : ℂ) * (x:ℂ)^ρ
              / ((Finset.range (m+1)).prod (fun k => (ρ:ℂ) + (k:ℂ))))
            - ((m:ℂ)/(x:ℂ)) * (((zeta1Order ρ : ℂ)/ρ) *
              (∫ t in (0:ℝ)..Xf, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ))) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_sub_distrib]
    rw [hR]
    apply Finset.sum_congr rfl
    intro ρ hρ
    exact hper ρ hρ
  -- bounds
  have hsum_mfold : ‖∑ ρ ∈ Z, (zeta1Order ρ : ℂ) * (x:ℂ)^ρ
        / ((Finset.range (m+1)).prod (fun k => (ρ:ℂ) + (k:ℂ)))‖ ≤ (Nat.factorial m : ℝ) * β * Real.sqrt x := by
    have h := psi_mfold_tiltedZeroSum_bound h m (by omega) Z x hZspec hx1
    rw [hβdef]
    simpa using h
  have hcorr_bnd : ((m:ℝ)/x) * ‖∑ ρ ∈ Z, ((zeta1Order ρ : ℂ)/ρ) *
        (∫ t in (0:ℝ)..Xf, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ)‖ ≤ 6 * (m:ℝ) * β * Xf^(3/2:ℝ) := by
    have hs : ‖∑ ρ ∈ Z, ((zeta1Order ρ : ℂ)/ρ) *
        (∫ t in (0:ℝ)..Xf, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ)‖
        ≤ ∑ ρ ∈ Z, (zeta1Order ρ : ℝ)/‖ρ‖ * Xf^(3/2:ℝ) := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
      intro ρ hρ
      rw [norm_mul, norm_div]
      have hρne : ρ ≠ 0 := by
        intro h0
        have hz : ρ.re = 1/2 := hZhalf ρ hρ
        rw [h0] at hz
        norm_num at hz
      have hXf3 : (0:ℝ) ≤ Xf^(3/2:ℝ) := le_of_lt (Real.rpow_pos_of_pos hXfpos _)
      calc ‖(zeta1Order ρ : ℂ)‖ / ‖ρ‖ * ‖∫ t in (0:ℝ)..Xf, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ‖
          ≤ (zeta1Order ρ : ℝ)/‖ρ‖ * Xf^(3/2:ℝ) := by
            apply mul_le_mul
            · rw [Complex.norm_natCast]
            · exact hInt_cpow ρ hρ
            · exact norm_nonneg _
            · positivity
        _ = _ := rfl
    have hsm : (∑ ρ ∈ Z, (zeta1Order ρ : ℝ)/‖ρ‖ * Xf^(3/2:ℝ))
        = (∑ ρ ∈ Z, (zeta1Order ρ : ℝ)/‖ρ‖) * Xf^(3/2:ℝ) := by
      rw [Finset.sum_mul]
    rw [hsm] at hs
    have hxlog : Tp / x ≤ 2 := by
      rw [div_le_iff₀ hxpos]
      have h7 : Real.sqrt x * (Real.log x)^3 ≤ x := by
        rw [Real.sqrt_eq_rpow]
        calc x^(1/2:ℝ) * (Real.log x)^3 ≤ x^(1/2:ℝ) * x^(3/8:ℝ) :=
              mul_le_mul_of_nonneg_left hlog3 (by positivity)
          _ = x^(7/8:ℝ) := by rw [← Real.rpow_add hxpos]; norm_num
          _ ≤ x := by
              have hh := Real.rpow_le_rpow_of_exponent_le hx1 (show (7/8:ℝ) ≤ 1 by norm_num)
              rwa [Real.rpow_one] at hh
      linarith [hTple, h7, hx1]
    calc ((m:ℝ)/x) * ‖∑ ρ ∈ Z, ((zeta1Order ρ : ℂ)/ρ) *
          (∫ t in (0:ℝ)..Xf, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ)‖
        = ((m:ℝ) * ‖∑ ρ ∈ Z, ((zeta1Order ρ : ℂ)/ρ) *
            (∫ t in (0:ℝ)..Xf, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ)‖) / x := by ring
      _ ≤ ((m:ℝ) * (3*Tp*β * Xf^(3/2:ℝ))) / x := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hxpos)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hXf3 : 0 ≤ Xf^(3/2:ℝ) := le_of_lt (Real.rpow_pos_of_pos hXfpos _)
          linarith [hs, mul_le_mul_of_nonneg_right hinv_rho hXf3]
      _ = 3 * (m:ℝ) * β * Xf^(3/2:ℝ) * (Tp/x) := by ring
      _ ≤ 6 * (m:ℝ) * β * Xf^(3/2:ℝ) := by
          have hb1 : 0 ≤ (m:ℝ) * β * Xf^(3/2:ℝ) := by positivity
          nlinarith [hxlog, hb1]
  -- final assembly
  have hfinal : ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ):ℂ) *
        (1-(n:ℂ)/(x:ℂ))^m - ((x:ℂ)/(m+1) - ((Real.log (2*Real.pi)):ℂ))‖ ≤ C * Real.sqrt x := by
    rw [hmain_id]
    have hnorm2 : ‖((m:ℂ)/(x:ℂ))‖ = (m:ℝ)/x := by
      have hxr : ‖(x:ℂ)‖ = x := by
        rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs,
          abs_of_nonneg hx0]
      rw [norm_div, Complex.norm_natCast, hxr]
    rw [norm_mul, hnorm2]
    have hIg : ‖∫ t in (0:ℝ)..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ggf t‖
        ≤ G₀ * Xf + ((8*Cfar*K*(Real.log x)^3/Tp * (x^2/2)
            + (4*C₂*(Real.log x) + 8*(Real.log x) + 16*D*Xf^(-(3/2:ℝ))*(Real.log x)^4) * x)
          + ‖∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * Sig t‖) := by
      rw [hsplit]
      calc ‖(∫ t in (0:ℝ)..Xf, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ggf t)
            + (∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ggf t)‖
          ≤ ‖∫ t in (0:ℝ)..Xf, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ggf t‖
            + ‖∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ggf t‖ := norm_add_le _ _
        _ ≤ G₀ * Xf + ((8*Cfar*K*(Real.log x)^3/Tp * (x^2/2)
              + (4*C₂*(Real.log x) + 8*(Real.log x) + 16*D*Xf^(-(3/2:ℝ))*(Real.log x)^4) * x)
            + ‖∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * Sig t‖) := by
            have h2 : ‖∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ggf t‖
                ≤ (8*Cfar*K*(Real.log x)^3/Tp * (x^2/2)
                    + (4*C₂*(Real.log x) + 8*(Real.log x) + 16*D*Xf^(-(3/2:ℝ))*(Real.log x)^4) * x)
                  + ‖∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * Sig t‖ := by
              rw [hggf_split]
              calc ‖(∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (ggf t + Sig t))
                    - (∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * Sig t)‖
                  ≤ ‖∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (ggf t + Sig t)‖
                    + ‖∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * Sig t‖ := norm_sub_le _ _
                _ ≤ _ := by linarith [hee_bnd]
            exact add_le_add hbnd0 h2
    have hSig_bnd : ((m:ℝ)/x) * ‖∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * Sig t‖
        ≤ (Nat.factorial m : ℝ)^2 * β * Real.sqrt x + 6 * (m:ℝ) * β * Xf^(3/2:ℝ) := by
      have heq : ((m:ℂ)/(x:ℂ)) * (∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * Sig t)
          = (Nat.factorial m : ℂ) * (∑ ρ ∈ Z, (zeta1Order ρ : ℂ) * (x:ℂ)^ρ
                / ((Finset.range (m+1)).prod (fun k => (ρ:ℂ) + (k:ℂ))))
            - ((m:ℂ)/(x:ℂ)) * (∑ ρ ∈ Z, ((zeta1Order ρ : ℂ)/ρ) *
                (∫ t in (0:ℝ)..Xf, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ)) := hsig
      have h1 : ((m:ℝ)/x) * ‖∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * Sig t‖
          = ‖((m:ℂ)/(x:ℂ)) * (∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * Sig t)‖ := by
        rw [norm_mul, hnorm2]
      rw [h1, heq]
      refine le_trans (norm_sub_le _ _) ?_
      have h3 : ‖(Nat.factorial m : ℂ) * (∑ ρ ∈ Z, (zeta1Order ρ : ℂ) * (x:ℂ)^ρ
            / ((Finset.range (m+1)).prod (fun k => (ρ:ℂ) + (k:ℂ))))‖
          ≤ (Nat.factorial m : ℝ)^2 * β * Real.sqrt x := by
        have hfacnn : (0:ℝ) ≤ (Nat.factorial m : ℝ) := by positivity
        calc ‖(Nat.factorial m : ℂ) * (∑ ρ ∈ Z, (zeta1Order ρ : ℂ) * (x:ℂ)^ρ
              / ((Finset.range (m+1)).prod (fun k => (ρ:ℂ) + (k:ℂ))))‖
            = (Nat.factorial m : ℝ) * ‖∑ ρ ∈ Z, (zeta1Order ρ : ℂ) * (x:ℂ)^ρ
              / ((Finset.range (m+1)).prod (fun k => (ρ:ℂ) + (k:ℂ)))‖ := by
              rw [norm_mul, Complex.norm_natCast]
          _ ≤ (Nat.factorial m : ℝ) * ((Nat.factorial m : ℝ) * β * Real.sqrt x) :=
              mul_le_mul_of_nonneg_left hsum_mfold hfacnn
          _ = (Nat.factorial m : ℝ)^2 * β * Real.sqrt x := by ring
      have h4 : ‖((m:ℂ)/(x:ℂ)) * (∑ ρ ∈ Z, ((zeta1Order ρ : ℂ)/ρ) *
            (∫ t in (0:ℝ)..Xf, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * (t:ℂ)^ρ))‖
          ≤ 6 * (m:ℝ) * β * Xf^(3/2:ℝ) := by
        rw [norm_mul, hnorm2]; exact hcorr_bnd
      exact add_le_add h3 h4
    have htotal : ((m:ℝ)/x) * ‖∫ t in (0:ℝ)..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ggf t‖
        ≤ (Nat.factorial m : ℝ)^2 * β * Real.sqrt x + m * G₀ * Xf
          + 4*(m:ℝ)*Cfar*K*Real.sqrt x
          + ((m:ℝ)*(4*C₂ + 8) + 16*(m:ℝ)*D*Xf^(-(3/2:ℝ))) * Real.sqrt x
          + 6 * (m:ℝ) * β * Xf^(3/2:ℝ) := by
      have hAa2 : ((m:ℝ)/x) * (8*Cfar*K*(Real.log x)^3/Tp * (x^2/2))
          ≤ 4*(m:ℝ)*Cfar*K*Real.sqrt x := by
        have hTpge' : Real.sqrt x * (Real.log x)^3 ≤ Tp := by
          have hsp : Real.sqrt x = x^(1/2:ℝ) := Real.sqrt_eq_rpow x
          rw [hsp]; exact hTpge
        have hTpge'' : Real.sqrt x * (Real.log x)^3 ≤ Tp := hTpge'
        have hlogx3pos : 0 ≤ (Real.log x)^3 := by positivity
        have hspos : 0 < Real.sqrt x := Real.sqrt_pos_of_pos hxpos
        have hden : 0 < Real.sqrt x * (Real.log x)^3 := mul_pos hspos (by positivity)
        have h1 : 8*Cfar*K*(Real.log x)^3/Tp * (x^2/2) ≤ 8*Cfar*K*(Real.log x)^3/(Real.sqrt x * (Real.log x)^3) * (x^2/2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply div_le_div_of_nonneg_left (by positivity) hden hTpge''
        have h2 : ((m:ℝ)/x) * (8*Cfar*K*(Real.log x)^3/(Real.sqrt x * (Real.log x)^3) * (x^2/2))
            = 4*(m:ℝ)*Cfar*K*Real.sqrt x := by
          field_simp
          rw [Real.sq_sqrt hx0]
          ring
        calc ((m:ℝ)/x) * (8*Cfar*K*(Real.log x)^3/Tp * (x^2/2))
            ≤ ((m:ℝ)/x) * (8*Cfar*K*(Real.log x)^3/(Real.sqrt x * (Real.log x)^3) * (x^2/2)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = 4*(m:ℝ)*Cfar*K*Real.sqrt x := h2
      have hLl2 : ((m:ℝ)/x) * ((4*C₂*(Real.log x) + 8*(Real.log x) + 16*D*Xf^(-(3/2:ℝ))*(Real.log x)^4) * x)
          ≤ ((m:ℝ)*(4*C₂ + 8) + 16*(m:ℝ)*D*Xf^(-(3/2:ℝ))) * Real.sqrt x := by
        have h1 : 4*C₂*(Real.log x) + 8*(Real.log x) + 16*D*Xf^(-(3/2:ℝ))*(Real.log x)^4
            ≤ (4*C₂ + 8) * x^(1/8:ℝ) + 16*D*Xf^(-(3/2:ℝ)) * x^(1/2:ℝ) := by
          have hC₂n : 0 ≤ C₂ := le_of_lt hC₂p
          have hDn : 0 ≤ D := le_of_lt hDp
          have h4 : (Real.log x)^4 ≤ x^(1/2:ℝ) := by
            calc (Real.log x)^4 = (Real.log x)^3 * Real.log x := by ring
              _ ≤ x^(3/8:ℝ) * x^(1/8:ℝ) :=
                  mul_le_mul hlog3 hlog8 (by linarith [hlog1]) (by positivity)
              _ = x^(1/2:ℝ) := by rw [← Real.rpow_add hxpos]; norm_num
          have h1 : 4*C₂*(Real.log x) ≤ 4*C₂*x^(1/8:ℝ) :=
            mul_le_mul_of_nonneg_left hlog8 (by positivity)
          have h2 : 8*(Real.log x) ≤ 8*x^(1/8:ℝ) :=
            mul_le_mul_of_nonneg_left hlog8 (by norm_num)
          have h3 : 16*D*Xf^(-(3/2:ℝ))*(Real.log x)^4 ≤ 16*D*Xf^(-(3/2:ℝ))*x^(1/2:ℝ) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
          nlinarith [h1, h2, h3]
        have h2 : (4*C₂ + 8) * x^(1/8:ℝ) ≤ (4*C₂ + 8) * Real.sqrt x := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
        have h3 : 16*D*Xf^(-(3/2:ℝ)) * x^(1/2:ℝ) = 16*D*Xf^(-(3/2:ℝ)) * Real.sqrt x := by
          rw [Real.sqrt_eq_rpow]
        calc ((m:ℝ)/x) * ((4*C₂*(Real.log x) + 8*(Real.log x) + 16*D*Xf^(-(3/2:ℝ))*(Real.log x)^4) * x)
            = (m:ℝ) * (4*C₂*(Real.log x) + 8*(Real.log x) + 16*D*Xf^(-(3/2:ℝ))*(Real.log x)^4) := by
              field_simp
          _ ≤ (m:ℝ) * ((4*C₂ + 8) * x^(1/8:ℝ) + 16*D*Xf^(-(3/2:ℝ)) * x^(1/2:ℝ)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ ≤ (m:ℝ) * ((4*C₂ + 8) * Real.sqrt x + 16*D*Xf^(-(3/2:ℝ)) * Real.sqrt x) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              linarith [h2, h3 ▸ le_refl (16*D*Xf^(-(3/2:ℝ))*x^(1/2:ℝ))]
          _ = ((m:ℝ)*(4*C₂ + 8) + 16*(m:ℝ)*D*Xf^(-(3/2:ℝ))) * Real.sqrt x := by ring
      have hG : ((m:ℝ)/x) * (G₀ * Xf) ≤ m * G₀ * Xf := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hxpos]
        have h2 : 0 ≤ (m:ℝ) * (G₀ * Xf) := by positivity
        calc (m:ℝ) * (G₀ * Xf) = (m:ℝ) * (G₀ * Xf) * 1 := by ring
          _ ≤ (m:ℝ) * (G₀ * Xf) * x := mul_le_mul_of_nonneg_left hx1 h2
          _ = (m:ℝ) * G₀ * Xf * x := by ring
      calc ((m:ℝ)/x) * ‖∫ t in (0:ℝ)..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * ggf t‖
          ≤ ((m:ℝ)/x) * (G₀ * Xf + ((8*Cfar*K*(Real.log x)^3/Tp * (x^2/2)
              + (4*C₂*(Real.log x) + 8*(Real.log x) + 16*D*Xf^(-(3/2:ℝ))*(Real.log x)^4) * x)
              + ‖∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * Sig t‖)) :=
            mul_le_mul_of_nonneg_left hIg (by positivity)
        _ = ((m:ℝ)/x) * (G₀ * Xf)
            + ((m:ℝ)/x) * (8*Cfar*K*(Real.log x)^3/Tp * (x^2/2))
            + ((m:ℝ)/x) * ((4*C₂*(Real.log x) + 8*(Real.log x) + 16*D*Xf^(-(3/2:ℝ))*(Real.log x)^4) * x)
            + ((m:ℝ)/x) * ‖∫ t in Xf..x, ((1-(t:ℂ)/(x:ℂ))^(m-1)) * Sig t‖ := by ring
        _ ≤ m * G₀ * Xf + 4*(m:ℝ)*Cfar*K*Real.sqrt x
            + ((m:ℝ)*(4*C₂ + 8) + 16*(m:ℝ)*D*Xf^(-(3/2:ℝ))) * Real.sqrt x
            + ((Nat.factorial m : ℝ)^2 * β * Real.sqrt x + 6 * (m:ℝ) * β * Xf^(3/2:ℝ)) := by
            linarith [hG, hAa2, hLl2, hSig_bnd]
        _ = _ := by ring
    have hXfm : Xf^(-(3/2:ℝ)) ≤ Xf^(-(1/2:ℝ)) := by
      rw [Real.rpow_neg (le_of_lt hXfpos), Real.rpow_neg (le_of_lt hXfpos)]
      exact (inv_le_inv₀ (Real.rpow_pos_of_pos hXfpos _) (Real.rpow_pos_of_pos hXfpos _)).mpr
        (Real.rpow_le_rpow_of_exponent_le hXf1 (by norm_num))
    have hXf3nn : 0 ≤ Xf^(3/2:ℝ) := le_of_lt (Real.rpow_pos_of_pos hXfpos _)
    have hKnn : 0 ≤ K := by linarith [hK1]
    have hmnn : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    have hfnn : (0:ℝ) ≤ (Nat.factorial m : ℝ) := Nat.cast_nonneg _
    have hsqx1 : (1:ℝ) ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx1
    have hGXf : m * G₀ * Xf ≤ m * G₀ * Xf * Real.sqrt x := by
      have h2 : 0 ≤ m * G₀ * Xf := mul_nonneg (mul_nonneg hmnn hG₀nn) (le_of_lt hXfpos)
      calc m * G₀ * Xf = m * G₀ * Xf * 1 := by ring
        _ ≤ m * G₀ * Xf * Real.sqrt x := mul_le_mul_of_nonneg_left hsqx1 h2
    have hA : 4*(m:ℝ)*Cfar*K*Real.sqrt x ≤ 8*(m:ℝ)*Xf*Cfar*K*Real.sqrt x := by
      have h4 : (4:ℝ) ≤ 8*Xf := by linarith
      have h2 : 0 ≤ (m:ℝ)*Cfar*K*Real.sqrt x := by positivity
      calc 4*(m:ℝ)*Cfar*K*Real.sqrt x = 4*((m:ℝ)*Cfar*K*Real.sqrt x) := by ring
        _ ≤ (8*Xf)*((m:ℝ)*Cfar*K*Real.sqrt x) := mul_le_mul_of_nonneg_right h4 h2
        _ = 8*(m:ℝ)*Xf*Cfar*K*Real.sqrt x := by ring
    have hB : (m:ℝ)*(4*C₂+8)*Real.sqrt x ≤ (m:ℝ)*Xf*(4*C₂+8)*Real.sqrt x := by
      have h2 : 0 ≤ (m:ℝ)*(4*C₂+8) := by positivity
      calc (m:ℝ)*(4*C₂+8)*Real.sqrt x = ((m:ℝ)*(4*C₂+8)) * Real.sqrt x := by ring
        _ ≤ ((m:ℝ)*(4*C₂+8)*Xf) * Real.sqrt x :=
            mul_le_mul_of_nonneg_right (by simpa using mul_le_mul_of_nonneg_left hXf1 h2)
              (Real.sqrt_nonneg x)
        _ = (m:ℝ)*Xf*(4*C₂+8)*Real.sqrt x := by ring
    have hCc : 16*(m:ℝ)*D*Xf^(-(3/2:ℝ))*Real.sqrt x ≤ 16*(m:ℝ)*D*Xf^(-(1/2:ℝ))*Real.sqrt x := by
      have h1 : 16*(m:ℝ)*D*Xf^(-(3/2:ℝ)) ≤ 16*(m:ℝ)*D*Xf^(-(1/2:ℝ)) :=
        mul_le_mul_of_nonneg_left hXfm (by positivity)
      exact mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg x)
    have hDd : 6*(m:ℝ)*β*Xf^(3/2:ℝ) ≤ 8*(m:ℝ)*β*Xf^(3/2:ℝ)*Real.sqrt x := by
      have h68 : 6*(m:ℝ)*β*Xf^(3/2:ℝ) ≤ 8*(m:ℝ)*β*Xf^(3/2:ℝ) := by
        have h6 : 0 ≤ (m:ℝ)*β*Xf^(3/2:ℝ) := by positivity
        linarith
      calc 6*(m:ℝ)*β*Xf^(3/2:ℝ) ≤ 8*(m:ℝ)*β*Xf^(3/2:ℝ) := h68
        _ = 8*(m:ℝ)*β*Xf^(3/2:ℝ) * 1 := by ring
        _ ≤ 8*(m:ℝ)*β*Xf^(3/2:ℝ) * Real.sqrt x :=
            mul_le_mul_of_nonneg_left hsqx1 (by positivity)
    rw [hCdef]
    have hexp : ((m:ℝ)*(4*C₂ + 8) + 16*(m:ℝ)*D*Xf^(-(3/2:ℝ))) * Real.sqrt x
        = (m:ℝ)*(4*C₂+8)*Real.sqrt x + 16*(m:ℝ)*D*Xf^(-(3/2:ℝ))*Real.sqrt x := by ring
    linarith [htotal, hGXf, hA, hB, hCc, hDd, hβnn, hfnn, hexp]
  exact hfinal

end Commons.NumberTheory.Zeta
