import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.Analysis.Asymptotics


open scoped BigOperators

private lemma log_bound_test (M : ℝ) (hM : 0 ≤ M) (N k : ℕ) :
    Real.log (2 * (2:ℝ)^(N+k) + 2*M + 1) ≤
      ((k:ℝ)+2) * Real.log (4 * (2:ℝ)^N + 2*M + 1) := by
  set X : ℝ := 4*(2:ℝ)^N + 2*M + 1 with hXdef
  set Y : ℝ := 2*(2:ℝ)^(N+k) + 2*M + 1 with hYdef
  have h2N : (0:ℝ) ≤ (2:ℝ)^N := by positivity
  have h2N1 : (1:ℝ) ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hXpos : 0 < X := by rw [hXdef]; positivity
  have hYpos : 0 < Y := by rw [hYdef]; positivity
  have hX4 : (4:ℝ) ≤ X := by rw [hXdef]; nlinarith [h2N1, hM]
  have hX2 : (2:ℝ) ≤ X := by linarith
  have h2Neq : (2:ℝ) * (2:ℝ)^N = (2:ℝ)^(1+N) := by
    rw [show (1:ℕ)+N = N+1 from by omega, pow_succ]; ring
  have h1 : 2 * (2:ℝ)^(N+k) = (2:ℝ)^k * (2*(2:ℝ)^N) := by
    have e1 : 2 * (2:ℝ)^(N+k) = (2:ℝ)^(1+(N+k)) := by
      rw [show (1:ℕ)+(N+k) = (N+k)+1 from by omega, pow_succ]; ring
    have e2 : (2:ℝ)^k * (2*(2:ℝ)^N) = (2:ℝ)^(k+(1+N)) := by
      rw [h2Neq, ← pow_add]
    rw [e1, e2]; congr 1; omega
  have h2N_le_X : 2*(2:ℝ)^N ≤ X := by rw [hXdef]; nlinarith [h2N, hM]
  have hM_le_X : 2*M+1 ≤ X := by rw [hXdef]; nlinarith [h2N]
  have hk0 : (0:ℝ) ≤ (2:ℝ)^k := by positivity
  have key1 : Y ≤ ((2:ℝ)^k + 1) * X := by
    rw [hYdef, h1]
    rw [show ((2:ℝ)^k + 1) * X = (2:ℝ)^k * X + X from by ring]
    have hstep := add_le_add (mul_le_mul_of_nonneg_left h2N_le_X hk0) hM_le_X
    linarith [hstep]
  have hk1 : (2:ℝ)^k + 1 ≤ (2:ℝ)^(k+1) := by
    have h1k : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
    rw [pow_succ]; nlinarith
  have key2 : ((2:ℝ)^k + 1) * X ≤ X^(k+2) := by
    calc ((2:ℝ)^k + 1) * X ≤ (2:ℝ)^(k+1) * X := mul_le_mul_of_nonneg_right hk1 hXpos.le
      _ ≤ X^(k+1) * X := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hX2 (k+1)) hXpos.le
      _ = X^(k+2) := by rw [← pow_succ]
  have hYle : Y ≤ X^(k+2) := le_trans key1 key2
  have hmain : Real.log Y ≤ ((k:ℝ)+2) * Real.log X := by
    calc Real.log Y ≤ Real.log (X^(k+2)) := Real.log_le_log hYpos hYle
      _ = ((k:ℝ)+2) * Real.log X := by rw [Real.log_pow]; push_cast; ring
  exact hmain

private lemma pointwise_test (A B M : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M) (N k : ℕ) :
    Real.sqrt ((A + B * Real.log (2 * (2:ℝ) ^ (N + k) + 2 * M + 1)) / (2:ℝ) ^ (N + k))
      ≤ Real.sqrt 2 * (Real.sqrt ((k:ℝ)+2) * (1/Real.sqrt 2)^k) *
          Real.sqrt ((A + B * Real.log (4 * (2:ℝ) ^ N + 2 * M + 1)) / (2 * (2:ℝ) ^ N)) := by
  set L : ℝ := Real.log (4*(2:ℝ)^N + 2*M+1) with hL
  set logW : ℝ := Real.log (2*(2:ℝ)^(N+k)+2*M+1) with hlogW
  set R : ℝ := (A + B*L)/(2*(2:ℝ)^N) with hR
  set q : ℝ := 1/Real.sqrt 2 with hq
  have hq2 : q^2 = 1/2 := by
    rw [hq, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hqpow : q^(2*k) = 1/(2:ℝ)^k := by
    rw [pow_mul, hq2, one_div, inv_pow, one_div]
  have hLnonneg : 0 ≤ L := by
    rw [hL]; apply Real.log_nonneg
    have : (1:ℝ) ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
    nlinarith [this, hM]
  have hPnonneg : 0 ≤ A + B*L := by
    have := mul_nonneg hB hLnonneg; linarith [hA, this]
  have hRnonneg : 0 ≤ R := by
    rw [hR]
    apply div_nonneg hPnonneg
    positivity
  have hlogW_le : logW ≤ ((k:ℝ)+2) * L := by
    rw [hlogW, hL]; exact log_bound_test M hM N k
  have hk2ge1 : (1:ℝ) ≤ ((k:ℝ)+2) := by
    have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  have hA2 : A ≤ ((k:ℝ)+2)*A := by
    calc A = 1*A := by ring
      _ ≤ ((k:ℝ)+2)*A := mul_le_mul_of_nonneg_right hk2ge1 hA
  have h1 : B*logW ≤ B*(((k:ℝ)+2)*L) := mul_le_mul_of_nonneg_left hlogW_le hB
  have hAB : A + B*logW ≤ ((k:ℝ)+2)*(A+B*L) := by
    have hsum : A + B*logW ≤ ((k:ℝ)+2)*A + B*(((k:ℝ)+2)*L) := add_le_add hA2 h1
    have heq : ((k:ℝ)+2)*A + B*(((k:ℝ)+2)*L) = ((k:ℝ)+2)*(A+B*L) := by ring
    rw [heq] at hsum; exact hsum
  have hT_le : (A + B*logW)/(2:ℝ)^(N+k) ≤ ((k:ℝ)+2)*(A+B*L)/(2:ℝ)^(N+k) :=
    div_le_div_of_nonneg_right hAB (by positivity)
  have hstep3 : ((k:ℝ)+2)*(A+B*L)/(2:ℝ)^(N+k) = 2*((k:ℝ)+2)*q^(2*k)*R := by
    rw [hR, hqpow]
    have h2Nk : (2:ℝ)^(N+k) = (2:ℝ)^N * (2:ℝ)^k := pow_add 2 N k
    rw [h2Nk]
    field_simp
  have hy2 : (Real.sqrt 2 * (Real.sqrt ((k:ℝ)+2) * q^k) * Real.sqrt R)^2
      = 2*((k:ℝ)+2)*q^(2*k)*R := by
    rw [mul_pow, mul_pow, mul_pow]
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ (k:ℝ)+2)]
    rw [Real.sq_sqrt hRnonneg]
    rw [← pow_mul, show k*2 = 2*k from by ring]
    ring
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [hy2]
  linarith [hT_le, hstep3]

private lemma summable_sqrt_mul_pow_test :
    Summable (fun k : ℕ => Real.sqrt ((k:ℝ)+2) * (1/Real.sqrt 2)^k) := by
  set q : ℝ := 1/Real.sqrt 2 with hq
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : q < 1 := by
    rw [hq, div_lt_iff₀ (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 2))]
    have h2 : (1:ℝ) < Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    simpa using h2
  have hqnorm : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1
  have hlin : Summable (fun k : ℕ => (k:ℝ) * q^k) := by
    have h := (summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hqnorm)
    have h2 := h.of_norm
    simpa using h2
  have hgeo : Summable (fun k : ℕ => q^k) := summable_geometric_of_lt_one hq0 hq1
  have hbig : Summable (fun k : ℕ => (k:ℝ)*q^k + 2*q^k) := hlin.add (hgeo.mul_left 2)
  apply Summable.of_nonneg_of_le _ _ hbig
  · intro k; exact mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hq0 k)
  · intro k
    have hqk : 0 ≤ q^k := pow_nonneg hq0 k
    have hs : Real.sqrt ((k:ℝ)+2) ≤ ((k:ℝ)+2) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have hk2 : (1:ℝ) ≤ (k:ℝ)+2 := by
        have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        linarith
      nlinarith
    calc Real.sqrt ((k:ℝ)+2) * q^k ≤ ((k:ℝ)+2) * q^k := mul_le_mul_of_nonneg_right hs hqk
      _ = (k:ℝ)*q^k + 2*q^k := by ring

theorem tsum_sqrt_log_div_pow_le (A B M : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      (∑' k : ℕ, Real.sqrt ((A + B * Real.log (2 * (2:ℝ) ^ (N + k) + 2 * M + 1)) / (2:ℝ) ^ (N + k)))
        ≤ C * Real.sqrt ((A + B * Real.log (4 * (2:ℝ) ^ N + 2 * M + 1)) / (2 * (2:ℝ) ^ N)) := by
  have hq0 : 0 ≤ (1/Real.sqrt 2 : ℝ) := by positivity
  have hgsumm := summable_sqrt_mul_pow_test
  have hgnonneg : ∀ k : ℕ, 0 ≤ Real.sqrt ((k:ℝ)+2) * (1/Real.sqrt 2)^k :=
    fun k => mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hq0 k)
  refine ⟨Real.sqrt 2 * (∑' k : ℕ, Real.sqrt ((k:ℝ)+2) * (1/Real.sqrt 2)^k) + 1, ?_, ?_⟩
  · have hT : 0 ≤ ∑' k : ℕ, Real.sqrt ((k:ℝ)+2) * (1/Real.sqrt 2)^k := tsum_nonneg hgnonneg
    have : 0 ≤ Real.sqrt 2 * (∑' k : ℕ, Real.sqrt ((k:ℝ)+2) * (1/Real.sqrt 2)^k) :=
      mul_nonneg (Real.sqrt_nonneg 2) hT
    nlinarith [this]
  · intro N
    set L : ℝ := Real.log (4 * (2:ℝ) ^ N + 2 * M + 1) with hL
    set R : ℝ := (A + B * L) / (2 * (2:ℝ) ^ N) with hR
    have hLnn : 0 ≤ L := by
      rw [hL]; apply Real.log_nonneg
      have h1 : (1:ℝ) ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
      nlinarith [h1, hM]
    have hRnn : 0 ≤ R := by
      rw [hR]; apply div_nonneg
      · nlinarith [hA, mul_nonneg hB hLnn]
      · positivity
    have hpt : ∀ k : ℕ,
        Real.sqrt ((A + B * Real.log (2 * (2:ℝ) ^ (N + k) + 2 * M + 1)) / (2:ℝ) ^ (N + k))
          ≤ Real.sqrt 2 * (Real.sqrt ((k:ℝ)+2) * (1/Real.sqrt 2)^k) * Real.sqrt R := by
      intro k
      rw [hR, hL]
      exact pointwise_test A B M hA hB hM N k
    have hsummRHS : Summable (fun k : ℕ =>
        Real.sqrt 2 * (Real.sqrt ((k:ℝ)+2) * (1/Real.sqrt 2)^k) * Real.sqrt R) := by
      have h2 := hgsumm.mul_left (Real.sqrt 2)
      have h3 := h2.mul_right (Real.sqrt R)
      exact h3
    have hsummterm : Summable (fun k : ℕ =>
        Real.sqrt ((A + B * Real.log (2 * (2:ℝ) ^ (N + k) + 2 * M + 1)) / (2:ℝ) ^ (N + k))) := by
      apply Summable.of_nonneg_of_le _ _ hsummRHS
      · intro k; exact Real.sqrt_nonneg _
      · intro k; exact hpt k
    have hle := Summable.tsum_le_tsum hpt hsummterm hsummRHS
    have hval : (∑' k : ℕ, Real.sqrt 2 * (Real.sqrt ((k:ℝ)+2) * (1/Real.sqrt 2)^k) * Real.sqrt R)
        = Real.sqrt 2 * (∑' k : ℕ, Real.sqrt ((k:ℝ)+2) * (1/Real.sqrt 2)^k) * Real.sqrt R := by
      rw [tsum_mul_right, tsum_mul_left]
    have hfinal :
        Real.sqrt 2 * (∑' k : ℕ, Real.sqrt ((k:ℝ)+2) * (1/Real.sqrt 2)^k) * Real.sqrt R
        ≤ (Real.sqrt 2 * (∑' k : ℕ, Real.sqrt ((k:ℝ)+2) * (1/Real.sqrt 2)^k) + 1) * Real.sqrt R := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg R)
      linarith
    calc (∑' k : ℕ, Real.sqrt ((A + B * Real.log (2 * (2:ℝ) ^ (N + k) + 2 * M + 1)) / (2:ℝ) ^ (N + k)))
        ≤ (∑' k : ℕ, Real.sqrt 2 * (Real.sqrt ((k:ℝ)+2) * (1/Real.sqrt 2)^k) * Real.sqrt R) := hle
      _ = Real.sqrt 2 * (∑' k : ℕ, Real.sqrt ((k:ℝ)+2) * (1/Real.sqrt 2)^k) * Real.sqrt R := hval
      _ ≤ (Real.sqrt 2 * (∑' k : ℕ, Real.sqrt ((k:ℝ)+2) * (1/Real.sqrt 2)^k) + 1) * Real.sqrt R := hfinal

end Commons.Analysis.Asymptotics