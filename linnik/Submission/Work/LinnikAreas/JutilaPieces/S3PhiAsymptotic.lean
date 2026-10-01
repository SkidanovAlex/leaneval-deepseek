import Mathlib
import Submission.Work.LinnikAreas.JutilaPieces.S3MainTermDefs
import Submission.Work.LinnikAreas.Density4.mkl_assembly
import Submission.Work.LinnikAreas.Density4.BzHard.mertens_log_weighted_one
import Submission.Commons.NumberTheory.Moebius.moebius_recip_sum_exp_decay
import Submission.Work.LinnikAreas.sum_card_divisors_div_le
import Submission.Work.LinnikAreas.JutilaPieces.KappaLogSumReductionReal
import Submission.Work.LinnikAreas.JutilaPieces.KappaPlainBound
import Submission.Work.LinnikAreas.JutilaPieces.KappaErrPowSelf

namespace Work.LinnikAreas.JutilaPieces

open Finset

noncomputable section

/-! ## Elementary facts about `s3w` -/

/-- `s3w n · ∏_{p | n} (1 + 1/p) = μ(n)/n`. -/
lemma s3w_mul_prod_one_add_inv (n : ℕ) :
    s3w n * ∏ p ∈ n.primeFactors, (1 + 1/(p:ℝ)) = (ArithmeticFunction.moebius n : ℝ)/(n:ℝ) := by
  have hprod : (∏ p ∈ n.primeFactors, (p:ℝ)/((p:ℝ)+1))
      * (∏ p ∈ n.primeFactors, (1 + 1/(p:ℝ))) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    have hp0 : (p:ℝ) ≠ 0 := by
      have := (Nat.mem_primeFactors.mp hp).1
      have h : (0:ℝ) < (p:ℝ) := by exact_mod_cast this.pos
      exact ne_of_gt h
    have hp1 : ((p:ℝ)+1) ≠ 0 := by positivity
    field_simp
  rw [s3w]
  have hkey : (ArithmeticFunction.moebius n : ℝ) * (∏ p ∈ n.primeFactors, (p:ℝ)/((p:ℝ)+1)) / (n:ℝ)
      * (∏ p ∈ n.primeFactors, (1 + 1/(p:ℝ)))
      = (ArithmeticFunction.moebius n : ℝ)
        * ((∏ p ∈ n.primeFactors, (p:ℝ)/((p:ℝ)+1))
          * (∏ p ∈ n.primeFactors, (1 + 1/(p:ℝ)))) / (n:ℝ) := by ring
  rw [hkey, hprod, mul_one]

/-- `|s3w n| ≤ 1/n`. -/
lemma abs_s3w_le_inv (n : ℕ) : |s3w n| ≤ 1/(n:ℝ) := by
  have hprod_nn : 0 ≤ ∏ p ∈ n.primeFactors, (p:ℝ)/((p:ℝ)+1) :=
    Finset.prod_nonneg (fun p hp => by positivity)
  have hprod_le : |∏ p ∈ n.primeFactors, (p:ℝ)/((p:ℝ)+1)| ≤ 1 := by
    rw [abs_of_nonneg hprod_nn]
    apply Finset.prod_le_one₀
    · intro p hp; positivity
    · intro p hp
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) p]
  have hmu : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 :=
    Commons.NumberTheory.Moebius.moebius_abs_le_one n
  have hnabs : |(n:ℝ)| = (n:ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
  rw [s3w, abs_div, abs_mul, hnabs]
  calc |(ArithmeticFunction.moebius n : ℝ)| * |∏ p ∈ n.primeFactors, (p:ℝ)/((p:ℝ)+1)| / (n:ℝ)
      ≤ 1 * 1 / (n:ℝ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
        exact mul_le_mul hmu hprod_le (abs_nonneg _) (by norm_num)
    _ = 1/(n:ℝ) := by ring

/-- `σ_{-1/2}(n) ≤ τ(n)`. -/
lemma sHalf_le_card_divisors (n : ℕ) :
    Work.LinnikAreas.Density4.sHalf n ≤ ((Nat.divisors n).card : ℝ) := by
  rw [Work.LinnikAreas.Density4.sHalf]
  have hcard : ((Nat.divisors n).card : ℝ) = ∑ d ∈ Nat.divisors n, (1:ℝ) := by
    rw [Finset.card_eq_sum_ones]; push_cast; ring
  rw [hcard]
  apply Finset.sum_le_sum
  intro d hd
  have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd)
    (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2)
  have hd1R : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd1
  rw [div_le_one (Real.sqrt_pos_of_pos (by linarith))]
  calc (1:ℝ) = Real.sqrt 1 := by rw [Real.sqrt_one]
    _ ≤ Real.sqrt (d:ℝ) := Real.sqrt_le_sqrt hd1R

/-- `Σ_{k ≤ X} 1/k ≤ 1 + log (2 + X)`. -/
lemma sum_Icc_inv_le_log (X : ℕ) :
    (∑ m ∈ Finset.Icc 1 X, (1:ℝ)/(m:ℝ)) ≤ 1 + Real.log (2 + (X:ℝ)) := by
  rcases Nat.eq_zero_or_pos X with hX | hX
  · subst hX
    have h0 : (Finset.Icc 1 0 : Finset ℕ) = ∅ := Finset.Icc_eq_empty (by norm_num)
    rw [h0, Finset.sum_empty, Nat.cast_zero, add_zero]
    have : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  · have h1 : (∑ m ∈ Finset.Icc 1 X, (1:ℝ)/(m:ℝ)) = (harmonic X : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      apply Finset.sum_congr rfl
      intro m hm
      rw [one_div]
    rw [h1]
    refine (harmonic_le_one_add_log X).trans ?_
    have hXpos : (0:ℝ) < (X:ℝ) := by exact_mod_cast hX
    have hle : Real.log (X:ℝ) ≤ Real.log (2 + (X:ℝ)) :=
      Real.log_le_log hXpos (by linarith [Nat.cast_nonneg (α := ℝ) X])
    linarith

/-- `Σ_{n ≤ X} σ_{-1/2}(n)·|s3w n| ≤ (1 + log (2+X))²`. -/
lemma sum_sHalf_abs_s3w_le (X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, Work.LinnikAreas.Density4.sHalf n * |s3w n|
      ≤ (1 + Real.log (2 + (X:ℝ)))^2 := by
  have h1 : ∀ n ∈ Finset.Icc 1 X,
      Work.LinnikAreas.Density4.sHalf n * |s3w n| ≤ ((Nat.divisors n).card : ℝ)/(n:ℝ) := by
    intro n hn
    obtain ⟨hn1, -⟩ := Finset.mem_Icc.mp hn
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
    calc Work.LinnikAreas.Density4.sHalf n * |s3w n|
        ≤ ((Nat.divisors n).card : ℝ) * (1/(n:ℝ)) :=
          mul_le_mul (sHalf_le_card_divisors n) (abs_s3w_le_inv n) (abs_nonneg _) (by positivity)
      _ = ((Nat.divisors n).card : ℝ)/(n:ℝ) := by ring
  have h2 : (∑ n ∈ Finset.Icc 1 X, ((Nat.divisors n).card : ℝ)/(n:ℝ))
      ≤ (∑ m ∈ Finset.Icc 1 X, (1:ℝ)/(m:ℝ))^2 := Work.LinnikAreas.sum_card_divisors_div_le X
  have h3 := sum_Icc_inv_le_log X
  have hnn : (0:ℝ) ≤ ∑ m ∈ Finset.Icc 1 X, (1:ℝ)/(m:ℝ) :=
    Finset.sum_nonneg (fun m hm => by positivity)
  have h4 : (0:ℝ) ≤ 1 + Real.log (2 + (X:ℝ)) := by
    have : 0 ≤ Real.log (2 + (X:ℝ)) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) X])
    linarith
  calc ∑ n ∈ Finset.Icc 1 X, Work.LinnikAreas.Density4.sHalf n * |s3w n|
      ≤ ∑ n ∈ Finset.Icc 1 X, ((Nat.divisors n).card : ℝ)/(n:ℝ) := Finset.sum_le_sum h1
    _ ≤ (∑ m ∈ Finset.Icc 1 X, (1:ℝ)/(m:ℝ))^2 := h2
    _ ≤ (1 + Real.log (2 + (X:ℝ)))^2 := by
        apply sq_le_sq' <;> linarith

/-! ## `exp (-c√log)` is dominated by every negative power of `log` -/

lemma exp_neg_sqrtlog_le_logpow (c B : ℝ) (hc : 0 < c) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 2 ≤ X →
      Real.exp (-(c * Real.sqrt (Real.log X))) ≤ C * (Real.log X) ^ (-B) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2*B ≤ (N:ℝ) := ⟨⌈2*B⌉₊, Nat.le_ceil (2*B)⟩
  have hNfact : 0 < (N.factorial : ℝ) := by exact_mod_cast N.factorial_pos
  have hcN : 0 < c^N := pow_pos hc N
  refine ⟨max 1 ((N.factorial:ℝ)/c^N), lt_max_of_lt_left one_pos, fun X hX => ?_⟩
  have hxpos : 0 < X := by linarith
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith)
  set u : ℝ := Real.sqrt (Real.log X) with hu
  have hupos : 0 < u := Real.sqrt_pos.mpr hlogpos
  have hfact := Real.pow_div_factorial_le_exp (c*u) (by positivity) N
  have hcu : 0 < c*u := by positivity
  have hexp_le : Real.exp (-(c*u)) ≤ (N.factorial:ℝ)/((c*u)^N) := by
    calc Real.exp (-(c*u)) = (1:ℝ)/(Real.exp (c*u)) := by rw [one_div, Real.exp_neg]
      _ ≤ (1:ℝ)/((c*u)^N/(N.factorial:ℝ)) :=
          one_div_le_one_div_of_le (by positivity) hfact
      _ = (N.factorial:ℝ)/((c*u)^N) := by rw [one_div_div]
  have huN : u^N = (Real.log X) ^ ((N:ℝ)/2) := by
    rw [hu, Real.sqrt_eq_rpow, ← Real.rpow_natCast ((Real.log X)^(1/2)) N,
      ← Real.rpow_mul hlogpos.le]
    congr 1
    ring
  rw [mul_pow, huN] at hexp_le
  by_cases h1 : (1:ℝ) ≤ Real.log X
  · have hexp2 : (Real.log X) ^ B ≤ (Real.log X) ^ ((N:ℝ)/2) := by
      apply Real.rpow_le_rpow_of_exponent_le h1
      linarith
    have hp1 : 0 < (Real.log X) ^ ((N:ℝ)/2) := Real.rpow_pos_of_pos hlogpos _
    have hp2 : 0 < (Real.log X) ^ B := Real.rpow_pos_of_pos hlogpos _
    calc Real.exp (-(c*u)) ≤ (N.factorial:ℝ)/(c^N * (Real.log X)^((N:ℝ)/2)) := hexp_le
      _ = (N.factorial:ℝ)/c^N * ((Real.log X)^((N:ℝ)/2))⁻¹ := by ring
      _ ≤ (N.factorial:ℝ)/c^N * ((Real.log X)^B)⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ (div_nonneg hNfact.le hcN.le)
          simpa only [one_div] using one_div_le_one_div_of_le hp2 hexp2
      _ = (N.factorial:ℝ)/c^N * (Real.log X)^(-B) := by rw [Real.rpow_neg hlogpos.le]
      _ ≤ max 1 ((N.factorial:ℝ)/c^N) * (Real.log X)^(-B) := by
          apply mul_le_mul_of_nonneg_right (le_max_right _ _)
          exact Real.rpow_nonneg hlogpos.le _
  · push_neg at h1
    have hexp2 : Real.exp (-(c*u)) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have : 0 ≤ c*u := le_of_lt hcu
      linarith
    have hpB : 0 < (Real.log X)^B := Real.rpow_pos_of_pos hlogpos _
    have hB1 : (Real.log X)^B ≤ 1 := by
      have := Real.rpow_le_rpow hlogpos.le h1.le hB.le
      rwa [Real.one_rpow] at this
    have hge1 : (1:ℝ) ≤ (Real.log X)^(-B) := by
      have hmul := mul_le_mul_of_nonneg_right hB1 (le_of_lt (inv_pos.mpr hpB))
      rw [mul_inv_cancel₀ (ne_of_gt hpB), one_mul] at hmul
      rwa [Real.rpow_neg hlogpos.le]
    calc Real.exp (-(c*u)) ≤ 1 := hexp2
      _ ≤ (Real.log X)^(-B) := hge1
      _ ≤ max 1 ((N.factorial:ℝ)/c^N) * (Real.log X)^(-B) := by
          have := mul_le_mul_of_nonneg_right (le_max_left (1:ℝ) ((N.factorial:ℝ)/c^N))
            (Real.rpow_nonneg hlogpos.le (-B))
          simpa using this

/-! ## The double sum and its decomposition -/

/-- The double sum of `s3Phi`, cleared of the factor `(π²/6)⁻¹`. -/
def s3D (x : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 ⌊x⌋₊, ∑ t ∈ Finset.Icc 1 ⌊x⌋₊,
    (if Nat.Coprime r t then
      s3w r * s3w t * ((Real.log (x/(r:ℝ)) - 1) * (Real.log (x/(t:ℝ)) - 1) + 1) else 0)

/-- `(π²/6)·∏_{p|t}(1+1/p)`, the main term of the sharp `κ`-Mertens estimate. -/
def s3Main (t : ℕ) : ℝ := (Real.pi^2/6) * ∏ p ∈ t.primeFactors, (1 + 1/(p:ℝ))

/-- `Σ_{t ≤ ⌊x⌋} μ(t)/t · (log (x/t) - 1)`, the Mertens-type main term. -/
def s3M (x : ℝ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 ⌊x⌋₊,
    (ArithmeticFunction.moebius t : ℝ)/(t:ℝ) * (Real.log (x/(t:ℝ)) - 1)

/-- `Σ_{r ≤ ⌊x⌋, (r,t)=1} s3w r · (log (x/r) - 1)`. -/
def s3KA (x : ℝ) (t : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun r => Nat.Coprime r t),
    s3w r * (Real.log (x/(r:ℝ)) - 1)

/-- `Σ_{r ≤ ⌊x⌋, (r,t)=1} s3w r`. -/
def s3KB (x : ℝ) (t : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun r => Nat.Coprime r t), s3w r

/-- `s3w n = μ(n)/(n·∏_{p|n}(1+1/p))`, the form in which the `κ`-Mertens estimates are stated. -/
lemma s3w_eq (n : ℕ) (hn : 1 ≤ n) :
    s3w n = (ArithmeticFunction.moebius n : ℝ)
      / ((n:ℝ) * ∏ p ∈ n.primeFactors, (1 + 1/(p:ℝ))) := by
  have hnne : ((n:ℝ)) ≠ 0 := by
    have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    exact ne_of_gt this
  have hPne : (∏ p ∈ n.primeFactors, (1 + 1/(p:ℝ))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    have hp' := (Nat.mem_primeFactors.mp hp).1
    have : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp'.pos
    positivity
  have h := s3w_mul_prod_one_add_inv n
  rw [eq_div_iff (mul_ne_zero hnne hPne)]
  have h2 : s3w n * ((n:ℝ) * ∏ p ∈ n.primeFactors, (1 + 1/(p:ℝ)))
      = (s3w n * (∏ p ∈ n.primeFactors, (1 + 1/(p:ℝ)))) * (n:ℝ) := by ring
  rw [h2, h]
  field_simp

lemma s3KA_add_s3KB (x : ℝ) (t : ℕ) : s3KA x t + s3KB x t
    = ∑ r ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun r => Nat.Coprime r t), s3w r * Real.log (x/(r:ℝ)) := by
  unfold s3KA s3KB
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  ring

lemma pi_div_six_ne_zero : (Real.pi^2/6 : ℝ) ≠ 0 := by
  have h : (0:ℝ) < Real.pi := Real.pi_pos
  positivity

lemma s3Phi_mul (x : ℝ) : Real.pi^2/6 * s3Phi x = s3D x := by
  unfold s3Phi s3D
  rw [← mul_assoc, mul_inv_cancel₀ pi_div_six_ne_zero, one_mul]

lemma s3D_eq_terms (x : ℝ) :
    s3D x = ∑ t ∈ Finset.Icc 1 ⌊x⌋₊,
      s3w t * ((Real.log (x/(t:ℝ)) - 1) * s3KA x t + s3KB x t) := by
  unfold s3D s3KA s3KB
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Finset.sum_filter]
  have h1 : s3w t * ((Real.log (x/(t:ℝ)) - 1)
        * (∑ r ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun r => Nat.Coprime r t),
            s3w r * (Real.log (x/(r:ℝ)) - 1))
        + (∑ r ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun r => Nat.Coprime r t), s3w r))
      = s3w t * (∑ r ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun r => Nat.Coprime r t),
          ((Real.log (x/(t:ℝ)) - 1) * (s3w r * (Real.log (x/(r:ℝ)) - 1)) + s3w r)) := by
    congr 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-! ## The main estimate -/

/-- `|log (x/t) - 1| ≤ 3 log x` for `1 ≤ t ≤ ⌊x⌋`. -/
lemma abs_log_div_sub_one_le (x : ℝ) (hx : 2 ≤ x) (t : ℕ)
    (ht : t ∈ Finset.Icc 1 ⌊x⌋₊) : |Real.log (x/(t:ℝ)) - 1| ≤ 3 * Real.log x := by
  obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.mp ht
  have htpos : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht1
  have hxpos : 0 < x := by linarith
  have htle : (t:ℝ) ≤ x := le_trans (by exact_mod_cast ht2) (Nat.floor_le (by linarith))
  have hlog_split : Real.log (x/(t:ℝ)) = Real.log x - Real.log (t:ℝ) :=
    Real.log_div (ne_of_gt hxpos) (ne_of_gt htpos)
  have htge : 0 ≤ Real.log (t:ℝ) := Real.log_nonneg (by exact_mod_cast ht1)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have htl : Real.log (t:ℝ) ≤ Real.log x := Real.log_le_log htpos htle
  have hlog2 : (2:ℝ)/3 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogx23 : (2:ℝ)/3 < Real.log x := lt_of_lt_of_le hlog2 (Real.log_le_log (by norm_num) hx)
  rw [abs_le]
  constructor
  · rw [hlog_split]; linarith
  · rw [hlog_split]; linarith

/-- `|2 - log (x/t)| ≤ 4 log x` for `1 ≤ t ≤ ⌊x⌋`. -/
lemma abs_two_sub_log_div_le (x : ℝ) (hx : 2 ≤ x) (t : ℕ)
    (ht : t ∈ Finset.Icc 1 ⌊x⌋₊) : |2 - Real.log (x/(t:ℝ))| ≤ 4 * Real.log x := by
  obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.mp ht
  have htpos : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht1
  have hxpos : 0 < x := by linarith
  have htle : (t:ℝ) ≤ x := le_trans (by exact_mod_cast ht2) (Nat.floor_le (by linarith))
  have hlog_split : Real.log (x/(t:ℝ)) = Real.log x - Real.log (t:ℝ) :=
    Real.log_div (ne_of_gt hxpos) (ne_of_gt htpos)
  have htge : 0 ≤ Real.log (t:ℝ) := Real.log_nonneg (by exact_mod_cast ht1)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have htl : Real.log (t:ℝ) ≤ Real.log x := Real.log_le_log htpos htle
  have hlog2 : (2:ℝ)/3 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogx23 : (2:ℝ)/3 < Real.log x := lt_of_lt_of_le hlog2 (Real.log_le_log (by norm_num) hx)
  rw [abs_le]
  constructor
  · rw [hlog_split]; linarith
  · rw [hlog_split]; linarith

/-- **The main estimate**, given the sharp `κ`-Mertens bound `hsharp` and the plain bound
`hplain` (both with exponent `6`). -/
theorem s3Phi_main (K1 K2 : ℝ) (hK1 : 0 < K1) (hK2 : 0 < K2)
    (hsharp : ∀ (Q : ℝ) (t : ℕ), 2 ≤ Q → 1 ≤ t →
      |(∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t),
          s3w n * Real.log (Q/(n:ℝ))) - s3Main t|
        ≤ K1 * Work.LinnikAreas.Density4.sHalf t * (Real.log (2 + Q))^(-6:ℝ))
    (hplain : ∀ (Q : ℝ) (t : ℕ), 2 ≤ Q → 1 ≤ t →
      |∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t), s3w n|
        ≤ K2 * Work.LinnikAreas.Density4.sHalf t * (Real.log (2 + Q))^(-6:ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → |s3Phi x - 1| ≤ C / (Real.log x)^2 := by
  obtain ⟨Cm, hCm, hmert⟩ := Work.LinnikAreas.Density4.BzHard.mertens_log_weighted_one
  obtain ⟨cd, Cd, hcd, hCd, hdec⟩ := Commons.NumberTheory.Moebius.moebius_recip_sum_exp_decay
  obtain ⟨Ce, hCe, hexp⟩ := exp_neg_sqrtlog_le_logpow cd 2 hcd (by norm_num)
  refine ⟨80*(K1+K2)/Real.log 2 + 4*(Cm + Real.log 2 * (Cd*Ce)) + 1, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hfl2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hfl1 : 1 ≤ ⌊x⌋₊ := by omega
  have hflpos : (0:ℝ) < (⌊x⌋₊:ℝ) := by exact_mod_cast hfl1
  have hlogfl : 0 < Real.log (⌊x⌋₊:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < ⌊x⌋₊))
  have hlogle : Real.log x ≤ 2 * Real.log (⌊x⌋₊:ℝ) := by
    have h1 : x < (⌊x⌋₊:ℝ) + 1 := Nat.lt_floor_add_one x
    have h2 : (1:ℝ) ≤ (⌊x⌋₊:ℝ) := by exact_mod_cast hfl1
    have h3 : x ≤ 2 * (⌊x⌋₊:ℝ) := by linarith
    have h4 := Real.log_le_log hx0 h3
    rw [Real.log_mul (by norm_num) (ne_of_gt hflpos)] at h4
    have h5 : Real.log 2 ≤ Real.log (⌊x⌋₊:ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hfl2)
    linarith
  have hsH : ∀ t : ℕ, 0 ≤ Work.LinnikAreas.Density4.sHalf t :=
    fun t => Work.LinnikAreas.Density4.sHalf_nonneg t
  have hM1 : |s3M x - 1| ≤ 4*(Cm + Real.log 2 * (Cd*Ce)) / (Real.log x)^2 := by
    have hsplit : s3M x
        = (∑ t ∈ Finset.Icc 1 ⌊x⌋₊,
              (ArithmeticFunction.moebius t:ℝ)/(t:ℝ)*(Real.log ((⌊x⌋₊:ℝ)/(t:ℝ))-1))
          + Real.log (x/(⌊x⌋₊:ℝ)) * (∑ t ∈ Finset.Icc 1 ⌊x⌋₊,
              (ArithmeticFunction.moebius t:ℝ)/(t:ℝ)) := by
      rw [s3M, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      have htne : (t:ℝ) ≠ 0 := by
        have : 1 ≤ t := (Finset.mem_Icc.mp ht).1
        positivity
      have hxne : x ≠ 0 := ne_of_gt hx0
      have hXne : (⌊x⌋₊:ℝ) ≠ 0 := ne_of_gt hflpos
      have hlog : Real.log (x/(t:ℝ)) = Real.log ((⌊x⌋₊:ℝ)/(t:ℝ)) + Real.log (x/(⌊x⌋₊:ℝ)) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        field_simp
      rw [hlog]; ring
    rw [hsplit]
    have hm1 : |(∑ t ∈ Finset.Icc 1 ⌊x⌋₊,
          (ArithmeticFunction.moebius t:ℝ)/(t:ℝ)*(Real.log ((⌊x⌋₊:ℝ)/(t:ℝ))-1)) - 1|
        ≤ Cm / (Real.log (⌊x⌋₊:ℝ))^2 := by
      have h := hmert ⌊x⌋₊ hfl2
      have hsum_eq : (∑ t ∈ Finset.Icc 1 ⌊x⌋₊,
            (ArithmeticFunction.moebius t:ℝ)/(t:ℝ)*(Real.log ((⌊x⌋₊:ℝ)/(t:ℝ))-1))
          = ∑ t ∈ Finset.Icc 1 ⌊x⌋₊,
            (ArithmeticFunction.moebius t:ℝ)*(Real.log (⌊x⌋₊:ℝ) - Real.log (t:ℝ) - 1)/(t:ℝ) := by
        apply Finset.sum_congr rfl
        intro t ht
        have htne : (t:ℝ) ≠ 0 := by
          have : 1 ≤ t := (Finset.mem_Icc.mp ht).1
          positivity
        rw [Real.log_div (ne_of_gt hflpos) htne]
        ring
      rw [hsum_eq]; exact h
    have hm0 : |Real.log (x/(⌊x⌋₊:ℝ)) * (∑ t ∈ Finset.Icc 1 ⌊x⌋₊,
          (ArithmeticFunction.moebius t:ℝ)/(t:ℝ))| ≤ Real.log 2 * (Cd*Ce)/(Real.log (⌊x⌋₊:ℝ))^2 := by
      have hdec' := hdec (⌊x⌋₊:ℝ) (by exact_mod_cast hfl2)
      rw [Nat.floor_natCast] at hdec'
      have hexp' := hexp (⌊x⌋₊:ℝ) (by exact_mod_cast hfl2)
      rw [abs_mul]
      have hlogle2 : |Real.log (x/(⌊x⌋₊:ℝ))| ≤ Real.log 2 := by
        have h1 : (1:ℝ) ≤ x/(⌊x⌋₊:ℝ) := by
          rw [le_div_iff₀ hflpos, one_mul]
          exact Nat.floor_le hx0.le
        have h2 : x/(⌊x⌋₊:ℝ) ≤ 2 := by
          rw [div_le_iff₀ hflpos]
          have h1' : x < (⌊x⌋₊:ℝ) + 1 := Nat.lt_floor_add_one x
          have h2' : (1:ℝ) ≤ (⌊x⌋₊:ℝ) := by exact_mod_cast hfl1
          linarith
        rw [abs_of_nonneg (Real.log_nonneg h1)]
        exact Real.log_le_log (by positivity) h2
      calc |Real.log (x/(⌊x⌋₊:ℝ))| * |(∑ t ∈ Finset.Icc 1 ⌊x⌋₊,
            (ArithmeticFunction.moebius t:ℝ)/(t:ℝ))|
          ≤ Real.log 2 * (Cd * Real.exp (-(cd * Real.sqrt (Real.log (⌊x⌋₊:ℝ))))) :=
            mul_le_mul hlogle2 hdec' (abs_nonneg _) (Real.log_nonneg (by norm_num))
        _ ≤ Real.log 2 * (Cd * (Ce * (Real.log (⌊x⌋₊:ℝ))^(-2:ℝ))) := by
            have h := mul_le_mul_of_nonneg_left hexp' hCd.le
            exact mul_le_mul_of_nonneg_left h (Real.log_nonneg (by norm_num))
        _ = Real.log 2 * (Cd*Ce)/(Real.log (⌊x⌋₊:ℝ))^2 := by
            rw [Real.rpow_neg hlogfl.le, Real.rpow_two]
            ring
    have hcomb : |(∑ t ∈ Finset.Icc 1 ⌊x⌋₊,
          (ArithmeticFunction.moebius t:ℝ)/(t:ℝ)*(Real.log ((⌊x⌋₊:ℝ)/(t:ℝ))-1))
          + Real.log (x/(⌊x⌋₊:ℝ)) * (∑ t ∈ Finset.Icc 1 ⌊x⌋₊,
              (ArithmeticFunction.moebius t:ℝ)/(t:ℝ)) - 1|
        ≤ Cm/(Real.log (⌊x⌋₊:ℝ))^2 + Real.log 2 * (Cd*Ce)/(Real.log (⌊x⌋₊:ℝ))^2 := by
      have heq : (∑ t ∈ Finset.Icc 1 ⌊x⌋₊,
            (ArithmeticFunction.moebius t:ℝ)/(t:ℝ)*(Real.log ((⌊x⌋₊:ℝ)/(t:ℝ))-1))
          + Real.log (x/(⌊x⌋₊:ℝ)) * (∑ t ∈ Finset.Icc 1 ⌊x⌋₊,
              (ArithmeticFunction.moebius t:ℝ)/(t:ℝ)) - 1
          = ((∑ t ∈ Finset.Icc 1 ⌊x⌋₊,
              (ArithmeticFunction.moebius t:ℝ)/(t:ℝ)*(Real.log ((⌊x⌋₊:ℝ)/(t:ℝ))-1)) - 1)
            + Real.log (x/(⌊x⌋₊:ℝ)) * (∑ t ∈ Finset.Icc 1 ⌊x⌋₊,
              (ArithmeticFunction.moebius t:ℝ)/(t:ℝ)) := by ring
      rw [heq]
      exact (abs_add_le _ _).trans (add_le_add hm1 hm0)
    have hfin : Cm/(Real.log (⌊x⌋₊:ℝ))^2 + Real.log 2 * (Cd*Ce)/(Real.log (⌊x⌋₊:ℝ))^2
        ≤ 4*(Cm + Real.log 2 * (Cd*Ce)) / (Real.log x)^2 := by
      have hCnn : 0 ≤ Cm + Real.log 2 * (Cd*Ce) := by
        have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        positivity
      have hkey : 1/(Real.log (⌊x⌋₊:ℝ))^2 ≤ 4/(Real.log x)^2 := by
        rw [div_le_div_iff₀ (pow_pos hlogfl 2) (pow_pos hlogx 2)]
        nlinarith [hlogle, hlogx, hlogfl]
      have hrew : Cm/(Real.log (⌊x⌋₊:ℝ))^2 + Real.log 2 * (Cd*Ce)/(Real.log (⌊x⌋₊:ℝ))^2
          = (Cm + Real.log 2 * (Cd*Ce)) * (1/(Real.log (⌊x⌋₊:ℝ))^2) := by ring
      rw [hrew]
      calc (Cm + Real.log 2 * (Cd*Ce)) * (1/(Real.log (⌊x⌋₊:ℝ))^2)
          ≤ (Cm + Real.log 2 * (Cd*Ce)) * (4/(Real.log x)^2) :=
            mul_le_mul_of_nonneg_left hkey hCnn
        _ = 4*(Cm + Real.log 2 * (Cd*Ce)) / (Real.log x)^2 := by ring
    exact hcomb.trans hfin
  have hE1 : |∑ t ∈ Finset.Icc 1 ⌊x⌋₊, s3w t * (Real.log (x/(t:ℝ))-1)
        * (s3KA x t + s3KB x t - s3Main t)|
      ≤ K1 * (3*Real.log x) * (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 * (Real.log (2+x))^(-6:ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ t ∈ Finset.Icc 1 ⌊x⌋₊,
        |s3w t * (Real.log (x/(t:ℝ))-1) * (s3KA x t + s3KB x t - s3Main t)|
        ≤ K1 * (Real.log (2+x))^(-6:ℝ)
            * (Work.LinnikAreas.Density4.sHalf t * |s3w t| * (3*Real.log x)) := by
      intro t ht
      obtain ⟨ht1, -⟩ := Finset.mem_Icc.mp ht
      have hb := hsharp x t (by linarith) ht1
      have hb' : |s3KA x t + s3KB x t - s3Main t|
          ≤ K1 * Work.LinnikAreas.Density4.sHalf t * (Real.log (2+x))^(-6:ℝ) := by
        rw [s3KA_add_s3KB]; exact hb
      have hl := abs_log_div_sub_one_le x hx t ht
      calc |s3w t * (Real.log (x/(t:ℝ))-1) * (s3KA x t + s3KB x t - s3Main t)|
          = |s3w t| * |Real.log (x/(t:ℝ))-1| * |s3KA x t + s3KB x t - s3Main t| := by
            rw [abs_mul, abs_mul]
        _ ≤ |s3w t| * (3*Real.log x) * (K1 * Work.LinnikAreas.Density4.sHalf t * (Real.log (2+x))^(-6:ℝ)) := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left hl (abs_nonneg _)) hb' (abs_nonneg _) (by positivity)
        _ = K1 * (Real.log (2+x))^(-6:ℝ)
            * (Work.LinnikAreas.Density4.sHalf t * |s3w t| * (3*Real.log x)) := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    have hsum : (∑ t ∈ Finset.Icc 1 ⌊x⌋₊, Work.LinnikAreas.Density4.sHalf t * |s3w t|)
        ≤ (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 := sum_sHalf_abs_s3w_le ⌊x⌋₊
    calc (∑ t ∈ Finset.Icc 1 ⌊x⌋₊, K1 * (Real.log (2+x))^(-6:ℝ)
            * (Work.LinnikAreas.Density4.sHalf t * |s3w t| * (3*Real.log x)))
        = K1 * (Real.log (2+x))^(-6:ℝ) * (3*Real.log x)
            * (∑ t ∈ Finset.Icc 1 ⌊x⌋₊, Work.LinnikAreas.Density4.sHalf t * |s3w t|) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro t ht; ring
      _ ≤ K1 * (Real.log (2+x))^(-6:ℝ) * (3*Real.log x) * (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 := by
          have h1 : (0:ℝ) ≤ (Real.log (2+x))^(-6:ℝ) := Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
          have h2 : (0:ℝ) ≤ 3*Real.log x := by linarith [hlogx]
          have h3 : (0:ℝ) ≤ K1 * (Real.log (2+x))^(-6:ℝ) * (3*Real.log x) :=
            mul_nonneg (mul_nonneg hK1.le h1) h2
          exact mul_le_mul_of_nonneg_left hsum h3
      _ = K1 * (3*Real.log x) * (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 * (Real.log (2+x))^(-6:ℝ) := by ring
  have hE2 : |∑ t ∈ Finset.Icc 1 ⌊x⌋₊, s3w t * (s3KB x t * (2 - Real.log (x/(t:ℝ))))|
      ≤ K2 * (4*Real.log x) * (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 * (Real.log (2+x))^(-6:ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ t ∈ Finset.Icc 1 ⌊x⌋₊,
        |s3w t * (s3KB x t * (2 - Real.log (x/(t:ℝ))))|
        ≤ K2 * (Real.log (2+x))^(-6:ℝ)
            * (Work.LinnikAreas.Density4.sHalf t * |s3w t| * (4*Real.log x)) := by
      intro t ht
      obtain ⟨ht1, -⟩ := Finset.mem_Icc.mp ht
      have hb := hplain x t (by linarith) ht1
      have hl := abs_two_sub_log_div_le x hx t ht
      calc |s3w t * (s3KB x t * (2 - Real.log (x/(t:ℝ))))|
          = |s3w t| * (|s3KB x t| * |2 - Real.log (x/(t:ℝ))|) := by rw [abs_mul, abs_mul]
        _ ≤ |s3w t| * ((K2 * Work.LinnikAreas.Density4.sHalf t * (Real.log (2+x))^(-6:ℝ)) * (4*Real.log x)) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            have hc : (0:ℝ) ≤ K2 * Work.LinnikAreas.Density4.sHalf t * (Real.log (2+x))^(-6:ℝ) := by
              have h1 : (0:ℝ) ≤ (Real.log (2+x))^(-6:ℝ) := Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
              exact mul_nonneg (mul_nonneg hK2.le (hsH t)) h1
            calc |s3KB x t| * |2 - Real.log (x/(t:ℝ))|
                ≤ (K2 * Work.LinnikAreas.Density4.sHalf t * (Real.log (2+x))^(-6:ℝ)) * |2 - Real.log (x/(t:ℝ))| :=
                  mul_le_mul_of_nonneg_right hb (abs_nonneg _)
              _ ≤ (K2 * Work.LinnikAreas.Density4.sHalf t * (Real.log (2+x))^(-6:ℝ)) * (4*Real.log x) :=
                  mul_le_mul_of_nonneg_left hl hc
        _ = K2 * (Real.log (2+x))^(-6:ℝ)
            * (Work.LinnikAreas.Density4.sHalf t * |s3w t| * (4*Real.log x)) := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    have hsum : (∑ t ∈ Finset.Icc 1 ⌊x⌋₊, Work.LinnikAreas.Density4.sHalf t * |s3w t|)
        ≤ (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 := sum_sHalf_abs_s3w_le ⌊x⌋₊
    calc (∑ t ∈ Finset.Icc 1 ⌊x⌋₊, K2 * (Real.log (2+x))^(-6:ℝ)
            * (Work.LinnikAreas.Density4.sHalf t * |s3w t| * (4*Real.log x)))
        = K2 * (Real.log (2+x))^(-6:ℝ) * (4*Real.log x)
            * (∑ t ∈ Finset.Icc 1 ⌊x⌋₊, Work.LinnikAreas.Density4.sHalf t * |s3w t|) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro t ht; ring
      _ ≤ K2 * (Real.log (2+x))^(-6:ℝ) * (4*Real.log x) * (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 := by
          have h1 : (0:ℝ) ≤ (Real.log (2+x))^(-6:ℝ) := Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
          have h2 : (0:ℝ) ≤ 4*Real.log x := by linarith [hlogx]
          have h3 : (0:ℝ) ≤ K2 * (Real.log (2+x))^(-6:ℝ) * (4*Real.log x) :=
            mul_nonneg (mul_nonneg hK2.le h1) h2
          exact mul_le_mul_of_nonneg_left hsum h3
      _ = K2 * (4*Real.log x) * (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 * (Real.log (2+x))^(-6:ℝ) := by ring
  have hMsum : (∑ t ∈ Finset.Icc 1 ⌊x⌋₊, s3w t*(Real.log (x/(t:ℝ))-1)*s3Main t)
      = (Real.pi^2/6)*s3M x := by
    rw [s3M, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have hP : s3w t * (∏ p ∈ t.primeFactors, (1+1/(p:ℝ))) = (ArithmeticFunction.moebius t:ℝ)/(t:ℝ) :=
      s3w_mul_prod_one_add_inv t
    have h2 : s3w t*(Real.log (x/(t:ℝ))-1)*((Real.pi^2/6)*(∏ p ∈ t.primeFactors, (1+1/(p:ℝ))))
        = (Real.pi^2/6) * ((s3w t * (∏ p ∈ t.primeFactors, (1+1/(p:ℝ)))) * (Real.log (x/(t:ℝ))-1)) := by
      ring
    rw [s3Main, h2, hP]
  have hD_eq : s3D x = (Real.pi^2/6)*s3M x
      + (∑ t ∈ Finset.Icc 1 ⌊x⌋₊, s3w t*(Real.log (x/(t:ℝ))-1)*(s3KA x t + s3KB x t - s3Main t))
      + (∑ t ∈ Finset.Icc 1 ⌊x⌋₊, s3w t*(s3KB x t*(2 - Real.log (x/(t:ℝ))))) := by
    rw [s3D_eq_terms x]
    have hpt : ∀ t : ℕ, s3w t * ((Real.log (x/(t:ℝ))-1)*s3KA x t + s3KB x t)
        = s3w t*(Real.log (x/(t:ℝ))-1)*s3Main t
          + s3w t*(Real.log (x/(t:ℝ))-1)*(s3KA x t + s3KB x t - s3Main t)
          + s3w t*(s3KB x t*(2 - Real.log (x/(t:ℝ)))) := by
      intro t; ring
    rw [Finset.sum_congr rfl (fun t ht => hpt t)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hMsum]
    try ring
  have hDB : |s3D x - (Real.pi^2/6)*s3M x|
      ≤ (K1 * (3*Real.log x) + K2 * (4*Real.log x)) * (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 * (Real.log (2+x))^(-6:ℝ) := by
    have hdec : s3D x - (Real.pi^2/6)*s3M x
        = (∑ t ∈ Finset.Icc 1 ⌊x⌋₊, s3w t*(Real.log (x/(t:ℝ))-1)*(s3KA x t + s3KB x t - s3Main t))
          + (∑ t ∈ Finset.Icc 1 ⌊x⌋₊, s3w t*(s3KB x t*(2 - Real.log (x/(t:ℝ))))) := by
      rw [hD_eq]; ring
    rw [hdec]
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add hE1 hE2).trans (le_of_eq ?_)
    ring
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfin2 : (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 * (Real.log (2+x))^(-6:ℝ)
      ≤ 20 / (Real.log x)^4 := by
    have hpos2 : 0 < Real.log (2+x) := Real.log_pos (by linarith)
    have h4 : (Real.log (2+x))^(-6:ℝ) = 1/(Real.log (2+x))^6 := by
      rw [Real.rpow_neg (le_of_lt hpos2), Real.rpow_ofNat, one_div]
    have h2x : Real.log (2+x) ≤ 2 * Real.log x := by
      have h : 2 + x ≤ x^2 := by nlinarith
      calc Real.log (2+x) ≤ Real.log (x^2) := Real.log_le_log (by linarith) h
        _ = 2 * Real.log x := by rw [Real.log_pow]; norm_num
    have hlog2x_le : Real.log (2 + (⌊x⌋₊:ℝ)) ≤ Real.log (2+x) :=
      Real.log_le_log (by linarith) (by linarith [Nat.floor_le hx0.le])
    have hlog4 : (1:ℝ) ≤ Real.log 4 := by
      have h := Real.log_two_gt_d9
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
      push_cast
      linarith
    have hlog4le : Real.log 4 ≤ Real.log (2+x) := Real.log_le_log (by norm_num) (by linarith)
    have h6 : (Real.log x)^6 ≤ (Real.log (2+x))^6 :=
      pow_le_pow_left₀ (le_of_lt hlogx) (Real.log_le_log hx0 (by linarith)) 6
    by_cases ht1 : 1 ≤ Real.log x
    · have hA : 1 + Real.log (2 + (⌊x⌋₊:ℝ)) ≤ 3 * Real.log x := by linarith [hlog2x_le, h2x, ht1]
      have hAnn : 0 ≤ 1 + Real.log (2 + (⌊x⌋₊:ℝ)) := by
        have : 0 ≤ Real.log (2 + (⌊x⌋₊:ℝ)) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) ⌊x⌋₊])
        linarith
      have hsq : (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 ≤ 9 * (Real.log x)^2 := by nlinarith
      have hstep1 : (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 * (Real.log x)^2 ≤ 9 * (Real.log x)^4 := by
        calc (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 * (Real.log x)^2
            ≤ (9 * (Real.log x)^2) * (Real.log x)^2 :=
              mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
          _ = 9 * (Real.log x)^4 := by ring
      have hstep3 : (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 * (Real.log x)^4 ≤ 9 * (Real.log x)^6 := by
        have h := mul_le_mul_of_nonneg_right hstep1 (sq_nonneg (Real.log x))
        calc (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 * (Real.log x)^4
            = ((1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 * (Real.log x)^2) * (Real.log x)^2 := by ring
          _ ≤ (9 * (Real.log x)^4) * (Real.log x)^2 := h
          _ = 9 * (Real.log x)^6 := by ring
      rw [h4, mul_one_div]
      rw [div_le_div_iff₀ (pow_pos hpos2 6) (pow_pos hlogx 4)]
      have hp : (0:ℝ) ≤ (Real.log (2+x))^6 := pow_nonneg (Real.log_nonneg (by linarith)) 6
      linarith [hstep3, h6, hp]
    · push_neg at ht1
      have h5e : (5:ℝ) ≤ Real.exp 3 := by
        have h2 : (2:ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
        have he3 : Real.exp 3 = (Real.exp 1)^3 := by rw [← Real.exp_nat_mul]; norm_num
        rw [he3]
        have h3 : (8:ℝ) ≤ (Real.exp 1)^3 := by
          have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h2 3
          norm_num at h
          linarith
        linarith
      have hxe : x < Real.exp 1 := (Real.log_lt_iff_lt_exp hx0).mp ht1
      have hle5 : 2 + (⌊x⌋₊:ℝ) ≤ 5 := by
        have h4' : (⌊x⌋₊:ℝ) ≤ x := Nat.floor_le hx0.le
        have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
        linarith
      have hlog5 : Real.log (2 + (⌊x⌋₊:ℝ)) ≤ 3 := by
        calc Real.log (2 + (⌊x⌋₊:ℝ)) ≤ Real.log 5 := Real.log_le_log (by linarith) hle5
          _ ≤ 3 := (Real.log_le_iff_le_exp (by norm_num)).mpr h5e
      have h1 : 1 + Real.log (2 + (⌊x⌋₊:ℝ)) ≤ 4 := by linarith [hlog5]
      have hAnn : 0 ≤ 1 + Real.log (2 + (⌊x⌋₊:ℝ)) := by
        have : 0 ≤ Real.log (2 + (⌊x⌋₊:ℝ)) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) ⌊x⌋₊])
        linarith
      have hsq : (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 ≤ 16 := by
        have h := pow_le_pow_left₀ hAnn h1 2
        norm_num at h ⊢
        exact h
      have h6' : 1 ≤ (Real.log (2+x))^6 := by
        have h1' : (1:ℝ) ≤ Real.log (2+x) := le_trans hlog4 hlog4le
        simpa using one_le_pow₀ h1'
      have hl2 : (Real.log x)^2 ≤ 1 := by
        have h := pow_le_pow_left₀ hlogx.le ht1.le 2
        simpa using h
      have hsq2 : (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 * (Real.log x)^2 ≤ 16 := by
        calc (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 * (Real.log x)^2
            ≤ 16 * 1 := mul_le_mul hsq hl2 (sq_nonneg _) (by norm_num)
          _ = 16 := by ring
      have hsq3 : (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 * (Real.log x)^4 ≤ 16 := by
        have h := mul_le_mul hsq2 hl2 (sq_nonneg _) (by norm_num)
        calc (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 * (Real.log x)^4
            = ((1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 * (Real.log x)^2) * (Real.log x)^2 := by ring
          _ ≤ 16 * 1 := h
          _ = 16 := by ring
      rw [h4, mul_one_div]
      rw [div_le_div_iff₀ (pow_pos hpos2 6) (pow_pos hlogx 4)]
      have hp : (0:ℝ) ≤ (Real.log (2+x))^6 := pow_nonneg (Real.log_nonneg (by linarith)) 6
      linarith [hsq3, h6', hp]
  have hkey : s3Phi x - 1 = (Real.pi^2/6)⁻¹ * (s3D x - (Real.pi^2/6)*s3M x) + (s3M x - 1) := by
    have h1 : s3Phi x = (Real.pi^2/6)⁻¹ * s3D x := by
      rw [← s3Phi_mul x, ← mul_assoc, inv_mul_cancel₀ pi_div_six_ne_zero, one_mul]
    rw [h1]
    field_simp [pi_div_six_ne_zero]
    ring
  rw [hkey]
  have hcoef : |(Real.pi^2/6)⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (by positivity), inv_le_one₀ (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hb1 : |s3D x - (Real.pi^2/6)*s3M x| ≤ (K1 + K2) * (80/(Real.log x)^3) := by
    refine hDB.trans ?_
    have h3l : (0:ℝ) ≤ (K1 + K2) * (4*Real.log x) := by
      have h2 : (0:ℝ) ≤ 4*Real.log x := by linarith [hlogx]
      exact mul_nonneg (add_nonneg hK1.le hK2.le) h2
    have hnn6 : (0:ℝ) ≤ (Real.log (2+x))^(-6:ℝ) := Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
    have hX : (0:ℝ) ≤ (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 := sq_nonneg _
    have hmono : K1 * (3*Real.log x) + K2 * (4*Real.log x) ≤ (K1 + K2) * (4*Real.log x) := by
      have ha : K1 * (3*Real.log x) ≤ K1 * (4*Real.log x) :=
        mul_le_mul_of_nonneg_left (by linarith [hlogx]) hK1.le
      have hb : K2 * (4*Real.log x) ≤ K2 * (4*Real.log x) := le_refl _
      linarith [ha, hb]
    have hstep1 : (K1 * (3*Real.log x) + K2 * (4*Real.log x)) * (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 * (Real.log (2+x))^(-6:ℝ)
        ≤ ((K1 + K2) * (4*Real.log x)) * (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 * (Real.log (2+x))^(-6:ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmono hX) hnn6
    have hstep2 : ((K1 + K2) * (4*Real.log x)) * (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 * (Real.log (2+x))^(-6:ℝ)
        ≤ ((K1 + K2) * (4*Real.log x)) * (20/(Real.log x)^4) := by
      have h := mul_le_mul_of_nonneg_left hfin2 h3l
      calc ((K1 + K2) * (4*Real.log x)) * (1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 * (Real.log (2+x))^(-6:ℝ)
          = ((K1 + K2) * (4*Real.log x)) * ((1 + Real.log (2 + (⌊x⌋₊:ℝ)))^2 * (Real.log (2+x))^(-6:ℝ)) := by ring
        _ ≤ ((K1 + K2) * (4*Real.log x)) * (20/(Real.log x)^4) := h
    have hfinal : ((K1 + K2) * (4*Real.log x)) * (20/(Real.log x)^4) = (K1 + K2) * (80/(Real.log x)^3) := by
      have ht : Real.log x ≠ 0 := ne_of_gt hlogx
      field_simp
      ring
    exact hstep1.trans (hstep2.trans (le_of_eq hfinal))
  have hstep : |(Real.pi^2/6)⁻¹ * (s3D x - (Real.pi^2/6)*s3M x)| ≤ (80*(K1+K2)/Real.log 2) / (Real.log x)^2 := by
    rw [abs_mul]
    have hbase : |(Real.pi^2/6)⁻¹| * |s3D x - (Real.pi^2/6)*s3M x| ≤ 80*(K1+K2)/(Real.log x)^3 := by
      calc |(Real.pi^2/6)⁻¹| * |s3D x - (Real.pi^2/6)*s3M x|
          ≤ 1 * ((K1 + K2) * (80/(Real.log x)^3)) :=
            mul_le_mul hcoef hb1 (abs_nonneg _) (by norm_num)
        _ = 80*(K1+K2)/(Real.log x)^3 := by rw [one_mul, div_eq_mul_inv, div_eq_mul_inv]; ring
    refine hbase.trans ?_
    have h2 : (1:ℝ)/Real.log x ≤ 1/Real.log 2 :=
      one_div_le_one_div_of_le hlog2pos (Real.log_le_log (by norm_num) hx)
    calc 80*(K1+K2)/(Real.log x)^3 = (1/Real.log x) * (80*(K1+K2)/(Real.log x)^2) := by ring
      _ ≤ (1/Real.log 2) * (80*(K1+K2)/(Real.log x)^2) :=
          mul_le_mul_of_nonneg_right h2 (div_nonneg (by positivity) (sq_nonneg _))
      _ = (80*(K1+K2)/Real.log 2)/(Real.log x)^2 := by ring
  have hlast : (80*(K1+K2)/Real.log 2)/(Real.log x)^2 + 4*(Cm + Real.log 2 * (Cd*Ce)) / (Real.log x)^2
      ≤ (80*(K1+K2)/Real.log 2 + 4*(Cm + Real.log 2 * (Cd*Ce)) + 1) / (Real.log x)^2 := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (pow_pos hlogx 2).le
    linarith
  calc |(Real.pi^2/6)⁻¹ * (s3D x - (Real.pi^2/6)*s3M x) + (s3M x - 1)|
      ≤ |(Real.pi^2/6)⁻¹ * (s3D x - (Real.pi^2/6)*s3M x)| + |s3M x - 1| := abs_add_le _ _
    _ ≤ (80*(K1+K2)/Real.log 2)/(Real.log x)^2 + 4*(Cm + Real.log 2 * (Cd*Ce)) / (Real.log x)^2 :=
        add_le_add hstep hM1
    _ ≤ (80*(K1+K2)/Real.log 2 + 4*(Cm + Real.log 2 * (Cd*Ce)) + 1) / (Real.log x)^2 := hlast


/-- The final assembly, given the weighted `Θ`-error estimate. -/
theorem s3Phi_final
    (herr : ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ) (t : ℕ), 1 ≤ Q → 1 ≤ t →
      (∑ d ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Squarefree d ∧ Nat.Coprime d t),
          Work.LinnikAreas.Density4.prodKappa d * Work.LinnikAreas.Density4.sHalf (d * t) *
            (Real.log (2 + Q / (d : ℝ))) ^ (-6:ℝ))
        ≤ C * Work.LinnikAreas.Density4.sHalf t * (Real.log (2 + Q)) ^ (-6:ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → |s3Phi x - 1| ≤ C / (Real.log x)^2 := by
  obtain ⟨K1, hK1, h1⟩ := Work.LinnikAreas.Density4.mkl_core 6 (by norm_num)
    KappaLogSumReductionReal herr
  obtain ⟨K2, hK2, h2⟩ := kappaSum_bound 6 (by norm_num)
  refine s3Phi_main K1 K2 hK1 hK2 ?_ ?_
  · intro Q t hQ ht
    have h := h1 Q t (by linarith) ht
    have hsum : (∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t),
          s3w n * Real.log (Q/(n:ℝ)))
        = ∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t),
            (ArithmeticFunction.moebius n : ℝ)/((n:ℝ) * ∏ p ∈ n.primeFactors, (1 + 1/(p:ℝ)))
              * Real.log (Q/(n:ℝ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
      rw [s3w_eq n hn1]
    have hmain : s3Main t = (∏ p ∈ t.primeFactors, (1 + 1/(p:ℝ))) * (Real.pi^2/6) := by
      rw [s3Main]; ring
    have hrhs : K1 * Work.LinnikAreas.Density4.sHalf t * (Real.log (2+Q))^(-6:ℝ)
        = (K1 * ∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ)) * (Real.log (2+Q))^(-6:ℝ) := by
      rw [Work.LinnikAreas.Density4.sHalf]
      try ring
    rw [hsum, hmain, hrhs]
    exact h
  · intro Q t hQ ht
    have h := h2 Q t (by linarith) ht
    have hsum : (∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t), s3w n)
        = Work.LinnikAreas.Density4.kappaSum ⌊Q⌋₊ t := by
      rw [Work.LinnikAreas.Density4.kappaSum]
      apply Finset.sum_congr rfl
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
      rw [s3w_eq n hn1, Work.LinnikAreas.Density4.kappaR]
    rw [hsum]
    exact h

/-- **Asymptotic of the S3 model sum.** -/
theorem S3PhiAsymptotic : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
    |s3Phi x - 1| ≤ C / (Real.log x) ^ 2 := by
  obtain ⟨Kerr, hKerr, herr⟩ := kappaErrPowSelf 6 (by norm_num)
  exact s3Phi_final ⟨Kerr, hKerr, herr⟩

end

end Work.LinnikAreas.JutilaPieces
