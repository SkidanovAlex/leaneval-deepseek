import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.NumberTheory.BombieriVinogradov.abel_tail_sum_le
import Submission.Commons.NumberTheory.DirichletCharacter.isPrimitive_ne_one
import Submission.Commons.Analysis.Asymptotics.log_rpow_le_const_mul_rpow
import Submission.Commons.Analysis.Asymptotics.abel_tail_numeric_absorb

set_option maxHeartbeats 0

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators
open Finset Filter
open Classical

noncomputable section

/-! ## Elementary rewrites for `vonMangoldt` sums -/

private lemma vonMangoldt_zero : ArithmeticFunction.vonMangoldt 0 = 0 := by
  rw [ArithmeticFunction.vonMangoldt_apply, if_neg (not_isPrimePow_zero)]

private lemma range_succ_eq_insert_zero_Icc (y : ℕ) :
    Finset.range (y + 1) = insert 0 (Finset.Icc 1 y) := by
  ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega

private lemma charSum_range_eq_charSum_Icc (q : ℕ) (χ : DirichletCharacter ℂ q) (y : ℕ) :
    (∑ n ∈ Finset.range (y + 1),
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q))
      = ∑ n ∈ Finset.Icc 1 y,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q) := by
  rw [range_succ_eq_insert_zero_Icc y, Finset.sum_insert (by simp [Finset.mem_Icc])]
  rw [vonMangoldt_zero]; simp

/-- For a primitive character modulo `q ≥ 2` the two sup-forms appearing in the
statement (with the von Mangoldt sum over `range (y+1)` and the principal-character
correction, respectively over `Icc 1 y` without correction) agree. -/
private lemma inner_sup_eq {q : ℕ} (hq : 2 ≤ q) (X : ℕ) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    sSup ((fun y : ℕ => ‖∑ n ∈ Finset.range (y + 1),
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)
          - (if χ = 1 then (y : ℂ) else 0)‖) '' Set.Icc 1 X)
  = sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)‖) '' Set.Icc 1 X) := by
  have hne : χ ≠ 1 := Commons.NumberTheory.DirichletCharacter.isPrimitive_ne_one hq χ hχ
  congr 1
  apply Set.image_congr
  intro y _
  simp only [hne, if_false, sub_zero]
  rw [charSum_range_eq_charSum_Icc]

/-! ## Asymptotic helpers -/

private lemma le_log_rpow_eventually' {b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c) :
    ∀ᶠ n : ℕ in atTop, c ≤ (Real.log (n:ℝ))^b := by
  have hcb : (0:ℝ) < c + 1 := by linarith
  have hpow : ((c+1)^(1/b))^b = c+1 := by
    rw [← Real.rpow_mul hcb.le, one_div_mul_cancel hb.ne', Real.rpow_one]
  have hM0 : (0:ℝ) ≤ (c+1)^(1/b) := Real.rpow_nonneg hcb.le _
  have hlog : ∀ᶠ n : ℕ in atTop, max 1 ((c+1)^(1/b)) ≤ Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hlog] with n hn
  have hMM : ((c+1)^(1/b)) ≤ max 1 ((c+1)^(1/b)) := le_max_right _ _
  calc c ≤ c + 1 := by linarith
    _ = ((c+1)^(1/b))^b := hpow.symm
    _ ≤ (max 1 ((c+1)^(1/b)))^b := Real.rpow_le_rpow hM0 hMM hb.le
    _ ≤ (Real.log (n:ℝ))^b := Real.rpow_le_rpow (by positivity) hn hb.le

private lemma tendsto_sqrt_nat : Tendsto (fun n:ℕ => Real.sqrt (n:ℝ)) atTop atTop := by
  have h2 : Tendsto (fun n:ℕ => (n:ℝ)^(1/2:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (show (0:ℝ) < 1/2 by norm_num)).comp tendsto_natCast_atTop_atTop
  simpa [Real.sqrt_eq_rpow] using h2

private lemma eventually_two_mul_sqrt_add_le_sq' :
    ∀ᶠ n : ℕ in atTop, 2 * Real.sqrt (n:ℝ) + 2 ≤ (n:ℝ)^2 := by
  filter_upwards [eventually_ge_atTop (4:ℕ)] with n hn
  have hn' : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnn : (0:ℝ) ≤ (n:ℝ) := by linarith
  have h1 : (1:ℝ) ≤ Real.sqrt (n:ℝ) := by
    rw [Real.one_le_sqrt]; linarith
  have hs : Real.sqrt (n:ℝ) ≤ (n:ℝ) := by
    nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (n:ℝ)]
  nlinarith [hs, hn']

/-- **Basic Mean Value Theorem on the large-moduli range `R < q ≤ Q`.**

Assume the Basic Mean Value Theorem in the form (Vaughan, Theorem 1.2): for some
`C > 0`, for every `x ≥ 2` and `q ≥ 1`,

`Σ_{q' ≤ q} (q'/φ(q')) Σ*_{χ mod q'} sup_{y ≤ x} ‖Σ_{n ≤ y} Λ(n) χ(n)‖
   ≤ C (x + x^{5/6} q + x^{1/2} q²) (log(xq+2))^5`.

Then for every `A > 0`, for all large `X`, whenever `R ≥ (log X)^{2A+40}/2`,
`R ≤ Q` and `Q ≤ √X/(log X)^{2A+40}`, the totient-weighted primitive-character
sum over `R < q ≤ Q` is at most `X (log X)^{-(A+12)}`. -/
theorem bmvt_tail_bound
    (hBMVT : ∃ C : ℝ, 0 < C ∧ ∀ x q : ℕ, 2 ≤ x → 1 ≤ q →
      (∑ q' ∈ Finset.Icc 1 q, ((q' : ℝ) / (q'.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ q' => χ.IsPrimitive)),
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q')‖)
                '' Set.Icc 1 x))
      ≤ C * ((x : ℝ) + (x : ℝ) ^ (5 / 6 : ℝ) * (q : ℝ) + (x : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ 2)
          * (Real.log ((x : ℝ) * (q : ℝ) + 2)) ^ 5) :
    ∀ A : ℝ, 0 < A → ∀ᶠ X : ℕ in Filter.atTop, ∀ R Q : ℕ, 1 ≤ R → R ≤ Q →
      (Real.log (X : ℝ)) ^ (2 * A + 40) ≤ 2 * (R : ℝ) →
      (Q : ℝ) ≤ Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ (2 * A + 40) →
      (∑ q ∈ Finset.Ioc R Q, ((q.totient : ℕ) : ℝ)⁻¹ *
        ∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)),
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.range (y + 1),
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)
                - (if χ = 1 then (y : ℂ) else 0)‖) '' Set.Icc 1 X))
        ≤ (X : ℝ) * (Real.log (X : ℝ)) ^ (-(A + 12)) := by
  intro A hA
  obtain ⟨C, hCpos, hBMVT⟩ := hBMVT
  set m : ℝ := max C 1 with hmdef
  have hm1 : (1:ℝ) ≤ m := le_max_right _ _
  have hmC : C ≤ m := le_max_left _ _
  have hmpos : (0:ℝ) < m := lt_of_lt_of_le zero_lt_one hm1
  obtain ⟨Cab, hCabpos, habel⟩ := abel_tail_sum_le
  set KPhi : ℝ := max 1 (max (2916 * Cab * m^6) (729 * Real.sqrt 2 * Cab * m^3)) with hKPhidef
  have hKPhi_a : 2916 * Cab * m^6 ≤ KPhi := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKPhi_b : 729 * Real.sqrt 2 * Cab * m^3 ≤ KPhi := le_trans (le_max_right _ _) (le_max_right _ _)
  set c2 : ℝ := 1458 * (2:ℝ)^(5/6:ℝ) * Cab * m^5 with hc2def
  have hc2pos : 0 < c2 := by rw [hc2def]; positivity
  -- eventual conditions
  have hEv_X2 : ∀ᶠ X:ℕ in atTop, (2:ℕ) ≤ X := eventually_ge_atTop 2
  have htendlog : Tendsto (fun X:ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hEv_Phi : ∀ᶠ X:ℕ in atTop, (1:ℝ) ≤ Real.log (X:ℝ) := htendlog.eventually_ge_atTop 1
  have hEv_loglarge : ∀ᶠ X:ℕ in atTop, KPhi ≤ Real.log (X:ℝ) := htendlog.eventually_ge_atTop KPhi
  have hEv_logpow : ∀ᶠ X:ℕ in atTop, c2 * (Real.log (X:ℝ))^(A+18) ≤ (X:ℝ)^(1/6:ℝ) := by
    have hb := Commons.Analysis.Asymptotics.log_rpow_le_const_mul_rpow
      (show (0:ℝ) < A+18 by linarith) (show (0:ℝ) < 1/6 by norm_num)
      (show (0:ℝ) < 1/c2 by positivity)
    filter_upwards [hb] with n hn
    calc c2 * (Real.log (n:ℝ))^(A+18) ≤ c2 * ((1/c2) * (n:ℝ)^(1/6:ℝ)) :=
          mul_le_mul_of_nonneg_left hn hc2pos.le
      _ = (n:ℝ)^(1/6:ℝ) := by rw [← mul_assoc, mul_one_div, div_self hc2pos.ne', one_mul]
  have hEv_sqrt : ∀ᶠ X:ℕ in atTop, 4*m^6 ≤ Real.sqrt (X:ℝ) :=
    tendsto_sqrt_nat.eventually_ge_atTop (4*m^6)
  have hEv_Xsq : ∀ᶠ X:ℕ in atTop, 2 * Real.sqrt (X:ℝ) + 2 ≤ (X:ℝ)^2 :=
    eventually_two_mul_sqrt_add_le_sq'
  filter_upwards [hEv_X2, hEv_Phi, hEv_loglarge, hEv_logpow, hEv_sqrt, hEv_Xsq]
    with X hX2 hPhi1 hloglarge hlogpow hsqrt hXsq
  intro R Q hR hRQ hRbd hQbd
  have hXpos : (0:ℝ) < (X:ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) hX2)
  have hXnn : (0:ℝ) ≤ (X:ℝ) := le_of_lt hXpos
  set xa : ℕ := Nat.ceil (m^6 * (X:ℝ)) with hxadef
  have hxa_ge : m^6 * (X:ℝ) ≤ (xa:ℝ) := by rw [hxadef]; exact Nat.le_ceil _
  have hm6_ge1 : (1:ℝ) ≤ m^6 := one_le_pow₀ hm1
  have hm6X_ge1 : (1:ℝ) ≤ m^6 * (X:ℝ) := by nlinarith [hm6_ge1, hXpos]
  have hxa_ub_lt : (xa:ℝ) < m^6 * (X:ℝ) + 1 := by
    rw [hxadef]; exact Nat.ceil_lt_add_one (by positivity)
  have hxa_ub : (xa:ℝ) ≤ 2 * m^6 * (X:ℝ) := by linarith [hxa_ub_lt, hm6X_ge1]
  have hxa_pos : 0 < xa := by
    have h : (0:ℝ) < (xa:ℝ) := lt_of_lt_of_le (by linarith : (0:ℝ) < m^6 * (X:ℝ)) hxa_ge
    exact_mod_cast h
  set inner : ℕ → ℝ := (fun q => ∑ χ ∈ (Finset.univ.filter
        (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)),
      sSup ((fun y : ℕ => ‖∑ n ∈ Finset.range (y + 1),
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)
            - (if χ = 1 then (y : ℂ) else 0)‖) '' Set.Icc 1 X)) with hinnerdef
  set f : ℕ → ℝ := (fun q => if q = 1 then 0 else ((q.totient : ℕ) : ℝ)⁻¹ * inner q) with hfdef
  set T : ℕ → ℝ := (fun t => C * ((X:ℝ) + (X:ℝ)^(5/6:ℝ)*(t:ℝ) + (X:ℝ)^(1/2:ℝ)*(t:ℝ)^2)
        * (Real.log ((X:ℝ)*(t:ℝ)+2))^5) with hTdef
  have hinner_nn : ∀ q, 0 ≤ inner q := by
    intro q
    simp only [hinnerdef]
    apply Finset.sum_nonneg
    intro χ hχ
    exact Real.sSup_nonneg (by rintro z ⟨y, hy, rfl⟩; exact norm_nonneg _)
  have hf_nn : ∀ q, 0 ≤ f q := by
    intro q
    simp only [hfdef]
    by_cases hq : q = 1
    · simp [hq]
    · rw [if_neg hq]
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hinner_nn q)
  have hT : ∀ t : ℕ, T t ≤ ((xa:ℝ) + (xa:ℝ)^(5/6:ℝ)*(t:ℝ) + (xa:ℝ)^(1/2:ℝ)*(t:ℝ)^2)
        * (Real.log ((xa:ℝ)*(t:ℝ)+2))^5 := by
    intro t
    simp only [hTdef]
    have ht0 : (0:ℝ) ≤ (t:ℝ) := Nat.cast_nonneg t
    have hm_le_m6 : m ≤ m^6 := by
      simpa using pow_le_pow_right₀ hm1 (show 1 ≤ 6 by norm_num)
    have hxa_nn : (0:ℝ) ≤ (xa:ℝ) := le_of_lt (by exact_mod_cast hxa_pos)
    have hA1 : C * (X:ℝ) ≤ (xa:ℝ) := by
      have h1 : C * (X:ℝ) ≤ m * (X:ℝ) := mul_le_mul_of_nonneg_right hmC hXnn
      have h2 : m * (X:ℝ) ≤ m^6 * (X:ℝ) := mul_le_mul_of_nonneg_right hm_le_m6 hXnn
      linarith [hxa_ge]
    have hm6split56 : (m^6:ℝ)^(5/6:ℝ) = m^5 := by
      rw [show (m^6:ℝ) = m^(6:ℝ) from (Real.rpow_natCast m 6).symm,
          ← Real.rpow_mul hmpos.le]
      norm_num
    have hm6split12 : (m^6:ℝ)^(1/2:ℝ) = m^3 := by
      rw [show (m^6:ℝ) = m^(6:ℝ) from (Real.rpow_natCast m 6).symm,
          ← Real.rpow_mul hmpos.le]
      norm_num
    have hA2 : C * (X:ℝ)^(5/6:ℝ) ≤ (xa:ℝ)^(5/6:ℝ) := by
      have hm5_ge : m ≤ m^5 := by
        simpa using pow_le_pow_right₀ hm1 (show 1 ≤ 5 by norm_num)
      have hcx : C * (X:ℝ)^(5/6:ℝ) ≤ m^5 * (X:ℝ)^(5/6:ℝ) := by
        have h1 : C * (X:ℝ)^(5/6:ℝ) ≤ m * (X:ℝ)^(5/6:ℝ) :=
          mul_le_mul_of_nonneg_right hmC (Real.rpow_nonneg hXnn _)
        have h2 : m * (X:ℝ)^(5/6:ℝ) ≤ m^5 * (X:ℝ)^(5/6:ℝ) :=
          mul_le_mul_of_nonneg_right hm5_ge (Real.rpow_nonneg hXnn _)
        linarith
      have hm5eq : m^5 * (X:ℝ)^(5/6:ℝ) = (m^6 * (X:ℝ))^(5/6:ℝ) := by
        rw [Real.mul_rpow (by positivity) hXnn, hm6split56]
      have hbase : (m^6 * (X:ℝ))^(5/6:ℝ) ≤ (xa:ℝ)^(5/6:ℝ) :=
        Real.rpow_le_rpow (by positivity) hxa_ge (by norm_num)
      linarith
    have hA3 : C * (X:ℝ)^(1/2:ℝ) ≤ (xa:ℝ)^(1/2:ℝ) := by
      have hm3_ge : m ≤ m^3 := by
        simpa using pow_le_pow_right₀ hm1 (show 1 ≤ 3 by norm_num)
      have hcx : C * (X:ℝ)^(1/2:ℝ) ≤ m^3 * (X:ℝ)^(1/2:ℝ) := by
        have h1 : C * (X:ℝ)^(1/2:ℝ) ≤ m * (X:ℝ)^(1/2:ℝ) :=
          mul_le_mul_of_nonneg_right hmC (Real.rpow_nonneg hXnn _)
        have h2 : m * (X:ℝ)^(1/2:ℝ) ≤ m^3 * (X:ℝ)^(1/2:ℝ) :=
          mul_le_mul_of_nonneg_right hm3_ge (Real.rpow_nonneg hXnn _)
        linarith
      have hm3eq : m^3 * (X:ℝ)^(1/2:ℝ) = (m^6 * (X:ℝ))^(1/2:ℝ) := by
        rw [Real.mul_rpow (by positivity) hXnn, hm6split12]
      have hbase : (m^6 * (X:ℝ))^(1/2:ℝ) ≤ (xa:ℝ)^(1/2:ℝ) :=
        Real.rpow_le_rpow (by positivity) hxa_ge (by norm_num)
      linarith
    have hpoly : C * ((X:ℝ) + (X:ℝ)^(5/6:ℝ)*(t:ℝ) + (X:ℝ)^(1/2:ℝ)*(t:ℝ)^2)
        ≤ (xa:ℝ) + (xa:ℝ)^(5/6:ℝ)*(t:ℝ) + (xa:ℝ)^(1/2:ℝ)*(t:ℝ)^2 := by
      have he : C * ((X:ℝ) + (X:ℝ)^(5/6:ℝ)*(t:ℝ) + (X:ℝ)^(1/2:ℝ)*(t:ℝ)^2)
          = C*(X:ℝ) + (C*(X:ℝ)^(5/6:ℝ))*(t:ℝ) + (C*(X:ℝ)^(1/2:ℝ))*(t:ℝ)^2 := by ring
      rw [he]
      nlinarith [hA1, hA2, hA3, ht0, sq_nonneg (t:ℝ),
        Real.rpow_nonneg hxa_nn (5/6:ℝ), Real.rpow_nonneg hxa_nn (1/2:ℝ)]
    have hlog : (Real.log ((X:ℝ)*(t:ℝ)+2))^5 ≤ (Real.log ((xa:ℝ)*(t:ℝ)+2))^5 := by
      apply pow_le_pow_left₀
      · apply Real.log_nonneg; nlinarith [hXnn, ht0]
      · apply Real.log_le_log
        · nlinarith [hXnn, ht0]
        · have hX_le_xa : (X:ℝ) ≤ (xa:ℝ) := by
            have h : (X:ℝ) ≤ m^6 * (X:ℝ) := by
              have := mul_le_mul_of_nonneg_right hm6_ge1 hXnn
              simpa using this
            linarith [hxa_ge]
          have := mul_le_mul_of_nonneg_right hX_le_xa ht0
          linarith
    have hlog1 : (0:ℝ) ≤ Real.log ((X:ℝ)*(t:ℝ)+2) := Real.log_nonneg (by nlinarith [hXnn, ht0])
    exact mul_le_mul hpoly hlog (by positivity) (by positivity)
  have hTnn : ∀ t : ℕ, 0 ≤ T t := by
    intro t
    simp only [hTdef]
    have ht0 : (0:ℝ) ≤ (t:ℝ) := Nat.cast_nonneg t
    have hp : (0:ℝ) ≤ (X:ℝ) + (X:ℝ)^(5/6:ℝ)*(t:ℝ) + (X:ℝ)^(1/2:ℝ)*(t:ℝ)^2 := by
      have h1 := Real.rpow_nonneg hXnn (5/6:ℝ)
      have h2 := Real.rpow_nonneg hXnn (1/2:ℝ)
      nlinarith [hXnn, h1, h2, ht0]
    have hl : (0:ℝ) ≤ (Real.log ((X:ℝ)*(t:ℝ)+2))^5 := by
      apply pow_nonneg
      apply Real.log_nonneg
      nlinarith [hXnn, ht0]
    exact mul_nonneg (mul_nonneg hCpos.le hp) hl
  have hPS : ∀ t : ℕ, (∑ q ∈ Finset.Icc 1 t, (q:ℝ) * f q) ≤ T t := by
    intro t
    by_cases ht0 : t = 0
    · subst ht0
      rw [Finset.Icc_eq_empty (by omega : ¬ 1 ≤ 0), Finset.sum_empty]
      exact hTnn 0
    · have ht1 : 1 ≤ t := by omega
      have hsplit : Finset.Icc 1 t = insert 1 (Finset.Icc 2 t) := by
        ext q; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have h1notin : 1 ∉ Finset.Icc 2 t := by simp [Finset.mem_Icc]
      have hf1 : f 1 = 0 := by simp [hfdef]
      have hLHS : (∑ q ∈ Finset.Icc 1 t, (q:ℝ) * f q) = ∑ q ∈ Finset.Icc 2 t, (q:ℝ) * f q := by
        rw [hsplit, Finset.sum_insert h1notin, hf1]
        ring
      have hsummand : ∀ q ∈ Finset.Icc 2 t, (q:ℝ) * f q = ((q:ℝ)/(q.totient:ℝ)) * inner q := by
        intro q hq
        have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
        have hqne : q ≠ 1 := by omega
        simp only [hfdef]
        rw [if_neg hqne, div_eq_mul_inv, mul_assoc]
      have hinner_eq : ∀ q ∈ Finset.Icc 2 t, inner q =
          (∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)),
            sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)‖)
                '' Set.Icc 1 X)) := by
        intro q hq
        have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
        simp only [hinnerdef]
        apply Finset.sum_congr rfl
        intro χ hχ
        exact inner_sup_eq hq2 X χ (Finset.mem_filter.mp hχ).2
      have hstep : (∑ q ∈ Finset.Icc 2 t, ((q:ℝ)/(q.totient:ℝ)) * inner q)
          ≤ (∑ q ∈ Finset.Icc 1 t, ((q:ℝ)/(q.totient:ℝ)) *
              ∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)),
                sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
                  ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)‖)
                    '' Set.Icc 1 X)) := by
        have heq : (∑ q ∈ Finset.Icc 2 t, ((q:ℝ)/(q.totient:ℝ)) * inner q)
            = ∑ q ∈ Finset.Icc 2 t, ((q:ℝ)/(q.totient:ℝ)) *
                (∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)),
                  sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
                    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)‖)
                      '' Set.Icc 1 X)) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [hinner_eq q hq]
        rw [heq, hsplit, Finset.sum_insert h1notin]
        have hg1 : (0:ℝ) ≤ ((1:ℝ)/(Nat.totient 1:ℝ)) *
            (∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ 1 => χ.IsPrimitive)),
              sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod 1)‖)
                  '' Set.Icc 1 X)) := by
          apply mul_nonneg (by norm_num)
          apply Finset.sum_nonneg
          intro χ hχ
          exact Real.sSup_nonneg (by rintro z ⟨y, hy, rfl⟩; exact norm_nonneg _)
        linarith [hg1]
      calc (∑ q ∈ Finset.Icc 1 t, (q:ℝ) * f q)
          = ∑ q ∈ Finset.Icc 2 t, (q:ℝ) * f q := hLHS
        _ = ∑ q ∈ Finset.Icc 2 t, ((q:ℝ)/(q.totient:ℝ)) * inner q :=
              Finset.sum_congr rfl hsummand
        _ ≤ ∑ q ∈ Finset.Icc 1 t, ((q:ℝ)/(q.totient:ℝ)) *
              ∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)),
                sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
                  ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)‖)
                    '' Set.Icc 1 X) := hstep
        _ ≤ C * ((X:ℝ) + (X:ℝ)^(5/6:ℝ)*(t:ℝ) + (X:ℝ)^(1/2:ℝ)*(t:ℝ)^2)
              * (Real.log ((X:ℝ)*(t:ℝ)+2))^5 := hBMVT X t hX2 ht1
        _ = T t := by simp only [hTdef]
  have habel_app := habel f xa Q R T hxa_pos hR hRQ hf_nn hT hPS
  have htarget_eq : (∑ q ∈ Finset.Ioc R Q, ((q.totient : ℕ) : ℝ)⁻¹ * inner q)
      = ∑ q ∈ Finset.Ioc R Q, f q := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqne : q ≠ 1 := by
      have hRq : R < q := (Finset.mem_Ioc.mp hq).1
      omega
    simp only [hfdef]
    rw [if_neg hqne]
  have hBnd : Cab * ((xa:ℝ)/(R:ℝ) + (xa:ℝ)^(5/6:ℝ)
        * Real.log (2 * ((Q:ℝ)/(R:ℝ)) + 2) + (xa:ℝ)^(1/2:ℝ) * (Q:ℝ))
        * (Real.log ((xa:ℝ)*(Q:ℝ)+2))^5
      ≤ (X:ℝ) * (Real.log (X:ℝ))^(-(A+12)) := by
    refine Commons.Analysis.Asymptotics.abel_tail_numeric_absorb Cab m A (X:ℝ) R Q xa
      hCabpos hm1 hA ?_ hPhi1 ?_ ?_ hR hRQ hRbd hQbd hxa_ub hXsq hsqrt
    · exact_mod_cast hX2
    · rw [← hKPhidef]; exact hloglarge
    · rw [← hc2def]; exact hlogpow
  calc (∑ q ∈ Finset.Ioc R Q, ((q.totient : ℕ) : ℝ)⁻¹ *
        ∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)),
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.range (y + 1),
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)
                - (if χ = 1 then (y : ℂ) else 0)‖) '' Set.Icc 1 X))
      = ∑ q ∈ Finset.Ioc R Q, f q := htarget_eq
    _ ≤ Cab * ((xa:ℝ)/(R:ℝ) + (xa:ℝ)^(5/6:ℝ)
          * Real.log (2 * ((Q:ℝ)/(R:ℝ)) + 2) + (xa:ℝ)^(1/2:ℝ) * (Q:ℝ))
          * (Real.log ((xa:ℝ)*(Q:ℝ)+2))^5 := habel_app
    _ ≤ (X:ℝ) * (Real.log (X:ℝ))^(-(A+12)) := hBnd

end
end Commons.NumberTheory.BombieriVinogradov