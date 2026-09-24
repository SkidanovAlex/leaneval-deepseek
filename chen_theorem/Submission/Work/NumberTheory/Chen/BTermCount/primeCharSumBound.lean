import Mathlib
import Mathlib.Algebra.BigOperators.Module
import Submission.Commons.NumberTheory.BombieriVinogradov.siegel_walfisz_chi_range
import Submission.Commons.NumberTheory.Chebyshev.cumulativePrimePowerLeSqrt
import Submission.Work.NumberTheory.Chen.BTermCount.abelLogWeightBound
import Submission.Work.NumberTheory.Chen.BTermCount.chiLambdaNonprimeSumBound

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

attribute [local instance] Classical.propDecidable

/-! ## Eventual arithmetic lemmas -/

/-- `D * (log x)^A` is eventually below any positive power of `x`. -/
lemma eventually_log_pow_mul_le_rpow (A s : ℝ) (hA : 0 < A) (hs : 0 < s) (D : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, D * (Real.log x) ^ A ≤ x ^ s := by
  rcases le_or_gt D 0 with hD | hD
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have h1 : (0 : ℝ) ≤ (Real.log x) ^ A := Real.rpow_nonneg (Real.log_nonneg hx) A
    have h3 : D * (Real.log x) ^ A ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hD h1
    have h2 : (0 : ℝ) ≤ x ^ s := Real.rpow_nonneg (by linarith) s
    linarith
  · have hc : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x ^ A‖ ≤ (1 / (2 * D)) * ‖x ^ s‖ :=
      (isLittleO_log_rpow_rpow_atTop A hs).bound (by positivity)
    filter_upwards [hc, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) A),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ x) s)] at hx
    have hstep : D * (Real.log x) ^ A ≤ D * (1 / (2 * D) * x ^ s) :=
      mul_le_mul_of_nonneg_left hx hD.le
    have hsimp : D * (1 / (2 * D) * x ^ s) = x ^ s / 2 := by field_simp
    rw [hsimp] at hstep
    have h2 : (0 : ℝ) ≤ x ^ s := Real.rpow_nonneg (by linarith) s
    linarith

/-- The natural-number version. -/
lemma eventually_nat_log_pow_mul_le_rpow (A s : ℝ) (hA : 0 < A) (hs : 0 < s) (D : ℝ) :
    ∀ᶠ x : ℕ in Filter.atTop, D * (Real.log (x : ℝ)) ^ A ≤ (x : ℝ) ^ s :=
  tendsto_natCast_atTop_atTop.eventually (eventually_log_pow_mul_le_rpow A s hA hs D)

/-- For any `D` and any positive exponent `e`, eventually `D ≤ x^e`. -/
lemma eventually_const_le_nat_rpow {e : ℝ} (he : 0 < e) (D : ℝ) :
    ∀ᶠ x : ℕ in Filter.atTop, D ≤ (x : ℝ) ^ e :=
  tendsto_natCast_atTop_atTop.eventually ((tendsto_rpow_atTop he).eventually_ge_atTop D)

/-- For any `D`, eventually `D ≤ log x`. -/
lemma eventually_const_le_nat_log (D : ℝ) :
    ∀ᶠ x : ℕ in Filter.atTop, D ≤ Real.log (x : ℝ) :=
  tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop D)

/-! ## The non-prime von Mangoldt contribution -/

/-- The sum of `Λ` over the non-prime `n ≤ t` is `ψ t - θ t`. -/
lemma psi_sub_theta_eq_filter_sum (t : ℕ) :
    Chebyshev.psi (t : ℝ) - Chebyshev.theta (t : ℝ)
      = ∑ n ∈ (Finset.Icc 0 t).filter (fun n => ¬ n.Prime),
          ArithmeticFunction.vonMangoldt n := by
  have hpsi : Chebyshev.psi (t : ℝ)
      = ∑ n ∈ Finset.Icc 0 t, ArithmeticFunction.vonMangoldt n := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  have htheta : Chebyshev.theta (t : ℝ)
      = ∑ n ∈ (Finset.Icc 0 t).filter (fun n => n.Prime),
          ArithmeticFunction.vonMangoldt n := by
    rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
    refine Finset.sum_congr rfl ?_
    intro n hn
    exact (ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2).symm
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.Icc 0 t)
    (p := fun n => n.Prime) (f := fun n => ArithmeticFunction.vonMangoldt n)
  rw [hpsi, htheta, ← hsplit, add_sub_cancel_left]

/-- The sum of `Λ` over the non-prime `n ≤ t` is `O(√t)`. -/
lemma exists_nonprime_vonMangoldt_sum_bound :
    ∃ Cpp : ℝ, 0 < Cpp ∧ ∀ t : ℕ,
      (∑ n ∈ (Finset.Icc 0 t).filter (fun n => ¬ n.Prime),
          ArithmeticFunction.vonMangoldt n) ≤ Cpp * Real.sqrt (t : ℝ) := by
  obtain ⟨Cθ, hCθ⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨max Cθ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun t => ?_⟩
  rw [← psi_sub_theta_eq_filter_sum t]
  calc Chebyshev.psi (t : ℝ) - Chebyshev.theta (t : ℝ) ≤ Cθ * Real.sqrt (t : ℝ) := hCθ _
    _ ≤ max Cθ 1 * Real.sqrt (t : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)

/-! ## Elementary summand bounds -/

/-- `|L⁻¹| * L ≤ 1` for every real `L`. -/
lemma abs_inv_mul_self_le_one (L : ℝ) : |L⁻¹| * L ≤ 1 := by
  by_cases h : L = 0
  · simp [h]
  · rw [abs_inv, inv_mul_eq_div, div_le_one (abs_pos.mpr h)]
    exact le_abs_self L

/-- For a prime `p`, the weighted term `χ(p) Λ(p) / log p` is just `χ(p)`. -/
lemma smul_prime_eq (c : ℕ) (χ : DirichletCharacter ℂ c) {p : ℕ} (hp : p.Prime) :
    ((Real.log (p : ℝ))⁻¹ : ℝ) •
        (χ (p : ZMod c) * ((ArithmeticFunction.vonMangoldt p : ℝ) : ℂ))
      = χ (p : ZMod c) := by
  have hlog : (Real.log (p : ℝ)) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt))
  have hlogC : ((Real.log (p : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog
  rw [Complex.real_smul, ArithmeticFunction.vonMangoldt_apply_prime hp, Complex.ofReal_inv]
  field_simp

/-- The contribution of `1 ≤ i ≤ Y` to the weighted von Mangoldt sum is at most `Y`. -/
lemma small_part_le (c Y : ℕ) (χ : DirichletCharacter ℂ c) :
    ‖∑ i ∈ Finset.Ico 1 (Y + 1),
        ((Real.log (i : ℝ))⁻¹ : ℝ) •
          (χ (i : ZMod c) * ((ArithmeticFunction.vonMangoldt i : ℝ) : ℂ))‖ ≤ Y := by
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ i ∈ Finset.Ico 1 (Y + 1),
      ‖((Real.log (i : ℝ))⁻¹ : ℝ) •
          (χ (i : ZMod c) * ((ArithmeticFunction.vonMangoldt i : ℝ) : ℂ))‖ ≤ 1 := by
    intro i _
    rw [Complex.real_smul, norm_mul, norm_mul]
    have h2 : ‖((ArithmeticFunction.vonMangoldt i : ℝ) : ℂ)‖
        = (ArithmeticFunction.vonMangoldt i : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have h4 : ‖(((Real.log (i : ℝ))⁻¹ : ℝ) : ℂ)‖ = |(Real.log (i : ℝ))⁻¹| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [h2, h4]
    have h3 : ‖χ (i : ZMod c)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hΛ : (ArithmeticFunction.vonMangoldt i : ℝ) ≤ Real.log (i : ℝ) :=
      ArithmeticFunction.vonMangoldt_le_log
    have hΛ0 : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt i : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have h5 : ‖χ (i : ZMod c)‖ * (ArithmeticFunction.vonMangoldt i : ℝ)
        ≤ 1 * (ArithmeticFunction.vonMangoldt i : ℝ) :=
      mul_le_mul_of_nonneg_right h3 hΛ0
    calc |(Real.log (i : ℝ))⁻¹| * (‖χ (i : ZMod c)‖ * (ArithmeticFunction.vonMangoldt i : ℝ))
        ≤ |(Real.log (i : ℝ))⁻¹| * (1 * (ArithmeticFunction.vonMangoldt i : ℝ)) :=
          mul_le_mul_of_nonneg_left h5 (abs_nonneg _)
      _ = |(Real.log (i : ℝ))⁻¹| * (ArithmeticFunction.vonMangoldt i : ℝ) := by ring
      _ ≤ |(Real.log (i : ℝ))⁻¹| * Real.log (i : ℝ) :=
          mul_le_mul_of_nonneg_left hΛ (abs_nonneg _)
      _ ≤ 1 := abs_inv_mul_self_le_one _
  calc ∑ i ∈ Finset.Ico 1 (Y + 1),
        ‖((Real.log (i : ℝ))⁻¹ : ℝ) •
          (χ (i : ZMod c) * ((ArithmeticFunction.vonMangoldt i : ℝ) : ℂ))‖
      ≤ ∑ _i ∈ Finset.Ico 1 (Y + 1), (1 : ℝ) := Finset.sum_le_sum hterm
    _ = ((Finset.Ico 1 (Y + 1)).card : ℝ) := by simp
    _ = Y := by rw [Nat.card_Ico]; simp

/-! ## A uniform bound for the twisted von Mangoldt sums -/

/-- The Siegel–Walfisz input, uniformly for all integers `n` in the range
`x^{1/15} + 1 < n ≤ x + 1`, with the sharp modulus range `c ≤ (log x)^C`. -/
lemma uniform_vonMangoldt_bound (A C : ℝ) (hA : 0 < A) (hC : 0 < C) :
    ∀ᶠ x : ℕ in Filter.atTop,
      ∀ {c : ℕ}, 2 ≤ c → c ≤ ⌊(Real.log (x : ℝ)) ^ C⌋₊ →
      ∀ χ : DirichletCharacter ℂ c, χ.IsPrimitive → χ ≠ 1 →
      ∀ n : ℕ, (x : ℝ) ^ ((1 : ℝ) / 15) + 1 < n → n ≤ x + 1 →
        ‖∑ i ∈ Finset.range n,
            ((ArithmeticFunction.vonMangoldt i : ℝ) : ℂ) * χ (i : ZMod c)‖
          ≤ (n : ℝ) / (Real.log (x : ℝ) / 15) ^ (A + 1) := by
  have hA1 : (0 : ℝ) < A + 1 := by linarith
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  have hSW : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ {q : ℕ} [NeZero q], q ≤ ⌊(Real.log (n : ℝ)) ^ (C + 1)⌋₊ →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
        ‖∑ i ∈ Finset.range (n + 1),
            ((ArithmeticFunction.vonMangoldt i : ℝ) : ℂ) * χ (i : ZMod q)‖
          ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ (A + 1) :=
    Commons.NumberTheory.BombieriVinogradov.siegel_walfisz_chi_range (A + 1) (C + 1) hA1 hC1
  rw [Filter.eventually_atTop] at hSW
  obtain ⟨Nsw, hNsw⟩ := hSW
  filter_upwards [eventually_const_le_nat_rpow (by norm_num : (0:ℝ) < 1/15) ((Nsw : ℝ) + 3),
                  eventually_const_le_nat_log (15 ^ (C + 1))] with x hxpow hxlog
  intro c hc2 hcC χ hprim h1ne n hnlo hnhi
  haveI : NeZero c := ⟨by omega⟩
  have h15pos : (0 : ℝ) < 15 ^ (C + 1) := Real.rpow_pos_of_pos (by norm_num) _
  have hlogpos : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le h15pos hxlog
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    by_contra hcon
    push_neg at hcon
    have hlogle : Real.log (x : ℝ) ≤ 0 := Real.log_nonpos (Nat.cast_nonneg x) hcon.le
    linarith
  have hx0 : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le one_pos hx1
  have hn1 : (1 : ℝ) < (n : ℝ) := by
    have h2 : (0 : ℝ) ≤ (x : ℝ) ^ ((1:ℝ)/15) := (Real.rpow_pos_of_pos hx0 _).le
    linarith
  have hn1n : (1 : ℕ) ≤ n := by exact_mod_cast hn1.le
  have hnNsw : Nsw ≤ n - 1 := by
    have h : (Nsw : ℝ) + 3 < (n : ℝ) :=
      lt_of_le_of_lt hxpow (by linarith : (x : ℝ) ^ ((1:ℝ)/15) < (n : ℝ))
    have h' : Nsw + 3 < n := by exact_mod_cast h
    omega
  have hlogm : Real.log (x : ℝ) / 15 ≤ Real.log ((n - 1 : ℕ) : ℝ) := by
    have hnm1 : (x : ℝ) ^ ((1 : ℝ) / 15) ≤ ((n - 1 : ℕ) : ℝ) := by
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub hn1n]; ring
      rw [hcast]; linarith
    calc Real.log (x : ℝ) / 15 = Real.log ((x : ℝ) ^ ((1 : ℝ) / 15)) := by
          rw [Real.log_rpow hx0]; ring
      _ ≤ Real.log ((n - 1 : ℕ) : ℝ) :=
          Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hnm1
  have hcle : (c : ℝ) ≤ (Real.log ((n - 1 : ℕ) : ℝ)) ^ (C + 1) := by
    have hlogun : (0 : ℝ) ≤ Real.log (x : ℝ) := le_of_lt hlogpos
    have h1 : (c : ℝ) ≤ (Real.log (x : ℝ)) ^ C :=
      le_trans (by exact_mod_cast hcC) (Nat.floor_le (Real.rpow_nonneg hlogun C))
    have h2 : (Real.log (x : ℝ)) ^ C ≤ (Real.log (x : ℝ) / 15) ^ (C + 1) := by
      rw [Real.div_rpow hlogun (by norm_num : (0:ℝ) ≤ 15)]
      rw [le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 15) _)]
      calc (Real.log (x : ℝ)) ^ C * 15 ^ (C + 1)
          ≤ (Real.log (x : ℝ)) ^ C * Real.log (x : ℝ) :=
            mul_le_mul_of_nonneg_left hxlog (Real.rpow_nonneg hlogun C)
        _ = (Real.log (x : ℝ)) ^ (C + 1) := by
            rw [← Real.rpow_add_one hlogpos.ne' C]
    have h4 : (Real.log (x : ℝ) / 15) ^ (C + 1)
        ≤ (Real.log ((n - 1 : ℕ) : ℝ)) ^ (C + 1) :=
      Real.rpow_le_rpow (by positivity) hlogm (by linarith)
    linarith
  have hbound := hNsw (n - 1) hnNsw (q := c) (Nat.le_floor hcle) χ hprim h1ne
  have hrange : Finset.range ((n - 1) + 1) = Finset.range n := by
    congr 1; omega
  rw [hrange] at hbound
  refine le_trans hbound ?_
  have hnum : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn1n]; ring
    rw [hcast]; linarith
  have hden1 : 0 < (Real.log ((n - 1 : ℕ) : ℝ)) ^ (A + 1) :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le (by positivity) hlogm) _
  have hden2 : 0 < (Real.log (x : ℝ) / 15) ^ (A + 1) :=
    Real.rpow_pos_of_pos (by positivity) _
  calc ((n - 1 : ℕ) : ℝ) / (Real.log ((n - 1 : ℕ) : ℝ)) ^ (A + 1)
      ≤ (n : ℝ) / (Real.log ((n - 1 : ℕ) : ℝ)) ^ (A + 1) :=
        div_le_div_of_nonneg_right hnum hden1.le
    _ ≤ (n : ℝ) / (Real.log (x : ℝ) / 15) ^ (A + 1) :=
        div_le_div_of_nonneg_left (by positivity) hden2
          (Real.rpow_le_rpow (by positivity) hlogm (by linarith))


/-! ## The final arithmetic comparison -/

/-- The three pieces of the bound are each at most a third of the target. -/
lemma final_arith (A : ℝ) (hA : 0 < A) (Cpp : ℝ) (hCppnonneg : 0 ≤ Cpp)
    {x : ℕ} (hxlog : 300 * 15 ^ (A + 1) ≤ Real.log (x : ℝ))
    (hbig1 : 6 * Cpp * (Real.log (x : ℝ)) ^ A ≤ (x : ℝ) ^ ((1 : ℝ) / 28))
    (hbig2 : 9 * (Real.log (x : ℝ)) ^ A ≤ (x : ℝ) ^ ((1 : ℝ) / 210))
    {T : ℝ} (hTlo : (x : ℝ) ^ ((1 : ℝ) / 14) ≤ T)
    {t Y : ℕ} (ht : T - 1 < (t : ℝ)) (htT : (t : ℝ) ≤ T)
    (hY : (Y : ℝ) ≤ 3 * (x : ℝ) ^ ((1 : ℝ) / 15)) :
    (Y : ℝ) + 100 * (1 / ((Real.log (x : ℝ) / 15) ^ (A + 1))) * (t : ℝ)
      + Cpp * Real.sqrt (t : ℝ) ≤ T / (Real.log (x : ℝ)) ^ A := by
  have h15A1 : (1 : ℝ) ≤ 15 ^ (A + 1) := Real.one_le_rpow (by norm_num) (by linarith)
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    by_contra hcon
    push_neg at hcon
    have hlog0 : Real.log (x : ℝ) ≤ 0 := Real.log_nonpos (Nat.cast_nonneg x) hcon.le
    linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le one_pos hx1
  have hlogx1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by linarith
  have hlogpos : (0 : ℝ) < Real.log (x : ℝ) := by linarith
  have hlogApos : (0 : ℝ) < (Real.log (x : ℝ)) ^ A := Real.rpow_pos_of_pos hlogpos A
  have hlogpow1 : (1 : ℝ) ≤ (Real.log (x : ℝ)) ^ A := Real.one_le_rpow hlogx1 hA.le
  have hx210 : (9 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 210) := by linarith [hbig2, hlogpow1]
  have hx15pos : (0 : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 15) := Real.rpow_pos_of_pos hxpos _
  have hx15ge : (9 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 15) :=
    le_trans hx210 (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))
  have hx14ge : (4 / 3 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 14) :=
    le_trans (by norm_num) (le_trans hx210
      (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)))
  have hx14split : (x : ℝ) ^ ((1 : ℝ) / 14)
      = (x : ℝ) ^ ((1 : ℝ) / 15) * (x : ℝ) ^ ((1 : ℝ) / 210) := by
    rw [← Real.rpow_add hxpos]; congr 1; norm_num
  have hTnonneg : (0 : ℝ) ≤ T := le_trans (Real.rpow_nonneg (Nat.cast_nonneg x) _) hTlo
  -- the three terms
  have h1 : (Y : ℝ) ≤ T / (3 * (Real.log (x : ℝ)) ^ A) := by
    have hkey : 9 * (Real.log (x : ℝ)) ^ A * (x : ℝ) ^ ((1 : ℝ) / 15)
        ≤ (x : ℝ) ^ ((1 : ℝ) / 14) := by
      rw [hx14split, mul_comm ((x : ℝ) ^ ((1 : ℝ) / 15))]
      exact mul_le_mul_of_nonneg_right hbig2 hx15pos.le
    have h3 : 3 * (x : ℝ) ^ ((1 : ℝ) / 15)
        ≤ (x : ℝ) ^ ((1 : ℝ) / 14) / (3 * (Real.log (x : ℝ)) ^ A) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 3 * (Real.log (x : ℝ)) ^ A)]
      nlinarith [hkey]
    have h4 : (x : ℝ) ^ ((1 : ℝ) / 14) / (3 * (Real.log (x : ℝ)) ^ A)
        ≤ T / (3 * (Real.log (x : ℝ)) ^ A) :=
      div_le_div_of_nonneg_right hTlo (by positivity)
    linarith [hY, h3, h4]
  have h2 : 100 * (1 / ((Real.log (x : ℝ) / 15) ^ (A + 1))) * (t : ℝ)
      ≤ T / (3 * (Real.log (x : ℝ)) ^ A) := by
    have hLeq : (1 / ((Real.log (x : ℝ) / 15) ^ (A + 1)) : ℝ)
        = 15 ^ (A + 1) / (Real.log (x : ℝ)) ^ (A + 1) := by
      rw [Real.div_rpow hlogpos.le (by norm_num : (0 : ℝ) ≤ 15), one_div_div]
    have hpoweq : (Real.log (x : ℝ)) ^ (A + 1)
        = (Real.log (x : ℝ)) ^ A * Real.log (x : ℝ) := by
      rw [Real.rpow_add_one hlogpos.ne']
    have hcoef : 100 * 15 ^ (A + 1) / Real.log (x : ℝ) ≤ 1 / 3 := by
      rw [div_le_iff₀ hlogpos]
      linarith
    calc 100 * (1 / ((Real.log (x : ℝ) / 15) ^ (A + 1))) * (t : ℝ)
        ≤ 100 * (1 / ((Real.log (x : ℝ) / 15) ^ (A + 1))) * T := by
          have h100 : (0 : ℝ) ≤ 100 * (1 / ((Real.log (x : ℝ) / 15) ^ (A + 1))) := by positivity
          exact mul_le_mul_of_nonneg_left htT h100
      _ = T * (100 * 15 ^ (A + 1) / Real.log (x : ℝ)) / (Real.log (x : ℝ)) ^ A := by
          rw [hLeq, hpoweq]
          field_simp
      _ ≤ T * (1 / 3) / (Real.log (x : ℝ)) ^ A := by
          have hApos : (0 : ℝ) < (Real.log (x : ℝ)) ^ A := hlogApos
          gcongr
      _ = T / (3 * (Real.log (x : ℝ)) ^ A) := by ring
  have h3 : Cpp * Real.sqrt (t : ℝ) ≤ T / (3 * (Real.log (x : ℝ)) ^ A) := by
    have hsqr : (x : ℝ) ^ ((1 : ℝ) / 28) / 2 ≤ Real.sqrt (t : ℝ) := by
      rw [Real.le_sqrt (by positivity) (Nat.cast_nonneg t)]
      have hsq : ((x : ℝ) ^ ((1 : ℝ) / 28) / 2) ^ 2 = (x : ℝ) ^ ((1 : ℝ) / 14) / 4 := by
        have h1 : ((x : ℝ) ^ ((1 : ℝ) / 28)) ^ 2 = (x : ℝ) ^ ((1 : ℝ) / 14) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
          congr 1
          norm_num
        rw [div_pow, h1]
        norm_num
      rw [hsq]
      have htge : (x : ℝ) ^ ((1 : ℝ) / 14) / 4 ≤ (t : ℝ) := by linarith [ht, hx14ge]
      linarith [htge]
    have hsqrtpos : 0 < Real.sqrt (t : ℝ) := by
      have hpos : (0 : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 28) / 2 := by positivity
      linarith
    have hsqr2 : (2 * Cpp) / (x : ℝ) ^ ((1 : ℝ) / 28)
        ≤ 1 / (3 * (Real.log (x : ℝ)) ^ A) := by
      rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hxpos _) (by positivity)]
      nlinarith [hbig1]
    have hsqrt_eq : Real.sqrt (t : ℝ) = (t : ℝ) / Real.sqrt (t : ℝ) := by
      rw [eq_div_iff hsqrtpos.ne']
      exact Real.mul_self_sqrt (Nat.cast_nonneg t)
    calc Cpp * Real.sqrt (t : ℝ) = Cpp * ((t : ℝ) / Real.sqrt (t : ℝ)) := by
          nth_rewrite 1 [hsqrt_eq]
          rfl
      _ = Cpp * (t : ℝ) / Real.sqrt (t : ℝ) := by ring
      _ ≤ Cpp * T / ((x : ℝ) ^ ((1 : ℝ) / 28) / 2) := by
          have hnum : Cpp * (t : ℝ) ≤ Cpp * T := mul_le_mul_of_nonneg_left htT hCppnonneg
          calc Cpp * (t : ℝ) / Real.sqrt (t : ℝ)
              ≤ Cpp * T / Real.sqrt (t : ℝ) := div_le_div_of_nonneg_right hnum hsqrtpos.le
            _ ≤ Cpp * T / ((x : ℝ) ^ ((1 : ℝ) / 28) / 2) :=
                div_le_div_of_nonneg_left (by positivity) (by positivity) hsqr
      _ = T * ((2 * Cpp) / (x : ℝ) ^ ((1 : ℝ) / 28)) := by
          field_simp
      _ ≤ T * (1 / (3 * (Real.log (x : ℝ)) ^ A)) :=
          mul_le_mul_of_nonneg_left hsqr2 hTnonneg
      _ = T / (3 * (Real.log (x : ℝ)) ^ A) := by ring
  have hsum : T / (3 * (Real.log (x : ℝ)) ^ A) + T / (3 * (Real.log (x : ℝ)) ^ A)
      + T / (3 * (Real.log (x : ℝ)) ^ A) = T / (Real.log (x : ℝ)) ^ A := by
    field_simp
    ring
  rw [← hsum]
  linarith [h1, h2, h3]

/-! ## The main theorem -/

theorem primeCharSumBound (A C : ℝ) (hA : 0 < A) (hC : 0 < C) :
    ∀ᶠ x : ℕ in Filter.atTop,
      ∀ {c : ℕ}, 2 ≤ c → c ≤ ⌊(Real.log (x : ℝ)) ^ C⌋₊ →
      ∀ χ : DirichletCharacter ℂ c, χ.IsPrimitive → χ ≠ 1 →
      ∀ T : ℝ, (x : ℝ) ^ ((1 : ℝ) / 14) ≤ T → T ≤ (x : ℝ) →
        ‖∑ p ∈ (Finset.Icc 1 ⌊T⌋₊).filter (fun p => p.Prime), χ (p : ZMod c)‖
          ≤ T / (Real.log (x : ℝ)) ^ A := by
  obtain ⟨Cpp, hCpppos, hCpp⟩ := exists_nonprime_vonMangoldt_sum_bound
  filter_upwards [uniform_vonMangoldt_bound A C hA hC,
    eventually_const_le_nat_log (300 * 15 ^ (A + 1)),
    eventually_nat_log_pow_mul_le_rpow A (1 / 28) hA (by norm_num) (6 * Cpp),
    eventually_nat_log_pow_mul_le_rpow A (1 / 210) hA (by norm_num) 9]
    with x hunif hxlog hbig1 hbig2
  intro c hc2 hcC χ hprim h1ne T hTlo hThi
  set t : ℕ := ⌊T⌋₊ with htdef
  set Y : ℕ := ⌈(x : ℝ) ^ ((1 : ℝ) / 15)⌉₊ + 1 with hYdef
  set L : ℝ := (Real.log (x : ℝ) / 15) ^ (A + 1) with hLdef
  set cseq : ℕ → ℂ :=
    fun i => χ (i : ZMod c) * ((ArithmeticFunction.vonMangoldt i : ℝ) : ℂ) with hcseq
  have hTnonneg : (0 : ℝ) ≤ T := le_trans (Real.rpow_nonneg (Nat.cast_nonneg x) _) hTlo
  have h15A1 : (1 : ℝ) ≤ 15 ^ (A + 1) := Real.one_le_rpow (by norm_num) (by linarith)
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    by_contra hcon
    push_neg at hcon
    have hlog0 : Real.log (x : ℝ) ≤ 0 := Real.log_nonpos (Nat.cast_nonneg x) hcon.le
    linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le one_pos hx1
  have hlogx1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by linarith
  have hlogpos : (0 : ℝ) < Real.log (x : ℝ) := by linarith
  have hLpos : 0 < L := by rw [hLdef]; exact Real.rpow_pos_of_pos (by positivity) _
  have hlogpow1 : (1 : ℝ) ≤ (Real.log (x : ℝ)) ^ A := Real.one_le_rpow hlogx1 hA.le
  have hx210 : (9 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 210) := by linarith [hbig2, hlogpow1]
  have hx15ge : (9 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 15) :=
    le_trans hx210 (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))
  have hx15pos : (0 : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 15) := Real.rpow_pos_of_pos hxpos _
  have hx14ge : (4 / 3 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 14) :=
    le_trans (by norm_num) (le_trans hx210
      (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)))
  have hx14split : (x : ℝ) ^ ((1 : ℝ) / 14)
      = (x : ℝ) ^ ((1 : ℝ) / 15) * (x : ℝ) ^ ((1 : ℝ) / 210) := by
    rw [← Real.rpow_add hxpos]; congr 1; norm_num
  -- facts about `t`
  have htT : (t : ℝ) ≤ T := by
    rw [htdef]; exact Nat.floor_le hTnonneg
  have htgt : T - 1 < (t : ℝ) := by
    rw [htdef]
    have := Nat.lt_floor_add_one T
    linarith
  -- facts about `Y`
  have hYle : (Y : ℝ) ≤ 3 * (x : ℝ) ^ ((1 : ℝ) / 15) := by
    rw [hYdef]
    have hceil : ((⌈(x : ℝ) ^ ((1 : ℝ) / 15)⌉₊ : ℕ) : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 15) + 1 :=
      Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg x) _)
    push_cast
    linarith
  have hY3 : 3 ≤ Y := by
    rw [hYdef]
    have hceil : (9 : ℝ) ≤ ((⌈(x : ℝ) ^ ((1 : ℝ) / 15)⌉₊ : ℕ) : ℝ) :=
      le_trans hx15ge (Nat.le_ceil _)
    have h9 : (9 : ℕ) ≤ ⌈(x : ℝ) ^ ((1 : ℝ) / 15)⌉₊ := by exact_mod_cast hceil
    omega
  have hYt : Y + 1 ≤ t := by
    have h1 : ((Y + 1 : ℕ) : ℝ) ≤ 3 * (x : ℝ) ^ ((1 : ℝ) / 15) + 1 := by
      push_cast; linarith [hYle]
    have h2 : 3 * (x : ℝ) ^ ((1 : ℝ) / 15) + 1 ≤ (t : ℝ) := by
      have h3 : 3 * (x : ℝ) ^ ((1 : ℝ) / 15) + 1 ≤ 9 * (x : ℝ) ^ ((1 : ℝ) / 15) - 1 := by
        linarith [hx15ge]
      have h4 : 9 * (x : ℝ) ^ ((1 : ℝ) / 15) - 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 14) - 1 := by
        have : 9 * (x : ℝ) ^ ((1 : ℝ) / 15) ≤ (x : ℝ) ^ ((1 : ℝ) / 14) := by
          rw [hx14split]
          nlinarith [hx210, hx15pos]
        linarith
      linarith [h3, h4, htgt, hTlo]
    have : ((Y + 1 : ℕ) : ℝ) ≤ (t : ℝ) := le_trans h1 h2
    exact_mod_cast this
  -- the uniform bound at every `n` in the range `[Y+1, t+1]`
  have hGn : ∀ n : ℕ, Y + 1 ≤ n → n ≤ t + 1 → ‖∑ i ∈ Finset.range n, cseq i‖ ≤ (1 / L) * n := by
    intro n hn1 hn2
    have hYval : ⌈(x : ℝ) ^ ((1 : ℝ) / 15)⌉₊ + 2 ≤ n := by
      have : Y + 1 ≤ n := hn1
      rw [hYdef] at this
      omega
    have hxn : (x : ℝ) ^ ((1 : ℝ) / 15) + 1 < (n : ℝ) := by
      have hcast : ((⌈(x : ℝ) ^ ((1 : ℝ) / 15)⌉₊ + 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hYval
      have hceil : (x : ℝ) ^ ((1 : ℝ) / 15) ≤ ((⌈(x : ℝ) ^ ((1 : ℝ) / 15)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      push_cast at hcast
      linarith
    have hnx : n ≤ x + 1 := by
      have htx : t ≤ x := by
        have : (t : ℝ) ≤ (x : ℝ) := le_trans htT hThi
        exact_mod_cast this
      omega
    have hb := hunif hc2 hcC χ hprim h1ne n hxn hnx
    have hsum_eq : (∑ i ∈ Finset.range n, cseq i)
        = ∑ i ∈ Finset.range n,
            ((ArithmeticFunction.vonMangoldt i : ℝ) : ℂ) * χ (i : ZMod c) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      simp only [hcseq, mul_comm]
    rw [hsum_eq]
    calc ‖∑ i ∈ Finset.range n,
          ((ArithmeticFunction.vonMangoldt i : ℝ) : ℂ) * χ (i : ZMod c)‖
        ≤ (n : ℝ) / (Real.log (x : ℝ) / 15) ^ (A + 1) := hb
      _ = (1 / L) * n := by rw [hLdef]; ring
  -- the three pieces of the split
  have hpiece1 : ‖∑ i ∈ Finset.Ico 1 (Y + 1), ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i‖ ≤ (Y : ℝ) := by
    simpa only [hcseq] using small_part_le c Y χ
  have hpiece2 : ‖∑ i ∈ Finset.Ico (Y + 1) (t + 1), ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i‖
      ≤ 100 * (1 / L) * t :=
    abelLogWeightBound cseq (1 / L) t Y (by positivity) hY3 hYt hGn
  have hIco : Finset.Ico 1 (t + 1) = Finset.Icc 1 t := by
    ext i; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  have hnonprimeEq :
      (∑ i ∈ (Finset.Ico 1 (t + 1)).filter (fun i => ¬ i.Prime),
          ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i)
        = ∑ i ∈ (Finset.Icc 1 t).filter (fun i => ¬ i.Prime),
            χ (i : ZMod c) * ((ArithmeticFunction.vonMangoldt i : ℝ) : ℂ) *
              (((Real.log (i : ℝ))⁻¹ : ℝ) : ℂ) := by
    rw [hIco]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp only [hcseq, Complex.real_smul]
    ring
  have hpiece3 : ‖∑ i ∈ (Finset.Ico 1 (t + 1)).filter (fun i => ¬ i.Prime),
      ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i‖ ≤ Cpp * Real.sqrt (t : ℝ) := by
    rw [hnonprimeEq]
    exact chiLambdaNonprimeSumBound Cpp hCpp c t χ
  have htarget_eq : (∑ p ∈ (Finset.Icc 1 t).filter (fun p => p.Prime), χ (p : ZMod c))
      = (∑ i ∈ Finset.Ico 1 (t + 1), ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i)
        - (∑ i ∈ (Finset.Ico 1 (t + 1)).filter (fun i => ¬ i.Prime),
            ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i) := by
    have hprimeSum : (∑ i ∈ (Finset.Ico 1 (t + 1)).filter (fun i => i.Prime),
          ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i)
        = ∑ p ∈ (Finset.Icc 1 t).filter (fun p => p.Prime), χ (p : ZMod c) := by
      rw [hIco]
      refine Finset.sum_congr rfl ?_
      intro p hp
      exact smul_prime_eq c χ (Finset.mem_filter.mp hp).2
    have hsplit : (∑ i ∈ Finset.Ico 1 (t + 1), ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i)
        = (∑ i ∈ (Finset.Ico 1 (t + 1)).filter (fun i => i.Prime),
              ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i)
          + (∑ i ∈ (Finset.Ico 1 (t + 1)).filter (fun i => ¬ i.Prime),
              ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i) :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    rw [hsplit, ← hprimeSum]
    abel
  have hSsplit : (∑ i ∈ Finset.Ico 1 (t + 1), ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i)
      = (∑ i ∈ Finset.Ico 1 (Y + 1), ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i)
        + (∑ i ∈ Finset.Ico (Y + 1) (t + 1), ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i) :=
    (Finset.sum_Ico_consecutive (fun i => ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i)
      (by omega : 1 ≤ Y + 1) (by omega : Y + 1 ≤ t + 1)).symm
  have hmain : ‖∑ p ∈ (Finset.Icc 1 t).filter (fun p => p.Prime), χ (p : ZMod c)‖
      ≤ (Y : ℝ) + 100 * (1 / L) * t + Cpp * Real.sqrt (t : ℝ) := by
    have hS : ‖∑ i ∈ Finset.Ico 1 (t + 1), ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i‖
        ≤ (Y : ℝ) + 100 * (1 / L) * t := by
      rw [hSsplit]
      calc ‖(∑ i ∈ Finset.Ico 1 (Y + 1), ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i)
            + (∑ i ∈ Finset.Ico (Y + 1) (t + 1), ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i)‖
          ≤ ‖∑ i ∈ Finset.Ico 1 (Y + 1), ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i‖
            + ‖∑ i ∈ Finset.Ico (Y + 1) (t + 1), ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i‖ :=
            norm_add_le _ _
        _ ≤ (Y : ℝ) + 100 * (1 / L) * t := add_le_add hpiece1 hpiece2
    calc ‖∑ p ∈ (Finset.Icc 1 t).filter (fun p => p.Prime), χ (p : ZMod c)‖
        = ‖(∑ i ∈ Finset.Ico 1 (t + 1), ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i)
            - (∑ i ∈ (Finset.Ico 1 (t + 1)).filter (fun i => ¬ i.Prime),
                ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i)‖ := by rw [htarget_eq]
      _ ≤ ‖∑ i ∈ Finset.Ico 1 (t + 1), ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i‖
            + ‖∑ i ∈ (Finset.Ico 1 (t + 1)).filter (fun i => ¬ i.Prime),
                ((Real.log (i : ℝ))⁻¹ : ℝ) • cseq i‖ := norm_sub_le _ _
      _ ≤ ((Y : ℝ) + 100 * (1 / L) * t) + Cpp * Real.sqrt (t : ℝ) :=
          add_le_add hS hpiece3
  have hfinal : (Y : ℝ) + 100 * (1 / L) * t + Cpp * Real.sqrt (t : ℝ)
      ≤ T / (Real.log (x : ℝ)) ^ A := by
    rw [hLdef]
    exact final_arith A hA Cpp hCpppos.le hxlog hbig1 hbig2 hTlo htgt htT hYle
  linarith [hmain, hfinal]

end Work.NumberTheory.Chen.BTermCount
