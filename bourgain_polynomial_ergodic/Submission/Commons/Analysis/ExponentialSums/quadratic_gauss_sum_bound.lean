import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.Analysis.ExponentialSums.norm_sum_sq_le_shift_conj

namespace Commons.Analysis.ExponentialSums

open Finset
open scoped BigOperators ComplexConjugate

/-- `e(m/q) = 1` if and only if `q ∣ m`, for `q > 0`. -/
private lemma exp_two_pi_I_int_div_eq_one (q : ℕ) (hq : 0 < q) (m : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) / (q : ℂ))) = 1 ↔ (q : ℤ) ∣ m := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hA : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hcomm : (2 * Real.pi * Complex.I : ℂ) * ((m : ℂ) / (q : ℂ))
        = ((m : ℂ) / (q : ℂ)) * (2 * Real.pi * Complex.I) := by ring
    rw [hcomm] at hn
    have h1 : ((m : ℂ) / (q : ℂ)) = (n : ℂ) := mul_right_cancel₀ hA hn
    have h2 : (m : ℂ) = (n : ℂ) * (q : ℂ) := by
      rw [div_eq_iff hqC] at h1; exact h1
    have h3 : (m : ℂ) = ((n * q : ℤ) : ℂ) := by rw [h2]; push_cast; ring
    have h4 : m = n * q := Int.cast_injective h3
    exact ⟨n, by rw [h4]; ring⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hm : (m : ℂ) = (n : ℂ) * (q : ℂ) := by rw [hn]; push_cast; ring
    rw [hm]
    rw [mul_div_cancel_right₀ _ hqC]
    ring

/-- Conjugation inverts the phase `e(t) = exp (2 π i t)` for real `t`. -/
private lemma conj_exp_two_pi_I (t : ℝ) :
    conj (Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))
      = Complex.exp (2 * Real.pi * Complex.I * ((-t : ℝ) : ℂ)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

/-- The phase `e(t) = exp (2 π i t)` has modulus one. -/
private lemma norm_exp_two_pi_I (t : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))‖ = 1 := by
  have h : 2 * Real.pi * Complex.I * (t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The real phase `y ↦ a y² / q` of the quadratic exponential sum. -/
private noncomputable def ps (q : ℕ) (a : ℤ) (y : ℤ) : ℝ := (a : ℝ) * (y : ℝ) ^ 2 / (q : ℝ)

/-- The summand `y ↦ e(a y²/q)` of the quadratic exponential sum. -/
private noncomputable def Fu (q : ℕ) (a : ℤ) (y : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (ps q a y : ℂ))

/-- Splitting identity: the shifted conjugate product is the diagonal phase times a
geometric-power term. -/
private lemma Fu_mul_conj (q : ℕ) (a : ℤ) (x h : ℕ) :
    Fu q a ((x : ℤ) + (h : ℤ)) * conj (Fu q a (x : ℤ))
      = Complex.exp (2 * Real.pi * Complex.I * (ps q a (h : ℤ) : ℂ))
        * (Complex.exp (2 * Real.pi * Complex.I * (((2 * a * (h : ℤ) : ℤ) : ℂ) / (q : ℂ)))) ^ x := by
  rw [Fu, Fu, conj_exp_two_pi_I, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [ps]
  push_cast
  ring

/-- The geometric base `e(2ah/q)` is a `q`-th root of unity. -/
private lemma zh_pow_q (q : ℕ) (hq : 0 < q) (a : ℤ) (h : ℕ) :
    (Complex.exp (2 * Real.pi * Complex.I * (((2 * a * (h : ℤ) : ℤ) : ℂ) / (q : ℂ)))) ^ q = 1 := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [← Complex.exp_nat_mul]
  rw [show (q : ℂ) * (2 * Real.pi * Complex.I * (((2 * a * (h : ℤ) : ℤ) : ℂ) / (q : ℂ)))
        = ((2 * a * (h : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
      field_simp]
  rw [Complex.exp_eq_one_iff]
  exact ⟨2 * a * (h : ℤ), rfl⟩

/-- A complete geometric sum of a `q`-th root of unity vanishes unless the base is `1`. -/
private lemma geom_sum_pow_eq_zero (q : ℕ) (w : ℂ) (hw : w ≠ 1) (hwq : w ^ q = 1) :
    ∑ x ∈ Finset.range q, w ^ x = 0 := by
  rw [geom_sum_eq hw q, hwq]; simp

/-- Norm bound for a complete geometric sum of a `q`-th root of unity. -/
private lemma norm_geom_sum_pow_le (q : ℕ) (w : ℂ) (hwq : w ^ q = 1) :
    ‖∑ x ∈ Finset.range q, w ^ x‖ ≤ if w = 1 then (q : ℝ) else 0 := by
  by_cases hw : w = 1
  · rw [if_pos hw, hw]; simp
  · rw [if_neg hw, geom_sum_pow_eq_zero q w hw hwq]; simp

/-- Counting bound: among the residues `h < q`, at most two satisfy `q ∣ 2 a h` when
`gcd a q = 1`. -/
private lemma card_filter_le_two (q : ℕ) (a : ℤ) (hq : 0 < q) (hgcd : Int.gcd a (q : ℤ) = 1) :
    ((((Finset.range q).filter (fun h : ℕ => (q : ℤ) ∣ 2 * a * (h : ℤ)))).card : ℝ) ≤ 2 := by
  set S := (Finset.range q).filter (fun h : ℕ => (q : ℤ) ∣ 2 * a * (h : ℤ)) with hS
  have hinj : Function.Injective (fun h : ℕ => 2 * h) := by
    intro p r hpr; simp only at hpr; omega
  have himg : S.image (fun h : ℕ => 2 * h) ⊆ ({0, q} : Finset ℕ) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨h, hh, rfl⟩ := hy
    rw [Finset.mem_filter, Finset.mem_range] at hh
    obtain ⟨hhlt, hdiv⟩ := hh
    have hcop : IsCoprime (q : ℤ) a := (Int.isCoprime_iff_gcd_eq_one.mpr hgcd).symm
    have hdiv' : (q : ℤ) ∣ (2 * (h : ℤ)) * a := by
      convert hdiv using 1; ring
    have hq2h : (q : ℤ) ∣ 2 * (h : ℤ) := IsCoprime.dvd_of_dvd_mul_right hcop hdiv'
    have hq2hN : q ∣ 2 * h := by
      have hcast : (2 * (h : ℤ)) = ((2 * h : ℕ) : ℤ) := by push_cast; ring
      rw [hcast] at hq2h
      exact_mod_cast hq2h
    obtain ⟨k, hk⟩ := hq2hN
    have hlt : 2 * h < 2 * q := by omega
    have hk2 : k < 2 := by
      have hqk : q * k < q * 2 := by rw [← hk, mul_comm q 2]; exact hlt
      exact (Nat.mul_lt_mul_left hq).mp hqk
    have hk01 : k = 0 ∨ k = 1 := by omega
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hk01 with h0 | h1
    · left; rw [h0] at hk; simpa using hk
    · right; rw [h1] at hk; simpa using hk
  calc (S.card : ℝ) = ((S.image (fun h : ℕ => 2 * h)).card : ℝ) := by
        rw [Finset.card_image_of_injective S hinj]
      _ ≤ (({0, q} : Finset ℕ).card : ℝ) := by exact_mod_cast Finset.card_le_card himg
      _ ≤ 2 := by
        have : ({0, q} : Finset ℕ).card ≤ 2 := by
          have h := Finset.card_insert_le 0 ({q} : Finset ℕ)
          rw [Finset.card_singleton] at h
          simpa using h
        exact_mod_cast this

/-- **Uniform bound on the quadratic Gauss sum.**  For `q ≥ 1` and `gcd a q = 1`, the
complete quadratic exponential sum `∑_{r<q} e(a r²/q)` is `≲ √q`; this is the weight
`S(a/q)` of the major-arc approximation of the square-averages multiplier (Bourgain,
*Pointwise ergodic theorems for arithmetic sets* §6). -/
theorem quadratic_gauss_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (a : ℤ), 0 < q → Int.gcd a (q : ℤ) = 1 →
      ‖∑ r ∈ Finset.range q,
          Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (r : ℂ) ^ 2 / (q : ℂ)))‖
        ≤ C * Real.sqrt (q : ℝ) := by
  refine ⟨Real.sqrt 2, Real.sqrt_pos.mpr (by norm_num), ?_⟩
  intro q a hq hgcd
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hsum : (∑ r ∈ Finset.range q,
        Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (r : ℂ) ^ 2 / (q : ℂ))))
      = ∑ r ∈ Finset.range q, Fu q a r := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [Fu]
    congr 1
    simp only [ps]
    push_cast
    ring
  rw [hsum]
  have hper : ∀ y : ℤ, Fu q a (y + q) = Fu q a y := by
    intro y
    rw [Fu, Fu, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨2 * a * y + a * q, ?_⟩
    simp only [ps]
    push_cast
    field_simp
    ring
  have hweyl := norm_sum_sq_le_shift_conj q hq (Fu q a) hper
  have hinner : ∀ h ∈ Finset.range q,
      ‖∑ x ∈ Finset.range q, Fu q a (x + h) * conj (Fu q a x)‖
        ≤ if (q : ℤ) ∣ 2 * a * (h : ℤ) then (q : ℝ) else 0 := by
    intro h _
    set zh : ℂ := Complex.exp (2 * Real.pi * Complex.I * (((2 * a * (h : ℤ) : ℤ) : ℂ) / (q : ℂ)))
      with hzh
    have hterm : (∑ x ∈ Finset.range q, Fu q a (x + h) * conj (Fu q a x))
        = ∑ x ∈ Finset.range q,
            Complex.exp (2 * Real.pi * Complex.I * (ps q a (h : ℤ) : ℂ)) * zh ^ x := by
      apply Finset.sum_congr rfl
      intro x _
      have := Fu_mul_conj q a x h
      simpa [hzh] using this
    rw [hterm, ← Finset.mul_sum, norm_mul, norm_exp_two_pi_I, one_mul]
    have hzif : (zh = 1) ↔ (q : ℤ) ∣ 2 * a * (h : ℤ) := by
      rw [hzh]; exact exp_two_pi_I_int_div_eq_one q hq (2 * a * (h : ℤ))
    have hb := norm_geom_sum_pow_le q zh (by rw [hzh]; exact zh_pow_q q hq a h)
    by_cases hd : (q : ℤ) ∣ 2 * a * (h : ℤ)
    · rw [if_pos hd]
      rw [if_pos (hzif.mpr hd)] at hb
      exact hb
    · rw [if_neg hd]
      rw [if_neg (fun hh => hd (hzif.mp hh))] at hb
      exact hb
  have hsum2 : (∑ h ∈ Finset.range q,
      ‖∑ x ∈ Finset.range q, Fu q a (x + h) * conj (Fu q a x)‖) ≤ 2 * (q : ℝ) := by
    calc (∑ h ∈ Finset.range q, ‖∑ x ∈ Finset.range q, Fu q a (x + h) * conj (Fu q a x)‖)
        ≤ ∑ h ∈ Finset.range q, (if (q : ℤ) ∣ 2 * a * (h : ℤ) then (q : ℝ) else 0) :=
          Finset.sum_le_sum hinner
      _ = (((Finset.range q).filter (fun h : ℕ => (q : ℤ) ∣ 2 * a * (h : ℤ))).card : ℝ) * (q : ℝ) := by
          rw [← Finset.sum_filter]
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (q : ℝ) := by
          have hc := card_filter_le_two q a hq hgcd
          have hqnn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
          nlinarith [hc, hqnn]
  have hG2 : ‖∑ r ∈ Finset.range q, Fu q a r‖ ^ 2 ≤ 2 * (q : ℝ) := le_trans hweyl hsum2
  calc ‖∑ r ∈ Finset.range q, Fu q a r‖
      = Real.sqrt (‖∑ r ∈ Finset.range q, Fu q a r‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (2 * (q : ℝ)) := Real.sqrt_le_sqrt hG2
    _ = Real.sqrt 2 * Real.sqrt (q : ℝ) := Real.sqrt_mul (by norm_num) (q : ℝ)

end Commons.Analysis.ExponentialSums