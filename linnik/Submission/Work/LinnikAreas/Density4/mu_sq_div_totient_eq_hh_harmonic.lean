import Mathlib
import Submission.Work.LinnikAreas.Density4.MuSqTotientDefs
import Submission.Work.LinnikAreas.Density4.hh_prime_pow_sum
import Submission.Work.LinnikAreas.Density4.faf_prime_pow
import Submission.Work.LinnikAreas.Density4.sum_Icc_one_div_eq_harmonic
import Submission.Work.LinnikAreas.Density4.sum_Icc_div_reindex

/-!
# `Σ_{n ≤ z} μ(n)²/φ(n) = Σ_{e ≤ z} h(e) · H_{⌊z/e⌋}`

The convolution identity `n·μ(n)²/φ(n) = Σ_{e ∣ n} e·h(e)` (with `h = hh` the sharp
Mertens weight, `h(p) = 1/(p(p-1))`, `h(p²) = -1/(p(p-1))`, `h(p^j) = 0` for `j ≥ 3`)
turns the Mertens sum into a harmonic sum: writing `n = e·m` and summing over pairs,
`Σ_{n ≤ z} μ(n)²/φ(n) = Σ_{e ≤ z} h(e) Σ_{m ≤ z/e} 1/m = Σ_{e ≤ z} h(e)·H_{⌊z/e⌋}`.
-/

open Finset BigOperators

namespace Work.LinnikAreas.Density4

noncomputable section

/-- The arithmetic function `n ↦ n·h(n)`. -/
private noncomputable def Gaf : ArithmeticFunction ℝ :=
  ⟨fun n => (n : ℝ) * hh n, by simp⟩

/-- The arithmetic function `n ↦ n·μ(n)²/φ(n)`. -/
private noncomputable def Faf : ArithmeticFunction ℝ :=
  ⟨fun n => (n : ℝ) * (((ArithmeticFunction.moebius n : ℤ) : ℝ)) ^ 2 / (Nat.totient n : ℝ),
    by simp⟩

private lemma isMult_Gaf : ArithmeticFunction.IsMultiplicative Gaf := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp only [Gaf, ArithmeticFunction.coe_mk]
    rw [hh_one]; norm_num
  · intro m n hm hn hcop
    simp only [Gaf, ArithmeticFunction.coe_mk]
    rw [hh_mul m n hm hn hcop]
    push_cast
    ring

private lemma isMult_Faf : ArithmeticFunction.IsMultiplicative Faf := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp only [Faf, ArithmeticFunction.coe_mk]
    norm_num
  · intro m n hm hn hcop
    simp only [Faf, ArithmeticFunction.coe_mk]
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop, Nat.totient_mul hcop]
    have hmφ : (Nat.totient m : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)).ne'
    have hnφ : (Nat.totient n : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
    push_cast
    field_simp

/-- The Dirichlet convolution of `n ↦ n·h(n)` with `1` at `n` is the divisor sum `Σ_{e ∣ n} e·h(e)`. -/
private lemma Gaf_mul_zeta_apply (n : ℕ) :
    (Gaf * (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n
      = ∑ e ∈ n.divisors, (e : ℝ) * hh e := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  simp only [Gaf, ArithmeticFunction.coe_mk]

/-- `n ↦ n·h(n)` convolved with `1` is `n ↦ n·μ(n)²/φ(n)`. -/
private lemma Gaf_mul_zeta_eq_Faf :
    Gaf * (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ) = Faf := by
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMult_Gaf.mul ArithmeticFunction.isMultiplicative_zeta.natCast) _ isMult_Faf).mpr ?_
  intro p i hp
  rw [Gaf_mul_zeta_apply, Nat.divisors_prime_pow hp i, Finset.sum_map]
  simp only [Faf, ArithmeticFunction.coe_mk, Function.Embedding.coeFn_mk, Nat.cast_pow]
  rw [hh_prime_pow_sum p i hp, faf_prime_pow p i hp]

/-- **Convolution identity**: `Σ_{e ∣ n} e·h(e) = n·μ(n)²/φ(n)`. -/
private lemma hh_divisor_sum (n : ℕ) :
    (∑ e ∈ n.divisors, (e : ℝ) * hh e)
      = (n : ℝ) * (((ArithmeticFunction.moebius n : ℤ) : ℝ)) ^ 2 / (Nat.totient n : ℝ) := by
  have h := Gaf_mul_zeta_apply n
  rw [Gaf_mul_zeta_eq_Faf] at h
  simp only [Faf, ArithmeticFunction.coe_mk] at h
  exact h.symm

/-- The convolution identity in reciprocal form. -/
private lemma mu_sq_div_totient_eq_sum_divisors_recip (n : ℕ) (hn : 1 ≤ n) :
    (((ArithmeticFunction.moebius n : ℤ) : ℝ)) ^ 2 / (Nat.totient n : ℝ)
      = ∑ e ∈ n.divisors, hh e * (1 / ((n / e : ℕ) : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hS : (n : ℝ) * (∑ e ∈ n.divisors, hh e * (1 / ((n / e : ℕ) : ℝ)))
      = ∑ e ∈ n.divisors, (e : ℝ) * hh e := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e he => ?_)
    obtain ⟨hdvd, hnz⟩ := Nat.mem_divisors.mp he
    have he0 : e ≠ 0 := fun h => hnz (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
    have heR : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he0
    have hcast : ((n / e : ℕ) : ℝ) = (n : ℝ) / (e : ℝ) := Nat.cast_div hdvd heR
    rw [hcast, one_div]
    field_simp
  refine mul_left_cancel₀ hn0 ?_
  rw [← mul_div_assoc, ← hh_divisor_sum n]
  exact hS.symm

theorem mu_sq_div_totient_eq_hh_harmonic (z : ℕ) :
    (∑ n ∈ Finset.Icc 1 z, ((ArithmeticFunction.moebius n : ℤ) : ℝ)^2 / (Nat.totient n : ℝ))
      = ∑ e ∈ Finset.Icc 1 z, hh e * (harmonic (z / e) : ℝ) := by
  have hstep :
      (∑ n ∈ Finset.Icc 1 z, ((ArithmeticFunction.moebius n : ℤ) : ℝ)^2 / (Nat.totient n : ℝ))
        = ∑ n ∈ Finset.Icc 1 z, ∑ e ∈ n.divisors, hh e * (1 / ((n / e : ℕ) : ℝ)) := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    exact mu_sq_div_totient_eq_sum_divisors_recip n (Finset.mem_Icc.mp hn).1
  rw [hstep]
  have hre := sum_Icc_div_reindex z (fun _ : ℕ => True) (fun d m => hh d * (1 / ((m : ℕ) : ℝ)))
  simp only [Finset.filter_true] at hre
  rw [← hre]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [← Finset.mul_sum, sum_Icc_one_div_eq_harmonic]

end

end Work.LinnikAreas.Density4
