/-
# FI §15: the vocabulary of the *box energy* (the closing estimate of Proposition 15.1)

This module only contains the `d₂`-function used by the two lemmas into which the box-energy
estimate `S15_box_energy2` is split:

* `Work.FIArea4.S15_polar_joint_count` — the joint lattice count
  `#{z ∈ polarBox : L ∣ re z, d ∣ |z|²} ≤ C·(A/d + 1)·(A/L + 1)·2^{ω(d)}·d₂(d)`,
  `A = 10θ√N` (the diameter of the polar box), obtained by fibring the box over `re z` and using
  the bound `#{α mod d : α² + re² ≡ 0} ≤ 2 ^ ω(d) · gcd (re, d₂(d))`;

* `Work.FIArea4.S15_tau10_d2_sum` — the divisor sum `Σ_{d ≤ Y} τ(d)^{10}·2^{ω(d)}·d₂(d)/d ≪
  (log Y)^B` with an explicit `B ≤ 9·10^5`.
-/
import Mathlib
import Submission.Work.FIArea4.S15_hard_defs
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_sum_sq_root_count_le_two_pow_omega
import Submission.Commons.NumberTheory.Divisors.sum_tau_pow_div_le
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound_ge_three
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
import Submission.Commons.NumberTheory.Divisors.small_divisor_tau_le
import Submission.Commons.NumberTheory.DivisorSum.tau_pow_eight_le_sum_dvd_cube
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FIArea4.S15box

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

open Finset

/-- `d₂(d) = ∏_{p ∣ d} p ^ (v_p(d) / 2)`, the square root of the largest square divisor of `d`.
(Equal to `Nat.floorRoot 2 d`; it appears in the bound
`#{α : ZMod d | α² + b² = 0} ≤ 2 ^ ω(d) · gcd (b, d₂(d))`.) -/
def S15d2 (d : ℕ) : ℕ := (d.primeFactors).prod (fun p => p ^ (d.factorization p / 2))

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary facts about `gnorm` -/

lemma gnorm_eq (z : GaussianInt) :
    Work.FIPlan.gnorm z = z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
  have hn : Zsqrtd.norm z = z.re * z.re + z.im * z.im := by
    rw [Zsqrtd.norm_def]; ring
  have h1 : (z.re * z.re).natAbs = z.re.natAbs ^ 2 := by
    rw [← Int.natAbs_mul_self (a := z.re), Int.natAbs_natCast]; ring
  have h2 : (z.im * z.im).natAbs = z.im.natAbs ^ 2 := by
    rw [← Int.natAbs_mul_self (a := z.im), Int.natAbs_natCast]; ring
  have hsum : (z.re * z.re + z.im * z.im).natAbs
      = (z.re * z.re).natAbs + (z.im * z.im).natAbs := by
    apply Int.natAbs_add_of_nonneg
    · exact mul_self_nonneg _
    · exact mul_self_nonneg _
  simp only [Work.FIPlan.gnorm, hn, hsum, h1, h2]

lemma re_sq_le_gnorm (z : GaussianInt) : z.re.natAbs ^ 2 ≤ Work.FIPlan.gnorm z := by
  rw [gnorm_eq]; exact Nat.le_add_right _ _

lemma natAbs_re_le_gnorm (z : GaussianInt) : z.re.natAbs ≤ Work.FIPlan.gnorm z := by
  have h := re_sq_le_gnorm z
  nlinarith [Nat.zero_le z.re.natAbs, Nat.zero_le (Work.FIPlan.gnorm z)]

/-! ## FI Lemma 2.2 in the two forms used by the closing estimate -/

/-- `τ(n)³` dominated by a sum over the *small* divisors `L` with `L² ≤ n`. -/
lemma tau_cube_le_sum_divisors_sq (n : ℕ) (hn : 1 ≤ n) :
    (((n.divisors.card : ℕ) : ℝ)) ^ 3
      ≤ ∑ L ∈ n.divisors.filter (fun L => L ^ 2 ≤ n), (2 * ((L.divisors.card : ℕ) : ℝ)) ^ 6 := by
  obtain ⟨d, hdvd, hdsq, hbound⟩ :=
    Commons.NumberTheory.Divisors.small_divisor_tau_le (k := 2) (by norm_num) hn
  have h2 : Real.log 2 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have h2' : Real.log ((2:ℕ):ℝ) ≠ 0 := by simpa using h2
  have he : (((2:ℕ):ℝ) * Real.log ((2:ℕ):ℝ) / Real.log 2) = ((2:ℕ):ℝ) := by
    rw [div_eq_iff h2]
    norm_num
  have hb : ((n.divisors.card : ℕ) : ℝ) ≤ (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 2 := by
    rw [he, Real.rpow_natCast] at hbound
    exact hbound
  have hcube : (((n.divisors.card : ℕ) : ℝ)) ^ 3
      ≤ (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 6 := by
    calc (((n.divisors.card : ℕ) : ℝ)) ^ 3
        = (((n.divisors.card : ℕ) : ℝ)) * (((n.divisors.card : ℕ) : ℝ))
            * (((n.divisors.card : ℕ) : ℝ)) := by ring
      _ ≤ (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 2 * (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 2
            * (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 2 :=
          mul_le_mul (mul_le_mul hb hb (by positivity) (by positivity)) hb
            (by positivity) (by positivity)
      _ = (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 6 := by ring_nf
  have hdmem : d ∈ n.divisors.filter (fun L => L ^ 2 ≤ n) := by
    rw [Finset.mem_filter]
    exact ⟨Nat.mem_divisors.mpr ⟨hdvd, by omega⟩, hdsq⟩
  refine le_trans hcube ?_
  exact Finset.single_le_sum (f := fun L => (2 * ((L.divisors.card : ℕ) : ℝ)) ^ 6)
    (fun L _ => by positivity) hdmem

/-- `τ(n)²` dominated by a sum over the divisors `d` with `d³ ≤ n`. -/
lemma tau_sq_le_sum_divisors_cube (n : ℕ) (hn : 1 ≤ n) :
    (((n.divisors.card : ℕ) : ℝ)) ^ 2
      ≤ ∑ d ∈ n.divisors.filter (fun d => d ^ 3 ≤ n), (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 10 := by
  obtain ⟨d, hdvd, hdcube, hbound⟩ :=
    Commons.NumberTheory.DivisorSum.exists_divisor_cube_le_pow_five n hn
  have hboundR : ((n.divisors.card : ℕ) : ℝ) ≤ (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 5 := by
    exact_mod_cast hbound
  have hs : (((n.divisors.card : ℕ) : ℝ)) ^ 2
      ≤ (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 10 := by
    calc (((n.divisors.card : ℕ) : ℝ)) ^ 2
        = (((n.divisors.card : ℕ) : ℝ)) * (((n.divisors.card : ℕ) : ℝ)) := by ring
      _ ≤ (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 5 * (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 5 :=
          mul_le_mul hboundR hboundR (by positivity) (by positivity)
      _ = (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 10 := by ring_nf
  have hdmem : d ∈ n.divisors.filter (fun d => d ^ 3 ≤ n) := by
    rw [Finset.mem_filter]
    exact ⟨Nat.mem_divisors.mpr ⟨hdvd, by omega⟩, hdcube⟩
  refine le_trans hs ?_
  exact Finset.single_le_sum (f := fun d => (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 10)
    (fun d _ => by positivity) hdmem

/-! ## `gnorm` of a point of the polar box -/

lemma polar_gnorm_pos (Pa : Work.FITop.Params) (φ : ℝ) {z : GaussianInt}
    (hz : z ∈ S15polarBox Pa φ) : 1 ≤ Work.FIPlan.gnorm z := by
  have h := (mem_S15polarBox.mp hz).2
  have h1 : (Pa.N : ℝ) < (Work.FIPlan.gnorm z : ℝ) := h.2.1
  have h2 : (1 : ℝ) ≤ (Pa.N : ℝ) := Pa.hN1
  have : (1 : ℝ) ≤ (Work.FIPlan.gnorm z : ℝ) := by linarith
  exact_mod_cast this

lemma polar_gnorm_le (Pa : Work.FITop.Params) (φ : ℝ) {z : GaussianInt}
    (hz : z ∈ S15polarBox Pa φ) : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := by
  have h := (mem_S15polarBox.mp hz).2
  have h1 : (Work.FIPlan.gnorm z : ℝ) ≤ (1 + Pa.θ) * Pa.N := h.2.2.1
  have hθ : Pa.θ ≤ 1 := theta_le_one Pa
  have hN : (0 : ℝ) < (Pa.N : ℝ) := by linarith [Pa.hN1]
  nlinarith [h1, hθ, hN]




end

end Work.FIArea4
