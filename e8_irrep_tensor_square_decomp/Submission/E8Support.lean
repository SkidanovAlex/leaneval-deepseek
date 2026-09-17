import Submission.E8Numerics

/-!
# The support of the candidate character `mfun`, and its determination by the norm

The candidate character `Submission.E8Numerics.mfun` is defined as

  `mfun v = if normOk v then tab (dcX v) else 0`,

i.e. by looking up the dominant conjugate `dcX v` in the table of seven dominant multiplicities,
with the shortcut that a weight whose norm `qq v = ⟪v,v⟫` is not one of `0,2,4,6,8,10` cannot be a
weight of `L(ω₁+ω₈)`.

This file proves the two structural facts recorded in the SESSION 15 roadmap section of
`Submission.lean`:

* `E8inv_ge_two`: every entry of `E8inv` is at least `2` (a `decide` check);
* `two_sum_sq_le_qZ`: for a *dominant* `ν` (`∀ i, 0 ≤ ν i`), `2 * (∑ i, ν i)^2 ≤ qq ν`
  (because `qq ν = ∑ᵢⱼ E8invᵢⱼ νᵢνⱼ` and all the terms are non-negative);
* `dominant_sum_le_two`, `mem_the7_of_norm_le`: a dominant `ν` with `qq ν ≤ 10` has coefficient sum
  `≤ 2` and is one of `the7`;
* `mfun_eq_mnorm`: **`mfun v` depends only on the norm `qq v`** — indeed on the whole lattice
  `mfun v = mnorm (qq v)` with the norm table `0 ↦ 1407, 2 ↦ 455, 4 ↦ 133, 6 ↦ 34, 8 ↦ 7, 10 ↦ 1`
  and `0` off these six values;
* `mfun_ne_zero_iff`: the support of `mfun` is exactly `{v | qq v ∈ {0,2,4,6,8,10}}` (56881 lattice
  points).

Consequences: no `dcX` evaluation is needed anywhere in the numerical treatment of the character of
`V`, which is what made the SESSION 13 numerical certification of the forty tensor-square
constituents infeasible, but leaves the SESSION 15 route (Klimyk formula plus word certificates)
open.  Also `dim V = ∑_ν mfun ν = ∑_q m_q · N_q` with `N_q = #{ν : qq ν = q}`.
-/

set_option maxHeartbeats 800000
set_option maxRecDepth 40000

namespace Submission.E8Support

open Submission.E8Enum Submission.E8Numerics Submission.E8Orbit Submission.WeylReflect
  Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo

/-- Every entry of the inverse Cartan matrix of `E₈` is at least `2`. -/
theorem E8inv_ge_two (i j : Fin 8) : 2 ≤ E8inv i j := by
  fin_cases i <;> fin_cases j <;> norm_num [E8inv]

/-- Every diagonal entry of `E8inv` is even. -/
theorem E8inv_diag_even (i : Fin 8) : 2 ∣ E8inv i i := by
  fin_cases i <;> norm_num [E8inv]

/-- For a dominant `ν`, `2 * (∑ i, ν i)^2 ≤ qq ν`. -/
theorem two_sum_sq_le_qZ (ν : Fin 8 → ℤ) (hν : ∀ i, 0 ≤ ν i) :
    2 * (∑ i, ν i) ^ 2 ≤ qq ν := by
  have hexp : (∑ i, ν i) ^ 2 = ∑ i, ∑ j, ν i * ν j := by
    rw [sq, Finset.sum_mul_sum]
  rw [hexp, qq, qZ, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h2 := E8inv_ge_two i j
  have hi := hν i
  have hj := hν j
  have hnn : 0 ≤ ν i * ν j := mul_nonneg hi hj
  nlinarith

/-- A dominant weight of norm at most `10` has coefficient sum at most `2`. -/
theorem dominant_sum_le_two (ν : Fin 8 → ℤ) (hν : ∀ i, 0 ≤ ν i) (h : qq ν ≤ 10) :
    ∑ i, ν i ≤ 2 := by
  have h2 := two_sum_sq_le_qZ ν hν
  have hs : 0 ≤ ∑ i, ν i := Finset.sum_nonneg fun i _ => hν i
  nlinarith [h2, h, hs, sq_nonneg (∑ i, ν i)]

/-- Decidable form of the norm bound `qq v ≤ 10`. -/
def qLe10 (v : Fin 8 → ℤ) : Bool := decide (qq v ≤ 10)

lemma qLe10_true {v : Fin 8 → ℤ} : qLe10 v = true ↔ qq v ≤ 10 := by
  simp [qLe10]

/-- **`decide`-check**: every *dominant* element of `candL 2` of norm `≤ 10` is one of `the7`. -/
theorem verifyNorm :
    (candL 2).all (fun v => if allNonneg v && qLe10 v then decide (v ∈ the7) else true) = true := by
  decide

/-- **A dominant weight of norm at most `10` is one of the seven.** -/
theorem mem_the7_of_norm_le (ν : Fin 8 → ℤ) (hν : ∀ i, 0 ≤ ν i) (h : qq ν ≤ 10) :
    ν ∈ the7 := by
  have hs : ∑ i, ν i ≤ 2 := dominant_sum_le_two ν hν h
  have hcand : ν ∈ candL 2 := mem_candL hν (by exact_mod_cast hs)
  have hall := List.all_eq_true.mp verifyNorm ν hcand
  have h1 : allNonneg ν = true := allNonneg_true.mpr hν
  have h2 : qLe10 ν = true := qLe10_true.mpr h
  rw [h1, h2] at hall
  simpa using hall

/-- The norm table of the seven dominant multiplicities: `mfun` is determined by the norm. -/
def mnorm (q : ℤ) : ℤ :=
  if q = 0 then 1407 else if q = 2 then 455 else if q = 4 then 133
  else if q = 6 then 34 else if q = 8 then 7 else if q = 10 then 1 else 0

lemma mnorm_eq_zero {q : ℤ} (h0 : q ≠ 0) (h2 : q ≠ 2) (h4 : q ≠ 4) (h6 : q ≠ 6)
    (h8 : q ≠ 8) (h10 : q ≠ 10) : mnorm q = 0 := by
  simp only [mnorm, if_neg h0, if_neg h2, if_neg h4, if_neg h6, if_neg h8, if_neg h10]

lemma mnorm_ne_zero {q : ℤ} (h : mnorm q ≠ 0) :
    q = 0 ∨ q = 2 ∨ q = 4 ∨ q = 6 ∨ q = 8 ∨ q = 10 := by
  by_contra hc
  push Not at hc
  exact h (mnorm_eq_zero hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2)

/-- **`decide`-check**: on `the7`, `tab` is a function of the norm. -/
theorem tab_norm_det : the7.all (fun w => decide (tab w = mnorm (qq w))) = true := by decide

/-- **`decide`-check**: on `the7`, `tab` is non-zero. -/
theorem tab_ne_zero_the7 : the7.all (fun w => decide (tab w ≠ 0)) = true := by decide

/-- **The candidate character depends only on the norm**: `mfun v = mnorm (qq v)`. -/
theorem mfun_eq_mnorm (ν : Fin 8 → ℤ) : mfun ν = mnorm (qq ν) := by
  by_cases h : normOk ν = true
  · have hnorm : qq ν = 0 ∨ qq ν = 2 ∨ qq ν = 4 ∨ qq ν = 6 ∨ qq ν = 8 ∨ qq ν = 10 :=
      normOk_eq_true.mp h
    have hle : qq ν ≤ 10 := by rcases hnorm with h | h | h | h | h | h <;> omega
    have hdq : qq (dcX ν) = qq ν := qZ_dcX ν
    have hmem : dcX ν ∈ the7 :=
      mem_the7_of_norm_le (dcX ν) (dcX_dominant ν) (by rw [hdq]; exact hle)
    have htab : tab (dcX ν) = mnorm (qq (dcX ν)) := by
      have hh := List.all_eq_true.mp tab_norm_det (dcX ν) hmem
      simpa using hh
    simp only [mfun, mfunAux, h, if_true]
    rw [htab, hdq]
  · have hfalse : normOk ν = false := by
      cases hb : normOk ν with
      | false => rfl
      | true => exact absurd hb h
    obtain ⟨h0, h2, h4, h6, h8, h10⟩ := normOk_eq_false hfalse
    simp only [mfun, mfunAux, hfalse, Bool.false_eq_true, if_false]
    exact (mnorm_eq_zero h0 h2 h4 h6 h8 h10).symm

/-- **The support of `mfun` is a union of norm classes.** -/
theorem mfun_ne_zero_iff (ν : Fin 8 → ℤ) :
    mfun ν ≠ 0 ↔ qq ν = 0 ∨ qq ν = 2 ∨ qq ν = 4 ∨ qq ν = 6 ∨ qq ν = 8 ∨ qq ν = 10 := by
  rw [mfun_eq_mnorm]
  constructor
  · exact mnorm_ne_zero
  · rintro (h | h | h | h | h | h)
    all_goals
      simp only [mnorm]
      rw [h]
      norm_num

end Submission.E8Support
