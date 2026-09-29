import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Trig

open Work.TMC16Core

/-- If `x` lies within `1/2` of an integer `m`, then `fracDist x` is exactly `|x - m|`
(the nearest integer to `x` is `m`). -/
lemma fracDist_eq_abs_sub_of_lt_half {x : ℝ} {m : ℤ} (h : |x - (m : ℝ)| < 1 / 2) :
    fracDist x = |x - (m : ℝ)| := by
  have h' : -(1 / 2) < x - (m : ℝ) ∧ x - (m : ℝ) < 1 / 2 := abs_lt.mp h
  have hround : round x = m := by
    rw [round_eq_iff, Set.mem_Ico]
    constructor <;> linarith [h'.1, h'.2]
  rw [Work.TMC16Core.fracDist, hround]

theorem coprime_of_sep {α : ℝ} {q : ℕ} (hq : 0 < q) {Δ : ℝ} (hΔ : 0 < Δ) {p : ℤ}
    (happ : |(q : ℝ) * α - (p : ℝ)| ≤ Δ)
    (hsep : ∀ k l : ℕ, 1 ≤ k → k ≤ q → 1 ≤ l → l ≤ q → k ≠ l →
      1 / (2 * (q : ℝ)) ≤ Work.TMC16Core.fracDist ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * α))
    (hsmall : (q : ℝ) * Δ ≤ 1 / 8) :
    Nat.Coprime p.natAbs q := by
  rcases eq_or_lt_of_le (show 1 ≤ q by omega) with hq_one | hq_gt
  · rw [← hq_one]
    exact Nat.coprime_one_right _
  by_contra hcop
  rw [Nat.coprime_iff_gcd_eq_one] at hcop
  -- write `d = gcd (|p|) q ≥ 2`, and choose the reduced `q' = q / d < q`
  set d : ℕ := Nat.gcd p.natAbs q with hddef
  have hdvdq : d ∣ q := by rw [hddef]; exact Nat.gcd_dvd_right _ _
  have hdvdp : d ∣ p.natAbs := by rw [hddef]; exact Nat.gcd_dvd_left _ _
  have hdne1 : d ≠ 1 := by rw [hddef]; exact hcop
  have hd2 : 2 ≤ d := by
    have hpos : 0 < d := Nat.pos_of_dvd_of_pos hdvdq hq
    omega
  set q' : ℕ := q / d with hq'def
  have hq'mul : d * q' = q := by
    rw [hq'def]
    exact Nat.mul_div_cancel' hdvdq
  have hq'pos : 0 < q' := by
    by_contra h
    have h0 : q' = 0 := Nat.eq_zero_of_not_pos h
    rw [h0, Nat.mul_zero] at hq'mul
    omega
  have hq'lt : q' < q := by
    have h1 : 2 * q' ≤ d * q' := Nat.mul_le_mul_right q' hd2
    rw [hq'mul] at h1
    omega
  -- an integer `p'` with `p = d * p'`
  have hdvdZ : (d : ℤ) ∣ p := by
    rw [← Int.dvd_natAbs]
    exact_mod_cast hdvdp
  obtain ⟨p', hp'⟩ := hdvdZ
  -- real algebra: `q α - p = d (q' α - p')`
  have hYid : (q : ℝ) * α - (p : ℝ) = (d : ℝ) * ((q' : ℝ) * α - (p' : ℝ)) := by
    have h1 : (q : ℝ) = (d : ℝ) * (q' : ℝ) := by rw [← hq'mul]; push_cast; ring
    have h2 : (p : ℝ) = (d : ℝ) * (p' : ℝ) := by rw [hp']; push_cast; ring
    rw [h1, h2]; ring
  have hdnonneg : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hbound : (d : ℝ) * |(q' : ℝ) * α - (p' : ℝ)| ≤ Δ := by
    have h := happ
    rw [hYid, abs_mul, abs_of_nonneg hdnonneg] at h
    exact h
  have hYle : |(q' : ℝ) * α - (p' : ℝ)| ≤ Δ := by
    have hdle : (1 : ℝ) ≤ (d : ℝ) := by
      have h1 : 1 ≤ d := by omega
      exact_mod_cast h1
    have h := mul_le_mul_of_nonneg_right hdle (abs_nonneg ((q' : ℝ) * α - (p' : ℝ)))
    simp only [one_mul] at h
    linarith
  have hDelta : Δ ≤ 1 / 16 := by
    have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_gt
    nlinarith [hsmall, hq2R, hΔ]
  have hYlt : |(q' : ℝ) * α - (p' : ℝ)| < 1 / 2 := by linarith
  have hfd : fracDist ((q' : ℝ) * α) = |(q' : ℝ) * α - (p' : ℝ)| :=
    fracDist_eq_abs_sub_of_lt_half hYlt
  -- the separation hypothesis applies to the difference `q' = (q' + 1) - 1`
  have hsep' : 1 / (2 * (q : ℝ)) ≤ Δ := by
    have hres := hsep (q' + 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega)
    have hcast : (((((q' + 1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ) : ℤ) : ℝ) * α) = (q' : ℝ) * α := by
      push_cast; ring
    rw [hcast, hfd] at hres
    linarith
  have h2q : (0 : ℝ) < 2 * (q : ℝ) := by
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    linarith
  have hfinal := (div_le_iff₀ h2q).mp hsep'
  nlinarith [hfinal, hsmall]

end Work.TMC16Core.Trig
