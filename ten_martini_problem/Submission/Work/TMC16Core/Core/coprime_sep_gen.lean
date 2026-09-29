import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Core

/-- If `q·α` is within `Δ` of an integer `p`, and the fractional distances of the
nonzero differences `(k-l)·α` with `1 ≤ k,l ≤ q` are all `≥ 1/(2q)`, then `p` and `q` are
coprime — as soon as `q·Δ < 1`.

(The separation hypothesis forces a common divisor `d` of `p` and `q` to satisfy
`q/d · α ≈ p/d` to precision `Δ/2`, hence `1/(2q) ≤ Δ/2`, i.e. `qΔ ≥ 1`.) -/
theorem coprime_sep_gen {α : ℝ} {q : ℕ} (hq : 0 < q) {Δ : ℝ} (hΔ : 0 < Δ) {p : ℤ}
    (happ : |(q : ℝ) * α - (p : ℝ)| ≤ Δ)
    (hsep : ∀ k l : ℕ, 1 ≤ k → k ≤ q → 1 ≤ l → l ≤ q → k ≠ l →
      1 / (2 * (q : ℝ)) ≤ Work.TMC16Core.fracDist ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * α))
    (hsmall : (q : ℝ) * Δ < 1) : Nat.Coprime p.natAbs q := by
  rcases eq_or_lt_of_le (show 1 ≤ q by omega) with hq_one | hq_gt
  · rw [← hq_one]
    exact Nat.coprime_one_right _
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hgcd
  -- write `d = gcd (|p|) q ≥ 2`, and choose the reduced `q' = q / d < q`
  set d : ℕ := Nat.gcd p.natAbs q with hddef
  have hdvdq : d ∣ q := by rw [hddef]; exact Nat.gcd_dvd_right _ _
  have hdvdp : d ∣ p.natAbs := by rw [hddef]; exact Nat.gcd_dvd_left _ _
  have hdne1 : d ≠ 1 := by rw [hddef]; exact hgcd
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
  -- hence `|q' α - p'| ≤ Δ / d ≤ Δ / 2`
  have hYle : |(q' : ℝ) * α - (p' : ℝ)| ≤ Δ / 2 := by
    have h := happ
    rw [hYid, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ))] at h
    have hd2R : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
    nlinarith [h, hd2R, abs_nonneg ((q' : ℝ) * α - (p' : ℝ)), hΔ]
  -- `fracDist (q' α) ≤ |q' α - p'|`
  have hfd : Work.TMC16Core.fracDist ((q' : ℝ) * α) ≤ |(q' : ℝ) * α - (p' : ℝ)| := by
    simpa only [Work.TMC16Core.fracDist] using round_le ((q' : ℝ) * α) p'
  -- the separation hypothesis applies to the difference `q' = (q' + 1) - 1`
  have hsep' : 1 / (2 * (q : ℝ)) ≤ Work.TMC16Core.fracDist ((q' : ℝ) * α) := by
    have hres := hsep (q' + 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega)
    have hcast : (((((q' + 1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ) : ℤ) : ℝ) * α) = (q' : ℝ) * α := by
      push_cast; ring
    rwa [hcast] at hres
  have hchain : 1 / (2 * (q : ℝ)) ≤ Δ / 2 := hsep'.trans (hfd.trans hYle)
  -- multiply by `2q > 0`: `1 ≤ Δ * q`, contradicting `q * Δ < 1`
  have h2q : (0 : ℝ) < 2 * (q : ℝ) := by positivity
  have hfinal : (1 : ℝ) ≤ Δ / 2 * (2 * (q : ℝ)) := (div_le_iff₀ h2q).mp hchain
  nlinarith [hfinal, hsmall]

end Work.TMC16Core.Core
