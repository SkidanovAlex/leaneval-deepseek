import Mathlib
import Submission.Work.TMC14Core.RatRot

namespace Work.TMC14Core

/-- Reduction of a rational `p/q` (with `q ≥ 1`) to lowest terms.

Writing `g = gcd p.natAbs q`, the pair `(p / g, q / g)` is primitive (its entries are coprime),
has denominator exactly `q / g`, and represents the same real number.  Note that
`p / g` is an integer because `g ∣ p.natAbs` hence `(g : ℤ) ∣ p`. -/
theorem exists_coprime_reduce (p : ℤ) (q : ℕ) (hq : 1 ≤ q) :
    ∃ p' : ℤ, ∃ q' : ℕ, 1 ≤ q' ∧ Nat.Coprime p'.natAbs q' ∧
      (q' : ℝ) = ((q / Nat.gcd p.natAbs q : ℕ) : ℝ) ∧
      (p' : ℝ) / (q' : ℝ) = (p : ℝ) / (q : ℝ) := by
  set g : ℕ := Nat.gcd p.natAbs q with hg
  have hqpos : 0 < q := by omega
  have hgpos : 0 < g := by rw [hg]; exact Nat.gcd_pos_of_pos_right p.natAbs hqpos
  have hgpos' : 0 < Nat.gcd p.natAbs q := by rw [← hg]; exact hgpos
  have hgdvdp : g ∣ p.natAbs := by rw [hg]; exact Nat.gcd_dvd_left p.natAbs q
  have hgdvdq : g ∣ q := by rw [hg]; exact Nat.gcd_dvd_right p.natAbs q
  have hgzdvdp : (g:ℤ) ∣ p := by
    rw [← Int.natAbs_dvd_natAbs (a := (g:ℤ)) (b := p)]
    simpa using hgdvdp
  have hp_eq : (g:ℤ) * (p / (g:ℤ)) = p := Int.mul_ediv_cancel' hgzdvdp
  have hq_eq : g * (q / g) = q := Nat.mul_div_cancel' hgdvdq
  refine ⟨p / (g:ℤ), q / g, ?_, ?_, ?_, ?_⟩
  · exact Nat.div_pos (Nat.le_of_dvd hqpos hgdvdq) hgpos
  · have hnat : (p / (g:ℤ)).natAbs = p.natAbs / g := by
      have h1 : p.natAbs = g * (p / (g:ℤ)).natAbs := by
        conv_lhs => rw [← hp_eq]
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [h1, Nat.mul_div_cancel_left _ hgpos]
    rw [hnat]
    simpa [hg] using Nat.coprime_div_gcd_div_gcd (m := p.natAbs) (n := q) hgpos'
  · rw [hg]
  · have hpc : (p : ℝ) = (g:ℝ) * ((p / (g:ℤ) : ℤ) : ℝ) := by
      conv_lhs => rw [← hp_eq]
      push_cast
      ring
    have hqc : (q : ℝ) = (g:ℝ) * ((q / g : ℕ) : ℝ) := by
      conv_lhs => rw [← hq_eq]
      push_cast
      ring
    have hgne : (g:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hgpos)
    rw [hpc, hqc]
    exact (mul_div_mul_left _ _ hgne).symm

end Work.TMC14Core
