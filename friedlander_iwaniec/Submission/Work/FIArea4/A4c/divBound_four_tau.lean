import Mathlib
import Submission.Work.FIArea4.A4c.Defs
import Submission.Work.FIArea4.A4c.card_dvd_finset_le

namespace Work.FIArea4.A4c

/-- The (5.9) clause of `IsBetaCoeff6`, extracted for the downstream use: a non-zero coefficient
point has at most `Pa.τ` divisors.  (This is the `τ(gnorm z) ≤ Pa.τ` conjunct of the defining
`if` of `IsBetaCoeff6`, exactly as in the extraction of the other clauses in `Defs6`.) -/
theorem IsBetaCoeff6.divisors_card_le_tau {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt}
    (hz : β z ≠ 0) :
    (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ := by
  obtain ⟨q, p, -, -, -, -, -, -, -, -, -, -, hβ⟩ := h
  rw [hβ z] at hz
  by_cases hc : Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0
      ∧ Work.FITop4.IsAxisFree Pa z
  · exact hc.2.2.1
  · rw [if_neg hc] at hz; exact absurd rfl hz

/-- **The divisor bound with the factor `4` and the coefficient cutoff `τ`** (design
`AREA4_ENGINES_LEAD.md` §3.3, the `DivBound` input of node N5).

For a round-6 coefficient `β` and the divisor count `CardDvdLe`, every finite set `W'` of divisors
of a support point `z` of `β` has at most `4·Pa.τ` elements: `IsBetaCoeff6.squarefree_gnorm` gives
`Squarefree (gnorm z)`, `CardDvdLe` gives `#W' ≤ 4·τ(gnorm z)`, and the (5.9) clause gives
`τ(gnorm z) ≤ Pa.τ`. -/
theorem divBound_four_tau (hcard : Work.FIArea4.A4c.CardDvdLe)
    (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ)
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) :
    Work.FIArea4.A4c.DivBound Pa β (4 * Pa.τ) := by
  intro z hz W' hW
  have hsq : Squarefree (Work.FIPlan.gnorm z) := hβ.squarefree_gnorm hz
  have hz0 : z ≠ 0 := by
    intro h0
    have hg : Work.FIPlan.gnorm z = 0 := by
      rw [h0]
      simp [Work.FIPlan.gnorm, Zsqrtd.norm_zero]
    rw [hg] at hsq
    exact not_squarefree_zero hsq
  have hτ : (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ :=
    IsBetaCoeff6.divisors_card_le_tau hβ hz
  calc (W'.card : ℝ)
      ≤ 4 * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := hcard z hz0 hsq W' hW
    _ ≤ 4 * Pa.τ := mul_le_mul_of_nonneg_left hτ (by norm_num)

end Work.FIArea4.A4c
