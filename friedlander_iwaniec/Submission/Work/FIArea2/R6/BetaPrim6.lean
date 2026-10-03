/-
# `FIArea2/R6/BetaPrim6.lean` — primitivity, `Δ ≠ 0` and the (9.2) weight for a round-6 coefficient

The part of the round-6 coefficient API that needs the arithmetic of `ℤ[i]`
(`isCoprime_star_of_squarefree_odd_gnorm`, `Delta_ne_zero_of_coprime`) and the (9.2) comparison
`Haver_le_uniform`; kept in its own module so that the purely analytic bookkeeping of
`BetaFacts6` does not depend on it.
-/
import Mathlib
import Submission.Work.FIArea2.R6.BetaFacts6
import Submission.Work.FIArea2.gamOf_nonneg_of_polarBox
import Submission.Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm
import Submission.Work.FIArea2.area2_r3

set_option autoImplicit false

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- A nonzero coefficient point is primitive: `(z, z̄) = 1`. -/
theorem IsBetaCoeff6.isCoprime_star6 {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt}
    (hz : β z ≠ 0) : IsCoprime z (star z) :=
  Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm
    (Work.FITop4.IsBetaCoeff6.squarefree_gnorm h hz)
    (Work.FIArea2.InPolarBox.odd_gnorm (Work.FITop4.IsBetaCoeff6.support h hz))

/-- **(*FI* (6.1)/(6.2))** for round-6 coefficients: on the support and for a coprime pair, the
determinant `Δ(z₁,z₂) = Im(z̄₁z₂)` does not vanish. -/
theorem IsBetaCoeff6.delta_ne_zero6 {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z1 z2 : GaussianInt}
    (hcop : Work.FIPlan.GaussCoprime z1 z2) (h1 : β z1 ≠ 0) (h2 : β z2 ≠ 0) :
    Work.FIPlan.Delta z1 z2 ≠ 0 := by
  have hb1 := Work.FITop4.IsBetaCoeff6.support h h1
  have hn1 : 2 ≤ Work.FIPlan.gnorm z1 := by
    have hgt : (1 : ℝ) < (Work.FIPlan.gnorm z1 : ℝ) :=
      lt_of_le_of_lt (by exact_mod_cast Pa.hN1) hb1.2.1
    have hgt' : (1 : ℕ) < Work.FIPlan.gnorm z1 := by exact_mod_cast hgt
    omega
  exact Work.FIArea2.Delta_ne_zero_of_coprime hcop (IsBetaCoeff6.isCoprime_star6 h h1)
    (IsBetaCoeff6.isCoprime_star6 h h2) hn1

/-- `0 ≤ γ < 1` on the support of a round-6 coefficient and for a coprime pair (the standing
hypotheses `hγ0`, `hγ1` of (9.1)). -/
theorem IsBetaCoeff6.gamOf_bounds6 {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z1 z2 : GaussianInt}
    (hcop : Work.FIPlan.GaussCoprime z1 z2) (h1 : β z1 ≠ 0) (h2 : β z2 ≠ 0) :
    0 ≤ Work.FIArea2.gamOf z1 z2 ∧ Work.FIArea2.gamOf z1 z2 < 1 :=
  ⟨Work.FIArea2.gamOf_nonneg_of_polarBox Pa φ z1 z2 (Work.FITop4.IsBetaCoeff6.support h h1)
      (Work.FITop4.IsBetaCoeff6.support h h2) (two_pi_theta_le_pi_div_two6 Pa),
    Work.FIArea2.gamOf_lt_one_of_Delta_ne_zero (IsBetaCoeff6.delta_ne_zero6 h hcop h1 h2)⟩

/-- **The (9.2) weight against the uniform one**: on the support of a round-6 coefficient and for a
coprime pair, `Haver Pa z₁ z₂ ≤ 64 · sec9Usum Pa z₁ z₂` (`Haver_le_uniform` with every polar-box
and parameter hypothesis discharged). -/
theorem IsBetaCoeff6.haver_le6 {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z1 z2 : GaussianInt}
    (hcop : Work.FIPlan.GaussCoprime z1 z2) (h1 : β z1 ≠ 0) (h2 : β z2 ≠ 0) :
    Work.FIArea2.Haver Pa z1 z2 ≤ 64 * Work.FIArea2.sec9Usum Pa z1 z2 := by
  obtain ⟨hg0, hg1⟩ := IsBetaCoeff6.gamOf_bounds6 h hcop h1 h2
  obtain ⟨hn1, hn1'⟩ := IsBetaCoeff6.gnorm_bounds h h1
  obtain ⟨hn2, hn2'⟩ := IsBetaCoeff6.gnorm_bounds h h2
  have hmain := Work.FIArea2.Haver_le_uniform Pa z1 z2
    (IsBetaCoeff6.delta_ne_zero6 h hcop h1 h2) hg0 hg1 Pa.hM1 (theta_le_one6 Pa)
    hn1 hn1' hn2 hn2'
  have heq : (∑' h : ℤ × ℤ, (if h = (0, 0) then 0 else
        (Work.FIArea2.gcdDelta z1 z2 h.1 h.2 : ℝ)
          * (1 + (h.1 : ℝ) ^ 2 / (Work.FIPlan.Hscale Pa.M Pa.N) ^ 2)⁻¹
          * (1 + (h.2 : ℝ) ^ 2 / (Work.FIPlan.Hscale Pa.M Pa.N) ^ 2)⁻¹))
      = Work.FIArea2.sec9Usum Pa z1 z2 := by
    rw [Work.FIArea2.sec9Usum]
    refine tsum_congr fun h => ?_
    by_cases hh : h = (0, 0)
    · rw [hh]; simp
    · rw [if_neg hh, if_neg hh, Work.FIArea2.sec9Uwt]; ring
  rw [heq] at hmain
  exact hmain


end

end Work.FIArea2.R6
