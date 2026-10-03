import Mathlib
import Submission.Work.FIChain.S3plusC_route_defs
import Submission.Work.FIChain.rhoTrunc_recip
import Submission.Work.FIChain.integral_rhoTrunc_recip_subst

namespace Work.FIChain

open MeasureTheory
open scoped Interval

set_option autoImplicit false

noncomputable section

/-- **The divisor duality carried through the integral.**  For squarefree `c ≠ 1` and
`1 ≤ X ≤ c`,
`∫_1^{c/X} ρ(c; c/u) du/u = -μ(c)·∫_1^{c/X} ρ(c; u) du/u`.

This is `rhoTrunc_recip` (`ρ(c; c/u) = -μ(c)·ρ(c; u)`) transferred to the integral: the equality
holds pointwise off the finite set of `u` that are divisors of `c`, hence almost everywhere. -/
lemma integral_recip_duality (c X : ℕ) (hc : Squarefree c) (hc1 : c ≠ 1) (hX : 1 ≤ X)
    (hXc : X ≤ c) :
    ∫ u in (1 : ℝ)..((c : ℝ) / (X : ℝ)), Submission.ASP.rhoTrunc c (c / u) / u
      = -(ArithmeticFunction.moebius c : ℝ)
          * ∫ u in (1 : ℝ)..((c : ℝ) / (X : ℝ)), Submission.ASP.rhoTrunc c u / u := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hcX : (1 : ℝ) ≤ (c : ℝ) / (X : ℝ) := by
    rw [le_div_iff₀ hXpos]
    simp only [one_mul]
    exact_mod_cast hXc
  set S : Set ℝ := (c.divisors : Set ℕ).image (fun m : ℕ => (m : ℝ)) with hS
  have hSfin : S.Finite := (Finset.finite_toSet c.divisors).image _
  have haeS : ∀ᵐ u ∂(volume : Measure ℝ), u ∉ S :=
    MeasureTheory.measure_eq_zero_iff_ae_notMem.mp (hSfin.measure_zero volume)
  have hcongr : (∫ u in (1 : ℝ)..((c : ℝ) / (X : ℝ)), Submission.ASP.rhoTrunc c (c / u) / u)
      = ∫ u in (1 : ℝ)..((c : ℝ) / (X : ℝ)),
          (-(ArithmeticFunction.moebius c : ℝ)) * (Submission.ASP.rhoTrunc c u / u) := by
    refine intervalIntegral.integral_congr_ae ?_
    refine haeS.mono (fun u huS huIoc => ?_)
    rw [Set.uIoc_of_le hcX] at huIoc
    have hu_pos : 0 < u := lt_trans zero_lt_one huIoc.1
    have hnd : ∀ d ∈ c.divisors, (d : ℝ) ≠ u := by
      intro d hd hdu
      exact huS (by rw [hS]; exact ⟨d, hd, hdu⟩)
    rw [rhoTrunc_recip c hc hc1 u hu_pos hnd]
    ring
  rw [hcongr, intervalIntegral.integral_const_mul]

/-- **The exact divisor-duality identity for `λ⁺`.**  For squarefree `c ≥ 2` and `1 ≤ Cm < c`,
`μ(c)·λ⁺(c) = ∫_1^{c/Cm} ρ(c;u) du/u`, where `ρ(c;u) = Σ_{d|c, d≤u} μ(d)` (here `rhoTrunc c u`).

Route: the PROVED `ASP.S8c.lamPlus_eq_neg_integral` gives `λ⁺(c) = −∫_{Cm}^{c} ρ(c;t)dt/t`
(needs `2 ≤ c`, `0 < Cm`, `Cm ≤ c`); then `∫_{Cm}^{c} ρ(c;t)dt/t = −μ(c)∫_1^{c/Cm}ρ(c;u)du/u`
(substitution `t = c/u` plus the a.e. divisor-duality `ρ(c;c/u) = −μ(c)ρ(c;u)`, valid since
`Σ_{d|c}μ(d) = 0` for `c > 1`), so `μ(c)λ⁺(c) = μ(c)·μ(c)∫_1^{c/Cm}ρ(c;u)du/u = ∫...`.

The intermediate identity `∫_X^c ρ(c;t)dt/t = -μ(c)∫_1^{c/X}ρ(c;u)du/u` (`0 < X ≤ c`) can also be
proved *without* measure-theoretic substitution, by computing both sides as explicit divisor sums
(`rhoTrunc c t = Σ_{d|c}μ(d)·1_{d≤t}`): LHS `= Σ_{d|c}μ(d)log(c/max(X,d))`,
RHS `= -μ(c)Σ_{d|c,d≤c/X}μ(d)log((c/X)/max(1,d))`, and these agree by the pairing `d ↔ c/d`
together with `Σ_{d|c}μ(d) = 0` (carefully: `d = X` is counted once on the left, and its term
`log(X/X) = 0` on the right).

Sanity checks (brute-forced by the reviewer): `c = p`: both sides `log(p/Cm)`.  `c = pq` with
`Cm < p < q`: both `log Cm`; with `p < Cm < q`: both `log p`.  `c = pqr` (all `> Cm`): `λ⁺ = log Cm`. -/
theorem S3plusC_lamPlus_identity (c Cm : ℕ) (hc : 2 ≤ c) (hsf : Squarefree c)
    (hCm : 1 ≤ Cm) (hlt : Cm < c) :
    (ArithmeticFunction.moebius c : ℝ) * Submission.ASP.lamPlus c (Cm : ℝ)
      = ∫ u in (1 : ℝ)..((c : ℝ) / (Cm : ℝ)), Submission.ASP.rhoTrunc c u / u := by
  have hc1 : c ≠ 1 := by omega
  have hCpos : (0 : ℝ) < (Cm : ℝ) := by exact_mod_cast hCm
  have hCmc : (Cm : ℝ) ≤ (c : ℝ) := by exact_mod_cast (le_of_lt hlt)
  have hsq : ((ArithmeticFunction.moebius c : ℝ)) ^ 2 = 1 := by
    have hz := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
    exact_mod_cast hz
  rw [Submission.ASP.lamPlus_eq_neg_integral c c hc le_rfl hCpos hCmc]
  have hB := integral_rhoTrunc_recip_subst c Cm hCm (le_of_lt hlt)
  have hC := integral_recip_duality c Cm hsf hc1 hCm (le_of_lt hlt)
  rw [hB, hC]
  set I : ℝ := ∫ u in (1 : ℝ)..((c : ℝ) / (Cm : ℝ)), Submission.ASP.rhoTrunc c u / u
  have : (ArithmeticFunction.moebius c : ℝ)
      * (-(-(ArithmeticFunction.moebius c : ℝ) * I))
      = ((ArithmeticFunction.moebius c : ℝ)) ^ 2 * I := by ring
  rw [this, hsq, one_mul]

end

end Work.FIChain
