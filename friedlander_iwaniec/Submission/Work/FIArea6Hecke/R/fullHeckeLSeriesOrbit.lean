import Mathlib
import Submission.Work.FIArea6Hecke.R.ConductorThetaDefs
import Submission.Work.FIArea6Hecke.R.oddPartLattice
import Submission.Work.FIArea6Hecke.R.evenSubstLattice

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

namespace Work.FIArea6Hecke.R

open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- The summand `ψ(z)·N(z)^{-s}` of the complete Hecke `L`-series `fullHeckeLSeries`. -/
def orbitSummand (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) (z : GaussianInt) : ℂ :=
  Work.FIArea5.S16Hecke.psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s))

lemma fullHeckeLSeries_eq_orbitSummand (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) :
    fullHeckeLSeries chi m s = ∑' z : GaussianInt, orbitSummand chi m s z := rfl

/-- Reindexing the `(1+i)`-sublattice: summing `f` over the multiples of `1+i` is summing the
indicator of the divisibility condition over `ℤ[i]`. -/
lemma tsum_indicator_oneAddI_mul (f : GaussianInt → ℂ) :
    (∑' w : GaussianInt, f (Work.FIArea5.S16Hecke.oneAddI * w))
      = ∑' z : GaussianInt,
          (if Work.FIArea5.S16Hecke.oneAddI ∣ z then f z else 0) := by
  have hne : Work.FIArea5.S16Hecke.oneAddI ≠ 0 := by decide
  have hinj : Function.Injective
      (fun w : GaussianInt => Work.FIArea5.S16Hecke.oneAddI * w) :=
    fun a b h => mul_left_cancel₀ hne h
  have hsupp : Function.support (fun z : GaussianInt =>
        (if Work.FIArea5.S16Hecke.oneAddI ∣ z then f z else 0))
      ⊆ Set.range (fun w : GaussianInt => Work.FIArea5.S16Hecke.oneAddI * w) := by
    intro z hz
    rw [Function.mem_support] at hz
    by_cases hd : Work.FIArea5.S16Hecke.oneAddI ∣ z
    · obtain ⟨w, hw⟩ := hd
      exact ⟨w, hw.symm⟩
    · rw [if_neg hd] at hz; exact absurd rfl hz
  simpa [dvd_mul_right] using hinj.tsum_eq hsupp

theorem fullHeckeLSeriesOrbit (chi : GaussianInt → ℂ) (m : ℤ)
    (h1 : chi 1 = 1) (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hbd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    ∀ s : ℂ, 1 < s.re →
      Work.FIArea6Hecke.R.fullHeckeLSeries chi m s *
          (1 - Work.FIArea5.S16Hecke.psi chi m Work.FIArea5.S16Hecke.oneAddI *
            ((2 : ℂ) ^ (-s)))
        = (∑ ε ∈ Work.FIArea5.S16Hecke.units4, chi ε * (ε.toComplex) ^ m) *
            Work.FIArea5.S16Hecke.heckeLSeries chi m s := by
  intro s hs
  have hfall : Summable (fun z : GaussianInt =>
      Work.FIArea5.S16Hecke.psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s))) :=
    summable_psi_gnorm_cpow chi m hbd hs
  have hevenSumm : Summable (fun z : GaussianInt =>
      (if Work.FIArea5.S16Hecke.oneAddI ∣ z then
        Work.FIArea5.S16Hecke.psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s)) else 0)) := by
    refine Summable.of_norm_bounded hfall.norm (fun z => ?_)
    by_cases h : Work.FIArea5.S16Hecke.oneAddI ∣ z
    · rw [if_pos h]
    · rw [if_neg h, norm_zero]; positivity
  have hoddSumm : Summable (fun z : GaussianInt =>
      (if Work.FIArea5.S16Hecke.isOddG z then
        Work.FIArea5.S16Hecke.psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s)) else 0)) := by
    refine Summable.of_norm_bounded hfall.norm (fun z => ?_)
    by_cases h : Work.FIArea5.S16Hecke.isOddG z
    · rw [if_pos h]
    · rw [if_neg h, norm_zero]; positivity
  have hsplit : (∑' z : GaussianInt,
        Work.FIArea5.S16Hecke.psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s)))
      = (∑' z : GaussianInt,
          (if Work.FIArea5.S16Hecke.oneAddI ∣ z then
            Work.FIArea5.S16Hecke.psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s)) else 0))
        + (∑' z : GaussianInt,
          (if Work.FIArea5.S16Hecke.isOddG z then
            Work.FIArea5.S16Hecke.psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s)) else 0)) := by
    rw [← Summable.tsum_add hevenSumm hoddSumm]
    refine tsum_congr (fun z => ?_)
    by_cases h : Work.FIArea5.S16Hecke.oneAddI ∣ z <;>
      simp [h, Work.FIArea5.S16Hecke.isOddG]
  have heven : (∑' z : GaussianInt,
        (if Work.FIArea5.S16Hecke.oneAddI ∣ z then
          Work.FIArea5.S16Hecke.psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s)) else 0))
      = Work.FIArea5.S16Hecke.psi chi m Work.FIArea5.S16Hecke.oneAddI * ((2 : ℂ) ^ (-s))
        * (∑' z : GaussianInt,
            Work.FIArea5.S16Hecke.psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s))) := by
    rw [← tsum_indicator_oneAddI_mul
      (fun z : GaussianInt => Work.FIArea5.S16Hecke.psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s)))]
    exact evenSubstLattice chi m hmul hbd s hs
  have hodd : (∑' z : GaussianInt,
        (if Work.FIArea5.S16Hecke.isOddG z then
          Work.FIArea5.S16Hecke.psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s)) else 0))
      = (∑ ε ∈ Work.FIArea5.S16Hecke.units4, chi ε * (ε.toComplex) ^ m)
        * Work.FIArea5.S16Hecke.heckeLSeries chi m s :=
    oddPartLattice chi m h1 hmul hbd s hs
  have hFL : Work.FIArea6Hecke.R.fullHeckeLSeries chi m s
      = ∑' z : GaussianInt,
          Work.FIArea5.S16Hecke.psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s)) := rfl
  have hmain : (∑' z : GaussianInt,
        Work.FIArea5.S16Hecke.psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s)))
      = (Work.FIArea5.S16Hecke.psi chi m Work.FIArea5.S16Hecke.oneAddI * ((2 : ℂ) ^ (-s)))
          * (∑' z : GaussianInt,
              Work.FIArea5.S16Hecke.psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s)))
        + (∑ ε ∈ Work.FIArea5.S16Hecke.units4, chi ε * (ε.toComplex) ^ m)
          * Work.FIArea5.S16Hecke.heckeLSeries chi m s := by
    refine hsplit.trans ?_
    rw [heven, hodd]
  rw [hFL]
  have key : (∑' z : GaussianInt,
        Work.FIArea5.S16Hecke.psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s)))
        - (Work.FIArea5.S16Hecke.psi chi m Work.FIArea5.S16Hecke.oneAddI * ((2 : ℂ) ^ (-s)))
          * (∑' z : GaussianInt,
              Work.FIArea5.S16Hecke.psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s)))
      = (∑ ε ∈ Work.FIArea5.S16Hecke.units4, chi ε * (ε.toComplex) ^ m)
          * Work.FIArea5.S16Hecke.heckeLSeries chi m s := by
    nth_rewrite 1 [hmain]
    ring
  rw [show (∑' z : GaussianInt,
        Work.FIArea5.S16Hecke.psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s)))
        * (1 - Work.FIArea5.S16Hecke.psi chi m Work.FIArea5.S16Hecke.oneAddI * ((2 : ℂ) ^ (-s)))
      = (∑' z : GaussianInt,
        Work.FIArea5.S16Hecke.psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s)))
        - (Work.FIArea5.S16Hecke.psi chi m Work.FIArea5.S16Hecke.oneAddI * ((2 : ℂ) ^ (-s)))
          * (∑' z : GaussianInt,
              Work.FIArea5.S16Hecke.psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s))) by ring]
  exact key

end

end Work.FIArea6Hecke.R
