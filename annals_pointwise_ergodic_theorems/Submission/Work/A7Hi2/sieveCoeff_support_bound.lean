/-
# Support bound for the sieve (Möbius) coefficients

The sieve coefficient `sieveCoeff ρ l d = Σ_{q ∈ iwP ρ l, d ∣ q} μ (q / d)` can only be nonzero
when `d` divides some element of the Ionescu--Wainger denominator set `P_{≤l}`; since every such
divisor is at most that element, the support of `d ↦ sieveCoeff ρ l d` lies in
`[1, 2^{C_ρ · 2^{ρ l}}]`.  The element bound for `P_{≤l}` is Appendix A of Krause--Mirek--Tao,
formalised as `Work.Analysis.IonescuWainger.iwP_element_le`.
-/
import Mathlib
import Submission.Work.A7Hi2.SieveDefs

namespace Work.A7Hi2

open scoped BigOperators

/-- **Support bound for the sieve coefficients.**  For `0 < ρ ≤ 1` there is `Cρ > 0` with: if
`sieveCoeff ρ l d ≠ 0` then `d ≤ 2^{Cρ · 2^{ρ l}}`. -/
theorem sieveCoeff_support_bound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∀ (l : ℕ) (d : ℕ), Work.A7Hi2.sieveCoeff ρ l d ≠ 0 →
      (d : ℝ) ≤ (2 : ℝ) ^ (Cρ * (2 : ℝ) ^ (ρ * (l : ℝ))) := by
  obtain ⟨C, hCpos, hC⟩ := Work.Analysis.IonescuWainger.iwP_element_le hρ
  refine ⟨C, hCpos, fun l d hd => ?_⟩
  -- A nonvanishing coefficient forces the filtering set to be nonempty.
  have hne : (Work.Analysis.IonescuWainger.iwP ρ l).filter (fun q => d ∣ q) ≠ ∅ := by
    intro h
    exact hd (by simp [Work.A7Hi2.sieveCoeff, h])
  obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨hqi, hdq⟩ := Finset.mem_filter.mp hq
  have hqpos := Work.Analysis.IonescuWainger.pos_of_mem_iwP hqi
  have hdq' : d ≤ q := Nat.le_of_dvd hqpos hdq
  calc (d : ℝ) ≤ (q : ℝ) := by exact_mod_cast hdq'
    _ ≤ (2 : ℝ) ^ (C * (2 : ℝ) ^ (ρ * (l : ℝ))) := hC l q hqi

end Work.A7Hi2
