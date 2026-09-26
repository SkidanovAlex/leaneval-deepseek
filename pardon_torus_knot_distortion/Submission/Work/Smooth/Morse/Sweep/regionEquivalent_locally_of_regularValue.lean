import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Morse.Transport
import Submission.Work.SurgeryInvariance.API
import Submission.Work.Smooth.Morse.Sweep.windingSpan_locally_const_of_regularValue

/-!
# The level family is locally constant in `RegionEquivalent` at a regular value

At a regular value `t` of `g|_F` the set of critical values is locally finite
(`Work.Smooth.Morse.LocallyFiniteCriticalValues`), so a whole neighbourhood of `t` consists of
regular values (`Work.Smooth.Morse.Sweep.exists_notMem_criticalValues_near`).  For every `s` in
that neighbourhood the interval between `s` and `t` is a regular interval, so the loop-level
transport across regular intervals (`Work.Smooth.Morse.RegularEquivalent`) relates the two
sublevel regions `region ψ g t` and `region ψ g s`; reading the interval in the correct order and
using symmetry of `Work.SurgeryInvariance.RegionEquivalent` gives the claim.
-/

namespace Work.Smooth.Morse.Sweep

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

theorem regionEquivalent_locally_of_regularValue (ψ : Submission.Diffeo) {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ} (hcrit : Work.Smooth.Morse.LocallyFiniteCriticalValues ψ g) (hreg : Work.Smooth.Morse.RegularEquivalent ψ g) {t : ℝ} (ht : Work.Smooth.Morse.IsRegularValue ψ g t) : ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε → Work.SurgeryInvariance.RegionEquivalent (Work.Smooth.Morse.torus ψ) (Work.Smooth.Morse.region ψ g t) (Work.Smooth.Morse.region ψ g s) := by
  -- a neighbourhood of the regular value `t` consists entirely of regular values
  obtain ⟨ε, hεpos, hε⟩ :=
    Work.Smooth.Morse.Sweep.exists_notMem_criticalValues_near ψ hcrit ht
  refine ⟨ε, hεpos, ?_⟩
  intro s hs
  rcases lt_trichotomy s t with hlt | heq | hgt
  · -- `s < t`: transport along `[s,t]` and reverse
    have hI : ∀ u ∈ Set.Icc s t, Work.Smooth.Morse.IsRegularValue ψ g u := by
      intro u hu
      rw [Set.mem_Icc] at hu
      apply hε u
      rw [abs_lt] at hs ⊢
      constructor <;> linarith [hu.1, hu.2, hs.1, hs.2, hεpos]
    exact Work.SurgeryInvariance.RegionEquivalent.symm (hreg s t (le_of_lt hlt) hI)
  · -- `s = t`
    rw [heq]
    exact Work.SurgeryInvariance.RegionEquivalent.refl
      (P := Work.Smooth.Morse.torus ψ) (Work.Smooth.Morse.region ψ g t)
  · -- `t < s`: transport along `[t,s]`
    have hI : ∀ u ∈ Set.Icc t s, Work.Smooth.Morse.IsRegularValue ψ g u := by
      intro u hu
      rw [Set.mem_Icc] at hu
      apply hε u
      rw [abs_lt] at hs ⊢
      constructor <;> linarith [hu.1, hu.2, hs.1, hs.2, hεpos]
    exact hreg t s (le_of_lt hgt) hI

end

end Work.Smooth.Morse.Sweep
