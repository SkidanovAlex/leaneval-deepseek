/-
# `Submission.Work.FIArea7.PiPairAux` — `ρ̄`, the uniform version of `rhoPi`

`rhoPi (radN Pa) π = 2⌊radN Pa·√2/√(gnorm π)⌋+1` is the point count of the fibre bound
(`card_piDvd_filter_dvd_absDelta_le`).  Since every `π ∈ bigPi Pa m` has `gnorm π > Pz`, the count
is dominated by the uniform
`rhoBar Pa = 2⌊radN Pa·√2/√Pz⌋+1`, which is what the assembly of `uniMode_pairMass_le` sums over
`(b,e)`.
-/
import Mathlib
import Submission.Work.FIArea7.PiPairDefs

attribute [local instance] Classical.propDecidable

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section

/-- The uniform point count `2⌊R√2/√Pz⌋+1`, dominating `rhoPi` on `bigPi`. -/
def rhoBar (Pa : Work.FITop.Params) : ℕ :=
  2 * Nat.floor ((Work.FITop.radN Pa : ℝ) * Real.sqrt 2 / Real.sqrt (Pa.Pz : ℝ)) + 1

lemma Pz_pos (Pa : Work.FITop.Params) : 0 < Pa.Pz := by have := Pa.hP2; omega

lemma gnorm_pos_of_bigPi {Pa : Work.FITop.Params} {m : ℕ} {π : GaussianInt}
    (hπ : π ∈ bigPi Pa m) : 0 < Work.FIPlan.gnorm π := by
  have h : Pa.Pz < Work.FIPlan.gnorm π := (Finset.mem_filter.mp hπ).2.2.2.2.1
  have := Pa.hP2
  omega

lemma rhoPi_le_rhoBar {Pa : Work.FITop.Params} {m : ℕ} {π : GaussianInt}
    (hπ : π ∈ bigPi Pa m) : rhoPi (Work.FITop.radN Pa) π ≤ rhoBar Pa := by
  unfold rhoPi rhoBar shrunkNat
  have hgn : Pa.Pz < Work.FIPlan.gnorm π := (Finset.mem_filter.mp hπ).2.2.2.2.1
  have h1 : Real.sqrt (Pa.Pz : ℝ) ≤ Real.sqrt (Work.FIPlan.gnorm π : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (le_of_lt hgn))
  have hR0 : (0 : ℝ) ≤ (Work.FITop.radN Pa : ℝ) := by
    rw [Work.FITop.radN]; positivity
  have h2 : (Work.FITop.radN Pa : ℝ) * Real.sqrt 2 / Real.sqrt (Work.FIPlan.gnorm π : ℝ)
      ≤ (Work.FITop.radN Pa : ℝ) * Real.sqrt 2 / Real.sqrt (Pa.Pz : ℝ) :=
    div_le_div_of_nonneg_left (by positivity)
      (Real.sqrt_pos_of_pos (by exact_mod_cast Pz_pos Pa)) h1
  have h3 : Nat.floor ((Work.FITop.radN Pa : ℝ) * Real.sqrt 2
        / Real.sqrt (Work.FIPlan.gnorm π : ℝ))
      ≤ Nat.floor ((Work.FITop.radN Pa : ℝ) * Real.sqrt 2 / Real.sqrt (Pa.Pz : ℝ)) :=
    Nat.floor_mono h2
  omega

lemma one_le_rhoPi (R : ℤ) (π : GaussianInt) : 1 ≤ rhoPi R π := by
  unfold rhoPi; omega

end

end Work.FIArea7
