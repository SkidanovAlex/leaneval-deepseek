import Mathlib
import Submission.Work.FIArea7.PiPairDefs
import Submission.Work.FIArea7.pairMass_fibre_le
import Submission.Work.FIArea7CF.card_gBox_filter_dvd_absDelta
import Submission.Work.FIArea7.card_Icc_int_filter_mod_eq

/-!
# `Submission.Work.FIArea7.pairPi_le_massW_rhoPi`

The per-`π` fibre bound of the coprimality-guard removal (`FI` §17): the `π`-part of the pair mass
is at most `rhoPi·(rhoPi/(4be)+1)` times the `L²`-mass of the `π`-sublattice.

The pair `T` of the box `piBox²` whose determinant is divisible by `4be` has, by
`pairMass_fibre_le` (AM–GM), mass at most `M·massW` as soon as every row/column fibre of `T` has
at most `M` elements.  For a fixed `z`, the fibre is the set of `w` in the box with
`4be ∣ |Δ(z,w)|`; writing `z = r+is`, `w = a+ib`, this is the lattice
`{(a,b) ∈ [-s,s]² : 4be ∣ r·b - s·a}` of index `4be` inside `[-s,s]²`, where
`s = shrunkNat (radN Pa) π`.  Counting it column by column (at most `2(s/d)+1` admissible columns
with `d = gcd(|r|, 4be)`, each carrying at most `min(2s+1, (2s+1)/(4be/d)+1)` values) is
`card_gBox_absDelta_le_gen`, and the resulting product is `≤ rhoPi·(rhoPi/(4be)+1)` by
`two_mul_div_bound`.  Note that no coprimality of `z.re` with `4be` is needed: the `d`-refinement
of the column count supplies exactly the factor needed.
-/
attribute [local instance] Classical.propDecidable

namespace Work.FIArea7
open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- `|Δ(πz, πw)| = |π|²·|Δ(z,w)|`. -/
lemma absDelta_mul_left (π z w : GaussianInt) :
    Work.FIPlan.absDelta (π * z) (π * w)
      = Work.FIPlan.gnorm π * Work.FIPlan.absDelta z w := by
  have hD : Work.FIPlan.Delta (π * z) (π * w)
      = (Work.FIPlan.gnorm π : ℤ) * Work.FIPlan.Delta z w := by
    simp only [Work.FIArea7.Delta_eq, Work.FIArea7.re_mul, Work.FIArea7.im_mul,
      Work.FIArea7.norm_eq]
    ring
  rw [Work.FIPlan.absDelta, Work.FIPlan.absDelta, hD, Int.natAbs_mul, Int.natAbs_natCast]

/-- `|Δ(z,w)| = |Δ(w,z)|`. -/
lemma absDelta_comm (a b : GaussianInt) :
    Work.FIPlan.absDelta a b = Work.FIPlan.absDelta b a := by
  have h : Work.FIPlan.Delta b a = - Work.FIPlan.Delta a b := by
    rw [Work.FIArea7.Delta_eq, Work.FIArea7.Delta_eq]; ring
  rw [Work.FIPlan.absDelta, Work.FIPlan.absDelta, h, Int.natAbs_neg]

end
end Work.FIArea7
