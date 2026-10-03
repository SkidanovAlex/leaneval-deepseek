/-
# `Submission.Work.FIArea6c.area6c_error_bound` — the §16 error bound (clash-free route)

The §16 error half `2 Σ_{d ≤ X} (φ(d)/d)‖Vd d − MainSum X d‖ ≤ C((Pz)⁻¹+X⁻¹)N²log N` used by the
pinned §16 display `Work.FIArea6c.section16_Ucut_twoP`.  It is the same statement as
`Work.FIArea6.S16ErrTwo.error_bound_self` (`Submission/Work/FIArea6/S16ErrTwo/Arith.lean`), but
derived from the *clash-free* pieces: the four mass estimates `diagMass_le`, `nearMass_le`,
`farMass_le`, `ncMass_le` (the last two taken from `Work.FIArea6.S16_masses`, which carries them
without importing the cycle-broken `S16ErrTwo/SfarDefs.lean`), combined by the arithmetic endgame
`Work.FIArea6.S16ErrTwo.error_bound_of_pieces`.  The bound is independent of the pin.
-/
import Mathlib
import Submission.Work.FITop4.Areas6
import Submission.Work.FIArea6.S16ErrTwo.error_bound_of_pieces
import Submission.Work.FIArea6.S16_masses
import Submission.Work.FIArea6.S16ErrTwo.diagMass_le
import Submission.Work.FIArea6.S16ErrTwo.ncMass_le

set_option autoImplicit false

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The §16 error bound, assembled from the four clash-free mass estimates. -/
theorem area6c_error_bound :
    ∃ C x0 : ℝ, 0 < C ∧ 0 < x0 ∧
    ∀ (Pa : Work.FITop.Params) (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
      x0 ≤ (Pa.x : ℝ) → Work.FITop4.IsBetaCoeff6 Pa φ z0 β → 1 ≤ X →
      (X : ℝ) ≤ (Real.log Pa.N) ^ Work.FITop4.nuU →
      2 * ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) *
          ‖Work.FIArea6.Vd Pa d β - Work.FIArea6.MainSum Pa X d β‖
        ≤ C * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ (2 : ℕ) * Real.log Pa.N :=
  Work.FIArea6.S16ErrTwo.error_bound_of_pieces
    Work.FIArea6.S16ErrTwo.diagMass_le
    Work.FIArea6.S16ErrTwo.nearMass_le
    Work.FIArea6.S16ErrTwo.farMass_le
    Work.FIArea6.S16ErrTwo.ncMass_le

end

end Work.FIArea6
