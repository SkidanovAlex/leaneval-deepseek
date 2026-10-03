/-
# `Submission.Work.FIArea5.S16Hecke.cvs_regroup8`

Reassociation of the eight-fold Cauchy product of geometric sequences underlying the four-fold
Hecke convolution `λ_1 ⍟ λ_{χ₁} ⍟ λ_{χ₂} ⍟ λ_{χ₁χ₂}`.

The sequence `GabC a b` is the Cauchy product of `gc 1`, `gc a`, `gc b`, `gc (a*b)`
(`= cvs (cvs (cvs (gc 1) (gc a)) (gc b)) (gc (a*b))`), and the left-hand side below is the same
convolution with the four factors `gc 1, gc 1` replaced by the pair `cvs (gc a₁) (gc b₁)` and
`cvs (gc a₂) (gc b₂)`.  Both sides are products of the same eight factors `gc 1, gc 1, gc a₁,
gc b₁, gc a₂, gc b₂, gc (a₁a₂), gc (b₁b₂)`, so the identity is a pure reassociation in the
commutative monoid `(ℕ → ℂ, cvs, deltaC)`.

The proof transports the identity to the formal power series ring through the Cauchy product
isomorphism `PowerSeries.mk` (`mk_cvs`), where the reassociation is handled by `ring`, and
descends again using injectivity of `PowerSeries.mk`.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.conv_defs

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators

noncomputable section

/-- A power series over a semiring is determined by its coefficient sequence: `PowerSeries.mk`
is injective. -/
lemma PowerSeries_mk_injective {R : Type*} [Semiring R] :
    Function.Injective (PowerSeries.mk : (ℕ → R) → PowerSeries R) := by
  intro f g h
  funext n
  have hn := congrArg (PowerSeries.coeff n) h
  simpa [PowerSeries.coeff_mk] using hn

/-- The two reassociations of the eight geometric factors `gc 1, gc 1, gc a₁, gc b₁, gc a₂, gc b₂,
`gc (a₁a₂)`, `gc (b₁b₂)` agree. -/
theorem cvs_regroup8 (a₁ a₂ b₁ b₂ : ℂ) :
    Work.FIArea5.S16Hecke.cvs
        (Work.FIArea5.S16Hecke.cvs
          (Work.FIArea5.S16Hecke.cvs
            (Work.FIArea5.S16Hecke.cvs (Work.FIArea5.S16Hecke.gc 1) (Work.FIArea5.S16Hecke.gc 1))
            (Work.FIArea5.S16Hecke.cvs (Work.FIArea5.S16Hecke.gc a₁) (Work.FIArea5.S16Hecke.gc b₁)))
          (Work.FIArea5.S16Hecke.cvs (Work.FIArea5.S16Hecke.gc a₂) (Work.FIArea5.S16Hecke.gc b₂)))
        (Work.FIArea5.S16Hecke.cvs (Work.FIArea5.S16Hecke.gc (a₁ * a₂)) (Work.FIArea5.S16Hecke.gc (b₁ * b₂)))
      = Work.FIArea5.S16Hecke.cvs (Work.FIArea5.S16Hecke.GabC a₁ a₂) (Work.FIArea5.S16Hecke.GabC b₁ b₂) := by
  apply PowerSeries_mk_injective
  simp only [GabC, mk_cvs]
  ring

end

end Work.FIArea5.S16Hecke
