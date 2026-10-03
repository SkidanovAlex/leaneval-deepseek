/-
# `Submission.Work.FIArea6V.S16CoreTwoV_of_radialCoreTwoV` — the polar-box redundancy, τ-vacuous lane

The clean (V) lane's counterpart of `Work.FIArea6.S16CoreTwo_of_radialCoreTwo`
(`Submission/Work/FIArea6/area5Two_of_invBound.lean`).

`S16CoreTwoV` is the `β`-indexed §16 core at the round-6 coefficient class `IsBetaCoeff6` and the
strict characters `IsCharMod4dStrict d χ`; `S16RadialCoreTwoV` is the same bound with the coefficient
written out through the explicit mollifiers `q`, `p` of (5.13).  The two statements carry the same
pair of constants `(c, C)`, the same threshold, and the same right-hand side, so the passage
β-indexed → radial is *elementary*: on the support of `IsBetaCoeff6` the polar-box indicator of the
radial sum is redundant (the angular support (5.12) of `q`, together with `q 0 = 0`, and the radial
segment (4.12) of `p` already give the sector and the norm range of `InPolarBox`).

Because `IsBetaCoeff6` carries the very same five support clauses (`InPolarBox`, `NoSmallPrimes`,
`τ(|z|²) ≤ Pa.τ`, `SameClass8`, `IsAxisFree`) in the V-lane as in the pinned lane, the pointwise
identity `Work.FIArea6.betaSummand_eq_radial` applies verbatim.  The only difference of the V-lane
is *extra hypotheses* on the two `∀Pa`-clauses (`TauVac Pa φ` and the axis-free polar box), which are
threaded through unchanged.

The axis-free hypothesis `hAxis` is not needed for the summand identity itself (it is already a
conjunct of the support); it is required only to feed `S16RadialCoreTwoV`.
-/
import Mathlib
import Submission.Work.FIArea6V.Defs
import Submission.Work.FIArea6.area5Two_of_invBound

namespace Work.FIArea6V

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **`S16CoreTwoV` from `S16RadialCoreTwoV`** (*FI* §16, the elementary redundancy of the polar-box
indicator with the mollifier supports (4.12)/(5.12), applied to the round-6 coefficient class, in the
τ-vacuous clean lane).

The two statements have the same constants `c, C` and the same right-hand side; `S16CoreTwoV` allows
the smaller frequency range `|k| ≤ exp(√log N)` (no `3`), an immediate weakening, and additionally
supplies the two lane hypotheses `TauVac Pa φ` and the axis-free polar box, which the radial core
receives.  The only mathematical content is that the `β`-sum equals the radial `q, p`-sum
pointwise. -/
theorem S16CoreTwoV_of_radialCoreTwoV (h : Work.FIArea6V.S16RadialCoreTwoV) :
    Work.FIArea6V.S16CoreTwoV := by
  intro ε hε0 hε4
  obtain ⟨c, C, x0, hc, hC, hx0, hS⟩ := h ε hε0 hε4
  refine ⟨c, C, x0, hc, hC, hx0, ?_⟩
  intro Pa hx φ ν z0 d k chi hTau hAxis hν0 hνlt hd1 hdl hk hchi β hβ
  obtain ⟨q, p, hqC, hpC, hq0, hq1, hqsupp, hqd, hp0, hp1, hpsupp, hpd, hβdef⟩ := hβ
  have hk3 : |(k : ℝ)| ≤ 3 * Real.exp (Real.sqrt (Real.log Pa.N)) := by
    have h0 : (0 : ℝ) ≤ Real.exp (Real.sqrt (Real.log Pa.N)) := (Real.exp_pos _).le
    nlinarith
  have key := hS Pa hx φ ν z0 d k chi q p hTau hAxis hν0 hνlt hd1 hdl hk3 hchi
    hqC hpC hq0 hq1 hqsupp hqd hp0 hp1 hpsupp hpd
  have heq : (∑ z ∈ Work.FITop.boxN Pa,
        β z * chi z * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ k)
      = ∑ z ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z
              ∧ (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ)
              ∧ Work.FITop4.SameClass8 z z0 ∧ Work.FITop4.IsAxisFree Pa z then
            ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ k
          else 0) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    exact Work.FIArea6.betaSummand_eq_radial Pa φ z0 k chi q p hqC hqsupp hpsupp hβdef z
  rw [heq]
  exact key

end

end Work.FIArea6V
