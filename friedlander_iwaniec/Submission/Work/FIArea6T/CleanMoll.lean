/-
# `Submission.Work.FIArea6T.CleanMoll` — a clean coefficient as *FI* (5.13) / (17.15)

The clean coefficient class `Work.FITop4.IsCleanCoeff6` is *FI* (5.13) restricted by (5.7)+(5.8)
with the angle written inside the support.  Area 7's τ-removal (§17 bridge) works with the *same*
coefficient written as `Work.FIArea7.betaTilde Pa q p φ z0 z`, i.e. with the angle factor
`q(arg z − φ)` pulled out of the support and the class/primary/small-prime conditions carried by
`Work.FIArea7.radBetaCls`.  This module records the two translations:

* `IsCleanCoeff6.exists_mollPair`: the `q, p` of (5.13) form an `Work.FIArea7.IsMollPair`
  (the hypothesis class of *FI* Prop. 17.2) and realise `β` by the (4.13) formula;
* `clean_eq_betaTilde`: on the support `(5.14)∧(5.8)∧(5.7)` the clean coefficient *is* `betaTilde`,
  and off it both sides vanish.
-/
import Mathlib
import Submission.Work.FIArea6T.Defs
import Submission.Work.FIArea7.Bridge17Defs

set_option autoImplicit false

namespace Work.FIArea6T

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- **The mollifiers of a clean coefficient.**  A clean coefficient comes with the pair `q, p` of
(5.13); as an `IsMollPair` (the hypothesis class of *FI* Prop. 17.2) plus the exact formula of
(4.13), which is `Work.FITop4.IsCleanCoeff6`'s last clause. -/
theorem IsCleanCoeff6.exists_mollPair {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsCleanCoeff6 Pa φ z0 β) :
    ∃ q p : ℝ → ℝ, Work.FIArea7.IsMollPair Pa q p ∧
      (∀ z : GaussianInt, β z =
        (if Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z
            ∧ Work.FITop4.SameClass8 z z0
         then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
                * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
                * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
         else 0)) := by
  obtain ⟨q, p, hc1, hc2, hq0, hq1, hqsupp, hqd, hp0, hp1, hpsupp, hpd, hβ⟩ := h
  exact ⟨q, p, ⟨hc1, hc2, fun α => ⟨hq0 α, hq1 α⟩, hqsupp, hqd,
    fun u => ⟨hp0 u, hp1 u⟩, hpsupp, hpd⟩, hβ⟩

/-- **A clean coefficient is area 7's `betaTilde` on its support.**  With the pair `q, p` of
(5.13),

  `β z = (if (5.14) ∧ (5.8) ∧ (5.7) then betaTilde Pa q p φ z0 z else 0)`.

On the support this is the (5.13) product, written as `q(arg z − φ)·radBetaCls`; both sides vanish
off it.  (`InPolarBox` carries the primarity (5.3), which is the `radBeta` support condition.) -/
theorem clean_eq_betaTilde {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsCleanCoeff6 Pa φ z0 β) :
    ∃ q p : ℝ → ℝ, Work.FIArea7.IsMollPair Pa q p ∧
      (∀ z : GaussianInt, β z =
        (if Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z
            ∧ Work.FITop4.SameClass8 z z0
         then Work.FIArea7.betaTilde Pa q p φ z0 z else 0)) := by
  obtain ⟨q, p, hmoll, hform⟩ := Work.FIArea6T.IsCleanCoeff6.exists_mollPair h
  refine ⟨q, p, hmoll, fun z => ?_⟩
  rw [hform z]
  by_cases hc : Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z
      ∧ Work.FITop4.SameClass8 z z0
  · rw [if_pos hc, if_pos hc]
    unfold Work.FIArea7.betaTilde Work.FIArea7.radBetaCls Work.FIArea7.radBeta
    rw [if_pos hc.2.2, if_pos ⟨hc.1.1, hc.2.1⟩]
    push_cast
    ring
  · rw [if_neg hc, if_neg hc]

end

end Work.FIArea6T
