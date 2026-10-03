import Mathlib
import Submission.Work.FIArea6T.Defs

set_option autoImplicit false

namespace Work.FIArea6T

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- `logFac6` vanishes when `|Δ(z₁,z₂)| = 0`: the argument is `8|z₁z₂|/0 = 0` and `log 0 = 0`. -/
lemma logFac6_eq_zero_of_absDelta_eq_zero {z1 z2 : GaussianInt}
    (h : Work.FIPlan.absDelta z1 z2 = 0) : Work.FITop4.logFac6 z1 z2 = 0 := by
  simp [Work.FITop4.logFac6, h]

/-- For `0 < |Δ(z₁,z₂)| < 4` the index set `Sset z₁ z₂` of (8.16)/(10.13) is empty: every
`d ∈ Sset` satisfies `d ≥ 1` and `4d ∣ |Δ|`, so `4d ≤ |Δ|`, while `4d ≥ 4`. -/
lemma Sset_eq_empty_of_absDelta_lt_four {z1 z2 : GaussianInt}
    (hpos : 0 < Work.FIPlan.absDelta z1 z2) (h : Work.FIPlan.absDelta z1 z2 < 4) :
    Work.FITop4.Sset z1 z2 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  rw [Work.FITop4.Sset, Finset.mem_filter, Finset.mem_Icc] at hd
  obtain ⟨⟨hd1, _⟩, hdiv⟩ := hd
  have h4d : 4 * d ≤ Work.FIPlan.absDelta z1 z2 := Nat.le_of_dvd hpos hdiv
  omega

theorem InnerSum_zero (Pa : Work.FITop.Params)
    (cut : GaussianInt → GaussianInt → ℕ → ℝ) {z1 z2 : GaussianInt}
    (h : Work.FIPlan.absDelta z1 z2 < 4) :
    (∑ d ∈ Work.FITop4.Sset z1 z2,
        ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
          * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 : ℂ) = 0 := by
  by_cases habs : Work.FIPlan.absDelta z1 z2 = 0
  · have hlog : Work.FITop4.logFac6 z1 z2 = 0 := logFac6_eq_zero_of_absDelta_eq_zero habs
    apply Finset.sum_eq_zero
    intro d _
    simp [hlog]
  · have hpos : 0 < Work.FIPlan.absDelta z1 z2 := Nat.pos_of_ne_zero habs
    rw [Sset_eq_empty_of_absDelta_lt_four hpos h]
    simp

end

end Work.FIArea6T
