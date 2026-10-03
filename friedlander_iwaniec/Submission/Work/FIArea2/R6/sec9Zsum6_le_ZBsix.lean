import Mathlib
import Submission.Work.FIArea2.R6.SixDefs
import Submission.Work.FIArea2.Count.sec9Zsum_le_ZB

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# `sec9Zsum6 ≤ ZB (radN Pa) h₁ h₂ (ϑ√N)` — the coordinate domination at the sector threshold

`sec9Zsum6` is the §9 per-frequency weight sum (9.5) at the *sector-scale* axis threshold
`Work.FITop4.IsAxisFree` (`ϑ√N < |Re z|,|Im z|`).  This is the exact mirror of
`Work.FIArea2.Count.sec9Zsum_le_ZB` (which is at the stronger threshold `√(ϑN)`): after
reindexing `boxN Pa = gBox (radN Pa)` into rectangular coordinates, the summand
`[coprime ∧ axis-free]·τ(Δ)³(Λ,Δ)/|Δ|` is at most `[axis-free]·ZW`, since the coprimality
indicator is dropped and the axis-avoidance is written in coordinates.  The only change from the
`√(ϑN)` version is that the threshold is now `ϑ√N`, which is exactly what `FITop4.IsAxisFree`
unfolds to.
-/

/-- The Gaussian-side weight of the §9 sum (9.5) at the sector-scale threshold:
`τ(Δ)³|Δ|⁻¹·(Λ,Δ)` on the coprime, `FITop4.IsAxisFree` pairs, and `0` otherwise. -/
def Wg6 (Pa : Work.FITop.Params) (h1 h2 : ℤ) (z1 z2 : GaussianInt) : ℝ :=
  if Work.FIPlan.GaussCoprime z1 z2 ∧ Work.FITop4.IsAxisFree Pa z1
      ∧ Work.FITop4.IsAxisFree Pa z2 then
    (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3
      / (Work.FIPlan.absDelta z1 z2 : ℝ)) * (Work.FIArea2.gcdDelta z1 z2 h1 h2 : ℝ)
  else 0

/-- `sec9Zsum6` is the double `gBox`-sum of `Wg6`. -/
lemma sec9Zsum6_eq_Wg6 (Pa : Work.FITop.Params) (h1 h2 : ℤ) :
    sec9Zsum6 Pa h1 h2
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa, Wg6 Pa h1 h2 z1 z2 := by
  rw [sec9Zsum6_eq]
  refine Finset.sum_congr rfl fun z1 _ => Finset.sum_congr rfl fun z2 _ => ?_
  unfold Wg6 sec9Core6
  by_cases h : Work.FIPlan.GaussCoprime z1 z2 ∧ Work.FITop4.IsAxisFree Pa z1
      ∧ Work.FITop4.IsAxisFree Pa z2 <;> simp [h]

/-- Axis-avoidance of `⟨r,s⟩` at the sector threshold `ϑ√N`, in coordinates. -/
lemma isAxisFree6_mk (Pa : Work.FITop.Params) (r s : ℤ) :
    Work.FITop4.IsAxisFree Pa (⟨r, s⟩ : GaussianInt) ↔
      Pa.ϑ * Real.sqrt Pa.N < |(r : ℝ)| ∧ Pa.ϑ * Real.sqrt Pa.N < |(s : ℝ)| := Iff.rfl

/-- Pointwise domination: dropping the coprimality indicator and writing the axis-avoidance in
coordinates makes the summand no smaller. -/
lemma Wg6_le_term (Pa : Work.FITop.Params) (h1 h2 r1 s1 r2 s2 : ℤ) :
    Wg6 Pa h1 h2 ⟨r1, s1⟩ ⟨r2, s2⟩ ≤
      (if Pa.ϑ * Real.sqrt Pa.N < |(r1 : ℝ)| ∧ Pa.ϑ * Real.sqrt Pa.N < |(s1 : ℝ)|
          ∧ Pa.ϑ * Real.sqrt Pa.N < |(r2 : ℝ)| ∧ Pa.ϑ * Real.sqrt Pa.N < |(s2 : ℝ)|
        then Work.FIArea2.Count.ZW h1 h2 r1 s1 r2 s2 else 0) := by
  unfold Wg6
  by_cases hP : Work.FIPlan.GaussCoprime ⟨r1, s1⟩ ⟨r2, s2⟩
      ∧ Work.FITop4.IsAxisFree Pa ⟨r1, s1⟩ ∧ Work.FITop4.IsAxisFree Pa ⟨r2, s2⟩
  · rw [if_pos hP]
    have hQ : Pa.ϑ * Real.sqrt Pa.N < |(r1 : ℝ)| ∧ Pa.ϑ * Real.sqrt Pa.N < |(s1 : ℝ)|
        ∧ Pa.ϑ * Real.sqrt Pa.N < |(r2 : ℝ)| ∧ Pa.ϑ * Real.sqrt Pa.N < |(s2 : ℝ)| := by
      have h1f := (isAxisFree6_mk Pa r1 s1).mp hP.2.1
      have h2f := (isAxisFree6_mk Pa r2 s2).mp hP.2.2
      exact ⟨h1f.1, h1f.2, h2f.1, h2f.2⟩
    rw [if_pos hQ]
    exact le_of_eq (Work.FIArea2.Count.Wg_eq_ZW h1 h2 r1 s1 r2 s2)
  · rw [if_neg hP]
    by_cases hQ : Pa.ϑ * Real.sqrt Pa.N < |(r1 : ℝ)| ∧ Pa.ϑ * Real.sqrt Pa.N < |(s1 : ℝ)|
        ∧ Pa.ϑ * Real.sqrt Pa.N < |(r2 : ℝ)| ∧ Pa.ϑ * Real.sqrt Pa.N < |(s2 : ℝ)|
    · rw [if_pos hQ]
      exact Work.FIArea2.Count.ZW_nonneg h1 h2 r1 s1 r2 s2
    · rw [if_neg hQ]

theorem sec9Zsum6_le_ZBsix (Pa : Work.FITop.Params) (h1 h2 : ℤ) :
    Work.FIArea2.R6.sec9Zsum6 Pa h1 h2 ≤ Work.FIArea2.Count.ZB (Work.FITop.radN Pa) h1 h2
      (Pa.ϑ * Real.sqrt Pa.N) := by
  rw [sec9Zsum6_eq_Wg6]
  simp only [Work.FITop.boxN]
  rw [Work.FIArea2.Count.double_sum_gBox_eq (Work.FITop.radN Pa) (Wg6 Pa h1 h2)]
  unfold Work.FIArea2.Count.ZB
  refine Finset.sum_le_sum (fun r1 _ => Finset.sum_le_sum (fun s1 _ =>
    Finset.sum_le_sum (fun r2 _ => Finset.sum_le_sum (fun s2 _ => ?_))))
  exact Wg6_le_term Pa h1 h2 r1 s1 r2 s2

end

end Work.FIArea2.R6
