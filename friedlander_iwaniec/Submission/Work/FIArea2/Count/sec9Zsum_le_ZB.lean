import Mathlib
import Submission.Work.FIArea2.Count.sec9_Z_defs
import Submission.Work.FIArea2.Sec9AggDefs

namespace Work.FIArea2.Count

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Reindexing `gBox R` into coordinates -/

/-- Summing over the Gaussian box `gBox R` is summing over `Icc (-R) R × Icc (-R) R` in
coordinates. -/
lemma sum_gBox_eq (R : ℤ) (f : GaussianInt → ℝ) :
    ∑ z ∈ Work.FIPlan.gBox R, f z
      = ∑ r ∈ Finset.Icc (-R) R, ∑ s ∈ Finset.Icc (-R) R, f (⟨r, s⟩ : GaussianInt) := by
  unfold Work.FIPlan.gBox
  rw [Finset.product_eq_sprod]
  rw [Finset.sum_image]
  · rw [Finset.sum_product]
  · intro x _ y _ h
    exact Work.FIPlan.gaussMk_injective h

/-- Double sum over `gBox R` in coordinates. -/
lemma double_sum_gBox_eq (R : ℤ) (f : GaussianInt → GaussianInt → ℝ) :
    ∑ z1 ∈ Work.FIPlan.gBox R, ∑ z2 ∈ Work.FIPlan.gBox R, f z1 z2
      = ∑ r1 ∈ Finset.Icc (-R) R, ∑ s1 ∈ Finset.Icc (-R) R,
        ∑ r2 ∈ Finset.Icc (-R) R, ∑ s2 ∈ Finset.Icc (-R) R, f ⟨r1, s1⟩ ⟨r2, s2⟩ := by
  rw [sum_gBox_eq R (fun z1 => ∑ z2 ∈ Work.FIPlan.gBox R, f z1 z2)]
  refine Finset.sum_congr rfl (fun r1 _ => Finset.sum_congr rfl (fun s1 _ => ?_))
  rw [sum_gBox_eq R (fun z2 => f (⟨r1, s1⟩ : GaussianInt) z2)]

/-! ## The Gaussian-side weight and its coordinate form -/

/-- The summand of `sec9Zsum`: the coprimality-and-axis-avoidance indicator times
`τ(Δ)³|Δ|^{-1}(Λ,Δ)`. -/
def Wg (Pa : Work.FITop.Params) (h1 h2 : ℤ) (z1 z2 : GaussianInt) : ℝ :=
  if Work.FIPlan.GaussCoprime z1 z2 ∧ Work.FIArea2.IsAxisFree Pa z1
      ∧ Work.FIArea2.IsAxisFree Pa z2 then
    (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3 / (Work.FIPlan.absDelta z1 z2 : ℝ))
      * (Work.FIArea2.gcdDelta z1 z2 h1 h2 : ℝ)
  else 0

/-- `sec9Zsum` is the double `gBox`-sum of `Wg`. -/
lemma sec9Zsum_eq_Wg (Pa : Work.FITop.Params) (h1 h2 : ℤ) :
    Work.FIArea2.sec9Zsum Pa h1 h2
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa, Wg Pa h1 h2 z1 z2 := rfl

/-- Axis-avoidance of `⟨r,s⟩` in coordinates. -/
lemma isAxisFree_mk (Pa : Work.FITop.Params) (r s : ℤ) :
    Work.FIArea2.IsAxisFree Pa (⟨r, s⟩ : GaussianInt) ↔
      Real.sqrt (Pa.ϑ * Pa.N) < |(r : ℝ)| ∧ Real.sqrt (Pa.ϑ * Pa.N) < |(s : ℝ)| := by
  unfold Work.FIArea2.IsAxisFree
  simp

/-- The Gaussian weight at `(⟨r₁,s₁⟩,⟨r₂,s₂⟩)` equals the coordinate weight `ZW`. -/
lemma Wg_eq_ZW (h1 h2 r1 s1 r2 s2 : ℤ) :
    (((Work.FIPlan.absDelta (⟨r1, s1⟩ : GaussianInt) ⟨r2, s2⟩).divisors.card : ℝ) ^ 3
        / (Work.FIPlan.absDelta (⟨r1, s1⟩ : GaussianInt) ⟨r2, s2⟩ : ℝ))
      * (Work.FIArea2.gcdDelta (⟨r1, s1⟩ : GaussianInt) ⟨r2, s2⟩ h1 h2 : ℝ)
    = ZW h1 h2 r1 s1 r2 s2 := by
  unfold ZW
  rw [absDelta_eq, gcdDelta_eq]

/-- `ZW` is non-negative. -/
lemma ZW_nonneg (h1 h2 r1 s1 r2 s2 : ℤ) : 0 ≤ ZW h1 h2 r1 s1 r2 s2 := by
  unfold ZW
  apply mul_nonneg
  · apply div_nonneg
    · positivity
    · positivity
  · positivity

/-- Pointwise domination: dropping the coprimality indicator, and rewriting the axis-avoidance
condition in coordinates, makes the summand no smaller. -/
lemma Wg_le_term (Pa : Work.FITop.Params) (h1 h2 r1 s1 r2 s2 : ℤ) :
    Wg Pa h1 h2 ⟨r1, s1⟩ ⟨r2, s2⟩ ≤
      (if Real.sqrt (Pa.ϑ * Pa.N) < |(r1 : ℝ)| ∧ Real.sqrt (Pa.ϑ * Pa.N) < |(s1 : ℝ)|
          ∧ Real.sqrt (Pa.ϑ * Pa.N) < |(r2 : ℝ)| ∧ Real.sqrt (Pa.ϑ * Pa.N) < |(s2 : ℝ)|
        then ZW h1 h2 r1 s1 r2 s2 else 0) := by
  unfold Wg
  by_cases hP : Work.FIPlan.GaussCoprime ⟨r1, s1⟩ ⟨r2, s2⟩
      ∧ Work.FIArea2.IsAxisFree Pa ⟨r1, s1⟩ ∧ Work.FIArea2.IsAxisFree Pa ⟨r2, s2⟩
  · rw [if_pos hP]
    have hQ : Real.sqrt (Pa.ϑ * Pa.N) < |(r1 : ℝ)| ∧ Real.sqrt (Pa.ϑ * Pa.N) < |(s1 : ℝ)|
          ∧ Real.sqrt (Pa.ϑ * Pa.N) < |(r2 : ℝ)| ∧ Real.sqrt (Pa.ϑ * Pa.N) < |(s2 : ℝ)| := by
      have h1f := (isAxisFree_mk Pa r1 s1).mp hP.2.1
      have h2f := (isAxisFree_mk Pa r2 s2).mp hP.2.2
      exact ⟨h1f.1, h1f.2, h2f.1, h2f.2⟩
    rw [if_pos hQ]
    exact le_of_eq (Wg_eq_ZW h1 h2 r1 s1 r2 s2)
  · rw [if_neg hP]
    by_cases hQ : Real.sqrt (Pa.ϑ * Pa.N) < |(r1 : ℝ)| ∧ Real.sqrt (Pa.ϑ * Pa.N) < |(s1 : ℝ)|
          ∧ Real.sqrt (Pa.ϑ * Pa.N) < |(r2 : ℝ)| ∧ Real.sqrt (Pa.ϑ * Pa.N) < |(s2 : ℝ)|
    · rw [if_pos hQ]
      exact ZW_nonneg h1 h2 r1 s1 r2 s2
    · rw [if_neg hQ]

/-! ## The target -/

/-- **§9 (9.5) rewritten in rectangular coordinates.**

`sec9Zsum Pa h₁ h₂ = Σ_{z₁,z₂ ∈ boxN} [(z₁,z₂)=1 ∧ axis-free] τ(Δ)³(Λ,Δ)/|Δ|` is at most the
four-fold coordinate sum `ZB (radN Pa) h₁ h₂ (√(ϑN))` of
`Submission/Work/FIArea2/Count/sec9_Z_defs.lean`, which drops the coprimality indicator and writes
`Δ = r₁s₂ − r₂s₁`, `(Λ,Δ) = (|r₁h₁²−r₂h₂²|, |s₁h₁²−s₂h₂²|, |Δ|)`, `thr = √(ϑN)` for the
axis-avoidance `√(ϑN) < |Re z|, |Im z|`.

Ingredients: `sec9_Z_defs.gcdDelta_eq`, `sec9_Z_defs.absDelta_eq`, `sec9_Z_defs.mem_gBox_iff`,
`gaussMk_injective` (`gBox R` is the image of `Icc (-R) R × Icc (-R) R`), `Finset.sum_image`,
`Finset.sum_product`, and the pointwise bound `[coprime ∧ axisfree]·X ≤ [axisfree]·X` for the
non-negative weight `X = τ(Δ)³(Λ,Δ)/|Δ|`. -/
theorem sec9Zsum_le_ZB (Pa : Work.FITop.Params) (h1 h2 : ℤ) :
    Work.FIArea2.sec9Zsum Pa h1 h2
      ≤ ZB (Work.FITop.radN Pa) h1 h2 (Real.sqrt (Pa.ϑ * Pa.N)) := by
  rw [sec9Zsum_eq_Wg]
  simp only [Work.FITop.boxN]
  rw [double_sum_gBox_eq (Work.FITop.radN Pa) (Wg Pa h1 h2)]
  unfold ZB
  refine Finset.sum_le_sum (fun r1 _ => Finset.sum_le_sum (fun s1 _ =>
    Finset.sum_le_sum (fun r2 _ => Finset.sum_le_sum (fun s2 _ => ?_))))
  exact Wg_le_term Pa h1 h2 r1 s1 r2 s2

end

end Work.FIArea2.Count
