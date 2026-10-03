import Mathlib
import Submission.Work.FatouL1.cauchyLineBound
import Submission.Work.FatouL1.DefsLower

/-!
# FATOU-L1: the cotangent boundary integral on a rectangle

`rectB a' b' Y (fun ζ => h ζ * (I / 2 * cot (π (ζ - z)))) = -h z`

whenever `h` is holomorphic on the strip `{a < Re < b}`, the rectangle `[a',b'] × [-Y,Y]` sits
strictly inside that strip, and `z` is strictly inside the rectangle.

The proof is the residue computation at the simple pole `ζ = z`: `(I/2) cot (π (ζ - z))` and
`I / (2π (ζ - z))` have the same residue `I/(2π)` at `ζ = z`, so their difference is holomorphic
on the closed rectangle and its boundary integral vanishes (Cauchy).  Hence

`rectB f = rectB (I/(2π) · h/(ζ - z)) = (I/(2π)) · 2πI · h z = -h z`,

the middle equality being the winding-number computation `rectCauchy`.
-/

namespace Work.FatouL1

open MeasureTheory
open scoped Topology

noncomputable section

/-- Cauchy's theorem on a rectangle, written in the `rectB` normalisation: a function that is
holomorphic on the closed rectangle has vanishing boundary integral. -/
lemma rectB_eq_zero_of_differentiableOn {a b Y : ℝ} (hab : a < b) (hY : -Y < Y)
    {f : ℂ → ℂ} (hdiff : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc (-Y) Y)) :
    rectB a b Y f = 0 := by
  have hcont : ContinuousOn f (Set.uIcc a b ×ℂ Set.uIcc (-Y) Y) := hdiff.continuousOn
  have hsub : Set.Ioo (min a b) (max a b) ×ℂ Set.Ioo (min (-Y) Y) (max (-Y) Y)
      ⊆ Set.uIcc a b ×ℂ Set.uIcc (-Y) Y := by
    rw [min_eq_left hab.le, max_eq_right hab.le, min_eq_left hY.le, max_eq_right hY.le]
    rw [Complex.reProdIm_subset_iff]
    exact Set.prod_mono (Set.Ioo_subset_Icc_self.trans Set.Icc_subset_uIcc)
      (Set.Ioo_subset_Icc_self.trans Set.Icc_subset_uIcc)
  have hd : ∀ x ∈ Set.Ioo (min a b) (max a b) ×ℂ Set.Ioo (min (-Y) Y) (max (-Y) Y)
      \ (∅ : Set ℂ), DifferentiableAt ℂ f x := by
    intro x hx
    rw [Set.sdiff_empty] at hx
    exact hdiff.differentiableAt
      (Filter.mem_of_superset ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hx) hsub)
  have key := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    f (⟨a, -Y⟩ : ℂ) (⟨b, Y⟩ : ℂ) (∅ : Set ℂ) Set.countable_empty hcont hd
  rw [rectB_eq_rect]
  exact key

/-- `rectB` is additive on functions that are integrable along the four edges of the rectangle. -/
lemma rectB_add {a b Y : ℝ} {f g : ℂ → ℂ}
    (h1 : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (-Y) * Complex.I)) volume a b)
    (h2 : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (-Y) * Complex.I)) volume a b)
    (h3 : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + Y * Complex.I)) volume a b)
    (h4 : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + Y * Complex.I)) volume a b)
    (h5 : IntervalIntegrable (fun y : ℝ => f ((b : ℂ) + y * Complex.I)) volume (-Y) Y)
    (h6 : IntervalIntegrable (fun y : ℝ => g ((b : ℂ) + y * Complex.I)) volume (-Y) Y)
    (h7 : IntervalIntegrable (fun y : ℝ => f ((a : ℂ) + y * Complex.I)) volume (-Y) Y)
    (h8 : IntervalIntegrable (fun y : ℝ => g ((a : ℂ) + y * Complex.I)) volume (-Y) Y) :
    rectB a b Y (fun ζ => f ζ + g ζ) = rectB a b Y f + rectB a b Y g := by
  simp only [rectB]
  rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_add h3 h4,
      intervalIntegral.integral_add h5 h6, intervalIntegral.integral_add h7 h8]
  ring

/-- `rectB` is homogeneous (unconditionally). -/
lemma rectB_const_mul (a b Y : ℝ) (c : ℂ) (f : ℂ → ℂ) :
    rectB a b Y (fun ζ => c * f ζ) = c * rectB a b Y f := by
  simp only [rectB, intervalIntegral.integral_const_mul]
  ring

section Edges

variable {a b Y : ℝ}

/-- Continuity along the bottom edge. -/
lemma continuousOn_edge_bot {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.uIcc a b ×ℂ Set.uIcc (-Y) Y)) :
    ContinuousOn (fun x : ℝ => f ((x : ℂ) + (-Y) * Complex.I)) (Set.uIcc a b) :=
  hf.comp ((Complex.continuous_ofReal.add continuous_const).continuousOn)
    (fun x hx => by
      rw [Complex.mem_reProdIm]
      exact ⟨by simpa using hx, by simp⟩)

/-- Continuity along the top edge. -/
lemma continuousOn_edge_top {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.uIcc a b ×ℂ Set.uIcc (-Y) Y)) :
    ContinuousOn (fun x : ℝ => f ((x : ℂ) + Y * Complex.I)) (Set.uIcc a b) :=
  hf.comp ((Complex.continuous_ofReal.add continuous_const).continuousOn)
    (fun x hx => by
      rw [Complex.mem_reProdIm]
      exact ⟨by simpa using hx, by simp⟩)

/-- Continuity along the right edge. -/
lemma continuousOn_edge_right {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.uIcc a b ×ℂ Set.uIcc (-Y) Y)) :
    ContinuousOn (fun y : ℝ => f ((b : ℂ) + y * Complex.I)) (Set.uIcc (-Y) Y) :=
  hf.comp ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn)
    (fun y hy => by
      rw [Complex.mem_reProdIm]
      exact ⟨by simp, by simpa using hy⟩)

/-- Continuity along the left edge. -/
lemma continuousOn_edge_left {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.uIcc a b ×ℂ Set.uIcc (-Y) Y)) :
    ContinuousOn (fun y : ℝ => f ((a : ℂ) + y * Complex.I)) (Set.uIcc (-Y) Y) :=
  hf.comp ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn)
    (fun y hy => by
      rw [Complex.mem_reProdIm]
      exact ⟨by simp, by simpa using hy⟩)

/-- Auxiliary: `h (φ t) * (I / (2π (φ t - z)))` is continuous on `s` as soon as `φ` and
`h ∘ φ` are, and `φ` avoids `z`. -/
lemma continuousOn_mul_div_sub {h : ℂ → ℂ} {z : ℂ} {s : Set ℝ} {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ s) (hne : ∀ t ∈ s, φ t ≠ z)
    (hh : ContinuousOn (fun t : ℝ => h (φ t)) s) :
    ContinuousOn (fun t : ℝ => h (φ t) * (Complex.I / (2 * Real.pi * (φ t - z)))) s := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  refine hh.mul (continuousOn_const.div (continuousOn_const.mul (hφ.sub continuousOn_const)) ?_)
  intro t ht
  exact mul_ne_zero hpi (sub_ne_zero.mpr (hne t ht))

end Edges


theorem hcRectCot {a b : ℝ} {h : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ h {z : ℂ | a < z.re ∧ z.re < b})
    {a' b' Y : ℝ} {z : ℂ}
    (ha : a < a') (hb : b' < b) (ha'z : a' < z.re) (hzb' : z.re < b')
    (hYl : -Y < z.im) (hYr : z.im < Y)
    (hdiff : DifferentiableOn ℂ
      (fun ζ => h ζ * (Complex.I / 2 * Complex.cot (Real.pi * (ζ - z))
        - Complex.I / (2 * Real.pi * (ζ - z))))
      (Set.uIcc a' b' ×ℂ Set.uIcc (-Y) Y)) :
    rectB a' b' Y (fun ζ => h ζ * (Complex.I / 2 * Complex.cot (Real.pi * (ζ - z)))) = -h z := by
  have hab : a' < b' := lt_trans ha'z hzb'
  have hY : -Y < Y := lt_trans hYl hYr
  -- the rectangle lies strictly inside the strip
  have hrect : Set.uIcc a' b' ×ℂ Set.uIcc (-Y) Y ⊆ {w : ℂ | a < w.re ∧ w.re < b} := by
    intro w hw
    rw [Complex.mem_reProdIm] at hw
    have h1 := hw.1
    rw [Set.uIcc_of_le hab.le, Set.mem_Icc] at h1
    exact ⟨lt_of_lt_of_le ha h1.1, lt_of_le_of_lt h1.2 hb⟩
  have hhol' : DifferentiableOn ℂ h (Set.uIcc a' b' ×ℂ Set.uIcc (-Y) Y) := hhol.mono hrect
  set F : ℂ → ℂ := fun ζ => h ζ * (Complex.I / 2 * Complex.cot (Real.pi * (ζ - z))) with hFdef
  set Hd : ℂ → ℂ := fun ζ => h ζ * (Complex.I / 2 * Complex.cot (Real.pi * (ζ - z))
        - Complex.I / (2 * Real.pi * (ζ - z))) with hHddef
  set g : ℂ → ℂ := fun ζ => h ζ * (Complex.I / (2 * Real.pi * (ζ - z))) with hgdef
  have hsplit : ∀ ζ : ℂ, F ζ = Hd ζ + g ζ := by
    intro ζ
    simp only [hFdef, hHddef, hgdef]
    ring
  have hHdcont : ContinuousOn Hd (Set.uIcc a' b' ×ℂ Set.uIcc (-Y) Y) := by
    rw [hHddef]; exact hdiff.continuousOn
  have hHd0 : rectB a' b' Y Hd = 0 := by
    rw [hHddef]; exact rectB_eq_zero_of_differentiableOn hab hY hdiff
  -- the "residue" summand is continuous along every edge of the rectangle
  have hgbot : ContinuousOn (fun x : ℝ => g ((x : ℂ) + (-Y) * Complex.I)) (Set.uIcc a' b') := by
    rw [hgdef]
    refine continuousOn_mul_div_sub (φ := fun x : ℝ => (x : ℂ) + (-Y) * Complex.I) ?_ ?_ ?_
    · exact (Complex.continuous_ofReal.add continuous_const).continuousOn
    · intro x _ hcon
      have h := congrArg Complex.im hcon
      simp at h
      linarith
    · exact continuousOn_edge_bot hhol'.continuousOn
  have hgtop : ContinuousOn (fun x : ℝ => g ((x : ℂ) + Y * Complex.I)) (Set.uIcc a' b') := by
    rw [hgdef]
    refine continuousOn_mul_div_sub (φ := fun x : ℝ => (x : ℂ) + Y * Complex.I) ?_ ?_ ?_
    · exact (Complex.continuous_ofReal.add continuous_const).continuousOn
    · intro x _ hcon
      have h := congrArg Complex.im hcon
      simp at h
      linarith
    · exact continuousOn_edge_top hhol'.continuousOn
  have hgright : ContinuousOn (fun y : ℝ => g ((b' : ℂ) + y * Complex.I)) (Set.uIcc (-Y) Y) := by
    rw [hgdef]
    refine continuousOn_mul_div_sub (φ := fun y : ℝ => (b' : ℂ) + y * Complex.I) ?_ ?_ ?_
    · exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
    · intro y _ hcon
      have h := congrArg Complex.re hcon
      simp at h
      linarith
    · exact continuousOn_edge_right (a := a') (b := b') hhol'.continuousOn
  have hgleft : ContinuousOn (fun y : ℝ => g ((a' : ℂ) + y * Complex.I)) (Set.uIcc (-Y) Y) := by
    rw [hgdef]
    refine continuousOn_mul_div_sub (φ := fun y : ℝ => (a' : ℂ) + y * Complex.I) ?_ ?_ ?_
    · exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
    · intro y _ hcon
      have h := congrArg Complex.re hcon
      simp at h
      linarith
    · exact continuousOn_edge_left (a := a') (b := b') hhol'.continuousOn
  -- split `rectB F = rectB Hd + rectB g`
  have hF_eq : rectB a' b' Y F = rectB a' b' Y Hd + rectB a' b' Y g := by
    have hadd := rectB_add (a := a') (b := b') (Y := Y) (f := Hd) (g := g)
      (continuousOn_edge_bot hHdcont).intervalIntegrable hgbot.intervalIntegrable
      (continuousOn_edge_top hHdcont).intervalIntegrable hgtop.intervalIntegrable
      (continuousOn_edge_right (a := a') (b := b') hHdcont).intervalIntegrable
        hgright.intervalIntegrable
      (continuousOn_edge_left (a := a') (b := b') hHdcont).intervalIntegrable
        hgleft.intervalIntegrable
    rw [show F = (fun ζ => Hd ζ + g ζ) by funext ζ; exact hsplit ζ]
    exact hadd
  -- the residue integral
  have hgval : rectB a' b' Y g = -h z := by
    have hg_eq : g = fun ζ => (Complex.I / (2 * Real.pi)) * (h ζ * (ζ - z)⁻¹) := by
      funext ζ
      simp only [hgdef]
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hg_eq, rectB_const_mul]
    rw [show rectB a' b' Y (fun ζ => h ζ * (ζ - z)⁻¹) = 2 * Real.pi * Complex.I * h z from by
      simpa only [div_eq_mul_inv] using rectCauchy ha'z hzb' hYl hYr hhol']
    field_simp
    rw [sq, Complex.I_mul_I]
    ring
  change rectB a' b' Y F = -h z
  rw [hF_eq, hHd0, zero_add, hgval]


end

end Work.FatouL1
