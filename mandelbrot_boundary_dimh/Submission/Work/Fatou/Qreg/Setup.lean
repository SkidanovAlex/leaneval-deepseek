import Mathlib
import Submission.Work.Interfaces.Fatou

/-!
# Geometry of a near-translation on Shishikura's region `𝒬(b₁,b₂)`

Elementary helper lemmas shared by the proof of `MandelDim.FatouFundamental`
(Shishikura, Annals 1998, Prop. A.2.1(i)).

`MandelDim.Qreg b₁ b₂ = {z | (∀ a ∈ b₁, -|Im (z-a)| < Re (z-a)) ∧ (∀ b ∈ b₂, Re (z-b) < |Im (z-b)|)}`
is the intersection of a `270°` cone opening left (vertex `b₁`) and one opening right (vertex `b₂`);
`None` means the corresponding condition is vacuous.  A near-translation `F` on `𝒬` moves `Re` by
between `31/32` and `33/32` and `Im` by at most `1/32`.

The vertical strip `x₀ - 1 < Re z < x₀ + 3` is contained in `𝒬` as soon as `x₀ > Re b₁ + 1` and
`x₀ + 3 < Re b₂`; it is convex, and `F` is injective on it (mean value inequality).
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Work.Fatou.Qreg

open Set Metric Complex
open scoped Topology

noncomputable section

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}

/-- The vertical strip `x₀ - 1 < Re z < x₀ + 3`. -/
def strip (x₀ : ℝ) : Set ℂ := {z : ℂ | x₀ - 1 < z.re ∧ z.re < x₀ + 3}

lemma isOpen_strip (x₀ : ℝ) : IsOpen (strip x₀) := by
  have h1 : IsOpen {z : ℂ | x₀ - 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {z : ℂ | z.re < x₀ + 3} :=
    isOpen_lt Complex.continuous_re continuous_const
  exact h1.inter h2

lemma convex_strip (x₀ : ℝ) : Convex ℝ (strip x₀) := by
  rw [convex_iff_forall_pos]
  rintro z hz w hw a b ha hb hab
  have hre : (a • z + b • w).re = a * z.re + b * w.re := by
    simp [Complex.add_re, Complex.smul_re]
  simp only [strip, Set.mem_setOf_eq] at hz hw ⊢
  rw [hre]
  constructor
  · have h1 : a * (x₀ - 1) < a * z.re := mul_lt_mul_of_pos_left hz.1 ha
    have h2 : b * (x₀ - 1) < b * w.re := mul_lt_mul_of_pos_left hw.1 hb
    have h3 : a * (x₀ - 1) + b * (x₀ - 1) = x₀ - 1 := by
      rw [← add_mul, hab, one_mul]
    linarith
  · have h1 : a * z.re < a * (x₀ + 3) := mul_lt_mul_of_pos_left hz.2 ha
    have h2 : b * w.re < b * (x₀ + 3) := mul_lt_mul_of_pos_left hw.2 hb
    have h3 : a * (x₀ + 3) + b * (x₀ + 3) = x₀ + 3 := by
      rw [← add_mul, hab, one_mul]
    linarith

/-- The strip `x₀ - 1 < Re z < x₀ + 3` lies in `𝒬` as soon as `x₀` is `1` to the right of `b₁`
and `3` to the left of `b₂`. -/
lemma strip_subset_Qreg (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    strip x₀ ⊆ MandelDim.Qreg b₁ b₂ := by
  intro z hz
  simp only [strip, Set.mem_setOf_eq] at hz
  refine ⟨?_, ?_⟩
  · intro a ha
    have ha' := h₁ a ha
    have hpos : 0 < (z - a).re := by simp only [Complex.sub_re]; linarith
    calc -|(z - a).im| ≤ 0 := neg_nonpos.mpr (abs_nonneg _)
      _ < (z - a).re := hpos
  · intro b hb
    have hb' := h₂ b hb
    have hneg : (z - b).re < 0 := by simp only [Complex.sub_re]; linarith
    calc (z - b).re < 0 := hneg
      _ ≤ |(z - b).im| := abs_nonneg _

/-- A near-translation moves `Re` by between `31/32` and `33/32`. -/
lemma re_step_bounds {u : ℂ} (h : ‖F u - (u + 1)‖ ≤ (1 / 32 : ℝ)) :
    u.re + 31 / 32 ≤ (F u).re ∧ (F u).re ≤ u.re + 33 / 32 := by
  have h1 : |(F u - (u + 1)).re| ≤ (1 / 32 : ℝ) := le_trans (Complex.abs_re_le_norm _) h
  have h2 : (F u - (u + 1)).re = (F u).re - u.re - 1 := by
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; ring
  rw [h2] at h1
  have h3 := abs_le.mp h1
  constructor <;> linarith

/-- A near-translation moves `Im` by at most `1/32`. -/
lemma im_step_bounds {u : ℂ} (h : ‖F u - (u + 1)‖ ≤ (1 / 32 : ℝ)) :
    |(F u).im - u.im| ≤ (1 / 32 : ℝ) := by
  have h1 : |(F u - (u + 1)).im| ≤ (1 / 32 : ℝ) := le_trans (Complex.abs_im_le_norm _) h
  have h2 : (F u - (u + 1)).im = (F u).im - u.im := by
    simp only [Complex.sub_im, Complex.add_im, Complex.one_im]; ring
  rwa [h2] at h1

/-- One step of `F` preserves the `b₁`-part of `𝒬`: the quantity `Re (z-a) + |Im (z-a)|`
increases by at least `30/32`. -/
lemma b1_step {a w : ℂ} (hw : -|(w - a).im| < (w - a).re)
    (h : ‖F w - (w + 1)‖ ≤ (1 / 32 : ℝ)) :
    -|(F w - a).im| < (F w - a).re := by
  set ε : ℂ := F w - w - 1 with hεdef
  have hε : ‖ε‖ ≤ (1 / 32 : ℝ) := by
    rw [hεdef]
    rwa [show F w - (w + 1) = F w - w - 1 by ring] at h
  have hA : (w - a).re + (1 - ‖ε‖) ≤ (F w - a).re := by
    have heq : (F w - a).re = (w - a).re + 1 + ε.re := by
      rw [hεdef]; simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; ring
    have hεre : -‖ε‖ ≤ ε.re := (abs_le.mp (Complex.abs_re_le_norm ε)).1
    linarith
  have hB : |(w - a).im| - |ε.im| ≤ |(F w - a).im| := by
    have heq : (F w - a).im = (w - a).im + ε.im := by
      rw [hεdef]; simp only [Complex.sub_im, Complex.add_im, Complex.one_im]; ring
    have h2 : (F w - a).im - ε.im = (w - a).im := by rw [heq]; ring
    have h3 := abs_sub_le ((F w - a).im) (0 : ℝ) ε.im
    have hle : |(w - a).im| ≤ |(F w - a).im| + |ε.im| := by
      rw [← h2]; simpa using h3
    linarith
  have hC : 0 < (w - a).re + |(w - a).im| := by linarith
  have hD : |ε.im| ≤ ‖ε‖ := Complex.abs_im_le_norm ε
  linarith

/-- One step of `F` does not change the `b₂`-part of `𝒬` when `Re z < Re b₂`. -/
lemma b2_of_re_lt {z : ℂ} (h : ∀ b ∈ b₂, z.re < b.re) :
    ∀ b ∈ b₂, (z - b).re < |(z - b).im| := by
  intro b hb
  have hb' := h b hb
  have hneg : (z - b).re < 0 := by simp only [Complex.sub_re]; linarith
  calc (z - b).re < 0 := hneg
    _ ≤ |(z - b).im| := abs_nonneg _

end

end Work.Fatou.Qreg
