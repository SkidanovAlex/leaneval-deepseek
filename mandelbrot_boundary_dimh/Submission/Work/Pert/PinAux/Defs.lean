import Mathlib
import Submission.Work.Pert.PinAux.Basic

namespace Work.Pert.PinAux

open MandelDim Complex Metric

set_option linter.unusedVariables false

noncomputable section

/-!
# `Work.Pert.PinAux.Defs`

The asymptotic medial line of the gate `Qm Ξ α`, used by `medial_to_axis`.

Writing `A = (1/α).re`, `γ = (1/α).im` and `t = Im z`, the slice of the gate at height `t` is

  `sliceLo Ξ α t = Ξ - A - |t + γ| < x < |t| - Ξ = sliceHi Ξ t`,

so the medial point `med Ξ α t = xMid Ξ α t + i t`, `xMid Ξ α t = (|t| - |t+γ| - A)/2`.  For `t`
in the *upper wing* (`0 ≤ t` and `-γ ≤ t`) the medial abscissa is the constant

  `xInf α = -(A+γ)/2`,

and both margins at `xInf + i t` equal `t - tPlus Ξ α` with `tPlus Ξ α = Ξ - (A+γ)/2` (the height
of the pinch above which the upper wing lives).  Similarly, in the *lower wing* (`t ≤ 0`,
`t ≤ -γ`) the medial abscissa is `xInfNeg α = (γ - A)/2` (so `xInfNeg = xInf + γ`), the point is
`xInfNeg + i t`, and both margins equal `-t - tMinus Ξ α`, `tMinus Ξ α = Ξ - (A-γ)/2`.

Thus along each wing the medial points lie on a *fixed vertical line*: this is what makes the walk
from `med Ξ α t` to a base point of bounded height possible inside the gate.
-/

/-- The asymptotic medial abscissa of the upper wing. -/
def xInf (α : ℂ) : ℝ := -(((1 / α).re + (1 / α).im) / 2)

/-- The asymptotic medial abscissa of the lower wing. -/
def xInfNeg (α : ℂ) : ℝ := (((1 / α).im - (1 / α).re) / 2)

/-- The height of the pinch of the upper wing. -/
def tPlus (Ξ : ℝ) (α : ℂ) : ℝ := Ξ - (((1 / α).re + (1 / α).im) / 2)

/-- The height (up to sign) of the pinch of the lower wing. -/
def tMinus (Ξ : ℝ) (α : ℂ) : ℝ := Ξ - (((1 / α).re - (1 / α).im) / 2)

lemma xMid_eq_xInf {Ξ : ℝ} {α : ℂ} {s : ℝ} (hs0 : 0 ≤ s) (hsg : -(1 / α).im ≤ s) :
    xMid Ξ α s = xInf α := by
  simp only [xMid, xInf, sliceLo, sliceHi]
  rw [abs_of_nonneg hs0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ s + (1 / α).im)]
  ring

lemma xMid_eq_xInfNeg {Ξ : ℝ} {α : ℂ} {s : ℝ} (hs0 : s ≤ 0) (hsg : s ≤ -(1 / α).im) :
    xMid Ξ α s = xInfNeg α := by
  simp only [xMid, xInfNeg, sliceLo, sliceHi]
  rw [abs_of_nonpos hs0, abs_of_nonpos (by linarith : s + (1 / α).im ≤ 0)]
  ring

lemma margA_xInf {Ξ : ℝ} {α : ℂ} {s : ℝ} (hs0 : 0 ≤ s) (hsg : -(1 / α).im ≤ s) :
    margA Ξ α ((xInf α : ℂ) + (s : ℂ) * Complex.I) = s - tPlus Ξ α := by
  have hre : ((xInf α : ℂ) + (s : ℂ) * Complex.I).re = xInf α := by simp
  have him : ((xInf α : ℂ) + (s : ℂ) * Complex.I).im = s := by simp
  rw [margA, hre, him, tPlus, xInf,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ s + (1 / α).im)]
  ring

lemma margB_xInf {Ξ : ℝ} {α : ℂ} {s : ℝ} (hs0 : 0 ≤ s) (hsg : -(1 / α).im ≤ s) :
    margB Ξ α ((xInf α : ℂ) + (s : ℂ) * Complex.I) = s - tPlus Ξ α := by
  have hre : ((xInf α : ℂ) + (s : ℂ) * Complex.I).re = xInf α := by simp
  have him : ((xInf α : ℂ) + (s : ℂ) * Complex.I).im = s := by simp
  rw [margB, hre, him, tPlus, xInf, abs_of_nonneg hs0]
  ring

lemma margA_xInfNeg {Ξ : ℝ} {α : ℂ} {s : ℝ} (hs0 : s ≤ 0) (hsg : s ≤ -(1 / α).im) :
    margA Ξ α ((xInfNeg α : ℂ) + (s : ℂ) * Complex.I) = -s - tMinus Ξ α := by
  have hre : ((xInfNeg α : ℂ) + (s : ℂ) * Complex.I).re = xInfNeg α := by simp
  have him : ((xInfNeg α : ℂ) + (s : ℂ) * Complex.I).im = s := by simp
  rw [margA, hre, him, tMinus, xInfNeg,
    abs_of_nonpos (by linarith : s + (1 / α).im ≤ 0)]
  ring

lemma margB_xInfNeg {Ξ : ℝ} {α : ℂ} {s : ℝ} (hs0 : s ≤ 0) (hsg : s ≤ -(1 / α).im) :
    margB Ξ α ((xInfNeg α : ℂ) + (s : ℂ) * Complex.I) = -s - tMinus Ξ α := by
  have hre : ((xInfNeg α : ℂ) + (s : ℂ) * Complex.I).re = xInfNeg α := by simp
  have him : ((xInfNeg α : ℂ) + (s : ℂ) * Complex.I).im = s := by simp
  rw [margB, hre, him, tMinus, xInfNeg, abs_of_nonpos hs0]
  ring

lemma med_eq_xInf {Ξ : ℝ} {α : ℂ} {s : ℝ} (hs0 : 0 ≤ s) (hsg : -(1 / α).im ≤ s) :
    med Ξ α s = (xInf α : ℂ) + (s : ℂ) * Complex.I := by
  rw [med, xMid_eq_xInf hs0 hsg]

lemma med_eq_xInfNeg {Ξ : ℝ} {α : ℂ} {s : ℝ} (hs0 : s ≤ 0) (hsg : s ≤ -(1 / α).im) :
    med Ξ α s = (xInfNeg α : ℂ) + (s : ℂ) * Complex.I := by
  rw [med, xMid_eq_xInfNeg hs0 hsg]

/-- In the upper wing, the points of the vertical line at `xInf` belong to the gate as soon as
their height exceeds the pinch height `tPlus`. -/
lemma mem_Qm_xInf {Ξ : ℝ} {α : ℂ} {s : ℝ} (hs0 : 0 ≤ s) (hsg : -(1 / α).im ≤ s)
    (h : tPlus Ξ α < s) :
    ((xInf α : ℂ) + (s : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
  rw [mem_Qm_iff_marg, margA_xInf hs0 hsg, margB_xInf hs0 hsg]
  constructor <;> linarith

/-- In the lower wing, the points of the vertical line at `xInfNeg` belong to the gate as soon as
their height is below `-tMinus`. -/
lemma mem_Qm_xInfNeg {Ξ : ℝ} {α : ℂ} {s : ℝ} (hs0 : s ≤ 0) (hsg : s ≤ -(1 / α).im)
    (h : s < -tMinus Ξ α) :
    ((xInfNeg α : ℂ) + (s : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
  rw [mem_Qm_iff_marg, margA_xInfNeg hs0 hsg, margB_xInfNeg hs0 hsg]
  constructor <;> linarith

/-- The ball of radius `(s - tPlus)/√2` around the corridor point at height `s` is inside the
gate (upper wing). -/
lemma ball_xInf_subset_Qm {Ξ : ℝ} {α : ℂ} {s : ℝ} (hs0 : 0 ≤ s) (hsg : -(1 / α).im ≤ s)
    (h : tPlus Ξ α < s) :
    Metric.ball ((xInf α : ℂ) + (s : ℂ) * Complex.I) ((s - tPlus Ξ α) / Real.sqrt 2)
      ⊆ Work.Pert.Qm Ξ α := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ball_subset_Qm_of_marg_le (div_nonneg (by linarith) (Real.sqrt_nonneg 2)) ?_
  rw [margA_xInf hs0 hsg, margB_xInf hs0 hsg, min_self,
    mul_div_cancel₀ _ (ne_of_gt hs)]

/-- The ball of radius `(-s - tMinus)/√2` around the corridor point at height `s` is inside the
gate (lower wing). -/
lemma ball_xInfNeg_subset_Qm {Ξ : ℝ} {α : ℂ} {s : ℝ} (hs0 : s ≤ 0) (hsg : s ≤ -(1 / α).im)
    (h : s < -tMinus Ξ α) :
    Metric.ball ((xInfNeg α : ℂ) + (s : ℂ) * Complex.I) ((-s - tMinus Ξ α) / Real.sqrt 2)
      ⊆ Work.Pert.Qm Ξ α := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ball_subset_Qm_of_marg_le (div_nonneg (by linarith) (Real.sqrt_nonneg 2)) ?_
  rw [margA_xInfNeg hs0 hsg, margB_xInfNeg hs0 hsg, min_self,
    mul_div_cancel₀ _ (ne_of_gt hs)]

/-- The margins of `z` add up to twice the margin of the medial point at the same height. -/
lemma marg_add_med {Ξ : ℝ} {α : ℂ} {z : ℂ} :
    margA Ξ α z + margB Ξ α z = 2 * margA Ξ α (med Ξ α z.im) := by
  rw [marg_add, margA_med, width_eq]
  have h : z.im = (med Ξ α z.im).im := (med_im Ξ α z.im).symm
  rw [h]
  ring

/-- Moving `z` to the left by `r < R₁` keeps it in the ball of radius `R₁`, and decreases the
`A`-margin by exactly `r`: hence `ball z R₁ ⊆ Qm` forces `margA z ≥ R₁`. -/
lemma margA_ge_of_ball {Ξ R₁ : ℝ} {α : ℂ} {z : ℂ} (hR₁ : 0 < R₁)
    (hball : Metric.ball z R₁ ⊆ Work.Pert.Qm Ξ α) : R₁ ≤ margA Ξ α z := by
  have hzQ : z ∈ Work.Pert.Qm Ξ α := hball (Metric.mem_ball_self hR₁)
  have hzA : 0 < margA Ξ α z := ((mem_Qm_iff_marg Ξ α z).mp hzQ).1
  refine le_of_forall_lt (fun r hr => ?_)
  rcases lt_or_ge r 0 with hrneg | hrnn
  · linarith
  · have hmem : ((z.re - r : ℝ) : ℂ) + (z.im : ℂ) * Complex.I ∈ Work.Pert.Qm Ξ α := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : ((z.re - r : ℝ) : ℂ) + (z.im : ℂ) * Complex.I - z = ((-r : ℝ) : ℂ) := by
        rw [Complex.ext_iff]
        constructor <;> simp
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hrnn]
      exact hr
    have hA := ((mem_Qm_iff_marg Ξ α _).mp hmem).1
    have heq : margA Ξ α (((z.re - r : ℝ) : ℂ) + (z.im : ℂ) * Complex.I) = margA Ξ α z - r := by
      have h1 : (((z.re - r : ℝ) : ℂ) + (z.im : ℂ) * Complex.I).re = z.re - r := by simp
      have h2 : (((z.re - r : ℝ) : ℂ) + (z.im : ℂ) * Complex.I).im = z.im := by simp
      rw [margA, margA, h1, h2]
      ring
    rw [heq] at hA
    linarith

/-- Moving `z` to the right by `r < R₁` decreases the `B`-margin by exactly `r`: hence
`ball z R₁ ⊆ Qm` forces `margB z ≥ R₁`. -/
lemma margB_ge_of_ball {Ξ R₁ : ℝ} {α : ℂ} {z : ℂ} (hR₁ : 0 < R₁)
    (hball : Metric.ball z R₁ ⊆ Work.Pert.Qm Ξ α) : R₁ ≤ margB Ξ α z := by
  have hzQ : z ∈ Work.Pert.Qm Ξ α := hball (Metric.mem_ball_self hR₁)
  have hzB : 0 < margB Ξ α z := ((mem_Qm_iff_marg Ξ α z).mp hzQ).2
  refine le_of_forall_lt (fun r hr => ?_)
  rcases lt_or_ge r 0 with hrneg | hrnn
  · linarith
  · have hmem : ((z.re + r : ℝ) : ℂ) + (z.im : ℂ) * Complex.I ∈ Work.Pert.Qm Ξ α := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : ((z.re + r : ℝ) : ℂ) + (z.im : ℂ) * Complex.I - z = ((r : ℝ) : ℂ) := by
        rw [Complex.ext_iff]
        constructor <;> simp
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrnn]
      exact hr
    have hB := ((mem_Qm_iff_marg Ξ α _).mp hmem).2
    have heq : margB Ξ α (((z.re + r : ℝ) : ℂ) + (z.im : ℂ) * Complex.I) = margB Ξ α z - r := by
      have h1 : (((z.re + r : ℝ) : ℂ) + (z.im : ℂ) * Complex.I).re = z.re + r := by simp
      have h2 : (((z.re + r : ℝ) : ℂ) + (z.im : ℂ) * Complex.I).im = z.im := by simp
      rw [margB, margB, h1, h2]
      ring
    rw [heq] at hB
    linarith

/-- If the ball of radius `R₁` around `z` is inside the gate, then the medial point at the same
height also has both margins at least `R₁`. -/
lemma marg_med_ge_of_ball {Ξ R₁ : ℝ} {α : ℂ} {z : ℂ} (hR₁ : 0 < R₁)
    (hball : Metric.ball z R₁ ⊆ Work.Pert.Qm Ξ α) :
    R₁ ≤ margA Ξ α (med Ξ α z.im) ∧ R₁ ≤ margB Ξ α (med Ξ α z.im) := by
  have hA := margA_ge_of_ball hR₁ hball
  have hB := margB_ge_of_ball hR₁ hball
  have h2 : margA Ξ α (med Ξ α z.im) = margB Ξ α (med Ξ α z.im) := by
    rw [margA_med, margB_med]
  have hsum := marg_add_med (Ξ := Ξ) (α := α) (z := z)
  constructor
  · rw [h2]; linarith
  · rw [← h2]; linarith

lemma continuous_margA (Ξ : ℝ) (α : ℂ) : Continuous fun z : ℂ => margA Ξ α z := by
  simp only [margA]
  fun_prop

lemma continuous_margB (Ξ : ℝ) (α : ℂ) : Continuous fun z : ℂ => margB Ξ α z := by
  simp only [margB]
  fun_prop

/-- The gate is open. -/
lemma isOpen_Qm (Ξ : ℝ) (α : ℂ) : IsOpen (Work.Pert.Qm Ξ α) := by
  have h : Work.Pert.Qm Ξ α = {z : ℂ | 0 < margA Ξ α z} ∩ {z : ℂ | 0 < margB Ξ α z} := by
    ext z
    rw [mem_Qm_iff_marg, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_setOf_eq]
  rw [h]
  exact (isOpen_lt continuous_const (continuous_margA Ξ α)).inter
    (isOpen_lt continuous_const (continuous_margB Ξ α))

end

end Work.Pert.PinAux
