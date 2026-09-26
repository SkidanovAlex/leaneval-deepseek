/-
# The weight-shape calculus on the cusp-`0` tile `E`

`Bdd c F` records the bound `‖F w‖ ≤ C (scale w)^N e^{c Im (S • w)}` for `w ∈ E`, with `C, N`
existential.  The calculus is closed under products (additive `c`), sums (max of exponents),
scalar multiples and weakening of `c`, which is what the tail estimates on `E` need.
-/
import Mathlib
import Submission.Work.Asymptotics.EtailE.Basic

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm

namespace Work.Asymptotics.EtailE

open Work.Kernels

lemma E_scale_pos (w : ℍ) : 0 < scale w := Work.Kernels.scale_pos w

lemma E_rpow_nonneg (w : ℍ) (N : ℝ) : 0 ≤ (scale w) ^ N :=
  Real.rpow_nonneg (le_of_lt (E_scale_pos w)) N

lemma E_one_le_rpow (w : ℍ) {N : ℝ} (hN : 0 ≤ N) : 1 ≤ (scale w) ^ N :=
  Real.one_le_rpow (Work.Kernels.one_le_scale w) hN

lemma E_rpow_mono (w : ℍ) {N M : ℝ} (h : N ≤ M) : (scale w) ^ N ≤ (scale w) ^ M :=
  Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) h

lemma E_rpow_mul (w : ℍ) (N M : ℝ) : (scale w) ^ N * (scale w) ^ M = (scale w) ^ (N + M) :=
  (Real.rpow_add (E_scale_pos w) N M).symm

lemma E_im_S_nonneg {w : ℍ} (hw : w ∈ KEpsilon) : 0 ≤ (ModularGroup.S • w).im := by
  linarith [hw.2]

/-- The threshold condition of the tail estimates on `E`: `t ≥ 2 Im (S • w) + 1` (so that the
contour point `z = i t` lies above all the poles of `z ↦ K(w,z)`, which are the
`SL(2,ℤ)`-translates of `w`). -/
def Ethresh (w : ℍ) (t : ℝ) : Prop := 2 * (ModularGroup.S • w).im + 1 ≤ t

/-- The bound shape `‖F w‖ ≤ C (scale w)^N e^{c Im (S • w)}` for `w ∈ E`. -/
def Bdd (c : ℝ) (F : ℍ → ℂ) : Prop :=
  ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ w : ℍ,
    w ∈ KEpsilon → ‖F w‖ ≤ C * (scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im)

namespace Bdd

variable {c c1 c2 : ℝ} {F G : ℍ → ℂ}

lemma congr (h : F = G) (hF : Bdd c F) : Bdd c G := h ▸ hF

lemma mono {c c' : ℝ} (hcc : c ≤ c') (hF : Bdd c F) : Bdd c' F := by
  obtain ⟨C, N, hC, hN, hb⟩ := hF
  refine ⟨C, N, hC, hN, fun w hw => ?_⟩
  refine le_trans (hb w hw) ?_
  have h1 : Real.exp (c * (ModularGroup.S • w).im) ≤ Real.exp (c' * (ModularGroup.S • w).im) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcc (E_im_S_nonneg hw))
  have h2 : (0:ℝ) ≤ C * (scale w) ^ N := mul_nonneg hC.le (E_rpow_nonneg w N)
  exact mul_le_mul_of_nonneg_left h1 h2

lemma mul (hF : Bdd c1 F) (hG : Bdd c2 G) : Bdd (c1 + c2) (fun w => F w * G w) := by
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := hF
  obtain ⟨C2, N2, hC2, hN2, hb2⟩ := hG
  refine ⟨C1 * C2, N1 + N2, by positivity, by positivity, fun w hw => ?_⟩
  have h1 := hb1 w hw
  have h2 := hb2 w hw
  rw [norm_mul]
  have key1 : (scale w) ^ N1 * (scale w) ^ N2 = (scale w) ^ (N1 + N2) := E_rpow_mul w N1 N2
  have key2 : Real.exp (c1 * (ModularGroup.S • w).im) * Real.exp (c2 * (ModularGroup.S • w).im)
      = Real.exp ((c1 + c2) * (ModularGroup.S • w).im) := by
    rw [← Real.exp_add]; congr 1; ring
  calc ‖F w‖ * ‖G w‖
      ≤ (C1 * (scale w) ^ N1 * Real.exp (c1 * (ModularGroup.S • w).im))
        * (C2 * (scale w) ^ N2 * Real.exp (c2 * (ModularGroup.S • w).im)) :=
        mul_le_mul h1 h2 (norm_nonneg _)
          (mul_nonneg (mul_nonneg hC1.le (E_rpow_nonneg w N1)) (Real.exp_pos _).le)
    _ = C1 * C2 * (scale w) ^ (N1 + N2)
          * Real.exp ((c1 + c2) * (ModularGroup.S • w).im) := by
        rw [show C1 * (scale w) ^ N1 * Real.exp (c1 * (ModularGroup.S • w).im)
              * (C2 * (scale w) ^ N2 * Real.exp (c2 * (ModularGroup.S • w).im))
            = C1 * C2 * ((scale w) ^ N1 * (scale w) ^ N2)
              * (Real.exp (c1 * (ModularGroup.S • w).im)
                  * Real.exp (c2 * (ModularGroup.S • w).im)) from by ring,
          key1, key2]

lemma add (hF : Bdd c F) (hG : Bdd c G) : Bdd c (fun w => F w + G w) := by
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := hF
  obtain ⟨C2, N2, hC2, hN2, hb2⟩ := hG
  refine ⟨C1 + C2, max N1 N2, by positivity, le_max_of_le_left hN1, fun w hw => ?_⟩
  refine le_trans (norm_add_le _ _) ?_
  have e1 := hb1 w hw
  have e2 := hb2 w hw
  have hN1' : (scale w) ^ N1 ≤ (scale w) ^ (max N1 N2) := E_rpow_mono w (le_max_left _ _)
  have hN2' : (scale w) ^ N2 ≤ (scale w) ^ (max N1 N2) := E_rpow_mono w (le_max_right _ _)
  have he : (0:ℝ) < Real.exp (c * (ModularGroup.S • w).im) := Real.exp_pos _
  have h1 : C1 * (scale w) ^ N1 * Real.exp (c * (ModularGroup.S • w).im)
      ≤ C1 * (scale w) ^ (max N1 N2) * Real.exp (c * (ModularGroup.S • w).im) := by
    refine mul_le_mul_of_nonneg_right ?_ he.le
    exact mul_le_mul_of_nonneg_left hN1' hC1.le
  have h2 : C2 * (scale w) ^ N2 * Real.exp (c * (ModularGroup.S • w).im)
      ≤ C2 * (scale w) ^ (max N1 N2) * Real.exp (c * (ModularGroup.S • w).im) := by
    refine mul_le_mul_of_nonneg_right ?_ he.le
    exact mul_le_mul_of_nonneg_left hN2' hC2.le
  calc ‖F w‖ + ‖G w‖
      ≤ C1 * (scale w) ^ (max N1 N2) * Real.exp (c * (ModularGroup.S • w).im)
        + C2 * (scale w) ^ (max N1 N2) * Real.exp (c * (ModularGroup.S • w).im) :=
        add_le_add (le_trans e1 h1) (le_trans e2 h2)
    _ = (C1 + C2) * (scale w) ^ (max N1 N2) * Real.exp (c * (ModularGroup.S • w).im) := by ring

/-- Products of moderate (`Bdd 0`) quantities. -/
lemma mul_zero (hF : Bdd 0 F) (hG : Bdd 0 G) : Bdd 0 (fun w => F w * G w) := by
  simpa using hF.mul hG

lemma neg (hF : Bdd c F) : Bdd c (fun w => -F w) := by
  obtain ⟨C, N, hC, hN, hb⟩ := hF
  exact ⟨C, N, hC, hN, fun w hw => by rw [norm_neg]; exact hb w hw⟩

lemma sub (hF : Bdd c F) (hG : Bdd c G) : Bdd c (fun w => F w - G w) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

lemma const_mul (d : ℂ) (hF : Bdd c F) : Bdd c (fun w => d * F w) := by
  obtain ⟨C, N, hC, hN, hb⟩ := hF
  refine ⟨‖d‖ * C + 1, N, by positivity, hN, fun w hw => ?_⟩
  rw [norm_mul]
  have h1 : ‖d‖ * ‖F w‖ ≤ ‖d‖ * (C * (scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im)) :=
    mul_le_mul_of_nonneg_left (hb w hw) (norm_nonneg d)
  have h0 : (0:ℝ) ≤ (scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im) :=
    mul_nonneg (E_rpow_nonneg w N) (Real.exp_pos _).le
  have h2 : (0:ℝ) < C := hC
  nlinarith [h1, h0, h2, norm_nonneg d, E_rpow_nonneg w N, Real.exp_pos (c * (ModularGroup.S • w).im)]

lemma one (c : ℝ) (hc : 0 ≤ c) : Bdd c (fun _ : ℍ => (1 : ℂ)) := by
  refine ⟨1, 0, one_pos, le_rfl, fun w hw => ?_⟩
  rw [norm_one, Real.rpow_zero, mul_one, one_mul]
  have h1 : (0:ℝ) ≤ c * (ModularGroup.S • w).im :=
    mul_nonneg hc (E_im_S_nonneg hw)
  calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp (c * (ModularGroup.S • w).im) := Real.exp_le_exp.mpr h1

/-- A constant is of shape `0`. -/
lemma const (d : ℂ) : Bdd 0 (fun _ : ℍ => d) := by
  refine ⟨‖d‖ + 1, 0, by positivity, le_rfl, fun w hw => ?_⟩
  have h1 : (0:ℝ) ≤ ‖d‖ := norm_nonneg d
  have h3 : Real.exp (0 * (ModularGroup.S • w).im) = 1 := by rw [zero_mul, Real.exp_zero]
  rw [Real.rpow_zero, mul_one, h3, mul_one]
  linarith

end Bdd

end Work.Asymptotics.EtailE

end
