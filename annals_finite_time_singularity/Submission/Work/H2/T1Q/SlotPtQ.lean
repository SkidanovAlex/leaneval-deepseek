
/-
# `Work.H2.T1Q.SlotPtQ` — the pointwise comparisons for the interior `T1Easy` estimate

For the target `Work.H2.T1Q.EasyBoundQ` every Leibniz summand of the "easy part" is estimated
by Cauchy–Schwarz, with **one** of its three factors bounded by `Kf`, `Kg`, or by an `L^∞`-bound
`S` on the slice of `D_z³f`, and the remaining two factors being genuine `ℋ⁴`-blocks.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.H2.T1EasyBound
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.H2.WPQ.Dth_DzIter_comm_smoothQuad
import Submission.Work.H2.T1Q.SliceSupOpen
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.H2.WPQ.Dth_DzIter_comm_smoothQuad
import Submission.Work.H2.T1Q.SliceSupOpen
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2.T1Q

set_option autoImplicit false
set_option maxHeartbeats 800000

open Work.FTS.H2

/-- **The `D_z`-slot summand with a low-order `f`-factor.** -/
theorem xD_Kf_pt (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (Kf : ℝ) (hKf0 : 0 ≤ Kf)
    (hKf : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ| ≤ Kf)
    (i b : ℕ) (hi : i ≤ 4) (hbi : b ≤ i) (hib : i - b ≤ 3) (hb2 : b ≤ 2) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |xD f g i b z θ| ≤ (i.choose b : ℝ) * Kf *
        ((|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := by
  intro z θ hz hθ0 hθ1
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hF : |Work.Spaces.DzIter b f z θ| ≤ Kf := by
    have h := hKf b 0 (by omega) z θ hz hθ0 hθ1
    rwa [Work.Spaces.mixed_zero_right] at h
  have hWmnn : 0 ≤ Wm α z θ := Wm_nonneg α hθI
  have hWhznn : 0 ≤ Whz z θ := Whz_nonneg hθI
  have hch : 0 ≤ (i.choose b : ℝ) := by positivity
  have hkey : Whz z θ ^ 2 ≤ Wm α z θ * Whz z θ := Whz_sq_le_Wm_mul α hα hθI
  have hG1 : 0 ≤ |Work.Spaces.mixed (i - b) 1 g z θ| := abs_nonneg _
  have hG2 : 0 ≤ |Work.Spaces.DzIter i g z θ| := abs_nonneg _
  have hfacnn : 0 ≤ (|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
      * (|Work.Spaces.DzIter i g z θ| * Whz z θ) :=
    mul_nonneg (mul_nonneg hG1 hWmnn) (mul_nonneg hG2 hWhznn)
  have hstep : |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
      * |Work.Spaces.DzIter i g z θ| * Whz z θ ^ 2
      ≤ Kf * ((|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
        * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := by
    have h1 : |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
        * |Work.Spaces.DzIter i g z θ| * Whz z θ ^ 2
        ≤ |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
          * |Work.Spaces.DzIter i g z θ| * (Wm α z θ * Whz z θ) :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    have h2 : |Work.Spaces.DzIter b f z θ|
          * (|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ)
        = |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
          * |Work.Spaces.DzIter i g z θ| * (Wm α z θ * Whz z θ) := by ring
    have h3 : |Work.Spaces.DzIter b f z θ|
          * (|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ)
        ≤ Kf * ((|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hF hfacnn
    calc |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
          * |Work.Spaces.DzIter i g z θ| * Whz z θ ^ 2
        ≤ |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
          * |Work.Spaces.DzIter i g z θ| * (Wm α z θ * Whz z θ) := h1
      _ = |Work.Spaces.DzIter b f z θ|
          * (|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ) := h2.symm
      _ ≤ Kf * ((|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := h3
  calc |xD f g i b z θ|
      = (i.choose b : ℝ) * (|Work.Spaces.DzIter b f z θ|
          * |Work.Spaces.mixed (i - b) 1 g z θ| * |Work.Spaces.DzIter i g z θ|
          * Whz z θ ^ 2) := by
        simp only [xD, abs_mul, abs_of_nonneg hch, abs_of_nonneg (sq_nonneg (Whz z θ))] <;> ring
    _ ≤ (i.choose b : ℝ) * (Kf * ((|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ))) :=
        mul_le_mul_of_nonneg_left hstep hch
    _ = (i.choose b : ℝ) * Kf *
        ((|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := by ring

/-- **The `D_z`-slot summand with a low-order `g`-factor.** -/
theorem xD_Kg_pt (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (Kg : ℝ) (hKg0 : 0 ≤ Kg)
    (hKg : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a g z θ| ≤ Kg)
    (i b : ℕ) (hi : i ≤ 4) (hbi : b ≤ i) (hb3 : 3 ≤ b) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |xD f g i b z θ| ≤ (i.choose b : ℝ) * Kg *
        ((|Work.Spaces.DzIter b f z θ| * Whz z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := by
  intro z θ hz hθ0 hθ1
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hG : |Work.Spaces.mixed (i - b) 1 g z θ| ≤ Kg :=
    hKg (i - b) 1 (by omega) z θ hz hθ0 hθ1
  have hWhznn : 0 ≤ Whz z θ := Whz_nonneg hθI
  have hch : 0 ≤ (i.choose b : ℝ) := by positivity
  have hG1 : 0 ≤ |Work.Spaces.DzIter b f z θ| := abs_nonneg _
  have hG2 : 0 ≤ |Work.Spaces.DzIter i g z θ| := abs_nonneg _
  have hfacnn : 0 ≤ (|Work.Spaces.DzIter b f z θ| * Whz z θ)
      * (|Work.Spaces.DzIter i g z θ| * Whz z θ) :=
    mul_nonneg (mul_nonneg hG1 hWhznn) (mul_nonneg hG2 hWhznn)
  have hstep : |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
      * |Work.Spaces.DzIter i g z θ| * Whz z θ ^ 2
      ≤ Kg * ((|Work.Spaces.DzIter b f z θ| * Whz z θ)
        * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := by
    have h1 : |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
        * |Work.Spaces.DzIter i g z θ| * Whz z θ ^ 2
        ≤ |Work.Spaces.DzIter b f z θ| * Kg
          * |Work.Spaces.DzIter i g z θ| * (Whz z θ * Whz z θ) := by
      have hmul : |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
          * |Work.Spaces.DzIter i g z θ|
          ≤ |Work.Spaces.DzIter b f z θ| * Kg * |Work.Spaces.DzIter i g z θ| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG hG1) hG2
      calc |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
            * |Work.Spaces.DzIter i g z θ| * Whz z θ ^ 2
          = (|Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
            * |Work.Spaces.DzIter i g z θ|) * (Whz z θ * Whz z θ) := by ring
        _ ≤ (|Work.Spaces.DzIter b f z θ| * Kg * |Work.Spaces.DzIter i g z θ|)
            * (Whz z θ * Whz z θ) :=
            mul_le_mul_of_nonneg_right hmul (mul_nonneg hWhznn hWhznn)
        _ = |Work.Spaces.DzIter b f z θ| * Kg
            * |Work.Spaces.DzIter i g z θ| * (Whz z θ * Whz z θ) := by ring
    have h2 : |Work.Spaces.DzIter b f z θ| * Kg * |Work.Spaces.DzIter i g z θ|
          * (Whz z θ * Whz z θ)
        = Kg * ((|Work.Spaces.DzIter b f z θ| * Whz z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := by ring
    rw [h2] at h1
    exact h1
  calc |xD f g i b z θ|
      = (i.choose b : ℝ) * (|Work.Spaces.DzIter b f z θ|
          * |Work.Spaces.mixed (i - b) 1 g z θ| * |Work.Spaces.DzIter i g z θ|
          * Whz z θ ^ 2) := by
        simp only [xD, abs_mul, abs_of_nonneg hch, abs_of_nonneg (sq_nonneg (Whz z θ))] <;> ring
    _ ≤ (i.choose b : ℝ) * (Kg * ((|Work.Spaces.DzIter b f z θ| * Whz z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ))) :=
        mul_le_mul_of_nonneg_left hstep hch
    _ = (i.choose b : ℝ) * Kg *
        ((|Work.Spaces.DzIter b f z θ| * Whz z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := by ring

/-- **The mixed summand with a low-order `f`-factor.** -/
theorem yM_Kf_pt (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf : ℝ) (hKf0 : 0 ≤ Kf)
    (hKf : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ| ≤ Kf)
    (i j a b : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) (hai : a ≤ i) (hbj : b ≤ j)
    (hab : a + b ≤ 2) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |yM α f g i j a b z θ| ≤ (i.choose a : ℝ) * (j.choose b : ℝ) * Kf *
        ((|Work.Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
          * (|Work.Spaces.mixed j i g z θ| * Wm α z θ)) := by
  intro z θ hz hθ0 hθ1
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hF : |Work.Spaces.mixed b a f z θ| ≤ Kf := hKf b a hab z θ hz hθ0 hθ1
  have hWmnn : 0 ≤ Wm α z θ := Wm_nonneg α hθI
  have hch : 0 ≤ (i.choose a : ℝ) * (j.choose b : ℝ) := by positivity
  have hG1 : 0 ≤ |Work.Spaces.mixed (j - b) (i - a + 1) g z θ| := abs_nonneg _
  have hG2 : 0 ≤ |Work.Spaces.mixed j i g z θ| := abs_nonneg _
  have hfacnn : 0 ≤ (|Work.Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
      * (|Work.Spaces.mixed j i g z θ| * Wm α z θ) :=
    mul_nonneg (mul_nonneg hG1 hWmnn) (mul_nonneg hG2 hWmnn)
  have hstep : |Work.Spaces.mixed b a f z θ| * |Work.Spaces.mixed (j - b) (i - a + 1) g z θ|
      * |Work.Spaces.mixed j i g z θ| * Wm α z θ ^ 2
      ≤ Kf * ((|Work.Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
        * (|Work.Spaces.mixed j i g z θ| * Wm α z θ)) := by
    have h1 : |Work.Spaces.mixed b a f z θ| * |Work.Spaces.mixed (j - b) (i - a + 1) g z θ|
        * |Work.Spaces.mixed j i g z θ| * Wm α z θ ^ 2
        = |Work.Spaces.mixed b a f z θ| * (|Work.Spaces.mixed (j - b) (i - a + 1) g z θ|
          * Wm α z θ) * (|Work.Spaces.mixed j i g z θ| * Wm α z θ) := by ring
    rw [h1, mul_assoc]
    exact mul_le_mul_of_nonneg_right hF hfacnn
  calc |yM α f g i j a b z θ|
      = ((i.choose a : ℝ) * (j.choose b : ℝ)) * (|Work.Spaces.mixed b a f z θ|
          * |Work.Spaces.mixed (j - b) (i - a + 1) g z θ|
          * |Work.Spaces.mixed j i g z θ| * Wm α z θ ^ 2) := by
        simp only [yM, abs_mul, abs_of_nonneg hch, abs_of_nonneg (sq_nonneg (Wm α z θ))] <;> ring
    _ ≤ ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Kf * ((|Work.Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
            * (|Work.Spaces.mixed j i g z θ| * Wm α z θ))) :=
        mul_le_mul_of_nonneg_left hstep hch
    _ = (i.choose a : ℝ) * (j.choose b : ℝ) * Kf *
        ((|Work.Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
          * (|Work.Spaces.mixed j i g z θ| * Wm α z θ)) := by ring

/-- **The mixed summand with a low-order `g`-factor and a mixed `f`-factor.** -/
theorem yM_Kg_mixed_pt (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kg : ℝ) (hKg0 : 0 ≤ Kg)
    (hKg : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a g z θ| ≤ Kg)
    (i j a b : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) (hai : a ≤ i) (hbj : b ≤ j)
    (ha1 : 1 ≤ a) (hab : 3 ≤ a + b) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |yM α f g i j a b z θ| ≤ (i.choose a : ℝ) * (j.choose b : ℝ) * Kg *
        ((|Work.Spaces.mixed b a f z θ| * Wm α z θ)
          * (|Work.Spaces.mixed j i g z θ| * Wm α z θ)) := by
  intro z θ hz hθ0 hθ1
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hG : |Work.Spaces.mixed (j - b) (i - a + 1) g z θ| ≤ Kg :=
    hKg (j - b) (i - a + 1) (by omega) z θ hz hθ0 hθ1
  have hWmnn : 0 ≤ Wm α z θ := Wm_nonneg α hθI
  have hch : 0 ≤ (i.choose a : ℝ) * (j.choose b : ℝ) := by positivity
  have hG1 : 0 ≤ |Work.Spaces.mixed b a f z θ| := abs_nonneg _
  have hG2 : 0 ≤ |Work.Spaces.mixed j i g z θ| := abs_nonneg _
  have hfacnn : 0 ≤ (|Work.Spaces.mixed b a f z θ| * Wm α z θ)
      * (|Work.Spaces.mixed j i g z θ| * Wm α z θ) :=
    mul_nonneg (mul_nonneg hG1 hWmnn) (mul_nonneg hG2 hWmnn)
  have hstep : |Work.Spaces.mixed b a f z θ| * |Work.Spaces.mixed (j - b) (i - a + 1) g z θ|
      * |Work.Spaces.mixed j i g z θ| * Wm α z θ ^ 2
      ≤ Kg * ((|Work.Spaces.mixed b a f z θ| * Wm α z θ)
        * (|Work.Spaces.mixed j i g z θ| * Wm α z θ)) := by
    have hmul : |Work.Spaces.mixed b a f z θ| * |Work.Spaces.mixed (j - b) (i - a + 1) g z θ|
        * |Work.Spaces.mixed j i g z θ| ≤ |Work.Spaces.mixed b a f z θ| * Kg
        * |Work.Spaces.mixed j i g z θ| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG hG1) hG2
    have h1 : |Work.Spaces.mixed b a f z θ| * |Work.Spaces.mixed (j - b) (i - a + 1) g z θ|
        * |Work.Spaces.mixed j i g z θ| * Wm α z θ ^ 2
        ≤ |Work.Spaces.mixed b a f z θ| * Kg * |Work.Spaces.mixed j i g z θ|
          * (Wm α z θ * Wm α z θ) := by
      calc |Work.Spaces.mixed b a f z θ| * |Work.Spaces.mixed (j - b) (i - a + 1) g z θ|
            * |Work.Spaces.mixed j i g z θ| * Wm α z θ ^ 2
          = (|Work.Spaces.mixed b a f z θ| * |Work.Spaces.mixed (j - b) (i - a + 1) g z θ|
            * |Work.Spaces.mixed j i g z θ|) * (Wm α z θ * Wm α z θ) := by ring
        _ ≤ (|Work.Spaces.mixed b a f z θ| * Kg * |Work.Spaces.mixed j i g z θ|)
            * (Wm α z θ * Wm α z θ) :=
            mul_le_mul_of_nonneg_right hmul (mul_nonneg hWmnn hWmnn)
        _ = |Work.Spaces.mixed b a f z θ| * Kg * |Work.Spaces.mixed j i g z θ|
            * (Wm α z θ * Wm α z θ) := by ring
    have h2 : |Work.Spaces.mixed b a f z θ| * Kg * |Work.Spaces.mixed j i g z θ|
          * (Wm α z θ * Wm α z θ)
        = Kg * ((|Work.Spaces.mixed b a f z θ| * Wm α z θ)
          * (|Work.Spaces.mixed j i g z θ| * Wm α z θ)) := by ring
    rw [h2] at h1
    exact h1
  calc |yM α f g i j a b z θ|
      = ((i.choose a : ℝ) * (j.choose b : ℝ)) * (|Work.Spaces.mixed b a f z θ|
          * |Work.Spaces.mixed (j - b) (i - a + 1) g z θ|
          * |Work.Spaces.mixed j i g z θ| * Wm α z θ ^ 2) := by
        simp only [yM, abs_mul, abs_of_nonneg hch, abs_of_nonneg (sq_nonneg (Wm α z θ))] <;> ring
    _ ≤ ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Kg * ((|Work.Spaces.mixed b a f z θ| * Wm α z θ)
            * (|Work.Spaces.mixed j i g z θ| * Wm α z θ))) :=
        mul_le_mul_of_nonneg_left hstep hch
    _ = (i.choose a : ℝ) * (j.choose b : ℝ) * Kg *
        ((|Work.Spaces.mixed b a f z θ| * Wm α z θ)
          * (|Work.Spaces.mixed j i g z θ| * Wm α z θ)) := by ring

/-- **The exceptional mixed summand** (`a = 0`, `b ≥ 3`; for the target only
`(i,j,a,b) = (1,3,0,3)` occurs). -/
theorem yM_pure_pt (α : ℝ) (f g : ℝ → ℝ → ℝ) (S : ℝ) (hS0 : 0 ≤ S)
    (i j b : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) (hbj : b ≤ j)
    (z : ℝ) (hz : 0 < z)
    (hS : ∀ θ : ℝ, 0 < θ → θ < π / 2 → |Work.Spaces.DzIter b f z θ| ≤ S) :
    ∀ θ : ℝ, 0 < θ → θ < π / 2 →
      |yM α f g i j 0 b z θ| ≤ (j.choose b : ℝ) * S *
        ((|Work.Spaces.mixed (j - b) (i + 1) g z θ| * Wm α z θ)
          * (|Work.Spaces.mixed j i g z θ| * Wm α z θ)) := by
  intro θ hθ0 hθ1
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hF : |Work.Spaces.DzIter b f z θ| ≤ S := hS θ hθ0 hθ1
  have hWmnn : 0 ≤ Wm α z θ := Wm_nonneg α hθI
  have hch : 0 ≤ (j.choose b : ℝ) := by positivity
  have hG1 : 0 ≤ |Work.Spaces.mixed (j - b) (i + 1) g z θ| := abs_nonneg _
  have hG2 : 0 ≤ |Work.Spaces.mixed j i g z θ| := abs_nonneg _
  have hfacnn : 0 ≤ (|Work.Spaces.mixed (j - b) (i + 1) g z θ| * Wm α z θ)
      * (|Work.Spaces.mixed j i g z θ| * Wm α z θ) :=
    mul_nonneg (mul_nonneg hG1 hWmnn) (mul_nonneg hG2 hWmnn)
  have hcoe : yM α f g i j 0 b z θ
      = (j.choose b : ℝ) * (Work.Spaces.DzIter b f z θ
          * Work.Spaces.mixed (j - b) (i + 1) g z θ
          * Work.Spaces.mixed j i g z θ * (Wm α z θ) ^ 2) := by
    rw [yM, Work.Spaces.mixed_zero_right]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  have hstep : |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (j - b) (i + 1) g z θ|
      * |Work.Spaces.mixed j i g z θ| * Wm α z θ ^ 2
      ≤ S * ((|Work.Spaces.mixed (j - b) (i + 1) g z θ| * Wm α z θ)
        * (|Work.Spaces.mixed j i g z θ| * Wm α z θ)) := by
    have h1 : |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (j - b) (i + 1) g z θ|
        * |Work.Spaces.mixed j i g z θ| * Wm α z θ ^ 2
        = |Work.Spaces.DzIter b f z θ| * (|Work.Spaces.mixed (j - b) (i + 1) g z θ|
          * Wm α z θ) * (|Work.Spaces.mixed j i g z θ| * Wm α z θ) := by ring
    rw [h1, mul_assoc]
    exact mul_le_mul_of_nonneg_right hF hfacnn
  calc |yM α f g i j 0 b z θ|
      = (j.choose b : ℝ) * (|Work.Spaces.DzIter b f z θ|
          * |Work.Spaces.mixed (j - b) (i + 1) g z θ|
          * |Work.Spaces.mixed j i g z θ| * Wm α z θ ^ 2) := by
        simp only [hcoe, abs_mul, abs_of_nonneg hch, abs_of_nonneg (sq_nonneg (Wm α z θ))] <;> ring
    _ ≤ (j.choose b : ℝ) * (S * ((|Work.Spaces.mixed (j - b) (i + 1) g z θ| * Wm α z θ)
          * (|Work.Spaces.mixed j i g z θ| * Wm α z θ))) :=
        mul_le_mul_of_nonneg_left hstep hch
    _ = (j.choose b : ℝ) * S *
        ((|Work.Spaces.mixed (j - b) (i + 1) g z θ| * Wm α z θ)
          * (|Work.Spaces.mixed j i g z θ| * Wm α z θ)) := by ring

/-! ## Boundedness of the `θ`-slice of `D_z³f` -/

/-- Almost every `θ ∈ Iθ` lies in the open interval `(0, π/2)`. -/
theorem ae_Iθ_mem_Ioo' : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
  have h : ∀ᵐ θ ∂(volume.restrict (Set.Icc (0 : ℝ) (π / 2))), θ ∈ Set.Ioo 0 (π / 2) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (Set.Finite.measure_zero
      (by simp : ({0, π / 2} : Set ℝ).Finite) volume)
    intro θ hθ
    simp only [Set.mem_setOf_eq, not_imp, Set.mem_Icc] at hθ
    obtain ⟨hθI, hnot⟩ := hθ
    simp only [Set.mem_Ioo, Set.mem_insert_iff, Set.mem_singleton_iff] at hnot ⊢
    by_cases h0 : 0 < θ
    · right
      by_contra h2
      exact hnot ⟨h0, lt_of_le_of_ne hθI.2 h2⟩
    · left
      exact le_antisymm (not_lt.mp h0) hθI.1
  exact h

theorem sup_DzIter_three_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ z ∈ Work.Spaces.Iz,
      ∃ S : ℝ, 0 ≤ S ∧ ∀ θ : ℝ, 0 < θ → θ < π / 2 → |Work.Spaces.DzIter 3 f z θ| ≤ S := by
  intro z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hzpos
  · subst h0
    refine ⟨0, le_refl 0, fun θ _ _ => ?_⟩
    have hzero : Work.Spaces.DzIter 3 f 0 θ = 0 := by
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
      ring
    rw [hzero, abs_zero]
  · have hz1 : (-1 : ℝ) < z := by linarith
    have hw1 : (1 : ℝ) ≤ Work.Spaces.w z := Work.H2.T1Q.one_le_w_of_pos hzpos
    have hsinpos : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2), 0 < Real.sin (2 * θ) := fun θ hθ =>
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hdiff : ContDiffOn ℝ 1 (fun θ : ℝ => Work.Spaces.DzIter 3 f z θ) (Set.Ioo 0 (π / 2)) :=
      ((hf.DzIter 3).curry_θ (Set.mem_Ioi.mpr hz1)).of_le (by simp [Work.Stability.smoothOrder])
    -- ## the two pointwise bounds
    have hbd1 : ∀ θ ∈ Set.Ioo 0 (π / 2),
        (Work.Spaces.DzIter 3 f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
      intro θ hθ
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hs0 : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθI
      have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hkey := Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ 3 (by norm_num)
      have hsp1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
        Real.rpow_le_one hs0 hs1 (by norm_num [Work.Spaces.eta])
      have hq1 : (1 : ℝ) ≤ Work.Spaces.w z
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
        rw [le_div_iff₀ (Real.rpow_pos_of_pos (hsinpos θ hθ) _)]
        linarith
      have hq2 : (1 : ℝ) ≤ (Work.Spaces.w z
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by nlinarith [hq1]
      have hstep : (Work.Spaces.DzIter 3 f z θ) ^ 2
          ≤ (Work.Spaces.DzIter 3 f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [mul_pow]
        nlinarith [hq2, sq_nonneg (Work.Spaces.DzIter 3 f z θ)]
      linarith [hkey, hstep]
    have hbd2slot : ∀ θ ∈ Set.Ioo 0 (π / 2),
        (Work.Spaces.mixed 3 1 f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
      intro θ hθ
      have hkey := Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ 1 3 (by norm_num) (by norm_num)
      rw [mul_pow, Work.FTS.H2.HQ.Wt_sq_quad α z θ hθ] at hkey
      have hw2 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by nlinarith [hw1]
      have hle : (Work.Spaces.mixed 3 1 f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          ≤ (Work.Spaces.mixed 3 1 f z θ) ^ 2
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        nlinarith [hw2, Real.rpow_nonneg (le_of_lt (hsinpos θ hθ)) (-(Work.Spaces.gam α))]
      linarith [hkey, hle]
    have hbd2 : ∀ θ ∈ Work.Spaces.Iθ,
        (deriv (fun θ' : ℝ => Work.Spaces.DzIter 3 f z θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
      intro θ hθI
      by_cases hθ : θ ∈ Set.Ioo 0 (π / 2)
      · have hs0 := hsinpos θ hθ
        have hcomm : Work.Spaces.Dth (Work.Spaces.DzIter 3 f) z θ
            = Work.Spaces.mixed 3 1 f z θ :=
          Work.H2.WPQ.Dth_DzIter_comm_smoothQuad hf 3 hz hθ
        have hmix : Work.Spaces.mixed 3 1 f z θ
            = Real.sin (2 * θ) * deriv (fun θ' : ℝ => Work.Spaces.DzIter 3 f z θ') θ := by
          rw [← hcomm]
          rfl
        have hsplit : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            = (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
          rw [show (2 : ℝ) - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring,
            Real.rpow_add hs0, Real.rpow_two]
        have hmain : (deriv (fun θ' : ℝ => Work.Spaces.DzIter 3 f z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            = (Work.Spaces.mixed 3 1 f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
          have hdiv : deriv (fun θ' : ℝ => Work.Spaces.DzIter 3 f z θ') θ
              = Work.Spaces.mixed 3 1 f z θ / Real.sin (2 * θ) := by
            rw [hmix]
            field_simp
          rw [hdiv, div_pow, hsplit]
          field_simp
        rw [hmain]
        exact hbd2slot θ hθ
      · have hsin0 : Real.sin (2 * θ) = 0 := by
          rcases le_or_gt θ 0 with h | h
          · rw [le_antisymm h hθI.1, mul_zero, Real.sin_zero]
          · have h2 : π / 2 ≤ θ := not_lt.mp (fun h3 => hθ ⟨h, h3⟩)
            rw [show (2:ℝ) * θ = π by linarith [h2, hθI.2], Real.sin_pi]
        have hzero : (0 : ℝ) ^ (2 - Work.Spaces.gam α) = 0 := by
          refine Real.zero_rpow ?_
          have hg : Work.Spaces.gam α < 2 := by
            simp only [Work.Spaces.gam]; linarith
          linarith
        rw [hsin0, hzero, mul_zero]
        exact Work.Spaces.HkIntegrand_nonneg α 4 f z θ
    -- ## integrability of the two integrals
    have haesm1 : AEStronglyMeasurable (fun θ => (Work.Spaces.DzIter 3 f z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := by
      refine Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Work.Spaces.DzIter 3 f p.1 p.2) ^ 2) ?_ hzpos
      exact (((Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hf 3).continuousOn.mono
        Work.FTS.H2.HQ.quadQ_subset_quadU)).pow 2
    have hint1 : MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.DzIter 3 f z θ) ^ 2) Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.mono' (hmem.1 z hz) haesm1 ?_
      filter_upwards [ae_Iθ_mem_Ioo'] with θ hθ
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hbd1 θ hθ
    have haesm2 : AEStronglyMeasurable
        (fun θ => (Work.Spaces.pth (Work.Spaces.DzIter 3 f) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) (volume.restrict Work.Spaces.Iθ) := by
      refine Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.DzIter 3 f) p.1 p.2) ^ 2
          * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)) ?_ hzpos
      have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.DzIter 3 f) p.1 p.2)
          Work.FTS.H2.HQ.quadQ :=
        ((Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU
          (Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hf 3)).continuousOn.mono
            Work.FTS.H2.HQ.quadQ_subset_quadU)
      have h2 : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α))
          Work.FTS.H2.HQ.quadQ :=
        ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
          (fun p hp => Or.inl (ne_of_gt (hsinpos p.2 hp.2)))
      exact (h1.pow 2).mul h2
    have hint2 : MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun θ' : ℝ => Work.Spaces.DzIter 3 f z θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.mono' (hmem.1 z hz)
        (by simpa only [Work.Spaces.pth] using haesm2) ?_
      filter_upwards [ae_Iθ_mem_Ioo'] with θ hθ
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (le_of_lt (hsinpos θ hθ)) _))]
      exact hbd2 θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    -- ## the slicewise supremum bound
    have hkey := Work.H2.T1Q.SliceSupOpen α (fun θ : ℝ => Work.Spaces.DzIter 3 f z θ) hα hα1
      hdiff hint1 hint2
    refine ⟨Real.sqrt ((4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 3 f z θ) ^ 2)
      + (200 / (Work.Spaces.gam α - 1)) * ∫ θ in Work.Spaces.Iθ,
          (deriv (fun θ' : ℝ => Work.Spaces.DzIter 3 f z θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)),
      Real.sqrt_nonneg _, fun θ hθ0 hθ1 => ?_⟩
    have h2 := hkey θ ⟨hθ0, hθ1⟩
    calc |Work.Spaces.DzIter 3 f z θ| = Real.sqrt ((Work.Spaces.DzIter 3 f z θ) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 3 f z θ) ^ 2)
            + (200 / (Work.Spaces.gam α - 1)) * ∫ θ in Work.Spaces.Iθ,
              (deriv (fun θ' : ℝ => Work.Spaces.DzIter 3 f z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := Real.sqrt_le_sqrt h2


end Work.H2.T1Q
