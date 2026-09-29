import Mathlib
import Submission.Work.TMContract.Components

/-!
# C8 (Kotani theory): local vocabulary

This file introduces the small vocabulary needed for the proof of `Work.TMContract.P_Kotani`
(AJ Theorem 2.2) and records the definitional bridges to the frozen definitions of
`Work.TMContract.Defs`.

The objects are:

* `pot lam y = 2 λ cos 2πy`, the potential at phase `y`;
* `step lam E y z = E - pot lam y - 1/z`, the Möbius action of the transfer matrix
  `tmC lam E y` (AJ's `S_{λ,E}(y) · z`);
* `delta z w = ‖z - w‖²/(im z · im w)`, the "hyperbolic square distance"
  (`delta = 2(cosh d_ℍ - 1)`); all contraction estimates are stated for `delta`;
* `approxIt α lam E n x z`: the `n`-fold composition `F_{x-α} ∘ F_{x-2α} ∘ ⋯ ∘ F_{x-nα}`
  applied to `z`, where `F_y = step lam E y`, i.e. the `n`-th approximant of the (left)
  `m`-function;
* `approx α lam E n x = approxIt α lam E n x I`, the approximant started at `i`;
* `mfun α lam E x`: the pointwise limit of `approx` (a total function; it agrees with
  `amoM` on `{Im E > 0}` where the limit is proved to exist).

Everything is stated for `lam : ℝ` and `E : ℂ`; the hypotheses `0 < E.im` appear in the
lemmas, not in the definitions (which are total, as in `Defs.lean`).
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Kotani

open Work.TMContract

/-! ## The potential and the Möbius step -/

/-- The potential `2 λ cos 2πy` (the real-valued potential at phase `y`). -/
def pot (lam : ℝ) (y : ℝ) : ℝ := 2 * lam * Real.cos (2 * Real.pi * y)

theorem pot_periodic (lam y : ℝ) : pot lam (y + 1) = pot lam y := by
  simp only [pot]
  rw [show 2 * Real.pi * (y + 1) = 2 * Real.pi * y + 2 * Real.pi by ring,
    Real.cos_add_two_pi]

theorem pot_even (lam y : ℝ) : pot lam (-y) = pot lam y := by
  simp only [pot]
  rw [show 2 * Real.pi * -y = -(2 * Real.pi * y) by ring, Real.cos_neg]

theorem pot_abs_le (lam y : ℝ) : |pot lam y| ≤ 2 * |lam| := by
  have h : |Real.cos (2 * Real.pi * y)| ≤ 1 := Real.abs_cos_le_one _
  calc |pot lam y| = 2 * |lam| * |Real.cos (2 * Real.pi * y)| := by
        simp only [pot, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    _ ≤ 2 * |lam| * 1 := mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * |lam| := by ring

/-- The Möbius step `z ↦ E - pot lam y - 1/z`, i.e. AJ's `S_{λ,E}(y) · z`. -/
def step (lam : ℝ) (E : ℂ) (y : ℝ) (z : ℂ) : ℂ :=
  E - ((pot lam y : ℝ) : ℂ) - 1 / z

/-- `step` agrees with the Möbius action `mob` of the transfer matrix `tmC`. -/
theorem step_eq_mob (lam : ℝ) (E : ℂ) (y : ℝ) (z : ℂ) (hz : z ≠ 0) :
    step lam E y z = mob (tmC lam E y) z := by
  have h1 : ((pot lam y : ℝ) : ℂ)
      = ((2 * lam * Real.cos (2 * Real.pi * y) : ℝ) : ℂ) := rfl
  rw [step, h1, mob, tmC]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
    Matrix.cons_val', Matrix.empty_val']
  have hden : (1 : ℂ) * z + 0 ≠ 0 := by simpa using hz
  rw [eq_div_iff hden]
  simp only [one_mul, add_zero]
  rw [sub_mul, sub_mul, div_mul_cancel₀ _ hz]
  ring

/-! ## The hyperbolic square distance -/

/-- `delta z w = ‖z - w‖²/(im z · im w) = 2(cosh d_ℍ - 1)`. -/
def delta (z w : ℂ) : ℝ := ‖z - w‖ ^ 2 / (z.im * w.im)

theorem delta_nonneg {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) : 0 ≤ delta z w := by
  unfold delta
  positivity

theorem delta_comm (z w : ℂ) : delta z w = delta w z := by
  unfold delta
  rw [show w - z = -(z - w) by ring, norm_neg, mul_comm]

/-- `delta` is invariant under real translations. -/
theorem delta_add_re (z w : ℂ) (c : ℝ) : delta (z + c) (w + c) = delta z w := by
  unfold delta
  rw [show z + (c:ℂ) - (w + (c:ℂ)) = z - w by ring]
  simp only [Complex.add_im, Complex.ofReal_im, add_zero]

/-! ## The approximants -/

/-- The `n`-fold composition `F_{x-α} ∘ F_{x-2α} ∘ ⋯ ∘ F_{x-nα}` applied to `z`,
where `F_y = step lam E y`. -/
def approxIt (α lam : ℝ) (E : ℂ) : ℕ → ℝ → ℂ → ℂ
  | 0, _, z => z
  | n + 1, x, z => step lam E (x - α) (approxIt α lam E n (x - α) z)

@[simp] theorem approxIt_zero (α lam : ℝ) (E : ℂ) (x : ℝ) (z : ℂ) :
    approxIt α lam E 0 x z = z := rfl

@[simp] theorem approxIt_succ (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) (z : ℂ) :
    approxIt α lam E (n + 1) x z = step lam E (x - α) (approxIt α lam E n (x - α) z) := rfl

/-- The `n`-th approximant of the `m`-function (started at `i`). -/
def approx (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) : ℂ := approxIt α lam E n x Complex.I

@[simp] theorem approx_zero (α lam : ℝ) (E : ℂ) (x : ℝ) : approx α lam E 0 x = Complex.I := rfl

@[simp] theorem approx_succ (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    approx α lam E (n + 1) x
      = step lam E (x - α) (approx α lam E n (x - α)) := rfl

/-- The pointwise limit of the approximants (a total function; it is the `m`-function
wherever the limit is proved to exist, in particular on `{Im E > 0}`). -/
def mfun (α lam : ℝ) (E : ℂ) (x : ℝ) : ℂ :=
  limUnder atTop fun n : ℕ => approx α lam E n x

end Work.TMComp.Kotani
