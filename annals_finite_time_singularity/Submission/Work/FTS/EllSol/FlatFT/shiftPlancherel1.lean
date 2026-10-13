import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.FTS.EllSol.FlatFT.plancherelSlice1
import Submission.Work.FTS.EllSol.FlatFT.plancherelSlice1Deriv
import Submission.Work.FTS.EllSol.FlatFT.integrable_weighted_slice1
import Submission.Work.FTS.EllSol.FlatFT.integrable_normSq_slice1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

open MeasureTheory
open scoped Real

namespace Work.FTS.EllSol.FlatFT

/-- The squared modulus of the *shifted* Fourier multiplier `2πIξ - b`: the two summands `-b`
and `2πξ·I` of `2πIξ - b` are orthogonal, so there is no cross term,
`‖(2πIξ - b)F‖² = ((2πξ)² + b²)·‖F‖²`. -/
private theorem norm_sq_mul_shift (F : ℂ) (b ξ : ℝ) :
    ‖(2 * Real.pi * Complex.I * ξ - (b : ℂ)) * F‖ ^ 2
      = ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖F‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  congr 1
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : (2 * Real.pi * Complex.I * ξ - (b : ℂ)).re = -b := by simp
  have him : (2 * Real.pi * Complex.I * ξ - (b : ℂ)).im = 2 * Real.pi * ξ := by simp
  rw [hre, him]
  ring

/-- Linearity of the `t`-Fourier slice `slice1` in its argument, for a difference of a constant
multiple: `slice1 (f - c·g) ξ = slice1 f ξ - c·slice1 g ξ`.  All the integrals involved are
absolutely convergent because `f` and `g` are continuous with compact support while the
exponential factor has modulus one. -/
private theorem slice1_sub_const_mul' (f g : ℝ → ℂ) (c : ℂ) (hf : Continuous f)
    (hfs : HasCompactSupport f) (hg : Continuous g) (hgs : HasCompactSupport g) (ξ : ℝ) :
    slice1 (fun t => f t - c * g t) ξ = slice1 f ξ - c * slice1 g ξ := by
  set κ : ℝ → ℂ := fun t => Complex.exp (-(2 * Real.pi * Complex.I * ξ * t)) with hκ
  have hκc : Continuous κ := by rw [hκ]; fun_prop
  have hfs' : HasCompactSupport (fun t => f t * κ t) :=
    hfs.mono (fun t ht => by
      intro h0
      exact ht (by simp [h0]))
  have hgs' : HasCompactSupport (fun t => g t * κ t) :=
    hgs.mono (fun t ht => by
      intro h0
      exact ht (by simp [h0]))
  have h1 : Integrable (fun t => f t * κ t) :=
    (hf.mul hκc).integrable_of_hasCompactSupport hfs'
  have h2 : Integrable (fun t => g t * κ t) :=
    (hg.mul hκc).integrable_of_hasCompactSupport hgs'
  have h3 : Integrable (fun t => c * (g t * κ t)) := h2.const_mul c
  calc slice1 (fun t => f t - c * g t) ξ
      = ∫ t, (f t - c * g t) * κ t := rfl
    _ = ∫ t, (f t * κ t - c * (g t * κ t)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        ring
    _ = (∫ t, f t * κ t) - ∫ t, c * (g t * κ t) := integral_sub h1 h3
    _ = (∫ t, f t * κ t) - c * ∫ t, g t * κ t := by rw [integral_const_mul]
    _ = slice1 f ξ - c * slice1 g ξ := rfl

/-- Shifted first-order Plancherel for the `t`-Fourier slice.  All helper lemmas in the file
should be `private` (the file's public interface is this one theorem). -/
theorem shiftPlancherel1 {h : ℝ → ℂ} (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) (b : ℝ) :
    MeasureTheory.Integrable
      (fun ξ : ℝ => ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice1 h ξ‖ ^ 2) ∧
    (∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice1 h ξ‖ ^ 2
      = ∫ t : ℝ, ‖deriv h t - b * h t‖ ^ 2) := by
  -- The shifted profile `g = h' - b·h` is continuous with compact support, and its Fourier
  -- slice is `(2πIξ - b)·slice1 h ξ`, whose squared modulus is `((2πξ)² + b²)‖slice1 h ξ‖²`.
  have hb : HasCompactSupport (fun t : ℝ => (b : ℂ) * h t) :=
    hs.mono (fun t ht => by
      intro h0
      exact ht (by simp [h0]))
  have gcont : Continuous (fun t : ℝ => deriv h t - (b : ℂ) * h t) :=
    hh.continuous_deriv_one.sub (hh.continuous.const_mul b)
  have gsupp : HasCompactSupport (fun t : ℝ => deriv h t - (b : ℂ) * h t) :=
    hs.deriv.sub hb
  have key : ∀ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice1 h ξ‖ ^ 2
      = ‖slice1 (fun t : ℝ => deriv h t - (b : ℂ) * h t) ξ‖ ^ 2 := by
    intro ξ
    rw [slice1_sub_const_mul' (deriv h) h (b : ℂ) hh.continuous_deriv_one hs.deriv
      hh.continuous hs ξ, slice1_deriv h hh hs ξ, ← sub_mul, norm_sq_mul_shift]
  constructor
  · exact (integrable_normSq_slice1 gcont gsupp).congr
      (Filter.Eventually.of_forall fun ξ => (key ξ).symm)
  · calc ∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice1 h ξ‖ ^ 2
        = ∫ ξ : ℝ, ‖slice1 (fun t : ℝ => deriv h t - (b : ℂ) * h t) ξ‖ ^ 2 :=
          integral_congr_ae (Filter.Eventually.of_forall key)
      _ = ∫ t : ℝ, ‖deriv h t - (b : ℂ) * h t‖ ^ 2 :=
          plancherelSlice1 (fun t : ℝ => deriv h t - (b : ℂ) * h t) gcont gsupp

end Work.FTS.EllSol.FlatFT

/-- Shifted first-order Plancherel for the `t`-Fourier slice, under the name requested for this
module (the statement above sits inside a doubly-opened `Work.FTS.EllSol.FlatFT` namespace, this
is the same theorem with the usual fully-qualified name). -/
theorem shiftPlancherel1 {h : ℝ → ℂ} (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) (b : ℝ) :
    MeasureTheory.Integrable
      (fun ξ : ℝ => ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice1 h ξ‖ ^ 2) ∧
    (∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice1 h ξ‖ ^ 2
      = ∫ t : ℝ, ‖deriv h t - b * h t‖ ^ 2) :=
  Work.FTS.EllSol.FlatFT.Work.FTS.EllSol.FlatFT.shiftPlancherel1 hh hs b

end Work.FTS.EllSol.FlatFT
