import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.J_finite_rank

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Linearity of the mode coefficients `scoeff` under scalar multiplication

`Work.Diff.STE.B3.scoeff n ρ ε f q` is the real coefficient of the Fourier mode `q` in the
Friedrichs truncation of the periodisation of `f` (`q = (m, σ)` with `σ = false` selecting the real
and `σ = true` the imaginary part of the character `e^{2πi m·z}`).

The whole construction is pointwise linear, so

  `scoeff n ρ ε (a • f) q = a * scoeff n ρ ε f q`

for *every* `a : ℝ` and *every* `f`; the continuity and support hypotheses of the statement are the
ones needed by the additive companion `scoeff_add_of_support` (where compact support gives
summability of the translated series) and are simply carried along here for uniformity.

The proof is a chain of three linearity steps: the translated series `∑' k, f (· + k)` (a `tsum`,
`tsum_mul_left`), the Fourier transform (`fourierCoeff`, linearity of the Bochner integral), and
the multiplier `trunc`; then the real/imaginary part extraction in the definition of `scoeff`.
-/

set_option linter.unusedVariables false

namespace Work.Diff.STE.B3

/-! ## Linearity of the three constituent maps -/

/-- The Fourier multiplier `trunc ρ ε` is linear: it is a pointwise multiplication by the
(scalar) weights `ρ (ε • m)`. -/
private lemma trunc_const_mul {n : ℕ} (ρ : (Fin n → ℝ) → ℝ) (ε : ℝ) (a : ℝ)
    (c : (Fin n → ℤ) → ℂ) :
    Work.Diff.STE.trunc ρ ε (fun m => (a : ℂ) * c m)
      = fun m => (a : ℂ) * Work.Diff.STE.trunc ρ ε c m := by
  funext m
  simp only [Work.Diff.STE.trunc]
  ring

/-- The Fourier transform `fourierCoeff` is linear: the coefficients of a constant multiple. -/
private lemma fourierCoeff_const_mul {ι : Type*} [Fintype ι] (c : ℂ) (g : (ι → ℝ) → ℂ) :
    Work.Diff.STE.fourierCoeff (fun y => c * g y)
      = fun k => c * Work.Diff.STE.fourierCoeff g k := by
  funext k
  simp only [Work.Diff.STE.fourierCoeff]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

/-- The coefficients of the periodisation are linear: `a • f` has periodisation
`y ↦ a · Σ_k f (y + k)`, by `tsum_mul_left`. -/
private lemma perCoeffN_const_mul {n : ℕ} (a : ℝ) (f : (Fin n → ℝ) → ℝ) :
    perCoeffN n (a • f) = fun m => (a : ℂ) * perCoeffN n f m := by
  funext m
  simp only [perCoeffN]
  have hpt : (fun y : Fin n → ℝ =>
        ∑' k : Fin n → ℤ, (((a • f) (y + Work.Diff.STE.iVec k) : ℝ) : ℂ))
      = fun y => (a : ℂ) * ∑' k : Fin n → ℤ,
          ((f (y + Work.Diff.STE.iVec k) : ℝ) : ℂ) := by
    funext y
    rw [← tsum_mul_left]
    refine tsum_congr (fun k => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  rw [hpt, fourierCoeff_const_mul]

/-! ## The target -/

theorem scoeff_smul_of_support
    {n : ℕ} (ρ : (Fin n → ℝ) → ℝ) (ε : ℝ) (a : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : Continuous f)
    (hfs : Function.support f ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)))
    (q : Work.Diff.STE.B3.QIdx n ε) :
    Work.Diff.STE.B3.scoeff n ρ ε (a • f) q = a * Work.Diff.STE.B3.scoeff n ρ ε f q := by
  have htrunc : ∀ m : Fin n → ℤ, Work.Diff.STE.trunc ρ ε (perCoeffN n (a • f)) m
      = (a : ℂ) * Work.Diff.STE.trunc ρ ε (perCoeffN n f) m := by
    intro m
    rw [perCoeffN_const_mul]
    exact congrFun (trunc_const_mul ρ ε a (perCoeffN n f)) m
  have hq := htrunc q.1.1
  simp only [scoeff, hq]
  cases q.2
  · simp only [Bool.cond_false, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  · simp only [Bool.cond_true, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, mul_neg]

end Work.Diff.STE.B3
