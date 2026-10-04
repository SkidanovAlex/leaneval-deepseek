import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.fourierCoeff_pd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Iterated Fourier multiplier of a partial derivative

Layer A of the STE Fourier toolkit, iterated form of `fourierCoeff_pd`:

  `fourierCoeff ((∂ᵢ)^n f) k = (2πi kᵢ)^n · fourierCoeff f k`

for `f : (ι → ℝ) → ℂ` of class `C^∞` (`ContDiff ℝ (⊤ : ℕ∞)`, i.e. the top level `∞` of
`ContDiff`) that is `1`-periodic in the `i`-th coordinate.

The proof is the induction on `n` whose step is exactly `fourierCoeff_pd`; the only two things to
check is that the tower `(∂ᵢ)^m f` stays smooth and `1`-periodic in the `i`-th coordinate, which
is `contDiff_pd_of_contDiff_top` and `periodicIn_pd` below.
-/

namespace Work.Diff.STE

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A partial derivative of a smooth function is smooth: the level `⊤ : ℕ∞` is the top level
`∞` of `ContDiff` ("differentiable of every order"), and `fderiv` lowers the level by one while
the level `∞` is fixed by `n ↦ n - 1`. -/
lemma contDiff_pd_of_contDiff_top {i : ι} {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (pd i f) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (m := (⊤ : ℕ∞)) (by norm_num)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → ℝ => (fderiv ℝ f x) (Pi.single i 1)) :=
    h1.clm_apply contDiff_const
  rw [show pd i f = (fun x : ι → ℝ => (fderiv ℝ f x) (Pi.single i 1)) from rfl]
  exact h2

/-- The partial derivative of a function periodic in the `i`-th coordinate is again periodic in
the `i`-th coordinate: translating by `eᵢ` does not change `f`, and the derivative of a translate
of `f` at `x` is the derivative of `f` at the translated point. -/
lemma periodicIn_pd {i : ι} {f : (ι → ℝ) → ℂ} (hper : PeriodicIn i f) :
    PeriodicIn i (pd i f) := by
  intro x
  simp only [pd]
  rw [show fderiv ℝ f (x + Pi.single i 1) = fderiv ℝ f x from by
    have hfun : (fun y : ι → ℝ => f (y + Pi.single i 1)) = f := funext hper
    rw [← fderiv_comp_add_right (f := f) (x := x) (Pi.single i 1), hfun]]

theorem fourierCoeff_iterate_pd {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (n : ℕ)
    (g : (ι → ℝ) → ℂ) (k : ι → ℤ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hper : Work.Diff.STE.PeriodicIn i g) :
    Work.Diff.STE.fourierCoeff ((Work.Diff.STE.pd i)^[n] g) k
      = (2 * Real.pi * Complex.I * (k i : ℂ)) ^ n * Work.Diff.STE.fourierCoeff g k := by
  -- the tower `(∂ᵢ)^m g` stays smooth and periodic in the `i`-th coordinate
  have htower : ∀ m : ℕ,
      ContDiff ℝ (⊤ : ℕ∞) ((pd i)^[m] g) ∧ PeriodicIn i ((pd i)^[m] g) := by
    intro m
    induction m with
    | zero => exact ⟨by simpa using hg, by simpa using hper⟩
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact ⟨contDiff_pd_of_contDiff_top ih.1, periodicIn_pd ih.2⟩
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hf1 : ContDiff ℝ 1 ((pd i)^[n] g) := (htower n).1.of_le (by norm_num)
      rw [fourierCoeff_pd i ((pd i)^[n] g) k hf1 (htower n).2, ih]
      ring

end Work.Diff.STE
