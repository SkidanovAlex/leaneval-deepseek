import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.fourierCoeff_mul_seriesFun
import Submission.Work.Diff.STE.integral_fourierExp
import Submission.Work.Diff.STE.bessel_continuous

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Inversion of the Fourier series: `fourierCoeff (seriesFun c) k = c k`

For an absolutely summable coefficient family `c : (ι → ℤ) → ℂ` (`Σ_k ‖c k‖ < ∞`), the Fourier
series `seriesFun c x = Σ_k c k · exp (2πi k·x)` has Fourier coefficients `c` again.  This is the
elementary (absolutely convergent) half of Fourier inversion on the unit torus, and it is what
justifies reading the Galerkin/energy estimates of the flat STE development as statements about
the coefficient family `c` itself.

The argument is a specialisation of the Fourier-side product rule
`Work.Diff.STE.fourierCoeff_mul_seriesFun` to the constant function `g = 1`:
`fourierCoeff (seriesFun c) k = conv c (fourierCoeff 1) k`, and the Fourier coefficients of the
constant `1` are the Kronecker delta (`fourierCoeff_one`, from the character orthogonality
`Work.Diff.STE.integral_fourierExp`), so the convolution with `c` is just `c`
(`conv_fourierCoeff_one`).
-/

noncomputable section

namespace Work.Diff.STE.flat

open MeasureTheory

/-- The Fourier coefficients of the constant function `1` on the torus are the Kronecker
delta, `fourierCoeff 1 j = if j = 0 then 1 else 0`: this is the orthogonality relation
`∫_{unitCube} fourierExp m = δ_{m,0}` for the characters. -/
private lemma fourierCoeff_one {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι → ℤ) :
    Work.Diff.STE.fourierCoeff (fun _ : ι → ℝ => (1 : ℂ)) j = if j = 0 then 1 else 0 := by
  rw [Work.Diff.STE.fourierCoeff]
  simp only [mul_one]
  rw [Work.Diff.STE.integral_fourierExp]
  by_cases hj : j = 0
  · subst hj
    simp
  · have hne : ¬(((-j : ι → ℤ)) = 0) := fun h => hj (neg_eq_zero.mp h)
    simp only [hne, ite_false, hj]

/-- Convolution of a coefficient family with the Fourier coefficients of the constant `1`
is the identity: `conv c (fourierCoeff 1) = c`.  Indeed the family
`b ↦ c b · (fourierCoeff 1) (k - b)` is supported on the single point `b = k`. -/
private lemma conv_fourierCoeff_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : (ι → ℤ) → ℂ) (k : ι → ℤ) :
    Work.Diff.STE.conv c (Work.Diff.STE.fourierCoeff (fun _ : ι → ℝ => (1 : ℂ))) k = c k := by
  have hsum : (∑' b : ι → ℤ, c b * Work.Diff.STE.fourierCoeff (fun _ : ι → ℝ => (1 : ℂ)) (k - b))
      = c k := by
    rw [tsum_eq_single k]
    · rw [fourierCoeff_one]; simp
    · intro b hb
      rw [fourierCoeff_one]
      have hne : ¬((k - b) = 0) := sub_ne_zero.mpr (fun h => hb h.symm)
      simp only [hne, ite_false, mul_zero]
  rw [Work.Diff.STE.conv, hsum]

/-- **Fourier inversion for absolutely convergent series.**  If `Σ_k ‖c k‖ < ∞`, then the `k`-th
Fourier coefficient of the series `seriesFun c = Σ_j c j · exp (2πi j·x)` is `c k`. -/
theorem fourierCoeff_seriesFun {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : (ι → ℤ) → ℂ) (hc : Summable (fun k => ‖c k‖)) (k : ι → ℤ) :
    Work.Diff.STE.fourierCoeff (Work.Diff.STE.seriesFun c) k = c k := by
  have : IsFiniteMeasure (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.BesselCont.isFiniteMeasure_restrict_unitCube
  have hg : Integrable (fun _ : ι → ℝ => (1 : ℂ))
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) := integrable_const 1
  have hmain := Work.Diff.STE.fourierCoeff_mul_seriesFun (fun _ : ι → ℝ => (1 : ℂ)) c k hg hc
  rw [show (fun x : ι → ℝ => (1 : ℂ) * Work.Diff.STE.seriesFun c x)
        = Work.Diff.STE.seriesFun c from funext fun x => one_mul _] at hmain
  rw [hmain]
  exact conv_fourierCoeff_one c k

end Work.Diff.STE.flat
