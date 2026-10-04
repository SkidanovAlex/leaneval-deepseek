import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.CubeSplit
import Submission.Work.Diff.STE.cube_fubini
import Submission.Work.Diff.STE.pd_integral_zero
import Submission.Work.Diff.STE.pd_fourierExp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Fourier coefficient of a partial derivative

Layer A of the STE Fourier toolkit: `∂ᵢ` is the Fourier multiplier `2πi kᵢ`, i.e.

  `fourierCoeff (pd i f) k = (2πi kᵢ) * fourierCoeff f k`

for `f : (ι → ℝ) → ℂ` of class `C¹` that is `1`-periodic in the `i`-th coordinate.

The proof is integration by parts on the torus.  Writing `g = fourierExp (-k)` (so that
`∂ᵢ g = -2πi kᵢ · g`) and `G = g · f`, the product rule gives the pointwise identity

  `g x * pd i f x = pd i G x + c * (g x * f x)`,  `c = 2πi kᵢ`,

and `∫_{unitCube} pd i G = 0` because `G` is `C¹` and periodic in the `i`-th coordinate.  The
latter is the Fubini decomposition of the cube integral (`cube_fubini`, splitting off the
`i`-th coordinate) followed by a one-dimensional fundamental-theorem-of-calculus computation
(`pd_integral_zero`).
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Elementary properties of `fourierExp` -/

/-- The sum of the characters along a shift in the `i`-th coordinate. -/
lemma sum_char_smul_single (m : ι → ℤ) (i : ι) (x : ι → ℝ) (t : ℝ) :
    (∑ j, (m j : ℂ) * ((x + t • Pi.single i 1 : ι → ℝ) j : ℂ))
      = (∑ j, (m j : ℂ) * (x j : ℂ)) + (t : ℂ) * (m i : ℂ) := by
  have step : ∀ j : ι, (m j : ℂ) * ((x + t • Pi.single i 1 : ι → ℝ) j : ℂ)
      = (m j : ℂ) * (x j : ℂ) + (if j = i then (t : ℂ) * (m i : ℂ) else 0) := by
    intro j
    by_cases h : j = i
    · subst h; simp; ring
    · simp [Pi.add_apply, h]
  simp_rw [step]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

lemma contDiff_fourierExp (m : ι → ℤ) : ContDiff ℝ 1 (fourierExp m) := by
  rw [show fourierExp m = fun x : ι → ℝ =>
      Complex.exp (((2 * (Real.pi : ℝ) : ℂ)) * Complex.I * ∑ j, (m j : ℂ) * (x j : ℂ))
      from rfl]
  apply Complex.contDiff_exp.comp
  have hsum : ContDiff ℝ 1 (fun x : ι → ℝ => (∑ j, (m j : ℂ) * (x j : ℂ))) := by
    apply ContDiff.sum
    intro j _
    have h2 : ContDiff ℝ 1 (fun r : ℝ => (r : ℂ)) := Complex.ofRealCLM.contDiff
    exact (contDiff_const (c := (m j : ℂ))).mul (h2.comp (by fun_prop))
  exact (contDiff_const (c := (((2 * (Real.pi : ℝ) : ℂ)) * Complex.I))).mul hsum

lemma periodicIn_fourierExp (m : ι → ℤ) (i : ι) : PeriodicIn i (fourierExp m) := by
  intro x
  simp only [fourierExp]
  rw [show (∑ j, (m j : ℂ) * ((x + Pi.single i 1 : ι → ℝ) j : ℂ))
      = (∑ j, (m j : ℂ) * (x j : ℂ)) + (m i : ℂ) by
    simpa using sum_char_smul_single m i x 1]
  rw [mul_add, Complex.exp_add]
  rw [show ((2 * (Real.pi:ℝ) : ℂ)) * Complex.I * (m i : ℂ)
      = (m i : ℂ) * (2 * (Real.pi:ℝ) * Complex.I) by ring]
  rw [Complex.exp_int_mul_two_pi_mul_I]
  ring

/-! ## Derivatives of `pd` -/

/-- Leibniz rule for the partial derivative `pd`. -/
lemma pd_mul (i : ι) {g f : (ι → ℝ) → ℂ} {x : ι → ℝ}
    (hg : DifferentiableAt ℝ g x) (hf : DifferentiableAt ℝ f x) :
    pd i (fun y => g y * f y) x = pd i g x * f x + g x * pd i f x := by
  simp only [pd]
  rw [fderiv_fun_mul hg hf]
  simp only [ContinuousLinearMap.add_apply, smul_apply, smul_eq_mul]
  ring

/-- `pd i f` is continuous when `f` is `C¹`. -/
lemma continuous_pd {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) (i : ι) :
    Continuous (pd i f) := by
  have h := hf.continuous_fderiv_apply (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have h2 : Continuous (fun x : ι → ℝ => (x, (Pi.single i 1 : ι → ℝ))) := by fun_prop
  exact h.comp h2

/-! ## Integrability on the cube -/

/-- A continuous function is integrable on the (bounded) unit cube. -/
lemma integrableOn_unitCube_of_continuous {F : (ι → ℝ) → ℂ} (hF : Continuous F) :
    Integrable F (volume.restrict unitCube) := by
  have hC : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsub : unitCube ⊆ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩
  exact (ContinuousOn.integrableOn_compact hC hF.continuousOn).mono_set hsub

/-! ## The integral of a periodic partial derivative -/

/-- The partial derivative of a `C¹` function periodic in the `i`-th coordinate integrates to
zero over the unit cube. -/
lemma integral_pd_unitCube_zero (i : ι) {h : (ι → ℝ) → ℂ} (hh : ContDiff ℝ 1 h)
    (hper : PeriodicIn i h) :
    ∫ x in unitCube, pd i h x = 0 := by
  rw [cube_fubini i (pd i h) (continuous_pd hh i)]
  have hz : ∀ y : {j : ι // j ≠ i} → ℝ,
      ∫ t in Set.Ioc (0 : ℝ) 1, pd i h (insertAt i t y) = 0 := by
    intro y
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact pd_integral_zero i h hh hper y
  simp_rw [hz]
  simp

/-! ## The main computation -/

theorem fourierCoeff_pd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (f : (ι → ℝ) → ℂ) (k : ι → ℤ)
    (hf : ContDiff ℝ 1 f) (hper : Work.Diff.STE.PeriodicIn i f) :
    Work.Diff.STE.fourierCoeff (Work.Diff.STE.pd i f) k
      = (2 * Real.pi * Complex.I * (k i : ℂ)) * Work.Diff.STE.fourierCoeff f k := by
  have hG : ContDiff ℝ 1 (fun y : ι → ℝ => fourierExp (-k) y * f y) :=
    (contDiff_fourierExp (-k)).mul hf
  have hperG : PeriodicIn i (fun y : ι → ℝ => fourierExp (-k) y * f y) := by
    intro x
    simp only [Pi.add_apply]
    rw [periodicIn_fourierExp (-k) i x, hper x]
  have hpoint : ∀ x : ι → ℝ,
      fourierExp (-k) x * pd i f x
        = pd i (fun y => fourierExp (-k) y * f y) x
            + (2 * Real.pi * Complex.I * (k i : ℂ)) * (fourierExp (-k) x * f x) := by
    intro x
    rw [pd_mul i ((contDiff_fourierExp (-k)).differentiable_one.differentiableAt)
          (hf.differentiable_one.differentiableAt)]
    rw [pd_fourierExp (-k) i x]
    have hneg : (((-k) i : ℤ) : ℂ) = -((k i : ℤ) : ℂ) := by simp
    rw [hneg]
    ring
  have hgf : Continuous (fun x : ι → ℝ => fourierExp (-k) x * f x) :=
    (contDiff_fourierExp (-k)).continuous.mul hf.continuous
  have h1 : Integrable (fun x : ι → ℝ => pd i (fun y => fourierExp (-k) y * f y) x)
      (volume.restrict unitCube) := integrableOn_unitCube_of_continuous (continuous_pd hG i)
  have h2 : Integrable
      (fun x : ι → ℝ => (2 * Real.pi * Complex.I * (k i : ℂ)) * (fourierExp (-k) x * f x))
      (volume.restrict unitCube) :=
    integrableOn_unitCube_of_continuous (continuous_const.mul hgf)
  simp only [fourierCoeff]
  rw [funext hpoint, integral_add h1 h2, integral_pd_unitCube_zero i hG hperG,
    integral_const_mul]
  ring

end Work.Diff.STE
