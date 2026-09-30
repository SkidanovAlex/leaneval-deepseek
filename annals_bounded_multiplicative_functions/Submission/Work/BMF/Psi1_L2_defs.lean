import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for `Work.BMF.Psi1_L2_bound`

The localisation device used to bound `∫_c^{c+1} ‖Ψ₁ f (1+α+iτ)‖² dτ` by a constant times `1/α`.

We use the **Gaussian** Fourier pair `(PhiLoc, pairK)`:
* `pairK θ = exp (-(θ²))` is the "pair kernel": it weights the pair `(p, q)` of primes by
  `pairK (log p - log q) = exp (-(log p - log q)²)`, i.e. it decays *super-exponentially* in the
  logarithmic distance `|log p - log q|`. This is what makes the local prime mass at `p` bounded by
  `C · p^{-α}` (see `Submission.Work.BMF.Psi1_L2_local_mass`).
* `PhiLoc s = (1/(2√π)) · exp (-(s²)/4)` is the nonnegative, integrable localiser, with
  `PhiLoc_fourier : ∫ s, PhiLoc s * exp (-I·s·θ) = pairK θ`, and `PhiLoc s ≥ phiDelta > 0` for
  `s ∈ [0,1]`, where `phiDelta = PhiLoc 1 = exp (-1/4)/(2√π)`.
-/

namespace Work.BMF

open Real MeasureTheory

noncomputable section

/-- The τ-localiser `PhiLoc s = (1/(2√π)) e^{-s²/4}`. -/
noncomputable def PhiLoc (s : ℝ) : ℝ := (1 / (2 * Real.sqrt Real.pi)) * Real.exp (-(s ^ 2) / 4)

/-- The pair kernel `pairK θ = e^{-θ²}`. -/
noncomputable def pairK (θ : ℝ) : ℝ := Real.exp (-(θ ^ 2))

/-- `phiDelta = PhiLoc 1 = e^{-1/4} / (2√π) > 0`, a lower bound for `PhiLoc` on `[0,1]`. -/
noncomputable def phiDelta : ℝ := (1 / (2 * Real.sqrt Real.pi)) * Real.exp (-(1 : ℝ) / 4)

lemma PhiLoc_nonneg (s : ℝ) : 0 ≤ PhiLoc s := by
  rw [PhiLoc]; positivity

lemma pairK_nonneg (θ : ℝ) : 0 ≤ pairK θ := Real.exp_nonneg _

lemma pairK_le_one (θ : ℝ) : pairK θ ≤ 1 := by
  rw [pairK]; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg θ))

lemma phiDelta_pos : 0 < phiDelta := by
  rw [phiDelta]; positivity

lemma PhiLoc_one : PhiLoc 1 = phiDelta := by
  rw [PhiLoc, phiDelta]; norm_num

/-- On `[0,1]`, `PhiLoc` is bounded below by `phiDelta`. -/
lemma phiDelta_le_PhiLoc {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) : phiDelta ≤ PhiLoc s := by
  have hc : (0 : ℝ) < 1 / (2 * Real.sqrt Real.pi) := by positivity
  have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
  rw [PhiLoc, phiDelta]
  apply mul_le_mul_of_nonneg_left _ hc.le
  apply Real.exp_le_exp.mpr
  linarith

lemma PhiLoc_eq (s : ℝ) :
    PhiLoc s = (1 / (2 * Real.sqrt Real.pi)) * Real.exp (-(1 / 4 : ℝ) * s ^ 2) := by
  rw [PhiLoc]; ring_nf

lemma PhiLoc_integrable : Integrable PhiLoc := by
  have h : Integrable
      (fun s : ℝ => (1 / (2 * Real.sqrt Real.pi)) * Real.exp (-(1 / 4 : ℝ) * s ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul _
  have heq : PhiLoc
      = fun s : ℝ => (1 / (2 * Real.sqrt Real.pi)) * Real.exp (-(1 / 4 : ℝ) * s ^ 2) :=
    funext PhiLoc_eq
  rw [heq]; exact h

lemma PhiLoc_continuous : Continuous PhiLoc := by
  have heq : PhiLoc
      = fun s : ℝ => (1 / (2 * Real.sqrt Real.pi)) * Real.exp (-(1 / 4 : ℝ) * s ^ 2) :=
    funext PhiLoc_eq
  rw [heq]
  fun_prop

lemma PhiLoc_integrableC : Integrable (fun s : ℝ => (PhiLoc s : ℂ)) := by
  have hmeas : AEStronglyMeasurable (fun s : ℝ => (PhiLoc s : ℂ)) volume :=
    (Complex.continuous_ofReal.comp PhiLoc_continuous).aestronglyMeasurable
  rw [← MeasureTheory.integrable_norm_iff hmeas]
  have hfun : (fun s : ℝ => ‖(PhiLoc s : ℂ)‖) = PhiLoc := by
    funext s
    rw [Complex.norm_real, Real.norm_of_nonneg (PhiLoc_nonneg s)]
  rw [hfun]
  exact PhiLoc_integrable

/-- **Fourier pair identity**: `∫ s, PhiLoc s * exp (-I·s·θ) = pairK θ`. -/
theorem PhiLoc_fourier (θ : ℝ) :
    ∫ s : ℝ, ((PhiLoc s : ℂ) * Complex.exp (-(s * θ) * Complex.I)) = (pairK θ : ℂ) := by
  have h14 : (0 : ℝ) < 1 / 4 := by norm_num
  have hb : (0 : ℝ) < (((1 / 4 : ℝ) : ℂ)).re := by simpa using h14
  have hgauss := fourierIntegral_gaussian (b := ((1 / 4 : ℝ) : ℂ)) hb ((-θ : ℝ) : ℂ)
  have hpt : ∀ s : ℝ, (PhiLoc s : ℂ) * Complex.exp (-(s * θ) * Complex.I)
      = (1 / (2 * Real.sqrt Real.pi) : ℂ) *
        (Complex.exp (Complex.I * ((-θ : ℝ) : ℂ) * (s : ℂ)) *
          Complex.exp (-((1 / 4 : ℝ) : ℂ) * (s : ℂ) ^ 2)) := by
    intro s
    rw [PhiLoc_eq]
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_exp]
    rw [mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [funext hpt, MeasureTheory.integral_const_mul, hgauss, pairK]
  rw [show (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) by norm_num]
  have h1 : ((Real.pi : ℂ) / ((1 / 4 : ℝ) : ℂ)) ^ (((1 / 2 : ℝ)) : ℂ)
      = ((2 * Real.sqrt Real.pi : ℝ) : ℂ) := by
    have hbase : (Real.pi : ℂ) / ((1 / 4 : ℝ) : ℂ) = ((4 * Real.pi : ℝ) : ℂ) := by
      push_cast; field_simp
    rw [hbase, ← Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ 4 * Real.pi)]
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    norm_num
  have h2 : Complex.exp (-(((-θ : ℝ) : ℂ)) ^ 2 / (4 * ((1 / 4 : ℝ) : ℂ)))
      = (((Real.exp (-(θ ^ 2)) : ℝ)) : ℂ) := by
    rw [show (4 : ℂ) * ((1 / 4 : ℝ) : ℂ) = 1 by norm_num, div_one]
    rw [show -(((-θ : ℝ) : ℂ)) ^ 2 = ((-(θ ^ 2) : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_exp]
  rw [h1, h2]
  have hs : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  field_simp
  push_cast
  ring

end

end Work.BMF
