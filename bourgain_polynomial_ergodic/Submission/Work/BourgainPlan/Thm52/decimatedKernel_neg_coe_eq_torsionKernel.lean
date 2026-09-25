import Mathlib
import Submission.Work.BourgainPlan.Thm52.decimatedKernel_lp
import Submission.Work.BourgainPlan.IonescuWainger.TorsionFamilyBound

namespace Work.BourgainPlan.Thm52

open MeasureTheory
open scoped BigOperators Interval

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-- `star (fourier j t) = fourier (-j) t`, i.e. the conjugate of the character `fourier j` is the
character of the opposite frequency. -/
private lemma star_fourier_eq (j : ℤ) (t : Work.BourgainPlan.IonescuWainger.Circle) :
    star (fourier j t) = fourier (-j) t := by
  rw [← starRingEnd_apply]
  exact (fourier_neg (n := j) (x := t)).symm

/-- `star (fourier j (-t)) = fourier j t`. -/
private lemma star_fourier_neg_eq (j : ℤ) (t : Work.BourgainPlan.IonescuWainger.Circle) :
    star (fourier j (-t)) = fourier j t := by
  have h : fourier j (-t) = star (fourier j t) := by
    simp only [Complex.star_def]
    rw [← fourier_neg (n := j) (x := t), fourier_apply, fourier_apply, neg_zsmul, smul_neg]
  rw [h, star_star]

/-- **The two integral conventions agree.**  The interval integral against `exp (2 π i j x)` of the
*reflected* bump `x ↦ φ (-x)` equals the Haar integral `∫ φ · star (fourier j)`.

Substituting `x ↦ -x` (`intervalIntegral.integral_comp_neg`) turns the left-hand side into the
interval-integral expression of `fourierCoeff φ j` (`fourierCoeff_eq_intervalIntegral`, `a = -1/2`),
while the conjugation identity `star (fourier j ·) = fourier (-j) ·` identifies the right-hand side
with the defining integral of `fourierCoeff φ j`.  This also uses
`AddCircle.integral_haarAddCircle`: for `T = 1` the Haar measure is already normalised. -/
private lemma intervalIntegral_neg_coe_eq_haar
    (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ) (j : ℤ) :
    (∫ ξ in (-(1/2):ℝ)..(1/2),
        φ (-(ξ : Work.BourgainPlan.IonescuWainger.Circle)) *
          Complex.exp (2 * Real.pi * Complex.I * ((j:ℂ) * (ξ:ℂ))))
      = ∫ ξ, φ ξ * star (fourier j ξ)
          ∂(AddCircle.haarAddCircle (T := 1)) := by
  let F : ℝ → ℂ := fun x =>
    φ (x : Work.BourgainPlan.IonescuWainger.Circle) *
      star (fourier j (x : Work.BourgainPlan.IonescuWainger.Circle))
  -- The Haar integral is the `fourierCoeff` of `φ` at `j`.
  have hR : (∫ ξ, φ ξ * star (fourier j ξ) ∂(AddCircle.haarAddCircle (T := 1)))
      = fourierCoeff (T := 1) φ j := by
    rw [fourierCoeff]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    change φ t * star (fourier j t) = fourier (-j) t • φ t
    rw [star_fourier_eq, smul_eq_mul]
    ring
  -- `fourierCoeff` as an interval integral over `(-1/2, 1/2)`.
  have hC : fourierCoeff (T := 1) φ j
      = ∫ x in (-(1/2):ℝ)..(1/2),
          fourier (-j) (x : Work.BourgainPlan.IonescuWainger.Circle) •
            φ (x : Work.BourgainPlan.IonescuWainger.Circle) := by
    rw [fourierCoeff_eq_intervalIntegral φ j (-(1/2))]
    rw [show (-(1/2:ℝ) + 1) = (1/2) by norm_num]
    rw [show ((1:ℝ)/1) = 1 by norm_num, one_smul]
  -- The two interval-integrand conventions.
  have h1 : (∫ x in (-(1/2):ℝ)..(1/2),
        fourier (-j) (x : Work.BourgainPlan.IonescuWainger.Circle) •
          φ (x : Work.BourgainPlan.IonescuWainger.Circle))
      = ∫ x in (-(1/2):ℝ)..(1/2), F x := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [F]
    rw [star_fourier_eq, smul_eq_mul]
    ring
  -- The reflection `x ↦ -x` on the symmetric interval.
  have h2 : (∫ x in (-(1/2):ℝ)..(1/2), F x)
      = ∫ x in (-(1/2):ℝ)..(1/2), F (-x) := by
    have h := intervalIntegral.integral_comp_neg (f := F) (a := (-(1/2):ℝ)) (b := (1/2))
    rw [neg_neg] at h
    exact h.symm
  -- `F (-x)` is the integrand of the decimated kernel of the reflected bump.
  have h3 : (∫ x in (-(1/2):ℝ)..(1/2), F (-x))
      = ∫ ξ in (-(1/2):ℝ)..(1/2),
          φ (-(ξ : Work.BourgainPlan.IonescuWainger.Circle)) *
            Complex.exp (2 * Real.pi * Complex.I * ((j:ℂ) * (ξ:ℂ))) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [F]
    rw [AddCircle.coe_neg, star_fourier_neg_eq]
    congr 1
    rw [fourier_coe_apply]
    norm_num
    congr 1
    ring
  rw [hR, hC, h1, h2, h3]

-- The bridge between the two kernel conventions in this corpus: the decimated kernel of the
-- *reflected* circle bump, as defined in Work.BourgainPlan.Thm52.decimatedKernel, is the torsion
-- (decimated) kernel Work.BourgainPlan.IonescuWainger.torsionKernel attached to the coefficients
-- K j = ∫ phi * star (fourier j) of the corpus's opArc convention.
-- Route: torsionKernel A K j = Q_A * (if Q_A | j then K j else 0) by definition, and
-- decimatedKernel Q m j = Q * (if Q | j then ∫ xi in (-1/2)..(1/2), m xi * exp (2 pi i j xi) else 0),
-- so after rewriting both sides the goal is the identity
-- ∫ x in (-1/2)..(1/2), phi (-(x : Circle)) * exp (2 pi i j x) = ∫ xi, phi xi * star (fourier j xi)
-- of the two integral conventions.  Substitute x |-> -x in the interval integral
-- (intervalIntegral.integral_comp_neg) to get ∫ y, phi (y : Circle) * exp (-2 pi i j y), i.e.
-- the Fourier coefficient of phi at j, which is the Haar integral over the circle by
-- AddCircle.fourierCoeff_eq_intervalIntegral (with a = -1/2, T = 1) together with
-- AddCircle.integral_haarAddCircle (the Haar measure is the normalised one).  The hypothesis hφ
-- supplies the integrability of phi * star (fourier j) on the probability space (MemLp.integrable).
theorem decimatedKernel_neg_coe_eq_torsionKernel {A : Finset ℕ}
    (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) (j : ℤ) :
    Work.BourgainPlan.Thm52.decimatedKernel (Work.BourgainPlan.IonescuWainger.QA A)
        (fun x : ℝ => φ (-(x : Work.BourgainPlan.IonescuWainger.Circle))) j
      = Work.BourgainPlan.IonescuWainger.torsionKernel A
          (fun l : ℤ => ∫ ξ, φ ξ * star (fourier l ξ)
            ∂(AddCircle.haarAddCircle (T := 1))) j := by
  rw [Work.BourgainPlan.Thm52.decimatedKernel,
    Work.BourgainPlan.IonescuWainger.torsionKernel]
  by_cases h : (Work.BourgainPlan.IonescuWainger.QA A : ℤ) ∣ j
  · rw [if_pos h, if_pos h]
    congr 1
    exact intervalIntegral_neg_coe_eq_haar φ j
  · rw [if_neg h, if_neg h]

end

end Work.BourgainPlan.Thm52
