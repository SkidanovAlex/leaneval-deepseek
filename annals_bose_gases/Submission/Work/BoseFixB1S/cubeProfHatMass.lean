import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.pcDefs
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.cubeProfHatMass` — the `L²` mass of the cube cutoff's profile

`profHatCube M p = ∫ z, χ_M(z)·cos⟪p,z⟫` is the (real) `p`-convention Fourier transform of the
cube cutoff `chiSmall M` (`cubeKinFT_chiSmall`).  Here we prove that `p ↦ profHatCube M p²` is
integrable, i.e. that the cube profile is an `L²` function.

Route (deliberately avoiding the full Fourier-transform identity): `profHatCube M p` is the *real
part* of `kinFT (chiSmall M : ℝ³ → ℂ) p` (the cosine profile is exactly the real part of the Fourier
integral), so `profHatCube M p² ≤ ‖kinFT (chiSmall M) p‖²`; the right-hand side is integrable by the
`L¹ ∩ L²` Plancherel theorem (`Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp`, since `chiSmall M` is
continuous with compact support), and integrability transfers by monotonicity
(`MeasureTheory.Integrable.mono'`).

The `AEStronglyMeasurable` input of `mono'` is supplied by continuity of `p ↦ kinFT χ p`
(`Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable`), again through the real-part identity.
-/

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The cosine profile of the cube cutoff is the real part of its Fourier transform.** -/
private theorem profHatCube_eq_re_kinFT (M : ℕ) (hM : 1 ≤ M) (p : E3) :
    profHatCube M p
      = (Submission.BoseGases.kinFT (fun z : E3 => (Submission.BoseGases.chiSmall M z : ℂ)) p).re := by
  have hχint : Integrable (fun y : E3 =>
      Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
        * (Submission.BoseGases.chiSmall M y : ℂ)) := by
    have hc : Continuous (fun y : E3 =>
        Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
          * (Submission.BoseGases.chiSmall M y : ℂ)) := by
      apply Continuous.mul
      · exact Complex.continuous_exp.comp (Continuous.neg (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id))))
      · exact Complex.continuous_ofReal.comp (Submission.BoseGases.chiSmall_continuous hM)
    have hcs : HasCompactSupport (fun y : E3 =>
        Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
          * (Submission.BoseGases.chiSmall M y : ℂ)) := by
      refine (Submission.BoseGases.chiSmall_hasCompactSupport hM).mono (fun y hy => ?_)
      intro hchi
      exact hy (by simp [hchi])
    exact hc.integrable_of_hasCompactSupport hcs
  have hcomp : (∫ y : E3, Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
      * (Submission.BoseGases.chiSmall M y : ℂ)).re
      = ∫ y : E3, (Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
      * (Submission.BoseGases.chiSmall M y : ℂ)).re := by
    have := ContinuousLinearMap.integral_comp_comm Complex.reCLM hχint
    simpa using this.symm
  rw [profHatCube, Submission.BoseGases.kinFT, hcomp]
  apply integral_congr_ae
  filter_upwards with z
  have hx : -(Complex.I * ((inner ℝ p z : ℝ) : ℂ)) = (((-inner ℝ p z : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hx, Complex.exp_ofReal_mul_I]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Real.cos_neg, Real.sin_neg]
  ring

theorem cubeProfHatMass (M : ℕ) (hM : 1 ≤ M) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      (Work.BoseFixB1S.profHatCube M p) ^ 2) := by
  have hcont : Continuous (fun z : E3 => (Submission.BoseGases.chiSmall M z : ℂ)) :=
    Complex.continuous_ofReal.comp (Submission.BoseGases.chiSmall_continuous hM)
  have hcs : HasCompactSupport (fun z : E3 => (Submission.BoseGases.chiSmall M z : ℂ)) :=
    (Submission.BoseGases.chiSmall_hasCompactSupport hM).comp_left
      (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hint : Integrable (fun z : E3 => (Submission.BoseGases.chiSmall M z : ℂ)) :=
    hcont.integrable_of_hasCompactSupport hcs
  have hmem1 : MemLp (fun z : E3 => (Submission.BoseGases.chiSmall M z : ℂ)) 1 volume :=
    memLp_one_iff_integrable.mpr hint
  have hmem2 : MemLp (fun z : E3 => (Submission.BoseGases.chiSmall M z : ℂ)) 2 volume :=
    hcont.memLp_of_hasCompactSupport hcs
  have hPL : Integrable (fun p : E3 =>
      ‖Submission.BoseGases.kinFT (fun z : E3 => (Submission.BoseGases.chiSmall M z : ℂ)) p‖ ^ 2) :=
    (Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp hmem1 hmem2).1
  have hcontK : Continuous (fun p : E3 =>
      Submission.BoseGases.kinFT (fun z : E3 => (Submission.BoseGases.chiSmall M z : ℂ)) p) :=
    Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable hint
  refine hPL.mono' ?_ ?_
  · have heq : (fun p : E3 => profHatCube M p ^ 2)
        = fun p : E3 => ((Submission.BoseGases.kinFT
            (fun z : E3 => (Submission.BoseGases.chiSmall M z : ℂ)) p).re) ^ 2 :=
      funext fun p => by rw [profHatCube_eq_re_kinFT M hM p]
    rw [heq]
    exact (((Complex.continuous_re.comp hcontK).pow 2)).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), profHatCube_eq_re_kinFT M hM p]
    have h1 := Complex.re_sq_le_normSq
      (Submission.BoseGases.kinFT (fun z : E3 => (Submission.BoseGases.chiSmall M z : ℂ)) p)
    rw [Complex.normSq_eq_norm_sq] at h1
    simpa [pow_two] using h1

end Work.BoseFixB1S
