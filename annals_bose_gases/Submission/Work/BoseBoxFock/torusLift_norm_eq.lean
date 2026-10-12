import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.integral_toLp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

attribute [local instance] instMeasureSpaceUnitAddCircle

namespace Work.BoseBoxFock

/-- **The torus lift is an isometry.**  For a smooth compactly supported `g : ℝ³ → ℂ` whose
support lies in the unit box `[-1/2,1/2]³`, the `L²` norm of its torus lift equals the `L²`
norm of `g`. -/
theorem torusLift_norm_eq {g : ℝ³ → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g)
    (hgsupp : tsupport g ⊆ {y : ℝ³ | ∀ i, |y i| ≤ (1 / 2 : ℝ)}) :
    (∫ t : UnitAddTorus (Fin 3), ‖Work.BoseBoxFock.torusLift g t‖ ^ 2
        ∂Work.BoseBoxFock.torusVol)
      = ∫ y : ℝ³, ‖g y‖ ^ 2 := by
  -- The half-open box, in the form produced by `UnitAddTorus.integral_preimage`.
  have hbox : boxIoc
      = {x : Fin 3 → ℝ | ∀ i, x i ∈ Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1)} := by
    ext x
    simp only [boxIoc, Set.mem_pi, Set.mem_univ, Set.mem_Ioc, Set.mem_ofPred_eq, true_implies]
    constructor <;> intro h i
    · exact ⟨(h i).1, by linarith [(h i).2]⟩
    · exact ⟨(h i).1, by linarith [(h i).2]⟩
  -- Step 1: the torus integral is the integral over the fundamental domain of the projection.
  have h1 : (∫ t : UnitAddTorus (Fin 3), ‖torusLift g t‖ ^ 2 ∂torusVol)
      = ∫ x in boxIoc, ‖torusLift g (torusProj x)‖ ^ 2 := by
    rw [torusVol_eq_volume, hbox]
    exact UnitAddTorus.integral_preimage (d := Fin 3)
      (fun t : UnitAddTorus (Fin 3) => ‖torusLift g t‖ ^ 2)
      (fun _ => (-(1/2) : ℝ))
  -- Step 2: on the fundamental domain the lift of `g` is `g` itself.
  have h2 : ∫ x in boxIoc, ‖torusLift g (torusProj x)‖ ^ 2
      = ∫ x in boxIoc, ‖g (WithLp.toLp 2 x)‖ ^ 2 := by
    refine setIntegral_congr_fun measurableSet_boxIoc fun x hx => ?_
    rw [torusLift_apply_proj hx]
  -- Step 3: `g` vanishes off the closed box, which agrees a.e. with the half-open box.
  have h3 : ∫ x in boxIoc, ‖g (WithLp.toLp 2 x)‖ ^ 2
      = ∫ x : Fin 3 → ℝ, ‖g (WithLp.toLp 2 x)‖ ^ 2 := by
    rw [setIntegral_congr_set boxIoc_ae_eq_boxIcc,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    have hx' : ¬ ∀ i, |x i| ≤ (1 / 2 : ℝ) := fun h => hx (mem_boxIcc.mpr h)
    simp only [not_forall, not_le] at hx'
    obtain ⟨i, hi⟩ := hx'
    have hy : ¬ ∀ i, |(WithLp.toLp 2 x : ℝ³) i| ≤ (1 / 2 : ℝ) :=
      fun h => absurd (h i) (not_le.mpr hi)
    have h0 : g (WithLp.toLp 2 x) = 0 := by
      by_contra hc
      exact hy (hgsupp (subset_tsupport g (Function.mem_support.mpr hc)))
    rw [h0, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  -- Step 4: change of variables along `WithLp.toLp 2`.
  rw [h1, h2, h3, ← integral_toLp (fun y : ℝ³ => ‖g y‖ ^ 2)]

end Work.BoseBoxFock
