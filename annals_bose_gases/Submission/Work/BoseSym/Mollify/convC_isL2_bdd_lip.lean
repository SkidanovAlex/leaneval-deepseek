import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseSym.Mollify.conv_fderiv_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseSym.Mollify.convC_isL2_bdd_lip`

The three basic regularity properties of the convolution `f ⋆ ρ` on configuration
space `Conf N = Fin N → EuclideanSpace ℝ (Fin 3)`:

* it is square integrable (it is continuous, since `f` is continuous with compact
  support, and it has compact support, since `tsupport (f ⋆ ρ) ⊆ tsupport f + tsupport ρ`);
* it is bounded by `‖f‖₂ ‖ρ‖₂` (Cauchy–Schwarz against the reflected function
  `y ↦ ρ (x - y)`, whose `L²` seminorm equals that of `ρ` by translation invariance
  of Lebesgue measure);
* it is Lipschitz with constant `‖∇f‖₂ ‖ρ‖₂`: its gradient is `∇f ⋆ ρ`
  (`Work.BoseSym.Mollify.conv_fderiv_le`, Mathlib's
  `HasCompactSupport.hasFDerivAt_convolution_left`), which is bounded by that
  constant, and a `C¹` function on a convex set with bounded derivative is
  Lipschitz with that constant (Mathlib's `Convex.norm_image_sub_le_of_norm_fderiv_le`).

The hypotheses `hbnd`, `hlip` of the statement are exactly the two numerical
bounds obtained from Cauchy–Schwarz, pre-composed with `toReal` so that the
constants `B` and `Λ` are real numbers.
-/

namespace Work.BoseSym.Mollify

open MeasureTheory Filter
open Work.BoseSym
open scoped Topology Real ContDiff ENNReal NNReal Convolution

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Translation invariance of the `L²` seminorm, in the form needed here: the
seminorm of the reflected function `t ↦ g (x - t)` is the seminorm of `g`. -/
lemma eLp2_sub_left (N : ℕ) (g : Conf N → ℝ) (x : Conf N) :
    eLpNorm (fun t => g (x - t)) 2 (volC N) = eLp2 N g := by
  have hneg : (volC N).IsNegInvariant := Pi.isNegInvariant_volume
  have hmap : Measure.map (fun t : Conf N => x - t) (volC N) = volC N :=
    @MeasureTheory.Measure.map_sub_left_eq_self (Conf N) _ _ _ _ (volC N) hneg _ x
  have hemp : MeasurableEmbedding (fun t : Conf N => x - t) := measurableEmbedding_subLeft x
  rw [eLp2]
  calc eLpNorm (fun t => g (x - t)) 2 (volC N)
      = eLpNorm (g ∘ fun t : Conf N => x - t) 2 (volC N) := rfl
    _ = eLpNorm g 2 (Measure.map (fun t : Conf N => x - t) (volC N)) :=
        (MeasurableEmbedding.eLpNorm_map_measure (μ := volC N) (p := 2)
          (f := fun t : Conf N => x - t) (g := g) hemp).symm
    _ = eLpNorm g 2 (volC N) := by rw [hmap]

theorem convC_isL2_bdd_lip {N : ℕ} {f ρ : Work.BoseSym.Conf N → ℝ} {B Λ : ℝ}
    (hf : Work.BoseSym.Smooth1 f) (hfs : HasCompactSupport f)
    (hρ : Work.BoseSym.Smooth ρ) (hρs : HasCompactSupport ρ)
    (hB : 0 ≤ B) (hΛ : 0 ≤ Λ)
    (hbnd : (Work.BoseSym.eLp2 N f).toReal * (Work.BoseSym.eLp2 N ρ).toReal ≤ B)
    (hlip : (Work.BoseSym.gradNorm N f).toReal * (Work.BoseSym.eLp2 N ρ).toReal ≤ Λ) :
    Work.BoseSym.IsL2 N (Work.BoseSym.convC N f ρ) ∧
      (∀ x, |Work.BoseSym.convC N f ρ x| ≤ B) ∧
      Work.BoseSym.LipsReal Λ (Work.BoseSym.convC N f ρ) := by
  haveI hneg : (volC N).IsNegInvariant := Pi.isNegInvariant_volume
  have hli : LocallyIntegrable ρ (volC N) := hρ.continuous.locallyIntegrable
  -- finiteness of the two `L²` seminorms
  have hf_lt : eLp2 N f < ⊤ := by
    have h : MemLp f 2 (volC N) := hf.continuous.memLp_of_hasCompactSupport hfs
    simpa only [eLp2] using h.eLpNorm_lt_top
  have hρ_lt : eLp2 N ρ < ⊤ := by
    have h : MemLp ρ 2 (volC N) := hρ.continuous.memLp_of_hasCompactSupport hρs
    simpa only [eLp2] using h.eLpNorm_lt_top
  refine ⟨?_, ?_, ?_⟩
  · -- square integrability: continuous with compact support
    have hcont : Continuous (convC N f ρ) :=
      hfs.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hf.continuous hli
    have hcpt : HasCompactSupport (convC N f ρ) :=
      hfs.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hρs
    exact hcont.memLp_of_hasCompactSupport hcpt
  · -- the pointwise bound, by Cauchy–Schwarz
    intro x
    have hconv : convC N f ρ x = ∫ t, f t * ρ (x - t) ∂(volC N) := by
      rw [convC, MeasureTheory.convolution_def]
      simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    have hu : AEMeasurable f (volC N) := hf.continuous.aemeasurable
    have hv : AEMeasurable (fun t : Conf N => ρ (x - t)) (volC N) :=
      (hρ.continuous.comp (continuous_const.sub continuous_id)).aemeasurable
    have hCS := cs_ennreal (volC N) hu hv
    have hshift : eLpNorm (fun t : Conf N => ρ (x - t)) 2 (volC N) = eLp2 N ρ :=
      eLp2_sub_left N ρ x
    have hmain : ENNReal.ofReal |convC N f ρ x| ≤ eLp2 N f * eLp2 N ρ := by
      rw [← Real.norm_eq_abs]
      calc ENNReal.ofReal ‖convC N f ρ x‖
          = ENNReal.ofReal ‖∫ t, f t * ρ (x - t) ∂(volC N)‖ := by rw [hconv]
        _ ≤ eLpNorm f 2 (volC N) * eLpNorm (fun t : Conf N => ρ (x - t)) 2 (volC N) := hCS
        _ = eLp2 N f * eLp2 N ρ := by simp only [hshift, eLp2]
    have hne : eLp2 N f * eLp2 N ρ ≠ ⊤ := (ENNReal.mul_lt_top hf_lt hρ_lt).ne
    have h1 : |convC N f ρ x| ≤ (eLp2 N f * eLp2 N ρ).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hne).1 hmain
    rw [ENNReal.toReal_mul] at h1
    exact h1.trans hbnd
  · -- the Lipschitz bound, from the pointwise gradient bound
    have hdiff : ∀ x : Conf N, DifferentiableAt ℝ (convC N f ρ) x := fun x =>
      (hfs.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hf hli x).differentiableAt
    have hbound : ∀ x : Conf N, ‖fderiv ℝ (convC N f ρ) x‖ ≤ Λ := fun x =>
      (conv_fderiv_le hf hfs hρ hρs x).trans hlip
    intro x y
    have hMVT := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hdiff x)
      (fun x _ => hbound x) convex_univ (Set.mem_univ x) (Set.mem_univ y)
    have hMVT' : ‖convC N f ρ x - convC N f ρ y‖ ≤ Λ * ‖y - x‖ := by
      rw [norm_sub_rev]
      exact hMVT
    calc |convC N f ρ x - convC N f ρ y| = ‖convC N f ρ x - convC N f ρ y‖ := by
          rw [Real.norm_eq_abs]
      _ ≤ Λ * ‖y - x‖ := hMVT'
      _ = Λ * dist x y := by rw [dist_eq_norm, norm_sub_rev]

end

end Work.BoseSym.Mollify
