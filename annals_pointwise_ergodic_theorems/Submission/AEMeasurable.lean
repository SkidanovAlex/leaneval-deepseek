import ChallengeDeps
import Mathlib.Tactic
import Submission.Half
import Submission.Reductions

/-!
# Almost-everywhere measurability of the averages and of the variational norm

`MemLp f p μ` only provides `AEStronglyMeasurable f μ`, and the `Lᵖ` Minkowski inequality for
countable sums requires `AEMeasurable` hypotheses.  We therefore record the `AEMeasurable`
versions of the measurability statements of `Submission.Basic` and `Submission.Variational`:
the averages `A` and `Ã` of a.e. measurable functions are a.e. measurable, and so is the
variational norm of a pointwise a.e. measurable sequence.
-/

set_option maxHeartbeats 1600000

namespace Submission

open _root_.PointwiseErgodicTheorems
set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {μ : Measure 𝓧} {T : 𝓧 ≃ᵐ 𝓧}

/-- Precomposition with a (quasi-)measure-preserving integer power of `T` preserves
`AEMeasurable`. -/
lemma aemeasurable_comp_zpow (hT : MeasurePreserving T μ μ) {f : 𝓧 → ℂ}
    (hf : AEMeasurable f μ) (k : ℤ) :
    AEMeasurable (fun x => f ((T ^ k : 𝓧 ≃ 𝓧) x)) μ :=
  hf.comp_quasiMeasurePreserving (quasiMeasurePreserving_zpow T hT k)

/-- The bilinear average of a.e. measurable functions is a.e. measurable. -/
lemma aemeasurable_A (hT : MeasurePreserving T μ μ) (N : ℝ≥0) (P₁ P₂ : ℤ[X]) {f g : 𝓧 → ℂ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : AEMeasurable (A T N P₁ P₂ f g) μ := by
  unfold A
  refine AEMeasurable.const_mul ?_ _
  have hfun : (fun x => ∑ n ∈ Finset.Icc 1 (Nat.floor N),
        f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x) * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x))
      = ∑ n ∈ Finset.Icc 1 (Nat.floor N),
          (fun x => f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x)
            * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x)) := by
    funext x
    rw [Finset.sum_apply]
  rw [hfun]
  exact Finset.aemeasurable_sum (Finset.Icc 1 (Nat.floor N)) (fun n _ =>
    (aemeasurable_comp_zpow hT hf (P₁.eval (n : ℤ))).mul
      (aemeasurable_comp_zpow hT hg (P₂.eval (n : ℤ))))

/-- The halved average of a.e. measurable functions is a.e. measurable. -/
lemma aemeasurable_AhalfR (hT : MeasurePreserving T μ μ) (N : ℝ≥0) (P₁ P₂ : ℤ[X])
    {f g : 𝓧 → ℂ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (AhalfR T N P₁ P₂ f g) μ := by
  unfold AhalfR Ahalf Ablock
  refine AEMeasurable.const_mul ?_ _
  have hfun : (fun x => ∑ n ∈ Finset.Ioc (Nat.floor N / 2) (Nat.floor N),
        f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x) * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x))
      = ∑ n ∈ Finset.Ioc (Nat.floor N / 2) (Nat.floor N),
          (fun x => f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x)
            * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x)) := by
    funext x
    rw [Finset.sum_apply]
  rw [hfun]
  exact Finset.aemeasurable_sum (Finset.Ioc (Nat.floor N / 2) (Nat.floor N)) (fun n _ =>
    (aemeasurable_comp_zpow hT hf (P₁.eval (n : ℤ))).mul
      (aemeasurable_comp_zpow hT hg (P₂.eval (n : ℤ))))

/-- The variational norm of a pointwise a.e. measurable sequence is a.e. measurable: it is a
supremum over the countable family of finite index selections. -/
lemma aemeasurable_variationalNorm {r : ℝ≥0} (hr : 0 < r) {u : ℕ → 𝓧 → ℂ}
    (hu : ∀ n, AEMeasurable (u n) μ) :
    AEMeasurable (fun x => variationalNorm r (fun n => u n x)) μ := by
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hfun : (fun x => variationalNorm r (fun n => u n x))
      = fun x => (⨆ n, ‖u n x‖ₑ) +
          ⨆ (J : ℕ) (w : Fin (J + 1) → ℕ) (_ : Monotone w),
            ENNReal.ofReal ‖(WithLp.toLp (r : ℝ≥0∞)
              (fun i : Fin J => u (w i.succ) x - u (w i.castSucc) x))‖ := by
    funext x
    exact variationalNorm_eq_iSup_fin r (fun n => u n x)
  rw [hfun]
  refine AEMeasurable.add (AEMeasurable.iSup (fun n => (hu n).enorm)) ?_
  refine AEMeasurable.iSup (fun J => AEMeasurable.iSup (fun w => AEMeasurable.iSup (fun _ => ?_)))
  have hterm : (fun x => ENNReal.ofReal ‖(WithLp.toLp (r : ℝ≥0∞)
      (fun i : Fin J => u (w i.succ) x - u (w i.castSucc) x))‖)
      = fun x => ENNReal.ofReal ((∑ i : Fin J,
          ‖u (w i.succ) x - u (w i.castSucc) x‖ ^ (r : ℝ)) ^ (1 / (r : ℝ))) := by
    funext x
    congr 1
    rw [PiLp.norm_eq_sum (p := (r : ℝ≥0∞)) (by rw [ENNReal.coe_toReal]; exact hrR)]
    simp [ENNReal.coe_toReal]
  rw [hterm]
  have hinner : AEMeasurable (fun x => ∑ i : Fin J,
      ‖u (w i.succ) x - u (w i.castSucc) x‖ ^ (r : ℝ)) μ := by
    have hfun2 : (fun x => ∑ i : Fin J, ‖u (w i.succ) x - u (w i.castSucc) x‖ ^ (r : ℝ))
        = ∑ i : Fin J, (fun x => ‖u (w i.succ) x - u (w i.castSucc) x‖ ^ (r : ℝ)) := by
      funext x
      rw [Finset.sum_apply]
    rw [hfun2]
    exact Finset.aemeasurable_sum (Finset.univ : Finset (Fin J)) (fun i _ =>
      (Real.continuous_rpow_const hrR.le).measurable.comp_aemeasurable
        (((hu (w i.succ)).sub (hu (w i.castSucc))).norm))
  have h1 : AEMeasurable (fun x => (∑ i : Fin J,
      ‖u (w i.succ) x - u (w i.castSucc) x‖ ^ (r : ℝ)) ^ (1 / (r : ℝ))) μ :=
    (Real.continuous_rpow_const (by positivity)).measurable.comp_aemeasurable hinner
  exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable h1

end PointwiseErgodicTheorems
end Submission
