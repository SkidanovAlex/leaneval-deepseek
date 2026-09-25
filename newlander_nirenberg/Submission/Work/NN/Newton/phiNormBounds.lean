import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc

namespace Work.NN.Newton

/-- **Norm bounds for the near-identity map `Φ = id - v`.**

Let `v : Fin n → ℂⁿ → ℂ` be such that each `v l` is `C¹` on the open set `Ω` and has `C^{2,α}`-norm
at most `b` there.  Then on `Ω` the map `Φ(z) = (z_l - v_l z)_l` is within `b` of the identity in the
sup norm, and its differential is within `b` of the identity in operator norm.

(The `C¹` hypothesis is needed: `holderNorm` is built from `iteratedFDerivWithin`, which is `0` at
points where the function is not differentiable, so without `C¹` the second bound would fail for
`v l = |x|`.) -/
theorem phiNormBounds {n : ℕ} {α : ℝ} {v : Fin n → Work.NN.Core.Cn n → ℂ}
    {Ω : Set (Work.NN.Core.Cn n)} (hΩ : IsOpen Ω) {b : ℝ} (hb : 0 ≤ b)
    (hv : ∀ l, Work.CR.Flat.holderNorm 2 α (v l) Ω ≤ ENNReal.ofReal b)
    (hv1 : ∀ l, ContDiffOn ℝ 1 (v l) Ω) :
    (∀ z ∈ Ω, ‖(fun l => z l - v l z) - z‖ ≤ b) ∧
    (∀ z ∈ Ω, ‖fderiv ℝ (fun w : Work.NN.Core.Cn n => fun l => w l - v l w) z
        - ContinuousLinearMap.id ℝ (Work.NN.Core.Cn n)‖ ≤ b) := by
  constructor
  · -- value bound: `Φ z - z = -v z` and `‖v z‖` is the maximum of the `‖v l z‖`
    intro z hz
    have hsub : ((fun l => z l - v l z) - z : Work.NN.Core.Cn n) = fun l => - v l z := by
      funext l; simp
    rw [hsub]
    refine (pi_norm_le_iff_of_nonneg hb).mpr fun l => ?_
    have h1 : ENNReal.ofReal ‖v l z‖ ≤ ENNReal.ofReal b :=
      le_trans (Work.CR.Flat.norm_apply_le_holderNorm 2 α (v l) Ω hz) (hv l)
    have h2 : ‖v l z‖ ≤ b := (ENNReal.ofReal_le_ofReal_iff hb).mp h1
    simpa using h2
  · -- differential bound: `dΦ z - 1` is the `pi` of the maps `-d(v l) z`
    intro z hz
    have hdiff : ∀ l : Fin n, DifferentiableAt ℝ (v l) z := fun l =>
      ((hv1 l).contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by norm_num)
    -- each `‖d(v l) z‖ ≤ b`, from the order-`1` term of the Hölder norm
    have hdv : ∀ l : Fin n, ‖fderiv ℝ (v l) z‖ ≤ b := by
      intro l
      have h1 : ENNReal.ofReal ‖iteratedFDerivWithin ℝ 1 (v l) Ω z‖ ≤ ENNReal.ofReal b :=
        le_trans (le_trans (Work.CR.Flat.le_iterDerivNorm 1 (v l) Ω hz)
          (Work.CR.Flat.iterDerivNorm_le_holderNorm 2 α (v l) Ω (by norm_num))) (hv l)
      have h2 : ‖iteratedFDerivWithin ℝ 1 (v l) Ω z‖ = ‖fderivWithin ℝ (v l) Ω z‖ :=
        norm_iteratedFDerivWithin_one (v l) (hΩ.uniqueDiffWithinAt hz)
      rw [h2, fderivWithin_of_isOpen hΩ hz] at h1
      exact (ENNReal.ofReal_le_ofReal_iff hb).mp h1
    -- the derivative of `Φ`, componentwise
    have hΦfd : HasFDerivAt (fun w : Work.NN.Core.Cn n => fun l => w l - v l w)
        (ContinuousLinearMap.pi (fun l => (ContinuousLinearMap.proj l : Work.NN.Core.Cn n →L[ℝ] ℂ)
          - fderiv ℝ (v l) z)) z := by
      refine hasFDerivAt_pi'' (fun l => ?_)
      rw [ContinuousLinearMap.proj_pi]
      exact (ContinuousLinearMap.hasFDerivAt
        (ContinuousLinearMap.proj l : Work.NN.Core.Cn n →L[ℝ] ℂ)).sub (hdiff l).hasFDerivAt
    have hEqFull : fderiv ℝ (fun w : Work.NN.Core.Cn n => fun l => w l - v l w) z
        - ContinuousLinearMap.id ℝ (Work.NN.Core.Cn n)
        = ContinuousLinearMap.pi (fun l => -(fderiv ℝ (v l) z)) := by
      rw [hΦfd.fderiv]
      ext w l
      simp [ContinuousLinearMap.pi_apply]
    rw [hEqFull]
    refine ContinuousLinearMap.opNorm_le_bound _ hb fun w => ?_
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hb (norm_nonneg w))).mpr fun l => ?_
    simp only [ContinuousLinearMap.pi_apply, neg_apply, norm_neg]
    exact le_trans ((fderiv ℝ (v l) z).le_opNorm w)
      (mul_le_mul_of_nonneg_right (hdv l) (norm_nonneg w))

end Work.NN.Newton
