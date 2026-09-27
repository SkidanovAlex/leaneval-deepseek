import Mathlib
import Submission.Work.KT.D2.CircleDegreeDefs
import Submission.Work.KT.D2.stdLoop_lift
import Submission.Work.KT.D2.lift_shift

namespace Work.KT.D2

noncomputable section

/-- If `G : I → ℂ` is any continuous lift of the loop `t ↦ f (e^{2πit})` through the exponential
covering, then `G 1 - G 0 = deg f · W`: this is the defining property of the winding number. -/
theorem deg_mul_W (f : C(S1, ℂˣ)) (G : C(unitInterval, ℂ))
    (hG : ∀ t, Complex.exp (G t) = (f (stdLoop t) : ℂ)) : G 1 - G 0 = deg f * W := by
  obtain ⟨m, hm⟩ := lift_shift f G hG
  rw [hm 1, hm 0, canLift_zero, deg_spec]
  ring

/-- **The winding number (degree) of a loop in `ℂˣ`.**  There is a function `deg` from continuous
loops `S¹ = Metric.sphere (0 : ℂ) 1 → ℂˣ` to `ℤ` such that

* `deg f = 0` exactly when `f` admits a continuous logarithm (`∃ F, exp ∘ F = f`), which by
  `Work.KT.Dim2.circle_log_facts` is equivalent to `f` being null-homotopic;
* `deg` is additive under pointwise multiplication;
* the constant loop has degree `0`;
* the identity loop `z ↦ z` has degree `1`.

Route: use the covering map `Complex.isCoveringMap_exp` (`exp : ℂ → ℂˣ`).  Parametrise `S¹` by
`t ↦ exp (2πit)` (`t ∈ [0,1]`), lift the resulting path `t ↦ f (exp (2πit))` through `exp` to a
path `G : I → ℂ` starting at `0`; then `exp (G 1) = exp (G 0)` so `G 1 ∈ 2πi ℤ`, and
`deg f := G 1 / (2πi)`.  Additivity follows from lifting sums, and `deg f = 0 ↔ ∃ log` from the
uniqueness of lifts; `zpowLogZero` in `Work.KT.Dim2.circle_log_facts` shows that the identity loop
has no logarithm, so its degree is a nonzero integer, and the explicit lift `t ↦ 2πit` of the
identity loop pins it to `1`. -/
theorem circle_degree :
    ∃ deg : C(Metric.sphere (0 : ℂ) 1, ℂˣ) → ℤ,
      (∀ f : C(Metric.sphere (0 : ℂ) 1, ℂˣ),
        (deg f = 0 ↔ ∃ F : C(Metric.sphere (0 : ℂ) 1, ℂ),
          ∀ z, Complex.exp (F z) = (f z : ℂ))) ∧
      (∀ f g : C(Metric.sphere (0 : ℂ) 1, ℂˣ), deg (f * g) = deg f + deg g) ∧
      deg 1 = 0 ∧
      (∃ f : C(Metric.sphere (0 : ℂ) 1, ℂˣ), deg f = 1 ∧
        ∀ z : Metric.sphere (0 : ℂ) 1, ((f z : ℂˣ) : ℂ) = (z : ℂ)) := by
  refine ⟨deg, ?_, ?_, ?_, ?_⟩
  · -- `deg f = 0` iff `f` has a continuous logarithm
    intro f
    constructor
    · -- a lift that closes up descends to a logarithm on the circle
      intro hf
      have h01 : canLift f 0 = canLift f 1 := by
        rw [canLift_zero, deg_spec, hf]
        simp
      obtain ⟨F, hF⟩ := stdLoop_lift.2 (canLift f) h01
      refine ⟨F, fun z => ?_⟩
      obtain ⟨t, ht⟩ := stdLoop_lift.1.1 z
      have hcomp : F z = canLift f t := by
        rw [← ht, ← ContinuousMap.comp_apply, hF]
      rw [hcomp, ← expSub_coe, canLift_spec, loopOf_apply, ht]
    · -- a logarithm is a lift whose endpoints agree, hence has degree `0`
      rintro ⟨F, hF⟩
      have hG : ∀ t, Complex.exp ((F.comp stdLoop) t) = (f (stdLoop t) : ℂ) :=
        fun t => hF (stdLoop t)
      have h := deg_mul_W f (F.comp stdLoop) hG
      have hz : (F.comp stdLoop) 1 = (F.comp stdLoop) 0 := by
        simp only [ContinuousMap.comp_apply]
        rw [stdLoop_zero_eq_one]
      have h2 : deg f * W = 0 := by
        rw [← h, hz, sub_self]
      have hc : ((deg f : ℤ) : ℂ) = 0 := by
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact h3
        · exact absurd h3 W_ne_zero
      exact Int.cast_eq_zero.mp hc
  · -- additivity: the sum of the two lifts lifts the product
    intro f g
    have hG : ∀ t, Complex.exp (((canLift f) + (canLift g)) t) = ((f * g) (stdLoop t) : ℂ) := by
      intro t
      calc Complex.exp (((canLift f) + (canLift g)) t)
          = Complex.exp (canLift f t) * Complex.exp (canLift g t) := by
            rw [ContinuousMap.add_apply, Complex.exp_add]
        _ = ((loopOf f t : nzC) : ℂ) * ((loopOf g t : nzC) : ℂ) := by
            simp only [← expSub_coe, canLift_spec]
        _ = (f (stdLoop t) : ℂ) * (g (stdLoop t) : ℂ) := by rw [loopOf_apply, loopOf_apply]
        _ = (((f (stdLoop t)) * (g (stdLoop t)) : ℂˣ) : ℂ) := by rw [Units.val_mul]
        _ = (((f * g) (stdLoop t) : ℂˣ) : ℂ) := by rw [ContinuousMap.mul_apply]
    have h := deg_mul_W (f * g) ((canLift f) + (canLift g)) hG
    have h2 : ((canLift f) + (canLift g)) 1 - ((canLift f) + (canLift g)) 0
        = ((deg f : ℂ) + (deg g : ℂ)) * W := by
      rw [ContinuousMap.add_apply, ContinuousMap.add_apply, canLift_zero, deg_spec,
        canLift_zero, deg_spec]
      ring
    rw [h2] at h
    have hcw : ((deg f : ℂ) + (deg g : ℂ)) = ((deg (f * g) : ℤ) : ℂ) :=
      mul_right_cancel₀ W_ne_zero h
    exact_mod_cast hcw.symm
  · -- the constant loop: the constant lift `0` shows the degree vanishes
    have hG : ∀ t, Complex.exp ((0 : C(unitInterval, ℂ)) t)
        = ((1 : C(Metric.sphere (0 : ℂ) 1, ℂˣ)) (stdLoop t) : ℂ) := by
      intro t
      simp
    have h := deg_mul_W (1 : C(Metric.sphere (0 : ℂ) 1, ℂˣ)) (0 : C(unitInterval, ℂ)) hG
    have h2 : deg (1 : C(Metric.sphere (0 : ℂ) 1, ℂˣ)) * W = 0 := by
      rw [← h]
      simp
    have hc : ((deg (1 : C(Metric.sphere (0 : ℂ) 1, ℂˣ)) : ℤ) : ℂ) = 0 := by
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact h3
      · exact absurd h3 W_ne_zero
    exact Int.cast_eq_zero.mp hc
  · -- the identity loop `z ↦ z` has degree `1`, with the explicit lift `t ↦ 2πit`
    let f : C(Metric.sphere (0 : ℂ) 1, ℂˣ) :=
      ⟨fun z => Units.mk0 (z : ℂ) (S1_coe_ne_zero z),
        Units.continuous_iff.mpr ⟨continuous_subtype_val, by
          simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
          exact continuous_subtype_val.inv₀ (fun z => S1_coe_ne_zero z)⟩⟩
    refine ⟨f, ?_, ?_⟩
    · let G : C(unitInterval, ℂ) := ⟨fun t => ((t : ℝ) : ℂ) * W, by fun_prop⟩
      have hG : ∀ t, Complex.exp (G t) = (f (stdLoop t) : ℂ) := by
        intro t
        change Complex.exp (G t) = ((stdLoop t : S1) : ℂ)
        rw [show G t = ((t : ℝ) : ℂ) * W from rfl, stdLoop_apply_W]
      have h := deg_mul_W f G hG
      have hG1 : G 1 = W := by
        show (((1 : unitInterval) : ℝ) : ℂ) * W = W
        simp
      have hG0 : G 0 = 0 := by
        show (((0 : unitInterval) : ℝ) : ℂ) * W = 0
        simp
      rw [hG1, hG0, sub_zero] at h
      have hc : ((deg f : ℤ) : ℂ) = 1 := by
        refine mul_right_cancel₀ W_ne_zero ?_
        rw [one_mul, ← h]
      exact_mod_cast hc
    · intro z
      rfl

end

end Work.KT.D2
