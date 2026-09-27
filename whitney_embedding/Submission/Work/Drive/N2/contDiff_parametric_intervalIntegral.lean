import Mathlib

namespace Work.Drive.N2

open MeasureTheory Filter Set Function
open scoped Topology Interval

universe uE uF u

/-- Auxiliary version of the parametric interval-integral smoothness statement, where the
codomain is allowed to live in the universe `max uE u` (so that the induction on the number of
derivatives can be carried out: the derivative of a function `E × ℝ → F` takes values in
`E →L[ℝ] F`, which lives in the universe `max uE uF`). -/
theorem contDiff_parametric_intervalIntegral_aux {E : Type uE} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] {a b : ℝ} :
    ∀ (n : ℕ) (F : Type (max uE u)) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (f : E × ℝ → F), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f →
        ContDiff ℝ ((n : ℕ) : WithTop ℕ∞) (fun x : E => ∫ t in a..b, f (x, t)) := by
  intro n
  induction n with
  | zero =>
    intro F _ _ _ f hf
    rw [show (((0 : ℕ) : WithTop ℕ∞)) = 0 from rfl, contDiff_zero]
    have hcont : Continuous (fun x : E => ∫ t in a..b, f (x, t)) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun x t => f (x, t)) hf.continuous a b
    exact hcont
  | succ n ih =>
    intro F _ _ _ f hf
    have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) :=
      (contDiff_infty_iff_fderiv.mp hf).2
    have hdf : Differentiable ℝ f := (contDiff_infty_iff_fderiv.mp hf).1
    let Φ : E × ℝ → (E →L[ℝ] F) := fun p => (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ := by
      have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : E × ℝ => fderiv ℝ f p) := hfd
      have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun _ : E × ℝ => ContinuousLinearMap.inl ℝ E ℝ) := contDiff_const
      exact h1.clm_comp h2
    rw [show (((Nat.succ n : ℕ) : WithTop ℕ∞)) = ((n : ℕ) : WithTop ℕ∞) + 1 from by simp]
    rw [contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun x : E => ∫ t in a..b, Φ (x, t), ?_, ?_⟩
    · exact ih (E →L[ℝ] F) Φ hΦ
    · intro x
      obtain ⟨C, hC⟩ :=
        ((isCompact_closedBall x 1).prod isCompact_uIcc).exists_bound_of_continuousOn
          hΦ.continuous.continuousOn
      refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F := fun y t => f (y, t)) (F' := fun y t => Φ (y, t)) (x₀ := x)
        (s := Metric.closedBall x 1) (bound := fun _ => C) (μ := volume)
        (Metric.closedBall_mem_nhds x one_pos) ?_ ?_ ?_ ?_ ?_ ?_
      · exact Filter.Eventually.of_forall fun y =>
          (hf.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      · exact (hf.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
      · exact (hΦ.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun t ht y hy => hC (y, t) ⟨hy, uIoc_subset_uIcc ht⟩
      · exact intervalIntegrable_const
      · exact Filter.Eventually.of_forall fun t _ht y _hy =>
          (hdf (y, t)).hasFDerivAt.comp y (hasFDerivAt_prodMk_left y t)

/-- The parametric interval integral of a `C^∞` function is `C^∞`, version with named
universes for the two spaces (used to transfer the result to arbitrary universes via `ULift`). -/
theorem contDiff_parametric_intervalIntegral_lift {E : Type uE} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {f : E × ℝ → F} {a b : ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : E => ∫ t in a..b, f (x, t)) := by
  have hf' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : E × ℝ => ULift.up (f p)) :=
    ((ContinuousLinearEquiv.ulift (R₁ := ℝ) (M₁ := F) : ULift F ≃L[ℝ] F).symm.contDiff).comp hf
  have hg' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : E => ∫ t in a..b, ULift.up (f (x, t))) :=
    contDiff_infty.mpr fun n =>
      contDiff_parametric_intervalIntegral_aux (E := E) n (ULift.{uE, uF} F)
        (fun p : E × ℝ => ULift.up (f p)) hf'
  have hfinal : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : E => (ContinuousLinearEquiv.ulift (R₁ := ℝ) (M₁ := F) : ULift F ≃L[ℝ] F)
        (∫ t in a..b, ULift.up (f (x, t)))) :=
    (ContinuousLinearEquiv.contDiff _).comp hg'
  have hcast : (fun x : E => (ContinuousLinearEquiv.ulift (R₁ := ℝ) (M₁ := F) : ULift F ≃L[ℝ] F)
        (∫ t in a..b, ULift.up (f (x, t))))
      = (fun x : E => ∫ t in a..b, f (x, t)) := by
    funext x
    have hint : IntervalIntegrable (fun t : ℝ => ULift.up (f (x, t))) volume a b :=
      (hf'.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
    have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm
      (L := (ContinuousLinearEquiv.ulift (R₁ := ℝ) (M₁ := F) : ULift F →L[ℝ] F)) hint
    change (ContinuousLinearEquiv.ulift (R₁ := ℝ) (M₁ := F) : ULift F →L[ℝ] F)
      (∫ t in a..b, ULift.up (f (x, t))) = ∫ t in a..b, f (x, t)
    rw [← hcomm]
    exact intervalIntegral.integral_congr fun t _ht => rfl
  rw [hcast] at hfinal
  exact hfinal

/-- The parametric interval integral of a `C^∞` function is `C^∞`. -/
theorem contDiff_parametric_intervalIntegral
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E × ℝ → F} {a b : ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : E => ∫ t in a..b, f (x, t)) :=
  contDiff_parametric_intervalIntegral_lift hf

end Work.Drive.N2
