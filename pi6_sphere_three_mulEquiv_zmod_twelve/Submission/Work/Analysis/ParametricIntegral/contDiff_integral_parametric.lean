import Mathlib

namespace Work.Analysis.ParametricIntegral

open scoped ContDiff Interval Topology
open MeasureTheory Filter TopologicalSpace

noncomputable section

/-- A continuous function on `ℝ × E` is bounded, uniformly in the first variable ranging over a
compact interval, on a neighbourhood of any point `x` of `E`.  This is the domination input needed
to differentiate an interval integral with respect to a parameter. -/
private lemma exists_bound_fderiv {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {h : ℝ × E → F} (hh : ContDiff ℝ 1 h) (a b : ℝ)
    (x : E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ v : Set E, v ∈ 𝓝 x ∧
      ∀ t ∈ Ι a b, ∀ y ∈ v, ‖(fderiv ℝ h (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ E)‖ ≤ C := by
  have hcont : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  obtain ⟨D, hD⟩ := (isCompact_uIcc.prod isCompact_singleton :
      IsCompact (Set.uIcc a b ×ˢ ({x} : Set E))).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨|D| + 1, by positivity, ?_⟩
  have hnopen : IsOpen {p : ℝ × E | ‖fderiv ℝ h p‖ < |D| + 1} :=
    isOpen_lt hcont.norm continuous_const
  have hKsub : (Set.uIcc a b ×ˢ ({x} : Set E)) ⊆ {p : ℝ × E | ‖fderiv ℝ h p‖ < |D| + 1} := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    show ‖fderiv ℝ h (t, y)‖ < |D| + 1
    have h1 := hD (t, y) ⟨ht, hy⟩
    have h2 : D ≤ |D| := le_abs_self D
    linarith
  obtain ⟨u, v, -, hvopen, hu, hxv, huv⟩ :=
    generalized_tube_lemma isCompact_uIcc isCompact_singleton hnopen hKsub
  refine ⟨v, hvopen.mem_nhds (hxv (Set.mem_singleton x)), ?_⟩
  intro t ht y hy
  have hp : ‖fderiv ℝ h (t, y)‖ < |D| + 1 := huv ⟨hu (Set.uIoc_subset_uIcc ht), hy⟩
  have h1 : ‖(fderiv ℝ h (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ E)‖ ≤ ‖fderiv ℝ h (t, y)‖ := by
    calc ‖(fderiv ℝ h (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ E)‖
        ≤ ‖fderiv ℝ h (t, y)‖ * ‖(ContinuousLinearMap.inr ℝ ℝ E)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ h (t, y)‖ * 1 := by
          exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inr_le_one ℝ ℝ E) (norm_nonneg _)
      _ = ‖fderiv ℝ h (t, y)‖ := mul_one _
  exact h1.trans (le_of_lt hp)

/-- Differentiation under the interval integral sign with respect to a parameter `x : E`: the
derivative of `x ↦ ∫ t in a..b, h (t, x)` is the interval integral of the partial derivative of `h`
with respect to `x`. -/
private lemma hasFDerivAt_integral_parametric {E : Type*} {F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {h : ℝ × E → F}
    (hh : ContDiff ℝ 1 h) (a b : ℝ) (x : E) :
    HasFDerivAt (fun y : E => ∫ t in a..b, h (t, y))
      (∫ t in a..b, (fderiv ℝ h (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) x := by
  obtain ⟨C, hC, v, hv, hbound⟩ := exists_bound_fderiv hh a b x
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume) (s := v) (bound := fun _ => C)
    (F := fun (y : E) (t : ℝ) => h (t, y))
    (F' := fun (y : E) (t : ℝ) => (fderiv ℝ h (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ E))
    hv ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun y =>
      (hh.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · exact (hh.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
  · exact ((hh.continuous_fderiv one_ne_zero).comp
      (continuous_id.prodMk continuous_const)).clm_comp continuous_const |>.aestronglyMeasurable
  · exact Eventually.of_forall fun t ht y hy => hbound t ht y hy
  · exact continuous_const.intervalIntegrable a b
  · exact Eventually.of_forall fun t ht y hy =>
      (hh.differentiable_one.differentiableAt.hasFDerivAt).comp y (hasFDerivAt_prodMk_right t y)

/-- The interval integral of a jointly continuous function on `ℝ × E` is continuous, as a function
of the parameter. -/
private lemma continuous_integral_parametric {E : Type*} {F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {h : ℝ × E → F}
    (hh : Continuous h) (a b : ℝ) :
    Continuous (fun x : E => ∫ t in a..b, h (t, x)) := by
  have hun : Continuous (Function.uncurry (fun (x : E) (t : ℝ) => h (t, x))) :=
    hh.comp (continuous_snd.prodMk continuous_fst)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hun a b

/-- `C^n` version of the main induction: for every `n`, an interval integral of a `C^n` function of
`(t, x)` is `C^n` in `x`.  The codomain is placed in the universe `max u v` so that it is stable
under passing to continuous linear maps, which is what the induction step does. -/
private theorem aux.{u, v} {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∀ (n : ℕ) (a b : ℝ) (G : Type (max u v)) [NormedAddCommGroup G] [NormedSpace ℝ G]
      [CompleteSpace G] (h : ℝ × E → G), ContDiff ℝ (n : ℕ∞ω) h →
        ContDiff ℝ (n : ℕ∞ω) (fun x : E => ∫ t in a..b, h (t, x)) := by
  intro n
  induction n with
  | zero =>
    intro a b G _ _ _ h hh
    rw [Nat.cast_zero] at hh ⊢
    rw [contDiff_zero] at hh ⊢
    exact continuous_integral_parametric hh a b
  | succ m ih =>
    intro a b G _ _ _ h hh
    rw [Nat.cast_succ] at hh ⊢
    rw [contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun x => ∫ t in a..b, (fderiv ℝ h (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E), ?_, ?_⟩
    · exact ih a b (E →L[ℝ] G)
        (fun p : ℝ × E => (fderiv ℝ h p).comp (ContinuousLinearMap.inr ℝ ℝ E))
        ((hh.fderiv_right le_rfl).clm_comp contDiff_const)
    · intro x
      exact hasFDerivAt_integral_parametric (hh.of_le (by simp)) a b x

/-- The main statement for a fixed pair of universes: the codomain is lifted to `max u v` so that
the `C^n` induction of `aux` applies.  The lifting is undone using the continuous linear equivalence
between `ULift F` and `F`. -/
private theorem main_aux.{u, v} {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {h : ℝ × E → F} (hh : ContDiff ℝ ∞ h) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x : E => ∫ t in a..b, h (t, x)) := by
  let e : ULift.{max u v, v} F ≃L[ℝ] F := ContinuousLinearEquiv.ulift
  have hlift : ContDiff ℝ ∞ (fun x : E => ∫ t in a..b, e.symm (h (t, x))) := by
    rw [contDiff_infty]
    intro n
    exact aux n a b (ULift.{max u v, v} F) (fun p : ℝ × E => e.symm (h p))
      ((ContinuousLinearEquiv.contDiff e.symm).comp (contDiff_infty.mp hh n))
  have h2 : ContDiff ℝ ∞ (fun x : E => e (∫ t in a..b, e.symm (h (t, x)))) :=
    (ContinuousLinearEquiv.contDiff e).comp hlift
  have heq : (fun x : E => e (∫ t in a..b, e.symm (h (t, x)))) =
      (fun x : E => ∫ t in a..b, h (t, x)) := by
    funext x
    change (e : ULift.{max u v, v} F →L[ℝ] F)
      (∫ t in a..b, e.symm (h (t, x))) = ∫ t in a..b, h (t, x)
    have hf : IntervalIntegrable (fun t : ℝ => e.symm (h (t, x))) volume a b :=
      ((e.symm : F →L[ℝ] ULift.{max u v, v} F).continuous.comp
        (hh.continuous.comp (continuous_id.prodMk continuous_const))).intervalIntegrable a b
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm
      (L := (e : ULift.{max u v, v} F →L[ℝ] F)) hf]
    simp [ContinuousLinearEquiv.apply_symm_apply]
  rwa [heq] at h2

open scoped ContDiff Interval in
theorem contDiff_integral_parametric {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {h : ℝ × E → F} (hh : ContDiff ℝ ∞ h) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x : E => ∫ t in a..b, h (t, x)) :=
  main_aux hh a b

end

end Work.Analysis.ParametricIntegral
