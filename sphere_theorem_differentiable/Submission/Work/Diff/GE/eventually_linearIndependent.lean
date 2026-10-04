import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

theorem eventually_linearIndependent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    {x : M} (F : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hF : ∀ i, ContMDiffAt I I.tangent ((⊤ : ENat) : WithTop ENat)
        (fun z : M => Bundle.TotalSpace.mk' E z (F i z)) x)
    (hli : LinearIndependent ℝ (fun i => F i x)) :
    ∀ᶠ y in nhds x, LinearIndependent ℝ (fun i : Fin (Module.finrank ℝ E) => F i y) := by
  classical
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) x
  -- The coordinates of the fields in the tangent-bundle trivialization at `x`.
  let c : M → (Fin (Module.finrank ℝ E) → E) :=
    fun y i => ((trivializationAt E (TangentSpace I) x) ⟨y, F i y⟩).2
  -- Those coordinates are continuous at `x` (each field is a smooth section).
  have hcont : ContinuousAt c x := by
    show ContinuousAt (fun y : M => fun i : Fin (Module.finrank ℝ E) =>
      ((trivializationAt E (TangentSpace I) x) ⟨y, F i y⟩).2) x
    rw [continuousAt_pi]
    intro i
    show ContinuousAt (fun y : M =>
      ((trivializationAt E (TangentSpace I) x) ⟨y, F i y⟩).2) x
    rw [← FiberBundle.continuousAt_section (F := E) (E := fun y : M => TangentSpace I y)
      (s := fun y => F i y) x]
    exact (hF i).continuousAt
  -- Independence at `x`, transported to the model space by the trivialization.
  have hli_cts : LinearIndependent ℝ (fun i : Fin (Module.finrank ℝ E) =>
      (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x (F i x)) := by
    refine hli.map'
      (((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x).toLinearMap) ?_
    rw [LinearMap.ker_eq_bot]
    intro u v huv
    change (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x u
      = (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x v at huv
    have h1 := (trivializationAt E (TangentSpace I) x).symmL_continuousLinearMapAt (R := ℝ) hxbase u
    have h2 := (trivializationAt E (TangentSpace I) x).symmL_continuousLinearMapAt (R := ℝ) hxbase v
    have h := congrArg (fun w => (trivializationAt E (TangentSpace I) x).symmL ℝ x w) huv
    rw [h1, h2] at h
    exact h
  have hli_coord : LinearIndependent ℝ (c x) := by
    show LinearIndependent ℝ (fun i : Fin (Module.finrank ℝ E) =>
      ((trivializationAt E (TangentSpace I) x) ⟨x, F i x⟩).2)
    have h_eq : (fun i : Fin (Module.finrank ℝ E) =>
        (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x (F i x))
        = (fun i : Fin (Module.finrank ℝ E) =>
        ((trivializationAt E (TangentSpace I) x) ⟨x, F i x⟩).2) := by
      funext i
      exact Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ
        (trivializationAt E (TangentSpace I) x) hxbase (F i x)
    rw [← h_eq]
    exact hli_cts
  -- Linear independence is an open condition; pull it back along `c`.
  filter_upwards [hcont.eventually (LinearIndependent.eventually hli_coord),
    (trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds hxbase] with y hy hybase
  have hker : LinearMap.ker
      (((trivializationAt E (TangentSpace I) x).symmL ℝ y).toLinearMap) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro u v huv
    change (trivializationAt E (TangentSpace I) x).symmL ℝ y u
      = (trivializationAt E (TangentSpace I) x).symmL ℝ y v at huv
    have h1 := (trivializationAt E (TangentSpace I) x).continuousLinearMapAt_symmL (R := ℝ) hybase u
    have h2 := (trivializationAt E (TangentSpace I) x).continuousLinearMapAt_symmL (R := ℝ) hybase v
    have h := congrArg (fun w => (trivializationAt E (TangentSpace I) x).continuousLinearMapAt
      ℝ y w) huv
    rw [h1, h2] at h
    exact h
  have hfam : (⇑(((trivializationAt E (TangentSpace I) x).symmL ℝ y).toLinearMap)) ∘ c y
      = fun i : Fin (Module.finrank ℝ E) => F i y := by
    funext i
    show (trivializationAt E (TangentSpace I) x).symmL ℝ y
      (((trivializationAt E (TangentSpace I) x) ⟨y, F i y⟩).2) = F i y
    rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ
      (trivializationAt E (TangentSpace I) x) hybase (F i y)]
    exact (trivializationAt E (TangentSpace I) x).symmL_continuousLinearMapAt hybase (F i y)
  have h2 := hy.map'
    (((trivializationAt E (TangentSpace I) x).symmL ℝ y).toLinearMap) hker
  rwa [hfam] at h2

end Work.Diff.GE
