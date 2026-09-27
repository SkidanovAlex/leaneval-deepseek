import Mathlib

open scoped unitInterval

namespace Work.KT.Dim2

/-- A map `f : S¹ → ℂˣ` homotopic to the constant `1` lifts through the exponential covering
`ℂ → ℂˣ`, i.e. admits a continuous logarithm. -/
theorem nullhomotopic_log (f : C(Metric.sphere (0 : ℂ) 1, ℂˣ))
    (h : ContinuousMap.Homotopic f (ContinuousMap.const _ 1)) :
    ∃ F : C(Metric.sphere (0 : ℂ) 1, ℂ), ∀ z, Complex.exp (F z) = (f z : ℂ) := by
  open ContinuousMap in
  -- Work with the covering map `exp : ℂ → {z : ℂ // z ≠ 0}`.
  let X := {z : ℂ // z ≠ 0}
  let p : ℂ → X := fun z => ⟨Complex.exp z, Complex.exp_ne_zero z⟩
  have hp : IsCoveringMap p := Complex.isCoveringMap_exp
  -- Transport `ℂˣ` to `X = ℂ \ {0}` along the homeomorphism of units with the nonzero elements.
  let e : C(ℂˣ, X) :=
    ⟨unitsHomeomorphNeZero (G₀ := ℂ), (unitsHomeomorphNeZero (G₀ := ℂ)).continuous_toFun⟩
  have he : ∀ u : ℂˣ, ((e u : X) : ℂ) = (u : ℂ) := fun u => rfl
  -- Reverse the given homotopy so that the *constant* map is lifted at `t = 0`, then lift the
  -- whole homotopy through the covering map `exp` starting from the lift `0` of `1`.
  let H : ContinuousMap.Homotopy (ContinuousMap.const (Metric.sphere (0 : ℂ) 1) 1) f := h.symm.some
  let HX : C(I × Metric.sphere (0 : ℂ) 1, X) := e.comp H.toContinuousMap
  have H_0 : ∀ a, HX (0, a) = p 0 := by
    intro a
    have hz : HX (0, a) = e 1 := by
      simp only [HX, ContinuousMap.comp_apply, Homotopy.coe_toContinuousMap]
      exact congrArg e (H.map_zero_left a)
    rw [hz]
    refine Subtype.ext ?_
    rw [he 1]
    simp [p, Complex.exp_zero]
  let Htil : C(I × Metric.sphere (0 : ℂ) 1, ℂ) :=
    hp.liftHomotopy HX (ContinuousMap.const _ 0) H_0
  have Htil_lifts : p ∘ Htil = HX := hp.liftHomotopy_lifts HX (ContinuousMap.const _ 0) H_0
  -- The desired logarithm is the end slice `a ↦ Htil (1, a)` of the lifted homotopy.
  refine ⟨Htil.comp (ContinuousMap.prodMk (ContinuousMap.const _ (1 : I)) (ContinuousMap.id _)), ?_⟩
  intro z
  have h1 : HX (1, z) = e (f z) := by
    simp only [HX, ContinuousMap.comp_apply, Homotopy.coe_toContinuousMap]
    exact congrArg e (H.map_one_left z)
  have key : p (Htil (1, z)) = e (f z) := by
    rw [← h1]; exact congr_fun Htil_lifts (1, z)
  have key2 : Complex.exp (Htil (1, z)) = (f z : ℂ) := by
    rw [← he (f z)]
    exact congrArg Subtype.val key
  simpa only [ContinuousMap.comp_apply, ContinuousMap.prod_eval, ContinuousMap.const_apply,
    ContinuousMap.id_apply] using key2

end Work.KT.Dim2
