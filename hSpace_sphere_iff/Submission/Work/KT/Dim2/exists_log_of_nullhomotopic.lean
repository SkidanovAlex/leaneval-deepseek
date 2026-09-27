import Mathlib

open scoped unitInterval

namespace Work.KT.Dim2

/-- A continuous map `f : X → ℂˣ` (the units of `ℂ`) which is null-homotopic, i.e. homotopic to a
constant map, admits a continuous logarithm: `exp : ℂ → ℂˣ` is a covering map, and the homotopy
lifting property lifts the null-homotopy of `f` starting from a logarithm of the constant value;
the final slice of the lift is a logarithm of `f`.

Route (this is exactly the proof of `Work.KT.Dim2.nullhomotopic_log`, with the circle
`Metric.sphere (0 : ℂ) 1` replaced by an arbitrary space `X`): let `X' := {z : ℂ // z ≠ 0}` and
`p : ℂ → X'` be `fun z => ⟨Complex.exp z, Complex.exp_ne_zero z⟩`, with
`hp : IsCoveringMap p := Complex.isCoveringMap_exp`.  Transport along
`unitsHomeomorphNeZero : ℂˣ ≃ₜ X'`, take the `y` with `h : f.Homotopic (const y)`, reverse it and
lift `HX := e.comp H.toContinuousMap` with `IsCoveringMap.liftHomotopy` from the constant lift
`Fun.const (Complex.log y)`. -/
theorem exists_log_of_nullhomotopic {X : Type} [TopologicalSpace X] (f : C(X, ℂˣ))
    (h : ContinuousMap.Nullhomotopic f) :
    ∃ F : C(X, ℂ), ∀ x, Complex.exp (F x) = (f x : ℂ) := by
  obtain ⟨y, hy⟩ := h
  open ContinuousMap in
  -- Work with the covering map `exp : ℂ → {z : ℂ // z ≠ 0}`.
  let X' := {z : ℂ // z ≠ 0}
  let p : ℂ → X' := fun z => ⟨Complex.exp z, Complex.exp_ne_zero z⟩
  have hp : IsCoveringMap p := Complex.isCoveringMap_exp
  -- Transport `ℂˣ` to `X' = ℂ \ {0}` along the homeomorphism of units with the nonzero elements.
  let e : C(ℂˣ, X') :=
    ⟨unitsHomeomorphNeZero (G₀ := ℂ), (unitsHomeomorphNeZero (G₀ := ℂ)).continuous_toFun⟩
  have he : ∀ u : ℂˣ, ((e u : X') : ℂ) = (u : ℂ) := fun u => rfl
  -- Reverse the given homotopy so that the *constant* map is lifted at `t = 0`, then lift the
  -- whole homotopy through the covering map `exp` starting from a logarithm of the constant value.
  let H : ContinuousMap.Homotopy (ContinuousMap.const X y) f := hy.symm.some
  let HX : C(I × X, X') := e.comp H.toContinuousMap
  have H_0 : ∀ a, HX (0, a) = p (Complex.log y) := by
    intro a
    have hz : HX (0, a) = e y := by
      simp only [HX, ContinuousMap.comp_apply, Homotopy.coe_toContinuousMap]
      exact congrArg e (H.map_zero_left a)
    rw [hz]
    refine Subtype.ext ?_
    rw [he y]
    exact (Complex.exp_log (Units.ne_zero y)).symm
  let Htil : C(I × X, ℂ) :=
    hp.liftHomotopy HX (ContinuousMap.const _ (Complex.log y)) H_0
  have Htil_lifts : p ∘ Htil = HX :=
    hp.liftHomotopy_lifts HX (ContinuousMap.const _ (Complex.log y)) H_0
  -- The desired logarithm is the end slice `a ↦ Htil (1, a)` of the lifted homotopy.
  refine ⟨Htil.comp (ContinuousMap.prodMk (ContinuousMap.const _ (1 : I)) (ContinuousMap.id _)), ?_⟩
  intro x
  have h1 : HX (1, x) = e (f x) := by
    simp only [HX, ContinuousMap.comp_apply, Homotopy.coe_toContinuousMap]
    exact congrArg e (H.map_one_left x)
  have key : p (Htil (1, x)) = e (f x) := by
    rw [← h1]; exact congr_fun Htil_lifts (1, x)
  have key2 : Complex.exp (Htil (1, x)) = (f x : ℂ) := by
    rw [← he (f x)]
    exact congrArg Subtype.val key
  simpa only [ContinuousMap.comp_apply, ContinuousMap.prod_eval, ContinuousMap.const_apply,
    ContinuousMap.id_apply] using key2

end Work.KT.Dim2
