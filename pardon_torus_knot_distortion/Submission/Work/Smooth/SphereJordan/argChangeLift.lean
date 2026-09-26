import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs

/-!
# The continuous argument lift of a nowhere vanishing path in `ℂ`

`Complex.exp : ℂ → ℂ` is a covering map onto `ℂ \ {0}`
(`Complex.isCoveringMap_exp`, in the form `ℂ → {z : ℂ // z ≠ 0}`), so a continuous nowhere
vanishing path `c : [0,1] → ℂ` lifts to a continuous path `Λ : [0,1] → ℂ` with `exp ∘ Λ = c`.
The lift is unique up to adding a constant in `2πi ℤ`; consequently the *increment*
`Λ 1 - Λ 0` is the same for every lift, which is the content of the second clause.

The proof of the uniqueness of the increment uses the covering-space form of the
uniqueness of lifts (`IsCoveringMap.const_of_comp`): if `Λ'` is any lift, then
`exp (Λ' t - Λ t) = c t / c t = 1` for all `t`, so `t ↦ Λ' t - Λ t` is continuous into the
fibre of `exp` over `1`; as `[0,1]` is preconnected, this map is constant.
-/

namespace Work.Smooth.SphereJordan

/-- **Lift of the argument.**  A continuous nowhere vanishing path `c : [0,1] → ℂ` has a
continuous logarithm `Λ`, and the increment `Λ 1 - Λ 0` is independent of the lift. -/
theorem argChangeLift (c : C(unitInterval, ℂ)) (hc : ∀ t : unitInterval, c t ≠ 0) :
    ∃ Λ : C(unitInterval, ℂ), (∀ t : unitInterval, Complex.exp (Λ t) = c t) ∧
      (∀ t : unitInterval, Complex.exp (Λ t) ≠ 0) ∧
      (∀ Λ' : C(unitInterval, ℂ), (∀ t : unitInterval, Complex.exp (Λ' t) = c t) →
        Λ' 1 - Λ' 0 = Λ 1 - Λ 0) := by
  -- `c`, viewed as a path in the covering space `ℂ \ {0}` of `Complex.exp`.
  let γ : C(unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun t => ⟨c t, hc t⟩, c.continuous.subtype_mk hc⟩
  -- a lift of the starting point: `log (c 0)`.
  have hγ0 : γ 0 = (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0}))
      (Complex.log (c 0)) := by
    apply Subtype.ext
    simp [γ, Complex.exp_log (hc 0)]
  -- path lifting in the covering space.
  obtain ⟨Γ, hΓ, -⟩ := Complex.isCoveringMap_exp.exists_path_lifts γ (Complex.log (c 0)) hγ0
  have hlift : ∀ t : unitInterval, Complex.exp (Γ t) = c t := by
    intro t
    have := congrArg Subtype.val (congrFun hΓ t)
    simpa [γ] using this
  refine ⟨Γ, hlift, fun t => Complex.exp_ne_zero _, ?_⟩
  -- uniqueness of the increment.
  intro Λ' hΛ'
  have key : ∀ a a' : unitInterval,
      (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0}))
        (Λ' a - Γ a) =
      (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0}))
        (Λ' a' - Γ a') := by
    intro a a'
    apply Subtype.ext
    show Complex.exp (Λ' a - Γ a) = Complex.exp (Λ' a' - Γ a')
    rw [Complex.exp_sub, Complex.exp_sub, hΛ' a, hΛ' a', hlift a, hlift a',
      div_self (hc a), div_self (hc a')]
  have hconst := Complex.isCoveringMap_exp.const_of_comp
    (g := fun t : unitInterval => Λ' t - Γ t) (by fun_prop) key 0 1
  linear_combination -hconst

end Work.Smooth.SphereJordan
