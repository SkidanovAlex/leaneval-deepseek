import Mathlib
import Submission.Work.RPCore.Port.ODE.SmoothFlow

/-!
# The semigroup law for a flow defined by integral curves

If `X : E → E` is `C¹` with `‖fderiv ℝ X z‖ ≤ K` for all `z` (so `X` is globally Lipschitz with
constant `K`), and `Φ : ℝ → E → E` is *any* map such that `Φ t y` is reached at time `t` by an
integral curve of `X` starting at `y`, then `Φ` satisfies the functional equation of a flow:

`Φ (s + u) y = Φ s (Φ u y)`.

The proof is uniqueness of integral curves of a globally Lipschitz autonomous field: the curve
`r ↦ Φ r y` and the chosen integral curve `γ` through `y` agree (both solve `γ' = X ∘ γ` and start
at `y`), and the time translate `r ↦ γ (r + u)` is an integral curve starting at `Φ u y`, hence
agrees with the curve computing `Φ s (Φ u y)`.
-/

namespace Work.RPCore.Flow

open Work.RPCore.Port.ODE

theorem flow_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] (X : E → E) (hX : ContDiff ℝ 1 X) {K : ℝ}
    (hK : ∀ z, ‖fderiv ℝ X z‖ ≤ K) (Φ : ℝ → E → E)
    (hΦ : ∀ t y, ∃ γ : ℝ → E, γ 0 = y ∧ IsIntegralCurve γ (fun _ z => X z) ∧ γ t = Φ t y)
    (s u : ℝ) (y : E) : Φ (s + u) y = Φ s (Φ u y) := by
  classical
  -- `X` is globally Lipschitz, so integral curves are unique.
  have hL : LipschitzWith (lipConst K) X := lipschitzWith_lipConst hX hK
  -- The global integral curve through `y`, chosen once and for all.
  let γ : ℝ → E := Classical.choose (hΦ 0 y)
  have hγ0 : γ 0 = y := (Classical.choose_spec (hΦ 0 y)).1
  have hγint : IsIntegralCurve γ (fun _ z => X z) := (Classical.choose_spec (hΦ 0 y)).2.1
  -- The curve `r ↦ Φ r y` is an integral curve through `y`, hence equals `γ`.
  have hflow : IsIntegralCurve (fun r => Φ r y) (fun _ z => X z) :=
    isIntegralCurve_flow hL Φ hΦ y
  have hΦy : ∀ r, Φ r y = γ r := by
    have heq : (fun r => Φ r y) = γ :=
      eq_of_isIntegralCurve hL hflow hγint (t := 0) (by
        show Φ 0 y = γ 0
        rw [flow_zero Φ hΦ y, hγ0])
    intro r
    exact congrFun heq r
  -- The curve computing `Φ s (Φ u y)`.
  obtain ⟨γ₂, hγ₂0, hγ₂int, hγ₂val⟩ := hΦ s (Φ u y)
  -- The time translate `r ↦ γ (r + u)` is an integral curve starting at `Φ u y = γ u`,
  -- so it coincides with `γ₂` by uniqueness.
  have hδ : IsIntegralCurve (fun r => γ (r + u)) (fun _ z => X z) := by
    have hv : (fun (_ : ℝ) (z : E) => X z) ∘ (· + u) = (fun (_ : ℝ) (z : E) => X z) := by
      funext r z; rfl
    have h := hγint.comp_add u
    rwa [hv] at h
  have hδ0 : (fun r => γ (r + u)) 0 = γ₂ 0 := by
    show γ (0 + u) = γ₂ 0
    rw [zero_add, hγ₂0]
    exact (hΦy u).symm
  have heq2 : (fun r => γ (r + u)) = γ₂ := eq_of_isIntegralCurve hL hδ hγ₂int hδ0
  have hval : γ (s + u) = Φ s (Φ u y) := by
    have h := congrFun heq2 s
    rw [hγ₂val] at h
    exact h
  rw [hΦy (s + u)]
  exact hval

end Work.RPCore.Flow
