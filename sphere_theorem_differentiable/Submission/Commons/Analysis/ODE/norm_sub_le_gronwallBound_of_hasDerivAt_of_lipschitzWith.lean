import Mathlib.Analysis.ODE.Gronwall

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.ODE

open Set

/-- If `z : ℝ → E` solves `z' = f ∘ z` on `[0, T]` with `f` Lipschitz with constant `L`, then
`‖z t - z 0‖` is bounded by the Grönwall bound `gronwallBound 0 L ‖f (z 0)‖ t`. -/
theorem norm_sub_le_gronwallBound_of_hasDerivAt_of_lipschitzWith
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → E} {L : NNReal}
    (hf : LipschitzWith L f) {z : ℝ → E} {T : ℝ} (hT : 0 ≤ T)
    (hz : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt z (f (z t)) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ‖z t - z 0‖ ≤ gronwallBound 0 (L : ℝ) ‖f (z 0)‖ t := by
  intro t ht
  have hcont : ContinuousOn (fun s => z s - z 0) (Set.Icc 0 t) := by
    intro s hs
    exact (((hz s ⟨hs.1, hs.2.trans ht.2⟩).continuousAt).sub
      continuousAt_const).continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ico (0 : ℝ) t,
      HasDerivWithinAt (fun s => z s - z 0) (f (z x)) (Set.Ici x) x := by
    intro x hx
    exact ((hz x ⟨hx.1, (le_of_lt hx.2).trans ht.2⟩).sub_const (z 0)).hasDerivWithinAt
  have ha : ‖(fun s => z s - z 0) 0‖ ≤ (0 : ℝ) := by simp
  have hbound : ∀ x ∈ Set.Ico (0 : ℝ) t,
      ‖f (z x)‖ ≤ (L : ℝ) * ‖(fun s => z s - z 0) x‖ + ‖f (z 0)‖ := by
    intro x hx
    have hlip := hf.dist_le_mul (z x) (z 0)
    rw [dist_eq_norm, dist_eq_norm] at hlip
    calc ‖f (z x)‖ = ‖f (z x) - f (z 0) + f (z 0)‖ := by rw [sub_add_cancel]
      _ ≤ ‖f (z x) - f (z 0)‖ + ‖f (z 0)‖ := norm_add_le _ _
      _ ≤ (L : ℝ) * ‖z x - z 0‖ + ‖f (z 0)‖ := by linarith
  have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun s => z s - z 0)
    (f' := fun s => f (z s)) (δ := 0) (K := (L : ℝ)) (ε := ‖f (z 0)‖)
    (a := 0) (b := t) hcont hderiv ha hbound t ⟨ht.1, le_refl t⟩
  simpa using h

end Commons.Analysis.ODE