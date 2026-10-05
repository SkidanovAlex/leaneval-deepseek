import Mathlib
import Submission.Work.RPA3.flux_prim_defs

namespace Work.RPA3

/-- The `x`-component of the flux form is `2π`-periodic in the angle `t`.

Proof: `Tk 1` is the translation by `c = ((0,2π),(0,0))` in `PS` (`Tk 1 a = a + c`), so
`LagFamily.per` reads `ℓ τ (y,t+2π) = ℓ τ (y,t) + c`.  Both slice derivatives occurring in
`bxf` are therefore unchanged: the `x`-slice `y' ↦ ℓ τ (y',t+2π)` differs from `y' ↦ ℓ τ (y',t)`
by the constant `c` (so `deriv_add_const`), and likewise the `τ`-slice
`σ ↦ ℓ σ (y,t+2π)` differs from `σ ↦ ℓ σ (y,t)` by the constant `c`. -/
theorem bxf_per (L : LagFamily) (τ y t : ℝ) :
    bxf L τ y (t + 2 * Real.pi) = bxf L τ y t := by
  -- `Tk 1` is the translation by `c = ((0,2π),(0,0))`.
  have hTk : ∀ a : PS, Tk (1 : ℤ) a = a + ((0, 2 * Real.pi), (0, 0)) := by
    intro a
    ext <;> simp [Tk]
  -- the `x`-slice derivative is unchanged by the constant translation.
  have hdx : deriv (fun y' => L.ℓ τ (y', t + 2 * Real.pi)) y
      = deriv (fun y' => L.ℓ τ (y', t)) y := by
    rw [show (fun y' => L.ℓ τ (y', t + 2 * Real.pi))
          = (fun y' => L.ℓ τ (y', t) + ((0, 2 * Real.pi), (0, 0))) from
            funext (fun y' => by rw [L.per τ y' t, hTk]),
        deriv_add_const]
  -- the `τ`-slice derivative is unchanged by the constant translation.
  have hdtau : deriv (fun σ => L.ℓ σ (y, t + 2 * Real.pi)) τ
      = deriv (fun σ => L.ℓ σ (y, t)) τ := by
    rw [show (fun σ => L.ℓ σ (y, t + 2 * Real.pi))
          = (fun σ => L.ℓ σ (y, t) + ((0, 2 * Real.pi), (0, 0))) from
            funext (fun σ => by rw [L.per σ y t, hTk]),
        deriv_add_const]
  simp only [bxf, hdtau, hdx]

/-- The flux primitive is `2π`-periodic in the angle `t`.

Route: by `LagFamily.per` and `Tk 1 a = a + ((0,2π),(0,0))`, the family satisfies
`ℓ τ (y, t+2π) = ℓ τ (y,t) + ((0,2π),(0,0))`; hence both slice derivatives `∂_xℓ` and `∂_τℓ`
are unchanged (`deriv_add_const`/`deriv_const_add`), so `bxf L τ y (t+2π) = bxf L τ y t` for all
`y`, and the two fixed-interval integrals defining `Hf L τ x (t+2π)` and `Hf L τ x t` agree by
`intervalIntegral.integral_congr`. -/
theorem Hf_per (L : Work.RPA3.LagFamily) (τ x t : ℝ) :
    Work.RPA3.Hf L τ x (t + 2 * Real.pi) = Work.RPA3.Hf L τ x t := by
  unfold Hf
  rw [show (fun σ => HfIntegrand L ((τ, (x, t + 2 * Real.pi)), σ))
        = (fun σ => HfIntegrand L ((τ, (x, t)), σ)) from
      funext (fun σ => by simp only [HfIntegrand]; rw [bxf_per])]

end Work.RPA3
