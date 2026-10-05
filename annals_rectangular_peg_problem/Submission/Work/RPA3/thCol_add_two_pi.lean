import Mathlib
import Submission.Work.RPA3.theta_columns_defs
import Submission.Work.RPA3.theta_per

namespace Work.RPA3

/-- **D2, the four columns are `2π`-periodic in the angle `t`.**  Shifting `t` by `2π` translates
the value of the tubular map by the constant `c = ((0,2π),(0,0))` in `q₂`
(`Work.RPA3.theta_per`: `θ(τ,x,t+2π,ξ) = Tk 1 (θ(τ,x,t,ξ)) = θ(τ,x,t,ξ) + c`, where
`Tk 1 a = a + c` is `rfl` after `ext`/`simp [Tk]`), and a translation of the *values* does not
change any of the four columns in `thCol`:

* `j = 0`: `deriv (fun y => θ(τ,y,t+2π,ξ)) x = deriv (fun y => θ(τ,y,t,ξ) + c) x`, use
  `deriv_add_const`;
* `j = 2` and `j = 3`: the derivative is taken with respect to the `ξ`-coordinate and the shifted
  function differs from the unshifted one by the constant `c`, again `deriv_add_const`;
* `j = 1` is the only case where `t` is also the point at which the `deriv` is taken: first replace
  `deriv (fun s => θ(τ,x,s,ξ)) (t+2π)` by `deriv (fun s => θ(τ,x,s+2π,ξ)) t`
  (`deriv_comp_add_const`), then use `deriv_add_const`.

After `fin_cases j`, `simp only [thCol_zero, thCol_one, thCol_two, thCol_three]` and the two
`deriv` lemmas should close each case; beware that `fin_cases` produces `Fin.mk 0 ⋯`, so
`Fin.reduceFinMk` or an explicit `show` may be needed to unfold the `![...]` vector notation. -/
theorem thCol_add_two_pi (L : Work.RPA3.LagFamilyAll) (j : Fin 4) (τ x t : ℝ) (ξ : ℝ × ℝ) :
    Work.RPA3.thCol L j (τ, ((x, t + 2 * Real.pi), ξ))
      = Work.RPA3.thCol L j (τ, ((x, t), ξ)) := by
  -- `θ` shifts by the constant `c = ((0,2π),(0,0))` when `t` is shifted by `2π`.
  have h : ∀ y s : ℝ, ∀ ξ' : ℝ × ℝ,
      theta L τ y (s + 2 * Real.pi) ξ' = theta L τ y s ξ' + ((0, 2 * Real.pi), (0, 0)) := by
    intro y s ξ'
    rw [theta_per]
    ext <;> simp [Tk]
  fin_cases j
  · show thCol L 0 (τ, ((x, t + 2 * Real.pi), ξ)) = thCol L 0 (τ, ((x, t), ξ))
    simp only [thCol_zero]
    rw [show (fun y => theta L τ y (t + 2 * Real.pi) ξ)
          = (fun y => theta L τ y t ξ + ((0, 2 * Real.pi), (0, 0))) from
            funext (fun y => h y t ξ),
        deriv_add_const]
  · show thCol L 1 (τ, ((x, t + 2 * Real.pi), ξ)) = thCol L 1 (τ, ((x, t), ξ))
    simp only [thCol_one]
    rw [← deriv_comp_add_const (fun s => theta L τ x s ξ) (2 * Real.pi) t]
    rw [show (fun y => theta L τ x (y + 2 * Real.pi) ξ)
          = (fun y => theta L τ x y ξ + ((0, 2 * Real.pi), (0, 0))) from
            funext (fun y => h x y ξ),
        deriv_add_const]
  · show thCol L 2 (τ, ((x, t + 2 * Real.pi), ξ)) = thCol L 2 (τ, ((x, t), ξ))
    simp only [thCol_two]
    rw [show (fun u => theta L τ x (t + 2 * Real.pi) (u, ξ.2))
          = (fun u => theta L τ x t (u, ξ.2) + ((0, 2 * Real.pi), (0, 0))) from
            funext (fun u => h x t (u, ξ.2)),
        deriv_add_const]
  · show thCol L 3 (τ, ((x, t + 2 * Real.pi), ξ)) = thCol L 3 (τ, ((x, t), ξ))
    simp only [thCol_three]
    rw [show (fun u => theta L τ x (t + 2 * Real.pi) (ξ.1, u))
          = (fun u => theta L τ x t (ξ.1, u) + ((0, 2 * Real.pi), (0, 0))) from
            funext (fun u => h x t (ξ.1, u)),
        deriv_add_const]

end Work.RPA3
