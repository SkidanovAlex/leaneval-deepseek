import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

/-- If `h z = 0` for every `z ∉ [a,b]`, then `deriv h` and `deriv (deriv h)` also vanish off
`[a,b]` (no regularity is required: `h` is identically `0` on a neighbourhood of every
`z ∉ [a,b]`, and a function which is eventually `0` near `z` has derivative `0` at `z`). -/
theorem AgmonDerivVanishing {h : ℝ → ℝ} {a b : ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc a b → h z = 0) :
    (∀ z, z < a → deriv h z = 0) ∧ (∀ z, b < z → deriv h z = 0) ∧
      (∀ z, z < a → deriv (deriv h) z = 0) ∧ (∀ z, b < z → deriv (deriv h) z = 0) := by
  -- `h` vanishes identically on the open set `Iio a`, resp. `Ioi b`, which is a neighbourhood
  -- of each of its points; hence `deriv h` vanishes on those halflines as functions, and the
  -- same argument applies once more with `deriv h` in place of `h`.
  have h1 : ∀ z, z < a → deriv h z = 0 := by
    intro z hz
    have hev : h =ᶠ[nhds z] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Iio.mem_nhds hz] with y hy
      exact hsupp y (fun hm => absurd hy (not_lt.mpr hm.1))
    rw [hev.deriv_eq, deriv_const]
  have h2 : ∀ z, b < z → deriv h z = 0 := by
    intro z hz
    have hev : h =ᶠ[nhds z] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      exact hsupp y (fun hm => absurd hy (not_lt.mpr hm.2))
    rw [hev.deriv_eq, deriv_const]
  have h3 : ∀ z, z < a → deriv (deriv h) z = 0 := by
    intro z hz
    have hev : deriv h =ᶠ[nhds z] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Iio.mem_nhds hz] with y hy
      exact h1 y hy
    rw [hev.deriv_eq, deriv_const]
  have h4 : ∀ z, b < z → deriv (deriv h) z = 0 := by
    intro z hz
    have hev : deriv h =ᶠ[nhds z] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      exact h2 y hy
    rw [hev.deriv_eq, deriv_const]
  exact ⟨h1, h2, h3, h4⟩

end Work.FTS.EllipticEst.Blocks
