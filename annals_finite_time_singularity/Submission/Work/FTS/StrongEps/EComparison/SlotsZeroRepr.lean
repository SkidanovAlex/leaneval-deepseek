import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

theorem SlotsZeroRepr {α : ℝ} (hα : 0 < α) {u : ℝ → ℝ → ℝ} {θ : ℝ}
    (hdiff : DifferentiableOn ℝ (fun z => u z θ) (Set.Ioi 0))
    (hode : ∀ z, 0 < z → z * deriv (fun z' => u z' θ) z = -(3 / α) * u z θ) :
    ∀ z, 0 < z → u z θ = u 1 θ * z ^ (-(3 / α)) := by
  -- The inhomogeneous problem `z f' = s f` with `s := -(3/α)` has the general solution
  -- `f z = C · z^s` on the connected open set `z > 0`: the function `z ↦ f z · z^{-s}` has
  -- vanishing derivative there, hence is constant.
  have _hαne : α ≠ 0 := ne_of_gt hα
  intro z hz
  let f : ℝ → ℝ := fun z => u z θ
  let h : ℝ → ℝ := f * fun z => z ^ (3 / α)
  -- the logarithmic derivative of `h` vanishes on `z > 0`
  have hder : ∀ w ∈ Set.Ioi (0 : ℝ), deriv h w = 0 := by
    intro w hw
    have hw0 : 0 < w := hw
    have hfd : DifferentiableAt ℝ f w := hdiff.differentiableAt (isOpen_Ioi.mem_nhds hw)
    have hgd : HasDerivAt (fun z : ℝ => z ^ (3 / α)) ((3 / α) * w ^ (3 / α - 1)) w :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hw0))
    have hmul : deriv h w = deriv f w * w ^ (3 / α) + f w * ((3 / α) * w ^ (3 / α - 1)) := by
      show deriv (f * fun z : ℝ => z ^ (3 / α)) w
          = deriv f w * w ^ (3 / α) + f w * ((3 / α) * w ^ (3 / α - 1))
      rw [deriv_mul hfd hgd.differentiableAt, hgd.deriv]
    -- `w · w^{(3/α)-1} = w^{3/α}`
    have hwp : w * w ^ (3 / α - 1) = w ^ (3 / α) := by
      calc w * w ^ (3 / α - 1) = w ^ (1 : ℝ) * w ^ (3 / α - 1) := by rw [Real.rpow_one]
        _ = w ^ ((1 : ℝ) + (3 / α - 1)) := by rw [Real.rpow_add hw0]
        _ = w ^ (3 / α) := by congr 1; ring
    have hode' : w * deriv f w = -(3 / α) * f w := by
      have hh := hode w hw0
      simpa only [f] using hh
    have hkey : deriv h w * w = 0 := by
      rw [hmul, ← hwp]
      have : (deriv f w * (w * w ^ (3 / α - 1)) + f w * ((3 / α) * w ^ (3 / α - 1))) * w
          = w ^ (3 / α - 1) * w * (w * deriv f w + (3 / α) * f w) := by ring
      rw [this, hode']
      ring
    rcases mul_eq_zero.mp hkey with h' | h'
    · exact h'
    · exact absurd h' (ne_of_gt hw0)
  have hdiffh : DifferentiableOn ℝ h (Set.Ioi 0) := by
    intro w hw
    have hw0 : 0 < w := hw
    have hfd : DifferentiableAt ℝ f w := hdiff.differentiableAt (isOpen_Ioi.mem_nhds hw)
    have hgd : DifferentiableAt ℝ (fun z : ℝ => z ^ (3 / α)) w :=
      (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hw0))).differentiableAt
    exact (hfd.mul hgd).differentiableWithinAt
  obtain ⟨a, ha⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi hdiffh
    (fun w hw => hder w hw)
  have hz1' : u z θ * z ^ (3 / α) = u 1 θ := by
    have hh : h z = h 1 := by rw [ha z hz, ha 1 (by norm_num)]
    simp only [h, Pi.mul_apply, f, Real.one_rpow, mul_one] at hh
    exact hh
  have hzc : z ^ (3 / α) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hz (3 / α))
  calc u z θ = u 1 θ * (z ^ (3 / α))⁻¹ := (eq_mul_inv_iff_mul_eq₀ hzc).mpr hz1'
    _ = u 1 θ * z ^ (-(3 / α)) := by rw [← Real.rpow_neg (le_of_lt hz) (3 / α)]

end Work.FTS.StrongEps.EComparison
