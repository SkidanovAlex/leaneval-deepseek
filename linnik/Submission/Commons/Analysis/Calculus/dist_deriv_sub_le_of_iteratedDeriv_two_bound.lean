import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.Calculus

theorem dist_deriv_sub_le_of_iteratedDeriv_two_bound {x₀ B : ℝ} (hx₀ : 0 < x₀) {f : ℝ → ℂ}
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) :
    ∀ u ∈ Set.Ioo (0:ℝ) x₀, ∀ v ∈ Set.Ioo (0:ℝ) x₀, dist (deriv f u) (deriv f v) ≤ B * |u - v| := by
  intro u hu v hv
  set s : Set ℝ := Set.Ioo 0 x₀ with hs_def
  have hsopen : IsOpen s := isOpen_Ioo
  have hs_unique : UniqueDiffOn ℝ s := hsopen.uniqueDiffOn
  -- Differentiability of `deriv f` on `s`, from `ContDiffOn ℝ 2 f s`.
  have hh := (contDiffOn_nat_iff_continuousOn_differentiableOn_deriv (n := 2) hs_unique).mp hf2
  have hdiffWithin : DifferentiableOn ℝ (iteratedDerivWithin 1 f s) s := hh.2 1 (by norm_num)
  have heq : Set.EqOn (deriv f) (iteratedDerivWithin 1 f s) s := by
    intro x hx
    rw [iteratedDerivWithin_of_isOpen hsopen hx, iteratedDeriv_one]
  have hdiff : DifferentiableOn ℝ (deriv f) s := hdiffWithin.congr heq
  have hdiffAt : ∀ x ∈ s, DifferentiableAt ℝ (deriv f) x := fun x hx =>
    hdiff.differentiableAt (hsopen.mem_nhds hx)
  -- Identify `deriv (deriv f)` with `iteratedDeriv 2 f`.
  have h2 : deriv (deriv f) = iteratedDeriv 2 f := by
    ext t
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
  have hbound : ∀ x ∈ s, ‖deriv (deriv f) x‖ ≤ B := by
    intro x hx
    rw [congrFun h2 x]
    exact hBnd x hx
  have hconv : Convex ℝ s := convex_Ioo _ _
  have := hconv.norm_image_sub_le_of_norm_deriv_le hdiffAt hbound hv hu
  rw [dist_eq_norm]
  simpa using this

end Commons.Analysis.Calculus