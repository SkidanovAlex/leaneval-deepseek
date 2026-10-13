import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.BoxRegAux

theorem abs_sub_mul_le_of_derivWithin_bound {u u' : ℝ → ℝ} {α β c C : ℝ}
    (hder : ∀ t ∈ Set.Icc α β, HasDerivWithinAt u (u' t) (Set.Icc α β) t)
    {x y : ℝ} (hx : x ∈ Set.Icc α β) (hy : y ∈ Set.Icc α β)
    (hb : ∀ t ∈ Set.uIcc x y, |u' t - c| ≤ C) :
    |u y - u x - (y - x) * c| ≤ C * |y - x| := by
  -- `uIcc x y ⊆ Icc α β`, so the derivative hypothesis restricts to the unordered interval
  have hsub : Set.uIcc x y ⊆ Set.Icc α β := Set.uIcc_subset_Icc hx hy
  -- apply the mean value theorem to `τ ↦ u τ - c * τ`, whose derivative is `u' t - c`
  have hf : ∀ t ∈ Set.uIcc x y,
      HasDerivWithinAt (fun τ : ℝ => u τ - τ * c) (u' t - c) (Set.uIcc x y) t := by
    intro t ht
    have h1 : HasDerivWithinAt u (u' t) (Set.uIcc x y) t := (hder t (hsub ht)).mono hsub
    have h2 : HasDerivWithinAt (fun τ : ℝ => τ * c) c (Set.uIcc x y) t := by
      simpa using ((hasDerivAt_id t).mul_const c).hasDerivWithinAt
    exact h1.sub h2
  have hbound : ∀ t ∈ Set.uIcc x y, ‖u' t - c‖ ≤ C := by
    intro t ht; rw [Real.norm_eq_abs]; exact hb t ht
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun τ : ℝ => u τ - τ * c) (f' := fun τ : ℝ => u' τ - c)
      (s := Set.uIcc x y) hf hbound (convex_uIcc x y) (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  have hnorm : ‖(fun τ : ℝ => u τ - τ * c) y - (fun τ : ℝ => u τ - τ * c) x‖
      = |u y - u x - (y - x) * c| := by
    rw [Real.norm_eq_abs]; congr 1; ring
  rw [hnorm, Real.norm_eq_abs] at hmain
  exact hmain

end Work.FTS_EllLimOK.BoxRegAux
