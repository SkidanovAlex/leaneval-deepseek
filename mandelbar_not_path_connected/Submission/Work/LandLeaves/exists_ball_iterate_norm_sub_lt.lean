import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A ball around an attracting fixed point is invariant along orbits

`Work.LandLeaves.exists_ball_iterate_norm_sub_lt` is the elementary local-dynamics input for the
landing leaf `Work.LandLeaves.attractingCyclesInner` (area `Submission/Work/LandLeaves/`): if
`f` is (complex-)differentiable at a fixed point `z` with multiplier `f'` of modulus `< 1`, then
some ball `B(z, r)` is mapped strictly into itself by `f`, and hence every forward orbit of a
point of that ball stays in the ball.

The proof is the standard attracting-fixed-point estimate: from the little-o form of the
derivative one gets a neighbourhood on which `‖f w - f z‖ ≤ C ‖w - z‖` with
`C = (1 + ‖f'‖)/2 < 1`, and then induction gives `‖f^[n] w - z‖ ≤ C ^ n ‖w - z‖ ≤ ‖w - z‖`.
-/

open Filter Asymptotics
open scoped Topology

namespace Work.LandLeaves

theorem exists_ball_iterate_norm_sub_lt {f : ℂ → ℂ} {f' z : ℂ} (h : HasDerivAt f f' z)
    (hfz : f z = z) (hlt : ‖f'‖ < 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, ‖w - z‖ < r → ∀ n : ℕ, ‖(f^[n]) w - z‖ < r := by
  -- the contraction factor `C = (1 + ‖f'‖)/2 ∈ [0, 1)`
  set C : ℝ := (1 + ‖f'‖) / 2 with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  have hC1 : C < 1 := by rw [hCdef]; linarith
  have hεpos : 0 < C - ‖f'‖ := by rw [hCdef]; linarith
  -- the derivative in `F`-form, and its little-o statement
  have hF : HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℂ f') z :=
    hasDerivAt_iff_hasFDerivAt.mp h
  have hlit : (fun y : ℂ => f y - f z - (ContinuousLinearMap.toSpanSingleton ℂ f') (y - z))
      =o[nhds z] (fun y : ℂ => y - z) := hF.isLittleO
  have hbound : ∀ᶠ y in nhds z,
      ‖f y - f z - (ContinuousLinearMap.toSpanSingleton ℂ f') (y - z)‖ ≤
        (C - ‖f'‖) * ‖y - z‖ :=
    IsLittleO.def hlit hεpos
  rw [Metric.eventually_nhds_iff] at hbound
  obtain ⟨δ, hδpos, hδ⟩ := hbound
  -- on the ball of radius `δ`, `f` contracts distances to `z` by `C`
  have step : ∀ u : ℂ, ‖u - z‖ < δ → ‖f u - z‖ ≤ C * ‖u - z‖ := by
    intro u hu
    have hu' : dist u z < δ := by rw [dist_eq_norm]; exact hu
    have h1 := hδ hu'
    have h2 : (ContinuousLinearMap.toSpanSingleton ℂ f') (u - z) = f' * (u - z) := by
      rw [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
    have heq : f u - z = (f u - f z - (ContinuousLinearMap.toSpanSingleton ℂ f') (u - z))
        + (ContinuousLinearMap.toSpanSingleton ℂ f') (u - z) := by
      rw [hfz]; ring
    calc ‖f u - z‖
        = ‖(f u - f z - (ContinuousLinearMap.toSpanSingleton ℂ f') (u - z))
            + (ContinuousLinearMap.toSpanSingleton ℂ f') (u - z)‖ := by rw [heq]
      _ ≤ ‖f u - f z - (ContinuousLinearMap.toSpanSingleton ℂ f') (u - z)‖
            + ‖(ContinuousLinearMap.toSpanSingleton ℂ f') (u - z)‖ := norm_add_le _ _
      _ ≤ (C - ‖f'‖) * ‖u - z‖ + ‖f'‖ * ‖u - z‖ := by
            apply add_le_add h1
            rw [h2, norm_mul]
      _ = C * ‖u - z‖ := by ring
  refine ⟨δ, hδpos, ?_⟩
  intro w hw n
  -- induction: `‖f^[n] w - z‖ ≤ C ^ n * ‖w - z‖`
  have hmain : ‖(f^[n]) w - z‖ ≤ C ^ n * ‖w - z‖ := by
    induction n with
    | zero => simp
    | succ k ih =>
        have huz : ‖(f^[k]) w - z‖ < δ := by
          calc ‖(f^[k]) w - z‖ ≤ C ^ k * ‖w - z‖ := ih
            _ ≤ ‖w - z‖ :=
                  mul_le_of_le_one_left (norm_nonneg _)
                    (by simpa using pow_le_pow_left₀ hC0 hC1.le k)
            _ < δ := hw
        calc ‖(f^[k.succ]) w - z‖ = ‖f ((f^[k]) w) - z‖ := by
                rw [Function.iterate_succ_apply']
          _ ≤ C * ‖(f^[k]) w - z‖ := step _ huz
          _ ≤ C * (C ^ k * ‖w - z‖) := mul_le_mul_of_nonneg_left ih hC0
          _ = C ^ k.succ * ‖w - z‖ := by rw [pow_succ]; ring
  calc ‖(f^[n]) w - z‖ ≤ C ^ n * ‖w - z‖ := hmain
    _ ≤ ‖w - z‖ :=
          mul_le_of_le_one_left (norm_nonneg _)
            (by simpa using pow_le_pow_left₀ hC0 hC1.le n)
    _ < δ := hw

end Work.LandLeaves
