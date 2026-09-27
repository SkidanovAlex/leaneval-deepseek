import Mathlib
import Submission.Work.Conn.Basic

namespace Work.Conn.PathConnected

open Metric (sphere closedBall)
open ContinuousMap

/-- A space homotopy equivalent to `𝕊ⁿ` is path connected, for `n ≥ 1` (`Sph n` is
`Work.Conn.Sph n`, the unit sphere of `ℝⁿ⁺¹`, used as a type).

Route: `Sph n` is path connected by `isPathConnected_sphere` (the hypothesis
`1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n+1)))` follows from `n ≥ 1`) together with
`isPathConnected_iff_pathConnectedSpace`.  Given `x y : M`, join `e x` to `e y` by a path in `𝕊ⁿ`
and map it back with the inverse of `e`; `HomotopyEquiv.left_inv` gives a homotopy from
`e.invFun ∘ e` to the identity, and a homotopy of maps provides a path between the two images of
any point, so `e.invFun (e x)` is joined to `x` and likewise for `y`. -/
theorem pathConnectedSpace_of_homotopyEquiv_sphere {n : ℕ} (hn : 1 ≤ n) {M : Type*}
    [TopologicalSpace M] (e : M ≃ₕ Sph n) : PathConnectedSpace M := by
  -- `𝕊ⁿ` is path connected for `n ≥ 1`.
  have hpcs : PathConnectedSpace (Sph n) := by
    rw [← isPathConnected_iff_pathConnectedSpace]
    refine isPathConnected_sphere ?_ 0 (by norm_num : (0 : ℝ) ≤ 1)
    change 1 < Module.rank ℝ (WithLp 2 (Fin (n + 1) → ℝ))
    rw [(WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).rank_eq]
    rw [rank_fin_fun]
    exact_mod_cast Nat.lt_succ_of_le hn
  refine ⟨?_, fun x y => ?_⟩
  · obtain ⟨p⟩ := hpcs.nonempty
    exact ⟨e.invFun p⟩
  · -- `e.invFun ∘ e` is homotopic to the identity, giving paths `e.invFun (e x) ~ x`, `~ y`.
    have hleft : Joined (e.invFun (e x)) x := ⟨e.left_inv.some.evalAt x⟩
    have hright : Joined (e.invFun (e y)) y := ⟨e.left_inv.some.evalAt y⟩
    -- transport a path in `𝕊ⁿ` from `e x` to `e y` back along `e.invFun`.
    have hmid : Joined (e.invFun (e x)) (e.invFun (e y)) :=
      (hpcs.joined (e x) (e y)).map e.invFun.continuous
    exact (Joined.symm hleft).trans (hmid.trans hright)

end Work.Conn.PathConnected
