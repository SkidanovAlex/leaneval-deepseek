import Mathlib
import Submission.Work.MotT.TwistPointKDefs
import Submission.Work.MotT.exists_kleinPoint

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotT

/-- **The twist has a `K`-point when the twist parameter is a fifth power.**  Let `D` be a good
Klein datum over a field `K`, `h ∈ Kˣ` and `w ∈ K` with `w ^ 5 = h`.  Then the twisted Klein curve
`C_h` has a nonzero `K`-point in Kummer coordinates: there is `y : Fin 5 → K`, `y ≠ 0`, with
`kleinTw D.a D.b h y k = 0` for all `k`.

Route: `Work.MotT.exists_kleinPoint D hD` gives `y₀ : Fin 5 → K` with `y₀ ≠ 0` and
`kleinP D.a D.b y₀ k = 0`.  Set `y i := w⁻¹ ^ (i : ℕ) * y₀ i`; then `w ^ (i:ℕ) * y i = y₀ i`, so
`kleinP a b (fun i => w^i * y i) k = kleinP a b y₀ k = 0`, and `Work.MotV.kleinTw_subst` gives
`w ^ (4 * k) * kleinTw a b (w ^ 5) y k = 0`; `w ≠ 0` (as `h ≠ 0` and `w^5 = h`) gives
`kleinTw a b h y k = 0` after rewriting `w^5 = h`.  `y ≠ 0` because `w` is a unit and `y₀ ≠ 0`. -/
theorem exists_kleinTw_point_of_fifth_pow {K : Type} [Field K] (D : Work.MotV.KleinData K)
    (hD : D.Good) {h : K} (hh : h ≠ 0) (w : K) (hw : w ^ 5 = h) :
    ∃ y : Fin 5 → K, y ≠ 0 ∧ ∀ k, Work.MotV.kleinTw D.a D.b h y k = 0 := by
  obtain ⟨y₀, hy₀ne, hy₀⟩ := Work.MotT.exists_kleinPoint D hD
  -- `w` is a unit because `w ^ 5 = h ≠ 0`
  have hwne : w ≠ 0 := fun h0 => hh (by rw [← hw, h0]; norm_num)
  refine ⟨fun i => w⁻¹ ^ (i : ℕ) * y₀ i, ?_, ?_⟩
  · -- `y ≠ 0`: applying `w ^ i` to `y i` recovers `y₀ i`
    intro hy
    have hy0 : y₀ = 0 := by
      funext i
      have hzi : w⁻¹ ^ (i : ℕ) * y₀ i = 0 := by simpa using congrFun hy i
      have hval : w ^ (i : ℕ) * (w⁻¹ ^ (i : ℕ) * y₀ i) = y₀ i := by
        rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hwne, one_pow, one_mul]
      calc y₀ i = w ^ (i : ℕ) * (w⁻¹ ^ (i : ℕ) * y₀ i) := hval.symm
        _ = 0 := by rw [hzi, mul_zero]
    exact hy₀ne hy0
  · -- `w ^ i * y i = y₀ i`, so `kleinP a b (w ^ i * y i) = 0`; `kleinTw_subst` extracts the twist
    intro k
    have hy_eq : (fun i : Fin 5 => w ^ (i : ℕ) * (w⁻¹ ^ (i : ℕ) * y₀ i)) = y₀ := by
      funext i
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hwne, one_pow, one_mul]
    have hsub := Work.MotV.kleinTw_subst D.a D.b w (fun i => w⁻¹ ^ (i : ℕ) * y₀ i) k
    rw [hy_eq, hy₀ k] at hsub
    have htw : Work.MotV.kleinTw D.a D.b (w ^ 5) (fun i => w⁻¹ ^ (i : ℕ) * y₀ i) k = 0 :=
      (mul_eq_zero.mp hsub.symm).resolve_left (pow_ne_zero _ hwne)
    rwa [hw] at htw

end Work.MotT
