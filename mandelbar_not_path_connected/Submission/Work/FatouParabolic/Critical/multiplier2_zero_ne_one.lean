import Mathlib
import Submission.Work.FatouParabolic.Defs
import Submission.Work.LANDCL.Critical.not_isRepelling_criticalValue

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Critical

/-!
# The critical point `0` of the second-return map is not parabolic

The tricorn second-return map is `Tsq c z = (z² + c̄)² + c`.  The point `0` is always a
critical point of `Tsq c`: the derivative is `4z(z² + c̄)`, which vanishes at `z = 0`.  Hence
the multiplier of the `m`-th iterate of `Tsq c` at `0`,
`multiplier2 c m 0 = deriv ((Tsq c)^[m]) 0`, is `0` for every `m > 0` — the critical orbit
starts at a critical point.  In particular the multiplier is never `1`, i.e. `0` is never a
parabolic periodic point of the critical orbit through the second-return map.
-/

/-- The second-return map `Tsq c` is differentiable (it is a polynomial). -/
lemma differentiable_tsq (c : ℂ) : Differentiable ℂ (Work.Landing.Tsq c) := by
  unfold Work.Landing.Tsq
  fun_prop

/-- The second-return map `Tsq c` has a critical point at `0`: its derivative vanishes there. -/
lemma deriv_tsq_zero (c : ℂ) : deriv (Work.Landing.Tsq c) 0 = 0 := by
  unfold Work.Landing.Tsq
  simp [deriv_add_const]

/-- If `f` is differentiable and `deriv f x = 0`, then every positive iterate of `f` has
derivative `0` at `x` (the chain rule `(f^[k]) ∘ f = f^[k+1]` exhibits the vanishing factor
`deriv f x`). -/
lemma deriv_iterate_eq_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x : ℂ}
    (hx : deriv f x = 0) : ∀ m : ℕ, 0 < m → deriv (f^[m]) x = 0 := by
  intro m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hm)
  rw [Function.iterate_succ]
  have hcomp : deriv ((f^[k]) ∘ f) x = deriv (f^[k]) (f x) * deriv f x :=
    deriv_comp x (hf.iterate k).differentiableAt hf.differentiableAt
  rw [hcomp, hx, mul_zero]

theorem multiplier2_zero_ne_one (c : ℂ) {m : ℕ} (hm : 0 < m) :
    Work.Landing.multiplier2 c m 0 ≠ 1 := by
  have h0 : Work.Landing.multiplier2 c m 0 = 0 := by
    unfold Work.Landing.multiplier2
    exact deriv_iterate_eq_zero (differentiable_tsq c) (deriv_tsq_zero c) m hm
  rw [h0]
  norm_num

end Work.FatouParabolic.Critical
