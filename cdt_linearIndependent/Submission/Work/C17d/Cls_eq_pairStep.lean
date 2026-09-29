import Mathlib
import Submission.Work.C17d.DyChainDefs

namespace Work.C17d

open Work.C17

/-- One step of `dW` on a module element whose integral (third) coordinates vanish: the sum
`∑ᵢ wᵢ·y^{i−4}` drops out and the third coordinate stays zero, so `dW` acts by `pairStep` on the
first two coordinates. -/
lemma dW_zero (a b : ℚ) (uv : RatFunc ℚ × RatFunc ℚ) :
    Work.C17.dW a b (uv, (0 : Fin 6 → RatFunc ℚ)) = (Work.C17d.pairStep a b uv, 0) := by
  unfold Work.C17.dW Work.C17d.pairStep
  simp
  funext i
  simp

/-- Iterating `dW` from `((1,0),0)` keeps the integral coordinates zero throughout, so the
`(e₀,e₁)`-part of the `n`-th iterate is exactly the `n`-th iterate of `pairStep`. -/
lemma iterate_dW_zero (a b : ℚ) (n : ℕ) :
    (Work.C17.dW a b)^[n] ((1, 0), 0)
      = ((Work.C17d.pairStep a b)^[n] (1, 0), 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      exact dW_zero a b _

theorem Cls_eq_pairStep (a b : ℚ) (k : Fin 4) :
    Work.C17.cls a b k = (Work.C17d.pairStep a b)^[(k : ℕ)] (1, 0) := by
  have hk := iterate_dW_zero a b (k : ℕ)
  unfold Work.C17.cls
  rw [hk]

end Work.C17d
