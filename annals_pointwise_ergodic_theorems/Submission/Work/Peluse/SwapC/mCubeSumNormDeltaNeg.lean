import Mathlib
import Submission.Work.Peluse.SwapC.Basic

namespace Work.Peluse.SwapC

open scoped BigOperators
open Work.Peluse

/-!
# The `mCubeSum` of a delta depends only on the *signed* separation

For a function `f : ℤ → ℂ` and shifts `u, v` put `g_{u,v}(y) = star (f (y+u)) * f (y+v)`
(the *delta* of the `(u,v)`-difference).  This file proves that the box norm
`‖mCubeSum d X ν S (fun _ y => g_{u,v} y)‖` depends only on the *signed* separation:
if `v - u = -(v' - u')` then the two box norms agree.

The two structural facts about `mCubeSum` used are

* `mCubeSum_comp_add_right` — the box sum is invariant under translating the argument of the
  function (`∑' x` ranges over all of `ℤ`);
* `mCubeSum_comp_star` — conjugating the function conjugates the box sum (all exponents
  `star^[weight ω]` acquire one extra `star`, and `∏_ω star (z_ω) = star (∏_ω z_ω)`).

The delta identity itself is the elementary pointwise relation
`g_{u',v'}(y) = star (g_{u,v}(y + (v' - u)))`, which holds exactly under the hypothesis
`v - u = -(v' - u')`.
-/

noncomputable section

/-- `star` commutes with its iterates on `ℂ`. -/
lemma star_iterate_apply_star (n : ℕ) (z : ℂ) : (star^[n]) (star z) = star ((star^[n]) z) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, star_star]

/-- `mCubeSum` is invariant under translating the argument of the function: for the inner
`∑' x : ℤ` this is the reindexing `x ↦ x + t`. -/
lemma mCubeSum_comp_add_right {d : ℕ} {X : Type} [Fintype X] (ν : Fin d → X → ℤ) (S : Finset ℤ)
    (F : (Fin d → Bool) → ℤ → ℂ) (t : ℤ) :
    mCubeSum d X ν S (fun ω y => F ω (y + t)) = mCubeSum d X ν S F := by
  simp only [mCubeSum]
  congr 1
  refine Finset.sum_congr rfl (fun h _ => ?_)
  refine Finset.sum_congr rfl (fun h' _ => ?_)
  have h1 : (∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
        (F ω ((x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω) + t)))
      = (∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
        (F ω ((x + t) + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))) :=
    tsum_congr (fun x => Finset.prod_congr rfl (fun ω _ => by
      rw [show (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω) + t
          = (x + t) + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω by ring]))
  rw [h1]
  exact Equiv.tsum_eq (Equiv.addRight t)
    (fun b : ℤ => ∏ ω : Fin d → Bool, (star^[weight ω])
        (F ω (b + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω)))

/-- Conjugating the function conjugates the box sum: every `star^[weight ω]` acquires one extra
`star`, and `∏_ω star (z_ω) = star (∏_ω z_ω)`. -/
lemma mCubeSum_comp_star {d : ℕ} {X : Type} [Fintype X] (ν : Fin d → X → ℤ) (S : Finset ℤ)
    (F : (Fin d → Bool) → ℤ → ℂ) :
    mCubeSum d X ν S (fun ω y => star (F ω y)) = star (mCubeSum d X ν S F) := by
  simp only [mCubeSum]
  rw [star_mul', star_mul', star_inv₀, star_natCast, star_pow, star_inv₀, star_natCast]
  congr 1
  simp only [star_sum, tsum_star, star_prod, star_iterate_apply_star]

theorem mCubeSumNormDeltaNeg {d : ℕ} {X : Type} [Fintype X] (ν : Fin d → X → ℤ) (S : Finset ℤ)
    (f : ℤ → ℂ) (u v u' v' : ℤ) (h : v - u = -(v' - u')) :
    ‖Work.Peluse.SwapC.mCubeSum d X ν S (fun _ y => star (f (y + u)) * f (y + v))‖
      = ‖Work.Peluse.SwapC.mCubeSum d X ν S (fun _ y => star (f (y + u')) * f (y + v'))‖ := by
  -- the delta of `(u,v)` and the delta of `(u',v')` differ by the translation `t = v' - u`
  -- and one conjugation
  set g : ℤ → ℂ := fun y => star (f (y + u)) * f (y + v) with hg
  set t : ℤ := v' - u with ht
  have key : ∀ y : ℤ, star (f (y + u')) * f (y + v') = star (g (y + t)) := by
    intro y
    have h1 : (y + t) + u = y + v' := by rw [ht]; ring
    have h2 : (y + t) + v = y + u' := by rw [ht]; linarith
    rw [hg]
    simp only
    rw [h1, h2, star_mul, star_star]
  have hfun : (fun (_ : Fin d → Bool) y => star (f (y + u')) * f (y + v'))
      = (fun (_ : Fin d → Bool) y => star (g (y + t))) := by
    funext ω y
    exact key y
  rw [hfun]
  rw [mCubeSum_comp_add_right ν S (fun _ y => star (g y)) t]
  rw [mCubeSum_comp_star ν S (fun _ y => g y)]
  rw [norm_star, hg]

end

end Work.Peluse.SwapC
