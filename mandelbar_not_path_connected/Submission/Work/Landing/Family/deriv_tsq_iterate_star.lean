import Mathlib
import Submission.Work.Landing.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The derivative of the `n`-th iterate of `Tsq` under complex conjugation

`Tsq c z = (z² + c̄)² + c` is the holomorphic second iterate of the antiholomorphic
quadratic `T_c(z) = z̄² + c`.  Complex conjugation intertwines the two maps
`Tsq c` and `Tsq (c̄)` (`Tsq c (z̄) = conj (Tsq (c̄) z)`), hence also their iterates
(`Tsq_iterate_star_aux`).  The main result here is the corresponding statement for the
derivatives:

`deriv ((Tsq c)^[n]) z = conj (deriv ((Tsq (c̄))^[n]) (conj z))`.

This is what allows one to transfer multiplier estimates at a point of the tricorn family
to the mirror-image parameter `c̄`; it is used in the landing theory for `T_c`
(see `Submission/Work/Landing/Land.lean`).

The proof is an induction on `n`: the chain rule for the holomorphic polynomial `Tsq c`,
together with the conjugacy of the first derivatives
`deriv (Tsq c) (conj w) = conj (deriv (Tsq (c̄)) w)`
(an immediate consequence of the explicit formula `deriv (Tsq c) z = 4 z (z² + c̄)`).
-/

namespace Work.Landing.Family

/-- The derivative of the holomorphic second iterate `Tsq c z = (z² + c̄)² + c`. -/
lemma deriv_Tsq_formula (c z : ℂ) : deriv (Work.Landing.Tsq c) z = 4 * z * (z ^ 2 + star c) := by
  change deriv ((fun w : ℂ => (w ^ 2 + star c) ^ 2) + fun _ : ℂ => c) z =
    4 * z * (z ^ 2 + star c)
  rw [deriv_add (by fun_prop) (differentiableAt_const c), deriv_const, add_zero]
  change deriv (fun w : ℂ => (w ^ 2 + star c) ^ 2) z = 4 * z * (z ^ 2 + star c)
  rw [deriv_fun_pow (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w ^ 2 + star c) z) 2]
  change (2 : ℂ) * (z ^ 2 + star c) ^ (2 - 1) *
      deriv ((fun w : ℂ => w ^ 2) + fun _ : ℂ => star c) z = 4 * z * (z ^ 2 + star c)
  rw [deriv_add (by fun_prop) (differentiableAt_const (star c)), deriv_const, add_zero]
  rw [deriv_fun_pow (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w) z) 2]
  rw [show deriv (fun w : ℂ => w) z = 1 from deriv_id z]
  norm_num
  ring

/-- `Tsq c` is a polynomial, hence entire. -/
lemma differentiable_Tsq (c : ℂ) : Differentiable ℂ (Work.Landing.Tsq c) := by
  unfold Work.Landing.Tsq
  fun_prop

/-- The chain rule for complex differentiable functions `ℂ → ℂ`, stated in the exact shape
in which it is used below (this avoids instance-mismatch issues of the Mathlib statement
when rewriting). -/
lemma deriv_comp_local (f g : ℂ → ℂ) (x : ℂ)
    (hf : DifferentiableAt ℂ f (g x)) (hg : DifferentiableAt ℂ g x) :
    deriv (f ∘ g) x = deriv f (g x) * deriv g x :=
  deriv_comp (x := x) (h := g) (h₂ := f) hf hg

/-- Complex conjugation intertwines `Tsq c` and `Tsq (c̄)`:
`Tsq c (conj z) = conj (Tsq (c̄) z)`. -/
lemma Tsq_star_conj (c z : ℂ) :
    Work.Landing.Tsq c (star z) = star (Work.Landing.Tsq (star c) z) := by
  simp only [Work.Landing.Tsq, star_add, star_pow, star_star]

/-- The first derivative of `Tsq` is conjugation-equivariant:
`deriv (Tsq c) (conj w) = conj (deriv (Tsq (c̄)) w)`. -/
lemma deriv_Tsq_star_conj (c w : ℂ) :
    deriv (Work.Landing.Tsq c) (star w) = star (deriv (Work.Landing.Tsq (star c)) w) := by
  rw [deriv_Tsq_formula, deriv_Tsq_formula]
  simp only [star_mul, star_add, star_pow, star_star, star_ofNat]
  ring

/-- Iterated form of `Tsq_star_conj`: conjugation intertwines the `n`-th iterates. -/
lemma Tsq_iterate_star_aux (c z : ℂ) (n : ℕ) :
    (Work.Landing.Tsq c)^[n] (star z) = star ((Work.Landing.Tsq (star c))^[n] z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Tsq_star_conj, Function.iterate_succ_apply']

/-- The derivative of the `n`-th iterate of `Tsq c` at `z` is the conjugate of the derivative
of the `n`-th iterate of `Tsq (c̄)` at `z̄`. -/
theorem deriv_tsq_iterate_star (c z : ℂ) (n : ℕ) :
    deriv ((Work.Landing.Tsq c)^[n]) z =
      star (deriv ((Work.Landing.Tsq (star c))^[n]) (star z)) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ',
      deriv_comp_local (f := Work.Landing.Tsq c) (g := (Work.Landing.Tsq c)^[n]) (x := z)
        (by exact (differentiable_Tsq c).differentiableAt)
        (by exact (differentiable_Tsq c).iterate n |>.differentiableAt)]
    have hz : (Work.Landing.Tsq c)^[n] z = star ((Work.Landing.Tsq (star c))^[n] (star z)) := by
      simpa using Tsq_iterate_star_aux c (star z) n
    rw [hz, ih, deriv_Tsq_star_conj, ← star_mul, mul_comm,
      ← deriv_comp_local (f := Work.Landing.Tsq (star c)) (g := (Work.Landing.Tsq (star c))^[n])
        (x := star z)
        (by exact (differentiable_Tsq (star c)).differentiableAt)
        (by exact (differentiable_Tsq (star c)).iterate n |>.differentiableAt)]
    rw [← Function.iterate_succ']

end Work.Landing.Family
