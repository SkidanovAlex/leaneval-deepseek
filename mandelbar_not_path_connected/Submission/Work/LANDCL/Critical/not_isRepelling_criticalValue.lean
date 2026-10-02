import Mathlib
import Submission.Work.Landing.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The critical value of `T_c` is never a repelling periodic point

The critical value of the antiholomorphic quadratic `T_c(z) = z̄² + c` is
`c = T_c(0)`.  We prove here that this point is never a *repelling* periodic point of `T_c`:

`¬ Work.Landing.IsRepelling c k c` for every parameter `c` and every period `k`.

The mechanism is the classical one.  Since `T_c z = z̄² + c`, the equation `T_c z = c` reads
`z̄² = 0`, so the critical value `c` has the critical point `0` as its *unique* preimage
(`Tantibar_eq_c_iff`).  Hence if `c` is periodic of period `k`, then
`(T_c)^[k-1] c = 0`: the cycle through `c` runs through the critical point.  Consequently the
holomorphic second return map `(Tsq c)^[k] = (T_c)^[2k]` has a critical point on the orbit of
`c`: the chain rule for the derivative of an iterate (`deriv_iterate_eq_prod`) exhibits the
vanishing factor, and the multiplier `multiplier2 c k c = deriv ((Tsq c)^[k]) c` is `0`.  A
repelling periodic point has multiplier of modulus `> 1` (`1 < ‖multiplier2 c k c‖`), so this is
impossible.

This is the elementary half of the reduction recorded in `Submission/Work/LANDCL/Defs.lean`: a
parameter ray cannot land at a repelling periodic point which is also the critical value.

The file is deliberately self-contained — it imports only `Mathlib` and the module
`Submission.Work.Landing.Core` that *defines* `Work.Landing.IsRepelling` — so that the statement
is available with no other part of the development as a dependency.  The two small facts about
`Tsq c` reproved here (`Tantibar_eq_c_iff`, `Tsq_deriv`) also occur as
`Work.LANDCL.Deriv.preimage_criticalValue` and `Work.LANDCL.Deriv.tsq_deriv`.
-/

noncomputable section

namespace Work.LANDCL.Critical

open Function
open LeanEval.ComplexAnalysis (Tantibar)

/-! ## `Tsq c = (T_c)^[2]` and its iterates -/

/-- The holomorphic second iterate `Tsq c` of the antiholomorphic quadratic `T_c` is the second
iterate of `T_c` as a function. -/
lemma Tsq_eq_Tantibar_iterate_two (c : ℂ) : Work.Landing.Tsq c = (Tantibar c)^[2] := by
  funext z
  simp [Work.Landing.Tsq, Tantibar, Function.iterate_succ]

/-- The iterates of the second return map are the even iterates of `T_c`:
`(Tsq c)^[n] = (T_c)^[2n]`. -/
lemma Tsq_iterate_apply (c : ℂ) (n : ℕ) (z : ℂ) :
    (Work.Landing.Tsq c)^[n] z = (Tantibar c)^[2 * n] z := by
  rw [Tsq_eq_Tantibar_iterate_two, ← Function.iterate_mul]

/-- `T_c` applied to the `n`-th iterate is the `(n+1)`-st iterate. -/
lemma Tantibar_iterate_succ (c : ℂ) (n : ℕ) (z : ℂ) :
    Tantibar c ((Tantibar c)^[n] z) = (Tantibar c)^[n + 1] z :=
  (Function.iterate_succ_apply' (Tantibar c) n z).symm

/-! ## The critical value `c` and its preimage -/

/-- The critical value `c = T_c(0)` of `T_c` has the critical point `0` as its unique preimage. -/
lemma Tantibar_eq_c_iff (c z : ℂ) : Tantibar c z = c ↔ z = 0 := by
  rw [Tantibar, add_eq_right, sq_eq_zero_iff, starRingEnd_apply, star_eq_zero]

/-! ## The derivative of `Tsq c` -/

/-- The conjugate of `T_c w` is the factor `w² + c̄` occurring in the derivative of `Tsq c`. -/
lemma star_Tantibar (c w : ℂ) : star (Tantibar c w) = w ^ 2 + star c := by
  rw [Tantibar]
  simp

/-- The derivative of the second iterate: `deriv (Tsq c) w = 4 w (w² + c̄)`. -/
lemma Tsq_deriv (c w : ℂ) :
    deriv (Work.Landing.Tsq c) w = 4 * w * (w ^ 2 + star c) := by
  have h : HasDerivAt (Work.Landing.Tsq c) (4 * w * (w ^ 2 + star c)) w := by
    unfold Work.Landing.Tsq
    have h1 : HasDerivAt (fun z : ℂ => z ^ 2 + star c) (2 * w) w := by
      simpa using ((hasDerivAt_id w).pow 2).const_add (star c)
    have h3 : HasDerivAt (fun z : ℂ => (z ^ 2 + star c) ^ 2 + c)
        (↑2 * (w ^ 2 + star c) ^ (2 - 1) * (2 * w)) w := (h1.pow 2).add_const c
    convert h3 using 1
    norm_num
    ring
  exact h.deriv

/-- `deriv (Tsq c) w = 4 w · conj (T_c w)`: the derivative vanishes exactly at the critical
points `w = 0` and at the preimages of the critical point `0` under `T_c`. -/
lemma Tsq_deriv_eq (c w : ℂ) :
    deriv (Work.Landing.Tsq c) w = 4 * w * star (Tantibar c w) := by
  rw [Tsq_deriv, star_Tantibar]

/-- The critical point `0` of `Tsq c` is a critical point: `deriv (Tsq c) 0 = 0`. -/
lemma Tsq_deriv_zero (c : ℂ) : deriv (Work.Landing.Tsq c) 0 = 0 := by
  rw [Tsq_deriv]
  ring

/-- Every preimage `w` of the critical point `0` under `T_c` is a critical point of `Tsq c`. -/
lemma Tsq_deriv_eq_zero_of_Tantibar_eq_zero (c : ℂ) {w : ℂ} (h : Tantibar c w = 0) :
    deriv (Work.Landing.Tsq c) w = 0 := by
  rw [Tsq_deriv_eq, h, star_zero, mul_zero]

/-- `Tsq c` is an entire function (it is a polynomial). -/
lemma differentiable_Tsq (c : ℂ) : Differentiable ℂ (Work.Landing.Tsq c) := by
  show Differentiable ℂ (fun z : ℂ => (z ^ 2 + star c) ^ 2 + c)
  fun_prop

/-! ## The chain rule for iterates -/

/-- The derivative of an iterate of an entire function is the product of the derivatives along
the orbit (the chain rule). -/
lemma deriv_iterate_eq_prod {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) (z : ℂ) :
    deriv (f^[n]) z = ∏ i ∈ Finset.range n, deriv f (f^[i] z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ', deriv_comp z hf.differentiableAt ((hf.iterate n).differentiableAt),
      ih, Finset.prod_range_succ]
    ring

/-- **If the orbit of `x` under an entire map `g` reaches a critical point `x₀` of `g` before
time `n`, then `deriv (g^[n]) x = 0`.**  Indeed the product formula for the derivative of an
iterate contains the factor `deriv g (g^[j] x) = deriv g x₀ = 0`. -/
lemma deriv_iterate_eq_zero_of_deriv_eq_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {x x₀ : ℂ} {j n : ℕ} (hj : g^[j] x = x₀) (hjn : j < n) (h0 : deriv g x₀ = 0) :
    deriv (g^[n]) x = 0 := by
  rw [deriv_iterate_eq_prod hg n x]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hjn) (by rw [hj, h0])

/-! ## The critical value is not a repelling periodic point -/

theorem not_isRepelling_criticalValue (c : ℂ) (k : ℕ) :
    ¬ Work.Landing.IsRepelling c k c := by
  rintro ⟨⟨hkpos, hiter⟩, hmult⟩
  obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [hm] at hiter hmult
  -- the cycle of `c` runs through the critical point `0`
  have hpre : (Tantibar c)^[m] c = 0 := by
    apply (Tantibar_eq_c_iff c _).mp
    rw [Tantibar_iterate_succ]
    exact hiter
  have hdiff : Differentiable ℂ (Work.Landing.Tsq c) := differentiable_Tsq c
  -- the holomorphic second return map has a critical point on the orbit of `c`
  have hzero : Work.Landing.multiplier2 c (m + 1) c = 0 := by
    show deriv ((Work.Landing.Tsq c)^[m + 1]) c = 0
    rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
    · -- `m = t + t` is even: the `t`-th iterate of `Tsq c` is the critical point `0`
      refine deriv_iterate_eq_zero_of_deriv_eq_zero hdiff (x := c) (x₀ := 0) (j := t)
        (n := m + 1) ?_ (by omega) (Tsq_deriv_zero c)
      rw [Tsq_iterate_apply, show 2 * t = m from by omega]
      exact hpre
    · -- `m = 2 * t + 1` is odd: the `t`-th iterate of `Tsq c` is a preimage of `0` under `T_c`
      refine deriv_iterate_eq_zero_of_deriv_eq_zero hdiff (x := c)
        (x₀ := (Work.Landing.Tsq c)^[t] c) (j := t) (n := m + 1) rfl (by omega) ?_
      apply Tsq_deriv_eq_zero_of_Tantibar_eq_zero
      rw [Tsq_iterate_apply, Tantibar_iterate_succ,
        show 2 * t + 1 = m from by omega]
      exact hpre
  rw [hzero, norm_zero] at hmult
  exact absurd hmult (by norm_num)

end Work.LANDCL.Critical
