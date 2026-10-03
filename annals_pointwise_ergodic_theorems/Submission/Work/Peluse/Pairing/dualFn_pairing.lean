/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.Tools.dualFn_supportIn

/-!
# The dual-function pairing identity for Peluse's bilinear average

`LambdaZ N₀ N P f₀ f₁ f₂` is the bilinear average
`(1/(N₀ N)) ∑_x f₀(x) ∑_{y ∈ [N]} f₁(x + y) f₂ (x + P(y))`, and `dualFn N P f₀ f₁` is Peluse's
dual function `x ↦ (1/N) ∑_{y ∈ [N]} f₀ (x - P(y)) f₁ (x + y - P(y))`.  The identity proved here,

`Λ^{N₀,N}(f₀,f₁,f₂) = (1/N₀) ∑_x dualFn(x) f₂(x)`,

is Peluse's duality (Corollary 3.8) in the case `ℓ = m = 2`, `P₁ = X`: it is nothing but the change
of variables `x ↦ x + P(y)` in the double sum

`∑_{x,y} f₀(x - P(y)) f₁(x + y - P(y)) f₂(x) = ∑_{x,y} f₀(x) f₁(x+y) f₂(x + P(y))`.

Because `f₀` has finite support both sides are really finite sums, so the identity is an elementary
reindexing.  All the care is in the `tsum`/`Finset` bookkeeping: `Summable.tsum_finsetSum` to swap
the finite `y`-sum with the infinite `x`-sum (both directions) and `Equiv.tsum_eq` for the shift
`x ↦ x + P(y)`.  No positivity hypothesis on `N₀`, `N` is needed: when `N = 0` the `y`-range is
empty and both sides vanish.

## Contents

* `K` — the joint integrand `f₀ x * (f₁ (x + y) * f₂ (x + P y))` shared by `LambdaZ` and `dualFn`;
* `natAbs_lt_of_not_mem_Icc`, `summable_of_natAbs` — summability from finite support;
* `natAbs_sub_eval_gt` — the shift `x ↦ x - P y` does not destroy support;
* `dualFn_pairing` — the identity.
-/

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace Work.Peluse.Pairing

noncomputable section

/-- The joint integrand of `LambdaZ` and `dualFn`: `f₀ x * (f₁ (x + y) * f₂ (x + P y))`.

The point of writing it with the argument `x` and the shift `y` separated is that the change of
variables `x ↦ x - P(y)` sends the `LambdaZ`-integrand at `(x,y)` to the `dualFn`-integrand at
`(x - P(y), y)`. -/
private def K (P : Polynomial ℤ) (f₀ f₁ f₂ : ℤ → ℂ) (x y : ℤ) : ℂ :=
  f₀ x * (f₁ (x + y) * f₂ (x + P.eval y))

/-- If `x` lies outside the symmetric interval `[-R, R]` then `R < x.natAbs`. -/
private lemma natAbs_lt_of_not_mem_Icc {R : ℕ} {x : ℤ}
    (h : ¬ (-(R : ℤ) ≤ x ∧ x ≤ R)) : R < x.natAbs := by
  have h2 : ¬ (x.natAbs ≤ R) := by
    intro hle
    apply h
    have h3 : |x| ≤ (R : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hle
    exact abs_le.mp h3
  omega

/-- A function on `ℤ` which vanishes outside `[-R, R]` is summable. -/
private lemma summable_of_natAbs {R : ℕ} {g : ℤ → ℂ}
    (h : ∀ x : ℤ, R < x.natAbs → g x = 0) : Summable g := by
  apply summable_of_hasFiniteSupport
  refine (Set.finite_Icc (-(R : ℤ)) (R : ℤ)).subset ?_
  intro x hx
  rw [Set.mem_Icc]
  by_contra hcon
  exact (Function.mem_support.mp hx) (h x (natAbs_lt_of_not_mem_Icc hcon))

/-- For `R = dSup P N₀ N` and `y ∈ [1, N]`, `|x| > R` forces `|x - P(y)| > N₀`, i.e. the shifted
point still misses the support `[-N₀, N₀]` of `f₀`. -/
private lemma natAbs_sub_eval_gt {N₀ N : ℕ} (P : Polynomial ℤ) {y : ℕ}
    (hy : y ∈ Finset.Icc 1 N) {x : ℤ} (hx : Work.Peluse.dSup P N₀ N < x.natAbs) :
    N₀ < (x - P.eval (y : ℤ)).natAbs := by
  have hyN : (y : ℤ) ≤ (N : ℤ) := by
    have h := (Finset.mem_Icc.mp hy).2
    exact_mod_cast h
  have hP : |P.eval (y : ℤ)| ≤ ((Work.Peluse.polySup P N : ℕ) : ℤ) :=
    Work.Peluse.Tools.eval_abs_le_polySup P (by positivity) hyN
  have hx' : (N₀ : ℤ) + ((Work.Peluse.polySup P N : ℕ) : ℤ) < |x| := by
    have h : ((Work.Peluse.dSup P N₀ N : ℕ) : ℤ) < ((x.natAbs : ℕ) : ℤ) := by
      exact_mod_cast hx
    rw [Int.natCast_natAbs] at h
    rw [Work.Peluse.dSup] at h
    push_cast at h
    linarith
  have h1 : (N₀ : ℤ) < |x - P.eval (y : ℤ)| := by
    have h2 := abs_sub_abs_le_abs_sub x (P.eval (y : ℤ))
    linarith
  have h3 : (N₀ : ℤ) < (((x - P.eval (y : ℤ)).natAbs : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]
    exact h1
  exact_mod_cast h3

theorem dualFn_pairing {N₀ N : ℕ} (P : Polynomial ℤ) (f₀ f₁ f₂ : ℤ → ℂ)
    (h₀ : Work.Peluse.SupportIn f₀ N₀) :
    Work.Peluse.LambdaZ N₀ N P f₀ f₁ f₂
      = ((N₀ : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.dualFn N P f₀ f₁ x * f₂ x := by
  classical
  -- the common canonical form of both sides
  set W : ℂ := ∑' z : ℤ, ∑ y ∈ Finset.Icc 1 N, K P f₀ f₁ f₂ z (y : ℤ) with hW
  -- the average `LambdaZ`, in the canonical form
  have hleft : Work.Peluse.LambdaZ N₀ N P f₀ f₁ f₂ = ((N₀ : ℂ) * (N : ℂ))⁻¹ * W := by
    rw [hW, Work.Peluse.LambdaZ]
    apply congrArg (fun t : ℂ => ((N₀ : ℂ) * (N : ℂ))⁻¹ * t)
    refine tsum_congr (fun x => ?_)
    rw [Finset.mul_sum]
    simp only [K]
  -- the dual pairing, in the same canonical form
  have hdual : (∑' x : ℤ, Work.Peluse.dualFn N P f₀ f₁ x * f₂ x) = (N : ℂ)⁻¹ * W := by
    have hstep : ∀ x : ℤ, Work.Peluse.dualFn N P f₀ f₁ x * f₂ x
        = (N : ℂ)⁻¹ * ∑ y ∈ Finset.Icc 1 N, K P f₀ f₁ f₂ (x - P.eval (y : ℤ)) (y : ℤ) := by
      intro x
      have h1 : Work.Peluse.dualFn N P f₀ f₁ x * f₂ x
          = (N : ℂ)⁻¹ * ((∑ y ∈ Finset.Icc 1 N,
              f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ))) * f₂ x) := by
        rw [Work.Peluse.dualFn]
        ring
      rw [h1, Finset.sum_mul]
      apply congrArg (fun t : ℂ => (N : ℂ)⁻¹ * t)
      refine Finset.sum_congr rfl (fun y _ => ?_)
      simp only [K]
      have e1 : (x - P.eval (y : ℤ)) + (y : ℤ) = x + (y : ℤ) - P.eval (y : ℤ) := by ring
      have e2 : (x - P.eval (y : ℤ)) + P.eval (y : ℤ) = x := by ring
      rw [e1, e2]
      ring
    rw [tsum_congr hstep, tsum_mul_left, hW]
    apply congrArg (fun t : ℂ => (N : ℂ)⁻¹ * t)
    -- the fibres of the `y`-sum are summable
    have hfib1 : ∀ y ∈ Finset.Icc 1 N,
        Summable (fun x : ℤ => K P f₀ f₁ f₂ (x - P.eval (y : ℤ)) (y : ℤ)) := by
      intro y hy
      apply summable_of_natAbs (R := Work.Peluse.dSup P N₀ N)
      intro x hx
      simp only [K]
      rw [h₀ (x - P.eval (y : ℤ)) (natAbs_sub_eval_gt (N₀ := N₀) (N := N) P hy hx)]
      ring
    have hfib2 : ∀ y ∈ Finset.Icc 1 N,
        Summable (fun z : ℤ => K P f₀ f₁ f₂ z (y : ℤ)) := by
      intro y hy
      apply summable_of_natAbs (R := N₀)
      intro z hz
      simp only [K]
      rw [h₀ z hz]
      ring
    -- the shift `x ↦ x - P y` is a bijection of `ℤ`
    have hreindex : ∀ y ∈ Finset.Icc 1 N,
        (∑' x : ℤ, K P f₀ f₁ f₂ (x - P.eval (y : ℤ)) (y : ℤ))
          = ∑' z : ℤ, K P f₀ f₁ f₂ z (y : ℤ) := by
      intro y _
      have h := Equiv.tsum_eq (Equiv.addRight (P.eval (y : ℤ)))
        (fun x : ℤ => K P f₀ f₁ f₂ (x - P.eval (y : ℤ)) (y : ℤ))
      simpa [Equiv.coe_addRight, add_sub_cancel_right] using h.symm
    rw [Summable.tsum_finsetSum (s := Finset.Icc 1 N)
      (f := fun (y : ℕ) (x : ℤ) => K P f₀ f₁ f₂ (x - P.eval (y : ℤ)) (y : ℤ)) hfib1]
    refine Eq.trans (Finset.sum_congr rfl hreindex) ?_
    exact (Summable.tsum_finsetSum (s := Finset.Icc 1 N)
      (f := fun (y : ℕ) (z : ℤ) => K P f₀ f₁ f₂ z (y : ℤ)) hfib2).symm
  rw [hleft, hdual, mul_inv]
  ring

end

end Work.Peluse.Pairing
