import Mathlib
import Submission.Work.SeedExist.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The orbit of a parabolic `T_c`-period-`5` point avoids the critical value `0`

Let `c, z₁ : ℂ` with `(T_c)^[5] z₁ = z₁` (`T_c = Tantibar c`, `z ↦ z̄² + c`) and with the
multiplier of the holomorphic second return map `(T_c)^{10} = (Tsq c)^[5]` at `z₁` equal to
`1`.  Then none of the first five points of the `T_c`-orbit of `z₁` is the critical value `0`.

The mathematical content is the standard "the critical value is not on a parabolic cycle"
observation, transported through the holomorphic second iterate:

* `Tsq c := (T_c)²` is the polynomial `z ↦ (z² + c̄)² + c`, whose critical point `0` is also
  the critical point of `T_c`;
* the multiplier of the second return map is a product of `(Tsq c)'` over the `Tsq`-cycle of
  `z₁`, and `(Tsq c)'(0) = 0`;
* since `5` is odd, the `Tsq`-cycle of `z₁` is exactly the whole `T_c`-cycle (with its points
  reordered), so if `0` lay on that cycle the product — hence the multiplier — would be `0`,
  contradicting `hmu`.

The last point is the only place where the specific values `5` and `i ≤ 4` are used; it is
handled by a finite case distinction.
-/

namespace Work.SeedExist.Pair

open Function
open LeanEval.ComplexAnalysis (Tantibar)

/-- `Tsq c` is the second iterate of `Tantibar c` (as functions `ℂ → ℂ`). -/
lemma Tsq_eq_iterate_two (c : ℂ) : Work.Landing.Tsq c = (Tantibar c)^[2] := by
  funext z
  simp [Work.Landing.Tsq, LeanEval.ComplexAnalysis.Tantibar, Function.iterate_succ_apply',
    map_add, map_pow]

/-- `Tsq c` is complex differentiable (it is a polynomial in `z`). -/
lemma differentiable_tsq (c : ℂ) : Differentiable ℂ (Work.Landing.Tsq c) := by
  unfold Work.Landing.Tsq; fun_prop

/-- The critical point `0` of `Tsq c` is a critical point: `(Tsq c)'(0) = 0`. -/
lemma deriv_tsq_zero (c : ℂ) : deriv (Work.Landing.Tsq c) 0 = 0 := by
  unfold Work.Landing.Tsq; simp

/-- **Chain rule for iterates**: for a complex-differentiable `f`, the derivative of `f^[n]`
at `x` is the product of `deriv f` over the orbit `x, f x, …, f^[n-1] x`. -/
lemma deriv_iterate_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) (x : ℂ) :
    deriv (f^[n]) x = ∏ i ∈ Finset.range n, deriv f ((f^[i]) x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ']
    rw [deriv_comp x hf.differentiableAt ((hf.iterate n).differentiableAt)]
    rw [ih x, Finset.prod_range_succ]; ring

/-- If the `T_c`-orbit of `z₁` (a point fixed by `(T_c)^[5]`) meets `0` within the first five
steps, then the `Tsq`-orbit of `z₁` (a cycle of length dividing `5`) also meets `0` within the
first five steps.  This is the finite combinatorial input of `iterate_ne_zero`. -/
lemma exists_tsq_iterate_eq_zero {c z₁ : ℂ} (hg : (Tantibar c)^[5] z₁ = z₁) {i : ℕ} (hi : i ≤ 4)
    (h0 : (Tantibar c)^[i] z₁ = 0) :
    ∃ k ∈ Finset.range 5, (Work.Landing.Tsq c)^[k] z₁ = 0 := by
  have hTsq : ∀ k : ℕ, (Work.Landing.Tsq c)^[k] z₁ = (Tantibar c)^[2 * k] z₁ := by
    intro k
    rw [Tsq_eq_iterate_two, ← Function.iterate_mul]
  have hred : ∀ n : ℕ, (Tantibar c)^[n + 5] z₁ = (Tantibar c)^[n] z₁ := by
    intro n; rw [Function.iterate_add_apply, hg]
  interval_cases i
  · exact ⟨0, by decide, by simpa using h0⟩
  · refine ⟨3, by decide, ?_⟩
    rw [hTsq 3]
    show (Tantibar c)^[1 + 5] z₁ = 0
    rw [hred 1, h0]
  · exact ⟨1, by decide, by rw [hTsq 1]; simpa using h0⟩
  · refine ⟨4, by decide, ?_⟩
    rw [hTsq 4]
    show (Tantibar c)^[3 + 5] z₁ = 0
    rw [hred 3, h0]
  · exact ⟨2, by decide, by rw [hTsq 2]; simpa using h0⟩

theorem iterate_ne_zero {c z₁ : ℂ}
    (hg : (LeanEval.ComplexAnalysis.Tantibar c)^[5] z₁ = z₁)
    (hmu : Work.Landing.multiplier2 c 5 z₁ = 1)
    (i : ℕ) (hi : i ≤ 4) :
    (LeanEval.ComplexAnalysis.Tantibar c)^[i] z₁ ≠ 0 := by
  intro h0
  obtain ⟨k, hkmem, hk0⟩ := exists_tsq_iterate_eq_zero hg hi h0
  have hprod : deriv ((Work.Landing.Tsq c)^[5]) z₁ =
      ∏ j ∈ Finset.range 5, deriv (Work.Landing.Tsq c) ((Work.Landing.Tsq c)^[j] z₁) :=
    deriv_iterate_of_differentiable (differentiable_tsq c) 5 z₁
  have hz : deriv ((Work.Landing.Tsq c)^[5]) z₁ = 0 := by
    rw [hprod]
    exact Finset.prod_eq_zero hkmem (by rw [hk0, deriv_tsq_zero])
  unfold Work.Landing.multiplier2 at hmu
  rw [hz] at hmu
  exact zero_ne_one hmu

end Work.SeedExist.Pair
