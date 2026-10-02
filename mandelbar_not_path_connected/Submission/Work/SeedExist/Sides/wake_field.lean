/-
# The `wake` field of `RootParabolic`, from the two side-inputs

The `wake` field of `Work.EL.RootParabolic` (`Submission/Work/ELTop/Defs.lean`) is the
statement

`∀ k, 1 ≤ k → (T_c)^[k] 0 ∈ wakeSide hN z₁ ((k-1) % 5)`,

i.e. the `k`-th point of the critical orbit of the tricorn map `T_c z = conj z ^ 2 + c` lies in
the wake side `X_j` for `j = (k-1) % 5`.  This file derives it from the two inputs that the
area `SeedExist` obtains from the geometry of the sides:

* `himg` — the side-image relation `T_c '' X_j = X_{j+1}` for `j ≤ 3`;
* `hgc`  — the return of the `5`-fold iterate of the critical value: `(T_c^[5])^[m] c ∈ X_0`
  for every `m`.

The mathematics is the following.  Since `T_c 0 = c`, the point `(T_c)^[k] 0` equals
`(T_c)^[k-1] c`.  Write `k - 1 = r + 5 * ((k-1)/5)` with `r = (k-1) % 5 ≤ 4`; by
`hgc`, the point `(T_c)^[5 * ((k-1)/5)] c` lies in `X_0`, and the side-image relation
iterated `r ≤ 4` times (`himg` is only needed for `j ≤ 3`) puts its `r`-th iterate in `X_r`.

The formal proof keeps the indices as *variables* wherever an equality between two terms has to
be checked: reducing arithmetic on symbolic natural numbers (`Nat.mod`, `Nat.div`, `Nat.iterate`)
inside the (large) definition of `wakeSide` makes the elaborator unfold the whole side
definition.  Concretely, the index `(k-1) % 5` is first replaced by a fresh variable `r`, and the
iterate is then split with `Function.iterate_add_apply`.
-/
import Mathlib
import Submission.Work.SeedExist.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedExist.Sides

open LeanEval.ComplexAnalysis (Tantibar)

theorem wake_field {c : ℂ} {z₁ : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    (himg : ∀ j : ℕ, j ≤ 3 →
      LeanEval.ComplexAnalysis.Tantibar c '' Work.SeedExist.wakeSide hN z₁ j =
        Work.SeedExist.wakeSide hN z₁ (j + 1))
    (hgc : ∀ m : ℕ, (((LeanEval.ComplexAnalysis.Tantibar c)^[5])^[m]) c ∈ Work.SeedExist.wakeSide hN z₁ 0)
    (k : ℕ) (hk : 1 ≤ k) :
    (LeanEval.ComplexAnalysis.Tantibar c)^[k] 0 ∈ Work.SeedExist.wakeSide hN z₁ ((k - 1) % 5) := by
  -- The one-step side-image relation `T_c '' X_j ⊆ X_{j+1}`, for `j ≤ 3`.
  have step : ∀ j : ℕ, j ≤ 3 → ∀ x : ℂ, x ∈ Work.SeedExist.wakeSide hN z₁ j →
      Tantibar c x ∈ Work.SeedExist.wakeSide hN z₁ (j + 1) := by
    intro j hj x hx
    have h := Set.mem_image_of_mem (Tantibar c) hx
    rwa [himg j hj] at h
  -- Iterating it: points of `X_0` stay in the right side for four steps.
  have chain : ∀ r : ℕ, r ≤ 4 → ∀ x : ℂ, x ∈ Work.SeedExist.wakeSide hN z₁ 0 →
      (Tantibar c)^[r] x ∈ Work.SeedExist.wakeSide hN z₁ r := by
    intro r
    induction r with
    | zero => intro _ x hx; simpa using hx
    | succ r ih =>
      intro hr x hx
      have hxr : (Tantibar c)^[r] x ∈ Work.SeedExist.wakeSide hN z₁ r := ih (by omega) x hx
      have h := step r (by omega) ((Tantibar c)^[r] x) hxr
      simpa [Function.iterate_succ_apply'] using h
  -- The `5`-blocks of the critical orbit, by `hgc`.
  have hiter : ∀ m : ℕ, (Tantibar c)^[5 * m] c ∈ Work.SeedExist.wakeSide hN z₁ 0 := by
    intro m
    rw [Function.iterate_mul]
    exact hgc m
  have h0 : (Tantibar c) 0 = c := by simp [Tantibar]
  -- Abstract the index `(k-1) % 5` as a variable, so that all later index comparisons are
  -- syntactic.
  obtain ⟨r, hr, hrlt⟩ : ∃ r : ℕ, r = (k - 1) % 5 ∧ r < 5 :=
    ⟨_, rfl, Nat.mod_lt _ (by norm_num)⟩
  rw [← hr]
  -- `k = r + 5 * ((k-1)/5) + 1`, so `T_c^[k] 0 = T_c^[r] (T_c^[5 * ((k-1)/5)] c)`.
  have hk_eq : k = r + (5 * ((k - 1) / 5)).succ := by
    have hdec := Nat.mod_add_div (k - 1) 5
    omega
  rw [hk_eq, Function.iterate_add_apply, Function.iterate_succ_apply, h0]
  exact chain r (by omega) ((Tantibar c)^[5 * ((k - 1) / 5)] c) (hiter ((k - 1) / 5))

end Work.SeedExist.Sides
