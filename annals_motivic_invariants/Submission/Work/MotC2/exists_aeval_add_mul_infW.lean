/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotC2

# The chart-at-infinity coordinate ring is `L[u] + L[u]·w`

The chart-at-infinity coordinate ring `infCoordRing E = L[u, w]` (with `u = 1/x`,
`w = y/x²`) is spanned, over `L[u]`, by `1` and `w`: the Weierstrass relation
`w² + a₁uw + a₃u²w = u + a₂u² + a₄u³ + a₆u⁴` exhibits `w²` as an element of
`L[u] + L[u]·w`, so the set `L[u] + L[u]·w` is an `L`-subalgebra of `L(E)` containing `u`
and `w`, hence contains `L[u, w]`.

## Main results

* `infNum`, `infDen`: the polynomials `u + a₂u² + a₄u³ + a₆u⁴` and `-(a₁u + a₃u²)`.
* `infW_sq_decomp`: `w² = (u + a₂u² + a₄u³ + a₆u⁴) + (-(a₁u + a₃u²))·w`.
* `exists_aeval_add_mul_infW`: every element of `L[u, w]` is of the form `A(u) + B(u)·w`.

## Tags

elliptic curve, function field, chart at infinity, coordinate ring
-/

import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve.Affine

namespace Work.MotC2

variable {L : Type*} [Field L]

/-- The `A`-part `u + a₂u² + a₄u³ + a₆u⁴` of the chart-at-infinity Weierstrass relation. -/
noncomputable def infNum (E : WeierstrassCurve L) : Polynomial L :=
  X + C E.a₂ * X ^ 2 + C E.a₄ * X ^ 3 + C E.a₆ * X ^ 4

/-- The `B`-part `-(a₁u + a₃u²)` of the chart-at-infinity Weierstrass relation. -/
noncomputable def infDen (E : WeierstrassCurve L) : Polynomial L :=
  -(C E.a₁ * X + C E.a₃ * X ^ 2)

/-- The chart-at-infinity Weierstrass relation, solved for `w²`: this exhibits `w²` as an element
of `L[u] + L[u]·w`. -/
lemma infW_sq_decomp (E : WeierstrassCurve L) :
    (infW E) ^ 2 = aeval (infU E) (infNum E) + aeval (infU E) (infDen E) * infW E := by
  rw [infNum, infDen]
  simp only [map_add, map_mul, map_pow, map_neg, aeval_X, aeval_C]
  have h := infW_sq_relation E
  rw [← sub_eq_zero] at h ⊢
  linear_combination (norm := first | refl_ring1 | ring1) h

/-- The set `L[u] + L[u]·w` is closed under addition. -/
lemma decomp_add (E : WeierstrassCurve L) {x y : Func E}
    (hx : ∃ A B : Polynomial L, x = aeval (infU E) A + aeval (infU E) B * infW E)
    (hy : ∃ A B : Polynomial L, y = aeval (infU E) A + aeval (infU E) B * infW E) :
    ∃ A B : Polynomial L, x + y = aeval (infU E) A + aeval (infU E) B * infW E := by
  obtain ⟨A₁, B₁, h₁⟩ := hx
  obtain ⟨A₂, B₂, h₂⟩ := hy
  refine ⟨A₁ + A₂, B₁ + B₂, ?_⟩
  rw [h₁, h₂]
  simp only [map_add]
  first | refl_ring1 | ring

/-- The set `L[u] + L[u]·w` is closed under multiplication, by `infW_sq_decomp`. -/
lemma decomp_mul (E : WeierstrassCurve L) {x y : Func E}
    (hx : ∃ A B : Polynomial L, x = aeval (infU E) A + aeval (infU E) B * infW E)
    (hy : ∃ A B : Polynomial L, y = aeval (infU E) A + aeval (infU E) B * infW E) :
    ∃ A B : Polynomial L, x * y = aeval (infU E) A + aeval (infU E) B * infW E := by
  obtain ⟨A₁, B₁, h₁⟩ := hx
  obtain ⟨A₂, B₂, h₂⟩ := hy
  refine ⟨A₁ * A₂ + B₁ * B₂ * infNum E, A₁ * B₂ + A₂ * B₁ + B₁ * B₂ * infDen E, ?_⟩
  rw [h₁, h₂]
  simp only [map_add, map_mul]
  linear_combination (norm := first | refl_ring1 | ring1) (aeval (infU E) B₁ * aeval (infU E) B₂) * infW_sq_decomp E

/-- Every element of the chart-at-infinity coordinate ring `L[u, w]` is of the form
`A(u) + B(u)·w` with `A, B ∈ L[X]`: the subalgebra `L[u, w]` is generated over `L` by `u` and `w`,
and `w²` lies in `L[u] + L[u]·w` by the Weierstrass relation. -/
theorem exists_aeval_add_mul_infW (L : Type*) [Field L] (E : WeierstrassCurve L)
    (f : Work.MotC2.infCoordRing E) :
    ∃ A B : Polynomial L, (f : Work.MotC2.Func E) =
      Polynomial.aeval (Work.MotC2.infU E) A +
        Polynomial.aeval (Work.MotC2.infU E) B * Work.MotC2.infW E := by
  refine Algebra.adjoin_induction (p := fun g _ =>
      ∃ A B : Polynomial L, g = aeval (infU E) A + aeval (infU E) B * infW E) ?_ ?_ ?_ ?_ f.2
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨X, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  · intro c
    exact ⟨C c, 0, by simp⟩
  · intro x y _ _ hx hy
    exact decomp_add E hx hy
  · intro x y _ _ hx hy
    exact decomp_mul E hx hy

end Work.MotC2
