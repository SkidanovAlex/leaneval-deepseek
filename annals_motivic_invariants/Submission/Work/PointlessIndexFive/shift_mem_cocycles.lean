/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.PointlessIndexFive
-/
import Mathlib
import Submission.Work.PointlessIndexFive.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The coboundaries lie in the cocycles: `N(σy - y) = 0`

For a quintic twist `D` — an elliptic curve `E/𝕜` with a rational point `P` of exact order `5`,
`j ≠ 1728`, and a cyclic extension `L/𝕜` of degree `5` with generator `σ` — the twist group of the
paper's Lemma `lem:torsors` is the Galois cohomology group

  `H¹(ℤ/5, E(L)) = ker N / (σ - 1)E(L)`,   `N = 1 + σ + σ² + σ³ + σ⁴`,

as realised in `Work.TorsorExistence.Twist`.  This file proves that the denominator is contained in
the numerator, i.e. that the image of the shift `σ - 1` is annihilated by the norm:

  `N(σy) = N(y)` for every `y ∈ E(L)`.

Indeed `N(σy - y) = σ⁵y - y`, because the five summands of the norm permute cyclically under `σ`
(a telescoping sum in the abelian group `E(L)`), and `σ⁵ = 1` because `σ` generates the Galois
group of the degree-`5` extension `L/𝕜`.  Hence `N(σy - y) = 0`, which is the statement that
`(σ - 1)E(L) ⊆ ker N`.

The key input is that `σ` acts on `E(L)` through the algebra automorphism `D.ext.gen` of `L`
(`D.galMap = Point.map D.ext.gen`), so that the iterate `σ^[n]` is `Point.map (D.ext.gen ^ n)` and
the fifth iterate is the identity.  The latter is `Mathlib`'s missing "`Point.map` is compatible
with composition", in iterate form (`galMap_iterate` below); the telescoping itself is `abel`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve

namespace Work.PointlessIndexFive

/-- The identity algebra homomorphism of `L` over `𝕜` induces the identity map on `E(L)`.
(This is `WeierstrassCurve.Affine.Point.map_id` for the base `𝕜` rather than the base `L`: the
identity of `L` is an algebra homomorphism over `𝕜`, and `Point.map` only sees the underlying
function.) -/
theorem pointMap_algHom_id {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜)
    (P : D.LPoints) :
    WeierstrassCurve.Affine.Point.map (W' := D.E) (AlgHom.id 𝕜 D.ext.L) P = P := by
  cases P <;> rfl

/-- The action of `σ^[n]` on `E(L)` corresponds to the `n`-th power of the algebra automorphism
`D.ext.gen` of `L`: the iterate of `Point.map (gen)` is `Point.map (gen ^ n)`.  This is the iterate
form of `WeierstrassCurve.Affine.Point.map_map`, made explicit for the endomorphism `gen` of `L`.

We work with the algebra-homomorphism power `(gen : L →ₐ[𝕜] L) ^ n` rather than the group power in
`L ≃ₐ[𝕜] L`, because `Point.map` consumes an algebra homomorphism; the two are identified in
`galMap_five_apply`. -/
theorem galMap_iterate {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) (n : ℕ)
    (P : D.LPoints) :
    (D.galMap^[n]) P = WeierstrassCurve.Affine.Point.map (W' := D.E)
      ((D.ext.gen : D.ext.L →ₐ[𝕜] D.ext.L) ^ n) P := by
  induction n with
  | zero =>
    -- `σ^[0] = id` and `gen ^ 0 = 1 = AlgHom.id`, whose induced map on points is the identity.
    rw [Function.iterate_zero_apply]
    have : ((D.ext.gen : D.ext.L →ₐ[𝕜] D.ext.L) ^ 0) = AlgHom.id 𝕜 D.ext.L := by
      ext y
      simp
    rw [this, pointMap_algHom_id D]
  | succ n ih =>
    -- `σ^[n+1] = σ ∘ σ^[n]`, and `Point.map` turns composition of algebra homomorphisms into
    -- composition of the induced maps.
    rw [Function.iterate_succ_apply', ih]
    rw [show D.galMap = WeierstrassCurve.Affine.Point.map (W' := D.E)
        (D.ext.gen : D.ext.L →ₐ[𝕜] D.ext.L) from rfl]
    rw [WeierstrassCurve.Affine.Point.map_map]
    have hcomp : ((D.ext.gen : D.ext.L →ₐ[𝕜] D.ext.L).comp
        ((D.ext.gen : D.ext.L →ₐ[𝕜] D.ext.L) ^ n))
        = (D.ext.gen : D.ext.L →ₐ[𝕜] D.ext.L) ^ (n + 1) := by
      ext y
      rw [AlgHom.comp_apply, pow_succ', AlgHom.mul_apply]
    rw [hcomp]

/-- `σ` has order `5`: since `σ = D.ext.gen` generates the Galois group of the degree-`5`
extension `L/𝕜`, the fifth iterate of `galMap` is the identity on `E(L)`. -/
theorem galMap_five_apply {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜)
    (P : D.LPoints) :
    D.galMap (D.galMap (D.galMap (D.galMap (D.galMap P)))) = P := by
  -- `σ` acts through `gen`, whose fifth power is `1`.
  have hiter : (D.galMap^[5]) P = P := by
    rw [galMap_iterate D]
    have hgen : ((D.ext.gen : D.ext.L →ₐ[𝕜] D.ext.L) ^ 5) = AlgHom.id 𝕜 D.ext.L := by
      -- `gen ^ 5 = 1` in the Galois group, because `orderOf gen = 5`.
      have h1 : D.ext.gen ^ 5 = 1 := by
        have h := pow_orderOf_eq_one D.ext.gen
        rwa [D.ext.orderOf_gen] at h
      -- The algebra-homomorphism power is the image of the group power under
      -- `AlgEquiv.toAlgHomHom`, which is a monoid homomorphism.
      have h2 : ((D.ext.gen : D.ext.L →ₐ[𝕜] D.ext.L) ^ 5)
          = ((D.ext.gen ^ 5 : D.ext.L ≃ₐ[𝕜] D.ext.L) : D.ext.L →ₐ[𝕜] D.ext.L) :=
        (MonoidHom.map_pow (AlgEquiv.toAlgHomHom 𝕜 D.ext.L) D.ext.gen 5).symm
      rw [h2, h1]
      ext y
      simp
    rw [hgen, pointMap_algHom_id D]
  simpa [Function.iterate_succ_apply'] using hiter

/-- The image of the shift `σ - 1` lies in `ker N`: `N(σy) = N(y)` because `σ` permutes the five
summands of the norm and has order `5`.  This is the inclusion of the coboundaries into the
cocycles. -/
theorem shift_mem_cocycles {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜)
    (x : D.LPoints) : D.shift x ∈ D.cocycles := by
  -- `ker N` is the subgroup of points annihilated by the norm `1 + σ + σ² + σ³ + σ⁴`.
  rw [Work.TorsorExistence.QuinticTwist.cocycles, AddMonoidHom.mem_ker,
    Work.TorsorExistence.QuinticTwist.norm_apply]
  -- Push `σ` through the subtraction defining the shift, at each of the five levels of the norm.
  have hshift : D.shift x = D.galMap x - x := rfl
  simp only [hshift, map_sub]
  -- The five terms now telescope: the sum is `σ⁵x - x`, and `σ⁵ = 1`.
  rw [galMap_five_apply D x]
  abel

end Work.PointlessIndexFive
