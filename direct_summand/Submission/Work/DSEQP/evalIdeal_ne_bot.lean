/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The evaluation ideal of a finite extension of a domain is nonzero

For a Noetherian domain `A` and a finite `A`-algebra `B` whose structure map `A → B` is
injective, the evaluation ideal `Work.DSEQP.evalIdeal A B` -- the image of
`Hom_A(B, A) → A`, `s ↦ s 1` -- is nonzero: there is an `A`-linear functional on `B` which
does not vanish at `1`.  Equivalently (`Work.DSEQP.evalIdeal_ne_bot_iff`), the obstruction to
splitting `A` off `B` is not as large as possible.

The argument is the classical "denominators" one, run through the fraction field:

* Let `K = FractionRing A` and let `V = LocalizedModule (nonZeroDivisors A) B` be the
  localization of `B` at the multiplicative set of non-zero-divisors of `A` (this is the
  base change `B ⊗[A] K`, in the form in which Mathlib provides the `K`-module structure).
* `mk 1 1 ≠ 0` in `V`: if some `r ∈ nonZeroDivisors A` killed `1 : B`, then
  `algebraMap A B r = 0`, so `r = 0` because `algebraMap A B` is injective, contradicting
  `r ≠ 0`.
* Hence `V` is a nonzero `K`-vector space, and a nonzero vector of a vector space over a
  field is hit by a linear functional with value `1` (`Module.Projective.exists_dual_eq_one`).
  Composing such a `t : V →ₗ[K] K` with `B → V`, `b ↦ mk b 1`, gives an `A`-linear map
  `f : B →ₗ[A] K` with `f 1 = 1`.
* `Work.DSEQP.exists_smul_mem_range_algebraMap` clears the denominators of `f` on a finite
  generating set of `B`: it produces `d ∈ nonZeroDivisors A` with `d • f (b) = algebraMap a`
  for suitable `a ∈ A`, for every `b : B`.  Descending `d • f` along the injective linear map
  `A → K` (using `Function.Injective` of `algebraMap A K`, an instance of
  `IsLocalization.injective`) gives `s : B →ₗ[A] A` with `algebraMap (s b) = d • f b`.
* Then `s 1 = d ≠ 0`, so `∃ s : B →ₗ[A] A, s 1 ≠ 0`, i.e. `evalIdeal A B ≠ ⊥`.
-/
import Mathlib
import Submission.Work.DSEQP.Basic
import Submission.Work.DSEQP.exists_smul_mem_range_algebraMap

open scoped TensorProduct

namespace Work.DSEQP

theorem evalIdeal_ne_bot (A B : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [Nontrivial B]
    (h : Function.Injective (algebraMap A B)) : evalIdeal A B ≠ ⊥ := by
  rw [evalIdeal_ne_bot_iff]
  classical
  -- `1 ⊗ 1 ≠ 0` in the localization `V = B[1/A]`: `1 : B` is not annihilated by a
  -- non-zero-divisor of `A`.
  have hx : LocalizedModule.mk (1 : B) (1 : nonZeroDivisors A) ≠ 0 := by
    intro h0
    have h0' : (LocalizedModule.mkLinearMap (nonZeroDivisors A) B) (1 : B) = 0 := by
      simpa [LocalizedModule.mkLinearMap_apply] using h0
    obtain ⟨r, hrS, hr⟩ := LocalizedModule.mem_ker_mkLinearMap_iff.mp h0'
    have hr' : algebraMap A B r = 0 := by
      rw [Algebra.algebraMap_eq_smul_one]
      exact hr
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hrS) (h (by simpa using hr'))
  -- A `K`-linear functional on `V` with value `1` at `1 ⊗ 1`.
  obtain ⟨t, ht⟩ := Module.Projective.exists_dual_eq_one (FractionRing A) hx
  -- The induced `A`-linear functional on `B` takes the value `1` at `1`.
  let f : B →ₗ[A] FractionRing A :=
    (t.restrictScalars A).comp (LocalizedModule.mkLinearMap (nonZeroDivisors A) B)
  have hf1 : f 1 = 1 := by
    simp only [f, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
      LocalizedModule.mkLinearMap_apply]
    exact ht
  -- Clear the denominators of `f` on the finite `A`-module `B`.
  obtain ⟨d, hdS, hdan⟩ := exists_smul_mem_range_algebraMap A (FractionRing A) B f
  have hinj : Function.Injective (algebraMap A (FractionRing A)) :=
    IsLocalization.injective (FractionRing A) (le_refl _)
  -- Descend `d • f`, whose values lie in the image of `A → K`, to an `A`-linear map `B → A`.
  choose s0 hs0 using hdan
  have hadd : ∀ b b' : B, s0 (b + b') = s0 b + s0 b' := fun b b' =>
    hinj (by rw [hs0 (b + b'), map_add, smul_add, ← hs0 b, ← hs0 b', map_add])
  have hsmul : ∀ (a : A) (b : B), s0 (a • b) = a • s0 b := fun a b =>
    hinj (by
      rw [hs0 (a • b), map_smul, smul_comm d a (f b), ← hs0 b]
      simp [Algebra.smul_def, map_mul])
  refine ⟨{ toFun := s0, map_add' := hadd, map_smul' := hsmul }, ?_⟩
  change s0 1 ≠ 0
  have h1 : s0 1 = d := hinj (by rw [hs0 1, hf1, Algebra.algebraMap_eq_smul_one])
  rw [h1]
  exact mem_nonZeroDivisors_iff_ne_zero.mp hdS

end Work.DSEQP
