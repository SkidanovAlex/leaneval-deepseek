/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A cyclic subfield of prescribed degree disjoint from a given finite Galois field

Given a finite Galois `L ⊆ AlgebraicClosure ℚ` and `n ≥ 1`, we produce a finite Galois
`M ⊆ AlgebraicClosure ℚ` with `Gal(M/ℚ) ≃* Multiplicative (ZMod n)` and `L ⊓ M = ⊥`.

The construction: only finitely many primes `p` have `CycloField p ⊓ L ≠ ⊥`
(`exists_prime_modEq_one_inf_eq_bot`), so we may choose `p ≡ 1 (mod n)` with
`CycloField p ⊓ L = ⊥`; then `exists_cyclic_subfield_of_prime` (from `Cyclic.lean`) gives
`M ≤ CycloField p` with `Gal(M/ℚ) ≃* Multiplicative (ZMod n)`, and `M ⊓ L ≤ CycloField p ⊓ L = ⊥`.

## Main declarations

* `exists_disjoint_cyclic`

-/
import Mathlib
import Submission.Work.FieldTheory.Crossing.Defs
import Submission.Work.FieldTheory.Crossing.Cyclic
import Submission.Work.FieldTheory.Crossing.exists_prime_modEq_one_inf_eq_bot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.FieldTheory.Crossing

open scoped Classical
open scoped Nat

noncomputable section

set_option linter.style.haveILetI false

/-- **A cyclic extension of degree `n` disjoint from a given finite Galois `L`.**  This is the
mathematical content of `realizableOver_prod_zmod`: see `ZMod.lean`.

(`hfd`/`hG` are passed explicitly rather than as instance arguments because the
`IntermediateField` coercions carry several non-definitionally-equal `Algebra`/`Field` instance
paths, along which type class search is unreliable.) -/
theorem exists_disjoint_cyclic (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hfd : FiniteDimensional ℚ L) (hG : IsGalois ℚ L) (n : ℕ) (hn : n ≠ 0) :
    ∃ M : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ M ∧ IsGalois ℚ M ∧
      L ⊓ M = ⊥ ∧ Nonempty (Multiplicative (ZMod n) ≃* (M ≃ₐ[ℚ] M)) := by
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨p, hp, -, hmod, hdisj⟩ := exists_prime_modEq_one_inf_eq_bot L hfd hG n 0 hn
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hdiv : n ∣ p - 1 := (Nat.modEq_iff_dvd' (le_of_lt hp.one_lt)).mp hmod.symm
  obtain ⟨M, hle, hMfd, hMG, hiso⟩ := exists_cyclic_subfield_of_prime p n hp hdiv
  refine ⟨M, hMfd, hMG, ?_, hiso⟩
  have h1 : M ⊓ L ≤ CycloField p ⊓ L := inf_le_inf_right L hle
  rw [hdisj] at h1
  have h2 : M ⊓ L = ⊥ := le_bot_iff.mp h1
  rwa [inf_comm]


/-- `exists_disjoint_cyclic` with the finite-dimensionality and Galois hypotheses as instance
arguments, for callers who have the instances in scope. -/
theorem exists_disjoint_cyclic_of_instances (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [hfd : FiniteDimensional ℚ L] [hG : IsGalois ℚ L] (n : ℕ) (hn : n ≠ 0) :
    ∃ M : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ M ∧ IsGalois ℚ M ∧
      L ⊓ M = ⊥ ∧ Nonempty (Multiplicative (ZMod n) ≃* (M ≃ₐ[ℚ] M)) :=
  exists_disjoint_cyclic L hfd hG n hn

end

end Work.FieldTheory.Crossing
