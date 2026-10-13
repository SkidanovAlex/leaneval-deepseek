/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Almost purity in characteristic `p` (affine form)

The mathematical content of the equal characteristic `p` proof of the direct summand theorem
(review `direct_summand_proof_map_REVIEW.md` §4(a)) is:

* the obstruction to splitting `A` off `B` is an ideal `I = evalIdeal A B`;
* after base change along a faithfully flat perfect `A`-algebra `S`, every *nonzero* element of
  `I` acquires `p^e`-th roots inside `I · S` (the Frobenius trick, `frobeniusTwist`);
* but an element `a ≠ 0` of `I ⊆ m` cannot have all its `p`-power roots inside `I·S` for a
  Noetherian local domain `A`, by Krull's intersection theorem (`krull_descent`).

This file proves the middle step: **almost purity**.
-/
import Mathlib
import Submission.Work.DSEQP.Basic
import Submission.Work.DSEQP.frobeniusTwist
import Submission.Work.DSEQP.evalIdeal_baseChange

namespace Work.DSEQP

/-- **Almost purity in characteristic `p`, affine form.**

Let `A` be a Noetherian domain of characteristic `p`, `B` a finite `A`-algebra with `A → B`
injective, and `S` a flat, perfect `A`-algebra.  Then every `p^e`-th root of every *nonzero*
element `a` of the evaluation ideal `evalIdeal A B` already lies in `(evalIdeal A B) · S`:
the Frobenius twist `b ↦ (s (b ^ p^e))^{1/p^e}` of an `A`-linear retraction candidate
`s : B →ₗ[A] A` with `s 1 = a` is again `A`-linear and has value a `p^e`-th root of `a`.

Note that `S` perfect is used through the existence of the `p^e`-th root map as a ring
homomorphism; the `A`-linearity of the twisted map uses that `B` has characteristic `p`. -/
theorem exists_pthRoot_mem_map_evalIdeal (A S B : Type*) [CommRing A] [CommRing S]
    [Algebra A S] [CommRing B] [Algebra A B] [IsDomain A] [IsNoetherianRing A]
    [Module.Finite A B] [Module.Flat A S] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP S p]
    [PerfectRing S p] (hB : Function.Injective (algebraMap A B)) {a : A}
    (ha : a ∈ evalIdeal A B) (e : ℕ) :
    ∃ t : S, t ∈ (evalIdeal A B).map (algebraMap A S) ∧ t ^ (p ^ e) = algebraMap A S a := by
  obtain ⟨s, hs⟩ := (mem_evalIdeal_iff A B).1 ha
  have hBp : CharP B p := charP_of_injective_algebraMap hB p
  -- base change the candidate retraction to `S`
  let sS : B →ₗ[A] S := (Algebra.linearMap A S).comp s
  have hsS : sS 1 = algebraMap A S a := by simp [sS, hs]
  -- the Frobenius twist
  obtain ⟨s', hs'⟩ := frobeniusTwist (S := S) (A := A) (B := B) p sS e
  refine ⟨s' 1, ?_, ?_⟩
  · rw [← evalIdeal_baseChange A S B]
    exact Ideal.subset_span ⟨s', rfl⟩
  · rw [← hsS]
    exact hs'

end Work.DSEQP
