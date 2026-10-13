/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The direct summand theorem in equal characteristic `p`

An affine form of the equal characteristic `p` case of the direct summand conjecture:
if a Noetherian local domain `A` of characteristic `p` admits a faithfully flat *perfect*
`A`-algebra `S` (which is the conclusion of Kunz's theorem when `A` is regular), then `A`
is a splinter: every finite faithful `A`-algebra `B` admits an `A`-linear retraction
`B → A`.

The proof is the classical one, in the form used in `direct_summand_proof_map_REVIEW.md`
§4(a):

1. the obstruction is the ideal `I = evalIdeal A B = {s 1 : s ∈ Hom_A(B, A)}`;
2. `I ≠ ⊥` (`evalIdeal_ne_bot`), say `0 ≠ a ∈ I`;
3. if `I ≠ ⊤` then `I ⊆ m`; base change along `A → S` and the Frobenius twist
   (`frobeniusTwist`, packaged as `exists_pthRoot_mem_map_evalIdeal`) give, for every `e`,
   an element `t_e ∈ I·S` with `t_e ^ p^e = a`;
4. faithfully flat descent plus Krull's intersection theorem (`krull_descent`) give a
   contradiction. Hence `I = ⊤`, i.e. `1 ∈ evalIdeal A B`.
-/
import Mathlib
import Submission.Work.DSEQP.Basic
import Submission.Work.DSEQP.AlmostPurity
import Submission.Work.DSEQP.krull_descent
import Submission.Work.DSEQP.evalIdeal_ne_bot

namespace Work.DSEQP

/-- **Equal characteristic `p` direct summand theorem (affine form).**

If `A` is a Noetherian local domain of characteristic `p` which has a faithfully flat perfect
extension `S` (e.g. `S = A^{1/p^∞}` when `A` is regular, by Kunz), then `A` is a splinter. -/
theorem isSplinter_of_flat_perfect (A : Type*) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] (p : ℕ) [Fact p.Prime] [CharP A p] (S : Type*) [CommRing S]
    [Algebra A S] [Module.FaithfullyFlat A S] [CharP S p] [PerfectRing S p] :
    IsSplinter A := by
  intro B _ _ _ hB
  haveI : Nontrivial B :=
    ⟨1, 0, fun h => one_ne_zero (hB (by simpa using h))⟩
  by_contra h1
  have hI : evalIdeal A B ≠ ⊥ := evalIdeal_ne_bot A B hB
  obtain ⟨a, ha, ha0⟩ := Submodule.ne_bot_iff (evalIdeal A B) |>.1 hI
  exact krull_descent A S p (evalIdeal A B)
    (IsLocalRing.le_maximalIdeal (fun htop => h1 (htop ▸ Submodule.mem_top))) ha ha0
    (fun e => exists_pthRoot_mem_map_evalIdeal A S B p hB ha e)

end Work.DSEQP
