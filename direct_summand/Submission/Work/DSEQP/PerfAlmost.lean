/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Almost acyclicity of the perfected Čech complex (node PERF)

The three clauses of `DSMap.Mix2.AlmostAcyc` for the perfected Čech complex `K` of
`Submission/Work/DSEQP/PerfCech.lean`, with the ideal `⊥` and the root tower
`ϖ k = g^(1/p^k) = (frobeniusEquiv W p).symm^[k] (ψW (φ g))`.
-/
import Mathlib
import Submission.Work.DSEQP.PerfCech
import Submission.Work.DSEQP.perf_charP_perfect
import Submission.Work.DSEQP.perf_frobEquiv_symm_of
import Submission.Work.DSEQP.glue_sections
import Submission.Work.DSEQP.alt_sum_pow
import Submission.Work.DSMap.Mix2Fix

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Simplicial BigOperators

namespace Work.DSEQP

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000

namespace PerfSetup

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime] {X : Scheme.{u}} [IsIntegral X]
  {f : X ⟶ Spec (.of A)} {ι : Type u}

/-- `Γ(X,⊤)` has characteristic `p`. -/
theorem charP_gamma (S : PerfSetup A p X f) : CharP (Γ(X, ⊤)) p := by
  have hdvd : ringChar (Γ(X, ⊤)) ∣ p := ringChar.dvd (S.hpU ⊤)
  have hne1 : ringChar (Γ(X, ⊤)) ≠ 1 := CharP.ringChar_ne_one
  refine ringChar.of_eq ?_
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h | h
  · exact absurd h hne1
  · exact h

/-- `W = Γ(X,⊤)^{1/p^∞}` has characteristic `p`. -/
theorem charP_W (S : PerfSetup A p X f) : CharP S.W p := by
  haveI := S.charP_gamma
  exact (perf_charP_perfect (Γ(X, ⊤)) p (S.hpU ⊤)).1

/-- `W = Γ(X,⊤)^{1/p^∞}` is perfect. -/
theorem perfectRing_W (S : PerfSetup A p X f) : PerfectRing S.W p := by
  haveI := S.charP_gamma
  exact (perf_charP_perfect (Γ(X, ⊤)) p (S.hpU ⊤)).2

/-- The root tower `g^(1/p^k)` in `W = Γ(X,⊤)^{1/p^∞}`. -/
noncomputable def varpi (S : PerfSetup A p X f) [CharP S.W p] [PerfectRing S.W p]
    (g : A) (k : ℕ) : S.W :=
  ((frobeniusEquiv S.W p).symm^[k]) (S.ψW (DSMap.phi A X f g))

/-- The root tower is given at level `k` by `Perf.of k (φ g)`. -/
theorem varpi_eq (S : PerfSetup A p X f) [CharP S.W p] [PerfectRing S.W p]
    (g : A) (k : ℕ) :
    S.varpi g k = Perf.of (Γ(X, ⊤)) p (S.hpU ⊤) k (DSMap.phi A X f g) := by
  have h : ∀ k : ℕ, ((frobeniusEquiv S.W p).symm^[k]) (S.ψW (DSMap.phi A X f g)) =
      Perf.of (Γ(X, ⊤)) p (S.hpU ⊤) k (DSMap.phi A X f g) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      haveI := S.charP_gamma
      exact perf_frobEquiv_symm_of (Γ(X, ⊤)) p (S.hpU ⊤) k (DSMap.phi A X f g)
  exact h k


end PerfSetup

end Work.DSEQP
