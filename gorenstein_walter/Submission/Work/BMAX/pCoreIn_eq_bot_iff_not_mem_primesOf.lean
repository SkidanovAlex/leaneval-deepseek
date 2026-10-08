/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BMAX area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE3.Case1aP_ne_bot

/-!
# `O_q(A) = 1` iff `q` does not divide `|F(A)|`

For a subgroup `A` of a finite group `G` and a prime `q`, the `q`-core of `A` is trivial
exactly when `q` does not divide the order of the Fitting subgroup of `A`:

  `Work.GW2.pCoreIn q A = ⊥ ↔ q ∉ Work.GW2.primesOf (Work.GW2.fittingIn A)`.

This is the prime-by-prime form of the standard decomposition `F(A) = ∏_q O_q(A)` of the
Fitting subgroup of a finite group into the direct product of its `q`-cores.

* `⇐` (contrapositive) is Cauchy's theorem: if `q ∈ π(F(A))` then `q ∣ |F(A)|`, so `F(A)`
  contains an element of order `q`; that element generates a `q`-subgroup, which — because
  `F(A)` is nilpotent and normal in `A` — is `q`-subnormal in `A` and therefore lies in
  `O_q(A) ≠ 1`.  This is the proved lemma
  `Work.CORE3.pCoreIn_ne_bot_of_mem_primesOf_fittingIn`.
* `⇒` (contrapositive) is the inclusion `O_q(A) ≤ F(A)`: a nontrivial `q`-group has order
  divisible by `q`, so `q ∣ |O_q(A)| ∣ |F(A)|`, i.e. `q ∈ π(F(A))`.

The `…In` vocabulary used here (`pCoreIn`, `fittingIn`, `primesOf`) is the one of
`Submission.Work.ASM.Defs`; the two import blocks of the original stub
(`Submission.Work.BMAX.Defs` on the one hand and `Submission.Work.GLUE.PcoreApi` on the
other) declare the same `Work.GW2` vocabulary and cannot be combined in one environment.
-/

set_option linter.style.haveILetI false

namespace Work.BMAX

theorem pCoreIn_eq_bot_iff_not_mem_primesOf {G : Type} [Group G] [Finite G] (A : Subgroup G)
    (q : ℕ) (hq : q.Prime) :
    Work.GW2.pCoreIn q A = ⊥ ↔ q ∉ Work.GW2.primesOf (Work.GW2.fittingIn A) := by
  constructor
  · -- `q ∈ π(F(A))` forces `O_q(A) ≠ 1` (Cauchy's theorem; `Work.CORE3`).
    intro hbot hmem
    exact (Work.CORE3.pCoreIn_ne_bot_of_mem_primesOf_fittingIn G A q hmem) hbot
  · -- Contrapositive: `O_q(A) ≠ 1` forces `q ∈ π(F(A))`.
    intro hnot
    by_contra hne
    apply hnot
    haveI : Fact q.Prime := ⟨hq⟩
    -- `O_q(A) ≠ ⊥` as a subgroup of `↥A` (the inclusion is injective).
    have hC_ne : Work.GW2.pCore q ↥A ≠ ⊥ := by
      intro h
      exact hne (by rw [Work.GW2.pCoreIn, h, Subgroup.map_bot])
    -- `O_q(↥A)` is a `q`-group …
    have hCpg : IsPGroup q ↥(Work.GW2.pCore q ↥A) := by
      rw [Work.CORE2A.pCore_eq_opCore (G := ↥A) (p := q)]
      exact OddOrder.Isaacs.Ch01.opCore_isPGroup q ↥A
    -- … contained in the Fitting subgroup `F(↥A)`.
    have hCle : Work.GW2.pCore q ↥A ≤ Work.GW2.fitting ↥A :=
      Work.CORE2A.pCore_le_fitting (G := ↥A) (p := q)
    -- A nontrivial `q`-group has order divisible by `q`.
    have hdvdC : q ∣ Nat.card ↥(Work.GW2.pCore q ↥A) := by
      rcases hCpg.card_eq_or_dvd (p := q) with h1 | h2
      · exact absurd (Subgroup.card_eq_one.mp h1) hC_ne
      · exact h2
    -- Hence `q ∣ |F(↥A)| = |F(A)|`, i.e. `q ∈ π(F(A))`.
    have hdvdF : q ∣ Nat.card ↥(Work.GW2.fitting ↥A) :=
      hdvdC.trans (Subgroup.card_dvd_of_le hCle)
    have hcard : Nat.card ↥(Work.GW2.fitting ↥A) = Nat.card ↥(Work.GW2.fittingIn A) := by
      rw [Work.GW2.fittingIn]
      exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective A)
        (K := Work.GW2.fitting ↥A)).symm
    rw [Work.GW2.primesOf]
    exact hcard ▸ Nat.mem_primeFactors.mpr ⟨hq, hdvdF, Nat.card_pos.ne'⟩

end Work.BMAX
