import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs

/-!
# The one-factorization interface of the Glock--Kühn--Osthus chapter

The GKO chapter reduces KKKMO Theorem 10.8 (`ErdosFaberLovaszConjecture.GKOStatement`) to a deep
input about *perfect matchings* rather than Hamilton cycles:

* `Work.Deep.GKO.gkoStatementFixed_of_KO` uses `KOStatement` (Hamilton decompositions of robust
  expanders) only in its step 5, where it is applied to the regular remainder `Gk` of the
  regularisation — a **lower-`(p,ε)`-regular** graph of degree `r ≥ αn` on an **even** number of
  vertices — and then only through `oneFactorization_of_hamDecomp` (each Hamilton cycle of an even
  order graph splits into two perfect matchings).

So the exact consumer need is `OneFactLowerRegStatement` below: a lower-`(p,ε)`-regular graph of
linear degree and even order has a 1-factorization.  This is the route the lead adopted
(`EFL_AUDIT_LEAD.md` §2.3, §4, 2026-10-01): it retires the robust-expander generality
(`KOStatement`, `AbsorptionStatement`, the KOT engine and the blow-up) and keeps only the
elementary matching absorber (`Work.Deep.GKO.OneFact.matchingAbsorber`) together with the
approximate Hamilton decomposition (`Work.Deep.GKO.ApproxHamDecompStatement`).

`BipLowerReg` is the bipartite lower-regularity predicate the absorber consumes.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.GKO

noncomputable section

variable {n : ℕ}

/-- **Bipartite lower regularity.**  Every pair of large subsets `S ⊆ A`, `T ⊆ B` spans at least
`q |S| |T|` edges. -/
def BipLowerReg (H : SimpleGraph (Fin n)) (A B : Finset (Fin n)) (q ε : ℝ) : Prop :=
  ∀ S : Finset (Fin n), S ⊆ A → ∀ T : Finset (Fin n), T ⊆ B →
    ε * (n : ℝ) ≤ (S.card : ℝ) → ε * (n : ℝ) ≤ (T.card : ℝ) →
    q * (S.card : ℝ) * (T.card : ℝ) ≤ (crossEdges H S T : ℝ)

/-- **What GKO's argument actually consumes from Kühn--Osthus.**

For every density `p ∈ (0,1]` and every linear degree bound `α > 0` there is `ε₀ > 0` such that for
every `ε ≤ ε₀` there is `n₀` such that every lower-`(p,ε)`-regular graph on an even number
`n ≥ n₀` of vertices that is `r`-regular with `r ≥ α n` has a 1-factorization with `r` factors.

This is GKO's `lowerReg ⇒ robust expander` observation together with Kühn--Osthus' theorem: it is
much weaker than `KOStatement` both in the conclusion (perfect matchings, not Hamilton cycles) and
in the hypothesis (lower regularity, not robust expansion; no `τ(α)` bookkeeping).  The audit
(`EFL_AUDIT_LEAD.md` §2.3) records that this is exactly the interface `gkoStatementFixed_of_KO`
uses, with `r` of either parity. -/
def OneFactLowerRegStatement : Prop :=
  ∀ p : ℝ, 0 < p → p ≤ 1 → ∀ α : ℝ, 0 < α → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ n₀ : ℕ, ∀ n ≥ n₀, Even n →
      ∀ G : SimpleGraph (Fin n), LowerReg G p ε → ∀ r : ℕ, IsRegularOf G r →
        α * (n : ℝ) ≤ (r : ℝ) → HasOneFactorization G r

end

end Work.Deep.GKO
