import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.Zassenhaus.Basic

namespace Work.ZASS

/-- Elementary arithmetic of the subtraction in `ncard_fixesOnly`: if `1 + q * (a - 1)` is at
most `q * a` (which holds by construction, since it is the cardinality of a subset of a
`q * a`-element set), then the complementary piece has `q - 1` elements.

The hypothesis is exactly what rules out the degenerate case `a = 0` (`q ≥ 3` in the
application, where `a = (q - 1) / 2`). -/
lemma nat_mul_sub_one_sub (q a : ℕ) (h : 1 + q * (a - 1) ≤ q * a) :
    q * a - (1 + q * (a - 1)) = q - 1 := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := by
    cases a with
    | zero => simp at h
    | succ n => exact ⟨n, rfl⟩
  rw [Nat.add_sub_cancel, Nat.mul_succ]
  omega

/-- **Z2 (blueprint §ZASS).** Exactly `q - 1` elements of `B = G_∞` fix only `∞`.  Uses
`Work.Zassenhaus.fixesOnly_union_fixesSome` (the two sets are complementary in `B`) and
`Work.Zassenhaus.fixesOnly_disjoint_fixesSome`, plus the two cardinality inputs.
(Hypothesis amended to `Work.GW2.ZassHyps2`, design pass 2.) -/
theorem ncard_fixesOnly {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
    {q : ℕ} (h : Work.GW2.ZassHyps2 G X q) {inf zero : X} (hne : inf ≠ zero)
    (hB : Nat.card (Work.Zassenhaus.borel G inf) = q * ((q - 1) / 2))
    (hsome : (Work.Zassenhaus.fixesSome G inf).ncard = 1 + q * ((q - 1) / 2 - 1)) :
    (Work.Zassenhaus.fixesOnly G inf).ncard = q - 1 := by
  have hdisj := Work.Zassenhaus.fixesOnly_disjoint_fixesSome (G := G) inf
  have hunion := Work.Zassenhaus.fixesOnly_union_fixesSome (G := G) inf
  -- `fixesOnly` and `fixesSome` partition `B`, so their cardinalities add up to `|B|`.
  have hcard : (Work.Zassenhaus.fixesOnly G inf).ncard
      + (Work.Zassenhaus.fixesSome G inf).ncard = q * ((q - 1) / 2) := by
    rw [← Set.ncard_union_eq hdisj, hunion, ← Nat.card_coe_set_eq]
    exact hB
  rw [hsome] at hcard
  -- the complement of a set of size `1 + q * (a - 1)` in a set of size `q * a`, `a = (q-1)/2`
  have harith := nat_mul_sub_one_sub q ((q - 1) / 2) (by omega)
  rw [Nat.eq_sub_of_add_eq hcard, harith]

end Work.ZASS
