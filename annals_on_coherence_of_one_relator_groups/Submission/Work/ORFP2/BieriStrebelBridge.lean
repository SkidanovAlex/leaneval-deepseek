/-
# Discharging the Bieri–Strebel hypothesis of node N13

Node N13 of the route design states JL Theorems 4.4 and 4.5 relative to the named hypothesis
`Work.ORDunwoody.BieriStrebel k` (JL Lemma 4.3 = Bieri–Strebel [BS78, Lemma 2.1]).

The theorem below *proves* that hypothesis: it is the `FP₂`/Bieri–Strebel criterion established in
this directory (`Work.ORFP2.isFP2_iff_hasFP2Extension`), transported to the vocabulary of node N13
by `Work.ORFP2.isFP2_iff_ORDunwoody` and `Work.ORFP2.hasFP2Extension_iff_ORDunwoody`.
-/
import Submission.Work.ORFP2.Summary
import Submission.Work.ORFP2.ORDunwoodyInterop
import Submission.Work.ORDunwoody.Hypotheses

set_option autoImplicit false

universe u

namespace Work.ORFP2

/-- **Bieri–Strebel [BS78, Lemma 2.1] = JL Lemma 4.3**, in the form used by node N13:
for a commutative ring `k` with `1 ≠ 0` and a group `G`, `G` is of type `FP₂` over `k` if and only
if it is the quotient of a finitely presented group by a normal subgroup `N` with
`N_ab ⊗_ℤ k = 0`. -/
theorem BieriStrebel (k : Type u) [CommRing k] [Nontrivial k] : Work.ORDunwoody.BieriStrebel k := by
  intro G _
  rw [← isFP2_iff_ORDunwoody k G, ← hasFP2Extension_iff_ORDunwoody k G]
  exact isFP2_iff_hasFP2Extension k G

end Work.ORFP2
