import Mathlib
import Submission.Work.OROneRel.weinbaumDefs
import Submission.Work.OROneRel.exists_complement_of_isSubwordOf_pow

namespace Work.OROneRel

universe u

theorem weinbaum_sigma_zero_of_half {β : Type u} (R : FreeGroup β) {z : β}
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator R)
    (hz : z ∈ Work.OROneRel.relatorLetters R) (hexp : Work.OROneRel.expSum z R = 1)
    (hhalf : ∀ (k : ℕ) (w : FreeGroup β), Work.OROneRel.IsSubwordOf w (R ^ k) →
      2 * Work.OROneRel.relatorNorm w ≤ Work.OROneRel.relatorNorm R → w ≠ 1 →
      PresentedGroup.mk ({R} : Set (FreeGroup β)) w ≠ 1) :
    ∀ (k : ℕ) (w : FreeGroup β), Work.OROneRel.IsSubwordOf w (R ^ k) →
      Work.OROneRel.relatorNorm w < Work.OROneRel.relatorNorm R → w ≠ 1 →
      PresentedGroup.mk ({R} : Set (FreeGroup β)) w ≠ 1 := by
  intro k w hsub hlen hw1 hcontra
  -- A counterexample `w` of length `< |R|` produces the complementary counterexample `s`: cutting
  -- out the arc of the cyclic word of `R` opposite to `w` gives a subword `s` of `R ^ 2` which is
  -- nontrivial, trivial in `⟨α | R⟩`, and whose length together with `|w|` adds up to `|R|`.
  obtain ⟨s, m, hsubs, hs1, hsnorm, hscontra⟩ :=
    exists_complement_counterexample hcyc hsub hlen hw1 hcontra
  have hsum : relatorNorm w + relatorNorm s = relatorNorm R := by omega
  -- the shorter of `w` and `s` has length at most half of `|R|`, so the hypothesis applies to it
  rcases le_total (relatorNorm w) (relatorNorm s) with h | h
  · exact hhalf k w hsub (by omega) hw1 hcontra
  · exact hhalf m s hsubs (by omega) hs1 hscontra

end Work.OROneRel
