import Mathlib
import Submission.Work.SmallRank.isMulCommutative_of_odd_coprime_le_GL2
import Submission.Work.SmallRank.GL2Defs
import Submission.Work.GL2odd.commutator_isPGroup_of_preserves_line
import Submission.Work.GL2odd.preserves_line_of_prime_dvd_card

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-
# `⁅G, G⁆` is a `p`-group for `G ≤ GL(2, p)` of odd order

Let `p` be a prime and let `G ≤ GL(2, p) = GL (Fin 2) (ZMod p)` be a subgroup of odd order.
Then the derived subgroup `⁅G, G⁆` is a `p`-group.

The proof splits on whether `p` divides the order of `G`:

* if `p ∤ |G|`, then `G` is contained in a `p'`-subgroup of odd order, hence is abelian by
  `Work.SmallRank.isMulCommutative_of_odd_coprime_le_GL2`, so `⁅G, G⁆ = ⊥`;
* if `p ∣ |G|`, then (as `|G|` is odd) `p` is odd, and `G` preserves a line of `(ZMod p)²`
  (`Work.GL2odd.preserves_line_of_prime_dvd_card`); a group preserving a line has
  `⁅G, G⁆ ≤ U`, where `U` is the unipotent radical of the line stabiliser, which is a
  `p`-group (`Work.GL2odd.commutator_isPGroup_of_preserves_line`).
-/

namespace Work.LocalPrelim

open scoped Pointwise commutatorElement

theorem odd_GL2_commutator_isPGroup {p : ℕ} [Fact p.Prime]
    (G : Subgroup (GL (Fin 2) (ZMod p))) (hodd : Odd (Nat.card G)) :
    IsPGroup p ↥(⁅G, G⁆) := by
  by_cases hpdvd : p ∣ Nat.card G
  · -- `p ∣ |G|`: then `p` is odd (as `|G|` is), and `G` preserves a line.
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hodd
      obtain ⟨j, hj⟩ := hpdvd
      omega
    have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
    obtain ⟨e, he, hpres⟩ :=
      Work.GL2odd.preserves_line_of_prime_dvd_card hpodd G hpdvd hodd
    exact Work.GL2odd.commutator_isPGroup_of_preserves_line G e he hpres
  · -- `p ∤ |G|`: `G` is abelian, so `⁅G, G⁆` is trivial.
    haveI hmc : IsMulCommutative ↥G :=
      Work.SmallRank.isMulCommutative_of_odd_coprime_le_GL2 G hodd hpdvd
    have hbot : ⁅G, G⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hmc
    rw [hbot]
    exact IsPGroup.of_bot

end Work.LocalPrelim
