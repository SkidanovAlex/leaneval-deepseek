import Mathlib
import Submission.Work.BSHallW.Defs
import Submission.Work.BSHallW.WeakClosure
import Submission.Work.BSHallW.SylowReduction
import Submission.Work.BSHallW.HallHyp
import Submission.Work.Grun.Main
import Submission.Work.ThmF.Tools.hasNormalIndexP_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSHallW.Main` — the corrected Hall–Wielandt theorem for odd `p`

`Work.BSHallW.hallWielandtOdd : Work.BSHallW.HallWielandtOddProp` is M. Hall's Theorem 14.4.2
(Hall–Wielandt) with the necessary hypothesis `p ≠ 2`, proved from P. Hall's Theorem 14.4.1 as
delivered by the area `Work.Grun` (`Work.Grun.hall_14_4_1`).

Setting: `G` finite, `p ≠ 2` prime, `S ∈ Sylow p G`, `A ≤ S` abelian and weakly closed in `S`
w.r.t. `G`, `H = N_G(A) ⊇ S` (`le_normalizer_of_weaklyClosed`).  The conclusion
`HasNormalIndexP p G ↔ HasNormalIndexP p H` is proved by rewriting both sides as "every
homomorphism into `ℤ/p` is trivial" (`Work.ThmF.Tools.hasNormalIndexP_iff`):

* `⟸`: `Work.BSHallW.forall_hom_eq_one_of_sylow_le` (the Sylow-index argument);
* `⟹`: `Work.Grun.hall_14_4_1` with `P = S`, `H = N_G(A)` and the transfer hypothesis supplied by
  `Work.BSHallW.hallHyp_of_weaklyClosed` (weak closure produces M. Hall's central `p`-cycle in each
  double coset; oddness of `p` is used here — see the module `Work.BSHallW.HallHyp`).

For `p = 2` the statement is false (`G = PSL(2,7)`, `A = C₄`), which is why the hypothesis `p ≠ 2`
is present in `HallWielandtOddProp`.
-/

set_option autoImplicit false

open scoped commutatorElement

namespace Work.BSHallW

/-- **M. Hall §14.4, Theorem 14.4.2 (Hall–Wielandt), correct form: `p` odd.**
If `A` is an abelian subgroup of a Sylow `p`-subgroup `S` of a finite group `G` (`p ≠ 2` prime)
which is weakly closed in `S` with respect to `G`, then `G` has a normal subgroup of index `p` if
and only if `N_G(A)` does. -/
theorem hallWielandtOdd : HallWielandtOddProp := by
  intro G _ _ p hp hp2 S A hAS hwc hAab
  haveI : Fact p.Prime := ⟨hp⟩
  have hSH : (S : Subgroup G) ≤ Subgroup.normalizer (A : Set G) :=
    le_normalizer_of_weaklyClosed hAS hwc
  rw [Work.ThmF.Tools.hasNormalIndexP_iff (G := G),
    Work.ThmF.Tools.hasNormalIndexP_iff (G := ↥(Subgroup.normalizer (A : Set G)))]
  constructor
  · -- every homomorphism out of `G` is trivial, hence every one out of `N_G(A)`
    intro hG hH
    exact hG (forall_hom_eq_one_of_sylow_le S hSH hH)
  · -- every homomorphism out of `N_G(A)` is trivial, by P. Hall's transfer theorem
    intro hH hG
    exact hH (Work.Grun.hall_14_4_1 S (Subgroup.normalizer (A : Set G)) hSH hG
      (hallHyp_of_weaklyClosed hp hp2 S hAS hwc hAab))

/-- **The abelian-Sylow corollary** of the corrected Hall–Wielandt theorem: an abelian Sylow
`p`-subgroup (`p ≠ 2`) is weakly closed in itself, so Hall–Wielandt applies to the pair `(P, P)`.
This is the add-`p ≠ 2` form of `Work.ThmF.Prove.AbelianSylowHallWielandt`. -/
theorem hallWielandtOdd_abelianSylow {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : HallWielandtOddProp) (hp : p.Prime) (hp2 : p ≠ 2) (P : Sylow p G)
    (hab : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y = y * x) :
    Work.ThmF.HasNormalIndexP p G ↔
      Work.ThmF.HasNormalIndexP p ↥(Subgroup.normalizer (P : Set G)) := by
  refine h G p hp hp2 P (P : Subgroup G) le_rfl ?_ hab
  intro g hg
  refine Subgroup.eq_of_le_of_card_ge hg ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

end Work.BSHallW
