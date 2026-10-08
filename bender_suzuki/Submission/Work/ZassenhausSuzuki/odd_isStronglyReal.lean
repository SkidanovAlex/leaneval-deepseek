import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.CountingDefs
import Submission.Work.ZassenhausPSL2.ZassenhausPSL2OfQCore
import Submission.Work.ZassenhausSuzuki.Q_suzuki_sq
import Submission.Work.ZassenhausSuzuki.Odd.psl2Model_odd_isStronglyReal
import Submission.Work.ZassenhausSuzuki.Odd.odd_isStronglyReal_of_suzuki

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-- **Suzuki 1962 / Huppert–Blackburn III XI.11.6 (a) and XI.10.**

In a finite simple group `G` with a split rank-one Zassenhaus configuration `H = Q ⋊ D`
(`IsSplitRankOne H Q t`, `IsZassenhaus H`) whose regular normal subgroup `Q` is a `2`-group,
every element of odd order is a product of two involutions (*strongly real*).

This is the union of the two alternatives of Peterfalvi II Ch. VI–VII / Suzuki 1962:

* `Q` **abelian**: the delivered classification `Work.ZassenhausPSL2.zassenhausPSL2`
  (`ZassenhausPSL2Prop`) gives `G ≃* PSL2Model n` with `|Q| = 2ⁿ`, and in `PSL(2, 2ⁿ)` every
  odd-order element is inverted by the Weyl involution or by an involution normalising a Singer
  cycle (`Work.ZassenhausSuzuki.Odd.psl2Model_odd_isStronglyReal`, via the element
  classification `sl2_classify`).
* `Q` **non-abelian**: `Work.ZassenhausSuzuki.Q_suzuki_sq` (Suzuki 1962 Theorem 3 / HB 11.2)
  gives that `Q` is a Suzuki `2`-group with `|Q| = |Z(Q)|²`, and the counting argument of
  Huppert–Blackburn XI.11.6 (a) — the same argument as Suzuki 1962 §10, resting on
  `numClasses_stronglyReal_general` (Suzuki Prop. 13: the strongly real elements `x` with
  `x² ≠ 1` fall into `|Z(Q)| - 1` classes), `centralizer_abelian_of_strongly_real` (Prop. 14)
  and the structure of the Sylow `2`-subgroups — shows that the set `B` of odd-order elements
  that are *not* strongly real is empty
  (`Work.ZassenhausSuzuki.Odd.odd_isStronglyReal_of_suzuki`). -/
theorem odd_isStronglyReal {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hG : IsSimpleGroup G)
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {x : G} (hodd : Odd (orderOf x)) (hx1 : x ≠ 1) :
    Work.ZassenhausSuzuki.IsStronglyReal x := by
  classical
  by_cases hab : Submission.Blueprint.IsAbelianSubgroup Q
  · -- ## `Q` abelian: `G ≅ PSL(2, 2ⁿ)`
    obtain ⟨n, hn, ⟨e⟩⟩ :=
      Work.ZassenhausPSL2.zassenhausPSL2 G hG H Q t hsplit hzass h2 hab
    have hodd' : Odd (orderOf (e x)) := by rwa [MulEquiv.orderOf_eq e x]
    have hx1' : e x ≠ 1 := by
      intro h
      exact hx1 (e.injective (by rw [h, map_one]))
    obtain ⟨a, b, ha, hb, hab'⟩ :=
      Work.ZassenhausSuzuki.Odd.psl2Model_odd_isStronglyReal n hn (e x) hodd' hx1'
    refine ⟨e.symm a, e.symm b, ?_, ?_, ?_⟩
    · rw [← map_mul, ha, map_one]
    · rw [← map_mul, hb, map_one]
    · rw [← map_mul, hab', MulEquiv.symm_apply_apply]
  · -- ## `Q` non-abelian: `Q` is a Suzuki two-group with `|Q| = |Z(Q)|²`
    obtain ⟨hSuz, hord⟩ :=
      Work.ZassenhausSuzuki.Q_suzuki_sq hG H Q t hsplit hzass h2 hab
    exact Work.ZassenhausSuzuki.Odd.odd_isStronglyReal_of_suzuki hG hsplit hzass h2 hSuz hord
      hab hodd hx1

end Work.ZassenhausSuzuki
