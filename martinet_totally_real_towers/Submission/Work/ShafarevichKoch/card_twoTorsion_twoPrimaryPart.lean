import Mathlib
import Submission.Work.ShafarevichKoch.WingbergDefs

/-!
# `Work.ShafarevichKoch.card_twoTorsion_twoPrimaryPart`

The `2`-torsion of the `2`-primary part of a finite abelian group `A` is the same as the
`2`-torsion of `A` itself: an element of order dividing `2` has `2`-power order, hence already
lies in `Work.ShafarevichKoch.twoPrimaryPart A`.  The inclusion therefore induces a bijection
on the `2`-torsion subgroups.
-/

namespace Work.ShafarevichKoch

theorem card_twoTorsion_twoPrimaryPart (A : Type*) [CommGroup A] [Fintype A] :
    Nat.card {x : Work.ShafarevichKoch.twoPrimaryPart A // x ^ 2 = 1} =
      Nat.card {x : A // x ^ 2 = 1} := by
  classical
  -- The inclusion of the `2`-primary part into `A`, restricted to the `2`-torsion.
  let f : {x : Work.ShafarevichKoch.twoPrimaryPart A // x ^ 2 = 1} →
      {x : A // x ^ 2 = 1} :=
    fun x => ⟨(x.1 : A), by
      have h : ((x.1 : Work.ShafarevichKoch.twoPrimaryPart A) : A) ^ 2 =
          ((1 : Work.ShafarevichKoch.twoPrimaryPart A) : A) :=
        congrArg Subtype.val x.2
      simpa using h⟩
  -- Conversely an element of order dividing `2` has `2`-power order.
  let g : {x : A // x ^ 2 = 1} →
      {x : Work.ShafarevichKoch.twoPrimaryPart A // x ^ 2 = 1} :=
    fun y => ⟨⟨y.1, ⟨1, by simpa using y.2⟩⟩, by
      apply Subtype.ext
      simpa using y.2⟩
  have hfg : Function.LeftInverse g f := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hgf : Function.RightInverse g f := by
    intro y
    apply Subtype.ext
    rfl
  exact Nat.card_congr (Equiv.ofBijective f ⟨hfg.injective, hgf.surjective⟩)

end Work.ShafarevichKoch
