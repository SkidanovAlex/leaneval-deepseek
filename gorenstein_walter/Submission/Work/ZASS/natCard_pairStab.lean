import Mathlib
import Submission.Work.ZASS.Defs

namespace Work.ZASS

open Work.GW2 (ZassHyps2)

/-- **Z1, unconditional form.** The order of the two-point stabilizer `G_{∞x}` is `(q - 1) / 2`,
straight from the arithmetic clause `2 * |G_x ⊓ G_∞| = q - 1` of `ZassHyps2`.

Unlike `Work.ZASS.card_pairStab` this version does not ask for `[Finite X]`: neither the
hypothesis clause nor the conclusion mentions finiteness of `X`. -/
theorem natCard_pairStab {G X : Type} [Group G] [Finite G] [MulAction G X]
    {q : ℕ} (h : Work.GW2.ZassHyps2 G X q) {inf x : X} (hx : x ≠ inf) :
    Nat.card (Work.Zassenhaus.pairStab G inf x) = (q - 1) / 2 := by
  have h2 : 2 * Nat.card (MulAction.stabilizer G x ⊓ MulAction.stabilizer G inf :
      Subgroup G) = q - 1 := h.2.2.2.2 x inf hx
  have h3 : Work.Zassenhaus.pairStab G inf x =
      MulAction.stabilizer G x ⊓ MulAction.stabilizer G inf := rfl
  rw [h3]
  omega

end Work.ZASS
