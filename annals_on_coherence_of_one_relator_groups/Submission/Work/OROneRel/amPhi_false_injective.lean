import Mathlib
import Submission.Work.OROneRel.NoZeroDefs

/-!
# Injectivity of the second amalgam map `amPhi r t p false`

The amalgamation map on the second factor of the amalgam
`⟨α | r⟩ ∗_(n ↦ t^n, n ↦ s^(pn)) ⟨s⟩` is

  `amPhi r t p false : ULift (Multiplicative ℤ) →* ULift (Multiplicative ℤ)`,
  `n ↦ ULift.up (n.down ^ p)`

(`Work.OROneRel.amPhi_false_apply`).  Since `Multiplicative ℤ` is multiplicative torsion-free,
the map `a ↦ a ^ p` is injective for `p ≠ 0` (`zpow_left_injective`), and `ULift.up`/`ULift.down`
are inverse bijections.  Hence `amPhi r t p false` is injective.

Note that the `false` component of `amPhi` depends on neither the relator `r` nor the letter `t`;
only the exponent `p` matters.
-/

namespace Work.OROneRel

universe u

/-- The underlying map of `amPhi r t p false` is `n ↦ ULift.up (n.down ^ p)`.  Consequently, for
`p ≠ 0` it is injective because the exponentiation map on the torsion-free group
`Multiplicative ℤ` is injective (cf. `zpow_left_injective`). -/
theorem amPhi_false_injective {α : Type u} (r : FreeGroup α) (t : α) {p : ℤ} (hp : p ≠ 0) :
    Function.Injective (Work.OROneRel.amPhi r t p false) := by
  intro a b hab
  -- `amPhi r t p false` is `ULift.up ∘ (· ^ p) ∘ ULift.down`; strip the outer `ULift.up`.
  have h : a.down ^ p = b.down ^ p :=
    congrArg (fun x : ULift.{u} (Multiplicative ℤ) => x.down) hab
  exact ULift.ext (x := a) (y := b) (zpow_left_injective hp h)

end Work.OROneRel
