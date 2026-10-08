import Mathlib
import Submission.Work.ThompsonFrobenius.GTDefs
import Submission.Work.ThompsonFrobenius.gtMinimal_false

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# **Theorem D** (Glauberman–Thompson): `ZWZ`-normalizer `p`-nilpotent ⟹ `p`-nilpotent

The main theorem of the area: for an odd prime `p` and a finite group `G`, if for some Sylow
`p`-subgroup `P` the normalizer `N_G(Z(J(P)))` has a normal `p`-complement, then so does `G`
(Glauberman 1968, Theorem D).  Proved by strong induction on `Nat.card G` using GT-8.
-/

set_option autoImplicit false

namespace Work.ThompsonFrobenius

theorem glauberman_thompson (hZJ : Submission.Blueprint.GlaubermanZJProp) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (G : Type) [Group G] [Finite G] : GTStatement p G := by
  have key : ∀ n : ℕ, ∀ (X : Type) [Group X] [Finite X], Nat.card X = n → GTStatement p X := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro X _ _ hnX Q hQ
      by_contra hnot
      refine gtMinimal_false hZJ (G := X) (P := Q) ⟨hp, hp2, hQ, hnot, ?_⟩
      intro Y _ _ hY
      exact ih (Nat.card Y) (hnX ▸ hY) Y rfl
  exact key (Nat.card G) G rfl

end Work.ThompsonFrobenius
