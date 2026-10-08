import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Z(E) = Φ(E)` for an extraspecial `p`-group `E`

For an extraspecial `p`-group, the center and the Frattini subgroup coincide.  This is the
`p = [P,P] = Z(P) = Φ(P)` part of the structure theory of extraspecial groups (FT §2; Gorenstein
*Finite Groups* §5.5, where an extraspecial group is defined by `Z(P) = Φ(P) = [P,P] ≅ C_p`).

In this workspace the two relevant definitions live in `Submission.Work.PGroup.Basic`:

* `Work.PGroup.IsSpecial p P` is `IsElementaryAbelian p P` (abelian case) **or**
  `IsPGroup p P ∧ ¬ IsMulCommutative P ∧ centerIn P = ⁅P, P⁆ ∧ centerIn P = frattiniIn P ∧
  IsElementaryAbelian p (centerIn P)`;
* `Work.PGroup.IsExtraspecial p P` is `¬ IsMulCommutative P ∧ IsSpecial p P ∧
  Nat.card (centerIn P) = p`.

So the statement is *definitional*: an extraspecial group is non-commutative, which rules out the
abelian branch of `IsSpecial`, and the non-abelian branch carries exactly the equality
`centerIn P = frattiniIn P` as a conjunct.
-/

namespace Work.PGroup

theorem center_eq_frattini_of_isExtraspecial {G : Type*} [Group G] {p : ℕ} (E : Subgroup G)
    (hE : Work.PGroup.IsExtraspecial p E) : Work.PGroup.centerIn E = Work.PGroup.frattiniIn E := by
  -- An extraspecial group is not commutative, so the abelian alternative in `IsSpecial` fails
  -- and only the non-abelian alternative — which contains `centerIn E = frattiniIn E` — remains.
  rcases hE with ⟨hnc, hsp, -⟩
  rcases hsp with h | ⟨-, -, -, hcf, -⟩
  · exact absurd h.1 hnc
  · exact hcf

end Work.PGroup
