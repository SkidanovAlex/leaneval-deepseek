import Mathlib
import Submission.Work.Clifford.Classes
import Submission.Work.Clifford.principalChar_mem_Irr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Clifford

/-- If there is exactly one real irreducible character of `G`, then every real irreducible
character is the principal character.  Indeed the principal character is real and irreducible,
so it is an element of the singleton type of real irreducible characters, and the hypothesis
`Nat.card ... = 1` makes that type a subsingleton. -/
theorem realIrr_eq_principal_of_card_one {G : Type*} [Group G] [Fintype G]
    (h : Nat.card {χ : G → ℂ // χ ∈ Work.Clifford.Irr G ∧ Work.Clifford.IsRealChar χ} = 1)
    {χ : G → ℂ} (hχ : χ ∈ Work.Clifford.Irr G) (hreal : Work.Clifford.IsRealChar χ) :
    χ = Work.Clifford.principalChar G := by
  have hsub : Subsingleton {χ : G → ℂ // χ ∈ Work.Clifford.Irr G ∧ Work.Clifford.IsRealChar χ} :=
    (Nat.card_eq_one_iff_unique.mp h).1
  have hprin : Work.Clifford.principalChar G ∈ Work.Clifford.Irr G :=
    Work.Clifford.principalChar_mem_Irr
  have hprinreal : Work.Clifford.IsRealChar (Work.Clifford.principalChar G) := by
    intro g
    simp [Work.Clifford.principalChar]
  have heq := Subsingleton.elim
    (⟨χ, hχ, hreal⟩ : {χ : G → ℂ // χ ∈ Work.Clifford.Irr G ∧ Work.Clifford.IsRealChar χ})
    ⟨Work.Clifford.principalChar G, hprin, hprinreal⟩
  exact congrArg Subtype.val heq

end Work.Clifford
