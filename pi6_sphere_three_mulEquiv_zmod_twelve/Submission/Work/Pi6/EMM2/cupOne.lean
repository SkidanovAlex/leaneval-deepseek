import Mathlib
import Submission.Work.Pi6.EMM2.Statements
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The cup-product unit for the interface's product `Work.Pi6.cup`

`Work.Cohomology.CupRing` proves the unit laws for the library's product `cupH'` on the cohomology
of a simplicial set (`cupH'_one_left`, `cupH'_one_right`).  The interface `Work.Pi6.cup` is
`cupH'` of the singular simplicial set of `TopCat.of X` and `Work.Pi6.one` is `oneH`, so the only
difference from the library statement is the *cast*: `cupH'_one_left` returns
`x = (Nat.zero_add n).symm ▸ y`, whereas the interface asks for `(Nat.zero_add n) ▸ x = y`
(the direction in which the degree `0 + n` is transported back to `n`).  The transport lemma
`cast_symm_cast_self` bridges the two.
-/

namespace Work.Pi6.EMM2

open CategoryTheory

/-- Transporting an element along an equality of degrees and back is the identity. -/
theorem cast_symm_cast_self {M : ℕ → Type*} {a b : ℕ} (h : a = b) (x : M b) :
    h ▸ (h.symm ▸ x) = x := by
  cases h
  rfl

theorem cupOne : Work.Pi6.EMM2.CupOneStatement := by
  intro 𝕜 _ X _ n b
  constructor
  · have h1 : Work.Pi6.cup 𝕜 X 0 n (Work.Pi6.one 𝕜 X) b = (Nat.zero_add n).symm ▸ b :=
      Work.Cohomology.cupH'_one_left 𝕜 (TopCat.toSSet.obj (TopCat.of X)) n b
    have h2 := congrArg (fun t : Work.Pi6.Coh 𝕜 X (0 + n) => (Nat.zero_add n) ▸ t) h1
    exact h2.trans
      (cast_symm_cast_self (M := fun k => Work.Pi6.Coh 𝕜 X k) (Nat.zero_add n) b)
  · exact Work.Cohomology.cupH'_one_right 𝕜 (TopCat.toSSet.obj (TopCat.of X)) n b

end Work.Pi6.EMM2
