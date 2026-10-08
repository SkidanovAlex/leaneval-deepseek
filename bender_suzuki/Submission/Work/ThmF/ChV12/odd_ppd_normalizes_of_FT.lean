import Mathlib
import Submission.Work.ThmF.ChV12.odd_ppd_normalizer_of_solvable
import Submission.Blueprint.Interfaces

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.odd_ppd_normalizes_of_FT` — the ppd normaliser, from Feit–Thompson

`Work.ThmF.ChV12.odd_ppd_normalizes` (`ChV12/odd_ppd_normalizes.lean`) is the statement

> for an elementary abelian 2-group `A` (`|A| = 2^k`), a prime `q` with `orderOf (2 : ZMod q) = k`,
> an **odd-order** subgroup `G ≤ Aut A` and `σ ∈ G` of order `q`: every `g ∈ G` normalises `⟨σ⟩`,

and it is the missing ingredient of the App. V route (`even_card_closure_of_two_ppd`
→ `fitting_irreducible_of_transitive` → `JformReduction`).  As stated it has no `FeitThompsonProp`
argument, so it cannot be proved from the recorded material: the proof (`ChV12/lemma5`'s odd-order
case) needs `G` **solvable**, which is exactly the odd-order theorem for `↥G`
(`Nat.card ↥G = Nat.card G` is odd by hypothesis).

The proved lemma `Work.ThmF.ChV12.odd_ppd_normalizer_of_solvable` supplies the statement modulo
`Group.IsSolvable G`; here `FeitThompsonProp` is applied to `↥G` to close the gap.  A consumer
wishing to use this instead of the `sorry`ed `odd_ppd_normalizes` must thread
`(hFT : FeitThompsonProp)` through the (few) files of that route; nothing else changes.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV12

/-- **The ppd normaliser statement, with `FeitThompsonProp` supplied.** -/
theorem odd_ppd_normalizes_of_FT (hFT : Submission.Blueprint.FeitThompsonProp)
    {A : Type} [Group A] [Finite A]
    (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x) {k q : ℕ}
    (hk1 : 1 ≤ k) (hk : Nat.card A = 2 ^ k) (hq : Nat.Prime q)
    (hord : orderOf (2 : ZMod q) = k)
    (G : Subgroup (MulAut A)) (hodd : Odd (Nat.card G))
    (σ : MulAut A) (hσG : σ ∈ G) (hσ : orderOf σ = q) :
    ∀ g ∈ G, ∃ i : ℤ, g * σ * g⁻¹ = σ ^ i :=
  Work.ThmF.ChV12.odd_ppd_normalizer_of_solvable hA2 hAc hk1 hk hq hord G hodd
    (hFT ↥G (by simpa using hodd)) σ hσG hσ

/-- The same, in the form of the missing solvability step alone. -/
theorem odd_ppd_solvable_of_FT (hFT : Submission.Blueprint.FeitThompsonProp)
    {A : Type} [Group A] [Finite A]
    (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x) {k q : ℕ}
    (hk1 : 1 ≤ k) (hk : Nat.card A = 2 ^ k) (hq : Nat.Prime q)
    (hord : orderOf (2 : ZMod q) = k)
    (G : Subgroup (MulAut A)) (hodd : Odd (Nat.card G))
    (σ : MulAut A) (hσG : σ ∈ G) (hσ : orderOf σ = q) :
    Group.IsSolvable G :=
  hFT ↥G (by simpa using hodd)

end Work.ThmF.ChV12
