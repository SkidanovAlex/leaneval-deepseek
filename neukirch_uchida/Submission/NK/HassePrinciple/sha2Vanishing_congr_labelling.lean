import Mathlib
import Submission.NK.BrauerHasse.Hasse

/-!
# Change of labelling for the Hasse principle `Sha2Vanishing`

`NK.BrauerHasse.Sha2Vanishing p K K' κ κ'` is stated for a pair of "local" fields
`κ ⊆ κ'`: it says that a class in `H²(H, Z/p)`, `H ≤ Gal(K'/K)` closed and isomorphic to
`Gal(κ'/κ)`, whose localisation at every finite place of `K` vanishes, is zero.

The local fields enter this Prop only through the *isomorphism type* of their absolute Galois
group, in the hypothesis `Nonempty (H ≃* Gal(κ'/κ))`.  Consequently an isomorphism
`Gal(κ'/κ) ≃* Gal(κ₀'/κ₀)` of absolute Galois groups makes `Sha2Vanishing p K K' κ κ'` and
`Sha2Vanishing p K K' κ₀ κ₀'` interderivable — this is the sense in which the Hasse principle
does not depend on the *labelling* of the local field: it may be applied to whatever
presentation of the local absolute Galois group is at hand.

The proof is only bookkeeping (`Gal(κ'/κ) ≃* Gal(κ₀'/κ₀)` upgrades to an equivalence of the
`Nonempty`-hypotheses by composing with `e` resp. `e.symm`), but the statement is the one the
local-global argument consumes: the local data is produced for a completion `K_𝔭` while the
input `Sha2Vanishing` was stated for a field `κ` model of that completion.
-/

namespace NK.HassePrinciple

universe u

/-- **Change of labelling of the local fields in the Hasse principle.**
If the absolute Galois groups of the local fields `κ/κ₀` are isomorphic, then the Hasse
principle for the pair `(κ, κ')` is equivalent to the one for the pair `(κ₀, κ₀')`. -/
theorem sha2Vanishing_congr_labelling {p : ℕ} {K K' κ κ' κ₀ κ₀' : Type u}
    [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']
    [Field κ₀] [Field κ₀'] [Algebra κ₀ κ₀'] [IsSepClosure κ₀ κ₀']
    (e : Gal(κ'/κ) ≃* Gal(κ₀'/κ₀)) :
    (NK.BrauerHasse.Sha2Vanishing (K := K) (K' := K') p κ κ' ↔
      NK.BrauerHasse.Sha2Vanishing (K := K) (K' := K') p κ₀ κ₀') := by
  -- The only occurrence of `κ, κ'` in `Sha2Vanishing` is the hypothesis
  -- `Nonempty (H ≃* Gal(κ'/κ))`, and `e` identifies the two possibilities.
  have key : ∀ H : Subgroup Gal(K'/K),
      Nonempty (H ≃* Gal(κ'/κ)) ↔ Nonempty (H ≃* Gal(κ₀'/κ₀)) := by
    intro H
    constructor
    · rintro ⟨f⟩; exact ⟨f.trans e⟩
    · rintro ⟨f⟩; exact ⟨f.trans e.symm⟩
  simp only [NK.BrauerHasse.Sha2Vanishing]
  constructor
  · intro h H hH hκ x hx
    exact h H hH ((key H).2 hκ) x hx
  · intro h H hH hκ x hx
    exact h H hH ((key H).1 hκ) x hx

end NK.HassePrinciple
