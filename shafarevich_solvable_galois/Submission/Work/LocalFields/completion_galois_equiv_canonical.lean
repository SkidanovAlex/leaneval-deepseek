import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.Decomposition
import Submission.Work.LocalFields.completionAut_injective
import Submission.Work.LocalFields.finrank_completion_le_card_decompositionGroup
import Submission.Work.LocalFields.finrank_completion_eq_card_decompositionGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Valued WithZero

/-- **The decomposition group is the local Galois group, as a group.**

For a finite Galois extension `L/K` of number fields, a finite prime `v` of `K` and a finite prime
`w` of `L` lying over `v`, the group of `K_v`-linear automorphisms of the completion `L_w` is
isomorphic to the decomposition group `D_w ≤ Gal(L/K)`.

The two directions are the canonical extension `D_w →* (L_w ≃ₐ[K_v] L_w)` (injective, because `L`
is dense in `L_w`; see `Work.LocalFields.completionAut_injective`) and the counting identity
`#D_w = [L_w : K_v] = #(L_w ≃ₐ[K_v] L_w)`, which combines
`Work.LocalFields.finrank_completion_eq_card_algEquiv` (`[L_w : K_v] = #Gal(L_w/K_v)`) with
`Work.LocalFields.finrank_completion_le_card_decompositionGroup` (`[L_w : K_v] ≤ #D_w`). -/
theorem completion_galois_equiv_canonical {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] :
    Nonempty ((Work.LocalFields.Completion L w ≃ₐ[Work.LocalFields.Completion K v]
        Work.LocalFields.Completion L w) ≃* Work.LocalFields.decompositionGroup K w) := by
  -- the canonical injective group homomorphism `D_w → Gal(L_w/K_v)`
  obtain ⟨Φ, hΦinj⟩ := completionAut_injective v w
  -- counting: `#(L_w ≃ₐ[K_v] L_w) = [L_w : K_v] ≤ #D_w` and `#D_w ≤ #(L_w ≃ₐ[K_v] L_w)`
  have hAutle : Nat.card (Work.LocalFields.Completion L w ≃ₐ[Work.LocalFields.Completion K v]
        Work.LocalFields.Completion L w) ≤ Nat.card (Work.LocalFields.decompositionGroup K w) := by
    rw [← finrank_completion_eq_card_algEquiv v w]
    exact finrank_completion_le_card_decompositionGroup v w
  have hDle : Nat.card (Work.LocalFields.decompositionGroup K w) ≤
      Nat.card (Work.LocalFields.Completion L w ≃ₐ[Work.LocalFields.Completion K v]
        Work.LocalFields.Completion L w) :=
    Nat.card_le_card_of_injective _ hΦinj
  have hcard : Nat.card (Work.LocalFields.decompositionGroup K w) =
      Nat.card (Work.LocalFields.Completion L w ≃ₐ[Work.LocalFields.Completion K v]
        Work.LocalFields.Completion L w) := le_antisymm hDle hAutle
  -- hence the injection is a bijection, giving the group isomorphism
  have hbij : Function.Bijective Φ :=
    (Nat.bijective_iff_injective_and_card Φ).mpr ⟨hΦinj, hcard⟩
  exact ⟨(MulEquiv.ofBijective Φ hbij).symm⟩

end Work.LocalFields
