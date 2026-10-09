/-
Work of the Neukirch–Uchida team: the analytic input of Čebotarev's theorem.

An elementary rearrangement of infinite products over complex numbers: a finite product of
absoIutely convergent infinite products is the infinite product of the finite products.
-/
import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped BigOperators Classical

noncomputable section

namespace NK.HeckeL.Nonvanishing

/-- **Interchange of a finite product with an infinite product.**  For a finite index type `ι` and
absolutely convergent families `f i`, the finite product of the infinite products is the infinite
product of the finite products. -/
theorem prod_finset_tprod_comm {ι β : Type*} [Fintype ι] (f : ι → β → ℂ)
    (h : ∀ i, Multipliable (f i)) :
    ∏ i : ι, (∏' b : β, f i b) = ∏' b : β, ∏ i : ι, f i b := by
  have hmain : ∀ s : Finset ι,
      HasProd (fun b : β => ∏ i ∈ s, f i b) (∏ i ∈ s, ∏' b : β, f i b) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hasProd_one (α := ℂ) (β := β)
    | insert a s ha ih =>
        have hstep : (fun b : β => ∏ i ∈ insert a s, f i b)
            = fun b => f a b * ∏ i ∈ s, f i b := by
          funext b
          rw [Finset.prod_insert ha]
        rw [hstep, Finset.prod_insert ha]
        exact (h a).hasProd.mul ih
  exact (hmain Finset.univ).tprod_eq.symm

end NK.HeckeL.Nonvanishing
