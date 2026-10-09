import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Commons.NumberTheory.NumberField.Valuation.centralizer_stabilizer_valuationSubring_sepClosure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

Lead design (Claude) 10-05 02:40 (_lead_design/v4_0215/restates/NOTE.md): apply the axiom-clean ZConstruction.eq_of_decomp_eq_of_finite at K := ⊥ and transport along fixingSubgroupEquiv (about 100–200 lines). Used for the v4 instantiation.
-/

namespace Work.SSGRoute

open scoped Pointwise

/-- Equal decomposition groups determine the finite place (base `k`).

Two finite places `A`, `A'` of `Ω` over `k` with `decomp k A = decomp k A'` are equal.  Needed to
instantiate the v4 interface from `G1pOwn.g1FinHalf`, which evaluates at `h.choose`, a place with
the same decomposition group.

Route: apply the proved, axiom-clean `Work.SSGRoute.ZConstruction.eq_of_decomp_eq_of_finite` with
the intermediate field `⊥` (or any finite Galois `K`).  Transport the equality of `decomp k`
groups to the `decomp (k := ↥⊥)` groups along `IntermediateField.fixingSubgroupEquiv`; this is the
identification `decomp ↥K A ≅ decomp k A ⊓ G_K` used in `grunwald_over_K_general`.  The
non-triviality hypotheses `A.comap … ≠ ⊤` come from `IsFinPlace`.

Here we instead run the same rigidity argument directly at the base field `k`: for a number field
`k` the algebraic closure `Ω` is a separable closure (`IsSepClosure k Ω`, since `k` has
characteristic zero), so `Commons.NumberTheory.NumberField.Valuation.stabilizer_inf_stabilizer_eq_bot_of_ne`
applies with `K := k`, `K' := Ω` and says that the decomposition groups of two *distinct* finite
places meet in `⊥`; combined with the nontriviality of the decomposition group of a finite place
(`...exists_ne_one_comap_eq_of_comap_ne_top`) this forces the places to be equal. -/
theorem decomp_injective_of_finPlace {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {A A' : ValuationSubring Ω}
    (hA : SSGRoute.IsFinPlace k A) (hA' : SSGRoute.IsFinPlace k A')
    (hD : SSGRoute.decomp k A = SSGRoute.decomp k A') : A = A' := by
  by_contra hne
  have hbot := Commons.NumberTheory.NumberField.Valuation.stabilizer_inf_stabilizer_eq_bot_of_ne
    (K := k) (K' := Ω) hne hA hA'
  simp only [SSGRoute.decomp] at hD
  rw [← hD, inf_idem] at hbot
  obtain ⟨σ, hσne, hσA⟩ :=
    Commons.NumberTheory.NumberField.Valuation.exists_ne_one_comap_eq_of_comap_ne_top
      (K := k) (K' := Ω) A hA
  have hσmem : σ ∈ SSGRoute.decomp k A :=
    (Commons.NumberTheory.NumberField.Valuation.comap_eq_iff_mem_stabilizer A σ).mp hσA
  simp only [SSGRoute.decomp] at hσmem
  rw [hbot] at hσmem
  exact hσne (Subgroup.mem_bot.mp hσmem)

end Work.SSGRoute
