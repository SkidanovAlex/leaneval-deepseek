import Mathlib
import Submission.Work.Cohomology.cokernelComponent
import Submission.Work.Cohomology.Crux.Transgression
import Submission.Work.Cohomology.relKernMono

/-!
# The cap map on the middle term of the relative Mayer–Vietoris sequence

The middle term of the relative Mayer–Vietoris sequence is
`cruxMid X A U V = cokernel (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))`, and
`relMVτ₂U U V A = subInclChain U V Set.inter_subset_left` (definitionally), so the two components
of the middle term are exactly the relative small chains to which `capRelSmall` applies.
Composing `cokernel_biprod_map_iso`
(`cokernel (biprod.map f g) ≅ cokernel f ⊞ cokernel g`) and the degreewise biproduct
`HomologicalComplex.biprodXIso` with the biproduct of the two component cap maps gives **the cap
map on the middle term**.

## Main results

* `cokernel_relMVτ₂U_eq`, `cokernel_relMVτ₂V_eq` — the two components of `cruxMid` are the relative
  small chains;
* `capRelMid` — the cap map on `cruxMid X A U V`, landing in `C^{U,V}(U) ⊞ C^{U,V}(V)`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- **The `U`-component of `cruxMid` is the relative small chains `C^{U,V}(U, U ∩ A)`**
(definitionally, since `relMVτ₂U U V A = subInclChain U V Set.inter_subset_left`). -/
theorem cokernel_relMVτ₂U_eq (X : TopCat) (A U V : Set X) :
    cokernel (relMVτ₂U U V A) =
      relSmallChains U V U (U ∩ A) (Set.inter_subset_left : U ∩ A ⊆ U) := rfl

/-- **The `V`-component of `cruxMid` is the relative small chains `C^{U,V}(V, V ∩ A)`.** -/
theorem cokernel_relMVτ₂V_eq (X : TopCat) (A U V : Set X) :
    cokernel (relMVτ₂V U V A) =
      relSmallChains U V V (V ∩ A) (Set.inter_subset_left : V ∩ A ⊆ V) := rfl

/-- **The cap map on the middle term of the relative Mayer–Vietoris sequence.** -/
noncomputable def capRelMid (X : TopCat) (A U V : Set X) (n m : ℕ)
    (α : Cochain ℤ (TopCat.toSSet.obj X) n) (hα : α ∈ relKern ℤ X A n) :
    (cruxMid X A U V).X (n + m) ⟶
      (smallInChains U V U ⊞ smallInChains U V V).X m := by
  refine (Classical.choice (cokernel_biprod_map_iso (relMVτ₂U U V A)
      (relMVτ₂V U V A))).hom.f (n + m) ≫
    (HomologicalComplex.biprodXIso (cokernel (relMVτ₂U U V A))
      (cokernel (relMVτ₂V U V A)) (n + m)).hom ≫ ?_
  exact (cokernel_relMVτ₂U_eq X A U V).symm ▸ (cokernel_relMVτ₂V_eq X A U V).symm ▸
    (biprod.map
      (capRelSmall X U V U (U ∩ A) (Set.inter_subset_left : U ∩ A ⊆ U) n m α
        (relKern_mono (Set.inter_subset_right : U ∩ A ⊆ A) hα))
      (capRelSmall X U V V (V ∩ A) (Set.inter_subset_left : V ∩ A ⊆ V) n m α
        (relKern_mono (Set.inter_subset_right : V ∩ A ⊆ A) hα)) ≫
      (HomologicalComplex.biprodXIso (smallInChains U V U) (smallInChains U V V) m).inv)

end

end Work.Cohomology
