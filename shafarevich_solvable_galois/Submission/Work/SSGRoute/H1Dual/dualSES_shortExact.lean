import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Submission.Work.SSGRoute.H1Dual.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory

namespace Work.SSGRoute.H1Dual

/-- **Dualizing preserves exactness in the middle.** For `k`-vector spaces and linear maps
`A --f--> B --g--> C` with `f.range = g.ker` (exactness at `B`), the transposed maps satisfy
`g.dualMap.range = f.dualMap.ker` (exactness at `B^∨`).

This is the general linear-algebra input for the exactness of the dual of the coinduced
resolution: over a field the range of a transpose is the annihilator of the kernel
(`LinearMap.range_dualMap_eq_dualAnnihilator_ker`) and the kernel of a transpose is the
annihilator of the range (`LinearMap.ker_dualMap_eq_dualAnnihilator_range`). -/
theorem range_dualMap_eq_ker_dualMap {k : Type} [Field k] {A B C : Type}
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
    (f : A →ₗ[k] B) (g : B →ₗ[k] C) (h : LinearMap.range f = LinearMap.ker g) :
    LinearMap.range g.dualMap = LinearMap.ker f.dualMap := by
  rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range, h,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker]

/-- The dual of the coinduced resolution `0 → M' → Coind(M) → M → 0` (defined in
`Submission.Work.SSGRoute.H1Dual.Defs` as `dualSES`) is short exact:
`0 → M^∨ → Coind(M)^∨ → (M')^∨ → 0`. -/
theorem dualSES_shortExact {k : Type} [Field k] {G : Type} [Group G] [Fintype G]
    (M : Rep k G) : (Work.SSGRoute.dualSES M).ShortExact := by
  classical
  -- It suffices to check everything after forgetting to `ModuleCat k`.
  refine CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (forget₂ (Rep k G) (ModuleCat k)) ?_
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · -- Exactness in the middle: `dualMap` of the augmentation `a` and of the inclusion
    -- `i : ker a → Coind(M)`.  Since `i.range = a.ker`, the transpose of `a` has range
    -- `(a.ker)^⊥ = (i.range)^⊥`, which is the kernel of the transpose of `i`.
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact range_dualMap_eq_ker_dualMap _ _
      (Submodule.range_subtype (LinearMap.ker (Work.SSGRoute.coindAugFun M)))
  · -- `a` is surjective, so its transpose is injective.
    rw [ModuleCat.mono_iff_injective]
    exact LinearMap.dualMap_injective_of_surjective (Work.SSGRoute.coindAugFun_surjective M)
  · -- `i` is injective, so its transpose is surjective.
    rw [ModuleCat.epi_iff_surjective]
    exact LinearMap.dualMap_surjective_of_injective (Submodule.subtype_injective _)

end Work.SSGRoute.H1Dual
