import Mathlib
import Submission.Work.DSCOH.AltCechComplex

namespace Work.DSCOH

open CategoryTheory

theorem altCech_d_comp {X : Type*} [TopologicalSpace X] {A : Type*} [CommRing A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : Opposite (TopologicalSpace.Opens X) ⥤ ModuleCat A)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ)
    (T : {S : Finset ι // S.card = n + 2}) :
    (Work.DSCOH.altCech P U).d n (n+1) ≫
        (ModuleCat.ofHom (LinearMap.proj (φ := fun S : {S : Finset ι // S.card = n + 2} =>
          P.obj (Opposite.op (S.1.inf U))) T))
      = ∑ i ∈ T.1.attach,
          ((-1 : ℤ) ^ ((T.1.filter fun j => j < i.1)).card) •
            ((ModuleCat.ofHom (LinearMap.proj (φ := fun S : {S : Finset ι // S.card = n + 1} =>
                P.obj (Opposite.op (S.1.inf U)))
                ⟨T.1.erase i.1, by rw [Finset.card_erase_of_mem i.2, T.2]; omega⟩)) ≫
              (P.map (homOfLE (Finset.le_inf fun k hk =>
                Finset.inf_le (Finset.mem_of_mem_erase hk))).op)) := by
  -- The `n`-th differential of `altCech` is by construction the morphism induced by
  -- `altCechDiff`, and the target is the product of its components.
  simp only [Work.DSCOH.altCech, CochainComplex.of_d]
  rw [← ModuleCat.ofHom_comp]
  -- It therefore suffices to compare the underlying linear maps, where the statement is the
  -- definition of the `T`-component of `altCechDiff`.
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_ofHom, ModuleCat.hom_sum, ModuleCat.hom_zsmul, ModuleCat.hom_comp,
    Work.DSCOH.altCechDiff]
  -- Finally evaluate both sides at a point, where the projection onto the `T`-component of the
  -- product of `altCechDiff` is literally the `T`-th summand.
  ext x
  simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply, LinearMap.sum_apply,
    LinearMap.smul_apply]

end Work.DSCOH
