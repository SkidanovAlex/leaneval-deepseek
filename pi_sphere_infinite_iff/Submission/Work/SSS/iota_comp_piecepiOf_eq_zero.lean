import Mathlib
import Submission.Work.SSS.serreE1EZ

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

noncomputable section

/-- **The projection to the σ-piece kills the generators carried by `∂T_σ`.**

For `f : X ⟶ Y`, a simplex `σ : Δ[P] ⟶ Y` and the pullback `T_σ = Work.SSS.pullAlong f σ`, a
simplex `w` of `T_σ` lying in the boundary subcomplex
`Work.SSS.bdryAlong f σ = (∂Δ[P]).preimage (pullback.fst σ f)` has zero image under the quotient
projection `Work.SSS.pieceπOf f σ : C(T_σ) ⟶ C(T_σ)/C(∂T_σ)`.

This is the analogue of `Work.SSS.iota_bdry_comp_pi_eq_zero` (stated in
`Submission/Work/SSS/grFMap.lean` for the `nIndex`-indexed simplices and `pieceπ`): the same
unfolding, with `pieceπOf f σ` definitionally the cokernel projection
`cokernel.π (sCCMap (bdryAlong f σ).ι)` (`Work.SSS.pieceπOf_eq`).  The proof is:
`Work.SSS.bd_iota_eq` (the generator of `w` factors through `C(∂T_σ)`), then
`cokernel.condition`.

(Notation-free style so that the statement elaborates standalone.) -/
theorem iota_comp_piecepiOf_eq_zero {X Y : SSet.{0}} (f : X ⟶ Y) {P : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y) {k : ℕ}
    (w : (Work.SSS.pullAlong f σ).obj (Opposite.op (SimplexCategory.mk k)))
    (hw : w ∈ (Work.SSS.bdryAlong f σ).obj (Opposite.op (SimplexCategory.mk k))) :
    CategoryTheory.CategoryStruct.comp
        ((Work.SSS.pullAlong f σ).ιChainComplex (R := ModuleCat.of ℤ ℤ) w)
        ((Work.SSS.pieceπOf f σ).f k)
      = 0 := by
  -- The cokernel projection kills the boundary inclusion at each degree.
  have h2 : (sCCMap (Work.SSS.bdryAlong f σ).ι).f k ≫ (Work.SSS.pieceπOf f σ).f k = 0 := by
    have hc : sCCMap (Work.SSS.bdryAlong f σ).ι ≫ Work.SSS.pieceπOf f σ = 0 := by
      rw [Work.SSS.pieceπOf_eq]
      exact cokernel.condition _
    have h3 : ((sCCMap (Work.SSS.bdryAlong f σ).ι) ≫ Work.SSS.pieceπOf f σ).f k = 0 := by
      rw [hc, HomologicalComplex.zero_f]
    rw [HomologicalComplex.comp_f] at h3
    exact h3
  -- The generator of `w` factors through the boundary subcomplex.
  have hb : (Work.SSS.pullAlong f σ).ιChainComplex (R := ModuleCat.of ℤ ℤ) w =
      (((Work.SSS.bdryAlong f σ : (Work.SSS.pullAlong f σ).Subcomplex)) : SSet).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) ⟨w, hw⟩ ≫
        (sCCMap (Work.SSS.bdryAlong f σ).ι).f k :=
    (SSet.ι_chainComplexMap_f (C := ModuleCat ℤ)
      (X := (((Work.SSS.bdryAlong f σ : (Work.SSS.pullAlong f σ).Subcomplex)) : SSet))
      (Y := Work.SSS.pullAlong f σ) (R := ModuleCat.of ℤ ℤ)
      ((Work.SSS.bdryAlong f σ).ι) ⟨w, hw⟩).symm
  rw [hb]
  simp only [Category.assoc, h2, comp_zero]

end

end Work.SSS
