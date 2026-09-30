import Mathlib
import Submission.Work.SSSR.serreE1EZ
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
noncomputable section

/-- **The projection to the σ-piece kills the generators carried by `∂T_σ`.**

For `f : X ⟶ Y`, a simplex `σ : Δ[P] ⟶ Y` and the pullback `T_σ = Work.SSSR.pullAlong f σ`, a
simplex `w` of `T_σ` lying in the boundary subcomplex
`Work.SSSR.bdryAlong f σ = (∂Δ[P]).preimage (pullback.fst σ f)` has zero image under the quotient
projection `Work.SSSR.pieceπOf f σ : C(T_σ) ⟶ C(T_σ)/C(∂T_σ)`.

This is the analogue of `Work.SSSR.iota_bdry_comp_pi_eq_zero` (stated in
`Submission/Work/SSS/grFMap.lean` for the `nIndex`-indexed simplices and `pieceπ R`): the same
unfolding, with `pieceπOf f σ` definitionally the cokernel projection
`cokernel.π (sCCMap R (bdryAlong f σ).ι)` (`Work.SSSR.pieceπOf_eq`).  The proof is:
`Work.SSSR.bd_iota_eq` (the generator of `w` factors through `C(∂T_σ)`), then
`cokernel.condition`.

(Notation-free style so that the statement elaborates standalone.) -/
theorem iota_comp_piecepiOf_eq_zero {X Y : SSet.{0}} (f : X ⟶ Y) {P : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y) {k : ℕ}
    (w : (Work.SSSR.pullAlong f σ).obj (Opposite.op (SimplexCategory.mk k)))
    (hw : w ∈ (Work.SSSR.bdryAlong f σ).obj (Opposite.op (SimplexCategory.mk k))) :
    CategoryTheory.CategoryStruct.comp
        ((Work.SSSR.pullAlong f σ).ιChainComplex (R := ModuleCat.of R R) w)
        ((Work.SSSR.pieceπOf f σ).f k)
      = 0 := by
  -- The cokernel projection kills the boundary inclusion at each degree.
  have h2 : (sCCMap R (Work.SSSR.bdryAlong f σ).ι).f k ≫ (Work.SSSR.pieceπOf f σ).f k = 0 := by
    have hc : sCCMap R (Work.SSSR.bdryAlong f σ).ι ≫ Work.SSSR.pieceπOf f σ = 0 := by
      rw [Work.SSSR.pieceπOf_eq]
      exact cokernel.condition _
    have h3 : ((sCCMap R (Work.SSSR.bdryAlong f σ).ι) ≫ Work.SSSR.pieceπOf f σ).f k = 0 := by
      rw [hc, HomologicalComplex.zero_f]
    rw [HomologicalComplex.comp_f] at h3
    exact h3
  -- The generator of `w` factors through the boundary subcomplex.
  have hb : (Work.SSSR.pullAlong f σ).ιChainComplex (R := ModuleCat.of R R) w =
      (((Work.SSSR.bdryAlong f σ : (Work.SSSR.pullAlong f σ).Subcomplex)) : SSet).ιChainComplex
          (R := ModuleCat.of R R) ⟨w, hw⟩ ≫
        (sCCMap R (Work.SSSR.bdryAlong f σ).ι).f k :=
    (SSet.ι_chainComplexMap_f (C := ModuleCat R)
      (X := (((Work.SSSR.bdryAlong f σ : (Work.SSSR.pullAlong f σ).Subcomplex)) : SSet))
      (Y := Work.SSSR.pullAlong f σ) (R := ModuleCat.of R R)
      ((Work.SSSR.bdryAlong f σ).ι) ⟨w, hw⟩).symm
  rw [hb]
  simp only [Category.assoc, h2, comp_zero]

end

end Work.SSSR
