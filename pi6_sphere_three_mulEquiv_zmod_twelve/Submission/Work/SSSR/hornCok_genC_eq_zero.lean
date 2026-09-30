import Mathlib
import Submission.Work.SSSR.serreE1PieceIotaDefs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial
noncomputable section

/-- The chain map `C(pieceHorn f σ) ⟶ C(pullAlong f σ)` sends the generator of a horn simplex
`z` to the generator of the same simplex `z`, regarded in `C(T_σ)`. -/
lemma sCCMap_pieceHorn_ι_ιChainComplex_eq {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) {k : ℕ}
    (z : (Work.SSSR.pullAlong f σ).obj (Opposite.op (SimplexCategory.mk k)))
    (hz : z ∈ (Work.SSSR.pieceHorn f σ).obj (Opposite.op (SimplexCategory.mk k))) :
    (Work.SSSR.sCCMap R (Work.SSSR.pieceHorn f σ).ι).f k
      ((SSet.ιChainComplex (X := (Work.SSSR.pieceHorn f σ : SSet.{0}))
        (R := ModuleCat.of R R) ⟨z, hz⟩).hom 1)
      = ((Work.SSSR.pullAlong f σ).ιChainComplex (R := ModuleCat.of R R) z).hom 1 := by
  have h := SSet.ι_chainComplexMap_f (X := (Work.SSSR.pieceHorn f σ : SSet.{0}))
    (Y := Work.SSSR.pullAlong f σ) (Work.SSSR.pieceHorn f σ).ι (ModuleCat.of R R) ⟨z, hz⟩
  have h2 := congrArg
    (fun (φ : ModuleCat.of R R ⟶ (Work.SSSR.sCC R (Work.SSSR.pullAlong f σ)).X k) => φ.hom 1) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2

theorem hornCok_genC_eq_zero {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) {k : ℕ}
    (z : (Work.SSSR.pullAlong f σ).obj (Opposite.op (SimplexCategory.mk k)))
    (hz : z ∈ (Work.SSSR.pieceHorn f σ).obj (Opposite.op (SimplexCategory.mk k))) :
    (Work.SSSR.hornCokπ f σ).f k
      (((Work.SSSR.pullAlong f σ).ιChainComplex (R := ModuleCat.of R R) z).hom 1) = 0 := by
  have hgen := sCCMap_pieceHorn_ι_ιChainComplex_eq (R := R) f σ z hz
  have hcond := cokernel.condition (Work.SSSR.bdryIncl f σ ≫ Work.SSSR.TIncl (R := R) f σ)
  have hcond2 := congrArg
    (fun (φ : Work.SSSR.sCC R (Work.SSSR.pieceHorn f σ) ⟶
        cokernel (Work.SSSR.bdryIncl f σ ≫ Work.SSSR.TIncl f σ)) =>
      (ModuleCat.Hom.hom (φ.f k))
        ((SSet.ιChainComplex (X := (Work.SSSR.pieceHorn f σ : SSet.{0}))
          (R := ModuleCat.of R R) ⟨z, hz⟩).hom 1)) hcond
  simp only [HomologicalComplex.comp_f] at hcond2
  rw [← hgen, Work.SSSR.sCCMap_pieceHorn_ι_eq]
  exact hcond2

end

end Work.SSSR
