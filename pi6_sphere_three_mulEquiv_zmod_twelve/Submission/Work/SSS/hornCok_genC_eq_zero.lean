import Mathlib
import Submission.Work.SSS.serreE1PieceIotaDefs

/-!
# The horn quotient kills the chain generators lying in the horn

For `f : X ⟶ Y`, a simplex `σ : Δ[s] ⟶ Y` and `Λ = pieceHorn f σ ≤ ∂T_σ ≤ T_σ = Δ[s] ×_Y X`,
the quotient map `hornCokπ f σ : C(T_σ) ⟶ C(T_σ)/C(Λ)` of `Work.SSS.serreE1PieceIotaDefs`
annihilates every chain generator `ι z` whose simplex `z` already lies in the horn `Λ`.

This is the elementary (but indispensable) observation that the connecting maps of the short exact
sequence `0 → C(Λ) → C(∂T_σ) → C(∂T_σ)/C(Λ) → 0` are insensitive to how a horn chain is spelled
inside `C(T_σ)`: the generator of `z ∈ Λ` is in the image of `C(Λ) ⟶ C(T_σ)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial

noncomputable section

/-- The chain map `C(pieceHorn f σ) ⟶ C(pullAlong f σ)` sends the generator of a horn simplex
`z` to the generator of the same simplex `z`, regarded in `C(T_σ)`. -/
lemma sCCMap_pieceHorn_ι_ιChainComplex_eq {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) {k : ℕ}
    (z : (Work.SSS.pullAlong f σ).obj (Opposite.op (SimplexCategory.mk k)))
    (hz : z ∈ (Work.SSS.pieceHorn f σ).obj (Opposite.op (SimplexCategory.mk k))) :
    (Work.SSS.sCCMap (Work.SSS.pieceHorn f σ).ι).f k
      ((SSet.ιChainComplex (X := (Work.SSS.pieceHorn f σ : SSet.{0}))
        (R := ModuleCat.of ℤ ℤ) ⟨z, hz⟩).hom 1)
      = ((Work.SSS.pullAlong f σ).ιChainComplex (R := ModuleCat.of ℤ ℤ) z).hom 1 := by
  have h := SSet.ι_chainComplexMap_f (X := (Work.SSS.pieceHorn f σ : SSet.{0}))
    (Y := Work.SSS.pullAlong f σ) (Work.SSS.pieceHorn f σ).ι (ModuleCat.of ℤ ℤ) ⟨z, hz⟩
  have h2 := congrArg
    (fun (φ : ModuleCat.of ℤ ℤ ⟶ (Work.SSS.sCC (Work.SSS.pullAlong f σ)).X k) => φ.hom 1) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2

theorem hornCok_genC_eq_zero {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) {k : ℕ}
    (z : (Work.SSS.pullAlong f σ).obj (Opposite.op (SimplexCategory.mk k)))
    (hz : z ∈ (Work.SSS.pieceHorn f σ).obj (Opposite.op (SimplexCategory.mk k))) :
    (Work.SSS.hornCokπ f σ).f k
      (((Work.SSS.pullAlong f σ).ιChainComplex (R := ModuleCat.of ℤ ℤ) z).hom 1) = 0 := by
  have hgen := sCCMap_pieceHorn_ι_ιChainComplex_eq f σ z hz
  have hcond := cokernel.condition (Work.SSS.bdryIncl f σ ≫ Work.SSS.TIncl f σ)
  have hcond2 := congrArg
    (fun (φ : Work.SSS.sCC (Work.SSS.pieceHorn f σ) ⟶
        cokernel (Work.SSS.bdryIncl f σ ≫ Work.SSS.TIncl f σ)) =>
      (ModuleCat.Hom.hom (φ.f k))
        ((SSet.ιChainComplex (X := (Work.SSS.pieceHorn f σ : SSet.{0}))
          (R := ModuleCat.of ℤ ℤ) ⟨z, hz⟩).hom 1)) hcond
  simp only [HomologicalComplex.comp_f] at hcond2
  rw [← hgen, Work.SSS.sCCMap_pieceHorn_ι_eq]
  exact hcond2

end

end Work.SSS
