import Mathlib
import Submission.Work.SSS.iotaF_isCycle
import Submission.Work.KunnethEZ.ezChain_isCycle

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory in
/-- The image of an arbitrary `0`-chain of `F` under `iotaFGen` is a cycle of the σ-piece.  The
simplex-level `Work.SSS.IotaAux.iotaFGen_zero_d` covers only the generators of the `0`-chains; this
is its chain-level (linearised) form, obtained by expanding `z` in the generators of the fibre
`0`-chains (`Work.KunnethEZ.chain_eq_sum_gen`). -/
theorem iotaFGen_zero_cycle {Xf Yf F : SSet.{0}} (f : Xf ⟶ Yf) (P : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Yf)
    (ez : ((SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⊗ F) ⟶ Work.SSS.pullAlong f σ)
    (hez : ez ≫ pullback.fst σ f = SemiCartesianMonoidalCategory.fst _ _)
    (z : (Work.SSS.sCC F).X 0) :
    (Work.SSS.pieceAlong f σ).d P ((ComplexShape.down ℕ).next P)
      ((Work.SSS.iotaFGen f P 0 σ ez).hom z) = 0 := by
  rcases Nat.eq_zero_or_pos P with hP0 | hPpos
  · -- `P = 0`: the σ-piece has no degree below `0`, so the differential out of degree `0` vanishes
    subst hP0
    rw [show (ComplexShape.down ℕ).next 0 = 0 from ChainComplex.next_nat_zero]
    rw [HomologicalComplex.shape _ 0 0 (by rw [ComplexShape.down_Rel]; omega)]
    simp
  · -- `P = P' + 1`: expand `z` in the generators `genC F x` of the fibre `0`-chains and apply the
    -- simplex-level statement `IotaAux.iotaFGen_zero_d` to each of them
    obtain ⟨P', rfl⟩ : ∃ P', P = P' + 1 := ⟨P - 1, by omega⟩
    rw [show (ComplexShape.down ℕ).next (P' + 1) = P' from ChainComplex.next_nat_succ P']
    rw [Work.KunnethEZ.chain_eq_sum_gen F 0 z]
    simp only [map_sum, map_zsmul]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    rw [IotaAux.iotaFGen_zero_d f P' σ ez hez x]
    exact zsmul_zero _

end Work.SSS
