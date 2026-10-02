import Mathlib
import Submission.Work.ThomBordism.coeff_pm_one_of_normalized

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

/-- A degree cast `h ▸ ·` applied to a scalar multiple of the reverse cast is the scalar multiple:
`h ▸ (m • (h⁻¹ ▸ x)) = m • x`. -/
private lemma cast_zsmul_symm_cast {α : Type*} {P : α → Type*} [∀ a, SMul ℤ (P a)]
    {a b : α} (h : a = b) (m : ℤ) (x : P b) : h ▸ (m • (h.symm ▸ x)) = m • x := by
  cases h; rfl

theorem pieceRes_singleton_eq_smul {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (T : Work.Thom.ThomClass Z n)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (b : B) (U : Set B)
    (hU : U ⊆ Z.baseSet (Z.indexAt b)) (hb : b ∈ U) (d : Work.Thom.Coh ℤ 0 ↥U)
    (hd : (ModuleCat.Hom.hom (Work.Thom.PieceRes Z U n)) T.τ
        = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n U
            ((Work.Thom.localThomOfChart Z n e (Z.indexAt b) U hU).τ) 0 d)) :
    (ModuleCat.Hom.hom (Work.Thom.PieceRes Z ({b} : Set B) n)) T.τ
      = (Work.Thom.ptEv ⟨b, hb⟩ d) •
          ((Work.Thom.localThomOfChart Z n e (Z.indexAt b) ({b} : Set B)
            (fun _ hy => by
              rw [Set.mem_singleton_iff] at hy
              exact hy ▸ Z.mem_baseSet_at b)).τ) := by
  set hbsub : ({b} : Set B) ⊆ Z.baseSet (Z.indexAt b) :=
    fun _ hy => by rw [Set.mem_singleton_iff] at hy; exact hy ▸ Z.mem_baseSet_at b
  have h1 := Work.Thom.PieceRes_singleton_eq Z n T (Z.indexAt b) hU e d hd b hb hbsub
  rw [h1, Work.Thom.CohMap_ptIncl_smul U b hb d, map_zsmul]
  show (Nat.zero_add n) ▸ ((Work.Thom.ptEv ⟨b, hb⟩ d) •
      ((Work.Thom.localThomMap Z n ({b} : Set B)
        ((Work.Thom.localThomOfChart Z n e (Z.indexAt b) ({b} : Set B) hbsub).τ) 0)
        (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥({b} : Set B))))))
    = (Work.Thom.ptEv ⟨b, hb⟩ d) •
        ((Work.Thom.localThomOfChart Z n e (Z.indexAt b) ({b} : Set B) hbsub).τ)
  rw [Work.Thom.localThomMap_oneH Z n ({b} : Set B)
        ((Work.Thom.localThomOfChart Z n e (Z.indexAt b) ({b} : Set B) hbsub).τ)]
  exact cast_zsmul_symm_cast
    (P := fun k => Work.Thom.PieceCoh Z ({b} : Set B) k) (Nat.zero_add n) _ _

end Work.ThomBordism
