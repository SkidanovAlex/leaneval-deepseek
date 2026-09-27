import Mathlib
import Submission.Work.KT.EG.KLG.kappa_bott_defs
import Submission.Work.KT.kappa_span

namespace Work.KT.EG.KLG


/-- `Bott.blk 0` is the identity on matrices (the `Fin 0` block is empty). -/
private lemma blk_zero_aux {R : Type} [Ring R] {N M : ℕ} (A : Matrix (Fin N) (Fin M) R) :
    Work.KT.Bott.blk 0 A = A := by
  ext i j
  have hi : finSumFinEquiv.symm i = Sum.inl i := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext rfl
  have hj : finSumFinEquiv.symm j = Sum.inl j := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext rfl
  rw [Work.KT.Bott.blk, Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj]
  simp only [Matrix.fromBlocks_apply₁₁]

theorem mvN_clutch_of_data (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ)
    (F : Matrix (Fin (n + n * 2)) (Fin (n + n * 2)) ↥(Work.KT.Fund.pullAlg2 X))
    (w : (Matrix (Fin n) (Fin n) C(X × Work.KT.Sph ℂ, ℂ))ˣ)
    (SA₁ SA₂ : Matrix (Fin n) (Fin (n + n * 2)) C(X × Work.KT.Ball ℂ, ℂ))
    (TB₁ TB₂ : Matrix (Fin (n + n * 2)) (Fin n) C(X × Work.KT.Ball ℂ, ℂ))
    (h₁ : TB₁ * SA₁ = F.map (Work.KT.Fund.prF X))
    (h₂ : SA₁ * TB₁ = 1)
    (h₃ : TB₂ * SA₂ = F.map (Work.KT.Fund.prS X))
    (h₄ : SA₂ * TB₂ = 1)
    (hu₁ : (↑w : Matrix (Fin n) (Fin n) C(X × Work.KT.Sph ℂ, ℂ)) *
        SA₁.map (⇑(Work.KT.Fund.bdryRestrict X))
      = SA₂.map (⇑(Work.KT.Fund.bdryRestrict X)))
    (hu₂ : TB₁.map (⇑(Work.KT.Fund.bdryRestrict X))
      = TB₂.map (⇑(Work.KT.Fund.bdryRestrict X)) *
        (↑w : Matrix (Fin n) (Fin n) C(X × Work.KT.Sph ℂ, ℂ))) :
    Work.KT.Mat.MvN (⟨n + n * 2, F⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
      (Work.KT.Fund.clutchIdem X n w
        (Work.KT.Fund.liftOf X (w : Matrix (Fin n) (Fin n) C(X × Work.KT.Sph ℂ, ℂ)))
        (Work.KT.Fund.liftOf X ((w⁻¹ : (Matrix (Fin n) (Fin n) C(X × Work.KT.Sph ℂ, ℂ))ˣ) :
          Matrix (Fin n) (Fin n) C(X × Work.KT.Sph ℂ, ℂ)))
        (Work.KT.Fund.liftOf_spec X (w : Matrix (Fin n) (Fin n) C(X × Work.KT.Sph ℂ, ℂ)))
        (Work.KT.Fund.liftOf_spec X ((w⁻¹ : (Matrix (Fin n) (Fin n) C(X × Work.KT.Sph ℂ, ℂ))ˣ) :
          Matrix (Fin n) (Fin n) C(X × Work.KT.Sph ℂ, ℂ)))) := by
  have hb₁ : TB₁ * SA₁ = Work.KT.Bott.blk 0 (F.map (Work.KT.Fund.prF X)) := by
    rw [h₁, blk_zero_aux]
  have hb₂ : TB₂ * SA₂ = Work.KT.Bott.blk 0 (F.map (Work.KT.Fund.prS X)) := by
    rw [h₃, blk_zero_aux]
  have hmvN := Work.KT.clutchIdem_mvN X (n + n * 2) n 0 F SA₁ TB₁ SA₂ TB₂
    hb₁ h₂ hb₂ h₄ w hu₁ hu₂
  have hsum : Work.KT.Mat.sum (⟨n + n * 2, F⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
      (Work.KT.Mat.one ↥(Work.KT.Fund.pullAlg2 X) 0) = ⟨n + n * 2, F⟩ := by
    show (⟨(n + n * 2) + 0, Work.KT.Bott.blk 0 F⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
      = ⟨n + n * 2, F⟩
    rw [blk_zero_aux]
    rfl
  rw [hsum] at hmvN
  exact hmvN

end Work.KT.EG.KLG
