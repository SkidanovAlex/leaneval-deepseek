import Mathlib
import Submission.Work.WilE9G.Lagrange.LagBlocks

noncomputable section
open Classical

namespace Work.WilE9G.Lagrange

open Matrix

/-- Evaluation of the index equivalence `cMEquiv` on an `L`-index: the left summand of the left
summand. -/
theorem cMEquiv_symm_inl_inl {r j : ℕ} (i : Fin r) :
    (cMEquiv r j).symm (Sum.inl (Sum.inl i)) = Fin.castAdd (j + 1) i := by
  simp [cMEquiv]

/-- Evaluation of the index equivalence `cMEquiv` on an `h`-index (multiplier of `S`): the right
summand of the left summand. -/
theorem cMEquiv_symm_inl_inr {r j : ℕ} (b : Fin j) :
    (cMEquiv r j).symm (Sum.inl (Sum.inr b)) = Fin.natAdd r (Fin.castAdd 1 b) := by
  simp [cMEquiv]

/-- Evaluation of the index equivalence `cMEquiv` on the normalisation index `N` / multiplier
`μ₀`: the right summand. -/
theorem cMEquiv_symm_inr {r j : ℕ} (u : Fin 1) :
    (cMEquiv r j).symm (Sum.inr u) = Fin.natAdd r (Fin.natAdd j u) := by
  simp [cMEquiv]

/-- `lagJacTrue` is the block matrix `cM` built from `lagA2`, `lagW`, `lagG`, `mu`, `mu0` after the
index equivalence `cMEquiv`. -/
theorem lagJacTrue_eq_cM {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ) :
    Work.WilE9G.Lagrange.lagJacTrue S Phi c z mu mu0
      = (Work.WilE9G.Lagrange.cM (Work.WilE9G.Lagrange.lagA2 S Phi c z mu mu0)
          (Work.WilE9G.Lagrange.lagW S z) (Work.WilE9G.Lagrange.lagG S Phi c z) mu mu0).submatrix
          (Work.WilE9G.Lagrange.cMEquiv (1 + m) S.j)
          (Work.WilE9G.Lagrange.cMEquiv (1 + m) S.j) := by
  have key : ∀ A B : (Fin (1 + m) ⊕ Fin S.j) ⊕ Fin 1,
      lagJacTrue S Phi c z mu mu0 ((cMEquiv (1 + m) S.j).symm A)
          ((cMEquiv (1 + m) S.j).symm B)
        = cM (lagA2 S Phi c z mu mu0) (lagW S z) (lagG S Phi c z) mu mu0 A B := by
    intro A B
    rcases A with (i | b) | u <;> rcases B with (i' | b') | u' <;>
      simp only [cMEquiv_symm_inl_inl, cMEquiv_symm_inl_inr, cMEquiv_symm_inr,
        lagJacTrue, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right,
        cM_apply_inl_inl_inl_inl, cM_apply_inl_inl_inl_inr, cM_apply_inl_inl_inr,
        cM_apply_inl_inr_inl_inl, cM_apply_inl_inr_inl_inr, cM_apply_inl_inr_inr,
        cM_apply_inr_inl_inl, cM_apply_inr_inl_inr, cM_apply_inr_inr,
        lagA2, lagW, lagG]
  ext a l
  rw [Matrix.submatrix_apply]
  have h := key (cMEquiv (1 + m) S.j a) (cMEquiv (1 + m) S.j l)
  simpa only [Equiv.symm_apply_apply] using h

end Work.WilE9G.Lagrange
