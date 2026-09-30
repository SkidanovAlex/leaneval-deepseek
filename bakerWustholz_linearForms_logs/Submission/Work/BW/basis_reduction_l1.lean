import Mathlib
import Submission.Work.BW.minkowski_defs
import Submission.Work.BW.basisRed_defs
import Submission.Work.BW.basisRed_core
import Submission.Work.BW.basisRed_exists_indep
import Submission.Work.BW.basisRed_wNorm_isLatticeNorm
import Submission.Work.BW.basisRed_bridge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The weighted `ℓ¹` norm of `toR (w j)` is the weighted `ℓ¹` norm of the `j`-th column of
`A * U`, where `U` is the matrix with rows `w`. -/
lemma wNorm_toR_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → ℝ)
    (w : Fin n → (Fin n → ℤ)) (j : Fin n) :
    Work.BW.wNorm A c (Work.BW.toR (w j))
      = Work.BW.wl1 c (fun i => (((A * Matrix.of (fun i j => w j i)) i j : ℤ) : ℝ)) := by
  simp only [Work.BW.wNorm, Work.BW.wl1, Work.BW.toR, Matrix.mulVec, Matrix.mul_apply,
    Matrix.of_apply, dotProduct, Matrix.map_apply, Int.coe_castRingHom]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  push_cast
  ring

theorem basis_reduction_l1 {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det ≠ 0)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) :
    ∃ U : Matrix (Fin n) (Fin n) ℤ, IsUnit U.det ∧
      ∏ j, Work.BW.wl1 c (fun i => (((A * U) i j : ℤ) : ℝ))
        ≤ (n.factorial : ℝ) / 2 ^ (n - 1) *
          ∏ j : Fin n, Work.BW.succMin (Work.BW.latOf A) (Work.BW.wl1 c) (j.1 + 1) := by
  have hF : IsLatticeNorm (wNorm A c) := basisRed_wNorm_isLatticeNorm A hA c hc
  obtain ⟨u, hind, hbd⟩ := basisRed_exists_indep hF
  obtain ⟨w, hunit, hprod⟩ := exists_basis_of_indep hn hF u hind hbd
  refine ⟨Matrix.of (fun i j => w j i), hunit, ?_⟩
  have hleft : ∏ j : Fin n, wl1 c (fun i => (((A * Matrix.of (fun i j => w j i)) i j : ℤ) : ℝ))
      = ∏ j : Fin n, wNorm A c (toR (w j)) :=
    Finset.prod_congr rfl (fun j _ => (wNorm_toR_eq A c w j).symm)
  rw [hleft]
  refine le_trans hprod ?_
  have hright : ∏ j : Fin n, succMinL (wNorm A c) (j.1 + 1)
      = ∏ j : Fin n, succMin (latOf A) (wl1 c) (j.1 + 1) :=
    Finset.prod_congr rfl (fun j _ => basisRed_bridge A hA c (j.1 + 1))
  rw [hright]

end Work.BW
