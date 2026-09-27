import Mathlib
import Submission.Work.KT.HopfK.Disk
import Submission.Work.KT.hk_relprod
import Submission.Work.KT.HopfK.diskW_map_evalC
import Submission.Work.KT.HopfK.hk_diskW_bdry_cases

namespace Work.KT.HopfK

open _root_.Matrix

noncomputable section

/-- Algebraic core: if at a point the evaluated matrices satisfy one of the three
compatible degeneracies, the `W`-construction specialises to the constant matrix
`diag(1_p, 0)` (i.e. `oneBlk`). -/
lemma hk_diskW_eval_eq_oneBlk_of_cases {n : ℕ}
    (Pz Qz Ez : Matrix (Fin n) (Fin n) ℂ) (c s : ℂ)
    (hPz : Pz * Pz = Pz) (hQz : Qz * Qz = Qz) (hEz : Ez * Ez = Ez)
    (hcs : c * c + s * s = 1)
    (hcase : (Pz = Ez ∧ c = 0 ∧ s = 1) ∨ (Pz = Ez ∧ Qz = Ez) ∨ (Qz = Ez ∧ c = 1 ∧ s = 0)) :
    diskW Pz Qz Ez c s = oneBlk ℂ (n * n + n * n) := by
  have hC : diskC Pz Qz Ez c s = diskQ1 Pz Qz Ez := by
    simpa only [diskC, diskQ2, diskQ1] using hkW_rot_cases Pz Qz Ez c s hcs hcase
  have hCidem : diskC Pz Qz Ez c s * diskC Pz Qz Ez c s = diskC Pz Qz Ez c s :=
    diskC_idem Pz Qz Ez hPz hQz hEz hcs
  unfold diskW
  rw [← hC]
  exact hkW_diag hCidem

/-- At a boundary point, evaluation of `hopfDiskW` is the constant matrix `diag(1_p,0)`. -/
lemma hopfDiskW_map_eval_bdry (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (n r : ℕ) (δ : ℝ) (χ : C(Ball (Eu m × Eu m), ℝ))
    (hχ : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
    (P Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)))
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hPc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).2‖ →
      P.map (evalC z) = diagIdemMat r n)
    (hQc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).1‖ →
      Q.map (evalC z) = diagIdemMat r n)
    (hδ : 1 - Real.sqrt 3 / 2 ≤ δ)
    (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)) :
    (hopfDiskW m n r χ P Q).map (evalC z) = oneBlk ℂ (n * n + n * n) := by
  have hmap := diskW_map_evalC (T := Ball (Eu m × Eu m)) z P Q
      (matConst (C(Ball (Eu m × Eu m), ℂ)) (diagIdemMat r n)) (diskCos χ) (diskSin χ)
  rw [show hopfDiskW m n r χ P Q
      = diskW P Q (matConst (C(Ball (Eu m × Eu m), ℂ)) (diagIdemMat r n))
          (diskCos χ) (diskSin χ) from rfl, hmap]
  rw [rot_matConst_map z (diagIdemMat r n)]
  refine hk_diskW_eval_eq_oneBlk_of_cases _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
  · rw [← Matrix.map_mul, hP]
  · rw [← Matrix.map_mul, hQ]
  · exact diagIdemMat_isIdem r n
  · have h := congrArg (evalC z) (diskCos_sq_add_diskSin_sq χ)
    simpa only [map_add, map_mul, map_one] using h
  · have hcase := hk_diskW_bdry_cases m μ n r δ χ hχ P Q hPc hQc hδ z hz
    simpa only [ContinuousMap.evalAlgHom_apply] using hcase

theorem hk_diskW_mem_Kpair (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (n r : ℕ) (δ : ℝ) (χ : C(Ball (Eu m × Eu m), ℝ))
    (hχ : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
    (P Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)))
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hPc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).2‖ →
      P.map (evalC z) = diagIdemMat r n)
    (hQc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).1‖ →
      Q.map (evalC z) = diagIdemMat r n)
    (hδ : 1 - Real.sqrt 3 / 2 ≤ δ) :
    ∀ i j : Fin ((n * n + n * n) + (n * n + n * n)),
      hopfDiskW m n r χ P Q i j ∈ Kpair (Eu m × Eu m) := by
  intro i j
  show ∀ a ∈ bdry (Eu m × Eu m), ∀ a' ∈ bdry (Eu m × Eu m),
    (hopfDiskW m n r χ P Q) i j a = (hopfDiskW m n r χ P Q) i j a'
  intro a ha a' ha'
  have h1 := hopfDiskW_map_eval_bdry m μ n r δ χ hχ P Q hP hQ hPc hQc hδ a ha
  have h2 := hopfDiskW_map_eval_bdry m μ n r δ χ hχ P Q hP hQ hPc hQc hδ a' ha'
  have e1 : (hopfDiskW m n r χ P Q) i j a = (oneBlk ℂ (n * n + n * n)) i j := by
    have h := congrFun (congrFun h1 i) j
    rwa [Matrix.map_apply] at h
  have e2 : (hopfDiskW m n r χ P Q) i j a' = (oneBlk ℂ (n * n + n * n)) i j := by
    have h := congrFun (congrFun h2 i) j
    rwa [Matrix.map_apply] at h
  rw [e1, e2]

end

end Work.KT.HopfK
