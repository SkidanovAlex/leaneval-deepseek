import Mathlib
import Submission.Work.KT.HopfK.Interface
import Submission.Work.KT.HopfK.hk_diskW_mem_Kpair
import Submission.Work.KT.hk_relprod

namespace Work.KT.HopfK

/-!
# Reduction of the boundary class of the `W`-construction

At a boundary point `y₀` of the cell `D_{E×E}` the `W`-matrix `hopfDiskW m n r χ P Q` specialises
to the constant block matrix `oneBlk ℂ (n*n+n*n) = diag(1_{n*n+n*n}, 0)` (this is
`hopfDiskW_map_eval_bdry`).  Consequently the class
`[hopfDiskZ] - [diagMat (2n²) (4n²)] = [diag(1_{2n²},0)] - [diag(1_{2n²},0)]` is annihilated by the
augmentation `augPair (E×E) y₀ : Kpair (E×E) → ℂ`, which is the statement proved here.
-/

noncomputable section

/-! ## The block matrix `oneBlk` is the diagonal idempotent `diag(1_p,0)` -/

private lemma finSumFinEquiv_symm_of_lt {p : ℕ} (i : Fin (p+p)) (hi : (i:ℕ) < p) :
    finSumFinEquiv.symm i = Sum.inl ⟨(i:ℕ), hi⟩ := by
  rw [← finSumFinEquiv_symm_apply_castAdd (n := p) (x := ⟨(i:ℕ), hi⟩)]
  congr 1

private lemma finSumFinEquiv_symm_of_ge {p : ℕ} (i : Fin (p+p)) (hi : p ≤ (i:ℕ)) :
    finSumFinEquiv.symm i = Sum.inr ⟨(i:ℕ) - p, by omega⟩ := by
  rw [← finSumFinEquiv_symm_apply_natAdd (m := p) (x := ⟨(i:ℕ) - p, by omega⟩)]
  congr 1
  apply Fin.ext
  show (i:ℕ) = ((Fin.natAdd p ⟨(i:ℕ) - p, by omega⟩ : Fin (p+p)) : ℕ)
  have : ((Fin.natAdd p ⟨(i:ℕ) - p, by omega⟩ : Fin (p+p)) : ℕ) = p + ((i:ℕ) - p) := rfl
  omega

/-- `oneBlk ℂ p`, reindexed, is the diagonal matrix `diag(1_p, 0)`. -/
private lemma oneBlk_eq_diagMat_coe (p : ℕ) :
    Work.KT.oneBlk ℂ p = (Work.KT.diagMat ℂ p (p + p)).2 := by
  show Work.KT.oneBlk ℂ p
    = Matrix.diagonal (fun i : Fin (p+p) => if (i:ℕ) < p then (1:ℂ) else 0)
  ext i j
  rw [Work.KT.oneBlk, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diagonal_apply]
  by_cases hi : (i:ℕ) < p
  · rw [finSumFinEquiv_symm_of_lt i hi]
    by_cases hj : (j:ℕ) < p
    · rw [finSumFinEquiv_symm_of_lt j hj, Matrix.fromBlocks_apply₁₁, Matrix.one_apply, if_pos hi]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij]
        have : ¬ (⟨(i:ℕ), hi⟩ : Fin p) = ⟨(j:ℕ), hj⟩ := by
          rw [Fin.ext_iff]; exact fun h => hij (Fin.ext h)
        rw [if_neg this]
    · push Not at hj
      rw [finSumFinEquiv_symm_of_ge j hj, Matrix.fromBlocks_apply₁₂, if_neg]
      · simp
      · intro h; rw [h] at hi; omega
  · push Not at hi
    rw [finSumFinEquiv_symm_of_ge i hi]
    by_cases hj : (j:ℕ) < p
    · rw [finSumFinEquiv_symm_of_lt j hj, Matrix.fromBlocks_apply₂₁, if_neg]
      · simp
      · intro h; rw [← h] at hj; omega
    · push Not at hj
      rw [finSumFinEquiv_symm_of_ge j hj, Matrix.fromBlocks_apply₂₂]
      simp [hi]

/-- `(p+p, oneBlk ℂ p) = diagMat ℂ p (p+p)`, as elements of `Mat ℂ`. -/
private lemma oneBlkMat_eq_diagMat (p : ℕ) :
    (⟨p + p, Work.KT.oneBlk ℂ p⟩ : Work.KT.Mat ℂ) = Work.KT.diagMat ℂ p (p + p) := by
  rw [show Work.KT.oneBlk ℂ p = (Work.KT.diagMat ℂ p (p + p)).2 from oneBlk_eq_diagMat_coe p]
  rfl

theorem hk_bdry_reduced (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) (n r : ℕ) (δ : ℝ)
    (χ : C(Ball (Eu m × Eu m), ℝ))
    (hχ : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
    (P Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)))
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hPc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).2‖ →
      P.map (evalC z) = diagIdemMat r n)
    (hQc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).1‖ →
      Q.map (evalC z) = diagIdemMat r n)
    (hδ : 1 - Real.sqrt 3 / 2 ≤ δ)
    (H : ∀ i j : Fin ((n * n + n * n) + (n * n + n * n)),
      hopfDiskW m n r χ P Q i j ∈ Kpair (Eu m × Eu m))
    (y0 : Ball (Eu m × Eu m)) (hy0 : y0 ∈ bdry (Eu m × Eu m)) :
    K0.mapA (augPair (Eu m × Eu m) y0)
      (cls (hopfDiskZ m n r χ P Q H)
        - cls (diagMat (Kpair (Eu m × Eu m)) (2 * (n * n)) (4 * (n * n)))) = 0 := by
  -- The trivial constant idempotent `E = diag(1_r,0)` over the cell algebra is idempotent.
  have hE : matConst (C(Ball (Eu m × Eu m), ℂ)) (diagIdemMat r n)
      * matConst (C(Ball (Eu m × Eu m), ℂ)) (diagIdemMat r n)
      = matConst (C(Ball (Eu m × Eu m), ℂ)) (diagIdemMat r n) := by
    rw [← matConst_mul]
    rw [show diagIdemMat r n * diagIdemMat r n = diagIdemMat r n from diagIdemMat_isIdem r n]
  -- The `W`-matrix is idempotent.
  have hWidem : hopfDiskW m n r χ P Q * hopfDiskW m n r χ P Q = hopfDiskW m n r χ P Q :=
    diskW_idem P Q _ hP hQ hE (diskCos_sq_add_diskSin_sq χ)
  -- Its value at the boundary point `y₀` is the constant `diag(1_{n*n+n*n},0)`.
  have hWval : ∀ i j : Fin ((n * n + n * n) + (n * n + n * n)),
      hopfDiskW m n r χ P Q i j y0 = oneBlk ℂ (n * n + n * n) i j := by
    intro i j
    have h := congrFun (congrFun
      (Work.KT.HopfK.hopfDiskW_map_eval_bdry m μ n r δ χ hχ P Q hP hQ hPc hQc hδ y0 hy0) i) j
    rwa [Matrix.map_apply] at h
  have hval : Function.Injective ⇑(((Kpair (Eu m × Eu m)).val).toRingHom) :=
    fun a b hab => Subtype.val_injective hab
  -- The `Kpair`-valued `W`-matrix, with its entrywise description made explicit.
  let L : Matrix (Fin ((n * n + n * n) + (n * n + n * n)))
      (Fin ((n * n + n * n) + (n * n + n * n))) (Kpair (Eu m × Eu m)) :=
    fun i j => ⟨hopfDiskW m n r χ P Q i j, H i j⟩
  have hZeq : hopfDiskZ m n r χ P Q H
      = (⟨(n * n + n * n) + (n * n + n * n), L⟩ : Mat (Kpair (Eu m × Eu m))) := rfl
  have hZ3 : L.map ((Kpair (Eu m × Eu m)).val.toRingHom) = hopfDiskW m n r χ P Q := by
    ext i j
    rfl
  rw [hZeq]
  -- `Z` is idempotent.
  have hZidem : Mat.IsIdem
      (⟨(n * n + n * n) + (n * n + n * n), L⟩ : Mat (Kpair (Eu m × Eu m))) := by
    show L * L = L
    apply Matrix.map_injective hval
    show (L * L).map ((Kpair (Eu m × Eu m)).val.toRingHom)
      = L.map ((Kpair (Eu m × Eu m)).val.toRingHom)
    rw [Matrix.map_mul, hZ3, hWidem]
  -- Evaluation of `Z` at the boundary augmentation.
  have hmat : L.map (augPair (Eu m × Eu m) y0).toRingHom = oneBlk ℂ (n * n + n * n) := by
    ext i j
    rw [Matrix.map_apply]
    show (augPair (Eu m × Eu m) y0) ⟨hopfDiskW m n r χ P Q i j, H i j⟩
      = oneBlk ℂ (n * n + n * n) i j
    rw [show (augPair (Eu m × Eu m) y0) ⟨hopfDiskW m n r χ P Q i j, H i j⟩
        = hopfDiskW m n r χ P Q i j y0 from rfl]
    exact hWval i j
  have hZmap : Mat.map (augPair (Eu m × Eu m) y0).toRingHom
      (⟨(n * n + n * n) + (n * n + n * n), L⟩ : Mat (Kpair (Eu m × Eu m)))
      = (⟨(n * n + n * n) + (n * n + n * n), oneBlk ℂ (n * n + n * n)⟩ : Mat ℂ) := by
    change (⟨(n * n + n * n) + (n * n + n * n),
        L.map (augPair (Eu m × Eu m) y0).toRingHom⟩ : Mat ℂ)
      = (⟨(n * n + n * n) + (n * n + n * n), oneBlk ℂ (n * n + n * n)⟩ : Mat ℂ)
    rw [hmat]
  have hDmap : (diagMat (Kpair (Eu m × Eu m)) (2 * (n * n)) (4 * (n * n))).map
      (augPair (Eu m × Eu m) y0).toRingHom = diagMat ℂ (2 * (n * n)) (4 * (n * n)) :=
    Mat.diagMat_map _ _ _
  have hmapAZ : K0.mapA (augPair (Eu m × Eu m) y0)
      (cls (⟨(n * n + n * n) + (n * n + n * n), L⟩ : Mat (Kpair (Eu m × Eu m))))
      = cls (⟨(n * n + n * n) + (n * n + n * n), oneBlk ℂ (n * n + n * n)⟩ : Mat ℂ) := by
    rw [K0map.map_cls]
    unfold mapCls
    rw [if_pos hZidem]
    exact congrArg cls hZmap
  have hmapAD : K0.mapA (augPair (Eu m × Eu m) y0)
      (cls (diagMat (Kpair (Eu m × Eu m)) (2 * (n * n)) (4 * (n * n))))
      = cls (diagMat ℂ (2 * (n * n)) (4 * (n * n))) := by
    rw [K0map.map_cls]
    unfold mapCls
    rw [if_pos (diagMat_isIdem (Kpair (Eu m × Eu m)) (2 * (n * n)) (4 * (n * n)))]
    exact congrArg cls hDmap
  -- Both classes are the class of a rank-`2n²` idempotent of size `4n²` over `ℂ`.
  rw [map_sub, hmapAZ, hmapAD]
  rw [show cls (⟨(n * n + n * n) + (n * n + n * n), oneBlk ℂ (n * n + n * n)⟩ : Mat ℂ)
      = cls (diagMat ℂ (2 * (n * n)) (4 * (n * n))) from by
    rw [oneBlkMat_eq_diagMat (n * n + n * n),
      show (n * n + n * n) + (n * n + n * n) = 4 * (n * n) from by ring,
      show n * n + n * n = 2 * (n * n) from by ring]]
  simp

end

end Work.KT.HopfK
