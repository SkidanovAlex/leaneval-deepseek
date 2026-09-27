import Mathlib
import Submission.Work.KT.HopfK.hk_diskW_mem_Kpair
import Submission.Work.KT.HopfK.hk_diskW_map
import Submission.Work.KT.HopfK.diskW_map_evalC

namespace Work.KT.HopfK

open _root_.Matrix

noncomputable section

/-- The base part of the constant diagonal idempotent `diag(1_r,0)` over the mapping cone, at a
point `t` of the base, is the complex diagonal idempotent `diag(1_r,0)`. -/
lemma coneDiag_map_evalT (m r n : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (t : Tgt m) :
    ((coneDiag m f r n).2).map (evalT m f t).toRingHom = diagIdemMat r n := by
  have hdiag : diagIdemMat r n =
      Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then (1 : ℂ) else 0) := rfl
  have hE2 : (coneDiag m f r n).2 = Matrix.diagonal
      (fun i : Fin n => if (i : ℕ) < r then (1 : coneAlg f) else 0) := rfl
  rw [hE2, hdiag]
  ext i j
  rw [Matrix.map_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hi : (i : ℕ) < r <;> simp [hi]
  · rw [if_neg hij, if_neg hij, map_zero]

/-- **The base part of the `W`-construction is the trivial idempotent.**  If the two idempotents
`P`, `Q` over `C(Tgt m, ℂ)` agree with the trivial idempotent `E` on the two contractible caps
`capTplus`, `capTminus`, then the `W`-construction with the base angle `χ = chiB m` specialises to
the constant block matrix `diag(1_{n*n + n*n}, 0)`: on each cap the rotation angle is a multiple of
`π/2`, so the rotated `Q₂` collapses to `Q₁` pointwise. -/
lemma diskW_base_oneBlk_aux (m n r : ℕ)
    (P Q E : Matrix (Fin n) (Fin n) C(Tgt m, ℂ))
    (hP : P * P = P) (hQ : Q * Q = Q) (hEe : E * E = E)
    (hE : ∀ t : Tgt m, E.map (evalC t) = diagIdemMat r n)
    (hPb : ∀ t : Tgt m, t ∈ capTplus m → P.map (evalC t) = diagIdemMat r n)
    (hQb : ∀ t : Tgt m, t ∈ capTminus m → Q.map (evalC t) = diagIdemMat r n) :
    diskW P Q E (hkCos m) (hkSin m) = oneBlk (C(Tgt m, ℂ)) (n * n + n * n) := by
  have hCl : diskC P Q E (hkCos m) (hkSin m) = diskQ1 P Q E := by
    apply rot_eq_of_eval
    intro t
    rw [diskC_map_evalC t, diskQ1_map_evalC t]
    rw [hE t]
    rw [show evalC t (hkCos m) = hkCos m t from rfl,
      show evalC t (hkSin m) = hkSin m t from rfl]
    refine hkW_rot_cases (P.map (evalC t)) (Q.map (evalC t)) (diagIdemMat r n)
      (hkCos m t) (hkSin m t) ?_ ?_
    · have h := congrArg (evalC t) (hkCos_sq_add_hkSin_sq m)
      simpa using h
    · by_cases h : (1 / 2 : ℝ) ≤ tgtHeight m t
      · exact Or.inl ⟨hPb t (by show -(1 / 2 : ℝ) ≤ tgtHeight m t; linarith),
          hkCos_eq_zero_of m h, hkSin_eq_one_of m h⟩
      · rw [not_le] at h
        by_cases h' : tgtHeight m t ≤ -(1 / 2 : ℝ)
        · exact Or.inr (Or.inr ⟨hQb t (by show tgtHeight m t ≤ (1 / 2 : ℝ); linarith),
            hkCos_eq_one_of m h', hkSin_eq_zero_of m h'⟩)
        · rw [not_le] at h'
          exact Or.inr (Or.inl ⟨hPb t (by show -(1 / 2 : ℝ) ≤ tgtHeight m t; linarith),
            hQb t (by show tgtHeight m t ≤ (1 / 2 : ℝ); linarith)⟩)
  unfold diskW
  rw [hCl]
  exact hkW_diag (diskQ1_idem P Q E hP hQ hEe)

theorem hk_diskW_base_oneBlk (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) (n r : ℕ)
    (p q : Matrix (Fin n) (Fin n) (coneAlg (hopfKMap m μ)))
    (hp : p * p = p) (hq : q * q = q)
    (hpb : ∀ t : Tgt m, t ∈ capTplus m → p.map (evalT m (hopfKMap m μ) t) = diagIdemMat r n)
    (hqb : ∀ t : Tgt m, t ∈ capTminus m → q.map (evalT m (hopfKMap m μ) t) = diagIdemMat r n) :
    diskW (p.map (coneToT (hopfKMap m μ)).toRingHom)
        (q.map (coneToT (hopfKMap m μ)).toRingHom)
        ((coneDiag m (hopfKMap m μ) r n).2.map (coneToT (hopfKMap m μ)).toRingHom)
        (hkCos m) (hkSin m) = oneBlk (C(Tgt m, ℂ)) (n * n + n * n) := by
  have hEidem : (coneDiag m (hopfKMap m μ) r n).2 * (coneDiag m (hopfKMap m μ) r n).2
      = (coneDiag m (hopfKMap m μ) r n).2 :=
    coneDiag_isIdem m (hopfKMap m μ) r n
  have hP : (p.map (coneToT (hopfKMap m μ)).toRingHom)
      * (p.map (coneToT (hopfKMap m μ)).toRingHom)
      = p.map (coneToT (hopfKMap m μ)).toRingHom := by
    rw [← Matrix.map_mul, hp]
  have hQ : (q.map (coneToT (hopfKMap m μ)).toRingHom)
      * (q.map (coneToT (hopfKMap m μ)).toRingHom)
      = q.map (coneToT (hopfKMap m μ)).toRingHom := by
    rw [← Matrix.map_mul, hq]
  have hEe : ((coneDiag m (hopfKMap m μ) r n).2.map (coneToT (hopfKMap m μ)).toRingHom)
      * ((coneDiag m (hopfKMap m μ) r n).2.map (coneToT (hopfKMap m μ)).toRingHom)
      = (coneDiag m (hopfKMap m μ) r n).2.map (coneToT (hopfKMap m μ)).toRingHom := by
    rw [← Matrix.map_mul, hEidem]
  have hE : ∀ t : Tgt m,
      ((coneDiag m (hopfKMap m μ) r n).2.map (coneToT (hopfKMap m μ)).toRingHom).map (evalC t)
        = diagIdemMat r n := by
    intro t
    rw [show ((coneDiag m (hopfKMap m μ) r n).2.map
          (coneToT (hopfKMap m μ)).toRingHom).map (evalC t)
        = ((coneDiag m (hopfKMap m μ) r n).2).map (evalT m (hopfKMap m μ) t).toRingHom from by
      rw [Matrix.map_map]; rfl]
    exact coneDiag_map_evalT m r n (hopfKMap m μ) t
  have hPb : ∀ t : Tgt m, t ∈ capTplus m →
      (p.map (coneToT (hopfKMap m μ)).toRingHom).map (evalC t) = diagIdemMat r n := by
    intro t ht
    rw [show (p.map (coneToT (hopfKMap m μ)).toRingHom).map (evalC t)
        = p.map (evalT m (hopfKMap m μ) t).toRingHom from by rw [Matrix.map_map]; rfl]
    exact hpb t ht
  have hQb : ∀ t : Tgt m, t ∈ capTminus m →
      (q.map (coneToT (hopfKMap m μ)).toRingHom).map (evalC t) = diagIdemMat r n := by
    intro t ht
    rw [show (q.map (coneToT (hopfKMap m μ)).toRingHom).map (evalC t)
        = q.map (evalT m (hopfKMap m μ) t).toRingHom from by rw [Matrix.map_map]; rfl]
    exact hqb t ht
  exact diskW_base_oneBlk_aux m n r _ _ _ hP hQ hEe hE hPb hQb

end

end Work.KT.HopfK
