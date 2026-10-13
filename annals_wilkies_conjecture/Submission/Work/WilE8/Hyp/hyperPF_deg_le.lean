import Mathlib
import Submission.Work.WilE8.Hyp.Basic
import Submission.Work.WilE8.Clear.clearDenom_totalDegree_le

namespace Work.WilE8.Hyp

open WilkiesDesign WilkiesDesign.E

/-- The atom degree of the equation `uᵢ² + wᵢ² = 1` is at most `3`. -/
lemma totalDegree_sqPoly_le (n : ℕ) (i : Fin n) : (sqPoly n i).totalDegree ≤ 2 := by
  rw [sqPoly]
  calc ((MvPolynomial.X (Sum.inl (Fin.castAdd n i)) ^ 2 +
        MvPolynomial.X (Sum.inl (Fin.natAdd n i)) ^ 2 - 1 : EAPoly (n+n) 0)).totalDegree
      ≤ max ((MvPolynomial.X (Sum.inl (Fin.castAdd n i)) ^ 2 +
        MvPolynomial.X (Sum.inl (Fin.natAdd n i)) ^ 2 : EAPoly (n+n) 0)).totalDegree
        (1 : EAPoly (n+n) 0).totalDegree := MvPolynomial.totalDegree_sub _ _
    _ ≤ 2 := by
      rw [MvPolynomial.totalDegree_one]
      refine max_le ?_ (by norm_num)
      calc _ ≤ max ((MvPolynomial.X (Sum.inl (Fin.castAdd n i)) ^ 2 : EAPoly (n+n) 0)).totalDegree
            ((MvPolynomial.X (Sum.inl (Fin.natAdd n i)) ^ 2 : EAPoly (n+n) 0)).totalDegree :=
            MvPolynomial.totalDegree_add _ _
        _ = 2 := by rw [MvPolynomial.totalDegree_X_pow, MvPolynomial.totalDegree_X_pow]; norm_num

/-- The atom degree of the sign condition `wᵢ > 0` is at most `2`. -/
lemma totalDegree_wPoly_le (n : ℕ) (i : Fin n) : (wPoly n i).totalDegree ≤ 1 := by
  rw [wPoly, MvPolynomial.totalDegree_X]

/-- The total degree of the cleared-denominator equation is at most `n * Q.totalDegree`. -/
lemma totalDegree_clrPoly_le (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) :
    (clrPoly Q).totalDegree ≤ n * Q.totalDegree := by
  rw [clrPoly]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    (Work.WilE8.Clear.clearDenom_totalDegree_le Q)

/-- The degree of the semi-Pfaffian set `hyperPF Q` is bounded by `5n + 1 + n·deg Q`:
there are `n` equations `uᵢ² + wᵢ² = 1` of atom degree `3`, `n` sign conditions `wᵢ > 0` of
atom degree `2`, and the cleared denominator equation of atom degree `≤ n·deg Q + 1`. -/
theorem hyperPF_deg_le {n : ℕ} (Q : MvPolynomial (Fin n) ℝ) :
    (Work.WilE8.Hyp.hyperPF Q).deg ≤ 5 * n + 1 + n * Q.totalDegree := by
  have hdeg : (hyperPF Q).deg
      = (List.map atomDeg
          ((List.ofFn (sqPoly n) ++ [clrPoly Q]) ++ List.ofFn (wPoly n))).sum := by
    simp only [SemiPf.deg, hyperPF, Basic.deg, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
  rw [hdeg]
  have hsq : (List.map atomDeg (List.ofFn (sqPoly n))).sum ≤ 3 * n := by
    have h := List.sum_le_length_nsmul (List.map atomDeg (List.ofFn (sqPoly n))) 3
      (fun x hx => ?_)
    · rwa [List.length_map, List.length_ofFn, nsmul_eq_mul, Nat.mul_comm] at h
    · simp only [List.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      rw [List.mem_ofFn] at ha
      obtain ⟨i, rfl⟩ := ha
      simp only [atomDeg]
      have := totalDegree_sqPoly_le n i
      omega
  have hw : (List.map atomDeg (List.ofFn (wPoly n))).sum ≤ 2 * n := by
    have h := List.sum_le_length_nsmul (List.map atomDeg (List.ofFn (wPoly n))) 2
      (fun x hx => ?_)
    · rwa [List.length_map, List.length_ofFn, nsmul_eq_mul, Nat.mul_comm] at h
    · simp only [List.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      rw [List.mem_ofFn] at ha
      obtain ⟨i, rfl⟩ := ha
      simp only [atomDeg]
      have := totalDegree_wPoly_le n i
      omega
  have hclr : (List.map atomDeg [clrPoly Q]).sum ≤ n * Q.totalDegree + 1 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, atomDeg]
    have := totalDegree_clrPoly_le n Q
    omega
  calc (List.map atomDeg ((List.ofFn (sqPoly n) ++ [clrPoly Q]) ++ List.ofFn (wPoly n))).sum
      = ((List.map atomDeg (List.ofFn (sqPoly n))).sum + (List.map atomDeg [clrPoly Q]).sum)
          + (List.map atomDeg (List.ofFn (wPoly n))).sum := by
        rw [List.map_append, List.sum_append, List.map_append, List.sum_append]
    _ ≤ (3 * n + (n * Q.totalDegree + 1)) + 2 * n := by gcongr
    _ = 5 * n + 1 + n * Q.totalDegree := by ring

end Work.WilE8.Hyp
