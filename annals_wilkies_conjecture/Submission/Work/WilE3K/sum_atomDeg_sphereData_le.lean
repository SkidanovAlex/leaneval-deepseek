import Mathlib
import Submission.Work.WilE3K.Elim

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE3K
open WilkiesDesign.E

variable {N rt n re : ℕ}

/-- The sphere equation has atom degree at most `3`: it is `∑ k, X k ^ 2 - C c`, a sum of
squares (total degree `≤ 2`) minus a constant (total degree `0`). -/
private lemma spherePoly_atomDeg_le (N re : ℕ) (c : ℝ) :
    atomDeg (ETData.spherePoly (N := N) (re := re) c) ≤ 3 := by
  rw [atomDeg, ETData.spherePoly]
  have h1 : (∑ k : Fin (N + 2), (MvPolynomial.X (Sum.inl k) : EAPoly (N + 2) re) ^ 2).totalDegree ≤ 2 := by
    have h := MvPolynomial.totalDegree_finsetSum (Finset.univ : Finset (Fin (N + 2)))
      (fun k => (MvPolynomial.X (Sum.inl k) : EAPoly (N + 2) re) ^ 2)
    refine le_trans h ?_
    apply Finset.sup_le
    intro k _
    calc ((MvPolynomial.X (Sum.inl k) : EAPoly (N + 2) re) ^ 2).totalDegree
        ≤ 2 * (MvPolynomial.X (Sum.inl k) : EAPoly (N + 2) re).totalDegree := MvPolynomial.totalDegree_pow _ _
      _ = 2 * 1 := by rw [MvPolynomial.totalDegree_X]
      _ = 2 := by norm_num
  have h2 : (MvPolynomial.C c : EAPoly (N + 2) re).totalDegree = 0 := MvPolynomial.totalDegree_C c
  have h3 := MvPolynomial.totalDegree_sub
    (∑ k : Fin (N + 2), (MvPolynomial.X (Sum.inl k) : EAPoly (N + 2) re) ^ 2) (MvPolynomial.C c)
  omega

/-- Embedding a polynomial in one more coordinate (via `rename`) does not raise the atom
degree: `rename` only substitutes variables. -/
private lemma embedP_atomDeg_le (E : ETData N rt n re) (i : Fin n) :
    atomDeg (ETData.embedP (E.G i)) ≤ atomDeg (E.G i) := by
  rw [atomDeg, atomDeg, ETData.embedP]
  have h := MvPolynomial.totalDegree_rename_le (Sum.map (Fin.castAdd 1) id) (E.G i)
  omega

theorem sum_atomDeg_sphereData_le {N rt n re : ℕ} (E : Work.WilE3K.ETData N (rt + 1) n re)
    (c : ℝ) :
    (∑ i, WilkiesDesign.E.atomDeg ((E.sphereData c).G i)) ≤
      (∑ i, WilkiesDesign.E.atomDeg (E.G i)) + 3 := by
  rw [Fin.sum_univ_castSucc]
  have key : ∀ i : Fin n,
      atomDeg ((E.sphereData c).G (Fin.castSucc i)) = atomDeg (ETData.embedP (E.G i)) := by
    intro i
    congr 1
    simp only [ETData.sphereData, Fin.val_castSucc]
    rw [dif_pos i.isLt]
  have keylast : atomDeg ((E.sphereData c).G (Fin.last n)) =
      atomDeg (ETData.spherePoly (N := N) (re := re) c) := by
    congr 1
    simp [ETData.sphereData]
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  rw [keylast]
  have hsum : (∑ i : Fin n, atomDeg (ETData.embedP (E.G i))) ≤ ∑ i : Fin n, atomDeg (E.G i) :=
    Finset.sum_le_sum (fun i _ => embedP_atomDeg_le E i)
  have hsp := spherePoly_atomDeg_le N re c
  omega

end Work.WilE3K
