/-
  annals_wilkies_conjecture, AREA E3K (`Submission.Work.WilE3K`).

  `Work.WilE3K.sphereData_jac_lastCol`: in the *sphere step* `E.sphereData c` (one new free
  coordinate `z_{N+1}` and the sphere equation `∑_k z_k² = c` added, `Elim.lean` §4), the last
  column of the symbolic Jacobian vanishes on every row except the new sphere equation itself.

  The mathematical content is simply that the new coordinate occurs **only** in the new equation:

  * on a `tan` row the entry is `- lam j (freeIndex (last))`, and the arctan coefficients of the
    sphere data are `0` on the last free coordinate (`sphereData_lastCol_dTanFun`);
  * on an old exp-affine row the entry is `evalPoly (dPoly last (G i'))`, and `G i'` is (the image
    under `embedP` of) an old polynomial, which does not involve the new coordinate: the symbolic
    derivative `dPoly last` of `embedP P` is `pderiv (inl last) (embedP P)` (the chain part dies
    because `dcoef last j = 0`) plus the chain sum, which vanishes too
    (`sphereData_lastCol_dPoly_embedP`).

  Together with `sphereData_jac_last_last` (`= 2 z_{N+1}`) this shows that the Jacobian of the
  sphere step is block lower triangular and that `det (jac) = 2 z_{N+1} · det (old jac)`.
-/
import Mathlib
import Submission.Work.WilE3K.Elim

namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## §1. `embedP` does not involve the new coordinate -/

/-- The embedding `embedP` of `A[Fin (N+1) ⊕ Fin re]` into `A[Fin (N+2) ⊕ Fin re]` only uses the
first `N + 1` coordinates, so the partial derivative in the new (last) coordinate vanishes. -/
lemma sphereData_lastCol_pderiv_embedP {N re : ℕ} (P : EAPoly (N + 1) re) :
    MvPolynomial.pderiv (Sum.inl (Fin.last (N + 1))) (ETData.embedP (N := N) (re := re) P) = 0 := by
  rw [ETData.embedP]
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hmem
  obtain ⟨i, _, hi⟩ := MvPolynomial.mem_vars_rename (Sum.map (Fin.castAdd 1) id) P hmem
  cases i with
  | inl k =>
      rw [Sum.map_inl] at hi
      have h : Fin.castAdd 1 k = Fin.last (N + 1) := Sum.inl.inj hi
      have h2 : (k : ℕ) = N + 1 := by have := congrArg Fin.val h; simpa using this
      omega
  | inr j =>
      rw [Sum.map_inr] at hi
      exact Sum.inr_ne_inl hi

/-! ## §2. The last column of the sphere data -/

/-- The new coordinate is the last free coordinate of the sphere step: its free index has value
`n`. -/
lemma sphereData_lastCol_freeIndex_val {N rt n re : ℕ} (E : ETData N (rt + 1) n re) (c : ℝ)
    (hk : rt + 1 ≤ ((Fin.last (N + 1) : Fin ((N + 1) + 1)) : ℕ)) :
    (((E.sphereData c).freeIndex (Fin.last (N + 1)) hk : Fin (n + 1)) : ℕ) = n := by
  simp only [ETData.freeIndex]
  have h := E.h
  simp only [Fin.val_last]
  omega

/-- The chain-derivative coefficient of the new coordinate is `0` (the chain functions of the
sphere data do not involve the new coordinate). -/
lemma sphereData_lastCol_dcoef {N rt n re : ℕ} (E : ETData N (rt + 1) n re) (c : ℝ) (j : Fin re) :
    (E.sphereData c).dcoef (Fin.last (N + 1)) j = 0 := by
  have hle : (rt + 1) ≤ ((Fin.last (N + 1) : Fin ((N + 1) + 1)) : ℕ) := by
    simp only [Fin.val_last]; have h := E.h; omega
  rw [ETData.dcoef, dif_pos hle]
  rw [show (E.sphereData c).ca j ((E.sphereData c).freeIndex (Fin.last (N + 1)) hle)
      = (if h : (((E.sphereData c).freeIndex (Fin.last (N + 1)) hle : Fin (n + 1)) : ℕ) < n
          then E.ca j ⟨_, h⟩ else 0) from rfl]
  rw [dif_neg (by rw [sphereData_lastCol_freeIndex_val E c hle]; omega)]

/-- The gradient of an `arctan` equation of the sphere data vanishes in the new coordinate: the
last coordinate is free and the arctan coefficients of the sphere data are `0` there. -/
lemma sphereData_lastCol_dTanFun {N rt n re : ℕ} (E : ETData N (rt + 1) n re) (c : ℝ)
    (j : Fin (rt + 1)) (z : Fin ((N + 1) + 1) → ℝ) :
    (E.sphereData c).dTanFun j z (Fin.last (N + 1)) = 0 := by
  have hle : (rt + 1) ≤ ((Fin.last (N + 1) : Fin ((N + 1) + 1)) : ℕ) := by
    simp only [Fin.val_last]; have h := E.h; omega
  rw [ETData.dTanFun]
  rw [dif_neg (show ¬ ((Fin.last (N + 1) : Fin ((N + 1) + 1)) : ℕ) < rt + 1 by
    simp only [Fin.val_last]; have h := E.h; omega)]
  rw [show (E.sphereData c).lam j ((E.sphereData c).freeIndex (Fin.last (N + 1)) _)
      = (if h : (((E.sphereData c).freeIndex (Fin.last (N + 1)) _ : Fin (n + 1)) : ℕ) < n
          then E.lam j ⟨_, h⟩ else 0) from rfl]
  rw [dif_neg (by rw [sphereData_lastCol_freeIndex_val E c hle]; omega)]
  ring

/-- Away from the new (sphere) equation, the equations of the sphere data are the images under
`embedP` of the equations of `E`. -/
lemma sphereData_lastCol_G {N rt n re : ℕ} (E : ETData N (rt + 1) n re) (c : ℝ)
    (i' : Fin (n + 1)) (hh : ((i' : Fin (n + 1)) : ℕ) < n) :
    (E.sphereData c).G i' = ETData.embedP (N := N) (re := re) (E.G ⟨(i' : ℕ), hh⟩) := by
  rw [show (E.sphereData c).G i' = dite (((i' : Fin (n + 1)) : ℕ) < n)
      (fun h => ETData.embedP (N := N) (re := re) (E.G ⟨(i' : ℕ), h⟩))
      (fun _ => ETData.spherePoly c) from rfl]
  rw [dif_pos hh]

/-- The symbolic derivative of an old equation of the sphere data in the new coordinate is `0`. -/
lemma sphereData_lastCol_dPoly_embedP {N rt n re : ℕ} (E : ETData N (rt + 1) n re) (c : ℝ)
    (P : EAPoly (N + 1) re) :
    (E.sphereData c).dPoly (Fin.last (N + 1)) (ETData.embedP (N := N) (re := re) P) = 0 := by
  rw [ETData.dPoly, sphereData_lastCol_pderiv_embedP]
  simp only [sphereData_lastCol_dcoef, MvPolynomial.C_0, zero_mul, Finset.sum_const_zero, zero_add]

/-! ## §3. The last column of the Jacobian of the sphere step -/

theorem sphereData_jac_lastCol {N rt n re : ℕ} (E : Work.WilE3K.ETData N (rt + 1) n re)
    (c : ℝ) (z : Fin ((N + 1) + 1) → ℝ) (i : Fin (N + 1)) :
    ((E.sphereData c).jac z) (Fin.castSucc i) (Fin.last (N + 1)) = 0 := by
  simp only [ETData.jac, Matrix.of_apply]
  by_cases hi : ((Fin.castSucc i : Fin ((N + 1) + 1)) : ℕ) < rt + 1
  · -- the row is an `arctan` row
    rw [dif_pos hi]
    exact sphereData_lastCol_dTanFun E c _ z
  · -- the row is one of the old exp-affine equations
    rw [dif_neg hi]
    set i' := (E.sphereData c).freeIndex (Fin.castSucc i) (not_lt.mp hi) with hi'def
    have hlt : ((i' : Fin (n + 1)) : ℕ) < n := by
      have hi' : rt + 1 ≤ (i : ℕ) := not_lt.mp hi
      have h1 : ((i' : Fin (n + 1)) : ℕ) = (i : ℕ) - (rt + 1) := by
        rw [hi'def, ETData.freeIndex]; rfl
      have h := E.h
      have hi2 : (i : ℕ) ≤ N := by have := i.isLt; omega
      rw [h1]
      omega
    rw [sphereData_lastCol_G E c i' hlt, sphereData_lastCol_dPoly_embedP]
    simp [ETData.evalPoly]

end Work.WilE3K
