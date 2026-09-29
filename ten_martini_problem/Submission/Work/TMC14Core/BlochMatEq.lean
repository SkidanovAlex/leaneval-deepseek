import Mathlib
import Submission.Work.TMC14Core.Weyl
import Submission.Work.TMC14Core.BlochAux

/-!
# TMC14Core: the Bloch matrix as a Weyl operator

The Bloch matrix `blochMat p q lam θ k` of the periodic problem with frequency
`p/q` is defined entrywise (`TMC14Core.Rat`): its diagonal is
`2 λ cos 2π(θ + i p/q)`, it has `1`'s on the two off-diagonals, and its two corner
entries `e^{±2πik}` implement the Bloch boundary condition.

`TMC14Core.BlochAux` splits that entrywise definition into the five elementary
matrices `bDiag + bSup + bSub + bTL + bBR`.  Here we identify the three pieces with
the Weyl clock-and-shift letters `U = wU q k` and `V = wV p q θ`:

* `bSup + bTL = U`,
* `bSub + bBR = U† = star U`,
* `bDiag = λ • (V + V†) = λ • (wV p q θ + star (wV p q θ))`,

so that `blochMat p q lam θ k = U + U† + λ(V + V†)`.

The two off-diagonal pieces `bSup`, `bSub` carry the interior `1`'s of the cyclic
shift while the corner pieces `bTL`, `bBR` carry its wrap-around entries `e^{±2πik}`
(the `q = 1` and `q = 2` cases, where the two corners interact, are handled by the
case analysis below).
-/

open Matrix

noncomputable section

namespace Work.TMC14Core

/-- `blochMat` regrouped as `(bSup + bTL) + (bSub + bBR) + bDiag`. -/
theorem blochMat_eq_cornerSum (p : ℤ) (q : ℕ) (lam θ k : ℝ) :
    blochMat p q lam θ k = (bSup q + bTL q k) + (bSub q + bBR q k) + bDiag p q lam θ := by
  rw [blochMat_decomp]
  abel

/-- The cyclic shift `wU q k` is the superdiagonal together with the top-right corner. -/
theorem wU_eq_bSup_add_bTL (q : ℕ) (k : ℝ) : wU q k = bSup q + bTL q k := by
  ext i j
  simp only [wU_apply, wShiftBeta, wPh, bSup, bTL, Matrix.add_apply]
  rcases q with _ | q'
  · exact Fin.elim0 i
  · have hi := i.isLt
    by_cases h : i.val + 1 < q' + 1
    · rw [Nat.mod_eq_of_lt h]
      have hfar : ¬ (i.val = (q' + 1) - 1 ∧ j.val = 0) := by omega
      by_cases h2 : i.val + 1 = j.val
      · simp only [if_pos h2, if_pos h, if_neg hfar, add_zero]
      · simp only [if_neg h2, if_neg hfar, zero_add]
    · have hmod : (i.val + 1) % (q' + 1) = 0 := by
        have hh : i.val + 1 = q' + 1 := by omega
        rw [hh, Nat.mod_self]
      have hi' : i.val = (q' + 1) - 1 := by omega
      have hjr : ¬ (i.val + 1 = j.val) := by omega
      rw [hmod, if_neg h, if_neg hjr, hi', zero_add]
      rw [if_congr (show ((0 : ℕ) = j.val) ↔ (j.val = 0) from eq_comm) rfl rfl]
      simp only [true_and]

/-- The adjoint `U†` of the cyclic shift is the subdiagonal together with the
bottom-left corner. -/
theorem star_wU_eq_bSub_add_bBR (q : ℕ) (k : ℝ) : star (wU q k) = bSub q + bBR q k := by
  ext i j
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, wU_apply]
  simp only [apply_ite star, star_one, star_zero, star_wShiftBeta, bSub, bBR, Matrix.add_apply]
  rcases q with _ | q'
  · exact Fin.elim0 i
  · have hj := j.isLt
    by_cases h : j.val + 1 < q' + 1
    · rw [Nat.mod_eq_of_lt h]
      have hfar : ¬ (i.val = 0 ∧ j.val = (q' + 1) - 1) := by omega
      by_cases h2 : j.val + 1 = i.val
      · simp only [if_pos h2, if_pos h, if_neg hfar, add_zero]
      · simp only [if_neg h2, if_neg hfar, zero_add]
    · have hmod : (j.val + 1) % (q' + 1) = 0 := by
        have hh : j.val + 1 = q' + 1 := by omega
        rw [hh, Nat.mod_self]
      have hj' : j.val = (q' + 1) - 1 := by omega
      have hir : ¬ (j.val + 1 = i.val) := by omega
      rw [hmod, if_neg h, if_neg hir, hj', zero_add]
      rw [if_congr (show ((0 : ℕ) = i.val) ↔ (i.val = 0) from eq_comm) rfl rfl]
      simp only [and_true]

/-- `λ • (V + V†)` is the diagonal `2λ cos 2π(θ + i p/q)`. -/
theorem smul_wV_add_star_eq_bDiag (p : ℤ) (q : ℕ) (lam θ : ℝ) :
    (lam : ℂ) • (wV p q θ + star (wV p q θ)) = bDiag p q lam θ := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, wV_apply, wV_apply, bDiag]
  simp only [apply_ite star, star_zero]
  by_cases hij : i = j
  · subst hij
    simp only [if_true]
    rw [wVd_add_conj]
    push_cast
    ring
  · have hji : ¬ (j = i) := fun h => hij h.symm
    simp only [if_neg hij, if_neg hji, add_zero, mul_zero]

/-- The Bloch matrix of the periodic problem is the Weyl operator
`U + U† + λ(V + V†)`. -/
theorem BlochMatEq (p : ℤ) (q : ℕ) (lam θ k : ℝ) :
    blochMat p q lam θ k = wU q k + star (wU q k) + (lam : ℂ) • (wV p q θ + star (wV p q θ)) := by
  rw [blochMat_eq_cornerSum, ← wU_eq_bSup_add_bTL, ← star_wU_eq_bSub_add_bBR,
    ← smul_wV_add_star_eq_bDiag]

end Work.TMC14Core
