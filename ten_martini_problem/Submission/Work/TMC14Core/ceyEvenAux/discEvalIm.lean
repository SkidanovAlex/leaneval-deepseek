import Mathlib
import Submission.Work.TMC14Core.Rat
import Submission.Work.TMC14Core.ceyDerivBound
import Submission.Work.TMC14Core.Chambers

/-!
# TMC14Core / `ceyEvenAux`: `disc` is real on the real axis

`disc p q lam` is the characteristic polynomial of the Bloch matrix
`blochMat p q lam (1/(4q)) 0` (shifted by the constant `2`).  At `k = 0` the two Bloch
corner entries are `e^{±0} = 1`, so *every* entry of this particular Bloch matrix is a
real number: `blochMat p q lam (1/(4q)) 0` is the entrywise image under `ℝ → ℂ` of an
explicitly real matrix `blochMatReal p q lam`.

Consequently the characteristic polynomial is the image of a real polynomial, and its
value at a real energy `a` is a real number — which is exactly the statement that its
imaginary part vanishes.
-/

namespace Work.TMC14Core.ceyEvenAux

open Polynomial

noncomputable section

/-- The real matrix whose entrywise image under `ℂ ← ℝ` is the Bloch matrix
`blochMat p q lam θ 0`: the diagonal and the off-diagonal `1`'s as in `blochMat`, and the
two Bloch corner entries, which at quasi-momentum `k = 0` equal `e^{0} = 1`. -/
def blochMatReal (p : ℤ) (q : ℕ) (lam θ : ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  fun i j =>
    (if i = j then 2 * lam * Real.cos (2 * Real.pi * (θ + (i : ℝ) * (p : ℝ) / (q : ℝ))) else 0)
    + (if (i : ℕ) + 1 = (j : ℕ) then 1 else 0)
    + (if (j : ℕ) + 1 = (i : ℕ) then 1 else 0)
    + (if (i : ℕ) = q - 1 ∧ (j : ℕ) = 0 then 1 else 0)
    + (if (i : ℕ) = 0 ∧ (j : ℕ) = q - 1 then 1 else 0)

/-- At quasi-momentum `k = 0` the Bloch matrix is the entrywise image of the real matrix
`blochMatReal`.  The two corner entries `e^{±0}` both collapse to `1`. -/
theorem blochMat_zero_eq_map_ofReal (p : ℤ) (q : ℕ) (lam θ : ℝ) :
    blochMat p q lam θ 0 = (blochMatReal p q lam θ).map Complex.ofRealHom := by
  ext i j
  show (blochMat p q lam θ 0) i j = ((blochMatReal p q lam θ i j : ℝ) : ℂ)
  simp only [blochMat, blochMatReal]
  split_ifs <;> simp [Complex.exp_zero]

/-- A polynomial obtained from a real polynomial by extending scalars from `ℝ` to `ℂ`
takes real values on real arguments: the imaginary part of its value at any `a : ℝ`
vanishes.  (Here it is applied to `charpoly`, which is the scalar extension of the
characteristic polynomial of a real matrix.) -/
theorem charpoly_map_ofReal_eval_im_zero {n : Type*} [Fintype n] [DecidableEq n]
    (R : Matrix n n ℝ) (a : ℝ) :
    (((R.map Complex.ofRealHom).charpoly).eval (a : ℂ)).im = 0 := by
  rw [Matrix.charpoly_map, Polynomial.eval_map]
  have ha : ((a : ℂ)) = Complex.ofRealHom a := rfl
  rw [ha, Polynomial.eval₂_at_apply]
  simp

/-- `disc p q lam` is real on the real axis. -/
theorem discEvalIm (p : ℤ) (q : ℕ) (lam a : ℝ) :
    ((disc p q lam).eval ((a : ℝ) : ℂ)).im = 0 := by
  have h := charpoly_map_ofReal_eval_im_zero (blochMatReal p q lam (1 / (4 * (q : ℝ)))) a
  rw [← blochMat_zero_eq_map_ofReal p q lam (1 / (4 * (q : ℝ)))] at h
  have hd : disc p q lam
      = (blochMat p q lam (1 / (4 * (q : ℝ))) 0).charpoly + Polynomial.C 2 := rfl
  rw [hd, Polynomial.eval_add, Polynomial.eval_C, Complex.add_im, h]
  simp

end

end Work.TMC14Core.ceyEvenAux
