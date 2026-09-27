import Mathlib
import Submission.Work.EKLContract.Lemmas.isHoro_Uij
import Submission.Work.EKLContract.Lemmas.isHoro_Upar
import Submission.Work.EKLContract.Interfaces

/-!
# The cross commutator relation for the root subgroups `U_ij`

For `p, q, r : Fin 3` pairwise distinct and reals `a, s`,

  `u_qr(a) · u_pq(s) · u_qr(a)⁻¹ = u_pq(s) · u_pr(-(a s))`.

This is the commutator relation `[E_qr, E_pq] = E_pr` of `sl₃`, in the form used when a leafwise
measure is transported along a conjugation: conjugating the root `u_pq(s)` by `u_qr(a)` keeps the
`U_pq`-factor and creates the `U_pr`-factor `u_pr(-(a s))`.

Everything reduces to `Matrix.single` bookkeeping: writing `E_ij = Matrix.single i j 1` one has
`E_qr E_pq = 0` (as `p ≠ r`), `E_pq E_qr = E_pr`, `E_qr E_qr = 0` (as `q ≠ r`) and
`E_pq E_pr = 0` (as `q ≠ r`), so both sides are the matrix `1 + s E_pq - a s E_pr`, i.e. the shape
matrix `shapeMat p r q s 0 (-(a s))` of `U_(pr)`.  The multiplication law `shapeMat_mul` for these
shape matrices (proved in `EKLContract.Lemmas.isHoro_Upar`) packages exactly this bookkeeping, so
the proof is: rewrite both sides through `toMat` into shape matrices and multiply.
-/

open Work.EKLContract Work.EKLContract.Lemmas

namespace Work.EKLC6Core

/-- `u_qr(a) · u_pq(s) · u_qr(a)⁻¹ = u_pq(s) · u_pr(-(a s))` for `p, q, r` pairwise distinct. -/
theorem uij_conj_uij_cross {p q r : Fin 3} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    (a s : ℝ) :
    Work.EKLContract.uij hqr a * Work.EKLContract.uij hpq s * (Work.EKLContract.uij hqr a)⁻¹
      = Work.EKLContract.uij hpq s * Work.EKLContract.uij hpr (-(a * s)) := by
  have hinv : (uij hqr a : SL3)⁻¹ = uij hqr (-a) := by
    rw [uij, uij, Matrix.SpecialLinearGroup.transvection_inv]
  apply ext_toMat
  rw [toMat_mul, toMat_mul, hinv, horoUij_toMat, horoUij_toMat, horoUij_toMat, toMat_mul,
    horoUij_toMat, horoUij_toMat]
  -- both sides are now products of `1 + single · ·` matrices; identify them as shape matrices
  have h1 : (1 + Matrix.single q r a : Matrix (Fin 3) (Fin 3) ℝ) = shapeMat p r q 0 a 0 := by
    simp [shapeMat]
  have h2 : (1 + Matrix.single p q s : Matrix (Fin 3) (Fin 3) ℝ) = shapeMat p r q s 0 0 := by
    simp [shapeMat]
  have h3 : (1 + Matrix.single q r (-a) : Matrix (Fin 3) (Fin 3) ℝ) = shapeMat p r q 0 (-a) 0 := by
    simp [shapeMat]
  have h4 : (1 + Matrix.single p r (-(a * s)) : Matrix (Fin 3) (Fin 3) ℝ)
      = shapeMat p r q 0 0 (-(a * s)) := by
    simp [shapeMat]
  rw [h1, h2, h3, h4]
  -- `u_qr(a) u_pq(s) u_qr(a)⁻¹ = shapeMat p r q s 0 (-(a s))`
  have hL : (shapeMat p r q 0 a 0 * shapeMat p r q s 0 0) * shapeMat p r q 0 (-a) 0
      = shapeMat p r q s 0 (-(a * s)) := by
    rw [shapeMat_mul hpr hpq hqr]
    rw [shapeMat_mul hpr hpq hqr]
    congr 1 <;> first | rfl | ring
  -- `u_pq(s) u_pr(-(a s)) = shapeMat p r q s 0 (-(a s))`
  have hR : shapeMat p r q s 0 0 * shapeMat p r q 0 0 (-(a * s))
      = shapeMat p r q s 0 (-(a * s)) := by
    rw [shapeMat_mul hpr hpq hqr]
    congr 1 <;> first | rfl | ring
  rw [hL, hR]

end Work.EKLC6Core
