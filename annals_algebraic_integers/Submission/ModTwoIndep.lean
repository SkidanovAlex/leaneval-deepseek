import Mathlib
import Submission.MinkBox

/-!
# ℚ-independence of a family whose mod-2 reductions are the monomials `X^j`

Used by `Submission.SecondSqueeze` (`lem:second_squeeze`, Smith GON.tex):
the integer polynomials `H_j` (`j < m`) produced by the adjust theorem satisfy
`H_j ≡ X^j (mod 2)` coefficient-wise (they equal `X^j − 2·R_j`), and we need
them to be ℚ-linearly independent (hence a basis of the degree-≤(m−1) space).

## Claim
If `H : Fin m → Polynomial ℤ` has `natDegree (H j) ≤ m−1` and
`(H j).map (Int.castRingHom (ZMod 2)) = X^(j:ℕ)` for every `j`, then the
length-`m+1` coefficient vectors `coeffVec (m+1) (H j)` are ℚ-independent.

## Proof route (any correct route accepted)
1. (Recommended) Let `M : Matrix (Fin m) (Fin m) ℤ` with `M i j := (H j).coeff i.val`.
   The mod-2 hypothesis gives `M mod 2 = I` (each `(H j).coeff i.val` is even
   when `i ≠ j` and odd when `i = j`), so `det M` is odd, in particular
   `det M ≠ 0` as an integer (reduce `det` mod 2: `(M.map (Int.castRingHom (ZMod 2))).det = 1`).
   Hence the ℚ-matrix of the columns is invertible and the column vectors
   `(fun j : Fin m => coeffVec m (H j))` are ℚ-independent; then embed into
   length `m+1` (append a trailing zero) to obtain the stated claim.
   (The trailing coordinate is 0 because `natDegree (H j) ≤ m−1`.)
2. Alternatively a 2-adic argument: a ℚ-relation, cleared of denominators,
   gives integers `z_j` with `∑ z_j • (H j) = 0` in `ℤ[X]`; divide by the
   largest power of 2 dividing all `z_j`, reduce mod 2 to contradict the
   independence of the monomials `X^j` over `ZMod 2`.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace Submission.ModTwoIndep

open Submission.MinkBox

/-- ℚ-independence of length-`m` coefficient vectors (degrees `0..m−1`). -/
theorem linIndep_coeffVec {m : ℕ}
    (H : Fin m → Polynomial ℤ)
    (hdeg : ∀ j : Fin m, (H j).natDegree ≤ m - 1)
    (hmod2 : ∀ j : Fin m, (H j).map (Int.castRingHom (ZMod 2)) = Polynomial.X ^ (j : ℕ)) :
    LinearIndependent ℚ (fun j : Fin m => coeffVec m (H j)) := by
  let Mz : Matrix (Fin m) (Fin m) ℤ := fun i j => (H j).coeff i.val
  -- The coefficient matrix reduces to the identity mod 2 (each `H j ≡ X^j`
  -- coefficient-wise), so its integer determinant is odd, hence nonzero.
  have hM : Mz.map (Int.castRingHom (ZMod 2)) =
      (1 : Matrix (Fin m) (Fin m) (ZMod 2)) := by
    ext i j
    dsimp [Mz]
    change (Int.castRingHom (ZMod 2)) ((H j).coeff i.val) =
      (1 : Matrix (Fin m) (Fin m) (ZMod 2)) i j
    rw [← Polynomial.coeff_map]
    rw [hmod2 j, Polynomial.coeff_X_pow]
    rw [Matrix.one_apply]
    by_cases hij : i = j
    · simp [hij]
    · have hval : i.val ≠ (j : ℕ) := by
        intro hv
        exact hij (Fin.ext hv)
      rw [if_neg hval, if_neg hij]
  have hdet2 : ((Int.castRingHom (ZMod 2)).mapMatrix Mz).det = 1 := by
    have hM' : (Int.castRingHom (ZMod 2)).mapMatrix Mz = Mz.map (Int.castRingHom (ZMod 2)) := by
      ext i j
      rfl
    rw [hM', hM]
    simp
  have hcast : ((Mz.det : ZMod 2)) = 1 := by
    change (Int.castRingHom (ZMod 2)) Mz.det = 1
    rw [RingHom.map_det]
    exact hdet2
  have hzdet : Mz.det ≠ 0 := by
    intro hz
    rw [hz] at hcast
    norm_num at hcast
  -- The same matrix over ℚ has the same nonzero determinant.
  let M : Matrix (Fin m) (Fin m) ℚ := fun i j => ((H j).coeff i.val : ℚ)
  have hMeq : M = Mz.map (fun z : ℤ => (z : ℚ)) := by
    ext i j
    dsimp [M, Mz]
    change ((H j).coeff i.val : ℚ) = (fun z : ℤ => (z : ℚ)) ((H j).coeff i.val)
    rfl
  have hdet_cast : (Mz.det : ℚ) = M.det := by
    rw [hMeq]
    exact Int.cast_det Mz
  have hMdet : M.det ≠ 0 := by
    intro h0
    have hz0 : (Mz.det : ℚ) = 0 := by
      rw [hdet_cast, h0]
    exact hzdet (by exact_mod_cast hz0)
  -- A square matrix over a field with nonzero determinant has independent columns.
  have hns : M.Nonsingular := (Matrix.nonsingular_iff_det_ne_zero).mpr hMdet
  have hindcol : LinearIndependent ℚ M.col := Matrix.Nonsingular.linearIndependent_col hns
  have hcol : M.col = fun j : Fin m => coeffVec m (H j) := by
    ext j i
    change M i j = ((H j).coeff i.val : ℚ)
    dsimp [M]
  exact hcol ▸ hindcol

/-- ℚ-independence of length-`m+1` coefficient vectors (degrees `0..m`). -/
theorem linIndep_coeffVec_succ {m : ℕ}
    (H : Fin m → Polynomial ℤ)
    (hdeg : ∀ j : Fin m, (H j).natDegree ≤ m - 1)
    (hmod2 : ∀ j : Fin m, (H j).map (Int.castRingHom (ZMod 2)) = Polynomial.X ^ (j : ℕ)) :
    LinearIndependent ℚ (fun j : Fin m => coeffVec (m + 1) (H j)) := by
  -- Restrict a putative ℚ-relation to the first `m` coordinates: the first
  -- `m` coordinates of `coeffVec (m+1) (H j)` are exactly `coeffVec m (H j)`.
  have hind_m := linIndep_coeffVec H hdeg hmod2
  rw [linearIndependent_iff]
  intro l hl
  have hsmall : Finsupp.linearCombination ℚ (fun j : Fin m => coeffVec m (H j)) l = 0 := by
    funext i
    have h := congrFun hl (Fin.castSucc i)
    rw [Finsupp.linearCombination_apply] at h ⊢
    rw [Finsupp.sum_apply'] at h ⊢
    simpa [Pi.smul_apply, coeffVec] using h
  rw [linearIndependent_iff] at hind_m
  exact hind_m l hsmall

end Submission.ModTwoIndep
