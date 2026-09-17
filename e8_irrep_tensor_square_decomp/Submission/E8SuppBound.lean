import Submission.E8WCFE
import Submission.WeylWeights
import Submission.WeylBall

/-!
# The support bound for the Weyl translates of the Euler characteristic

`Submission/E8WCFE.lean` proves `euler_support : euler Λ μ ≠ 0 → μ ⪯ Λ` for dominant `Λ` and
`euler_ht : euler Λ μ ≠ 0 → htOf μ ≤ htOf Λ`.  To finish the `W`-invariance of `euler Λ` (the one
remaining input of the Weyl-character-formula route) one has to know that the support of
`euler Λ ∘ sᵢ - euler Λ` is *bounded above in height*.  Since `supp (euler Λ)` is a cone translate
`Λ - ℕΦ⁺`, the only obstruction is an unbounded `αᵢ`-coordinate: the **string bound**

  `μ ∈ supp (euler Λ) → -C ≤ μ i`

(equivalently `htOf (sᵢ ν) ≤ htOf Λ + C` for `ν` in the reflected support).

This file proves the *reduction*: the string bound gives the height bound, hence the boundedness
of the support of `euler Λ ∘ sᵢ` and of the difference `euler Λ ∘ sᵢ - euler Λ`.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

noncomputable section
open scoped BigOperators

namespace Submission.E8SuppBound

open Submission.WCFSetup
open Submission.E8Character
open Submission.E8WCFC
open Commons.LinearAlgebra.Matrix.Cartan

/-- The effect of a simple reflection on the height: `htOf (sᵢ v) = htOf v - v i`. -/
theorem htOf_sref (i : Fin 8) (v : Fin 8 → ℤ) : htOf (sref i v) = htOf v - v i := by
  have h : sref i v = v - v i • (fun j : Fin 8 => E8 i j) := by
    funext j
    rw [sref_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [h, htOf_sub, htOf_smul_int]
  have h1 : htOf (fun j : Fin 8 => E8 i j) = 1 := by fin_cases i <;> decide
  rw [h1]; ring

/-- The `αᵢ`-coordinate of `sᵢ v` is the negative of that of `v`. -/
theorem sref_apply_self' (i : Fin 8) (v : Fin 8 → ℤ) : sref i v i = -v i :=
  Submission.WeylWeights.sref_apply_self i v

/-- The single reflection as a word. -/
theorem wact_single (i : Fin 8) (v : Fin 8 → ℤ) : wact [i] v = sref i v := rfl

/-- The reflected support in terms of `ap` (the matrix action). -/
theorem ap_single_eq_sref (i : Fin 8) (v : Fin 8 → ℤ) : ap (wactMat [i]) v = sref i v := by
  rw [wactMat_ap, wact_single]

/-- **The reduction.**  If the string bound `-C ≤ μ i` holds at every non-zero point of the
support of `euler Λ`, then the support of the translated function `euler Λ ∘ sᵢ` is bounded above
by `htOf Λ + C`. -/
theorem supp_smul_s_i_bounded {Λ : Fin 8 → ℤ} (hΛ : ∀ j, 0 ≤ Λ j) (i : Fin 8) (C : ℤ)
    (hstr : ∀ μ : Fin 8 → ℤ, euler Λ μ ≠ 0 → -C ≤ μ i) :
    ∀ ν : Fin 8 → ℤ, euler Λ (ap (wactMat [i]) ν) ≠ 0 → htOf ν ≤ htOf Λ + C := by
  intro ν hν
  rw [ap_single_eq_sref] at hν
  have h1 := euler_ht (Λ := Λ) hΛ (sref i ν) hν
  have h2 := hstr (sref i ν) hν
  rw [sref_apply_self'] at h2
  rw [htOf_sref] at h1
  linarith

/-- Hence the difference `euler Λ ∘ sᵢ - euler Λ` is supported on the same bounded set. -/
theorem supp_sub_bounded {Λ : Fin 8 → ℤ} (hΛ : ∀ j, 0 ≤ Λ j) (i : Fin 8) (C : ℤ)
    (hstr : ∀ μ : Fin 8 → ℤ, euler Λ μ ≠ 0 → -C ≤ μ i) :
    ∀ ν : Fin 8 → ℤ,
      (fun v => euler Λ (ap (wactMat [i]) v) - euler Λ v) ν ≠ 0 →
      htOf ν ≤ max (htOf Λ + C) (htOf Λ) := by
  intro ν hν
  have h := supp_smul_s_i_bounded hΛ i C hstr ν
  by_cases hz : euler Λ (ap (wactMat [i]) ν) = 0
  · -- then the second summand is non-zero
    have h2 : euler Λ ν ≠ 0 := by
      intro h0
      refine hν ?_
      show euler Λ (ap (wactMat [i]) ν) - euler Λ ν = 0
      rw [hz, h0, sub_zero]
    exact le_trans (euler_ht (Λ := Λ) hΛ ν h2) (le_max_right _ _)
  · exact le_trans (h hz) (le_max_left _ _)

end Submission.E8SuppBound
