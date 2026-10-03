import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.envelopeDefs
import Submission.Work.ORHughesFree.RankAPI.rk_diagonal_eq_sum
import Submission.Work.ORHughesFree.RankAPI.rk_one_fin
import Submission.Work.ORHughesFree.RankAPI.rk_submatrix
import Submission.Work.ORHughesFree.NaturalExtension.rk_le_card_of_rowSupport
import Submission.Work.ORHughesFree.NaturalExtension.rk_le_card_of_colSupport

/-!
# The rank of the truncations of `t` and of `1 - t t^*`

For `U` a ring with a twist `τ` (`MulSemiringAction (Multiplicative ℤ) U`) and
`t = skewLaurentT ∈ U[t^{±1};τ]`, the `N × N` truncation `toeplitz N t` is the matrix with `1`s on
the superdiagonal, and `star (toeplitz N t)` is its conjugate transpose, i.e. the matrix with `1`s
on the subdiagonal.  Consequently

* `toeplitz N t` is the shift matrix, of rank `N - 1` (it is the identity with its last row
  deleted);
* `1 - toeplitz N t * star (toeplitz N t)` is the matrix with a single `1` in the bottom right
  corner, of rank `1`.

Both statements are proved here for an *arbitrary* Sylvester rank function on `U`, using only the
row-support estimate `rk_le_card_of_rowSupport` and the general submatrix estimate `rk_submatrix`.
-/

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-! ## The three concrete matrices -/

/-- The `N × N` "shift-up" matrix, with `1`s on the superdiagonal. -/
def shiftUpMat (R : Type*) [Zero R] [One R] (N : ℕ) : Matrix (Fin N) (Fin N) R :=
  fun r s => if (s : ℕ) = (r : ℕ) + 1 then 1 else 0

/-- The `N × N` "shift-down" matrix, with `1`s on the subdiagonal; the conjugate transpose of
`shiftUpMat`. -/
def shiftDownMat (R : Type*) [Zero R] [One R] (N : ℕ) : Matrix (Fin N) (Fin N) R :=
  fun r s => if (r : ℕ) = (s : ℕ) + 1 then 1 else 0

/-- The `N × N` matrix with a single `1` in the bottom right corner. -/
def lastOneMat (R : Type*) [Zero R] [One R] (N : ℕ) : Matrix (Fin N) (Fin N) R :=
  fun r s => if (r : ℕ) + 1 = N ∧ (s : ℕ) + 1 = N then 1 else 0

@[simp] theorem shiftUpMat_apply {R : Type*} [Zero R] [One R] (N : ℕ) (r s : Fin N) :
    shiftUpMat R N r s = if (s : ℕ) = (r : ℕ) + 1 then 1 else 0 := rfl

@[simp] theorem shiftDownMat_apply {R : Type*} [Zero R] [One R] (N : ℕ) (r s : Fin N) :
    shiftDownMat R N r s = if (r : ℕ) = (s : ℕ) + 1 then 1 else 0 := rfl

@[simp] theorem lastOneMat_apply {R : Type*} [Zero R] [One R] (N : ℕ) (r s : Fin N) :
    lastOneMat R N r s = if (r : ℕ) + 1 = N ∧ (s : ℕ) + 1 = N then 1 else 0 := rfl

/-- The rows `0, …, N-2` of `Fin N`, as a map out of `Fin (N-1)`. -/
def shiftRowEmb (N : ℕ) : Fin (N - 1) → Fin N := fun i => ⟨(i : ℕ), by omega⟩

/-- The columns `1, …, N-1` of `Fin N`, as a map out of `Fin (N-1)`. -/
def shiftColEmb (N : ℕ) : Fin (N - 1) → Fin N := fun j => ⟨(j : ℕ) + 1, by omega⟩

/-- The bottom right index of `Fin N`, as a map out of `Fin 1`. -/
def lastIdx (N : ℕ) (h : 0 < N) : Fin 1 → Fin N := fun _ => ⟨N - 1, by omega⟩

theorem shiftRowEmb_injective (N : ℕ) : Function.Injective (shiftRowEmb N) := by
  intro a b hab
  exact Fin.ext (by simpa [shiftRowEmb] using congrArg Fin.val hab)

theorem shiftColEmb_injective (N : ℕ) : Function.Injective (shiftColEmb N) := by
  intro a b hab
  have h : (a : ℕ) + 1 = (b : ℕ) + 1 := by simpa [shiftColEmb] using congrArg Fin.val hab
  exact Fin.ext (by omega)

theorem lastIdx_injective (N : ℕ) (h : 0 < N) : Function.Injective (lastIdx N h) :=
  fun a b _ => Subsingleton.elim a b

/-! ## The truncation of `t` and of its conjugate transpose -/

lemma coeffElt_skewLaurentT {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (k : ℤ) :
    coeffElt (skewLaurentT : SkewMonoidAlgebra U (Multiplicative ℤ)) k = if k = 1 then 1 else 0 := by
  have h : coeffElt (skewLaurentT : SkewMonoidAlgebra U (Multiplicative ℤ)) k =
      if (1 : ℤ) = k then 1 else 0 := by
    simp [coeffElt, skewLaurentT, SkewMonoidAlgebra.coeff_single, Finsupp.single_apply,
      Multiplicative.ofAdd.injective.eq_iff]
  rw [h]
  exact if_congr eq_comm rfl rfl

/-- The `(r,s)` entry of the truncation of `t` is `1` exactly on the superdiagonal. -/
theorem toeplitz_skewLaurentT_apply {U : Type} [Ring U]
    [MulSemiringAction (Multiplicative ℤ) U] (N : ℕ) (r s : Fin N) :
    toeplitz N (skewLaurentT : SkewMonoidAlgebra U (Multiplicative ℤ)) r s =
      if (s : ℕ) = (r : ℕ) + 1 then 1 else 0 := by
  have hc := coeffElt_skewLaurentT (U := U) (((s : ℕ) : ℤ) - ((r : ℕ) : ℤ))
  rw [toeplitz, hc, smul_ite, smul_one, smul_zero]
  by_cases h : ((s : ℕ) : ℤ) - ((r : ℕ) : ℤ) = 1
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem toeplitz_skewLaurentT_eq {U : Type} [Ring U]
    [MulSemiringAction (Multiplicative ℤ) U] (N : ℕ) :
    toeplitz N (skewLaurentT : SkewMonoidAlgebra U (Multiplicative ℤ)) = shiftUpMat U N := by
  ext r s
  rw [shiftUpMat_apply, toeplitz_skewLaurentT_apply]

/-- The conjugate transpose of the truncation of `t` is the shift-down matrix. -/
theorem star_toeplitz_skewLaurentT_apply {U : Type} [Ring U] [StarRing U]
    [MulSemiringAction (Multiplicative ℤ) U] (N : ℕ) (r s : Fin N) :
    star (toeplitz N (skewLaurentT : SkewMonoidAlgebra U (Multiplicative ℤ))) r s =
      if (r : ℕ) = (s : ℕ) + 1 then 1 else 0 := by
  rw [Matrix.star_apply, toeplitz_skewLaurentT_apply]
  by_cases h : (r : ℕ) = (s : ℕ) + 1
  · rw [if_pos h]
    simp
  · rw [if_neg h]
    simp

theorem star_toeplitz_skewLaurentT_eq {U : Type} [Ring U] [StarRing U]
    [MulSemiringAction (Multiplicative ℤ) U] (N : ℕ) :
    star (toeplitz N (skewLaurentT : SkewMonoidAlgebra U (Multiplicative ℤ))) =
      shiftDownMat U N := by
  ext r s
  rw [shiftDownMat_apply, star_toeplitz_skewLaurentT_apply]

/-! ## The product of the two shift matrices -/

/-- The product of the shift-up and the shift-down matrix is the identity with its last diagonal
entry deleted. -/
theorem shiftUpMat_mul_shiftDownMat_apply {R : Type*} [Ring R] (N : ℕ) (r s : Fin N) :
    (shiftUpMat R N * shiftDownMat R N) r s =
      if (r : ℕ) + 1 < N ∧ r = s then 1 else 0 := by
  rw [Matrix.mul_apply]
  by_cases hr : (r : ℕ) + 1 < N
  · obtain ⟨u₀, hu₀⟩ : ∃ u : Fin N, (u : ℕ) = (r : ℕ) + 1 := ⟨⟨(r : ℕ) + 1, hr⟩, rfl⟩
    rw [Finset.sum_eq_single u₀]
    · rw [shiftUpMat_apply, if_pos hu₀, one_mul, shiftDownMat_apply]
      have hpq : ((u₀ : ℕ) = (s : ℕ) + 1) ↔ ((r : ℕ) + 1 < N ∧ r = s) := by
        rw [hu₀]
        constructor
        · intro h
          exact ⟨hr, Fin.ext (by omega)⟩
        · rintro ⟨-, rfl⟩
          rfl
      by_cases h : (u₀ : ℕ) = (s : ℕ) + 1
      · rw [if_pos h, if_pos (hpq.mp h)]
      · rw [if_neg h, if_neg (fun hh => h (hpq.mpr hh))]
    · intro u _ hu
      have hune : ¬ ((u : ℕ) = (r : ℕ) + 1) := fun h => hu (Fin.ext (by omega))
      rw [shiftUpMat_apply, if_neg hune, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ u₀) h
  · rw [Finset.sum_eq_zero, if_neg (fun h => hr h.1)]
    intro u _
    have hune : ¬ ((u : ℕ) = (r : ℕ) + 1) := fun h => hr (by have := u.isLt; omega)
    rw [shiftUpMat_apply, if_neg hune, zero_mul]

/-- `1 - shiftUpMat * shiftDownMat` is the matrix with a single `1` in the bottom right corner. -/
theorem one_sub_shiftUpMat_mul_shiftDownMat (R : Type*) [Ring R] (N : ℕ) :
    (1 : Matrix (Fin N) (Fin N) R) - shiftUpMat R N * shiftDownMat R N = lastOneMat R N := by
  ext r s
  rw [Matrix.sub_apply, Matrix.one_apply, shiftUpMat_mul_shiftDownMat_apply, lastOneMat_apply]
  by_cases hrs : r = s
  · subst hrs
    rw [if_pos rfl]
    by_cases hlt : (r : ℕ) + 1 < N
    · rw [if_pos (show (r : ℕ) + 1 < N ∧ r = r from ⟨hlt, rfl⟩), sub_self,
        if_neg (show ¬ ((r : ℕ) + 1 = N ∧ (r : ℕ) + 1 = N) from fun h => by omega)]
    · rw [if_neg (show ¬ ((r : ℕ) + 1 < N ∧ r = r) from fun h => hlt h.1), sub_zero]
      rw [if_pos (show (r : ℕ) + 1 = N ∧ (r : ℕ) + 1 = N from ⟨by omega, by omega⟩)]
  · rw [if_neg hrs, if_neg (show ¬ ((r : ℕ) + 1 < N ∧ r = s) from fun h => hrs h.2), sub_self]
    rw [if_neg (show ¬ ((r : ℕ) + 1 = N ∧ (s : ℕ) + 1 = N) from fun h => hrs (Fin.ext (by omega)))]

/-! ## The ranks of the two matrices -/

/-- The shift-up matrix has rank `N - 1`. -/
theorem rk_shiftUpMat {R : Type*} [Ring R] (rk : SylvesterRank R) {N : ℕ} (hN : 0 < N) :
    rk.rk N N (shiftUpMat R N) = (N : ℝ) - 1 := by
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ N from hN)]
    norm_num
  have hle : rk.rk N N (shiftUpMat R N) ≤ ((N - 1 : ℕ) : ℝ) := by
    refine rk_le_card_of_rowSupport rk (t := N - 1) (shiftRowEmb N) (shiftRowEmb_injective N) _
      ?_
    intro i hi j
    have hge : N - 1 ≤ (i : ℕ) := by
      by_contra hcon
      exact hi ⟨⟨(i : ℕ), by omega⟩, Fin.ext rfl⟩
    rw [shiftUpMat_apply, if_neg (by have := i.isLt; omega)]
  have hge : ((N - 1 : ℕ) : ℝ) ≤ rk.rk N N (shiftUpMat R N) := by
    have hsub : (shiftUpMat R N).submatrix (shiftRowEmb N) (shiftColEmb N) = 1 := by
      ext a b
      rw [Matrix.submatrix_apply, shiftUpMat_apply, Matrix.one_apply]
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl, if_pos (by simp [shiftRowEmb, shiftColEmb])]
      · rw [if_neg hab]
        have hneq : ¬ ((shiftColEmb N b : ℕ) = (shiftRowEmb N a : ℕ) + 1) := by
          intro hh
          have hh' : (b : ℕ) + 1 = (a : ℕ) + 1 := by
            simpa [shiftRowEmb, shiftColEmb] using hh
          exact hab (Fin.ext (by omega))
        rw [if_neg hneq]
    calc ((N - 1 : ℕ) : ℝ)
        = rk.rk (N - 1) (N - 1) (1 : Matrix (Fin (N - 1)) (Fin (N - 1)) R) :=
          (Work.ORHughesFree.RankAPI.rk_one_fin rk (N - 1)).symm
      _ = rk.rk (N - 1) (N - 1)
            ((shiftUpMat R N).submatrix (shiftRowEmb N) (shiftColEmb N)) := by rw [hsub]
      _ ≤ rk.rk N N (shiftUpMat R N) := Work.ORHughesFree.RankAPI.rk_submatrix rk _ _ _
  rw [le_antisymm hle hge, hcast]

/-- The matrix with a single `1` in the bottom right corner has rank `1`. -/
theorem rk_lastOneMat {R : Type*} [Ring R] (rk : SylvesterRank R) {N : ℕ} (hN : 0 < N) :
    rk.rk N N (lastOneMat R N) = 1 := by
  have hle : rk.rk N N (lastOneMat R N) ≤ (1 : ℝ) := by
    have h := rk_le_card_of_rowSupport rk (t := 1) (lastIdx N hN) (lastIdx_injective N hN)
      (lastOneMat R N) (by
        intro i hi j
        have hine : (i : ℕ) ≠ N - 1 := by
          intro hcon
          exact hi ⟨0, Fin.ext (by simp [lastIdx]; omega)⟩
        rw [lastOneMat_apply, if_neg (by have := i.isLt; omega)])
    simpa using h
  have hge : (1 : ℝ) ≤ rk.rk N N (lastOneMat R N) := by
    have hsub : (lastOneMat R N).submatrix (lastIdx N hN) (lastIdx N hN) = 1 := by
      ext a b
      rw [Matrix.submatrix_apply, lastOneMat_apply, Matrix.one_apply]
      have hab : a = b := Subsingleton.elim a b
      rw [if_pos hab]
      have h0a : ((lastIdx N hN) a : ℕ) + 1 = N := by simp [lastIdx]; omega
      have h0b : ((lastIdx N hN) b : ℕ) + 1 = N := by simp [lastIdx]; omega
      rw [if_pos ⟨h0a, h0b⟩]
    calc (1 : ℝ) = ((1 : ℕ) : ℝ) := by norm_num
      _ = rk.rk 1 1 (1 : Matrix (Fin 1) (Fin 1) R) :=
          (Work.ORHughesFree.RankAPI.rk_one_fin rk 1).symm
      _ = rk.rk 1 1 ((lastOneMat R N).submatrix (lastIdx N hN) (lastIdx N hN)) := by rw [hsub]
      _ ≤ rk.rk N N (lastOneMat R N) := Work.ORHughesFree.RankAPI.rk_submatrix rk _ _ _
  exact le_antisymm hle hge

/-- **The ranks of the truncations of `t` and of `1 - t t^*`.**  For every `N > 0` and every
Sylvester rank function `rk` on `U`,

* the truncation `toeplitz N t` of the variable has rank `N - 1`, and
* the projection `1 - toeplitz N t * star (toeplitz N t)` has rank `1`. -/
theorem toeplitzT_rank {U : Type} [Ring U] [StarRing U] [MulSemiringAction (Multiplicative ℤ) U]
    (rk : SylvesterRank U) :
    (∀ N : ℕ, 0 < N → rk.rk N N (toeplitz N (skewLaurentT : SkewMonoidAlgebra U (Multiplicative ℤ))) = (N : ℝ) - 1) ∧
    (∀ N : ℕ, 0 < N → rk.rk N N (1 - toeplitz N (skewLaurentT : SkewMonoidAlgebra U (Multiplicative ℤ)) *
      star (toeplitz N (skewLaurentT : SkewMonoidAlgebra U (Multiplicative ℤ)))) = 1) := by
  refine ⟨fun N hN => ?_, fun N hN => ?_⟩
  · rw [toeplitz_skewLaurentT_eq]
    exact rk_shiftUpMat rk hN
  · rw [star_toeplitz_skewLaurentT_eq, toeplitz_skewLaurentT_eq,
      one_sub_shiftUpMat_mul_shiftDownMat U N]
    exact rk_lastOneMat rk hN

end Work.ORHughesFree.NaturalExtension
