import Mathlib
import Submission.Work.KT.Psi.ClsM

/-!
# `Work.KT.Psi.subIncl` — the inclusion matrix of a subtype

For `pr : ι → Prop` with `ι` a finite type, `subIncl A pr : Matrix ι {i // pr i} A` is the
rectangular matrix with entries `if (j : ι) = i then 1 else 0`.  It is the partial isometry that
exhibits the inclusion of the subtype `{i // pr i}` into `ι`: its columns are the standard basis
vectors indexed by the subtype, so `((subIncl A pr)ᵀ * N) * subIncl A pr` picks out the
`({i // pr i} × {i // pr i})`-minor of `N`.

The file collects the definition together with the elementary "apply" identities that turn
products with `subIncl` into sums over the subtype.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

variable {A : Type} [Ring A]

/-- The inclusion matrix `ι ← {i // pr i}`: its `(i, j)` entry is `1` if `(j : ι) = i` and `0`
otherwise. -/
def subIncl (A : Type) [Zero A] [One A] {ι : Type} [DecidableEq ι] (pr : ι → Prop) :
    Matrix ι {i // pr i} A :=
  fun i j => if (j : ι) = i then 1 else 0

@[simp] theorem subIncl_apply {ι : Type} [DecidableEq ι] (pr : ι → Prop) (i : ι)
    (j : {i // pr i}) : subIncl A pr i j = if (j : ι) = i then (1 : A) else 0 := rfl

@[simp] theorem subIncl_transpose_apply {ι : Type} [DecidableEq ι] (pr : ι → Prop)
    (j : {i // pr i}) (i : ι) :
    (subIncl A pr)ᵀ j i = if (j : ι) = i then (1 : A) else 0 := rfl

/-- `(N * subIncl A pr) i j` is the `i`-th entry of the `j`-th column of `N`. -/
theorem mul_subIncl_apply {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → Prop)
    (N : Matrix ι ι A) (i : ι) (j : {i // pr i}) : (N * subIncl A pr) i j = N i (j : ι) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (j : ι)
    (fun l _ hl => by rw [subIncl_apply, if_neg (fun h => hl h.symm), mul_zero])
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [subIncl_apply, if_pos rfl, mul_one]

/-- `((subIncl A pr)ᵀ * N) j i` is the `i`-th entry of the `j`-th row of `N`. -/
theorem subInclT_mul_apply {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → Prop)
    (N : Matrix ι ι A) (j : {i // pr i}) (i : ι) : ((subIncl A pr)ᵀ * N) j i = N (j : ι) i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (j : ι)
    (fun l _ hl => by rw [subIncl_transpose_apply, if_neg (fun h => hl h.symm), zero_mul])
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [subIncl_transpose_apply, if_pos rfl, one_mul]

/-- `((subIncl A pr)ᵀ * N) * subIncl A pr` is the `{i // pr i} × {i // pr i}`-minor of `N`. -/
theorem subInclT_mul_subIncl {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → Prop)
    (N : Matrix ι ι A) :
    ((subIncl A pr)ᵀ * N) * subIncl A pr = N.submatrix Subtype.val Subtype.val := by
  ext j j'
  rw [Matrix.mul_apply, Finset.sum_eq_single (j' : ι)
    (fun l _ hl => by rw [subInclT_mul_apply, subIncl_apply, if_neg (fun h => hl h.symm), mul_zero])
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [subInclT_mul_apply, subIncl_apply, if_pos rfl, mul_one]
  rfl

end

end Work.KT.Psi
