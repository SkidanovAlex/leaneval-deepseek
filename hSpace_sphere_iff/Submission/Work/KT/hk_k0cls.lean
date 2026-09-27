import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.HopfK.Basic
import Submission.Work.KT.Basic
import Submission.Work.KT.Fund.Basic

namespace Work.KT

/-!
# `Work.KT.hk_k0cls` — the unit class of `K₀` scales with the size

The two elementary facts about the idempotent model of `K₀` (`Submission/Work/KT/Defs.lean`):

* `cls (Mat.one A (n+1)) = ((n : ℤ) + 1) • cls (Mat.one A 1)`: the class of the trivial bundle
  of rank `r` is `r` times the class of the trivial line bundle.  This is proved by induction
  from `1_r ⊕ 1_s = 1_{r+s}` (`Mat.one_sum`, `hk_Mat_sum_one` below) and additivity of `cls`
  on block sums (`cls_sum`).
* `Mat.MvN (diagMat A r n) (Mat.one A r)` for `r ≤ n`: the diagonal idempotent `diag(1_r, 0)` of
  size `n` is Murray–von Neumann equivalent to the identity of size `r`, with explicit witnesses
  (the "inclusion" `a` and the "restriction" `b` of `Fin r` into `Fin n`).  The entries of the two
  products are evaluated by the elementary sum `hk_sum_val_ite`.

Everything here is over an arbitrary ring `A`; no commutativity is used.
-/

noncomputable section

/-! ## The sum of two indicator columns -/

/-- The dot product of the two "delta columns" at `u` and `v` inside `Fin m`: it is `1` exactly
when `u = v` and `u` is in range. -/
lemma hk_sum_val_ite {A : Type} [Ring A] (m u v : ℕ) :
    (∑ j : Fin m, (if u = (j : ℕ) then (1 : A) else 0) * (if (j : ℕ) = v then (1 : A) else 0))
      = if u = v then (if u < m then (1 : A) else 0) else 0 := by
  rcases eq_or_ne u v with h | h
  · subst h
    have hcongr : ∀ j : Fin m,
        (if u = (j : ℕ) then (1 : A) else 0) * (if (j : ℕ) = u then (1 : A) else 0)
          = (if u = (j : ℕ) then (1 : A) else 0) := by
      intro j
      by_cases hj : u = (j : ℕ) <;> simp [hj]
    rw [Finset.sum_congr rfl (fun j _ => hcongr j)]
    by_cases hu : u < m
    · rw [if_pos hu, if_pos rfl]
      rw [Finset.sum_eq_single ⟨u, hu⟩]
      · simp
      · intro b _ hb
        have hbu : ¬ (u = (b : ℕ)) := fun hh => hb (Fin.ext hh.symm)
        simp [hbu]
      · intro hc
        exact absurd (Finset.mem_univ _) hc
    · rw [if_neg hu, if_pos rfl]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      have hju : ¬ (u = (j : ℕ)) := fun hh => hu (hh ▸ j.isLt)
      simp [hju]
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    by_cases hj : u = (j : ℕ)
    · have hjv : ¬ ((j : ℕ) = v) := fun hh => h (hj.trans hh)
      rw [if_pos hj, if_neg hjv, mul_zero]
    · rw [if_neg hj, zero_mul]

/-! ## The identity matrices add up -/

/-- `1_m ⊕ 1_n = 1_{m+n}`. -/
lemma hk_Mat_sum_one (A : Type) [Ring A] (m n : ℕ) :
    (Mat.one A m).sum (Mat.one A n) = Mat.one A (m + n) := by
  show (⟨m + n, Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) A) 0 0
        (1 : Matrix (Fin n) (Fin n) A))⟩ : Mat A) = ⟨m + n, 1⟩
  congr 1
  rw [Matrix.fromBlocks_one, Matrix.reindex_apply]
  exact Matrix.submatrix_one_equiv finSumFinEquiv.symm

/-- The class of the empty identity matrix vanishes (it is `0 ⊕ 0`). -/
lemma hk_cls_one_zero (A : Type) [Ring A] : cls (Mat.one A 0) = (0 : K0 A) := by
  have h1 : cls (Mat.sum (Mat.one A 0) (Mat.one A 0)) = cls (Mat.one A 0) + cls (Mat.one A 0) :=
    cls_sum (Mat.one_isIdem (R := A) 0) (Mat.one_isIdem (R := A) 0)
  rw [hk_Mat_sum_one A 0 0, Nat.add_zero] at h1
  have h2 : cls (Mat.one A 0) + 0 = cls (Mat.one A 0) + cls (Mat.one A 0) := by
    rw [add_zero]; exact h1
  exact (add_left_cancel h2).symm

/-- `cls (1_r) = r • cls (1₁)`. -/
lemma hk_cls_one_nsmul (A : Type) [Ring A] (r : ℕ) :
    cls (Mat.one A r) = r • cls (Mat.one A 1) := by
  induction r with
  | zero => rw [zero_nsmul, hk_cls_one_zero]
  | succ r ih =>
    rw [← hk_Mat_sum_one A r 1, cls_sum (Mat.one_isIdem (R := A) r) (Mat.one_isIdem (R := A) 1),
      ih, succ_nsmul]

/-! ## `diag(1_r, 0)` is Murray–von Neumann equivalent to `1_r` -/

/-- For `r ≤ n` the diagonal idempotent `diag(1_r, 0)` of size `n` is Murray–von Neumann
equivalent to the identity of size `r`, with the explicit witnesses
`a_{ij} = δ_{ij}` (`i : Fin r`, `j : Fin n`) and `b_{ji} = δ_{ji}`. -/
lemma hk_diagMat_mvN_one (A : Type) [Ring A] (r n : ℕ) (h : r ≤ n) :
    Mat.MvN (diagMat A r n) (Mat.one A r) := by
  let a : Matrix (Fin r) (Fin n) A := fun i j => if (i : ℕ) = (j : ℕ) then 1 else 0
  let b : Matrix (Fin n) (Fin r) A := fun j i => if (j : ℕ) = (i : ℕ) then 1 else 0
  have hba : b * a = (diagMat A r n).2 := by
    ext j j'
    rw [Matrix.mul_apply]
    simp only [a, b]
    rw [hk_sum_val_ite r (j : ℕ) (j' : ℕ)]
    rw [show (diagMat A r n).2 =
      Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then (1 : A) else 0) from rfl]
    rw [Matrix.diagonal_apply]
    by_cases hj : j = j'
    · subst hj; simp
    · have hne : ¬ ((j : ℕ) = (j' : ℕ)) := fun hh => hj (Fin.ext hh)
      simp [hj, hne]
  have hab : a * b = (Mat.one A r).2 := by
    ext i i'
    rw [Matrix.mul_apply]
    simp only [a, b]
    rw [hk_sum_val_ite n (i : ℕ) (i' : ℕ)]
    rw [if_pos (i.isLt.trans_le h)]
    rw [show (Mat.one A r).2 = (1 : Matrix (Fin r) (Fin r) A) from rfl, Matrix.one_apply]
    by_cases hi : i = i'
    · subst hi; simp
    · have hne : ¬ ((i : ℕ) = (i' : ℕ)) := fun hh => hi (Fin.ext hh)
      simp [hi, hne]
  exact ⟨a, b, hba, hab⟩

/-- The unit class of `K₀ A` scales with the size, and the diagonal idempotent `diag(1_r,0)` of
size `n ≥ r` is Murray–von Neumann equivalent to the identity of size `r`. -/
theorem hk_k0cls (A : Type) [Ring A] :
    (∀ (n : ℕ), cls (Mat.one A (n + 1)) = ((n : ℤ) + 1) • cls (Mat.one A 1)) ∧
    (∀ (r n : ℕ), r ≤ n → Mat.MvN (diagMat A r n) (Mat.one A r)) := by
  refine ⟨fun n => ?_, fun r n h => hk_diagMat_mvN_one A r n h⟩
  rw [hk_cls_one_nsmul A (n + 1),
    show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, natCast_zsmul]

end

end Work.KT
