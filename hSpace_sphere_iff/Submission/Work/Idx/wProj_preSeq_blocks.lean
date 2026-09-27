import Mathlib
import Submission.Work.Idx.WPenBlk

namespace Work.Idx

/-!
# `Work.Idx.wProj_preSeq_blocks` — the prepend comparison, block by block

This file proves the prepend comparison of the W-linearisation at the level of the explicit
Fourier block matrix `wProj`:  restricting the `(d+2)`-block matrix `wProj n (d+1) (preSeq X b) Ψ'`
to its first `d+1` blocks (the sandwich `(wInc n d)ᵀ * · * wInc n d`) gives the `(d+1)`-block
matrix `wProj n d b Ψ` plus the correction `wUpdate n d b Ψ`, as soon as the Fourier data are
shifted, `Ψ' m = Ψ (m-1)`.

Everything is a finite-index computation; the two ingredients are

* the trivial `wInc` reduction: the sandwich picks out the entry at the indices
  `(p.1.castSucc, p.2)`, `(q.1.castSucc, q.2)`;
* the exact repackaging of the sum `∑_{j : Fin (d+2), q.1.castSucc < j} Ψ' (k+j-1-i) · c'_j`, where
  `c' = preSeq X b`: the summand at `j = 0` never occurs and `j = j' + 1` runs through `j' : Fin (d+1)`
  with `i ≤ j'`; splitting off `j' = i` and using `Ψ' m = Ψ (m-1)` leaves
  `∑_{j' > i} Ψ_{k+j'-1-i} · b_{j'} + Ψ_{k-1} · b_i`.
-/

/-- Splitting a sum indexed by `{j | I ≤ j}` into the sum over `{j | I < j}` and the single
term `j = I`. -/
lemma sum_univ_filter_le_eq_add {M : Type*} [AddCommMonoid M] {d : ℕ}
    (I : Fin (d + 1)) (g : Fin (d + 1) → M) :
    (∑ j ∈ Finset.univ.filter (fun j => I ≤ j), g j)
      = (∑ j ∈ Finset.univ.filter (fun j => I < j), g j) + g I := by
  have h : Finset.univ.filter (fun j : Fin (d + 1) => I ≤ j)
      = insert I (Finset.univ.filter (fun j : Fin (d + 1) => I < j)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      rcases lt_or_eq_of_le h with h | h
      · exact Or.inr h
      · exact Or.inl h.symm
    · rintro (rfl | h)
      · exact le_refl _
      · exact le_of_lt h
  rw [h, Finset.sum_insert (by simp), add_comm]

/-- The sum over the indices `j : Fin (d+2)` above `I.castSucc` is the sum over the indices
`j' : Fin (d+1)` above or equal to `I`, of the values at `j = j' + 1`.  (The value at `j = 0` is
discarded, and it is the only discarded index.) -/
lemma sum_univ_filter_castSucc_lt_eq_sum_univ_filter_le {M : Type*} [AddCommMonoid M] {d : ℕ}
    (I : Fin (d + 1)) (F : Fin (d + 2) → M) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin (d + 2) => Fin.castSucc I < j), F j)
      = ∑ j ∈ Finset.univ.filter (fun j : Fin (d + 1) => I ≤ j), F (Fin.succ j) := by
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_succ]
  have h0 : ¬ (Fin.castSucc I < (0 : Fin (d + 2))) := by simp
  rw [if_neg h0, zero_add]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hiff : Fin.castSucc I < Fin.succ j ↔ I ≤ j := by
    simp only [Fin.lt_def, Fin.le_def, Fin.val_castSucc, Fin.val_succ]
    omega
  rw [if_congr hiff rfl rfl]

section BlockInc

variable {X : Type} [TopologicalSpace X]

/-- `wInc n d` has a `1` in the entry `(p.1.castSucc, p.2) → (p.1, p.2)`. -/
lemma wInc_castSucc_left (n d : ℕ) (p : Fin (d + 1) × Fin n) :
    wInc (X := X) n d (Fin.castSucc p.1, p.2) p = 1 := by
  simp [wInc]

/-- `wInc n d` has no other nonzero entries. -/
lemma wInc_eq_zero_of_ne (n d : ℕ) {p : Fin (d + 2) × Fin n} {q : Fin (d + 1) × Fin n}
    (h : p ≠ (Fin.castSucc q.1, q.2)) : wInc (X := X) n d p q = 0 := by
  simp only [wInc]
  split_ifs with hc
  · exact absurd (Prod.ext (Fin.ext (by simpa using hc.1)) hc.2) h
  · rfl

/-- Left multiplication by `(wInc n d)ᵀ` restricts the row index to the first `d+1` blocks. -/
lemma transpose_wInc_mul_apply (n d : ℕ)
    (A : Matrix (Fin (d + 2) × Fin n) (Fin (d + 2) × Fin n) C(X, ℂ))
    (p : Fin (d + 1) × Fin n) (q : Fin (d + 2) × Fin n) :
    (Matrix.transpose (wInc (X := X) n d) * A) p q = A (Fin.castSucc p.1, p.2) q := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (Fin.castSucc p.1, p.2)]
  · rw [Matrix.transpose_apply, wInc_castSucc_left, one_mul]
  · intro b _ hb
    rw [Matrix.transpose_apply, wInc_eq_zero_of_ne (n := n) (d := d) hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The sandwich `(wInc n d)ᵀ * A * wInc n d` is the top-left `(d+1) × (d+1)` block of `A`. -/
lemma transpose_wInc_mul_wInc_apply (n d : ℕ)
    (A : Matrix (Fin (d + 2) × Fin n) (Fin (d + 2) × Fin n) C(X, ℂ))
    (p q : Fin (d + 1) × Fin n) :
    (Matrix.transpose (wInc (X := X) n d) * A * wInc (X := X) n d) p q
      = A (Fin.castSucc p.1, p.2) (Fin.castSucc q.1, q.2) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (Fin.castSucc q.1, q.2)]
  · rw [transpose_wInc_mul_apply, wInc_castSucc_left, mul_one]
  · intro b _ hb
    rw [wInc_eq_zero_of_ne (n := n) (d := d) hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end BlockInc

section Prepend

variable {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The `(j'-th)` coefficient of `preSeq X b = (0, b₀, …, b_d)` is `b_{j'}`. -/
@[simp] lemma preSeq_succ (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (j : Fin (d + 1)) :
    Work.KT.Idx.preSeq X b (Fin.succ j) = b j := by
  rw [Work.KT.Idx.preSeq_apply,
    dif_pos (by simp : 0 < (((Fin.succ j : Fin (d + 2))) : ℕ))]
  exact congrArg b (Fin.ext (by simp))

/-- **The prepend comparison for the defining sums of `wProj`.**  For a coefficient sequence `b` of
length `d+1`, the coefficient sequence `c' = preSeq X b` of length `d+2` and Fourier data related
by `Ψ' m = Ψ (m-1)`, the `(k,i)` block sum of the big `wProj` collapses to the `(k,i)` block sum of
the small `wProj` plus the correction `Ψ_{k-1} · b_i`. -/
lemma wProj_preSeq_sum (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (Ψ Ψ' : ℤ → Matrix (Fin n) (Fin n) C(X, ℂ)) (hΨ : ∀ m : ℤ, Ψ' m = Ψ (m - 1))
    (I : Fin (d + 1)) (K : ℤ) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin (d + 2) => Fin.castSucc I < j),
        Ψ' (K + (j : ℤ) - 1 - (I : ℤ)) * Work.KT.Idx.preSeq X b j)
      = (∑ j ∈ Finset.univ.filter (fun j : Fin (d + 1) => I < j),
          Ψ (K + (j : ℤ) - 1 - (I : ℤ)) * b j) + Ψ (K - 1) * b I := by
  rw [sum_univ_filter_castSucc_lt_eq_sum_univ_filter_le]
  have hterm : ∀ j : Fin (d + 1),
      Ψ' (K + ((Fin.succ j : Fin (d + 2)) : ℤ) - 1 - (I : ℤ))
          * Work.KT.Idx.preSeq X b (Fin.succ j)
        = Ψ (K + (j : ℤ) - 1 - (I : ℤ)) * b j := by
    intro j
    rw [preSeq_succ]
    congr 1
    rw [hΨ]
    congr 1
    have : ((Fin.succ j : Fin (d + 2)) : ℤ) = (j : ℤ) + 1 := by simp [Fin.val_succ]
    rw [this]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), sum_univ_filter_le_eq_add]
  rw [show K + (I : ℤ) - 1 - (I : ℤ) = K - 1 by ring]

end Prepend

/-- **The prepend comparison, explicitly, at the level of the Fourier block matrix.**

`wInc n d : Matrix (Fin (d+2) × Fin n) (Fin (d+1) × Fin n)` is the block inclusion (identity in
the first `d+1` blocks, zero in the last), so `Matrix.transpose (wInc n d) * X * wInc n d` is the
top-left `(d+1) × (d+1)` block of a `(d+2)`-block matrix `X`.  `wProj n D c Ψ` is the block matrix
with block `(k,i)` equal to `∑_{j > i} Ψ_{k+j-1-i} * c_j` (zero in the last block column
`i = D`), `wUpdate n d b Ψ` is the block matrix with block `(k,i)` equal to `Ψ_{k-1} * b_i`, and
`Work.KT.Idx.preSeq X b = (0, b₀, …, b_d)` is the coefficient sequence of the polynomial `z · q_b`.

Claim: if the Fourier data of the `(d+2)`-indexed sequence `preSeq X b` is the shift of the Fourier
data of `b`, `Ψ' m = Ψ (m-1)` for all `m : ℤ`, then

`(wInc n d)ᵀ * wProj n (d+1) (preSeq X b) Ψ' * wInc n d = wProj n d b Ψ + wUpdate n d b Ψ`.

Proof: a pure finite-index computation.  With `c' = preSeq X b` (`c'_0 = 0`, `c'_{j'+1} = b_{j'}`
for `j' : Fin (d+1)`), the `(k,i)` block of the left side (all indices cast into `Fin (d+2)`) is
`∑_{j : Fin (d+2), i < j} Ψ'_{k+j-1-i} c'_j`; the `j = 0` term never occurs (`i ≥ 0`, so `i < 0` is
false), and substituting `j = j' + 1` (`j' : Fin (d+1)`, condition `j' ≥ i`) and `Ψ' m = Ψ (m-1)`
gives `∑_{j' ≥ i} Ψ_{k+j'-1-i} b_{j'} = ∑_{j' > i} Ψ_{k+j'-1-i} b_{j'} + Ψ_{k-1} * b_i`, which is
the `(k,i)` block of `wProj n d b Ψ + wUpdate n d b Ψ`.  Useful: `Finset.sum_eq_zero`,
`Finset.sum_congr`, `Fin.ext_iff`, `Fin.val_succ`, `Finset.sum_filter`, and the index change
`Finset.sum_bij` / `Finset.sum_nbij'`. -/
theorem wProj_preSeq_blocks {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (Ψ Ψ' : ℤ → Matrix (Fin n) (Fin n) C(X, ℂ)) (hΨ : ∀ m : ℤ, Ψ' m = Ψ (m - 1)) :
    Matrix.transpose (wInc (X := X) n d) *
        wProj n (d + 1) (Work.KT.Idx.preSeq X b) Ψ' * wInc (X := X) n d
      = wProj n d b Ψ + wUpdate n d b Ψ := by
  apply Matrix.ext
  intro p q
  have hL : (wProj n (d + 1) (Work.KT.Idx.preSeq X b) Ψ')
        (Fin.castSucc p.1, p.2) (Fin.castSucc q.1, q.2)
      = (∑ j ∈ Finset.univ.filter (fun j : Fin (d + 2) => Fin.castSucc q.1 < j),
          Ψ' ((p.1 : ℤ) + (j : ℤ) - 1 - (q.1 : ℤ))
            * Work.KT.Idx.preSeq X b j) p.2 q.2 := by
    simp [wProj]
  have hR : (wProj n d b Ψ) p q + (wUpdate n d b Ψ) p q
      = ((∑ j ∈ Finset.univ.filter (fun j : Fin (d + 1) => q.1 < j),
          Ψ ((p.1 : ℤ) + (j : ℤ) - 1 - (q.1 : ℤ)) * b j)
          + Ψ ((p.1 : ℤ) - 1) * b q.1) p.2 q.2 := by
    simp [wProj, wUpdate]
  rw [Matrix.add_apply, transpose_wInc_mul_wInc_apply, hL,
    wProj_preSeq_sum (hΨ := hΨ) (I := q.1) (K := (p.1 : ℤ)), hR]

end Work.Idx
