import Mathlib
import Submission.Work.Idx.WPenBlk

namespace Work.Idx

/-- **Entry form of the block inclusion.**

`wInc n d : Matrix (Fin (d+2) × Fin n) (Fin (d+1) × Fin n)` is the identity on the first `d+1`
blocks and zero in the last one, so its `(p, r)` entry is `1` exactly when `p` is the image of `r`
under the block inclusion `r ↦ (Fin.castSucc r.1, r.2)`. -/
lemma wInc_apply {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n d : ℕ) (p : Fin (d + 2) × Fin n) (r : Fin (d + 1) × Fin n) :
    wInc (X := X) n d p r = if p = (Fin.castSucc r.1, r.2) then 1 else 0 := by
  have hiff : ((p.1 : ℕ) = (r.1 : ℕ) ∧ p.2 = r.2) ↔ p = (Fin.castSucc r.1, r.2) := by
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := h
      exact Prod.ext (Fin.ext (by simpa using h1)) h2
    · intro h
      rw [h]
      exact ⟨rfl, rfl⟩
  rw [wInc]
  by_cases h : p = (Fin.castSucc r.1, r.2)
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]

/-- **Entry form of the block projection `wQbig = wInc * wIncᵀ`.**

`wQbig n d` is `wInc n d * (wInc n d)ᵀ`, which is the projection of `Fin (d+2) × Fin n` onto its
first `d+1` blocks; since `wInc` has orthonormal columns it is in fact the *diagonal* matrix
`1` on the first `d+1` blocks and `0` on the last block row/column.  Thus
`wQbig n d p q = if p = q ∧ (p.1 : ℕ) < d + 1 then 1 else 0`. -/
lemma wQbig_apply {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n d : ℕ) (p q : Fin (d + 2) × Fin n) :
    wQbig (X := X) n d p q = if p = q ∧ (p.1 : ℕ) < d + 1 then 1 else 0 := by
  rw [wQbig, Matrix.mul_apply]
  have hsummand : ∀ r : Fin (d + 1) × Fin n,
      wInc (X := X) n d p r * (Matrix.transpose (wInc (X := X) n d)) r q
        = if (p = (Fin.castSucc r.1, r.2) ∧ q = (Fin.castSucc r.1, r.2)) then 1 else 0 := by
    intro r
    rw [Matrix.transpose_apply, wInc_apply, wInc_apply]
    by_cases h1 : p = (Fin.castSucc r.1, r.2) <;>
      by_cases h2 : q = (Fin.castSucc r.1, r.2) <;> simp [h1, h2]
  simp_rw [hsummand]
  have hinj : ∀ r s : Fin (d + 1) × Fin n,
      (Fin.castSucc r.1, r.2) = (Fin.castSucc s.1, s.2) → r = s := by
    intro r s h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext (by simpa using congrArg Fin.val h.1)) h.2
  by_cases h : p = q ∧ (p.1 : ℕ) < d + 1
  · rw [if_pos h]
    let r0 : Fin (d + 1) × Fin n := (⟨(p.1 : ℕ), h.2⟩, p.2)
    have hpr0 : p = (Fin.castSucc r0.1, r0.2) := Prod.ext (Fin.ext (by simp [r0])) rfl
    have hqr0 : q = (Fin.castSucc r0.1, r0.2) := by rw [← h.1]; exact hpr0
    refine (Finset.sum_eq_single r0 ?_ ?_).trans ?_
    · intro r _ hr
      rw [if_neg]
      rintro ⟨hp, _⟩
      exact hr (hinj r r0 (by rw [← hp]; exact hpr0))
    · intro hh; exact absurd (Finset.mem_univ _) hh
    · rw [if_pos ⟨hpr0, hqr0⟩]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [if_neg]
    rintro ⟨hp, hq⟩
    exact h ⟨hp.trans hq.symm, by rw [hp]; exact r.1.isLt⟩

/-- **A matrix with vanishing last block column is fixed by `wQbig`.**

If the last block column of `M : Matrix (Fin (d+2) × Fin n) (Fin (d+2) × Fin n)` vanishes, i.e.
`M p q = 0` whenever `(q.1 : ℕ) = d + 1`, then `M * wQbig n d = M`: multiplying on the right by the
projection onto the first `d+1` blocks keeps the first `d+1` columns (`wQbig` is the diagonal
projection, `wQbig_apply`) and kills the last one, where `M` already vanishes. -/
lemma mul_wQbig_of_last_col_zero {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n d : ℕ) (M : Matrix (Fin (d + 2) × Fin n) (Fin (d + 2) × Fin n) C(X, ℂ))
    (hM : ∀ p q, (q.1 : ℕ) = d + 1 → M p q = 0) :
    M * wQbig (X := X) n d = M := by
  apply Matrix.ext
  intro p q
  rw [Matrix.mul_apply]
  refine (Finset.sum_eq_single (s := Finset.univ)
    (f := fun r => M p r * wQbig (X := X) n d r q) q ?_ ?_).trans ?_
  · intro r _ hr
    rw [wQbig_apply, if_neg (by rintro ⟨hrq, _⟩; exact hr hrq), mul_zero]
  · intro hh; exact absurd (Finset.mem_univ _) hh
  · rw [wQbig_apply]
    by_cases hq : (q.1 : ℕ) < d + 1
    · rw [if_pos ⟨rfl, hq⟩, mul_one]
    · rw [if_neg (fun hh => hq hh.2), mul_zero]
      have hqd : (q.1 : ℕ) = d + 1 := by have := q.1.isLt; omega
      exact (hM p q hqd).symm

/-- **The projection of a `(D+2)`-block pencil is fixed by the projection onto the first `D+1`
blocks.**

`wInc n D : Matrix (Fin (D+2) × Fin n) (Fin (D+1) × Fin n)` is the block inclusion (identity in the
first `D+1` blocks, zero in the last) and `wQbig n D = wInc n D * (wInc n D)ᵀ` is the projection of
`Fin (D+2) × Fin n` onto its first `D+1` blocks (it is the identity outside the last block row and
column).  `wProj n (D+1) c Ψ` is the block matrix with block `(k,i)` equal to
`∑_{j > i} Ψ_{k+j-1-i} * c_j`, where `i` ranges over `Fin (D+2)`; in particular its block column
`i = D+1` (the last one) **vanishes**, because the index filter `{j : Fin (D+2) | i < j}` is empty
when `i` is the last index.

Claim: `wProj n (D+1) c Ψ * wQbig n D = wProj n (D+1) c Ψ` — for *every* `c` and `Ψ`, no
hypothesis.

Proof: multiply by `wInc` on the right instead: `M * (wInc * wIncᵀ) = (M * wInc) * wIncᵀ`, or
compute entries.  Entry form of `wQbig` (a good helper lemma): `wQbig n D p q = if p = q ∧
(p.1 : ℕ) < D + 1 then 1 else 0` (the sum `∑_r wInc p r * wInc q r` is nonempty only for the
unique `r` with `p = q = Fin.castSucc r`; `wInc_apply`/`Finset.sum_eq_single`).  Hence
`(wProj * wQbig) p q = wProj p q * wQbig q q`, which is `wProj p q` when `(q.1 : ℕ) < D + 1` and
`0 = wProj p q` when `q.1 = D + 1` is the last block (there the filter `{j | q.1 < j}` is empty:
`Fin.eq_mk_iff_val_eq`, `Finset.filter_eq_empty_iff`, `Finset.sum_empty`).  Could also be done by
proving the general statement "if the last block column of `M` vanishes then `M * wQbig = M`". -/
theorem wProj_mul_wQbig {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n D : ℕ) (c : Fin (D + 2) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (Ψ : ℤ → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    wProj n (D + 1) c Ψ * wQbig (X := X) n D = wProj n (D + 1) c Ψ := by
  refine mul_wQbig_of_last_col_zero (X := X) n D (wProj n (D + 1) c Ψ) ?_
  intro p q hq
  -- the last block column `q.1 = D+1` of `wProj` vanishes: no index is larger than it.
  rw [wProj]
  have hfilter : Finset.univ.filter (fun j : Fin (D + 1 + 1) => q.1 < j) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro j _
    rw [not_lt]
    refine Fin.le_iff_val_le_val.mpr ?_
    have h1 : (q.1 : ℕ) < D + 2 := by omega
    have h2 : (j : ℕ) < D + 2 := j.isLt
    omega
  rw [hfilter]
  simp

end Work.Idx
