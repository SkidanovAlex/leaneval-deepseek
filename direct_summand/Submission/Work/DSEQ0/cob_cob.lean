import Mathlib
import Submission.Work.DSEQ0.SurjBasic

/-!
# `d ∘ d = 0` for the surjection (Čech) complex

We prove `Work.DSEQ0.cob_cob`: the alternating coboundary `cob` introduced in
`Submission.Work.DSEQ0.SurjBasic` satisfies `cob (k+1) (cob k f) = 0`.

Writing `succAbove_j : Fin (k+1) → Fin (k+2)` for the order embedding that skips `j`,

```
(cob k f) x = ∑ j : Fin (k+2), (-1)^j • f (x ∘ succAbove_j),
```

hence

```
(cob (k+1) (cob k f)) x
  = ∑ p : Fin (k+3) × Fin (k+2),
      (-1)^{p.1+p.2} • f (x ∘ (succAbove_{p.1} ∘ succAbove_{p.2})).
```

The assignment `(j,i) ↦ succAbove_j ∘ succAbove_i` is *not* injective: the pair `(j,i)`
and the pair obtained by inserting the same two values in the other order give the same
composite map.  `swapIdx` below is the resulting fixed-point-free involution of
`Fin (k+3) × Fin (k+2)`; it preserves the composite map (the cosimplicial identities
`succAbove_succAbove_lt` / `succAbove_succAbove_le`) and it flips the parity of
`p.1 + p.2`.  `Finset.sum_ninvolution` then makes the whole double sum vanish.
-/

namespace Work.DSEQ0

universe u

/-! ## The value of `Fin.succAbove` -/

/-- `Fin.succAbove p x` embeds `x` by `castSucc` when the result is `< p` and by `succ`
otherwise; spelled out in terms of values this reads as follows. -/
theorem val_succAbove {n : ℕ} (p : Fin (n+1)) (x : Fin n) :
    (Fin.succAbove p x : ℕ) = if (x:ℕ) < (p:ℕ) then (x:ℕ) else (x:ℕ)+1 := by
  rw [show Fin.succAbove p x = if (x:ℕ) < (p:ℕ) then x.castSucc else x.succ from by
    rw [Fin.succAbove]
    by_cases h : (x:ℕ) < (p:ℕ)
    · have h' : Fin.castSucc x < p := by simp only [Fin.lt_def, Fin.val_castSucc]; exact h
      rw [ite_eq_left h', ite_eq_left h]
    · have h' : ¬ (Fin.castSucc x < p) := by simp only [Fin.lt_def, Fin.val_castSucc]; omega
      rw [ite_eq_right h', ite_eq_right h]]
  split_ifs <;> rfl

/-! ## The two cosimplicial identities

For `i : Fin (m+1)` and `j : Fin (m+2)` the composite `succAbove_j ∘ succAbove_i`
depends only on the (unordered) pair of values inserted; the two insertions of the
same pair are related by the identities below. -/

/-- Case `i < j`: the two ways of inserting the values `i` and `j` coincide. -/
theorem succAbove_succAbove_lt {m : ℕ} (i : Fin (m+1)) (j : Fin (m+2))
    (h : (i:ℕ) < (j:ℕ)) (t : Fin m) :
    Fin.succAbove j (Fin.succAbove i t)
      = Fin.succAbove (Fin.castSucc i) (Fin.succAbove ⟨(j:ℕ)-1, by omega⟩ t) := by
  apply Fin.ext
  simp only [val_succAbove, Fin.val_castSucc]
  split_ifs <;> omega

/-- Case `j ≤ i`: the two ways of inserting the values `j` and `i+1` coincide. -/
theorem succAbove_succAbove_le {m : ℕ} (i : Fin (m+1)) (j : Fin (m+2))
    (h : (j:ℕ) ≤ (i:ℕ)) (t : Fin m) :
    Fin.succAbove j (Fin.succAbove i t)
      = Fin.succAbove (Fin.succ i) (Fin.succAbove ⟨(j:ℕ), by omega⟩ t) := by
  apply Fin.ext
  simp only [val_succAbove, Fin.val_succ]
  split_ifs <;> omega

/-! ## The sign-reversing involution of `Fin (k+3) × Fin (k+2)` -/

/-- The involution exchanging the two ways of writing the composite map
`succAbove_{p.1} ∘ succAbove_{p.2}`.  On a pair `(j,i)` with `i < j` it replaces the
insertion of `i` at the "inner" slot by the equivalent insertion of `j`, and vice
versa. -/
def swapIdx (k : ℕ) : Fin (k+3) × Fin (k+2) → Fin (k+3) × Fin (k+2) := fun p =>
  if h : (p.2 : ℕ) < (p.1 : ℕ) then
    (Fin.castSucc p.2, ⟨(p.1 : ℕ) - 1, by omega⟩)
  else
    (Fin.succ p.2, ⟨(p.1 : ℕ), by omega⟩)

/-- The value of the first component of `swapIdx`. -/
theorem swapIdx_fst_val (k : ℕ) (p : Fin (k+3) × Fin (k+2)) :
    ((swapIdx k p).1 : ℕ) = if (p.2 : ℕ) < (p.1 : ℕ) then (p.2 : ℕ) else (p.2 : ℕ) + 1 := by
  rw [swapIdx]; split_ifs <;> simp [Fin.val_castSucc, Fin.val_succ]

/-- The value of the second component of `swapIdx`. -/
theorem swapIdx_snd_val (k : ℕ) (p : Fin (k+3) × Fin (k+2)) :
    ((swapIdx k p).2 : ℕ) = if (p.2 : ℕ) < (p.1 : ℕ) then (p.1 : ℕ) - 1 else (p.1 : ℕ) := by
  rw [swapIdx]; split_ifs <;> simp

/-- `swapIdx` is an involution. -/
theorem swapIdx_swapIdx (k : ℕ) (p : Fin (k+3) × Fin (k+2)) :
    swapIdx k (swapIdx k p) = p := by
  ext <;> simp only [swapIdx_fst_val, swapIdx_snd_val] <;> split_ifs <;> omega

/-- `swapIdx` has no fixed point. -/
theorem swapIdx_ne (k : ℕ) (p : Fin (k+3) × Fin (k+2)) : swapIdx k p ≠ p := by
  intro h
  have hc := congrArg (fun q : Fin (k+3) × Fin (k+2) => (q.1 : ℕ)) h
  simp only [swapIdx_fst_val] at hc
  split_ifs at hc <;> omega

/-- Unfolding of `swapIdx` in the first case. -/
theorem swapIdx_pair_lt (k : ℕ) (p : Fin (k+3) × Fin (k+2)) (h : (p.2:ℕ) < (p.1:ℕ)) :
    swapIdx k p = (Fin.castSucc p.2, (⟨(p.1:ℕ)-1, by omega⟩ : Fin (k+2))) := by
  rw [swapIdx, dite_eq_left h]

/-- Unfolding of `swapIdx` in the second case. -/
theorem swapIdx_pair_ge (k : ℕ) (p : Fin (k+3) × Fin (k+2)) (h : ¬ (p.2:ℕ) < (p.1:ℕ)) :
    swapIdx k p = (Fin.succ p.2, (⟨(p.1:ℕ), by omega⟩ : Fin (k+2))) := by
  rw [swapIdx, dite_eq_right h]

/-- `swapIdx` does not change the composite insertion map, case `i < j`. -/
theorem succAbove_swapIdx_lt (k : ℕ) (p : Fin (k+3) × Fin (k+2)) (h : (p.2:ℕ) < (p.1:ℕ)) :
    Fin.succAbove (swapIdx k p).1 ∘ Fin.succAbove (swapIdx k p).2
      = Fin.succAbove p.1 ∘ Fin.succAbove p.2 := by
  rw [swapIdx_pair_lt k p h]
  exact (funext (succAbove_succAbove_lt p.2 p.1 h)).symm

/-- `swapIdx` does not change the composite insertion map, case `j ≤ i`. -/
theorem succAbove_swapIdx_ge (k : ℕ) (p : Fin (k+3) × Fin (k+2)) (h : ¬ (p.2:ℕ) < (p.1:ℕ)) :
    Fin.succAbove (swapIdx k p).1 ∘ Fin.succAbove (swapIdx k p).2
      = Fin.succAbove p.1 ∘ Fin.succAbove p.2 := by
  rw [swapIdx_pair_ge k p h]
  exact (funext (succAbove_succAbove_le p.2 p.1 (by omega))).symm

/-! ## The vanishing of the double sum -/

/-- `(-1)^{n+1} = -(-1)^n`. -/
theorem neg_one_pow_succ (n : ℕ) : (-1:ℤ) ^ (n+1) = - ((-1:ℤ)^n) := by
  rw [pow_succ]; ring

/-- For fixed `x` and `f`, the signed double sum over the insertion pairs vanishes:
`swapIdx` pairs up the terms of equal value and opposite sign. -/
theorem sum_prod_eq_zero {ι : Type u} [Fintype ι] {M : Type u} [AddCommGroup M] (k : ℕ)
    (x : Fin (k+3) → ι) (f : (Fin (k+1) → ι) → M) :
    (∑ p : Fin (k+3) × Fin (k+2),
      ((-1:ℤ) ^ ((p.1:ℕ) + (p.2:ℕ))) • f (x ∘ (Fin.succAbove p.1 ∘ Fin.succAbove p.2))) = 0 := by
  refine Finset.sum_ninvolution (s := Finset.univ)
    (g := fun p : Fin (k+3) × Fin (k+2) => swapIdx k p) ?_ ?_ ?_ ?_
  · intro p
    by_cases h : (p.2:ℕ) < (p.1:ℕ)
    · have hcomp : x ∘ (Fin.succAbove (swapIdx k p).1 ∘ Fin.succAbove (swapIdx k p).2)
          = x ∘ (Fin.succAbove p.1 ∘ Fin.succAbove p.2) := by
        rw [succAbove_swapIdx_lt k p h]
      rw [hcomp]
      have hsign : ((-1:ℤ) ^ (((swapIdx k p).1 : ℕ) + ((swapIdx k p).2 : ℕ)))
          = - ((-1:ℤ) ^ ((p.1:ℕ) + (p.2:ℕ))) := by
        rw [swapIdx_fst_val k p, ite_eq_left h, swapIdx_snd_val k p, ite_eq_left h]
        have h2 : (p.2:ℕ) + ((p.1:ℕ) - 1) + 1 = (p.1:ℕ) + (p.2:ℕ) := by omega
        rw [← h2, neg_one_pow_succ]
        simp
      rw [← add_zsmul, hsign]
      simp
    · have hcomp : x ∘ (Fin.succAbove (swapIdx k p).1 ∘ Fin.succAbove (swapIdx k p).2)
          = x ∘ (Fin.succAbove p.1 ∘ Fin.succAbove p.2) := by
        rw [succAbove_swapIdx_ge k p h]
      rw [hcomp]
      have hsign : ((-1:ℤ) ^ (((swapIdx k p).1 : ℕ) + ((swapIdx k p).2 : ℕ)))
          = - ((-1:ℤ) ^ ((p.1:ℕ) + (p.2:ℕ))) := by
        rw [swapIdx_fst_val k p, ite_eq_right h, swapIdx_snd_val k p, ite_eq_right h]
        have h2 : (p.2:ℕ) + 1 + (p.1:ℕ) = (p.1:ℕ) + (p.2:ℕ) + 1 := by omega
        rw [h2, neg_one_pow_succ]
      rw [← add_zsmul, hsign]
      simp
  · intro p _
    exact swapIdx_ne k p
  · intro p
    exact Finset.mem_univ _
  · intro p
    exact swapIdx_swapIdx k p

/-! ## The main result -/

theorem cob_cob {ι : Type u} [Fintype ι] {M : Type u} [AddCommGroup M] (k : ℕ)
    (f : (Fin (k + 1) → ι) → M) : cob (k + 1) (cob k f) = 0 := by
  funext x
  simp only [cob, Pi.zero_apply, Finset.smul_sum, smul_smul, ← pow_add]
  rw [← Fintype.sum_prod_type']
  exact sum_prod_eq_zero k x f

end Work.DSEQ0
