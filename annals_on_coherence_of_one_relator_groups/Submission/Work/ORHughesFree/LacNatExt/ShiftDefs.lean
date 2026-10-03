import Mathlib
import Submission.Work.ORHughesFree.LacNatExt.PolyTDefs

set_option autoImplicit false
open Matrix
open Work.ORHughesFree
open Work.ORHughesFree.NaturalExtension
open Work.ORHughesFree.MatrixBlocks

namespace Work.ORHughesFree.NaturalExtension

variable {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]

noncomputable section

/-- The downward shift matrix `N` (nilpotent with `N ^ d = 0`): its `(q, q')` entry is `t`
when the block index of `q` is one larger than that of `q'` and the inner indices agree, and
`0` otherwise.  With this matrix, `lacWB = -1 + lacSB`. -/
def lacSB (d n : ℕ) : Matrix (Fin (d * n)) (Fin (d * n)) (SkewL R) :=
  fun q q' => if (q.divNat : ℕ) = (q'.divNat : ℕ) + 1 ∧ q.modNat = q'.modNat
    then skewLaurentT else 0

theorem lacand_ite_zero {S : Type*} [Zero S] (P Q : Prop) [Decidable P] [Decidable Q] (x : S) :
    (if P ∧ Q then x else 0) = (if Q then (if P then x else 0) else 0) := by
  by_cases hQ : Q <;> by_cases hP : P <;> simp [hQ, hP]

theorem lacSB_pow_apply (d n k : ℕ) :
    ∀ q q' : Fin (d*n), (lacSB (R:=R) d n ^ k) q q' =
      (if (q.divNat : ℕ) = (q'.divNat : ℕ) + k ∧ q.modNat = q'.modNat
        then (skewLaurentT : SkewL R) ^ k else 0) := by
  induction k with
  | zero =>
    intro q q'
    rw [pow_zero, Matrix.one_apply]
    have hiff : ((q.divNat : ℕ) = (q'.divNat : ℕ) + 0 ∧ q.modNat = q'.modNat) ↔ q = q' := by
      constructor
      · rintro ⟨h1, h2⟩
        have hd : q.divNat = q'.divNat := Fin.ext (by simpa using h1)
        exact finProdFinEquiv.symm.injective (by
          rw [finProdFinEquiv_symm_apply, finProdFinEquiv_symm_apply, hd, h2])
      · rintro rfl; simp
    by_cases h : q = q'
    · subst h; simp
    · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc))]
  | succ k ih =>
    intro q q'
    rw [pow_succ, Matrix.mul_apply]
    rw [← Equiv.sum_comp (finProdFinEquiv (m := d) (n := n))
        (fun z => (lacSB (R:=R) d n ^ k) q z * lacSB (R:=R) d n z q')]
    rw [Fintype.sum_prod_type]
    simp only [lacSB, finProdFinEquiv_fst, finProdFinEquiv_snd, ih]
    have hinner : ∀ x : Fin d,
        (∑ y : Fin n,
          (if (q.divNat : ℕ) = (x:ℕ) + k ∧ q.modNat = y then (skewLaurentT : SkewL R) ^ k else 0) *
          (if (x:ℕ) = (q'.divNat : ℕ) + 1 ∧ y = q'.modNat then (skewLaurentT : SkewL R) else 0))
        = (if q.modNat = q'.modNat then
            (if (q.divNat : ℕ) = (x:ℕ)+k then (skewLaurentT : SkewL R) ^ k else 0) *
            (if (x:ℕ) = (q'.divNat : ℕ)+1 then (skewLaurentT : SkewL R) else 0)
          else 0) := by
      intro x
      have h1 : (∑ y : Fin n,
          (if (q.divNat : ℕ) = (x:ℕ) + k ∧ q.modNat = y then (skewLaurentT : SkewL R) ^ k else 0) *
          (if (x:ℕ) = (q'.divNat : ℕ) + 1 ∧ y = q'.modNat then (skewLaurentT : SkewL R) else 0))
        = (if (q.divNat : ℕ) = (x:ℕ) + k ∧ q.modNat = q'.modNat then (skewLaurentT : SkewL R) ^ k else 0) *
          (if (x:ℕ) = (q'.divNat : ℕ) + 1 ∧ q'.modNat = q'.modNat then (skewLaurentT : SkewL R) else 0) :=
        Finset.sum_eq_single q'.modNat (by intro y _ hy; simp [hy])
          (by intro hmem; exact absurd (Finset.mem_univ _) hmem)
      rw [h1]
      rw [show (if ((q.divNat : ℕ) = (x:ℕ) + k ∧ q.modNat = q'.modNat) then (skewLaurentT : SkewL R) ^ k else 0)
            = (if q.modNat = q'.modNat then (if ((q.divNat : ℕ) = (x:ℕ) + k) then (skewLaurentT : SkewL R) ^ k else 0) else 0)
          from lacand_ite_zero _ _ _]
      rw [show (if ((x:ℕ) = (q'.divNat : ℕ) + 1 ∧ q'.modNat = q'.modNat) then (skewLaurentT : SkewL R) else 0)
            = (if q'.modNat = q'.modNat then (if ((x:ℕ) = (q'.divNat : ℕ) + 1) then (skewLaurentT : SkewL R) else 0) else 0)
          from lacand_ite_zero _ _ _]
      rw [if_pos rfl]
      by_cases h : q.modNat = q'.modNat
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, zero_mul]
    have hsum : (∑ x : Fin d,
          (if (q.divNat : ℕ) = (x:ℕ)+k then (skewLaurentT : SkewL R) ^ k else 0) *
          (if (x:ℕ) = (q'.divNat : ℕ)+1 then (skewLaurentT : SkewL R) else 0))
        = if (q.divNat : ℕ) = (q'.divNat : ℕ)+(k+1) then (skewLaurentT : SkewL R) ^ (k+1) else 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun i =>
        (if (q.divNat : ℕ) = i+k then (skewLaurentT : SkewL R) ^ k else 0) *
        (if i = (q'.divNat : ℕ)+1 then (skewLaurentT : SkewL R) else 0)) d]
      rw [Finset.sum_eq_single ((q'.divNat : ℕ)+1)]
      · by_cases hc : (q.divNat : ℕ) = (q'.divNat : ℕ) + 1 + k
        · have hc' : (q.divNat : ℕ) = (q'.divNat : ℕ) + (k+1) := by omega
          rw [if_pos hc, if_pos rfl, if_pos hc', ← pow_succ]
        · have hc' : ¬ ((q.divNat : ℕ) = (q'.divNat : ℕ) + (k+1)) := by omega
          rw [if_neg hc, if_neg hc', zero_mul]
      · intro b _ hne
        rw [if_neg hne, mul_zero]
      · intro hmem
        have hmem' : d ≤ (q'.divNat : ℕ) + 1 := by
          simpa only [Finset.mem_range, not_lt] using hmem
        have hq : (q.divNat : ℕ) < d := q.divNat.isLt
        have hne : (q.divNat : ℕ) ≠ (q'.divNat : ℕ) + 1 + k := by omega
        rw [if_neg hne, zero_mul]
    rw [Finset.sum_congr rfl (fun x _ => hinner x)]
    rw [show (if ((q.divNat : ℕ) = (q'.divNat : ℕ)+(k+1) ∧ q.modNat = q'.modNat) then (skewLaurentT : SkewL R)^(k+1) else 0)
          = (if q.modNat = q'.modNat then (if ((q.divNat : ℕ) = (q'.divNat : ℕ)+(k+1)) then (skewLaurentT : SkewL R)^(k+1) else 0) else 0)
        from lacand_ite_zero _ _ _]
    by_cases h : q.modNat = q'.modNat
    · have hcong : (∑ x : Fin d, (if q.modNat = q'.modNat then (if (q.divNat : ℕ) = (x:ℕ)+k then (skewLaurentT : SkewL R) ^ k else 0) * (if (x:ℕ) = (q'.divNat : ℕ)+1 then (skewLaurentT : SkewL R) else 0) else 0))
            = (∑ x : Fin d, (if (q.divNat : ℕ) = (x:ℕ)+k then (skewLaurentT : SkewL R) ^ k else 0) * (if (x:ℕ) = (q'.divNat : ℕ)+1 then (skewLaurentT : SkewL R) else 0)) := by
        refine Finset.sum_congr rfl ?_
        intro x _
        rw [if_pos h]
      rw [hcong, if_pos h]
      exact hsum
    · have hcong : (∑ x : Fin d, (if q.modNat = q'.modNat then (if (q.divNat : ℕ) = (x:ℕ)+k then (skewLaurentT : SkewL R) ^ k else 0) * (if (x:ℕ) = (q'.divNat : ℕ)+1 then (skewLaurentT : SkewL R) else 0) else 0))
            = (∑ x : Fin d, (0 : SkewL R)) := by
        refine Finset.sum_congr rfl ?_
        intro x _
        rw [if_neg h]
      rw [hcong, if_neg h]
      simp


/-- `lacSB d n` is nilpotent, with `lacSB d n ^ d = 0`. -/
theorem lacSB_pow_eq_zero (d n : ℕ) : lacSB (R := R) d n ^ d = 0 := by
  ext q q'
  rw [Matrix.zero_apply, lacSB_pow_apply]
  rw [if_neg]
  rintro ⟨h1, -⟩
  have h2 : (q.divNat : ℕ) < d := q.divNat.isLt
  have h3 : (q'.divNat : ℕ) < d := q'.divNat.isLt
  omega

end

end Work.ORHughesFree.NaturalExtension
