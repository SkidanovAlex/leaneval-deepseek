import Mathlib
import Submission.Work.TMComp.IDSDefs

namespace Work.TMComp.IDSBox

theorem jbox_apply (α lam θ E : ℝ) {R : ℕ} (φ : ℤ → ℂ)
    (hsupp : ∀ m : ℤ, R ≤ m.natAbs → φ m = 0)
    (j : ℤ) (n : ℕ) (hj : (R : ℤ) ≤ j + 1) (hj2 : j + (R : ℤ) + 1 ≤ (n : ℤ))
    (k : Fin n) :
    (Matrix.mulVec (Work.TMComp.Jbox α lam θ n) (Work.TMComp.shiftVec φ j n)) k
        - (E : ℂ) * Work.TMComp.shiftVec φ j n k
      = (Work.TMContract.amoAct α lam 0 φ ((k : ℤ) - j) - (E : ℂ) * φ ((k : ℤ) - j))
        + ((Work.TMContract.amoPot α lam θ (k : ℤ) - Work.TMContract.amoPot α lam 0 ((k : ℤ) - j) : ℝ) : ℂ)
            * φ ((k : ℤ) - j) := by
  have key : (Matrix.mulVec (Work.TMComp.Jbox α lam θ n) (Work.TMComp.shiftVec φ j n)) k
      = ((Work.TMContract.amoPot α lam θ (k:ℤ) : ℝ) : ℂ) * φ ((k:ℤ) - j)
        + φ ((k:ℤ) + 1 - j) + φ ((k:ℤ) - 1 - j) := by
    rw [Matrix.mulVec, dotProduct]
    simp only [Work.TMComp.Jbox, Work.TMComp.shiftVec, Work.TMComp.pot_eq_amoPot]
    have hpoint : ∀ i : Fin n,
        (if k = i then ((Work.TMContract.amoPot α lam θ (k:ℤ) : ℝ) : ℂ)
            else if (k:ℕ)+1 = (i:ℕ) ∨ (i:ℕ)+1 = (k:ℕ) then 1 else 0) * φ ((i:ℤ) - j)
        = (if k = i then ((Work.TMContract.amoPot α lam θ (k:ℤ) : ℝ) : ℂ) else 0) * φ ((i:ℤ) - j)
          + (if (k:ℕ)+1 = (i:ℕ) then (1:ℂ) else 0) * φ ((i:ℤ) - j)
          + (if (i:ℕ)+1 = (k:ℕ) then (1:ℂ) else 0) * φ ((i:ℤ) - j) := by
      intro i
      by_cases hki : k = i
      · subst hki
        simp
      · simp only [if_neg hki]
        by_cases hQ : (k:ℕ)+1 = (i:ℕ)
        · have hQ' : ¬ ((i:ℕ)+1 = (k:ℕ)) := by omega
          rw [if_pos (Or.inl hQ), if_pos hQ, if_neg hQ']
          ring
        · by_cases hQ' : (i:ℕ)+1 = (k:ℕ)
          · rw [if_pos (Or.inr hQ'), if_neg hQ, if_pos hQ']
            ring
          · rw [if_neg (by tauto), if_neg hQ, if_neg hQ']
            ring
    have h1 : (∑ i : Fin n, (if k = i then ((Work.TMContract.amoPot α lam θ (k:ℤ) : ℝ) : ℂ) else 0) * φ ((i:ℤ) - j))
        = ((Work.TMContract.amoPot α lam θ (k:ℤ) : ℝ) : ℂ) * φ ((k:ℤ) - j) := by
      rw [show (∑ i : Fin n, (if k = i then ((Work.TMContract.amoPot α lam θ (k:ℤ) : ℝ) : ℂ) else 0) * φ ((i:ℤ) - j))
          = ∑ i : Fin n, (if k = i then ((Work.TMContract.amoPot α lam θ (k:ℤ) : ℝ) : ℂ) * φ ((i:ℤ) - j) else 0)
          from Finset.sum_congr rfl (fun i _ => by simp only [ite_mul, zero_mul])]
      rw [Finset.sum_ite_eq]
      simp
    have h2 : (∑ i : Fin n, (if (k:ℕ)+1 = (i:ℕ) then (1:ℂ) else 0) * φ ((i:ℤ) - j))
        = φ ((k:ℤ) + 1 - j) := by
      by_cases hk1 : (k:ℕ) + 1 < n
      · have hsum : (∑ i : Fin n, (if (k:ℕ)+1 = (i:ℕ) then (1:ℂ) else 0) * φ ((i:ℤ) - j))
            = (if (k:ℕ)+1 = ((⟨(k:ℕ)+1, hk1⟩ : Fin n):ℕ) then (1:ℂ) else 0)
                * φ (((⟨(k:ℕ)+1, hk1⟩ : Fin n):ℤ) - j) :=
          Finset.sum_eq_single_of_mem (⟨(k:ℕ)+1, hk1⟩ : Fin n) (Finset.mem_univ _)
            (fun b _ hb => by
              have hb' : ¬ ((b:ℕ) = (k:ℕ)+1) := fun h => hb (Fin.ext (by exact h))
              rw [if_neg (Ne.symm hb'), zero_mul])
        rw [hsum, if_pos rfl, one_mul]
        congr 1
        all_goals (push_cast; ring)
      · have hsum0 : (∑ i : Fin n, (if (k:ℕ)+1 = (i:ℕ) then (1:ℂ) else 0) * φ ((i:ℤ) - j)) = 0 := by
          rw [Finset.sum_eq_zero]
          intro i _
          have : ¬ ((k:ℕ)+1 = (i:ℕ)) := by have := i.isLt; omega
          rw [if_neg this, zero_mul]
        have hphi0 : φ ((k:ℤ) + 1 - j) = 0 := by
          have hkn : (k:ℕ) + 1 = n := by have := k.isLt; omega
          have hkz : (k:ℤ) + 1 = (n:ℤ) := by omega
          rw [hkz]
          apply hsupp
          have hle1 : (R:ℤ) ≤ (n:ℤ) - j := by omega
          have hle2 : (R:ℤ) ≤ ((((n:ℤ)-j).natAbs : ℕ) : ℤ) := le_trans hle1 Int.le_natAbs
          exact_mod_cast hle2
        rw [hsum0, hphi0]
    have h3 : (∑ i : Fin n, (if (i:ℕ)+1 = (k:ℕ) then (1:ℂ) else 0) * φ ((i:ℤ) - j))
        = φ ((k:ℤ) - 1 - j) := by
      by_cases hk0 : 0 < (k:ℕ)
      · have hsum : (∑ i : Fin n, (if (i:ℕ)+1 = (k:ℕ) then (1:ℂ) else 0) * φ ((i:ℤ) - j))
            = (if ((⟨(k:ℕ)-1, by omega⟩ : Fin n):ℕ)+1 = (k:ℕ) then (1:ℂ) else 0)
                * φ (((⟨(k:ℕ)-1, by omega⟩ : Fin n):ℤ) - j) :=
          Finset.sum_eq_single_of_mem (⟨(k:ℕ)-1, by omega⟩ : Fin n) (Finset.mem_univ _)
            (fun b _ hb => by
              have hb' : ¬ ((b:ℕ)+1 = (k:ℕ)) := fun h => hb (Fin.ext (by show (b:ℕ) = (k:ℕ)-1; omega))
              rw [if_neg hb', zero_mul])
        rw [hsum, if_pos (by show (k:ℕ)-1+1 = (k:ℕ); omega), one_mul]
        congr 1
        have hcast : ((↑((k:ℕ)-1) : ℤ)) = (k:ℤ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ (k:ℕ)), Nat.cast_one]
        rw [hcast]
      · have hsum0 : (∑ i : Fin n, (if (i:ℕ)+1 = (k:ℕ) then (1:ℂ) else 0) * φ ((i:ℤ) - j)) = 0 := by
          rw [Finset.sum_eq_zero]
          intro i _
          have : ¬ ((i:ℕ)+1 = (k:ℕ)) := by omega
          rw [if_neg this, zero_mul]
        have hphi0 : φ ((k:ℤ) - 1 - j) = 0 := by
          have hkz : (k:ℤ) = 0 := by omega
          rw [hkz]
          apply hsupp
          have hle1 : (R:ℤ) ≤ (1:ℤ) + j := by omega
          have hle2 : ((1:ℤ)+j) ≤ ((((1:ℤ)+j).natAbs : ℕ) : ℤ) := Int.le_natAbs
          have hR : R ≤ ((1:ℤ)+j).natAbs := by exact_mod_cast (le_trans hle1 hle2)
          have hnat : ((0:ℤ) - 1 - j).natAbs = ((1:ℤ)+j).natAbs := by
            rw [show (0:ℤ) - 1 - j = -((1:ℤ)+j) from by ring, Int.natAbs_neg]
          rw [hnat]; exact hR
        rw [hsum0, hphi0]
    rw [show (∑ i : Fin n, (if k = i then ((Work.TMContract.amoPot α lam θ (k:ℤ) : ℝ) : ℂ)
              else if (k:ℕ)+1 = (i:ℕ) ∨ (i:ℕ)+1 = (k:ℕ) then 1 else 0) * φ ((i:ℤ) - j))
        = ∑ i : Fin n, ((if k = i then ((Work.TMContract.amoPot α lam θ (k:ℤ) : ℝ) : ℂ) else 0) * φ ((i:ℤ) - j)
            + (if (k:ℕ)+1 = (i:ℕ) then (1:ℂ) else 0) * φ ((i:ℤ) - j)
            + (if (i:ℕ)+1 = (k:ℕ) then (1:ℂ) else 0) * φ ((i:ℤ) - j))
        from Finset.sum_congr rfl (fun i _ => hpoint i)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2, h3]
  rw [key]
  simp only [Work.TMContract.amoAct, Work.TMComp.shiftVec]
  rw [show (k:ℤ) - j + 1 = (k:ℤ) + 1 - j from by ring,
      show (k:ℤ) - j - 1 = (k:ℤ) - 1 - j from by ring,
      Complex.ofReal_sub]
  ring

end Work.TMComp.IDSBox
