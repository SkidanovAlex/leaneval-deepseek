import Mathlib

namespace Work.HP.MDEstimates

/-- Given a not-identically-zero rational vector `c`, there is a nonzero integer `N` and a nonzero
integer vector `a` with `a i = N * c i` for every `i`.  `N` is built as the product of the
denominators of the `c i`. -/
lemma ratDenClearVec (c : Fin 5 → ℚ) (hc : ∃ i, c i ≠ 0) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ a : Fin 5 → ℤ, a ≠ 0 ∧ ∀ i, (a i : ℚ) = (N : ℚ) * c i := by
  set N : ℤ := ∏ i, ((c i).den : ℤ) with hN
  set a : Fin 5 → ℤ := (fun i => (c i).num * ∏ j ∈ Finset.univ.erase i, ((c j).den : ℤ)) with hA
  have hNnz : N ≠ 0 := by
    rw [hN]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast (c i).den_nz)
  have hNcast : (N : ℚ) = ∏ j, ((c j).den : ℚ) := by
    rw [hN]; push_cast; rfl
  have hid : ∀ i, (a i : ℚ) = (N : ℚ) * c i := by
    intro i
    have hnum : ((c i).num : ℚ) = ((c i).den : ℚ) * c i := (Rat.den_mul_eq_num (c i)).symm
    have hprod : ((c i).den : ℚ) * ∏ j ∈ Finset.univ.erase i, ((c j).den : ℚ)
        = ∏ j, ((c j).den : ℚ) :=
      Finset.mul_prod_erase Finset.univ (fun j => ((c j).den : ℚ)) (Finset.mem_univ i)
    rw [hNcast]
    calc (a i : ℚ) = ((c i).num : ℚ) * ∏ j ∈ Finset.univ.erase i, ((c j).den : ℚ) := by
            simp only [hA, Int.cast_mul, Int.cast_prod, Int.cast_natCast]
      _ = (((c i).den : ℚ) * c i) * ∏ j ∈ Finset.univ.erase i, ((c j).den : ℚ) := by rw [hnum]
      _ = c i * (((c i).den : ℚ) * ∏ j ∈ Finset.univ.erase i, ((c j).den : ℚ)) := by ring
      _ = c i * ∏ j, ((c j).den : ℚ) := by rw [hprod]
      _ = (∏ j, ((c j).den : ℚ)) * c i := by ring
  have ha : a ≠ 0 := by
    obtain ⟨i, hi⟩ := hc
    intro hzero
    have h1 : (a i : ℚ) = 0 := by simp [hzero]
    rw [hid i] at h1
    have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hNnz
    exact (mul_ne_zero hNq hi) h1
  exact ⟨N, hNnz, a, ha, hid⟩

end Work.HP.MDEstimates
