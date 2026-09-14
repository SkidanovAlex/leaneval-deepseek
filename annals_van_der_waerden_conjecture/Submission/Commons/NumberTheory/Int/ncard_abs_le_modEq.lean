import Submission.Commons.NumberTheory.Int.ncard_int_residue_class_sq_le

namespace Commons.NumberTheory.Int

theorem ncard_abs_le_modEq (B M : ℕ) (hM : 1 ≤ M) (r : ℤ) :
    (({a : ℤ | |a| ≤ (B : ℤ) ∧ Int.ModEq (M : ℤ) a r} : Set ℤ).ncard : ℝ)
      ≤ 2 * (B : ℝ) / (M : ℝ) + 1 := by
  classical
  set S : Set ℤ := {a : ℤ | |a| ≤ (B : ℤ) ∧ Int.ModEq (M : ℤ) a r} with hS
  have hsub : S ⊆ (Finset.Icc (-(B : ℤ)) (B : ℤ) : Set ℤ) := by
    intro a ha
    rw [hS] at ha
    rw [Finset.mem_coe, Finset.mem_Icc]
    exact abs_le.mp ha.1
  have hSfin : S.Finite := Set.Finite.subset (Finset.finite_toSet _) hsub
  have hcount := card_le_of_modEq_abs_le (d := M) hM (s := hSfin.toFinset) (r := r)
      (A := (B : ℝ)) (by positivity)
      (fun a ha => by
        have h := (hSfin.mem_toFinset.mp ha)
        rw [hS] at h
        exact h.2)
      (fun a ha => by
        have h := (hSfin.mem_toFinset.mp ha)
        rw [hS] at h
        have h1 : |a| ≤ (B : ℤ) := h.1
        have h2 : ((|a| : ℤ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast h1
        rwa [Int.cast_abs] at h2)
  change (S.ncard : ℝ) ≤ 2 * (B : ℝ) / (M : ℝ) + 1
  rw [Set.ncard_eq_toFinset_card S hSfin]
  exact hcount

end Commons.NumberTheory.Int
