import Mathlib.Analysis.Normed.Ring.Lemmas

open scoped BigOperators

set_option autoImplicit false

namespace Commons.Lattice.Counting

/-- Clearing denominators: for any finite family of rationals there is a nonzero integer
`a` such that multiplication by `(a : ℚ)` makes every family member an integer. -/
private lemma exists_int_scaling_of_rat_family {ι : Type*} [Fintype ι] (c : ι → ℚ) :
    ∃ a : ℤ, a ≠ 0 ∧ ∃ d : ι → ℤ, ∀ i, (a : ℚ) * c i = (d i : ℚ) := by
  classical
  let denZ : ι → ℤ := fun j => ((c j).den : ℤ)
  let BZ : ℤ := ∏ i : ι, denZ i
  let a : ℤ := BZ
  let d : ι → ℤ := fun i => (c i).num * ((Finset.univ.erase i).prod denZ)
  refine ⟨a, ?_, d, ?_⟩
  · dsimp [a, BZ, denZ]
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => by exact_mod_cast Rat.den_nz (c i))
  · intro i
    dsimp [a, d]
    have hEr : ((Finset.univ.erase i).prod denZ) * ((c i).den : ℤ) = BZ := by
      simpa [BZ, denZ] using (Finset.prod_erase_mul Finset.univ denZ (a := i) (by simp))
    have hc : (((c i).den : ℤ) : ℚ) * c i = ((c i).num : ℚ) := by
      rw [Int.cast_natCast]
      rw [mul_comm]
      exact Rat.mul_den_eq_num (c i)
    have hErq : (BZ : ℚ) = (((Finset.univ.erase i).prod denZ : ℤ) : ℚ) * (((c i).den : ℤ) : ℚ) := by
      rw [← hEr]
      norm_num
    rw [Int.cast_mul]
    rw [hErq]
    rw [mul_assoc]
    rw [hc]
    ring

theorem mem_sat_iff_mem_qspan {n r : ℕ} (w : Fin r → Fin n → ℤ) (x : Fin n → ℤ) :
    (∃ a : ℤ, a ≠ 0 ∧ a • x ∈ Submodule.span ℤ (Set.range w)) ↔
      (fun i : Fin n => (x i : ℚ)) ∈
        Submodule.span ℚ (Set.range (fun j : Fin r => fun i : Fin n => (w j i : ℚ))) := by
  constructor
  · -- integer multiple in the integer span implies membership in the rational span
    rintro ⟨a, ha, hmem⟩
    rw [Submodule.mem_span_range_iff_exists_fun (R := ℚ)
      (v := (fun j : Fin r => fun i : Fin n => (w j i : ℚ)))
      (x := (fun i : Fin n => (x i : ℚ)))]
    rcases (Submodule.mem_span_range_iff_exists_fun (R := ℤ) (v := w) (x := a • x)).mp hmem with ⟨d, hd⟩
    refine ⟨fun j : Fin r => (d j : ℚ) / (a : ℚ), ?_⟩
    ext i
    calc
      ((∑ j : Fin r, ((d j : ℚ) / (a : ℚ)) • (fun i : Fin n => (w j i : ℚ))) i)
          = ∑ j : Fin r, ((d j : ℚ) / (a : ℚ)) * (w j i : ℚ) := by
        simp [Finset.sum_apply]
      _ = (a : ℚ)⁻¹ * (∑ j : Fin r, (d j : ℚ) * (w j i : ℚ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [div_eq_mul_inv]
        ring
      _ = (x i : ℚ) := by
        have hstep : (∑ j : Fin r, (d j : ℚ) * (w j i : ℚ)) = (a : ℚ) * (x i : ℚ) := by
          have hz : (∑ j : Fin r, d j * w j i : ℤ) = a * x i := by
            have := congr_fun hd i
            simpa [Finset.sum_apply] using this
          have hcast := congrArg (fun t : ℤ => (t : ℚ)) hz
          simpa [Finset.sum_apply] using hcast
        rw [hstep]
        field_simp [show ((a : ℚ) ≠ 0) from by exact_mod_cast ha]

  · -- membership in the rational span gives a nonzero integer multiple in the integer span
    intro hq
    rcases (Submodule.mem_span_range_iff_exists_fun (R := ℚ)
      (v := (fun j : Fin r => fun i : Fin n => (w j i : ℚ)))
      (x := (fun i : Fin n => (x i : ℚ)))).mp hq with ⟨c, hc⟩
    rcases exists_int_scaling_of_rat_family c with ⟨a, ha, d, hd⟩
    refine ⟨a, ha, ?_⟩
    rw [Submodule.mem_span_range_iff_exists_fun (R := ℤ) (v := w) (x := a • x)]
    refine ⟨d, ?_⟩
    ext i
    apply Int.cast_injective (α := ℚ)
    calc
      (((∑ j : Fin r, d j • w j) i) : ℚ) = ∑ j : Fin r, (d j : ℚ) * (w j i : ℚ) := by
        simp [Finset.sum_apply]
      _ = ∑ j : Fin r, (a : ℚ) * c j * (w j i : ℚ) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← hd j]
      _ = (a : ℚ) * (∑ j : Fin r, c j * (w j i : ℚ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (a : ℚ) * (x i : ℚ) := by
        congr 1
        have := congr_fun hc i
        simpa using this
      _ = ((a • x) i : ℚ) := by
        simp

end Commons.Lattice.Counting