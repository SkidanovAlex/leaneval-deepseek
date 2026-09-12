import Mathlib
import Submission.Commons.Lattice.Minkowski.wedge_norm_ge_prod_successiveMinimum

set_option linter.style.haveILetI false

namespace Commons.Lattice.Minkowski

theorem wedge_norm_ge_pow_of_successiveMinimum_le {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] {c : ℝ} (hc : 0 ≤ c) (h1 : c ≤ Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E) L 1) (w : Fin k → L) (hw : LinearIndependent ℤ w) : ∃ C : ℝ, 0 < C ∧ C * c ^ k ≤ ‖exteriorPower.ιMulti ℝ k (fun i => (w i : E))‖ := by
  classical
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  obtain ⟨C, hCpos, hbound⟩ := wedge_norm_ge_prod_successiveMinimum L w hw
  refine ⟨C, hCpos, ?_⟩
  have hkfin : k ≤ Module.finrank ℤ L := by
    have := hw.fintype_card_le_finrank (R := ℤ) (M := L)
    simpa using this
  have hpow : c ^ k ≤
      ∏ i : Fin k, Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E) L (i.val + 1) := by
    have hconst : c ^ k = ∏ _i : Fin k, c := by
      rw [Finset.prod_const]
      simp
    rw [hconst]
    refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
    · exact hc
    · have hm : 1 ≤ i.val + 1 := by omega
      have hmfin : i.val + 1 ≤ Module.finrank ℤ L := by have := i.isLt; omega
      exact le_trans h1 (Commons.Lattice.SuccessiveMinima.successiveMinimum_mono L hm hmfin)
  calc C * c ^ k
      ≤ C * (∏ i : Fin k, Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E) L (i.val + 1)) :=
        mul_le_mul_of_nonneg_left hpow (le_of_lt hCpos)
    _ ≤ ‖exteriorPower.ιMulti ℝ k (fun i => (w i : E))‖ := hbound

end Commons.Lattice.Minkowski
