import Mathlib
import Submission.GeometryOfNumbers.SuccessiveMinima
import Submission.Commons.Lattice.FundamentalDomain.submodule_toAddSubgroup_fundamentalDomain
import Submission.Commons.Lattice.Minkowski.first_minimum_le_of_covolume

/-!
# Minkowski's first theorem for the first successive minimum

A Mathlib-only corollary of Mathlib's Minkowski convex body theorem
(`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure`)
stated in terms of the successive minima defined in `SuccessiveMinima`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Submission.GeometryOfNumbers

variable {n : ℕ}
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/-- **Minkowski's first theorem** for the first successive minimum of a full lattice in
`EuclideanSpace ℝ (Fin n)`: if the ball of radius `R` has volume at least `2^n` times the
volume of a fundamental domain of the lattice, then the ball contains a nonzero lattice point. -/
lemma exists_ne_zero_mem_closedBall_of_covolume_le
    (L : Submodule ℤ Eₙ) [DiscreteTopology L] [IsZLattice ℝ L]
    (hE : Nontrivial Eₙ) {R : ℝ} (hR : 0 ≤ R)
    (hvol : volume (ZSpan.fundamentalDomain (Module.Basis.ofZLatticeBasis ℝ L (Module.finBasis ℤ L))) *
        (2 : ℝ≥0∞) ^ Module.finrank ℝ Eₙ ≤ volume (Metric.closedBall (0 : Eₙ) R)) :
    ∃ v : L, v ≠ 0 ∧ ‖(v : Eₙ)‖ ≤ R := by
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  haveI : Countable L := instCountable_of_discrete_submodule L
  haveI : Countable L.toAddSubgroup := by
    -- the underlying types of `L` and `L.toAddSubgroup` agree; transport the countable instance
    let e : L ≃+ L.toAddSubgroup := {
      toFun := fun x => ⟨x.1, by simpa [Submodule.coe_toAddSubgroup] using x.2⟩
      invFun := fun x => ⟨x.1, by simpa [Submodule.coe_toAddSubgroup] using x.2⟩
      left_inv := by intro x; ext; rfl
      right_inv := by intro x; ext; rfl
      map_add' := by intro x y; ext; rfl }
    exact Countable.of_equiv L e.symm.toEquiv
  let b : Module.Basis (Fin (Module.finrank ℤ L)) ℤ L := Module.finBasis ℤ L
  let F : Set Eₙ := ZSpan.fundamentalDomain (Module.Basis.ofZLatticeBasis ℝ L b)
  have hfundL : IsAddFundamentalDomain L F volume := by
    simpa [F] using ZLattice.isAddFundamentalDomain (L := L) b volume
  have hfund : IsAddFundamentalDomain L.toAddSubgroup F volume :=
    Commons.Lattice.FundamentalDomain.submodule_toAddSubgroup_fundamentalDomain L hfundL
  obtain ⟨x, hx0, hxmem⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (L := L.toAddSubgroup) (μ := volume) hfund
    (by intro x hx; simpa [Metric.mem_closedBall, dist_eq_norm, norm_neg] using hx)
    (convex_closedBall (0 : Eₙ) R) (isCompact_closedBall (0 : Eₙ) R) hvol
  let v : L := ⟨x.1, by simpa [Submodule.coe_toAddSubgroup] using x.2⟩
  have hv0 : v ≠ 0 := by
    intro hv
    apply hx0
    apply Subtype.ext
    exact congrArg Subtype.val hv
  refine ⟨v, hv0, ?_⟩
  · have hvmem : ((v : L) : Eₙ) ∈ Metric.closedBall (0 : Eₙ) R := by
      simpa [v, Metric.mem_closedBall, dist_eq_norm] using hxmem
    simpa [Metric.mem_closedBall, dist_eq_norm] using hvmem

/-- Consequence for the first successive minimum: `λ₁(L) ≤ R`. -/
lemma first_successiveMinimum_le_of_covolume_le
    (L : Submodule ℤ Eₙ) [DiscreteTopology L] [IsZLattice ℝ L]
    (hE : Nontrivial Eₙ) {R : ℝ} (hR : 0 ≤ R)
    (hvol : volume (ZSpan.fundamentalDomain (Module.Basis.ofZLatticeBasis ℝ L (Module.finBasis ℤ L))) *
        (2 : ℝ≥0∞) ^ Module.finrank ℝ Eₙ ≤ volume (Metric.closedBall (0 : Eₙ) R)) :
    Submission.SuccessiveMinima.successiveMinimum L 1 ≤ R := by
  obtain ⟨v, hv0, hvnorm⟩ := exists_ne_zero_mem_closedBall_of_covolume_le L hE hR hvol
  have hvE : (v : Eₙ) ≠ 0 := by
    intro h
    apply hv0
    apply Subtype.ext
    exact h
  haveI : Module.IsTorsionFree ℤ Eₙ := by
    refine Module.IsTorsionFree.of_smul_eq_zero (R := ℤ) (M := Eₙ) ?_
    intro z m hm
    rw [← Int.cast_smul_eq_zsmul ℝ z m] at hm
    rcases (smul_eq_zero.mp hm) with hz | hm
    · exact Or.inl (Int.cast_eq_zero.mp hz)
    · exact Or.inr hm
  exact Submission.SuccessiveMinima.successiveMinimum_le_of_exists L 1 hR
    (fun _ : Fin 1 => v) (LinearIndependent.of_subsingleton (i := 0) hvE)
    (by intro j; simpa using hvnorm)

end Submission.GeometryOfNumbers

section CovolumeForm

variable {n : ℕ}
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

open scoped ENNReal

/-- Minkowski's first theorem, in the classical covolume form: if `R` is large enough that
`covolume L * 2^n ≤ volume (ball R)`, then `λ₁(L) ≤ R`. -/
lemma first_successiveMinimum_le_of_covolume
    (L : Submodule ℤ Eₙ) [DiscreteTopology L] [IsZLattice ℝ L]
    (hE : Nontrivial Eₙ) {R : ℝ} (hR : 0 ≤ R)
    (hvol : ENNReal.ofReal (ZLattice.covolume L) *
        (2 : ℝ≥0∞) ^ Module.finrank ℝ Eₙ ≤ volume (Metric.closedBall (0 : Eₙ) R)) :
    Submission.SuccessiveMinima.successiveMinimum L 1 ≤ R := by
  haveI : Module.IsTorsionFree ℤ Eₙ := by
    refine Module.IsTorsionFree.of_smul_eq_zero (R := ℤ) (M := Eₙ) ?_
    intro z m hm
    rw [← Int.cast_smul_eq_zsmul ℝ z m] at hm
    rcases (smul_eq_zero.mp hm) with hz | hm
    · exact Or.inl (Int.cast_eq_zero.mp hz)
    · exact Or.inr hm
  obtain ⟨v, hv0, hvnorm⟩ :=
    Commons.Lattice.Minkowski.first_minimum_le_of_covolume (n := n) hE L hR hvol
  have hvE : (v : Eₙ) ≠ 0 := by
    intro h
    apply hv0
    apply Subtype.ext
    exact h
  exact Submission.SuccessiveMinima.successiveMinimum_le_of_exists L 1 hR
    (fun _ : Fin 1 => v) (LinearIndependent.of_subsingleton (i := 0) hvE)
    (by intro j; simpa using hvnorm)

end CovolumeForm
