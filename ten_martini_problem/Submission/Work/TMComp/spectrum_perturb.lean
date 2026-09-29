import Mathlib
import Submission.Work.TMC7Core.Scale.spectral_continuity

/-!
# Perturbation of the spectrum of self-adjoint operators

If `A` and `B` are bounded self-adjoint operators on a complex Hilbert space and
`z` lies in the spectrum of `A`, then the spectrum of `B` has a point within
`γ` of `z` whenever `‖A - B‖ < γ`.

The proof is the classical resolvent argument.  Writing `δ = ‖A - B‖`, suppose
towards a contradiction that the spectrum of `B` stays at distance `> γ` from
`z`.  Then `z ∉ spectrum B`, so `T := z - B` is invertible, and the resolvent
bound `‖T⁻¹‖ ≤ γ⁻¹` (obtained from
`Work.TMC7Core.Scale.norm_le_of_spectrum_avoid`, which for a self-adjoint
operator turns a spectral gap of size `γ` into the lower bound
`γ ‖u‖ ≤ ‖(B - z) u‖`) gives `‖T⁻¹ (B - A)‖ ≤ γ⁻¹ δ < 1`.  Hence
`z - A = T (1 + T⁻¹ (B - A))` is invertible by a Neumann series, contradicting
`z ∈ spectrum A`.

The argument does not use self-adjointness of `A` beyond the fact that its
spectrum is real, but the statement provides both hypotheses.
-/

namespace Work.TMComp

set_option linter.style.haveILetI false

theorem spectrum_perturb {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A B : E →L[ℂ] E) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) {z : ℂ}
    (hz : z ∈ spectrum ℂ A) {γ : ℝ} (hγ : ‖A - B‖ < γ) :
    ∃ z' ∈ spectrum ℂ B, ‖z - z'‖ ≤ γ := by
  by_cases hnt : Nontrivial E
  · haveI : Nontrivial E := hnt
    have hγpos : 0 < γ := lt_of_le_of_lt (norm_nonneg _) hγ
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    -- The spectral point `z` of a self-adjoint operator is real.
    have hzre : z = ((z.re : ℝ) : ℂ) := hA.mem_spectrum_eq_re hz
    -- `z` itself is not in the spectrum of `B`.
    have hzB : z ∉ spectrum ℂ B := by
      intro hmem
      have h := hcon z hmem
      rw [sub_self, norm_zero] at h
      linarith
    -- The spectrum of `B` avoids the closed ball of radius `γ` around `z`.
    have hspecB : ∀ w ∈ spectrum ℂ B, γ ≤ ‖w - ((z.re : ℝ) : ℂ)‖ := by
      intro w hw
      have h := hcon w hw
      have h2 : ‖w - ((z.re : ℝ) : ℂ)‖ = ‖z - w‖ := by
        rw [← hzre, norm_sub_rev]
      rw [h2]
      exact le_of_lt h
    have halg : algebraMap ℂ (E →L[ℂ] E) z = algebraMap ℂ (E →L[ℂ] E) ↑z.re :=
      congrArg (algebraMap ℂ (E →L[ℂ] E)) hzre
    -- Resolvent / spectral gap bound: `γ ‖u‖ ≤ ‖(B - z) u‖`.
    have hboundz : ∀ u : E, γ * ‖u‖ ≤ ‖(B - algebraMap ℂ (E →L[ℂ] E) z) u‖ := by
      intro u
      have h := Work.TMC7Core.Scale.norm_le_of_spectrum_avoid B hB z.re hγpos hspecB u
      rw [← halg] at h
      exact h
    set T : E →L[ℂ] E := algebraMap ℂ (E →L[ℂ] E) z - B with hT
    have hunitT : IsUnit T := by rw [hT]; exact (spectrum.notMem_iff).mp hzB
    set V : E →L[ℂ] E := Ring.inverse T with hV
    have hTV : T * V = 1 := by rw [hV]; exact Ring.mul_inverse_cancel T hunitT
    -- `‖T⁻¹‖ ≤ γ⁻¹`.
    have hVnorm : ‖V‖ ≤ γ⁻¹ := by
      refine ContinuousLinearMap.opNorm_le_bound V (by positivity) (fun u => ?_)
      have hTu : T (V u) = u := by
        rw [← mul_apply_eq_comp, hTV, one_apply_eq_self]
      have h2 : γ * ‖V u‖ ≤ ‖(B - algebraMap ℂ (E →L[ℂ] E) z) (V u)‖ := hboundz (V u)
      have hneg : B - algebraMap ℂ (E →L[ℂ] E) z = -T := by rw [hT]; abel
      rw [hneg, neg_apply, hTu, norm_neg] at h2
      rw [inv_mul_eq_div]
      refine (le_div_iff₀ hγpos).mpr ?_
      rw [mul_comm ‖V u‖ γ]
      exact h2
    -- The Neumann correction is a contraction.
    have hSnorm : ‖V * (B - A)‖ < 1 := by
      have h2 : ‖B - A‖ = ‖A - B‖ := norm_sub_rev B A
      calc ‖V * (B - A)‖ ≤ ‖V‖ * ‖B - A‖ := norm_mul_le V (B - A)
        _ = ‖V‖ * ‖A - B‖ := by rw [h2]
        _ ≤ γ⁻¹ * ‖A - B‖ := mul_le_mul_of_nonneg_right hVnorm (norm_nonneg _)
        _ < γ⁻¹ * γ := mul_lt_mul_of_pos_left hγ (inv_pos.mpr hγpos)
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hγpos)
    have hunit1 : IsUnit (1 + V * (B - A)) := by
      have hlt : ‖-(V * (B - A))‖ < 1 := by rwa [norm_neg]
      have hu := (Units.oneSub (-(V * (B - A))) hlt).isUnit
      rw [Units.val_oneSub, sub_neg_eq_add] at hu
      exact hu
    have hTA : algebraMap ℂ (E →L[ℂ] E) z - A = T * (1 + V * (B - A)) := by
      have h1 : T * (1 + V * (B - A)) = T + (B - A) := by
        rw [mul_add, mul_one, ← mul_assoc, hTV, one_mul]
      rw [h1, hT]; abel
    have hunitA : IsUnit (algebraMap ℂ (E →L[ℂ] E) z - A) := by
      rw [hTA]; exact hunitT.mul hunit1
    exact (spectrum.mem_iff).mp hz hunitA
  · -- In the trivial space the spectrum is empty, so `hz` is impossible.
    haveI : Subsingleton E := not_nontrivial_iff_subsingleton.mp hnt
    haveI : Subsingleton (E →L[ℂ] E) := inferInstance
    rw [spectrum.of_subsingleton A] at hz
    exact absurd hz (Set.notMem_empty z)

end Work.TMComp
