import Submission.NBody.MarchalStdVarGeometry
import Submission.NBody.MarchalBumpIntegrable

/-!
# The bumped blow-up profile stays collision free (the good direction)

For a direction `δ` which is not parallel to any pair separation `s̄ i₀ - s̄ j` of the limit shape,
the bumped parabolic profile `q̄ + stdVarVec m k i₀ δ T` stays collision free inside the cluster:
the only pairs which change are those through `i₀`, and for them the standard variation provides a
component orthogonal to `δ` which the parabolic separation supplies.  This is the `hfnc2`
hypothesis of the transfer `tendsto_transfer_of_data`, discharged.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- The `i₀`-`j` separation of the bumped blow-up profile, with the standard variation. -/
lemma add_stdVarVec_sub (m : Fin N → ℝ) (k : Finset (Fin N)) {i₀ j : Fin N} (hi₀ : i₀ ∈ k)
    (hj : j ∈ k) (hjne : j ≠ i₀) (κ T t : ℝ) (sbar : EN E N) (δ : E) :
    (blowUpProfile κ sbar t + stdVarVec m k i₀ δ T t) i₀
        - (blowUpProfile κ sbar t + stdVarVec m k i₀ δ T t) j
      = (Real.sqrt κ * t ^ ((2:ℝ)/3)) • (sbar i₀ - sbar j) + stdVar δ T t := by
  have hblow : (blowUpProfile κ sbar t) i₀ - (blowUpProfile κ sbar t) j
      = (Real.sqrt κ * t ^ ((2:ℝ)/3)) • (sbar i₀ - sbar j) := by
    rw [blowUpProfile, PiLp.smul_apply, PiLp.smul_apply, smul_sub]
  have hv : (stdVarVec m k i₀ δ T t) i₀ - (stdVarVec m k i₀ δ T t) j = stdVar δ T t := by
    rw [stdVarVec, PiLp.smul_apply (fun _ : Fin N => E), PiLp.smul_apply (fun _ : Fin N => E),
      ← smul_sub, stdPertVec_sub_i₀ hi₀ hj hjne, stdVar]
  have h2 : (blowUpProfile κ sbar t + stdVarVec m k i₀ δ T t) i₀
      - (blowUpProfile κ sbar t + stdVarVec m k i₀ δ T t) j
      = ((blowUpProfile κ sbar t) i₀ - (blowUpProfile κ sbar t) j)
        + ((stdVarVec m k i₀ δ T t) i₀ - (stdVarVec m k i₀ δ T t) j) := by
    rw [PiLp.add_apply, PiLp.add_apply]
    abel
  rw [h2, hv, hblow]

/-- **The pair lower bound of the bumped profile.** -/
theorem norm_bumped_pair_ge (m : Fin N → ℝ) (k : Finset (Fin N)) {i₀ j : Fin N} (hi₀ : i₀ ∈ k)
    (hj : j ∈ k) (hjne : j ≠ i₀) {κ T t : ℝ} (hκ : 0 < κ) (sbar : EN E N) {δ : E}
    (hδ : δ ≠ 0) (ht : 0 ≤ t) :
    Real.sqrt (‖sbar i₀ - sbar j‖^2 - (inner ℝ (sbar i₀ - sbar j) δ)^2 / ‖δ‖^2)
        * (Real.sqrt κ * t ^ ((2:ℝ)/3))
      ≤ ‖(blowUpProfile κ sbar t + stdVarVec m k i₀ δ T t) i₀
          - (blowUpProfile κ sbar t + stdVarVec m k i₀ δ T t) j‖ := by
  rw [add_stdVarVec_sub m k hi₀ hj hjne]
  exact mul_sqrt_gap_le_norm_parabolic_add_stdVar (xi := sbar i₀ - sbar j) hδ
    (Real.sqrt_nonneg κ) ht

/-- **The bumped blow-up profile is collision free inside the cluster**, as soon as the direction is
not parallel to any pair separation of the limit shape. -/
theorem clusterNoColl_blowUpProfile_add_stdVarVec {m : Fin N → ℝ} {k : Finset (Fin N)}
    {i₀ : Fin N} (hi₀ : i₀ ∈ k) {κ T : ℝ} (hκ : 0 < κ) (sbar : EN E N) {δ : E} (hδ : δ ≠ 0)
    (hsbarnc : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → sbar i ≠ sbar j)
    (hgood : ∀ j ∈ k.erase i₀,
      (inner ℝ (sbar i₀ - sbar j) δ)^2 < ‖sbar i₀ - sbar j‖^2 * ‖δ‖^2) :
    ∀ t ∈ Set.Ioc (0:ℝ) T,
      ClusterNoColl k (blowUpProfile κ sbar t + stdVarVec m k i₀ δ T t) := by
  intro t ht i hi j hj hij hEq
  have ht0 : 0 < t := ht.1
  have htp : 0 < t ^ ((2:ℝ)/3) := Real.rpow_pos_of_pos ht0 _
  -- the pair lower bound for the pair `(a,c)` through `i₀`
  have hlower : ∀ c ∈ k.erase i₀,
      (blowUpProfile κ sbar t + stdVarVec m k i₀ δ T t) i₀
        - (blowUpProfile κ sbar t + stdVarVec m k i₀ δ T t) c ≠ 0 := by
    intro c hc
    obtain ⟨hc1, hc2⟩ := Finset.mem_erase.mp hc
    have hzj : 0 < ‖sbar i₀ - sbar c‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hsbarnc i₀ hi₀ c hc2 hc1.symm h)
    have hgap : 0 < ‖sbar i₀ - sbar c‖^2
        - (inner ℝ (sbar i₀ - sbar c) δ)^2 / ‖δ‖^2 := by
      have hd : 0 < ‖δ‖^2 := pow_pos (norm_pos_iff.mpr hδ) 2
      rw [sub_pos, div_lt_iff₀ hd]
      exact hgood c hc
    have hlb := norm_bumped_pair_ge m k hi₀ hc2 hc1 (T := T) hκ sbar hδ ht0.le
    have hpos : 0 < Real.sqrt (‖sbar i₀ - sbar c‖^2
        - (inner ℝ (sbar i₀ - sbar c) δ)^2 / ‖δ‖^2) * (Real.sqrt κ * t ^ ((2:ℝ)/3)) :=
      mul_pos (Real.sqrt_pos.mpr hgap) (mul_pos (Real.sqrt_pos.mpr hκ) htp)
    intro h0
    rw [h0, norm_zero] at hlb
    exact absurd hlb (not_le.mpr hpos)
  rcases eq_or_ne i i₀ with hii | hii
  · subst hii
    exact hlower j (Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩) (sub_eq_zero.mpr hEq)
  · rcases eq_or_ne j i₀ with hjj | hjj
    · subst hjj
      exact hlower i (Finset.mem_erase.mpr ⟨hii, hi⟩) (sub_eq_zero.mpr hEq.symm)
    · -- neither is `i₀`: the perturbation does not change the difference
      have hsub : (stdVarVec m k i₀ δ T t) i - (stdVarVec m k i₀ δ T t) j = 0 := by
        have h1 : (stdVarVec m k i₀ δ T t) i = stdCoef δ T t • ((stdPertVec m k i₀ δ) i) := by
          rw [stdVarVec, PiLp.smul_apply]
        have h2 : (stdVarVec m k i₀ δ T t) j = stdCoef δ T t • ((stdPertVec m k i₀ δ) j) := by
          rw [stdVarVec, PiLp.smul_apply]
        have h3 : (stdPertVec m k i₀ δ) i = (stdPertVec m k i₀ δ) j :=
          stdPertVec_sub_of_notMem hi hj hii hjj δ
        rw [h1, h2, h3, sub_self]
      have hkey : (blowUpProfile κ sbar t) i - (blowUpProfile κ sbar t) j = 0 := by
        have hsplit : (blowUpProfile κ sbar t + stdVarVec m k i₀ δ T t) i
            - (blowUpProfile κ sbar t + stdVarVec m k i₀ δ T t) j
            = ((blowUpProfile κ sbar t) i - (blowUpProfile κ sbar t) j)
              + ((stdVarVec m k i₀ δ T t) i - (stdVarVec m k i₀ δ T t) j) := by
          rw [PiLp.add_apply, PiLp.add_apply]
          abel
        have h0 : (blowUpProfile κ sbar t) i - (blowUpProfile κ sbar t) j
            + ((stdVarVec m k i₀ δ T t) i - (stdVarVec m k i₀ δ T t) j) = 0 := by
          rw [← hsplit]; exact sub_eq_zero.mpr hEq
        rw [hsub, add_zero] at h0
        exact h0
      have hblow : (blowUpProfile κ sbar t) i - (blowUpProfile κ sbar t) j
          = (√κ * t ^ ((2:ℝ)/3)) • (sbar i - sbar j) := by
        rw [blowUpProfile, PiLp.smul_apply, PiLp.smul_apply, smul_sub]
      have h1 : (√κ * t ^ ((2:ℝ)/3)) • sbar i = (√κ * t ^ ((2:ℝ)/3)) • sbar j := by
        have h2 : (√κ * t ^ ((2:ℝ)/3)) • (sbar i - sbar j) = 0 := by
          rw [← hblow]; exact hkey
        have h3 : (√κ * t ^ ((2:ℝ)/3)) • sbar i
            - (√κ * t ^ ((2:ℝ)/3)) • sbar j = 0 := by
          rw [← smul_sub]; exact h2
        exact sub_eq_zero.mp h3
      have hc : (√κ * t ^ ((2:ℝ)/3)) ≠ 0 :=
        mul_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hκ)) (ne_of_gt htp)
      exact hsbarnc i hi j hj hij (smul_right_injective E hc h1)

end Submission.NBody
