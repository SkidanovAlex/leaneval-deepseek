import Submission.NBody.MarchalTransferLimit
import Submission.NBody.MarchalSeqBlowUp

/-!
# The transfer to the blow-up limit, sequential form

`tendsto_transfer_of_data` (`MarchalTransferLimit.lean`) is stated for a general filter `l`, but its
pointwise-convergence hypotheses `hconv`, `hconvd` are genuine `nhdsWithin 0 (Ioi 0)`-limits of the
family `λ ↦ q^λ`, which are *not* available (see the SESSION 39 section of `Submission/ROADMAP.md`:
the normalised configuration has no genuine limit).  The sequential form below takes the
pointwise convergence along the sequence `λ_n` instead and concludes the convergence of the
integrals along `atTop`.  The proof is the same: `tendsto_intervalIntegral_of_dominated` is stated
for an arbitrary filter.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The transfer to the blow-up limit, sequential form (FT `propo:blowup`).** -/
theorem tendsto_transfer_of_data_seq {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {κ T : ℝ} {sbar : EN E N} {f f' : ℝ → EN E N} {lam : ℕ → ℝ}
    (hm : ∀ i, 0 < m i) (hκ : 0 < κ) (hT : 0 < T)
    (hsbarnc : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → sbar i ≠ sbar j)
    (hconv : ∀ t ∈ Ioc (0:ℝ) T, Tendsto (fun n => rescaledCentered m k x (lam n) t)
      atTop (nhds (blowUpProfile κ sbar t)))
    (hconvd : ∀ t ∈ Ioc (0:ℝ) T, Tendsto (fun n => deriv (rescaledCentered m k x (lam n)) t)
      atTop (nhds (deriv (blowUpProfile κ sbar) t)))
    (hmeasq : ∀ᶠ n in atTop,
      AEStronglyMeasurable (rescaledCentered m k x (lam n)) (volume.restrict (Ioc (0:ℝ) T)))
    (hmeasf : AEStronglyMeasurable f (volume.restrict (Ioc (0:ℝ) T)))
    (hmeasf' : AEStronglyMeasurable f' (volume.restrict (Ioc (0:ℝ) T)))
    {Cd Cf Cp1 Cp2 : ℝ} (hCd : 0 < Cd) (hCf : 0 ≤ Cf)
    (hd : ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T,
      ‖deriv (rescaledCentered m k x (lam n)) t‖_[m] ≤ Cd * t ^ (-(1:ℝ)/3))
    (hf' : ∀ t, ‖f' t‖_[m] ≤ Cf)
    (hfnc2 : ∀ t ∈ Ioc (0:ℝ) T, ClusterNoColl k (blowUpProfile κ sbar t + f t))
    (hp1 : ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T,
      clusterPotential m k (rescaledCentered m k x (lam n) t) ≤ Cp1 * t ^ (-(2:ℝ)/3))
    (hp2 : ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T,
      clusterPotential m k (rescaledCentered m k x (lam n) t + f t) ≤ Cp2 * t ^ (-(2:ℝ)/3)) :
    Tendsto (fun n => ∫ t in (0:ℝ)..T,
        (massInner m (deriv (rescaledCentered m k x (lam n)) t) (f' t)
          + (1/2) * ‖f' t‖_[m] ^ 2
          + clusterPotential m k (rescaledCentered m k x (lam n) t + f t)
          - clusterPotential m k (rescaledCentered m k x (lam n) t)))
      atTop
      (nhds (∫ t in (0:ℝ)..T,
        (massInner m (deriv (blowUpProfile κ sbar) t) (f' t) + (1/2) * ‖f' t‖_[m] ^ 2
          + clusterPotential m k (blowUpProfile κ sbar t + f t)
          - clusterPotential m k (blowUpProfile κ sbar t)))) := by
  -- the unscaled configuration is collision free inside `k`
  have hfnc1 : ∀ t ∈ Ioc (0:ℝ) T, ClusterNoColl k (blowUpProfile κ sbar t) := by
    intro t ht i hi j hj hij hEq
    simp only [blowUpProfile, PiLp.smul_apply] at hEq
    have hc : (Real.sqrt κ * t ^ ((2:ℝ)/3)) ≠ 0 :=
      mul_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hκ))
        (((Real.rpow_ne_zero ht.1.le (by norm_num : (2:ℝ)/3 ≠ 0)).mpr (ne_of_gt ht.1)))
    exact hsbarnc i hi j hj hij (smul_right_injective E hc hEq)
  -- the dominating function
  have hInt1 : IntegrableOn (fun t : ℝ => t ^ (-(1:ℝ)/3)) (Ioc (0:ℝ) T) volume := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff hT).mpr (by norm_num)
  have hInt2 : IntegrableOn (fun t : ℝ => t ^ (-(2:ℝ)/3)) (Ioc (0:ℝ) T) volume := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff hT).mpr (by norm_num)
  have hIntc : IntegrableOn (fun _ : ℝ => (1/2) * Cf^2) (Ioc (0:ℝ) T) volume :=
    integrableOn_const (measure_Ioc_lt_top (μ := volume)).ne
  have hInt : Integrable
      (fun t : ℝ => (Cd * Cf * t ^ (-(1:ℝ)/3) + (1/2) * Cf^2) + Cp2 * t ^ (-(2:ℝ)/3)
        + Cp1 * t ^ (-(2:ℝ)/3))
      (volume.restrict (Ioc (0:ℝ) T)) := by
    refine (((hInt1.const_mul (Cd * Cf)).add hIntc).add (hInt2.const_mul Cp2)).add
      (hInt2.const_mul Cp1)
  -- pointwise convergence
  have hpt : ∀ᵐ t ∂(volume.restrict (Ioc (0:ℝ) T)),
      Tendsto (fun n => massInner m (deriv (rescaledCentered m k x (lam n)) t) (f' t)
          + (1/2) * ‖f' t‖_[m] ^ 2
          + clusterPotential m k (rescaledCentered m k x (lam n) t + f t)
          - clusterPotential m k (rescaledCentered m k x (lam n) t)) atTop
        (nhds (massInner m (deriv (blowUpProfile κ sbar) t) (f' t)
          + (1/2) * ‖f' t‖_[m] ^ 2 + clusterPotential m k (blowUpProfile κ sbar t + f t)
          - clusterPotential m k (blowUpProfile κ sbar t))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hA : Tendsto (fun n => massInner m (deriv (rescaledCentered m k x (lam n)) t) (f' t))
        atTop (nhds (massInner m (deriv (blowUpProfile κ sbar) t) (f' t))) :=
      tendsto_massInner (m := m) (hconvd t ht)
    have hB : Tendsto (fun _ : ℕ => (1/2) * ‖f' t‖_[m] ^ 2) atTop
        (nhds ((1/2) * ‖f' t‖_[m] ^ 2)) := tendsto_const_nhds
    have hC : Tendsto (fun n => clusterPotential m k (rescaledCentered m k x (lam n) t + f t))
        atTop (nhds (clusterPotential m k (blowUpProfile κ sbar t + f t))) :=
      tendsto_clusterPotential_of_tendsto ((hconv t ht).add tendsto_const_nhds) (hfnc2 t ht)
    have hD : Tendsto (fun n => clusterPotential m k (rescaledCentered m k x (lam n) t)) atTop
        (nhds (clusterPotential m k (blowUpProfile κ sbar t))) :=
      tendsto_clusterPotential_of_tendsto (hconv t ht) (hfnc1 t ht)
    exact ((hA.add hB).add hC).sub hD
  -- measurability
  have hmpot : Measurable (fun y : EN E N => clusterPotential m k y) :=
    measurable_clusterPotential_pair m k
  have hmeasmass : Measurable (fun p : EN E N × EN E N => massInner m p.1 p.2) :=
    measurable_massInner_pair m
  have hae : ∀ᶠ n in atTop,
      AEStronglyMeasurable (fun t : ℝ =>
        massInner m (deriv (rescaledCentered m k x (lam n)) t) (f' t)
          + (1/2) * ‖f' t‖_[m] ^ 2
          + clusterPotential m k (rescaledCentered m k x (lam n) t + f t)
          - clusterPotential m k (rescaledCentered m k x (lam n) t))
        (volume.restrict (Ioc (0:ℝ) T)) := by
    filter_upwards [hmeasq] with n hq
    have hderiv : Measurable (deriv (rescaledCentered m k x (lam n))) := measurable_deriv _
    have hmass : AEMeasurable (fun t : ℝ =>
        massInner m (deriv (rescaledCentered m k x (lam n)) t) (f' t))
        (volume.restrict (Ioc (0:ℝ) T)) :=
      (hmeasmass.comp_aemeasurable (hderiv.aemeasurable.prodMk hmeasf'.aemeasurable))
    have hnorm : AEMeasurable (fun t : ℝ => ‖f' t‖_[m] ^ 2) (volume.restrict (Ioc (0:ℝ) T)) :=
      ((continuous_weightedNorm (fun i => (hm i).le)).measurable.comp_aemeasurable
        hmeasf'.aemeasurable).pow_const 2
    have hsum : AEMeasurable (fun t : ℝ => rescaledCentered m k x (lam n) t + f t)
        (volume.restrict (Ioc (0:ℝ) T)) := hq.aemeasurable.add hmeasf.aemeasurable
    have hc1 : AEMeasurable (fun t : ℝ =>
        clusterPotential m k (rescaledCentered m k x (lam n) t + f t))
        (volume.restrict (Ioc (0:ℝ) T)) := hmpot.comp_aemeasurable hsum
    have hc2 : AEMeasurable (fun t : ℝ =>
        clusterPotential m k (rescaledCentered m k x (lam n) t))
        (volume.restrict (Ioc (0:ℝ) T)) := hmpot.comp_aemeasurable hq.aemeasurable
    exact ((hmass.add (hnorm.const_mul (1/2))).add hc1).sub hc2 |>.aestronglyMeasurable
  -- domination
  have hbd : ∀ᶠ n in atTop, ∀ᵐ t ∂(volume.restrict (Ioc (0:ℝ) T)),
      ‖massInner m (deriv (rescaledCentered m k x (lam n)) t) (f' t) + (1/2) * ‖f' t‖_[m] ^ 2
          + clusterPotential m k (rescaledCentered m k x (lam n) t + f t)
          - clusterPotential m k (rescaledCentered m k x (lam n) t)‖
        ≤ (Cd * Cf * t ^ (-(1:ℝ)/3) + (1/2) * Cf^2) + Cp2 * t ^ (-(2:ℝ)/3)
            + Cp1 * t ^ (-(2:ℝ)/3) := by
    filter_upwards [hd, hp1, hp2] with n hdn hp1n hp2n
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hd0 : 0 < Cd * t ^ (-(1:ℝ)/3) := mul_pos hCd (Real.rpow_pos_of_pos ht.1 _)
    have hA : |massInner m (deriv (rescaledCentered m k x (lam n)) t) (f' t)|
        ≤ Cd * Cf * t ^ (-(1:ℝ)/3) := by
      have h1 := abs_massInner_le_weightedNorm_mul m (fun i => (hm i).le)
        (deriv (rescaledCentered m k x (lam n)) t) (f' t)
      calc |massInner m (deriv (rescaledCentered m k x (lam n)) t) (f' t)|
          ≤ ‖deriv (rescaledCentered m k x (lam n)) t‖_[m] * ‖f' t‖_[m] := h1
        _ ≤ (Cd * t ^ (-(1:ℝ)/3)) * Cf :=
            mul_le_mul (hdn t ht) (hf' t) (weightedNorm_nonneg m (f' t)) (le_of_lt hd0)
        _ = Cd * Cf * t ^ (-(1:ℝ)/3) := by ring
    have hB : ‖(1/2) * ‖f' t‖_[m] ^ 2‖ ≤ (1/2) * Cf^2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (weightedNorm_nonneg m (f' t)) (hf' t) 2) (by norm_num)
    have hC : ‖clusterPotential m k (rescaledCentered m k x (lam n) t + f t)‖
        ≤ Cp2 * t ^ (-(2:ℝ)/3) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (clusterPotential_nonneg (fun i => (hm i).le) k _)]
      exact hp2n t ht
    have hD : ‖clusterPotential m k (rescaledCentered m k x (lam n) t)‖
        ≤ Cp1 * t ^ (-(2:ℝ)/3) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (clusterPotential_nonneg (fun i => (hm i).le) k _)]
      exact hp1n t ht
    have hB0 : 0 ≤ (1/2) * ‖f' t‖_[m] ^ 2 := by positivity
    have hC0 : 0 ≤ clusterPotential m k (rescaledCentered m k x (lam n) t + f t) :=
      clusterPotential_nonneg (fun i => (hm i).le) k _
    have hD0 : 0 ≤ clusterPotential m k (rescaledCentered m k x (lam n) t) :=
      clusterPotential_nonneg (fun i => (hm i).le) k _
    have h1 : ‖massInner m (deriv (rescaledCentered m k x (lam n)) t) (f' t)
          + (1/2) * ‖f' t‖_[m] ^ 2
          + clusterPotential m k (rescaledCentered m k x (lam n) t + f t)
          - clusterPotential m k (rescaledCentered m k x (lam n) t)‖
        ≤ ‖massInner m (deriv (rescaledCentered m k x (lam n)) t) (f' t)
            + (1/2) * ‖f' t‖_[m] ^ 2
            + clusterPotential m k (rescaledCentered m k x (lam n) t + f t)‖
          + ‖clusterPotential m k (rescaledCentered m k x (lam n) t)‖ := norm_sub_le _ _
    have h2 : ‖massInner m (deriv (rescaledCentered m k x (lam n)) t) (f' t)
            + (1/2) * ‖f' t‖_[m] ^ 2
            + clusterPotential m k (rescaledCentered m k x (lam n) t + f t)‖
        ≤ ‖massInner m (deriv (rescaledCentered m k x (lam n)) t) (f' t)
            + (1/2) * ‖f' t‖_[m] ^ 2‖
          + ‖clusterPotential m k (rescaledCentered m k x (lam n) t + f t)‖ := norm_add_le _ _
    have h3 : ‖massInner m (deriv (rescaledCentered m k x (lam n)) t) (f' t)
            + (1/2) * ‖f' t‖_[m] ^ 2‖
        ≤ ‖massInner m (deriv (rescaledCentered m k x (lam n)) t) (f' t)‖
          + ‖(1/2) * ‖f' t‖_[m] ^ 2‖ := norm_add_le _ _
    have h4 : ‖massInner m (deriv (rescaledCentered m k x (lam n)) t) (f' t)‖
        = |massInner m (deriv (rescaledCentered m k x (lam n)) t) (f' t)| :=
      Real.norm_eq_abs _
    have h5 : ‖(1/2) * ‖f' t‖_[m] ^ 2‖ = (1/2) * ‖f' t‖_[m] ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hB0]
    have h6 : ‖clusterPotential m k (rescaledCentered m k x (lam n) t + f t)‖
        = clusterPotential m k (rescaledCentered m k x (lam n) t + f t) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hC0]
    have h7 : ‖clusterPotential m k (rescaledCentered m k x (lam n) t)‖
        = clusterPotential m k (rescaledCentered m k x (lam n) t) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hD0]
    linarith [h1, h2, h3, h4, h5, h6, h7, hA, hB, hC, hD]
  exact tendsto_intervalIntegral_of_dominated
    (F := fun n t => massInner m (deriv (rescaledCentered m k x (lam n)) t) (f' t)
      + (1/2) * ‖f' t‖_[m] ^ 2 + clusterPotential m k (rescaledCentered m k x (lam n) t + f t)
      - clusterPotential m k (rescaledCentered m k x (lam n) t))
    (F₀ := fun t => massInner m (deriv (blowUpProfile κ sbar) t) (f' t)
      + (1/2) * ‖f' t‖_[m] ^ 2 + clusterPotential m k (blowUpProfile κ sbar t + f t)
      - clusterPotential m k (blowUpProfile κ sbar t))
    hT
    (fun t : ℝ => (Cd * Cf * t ^ (-(1:ℝ)/3) + (1/2) * Cf^2) + Cp2 * t ^ (-(2:ℝ)/3)
      + Cp1 * t ^ (-(2:ℝ)/3))
    hInt hae hbd hpt

end Submission.NBody
