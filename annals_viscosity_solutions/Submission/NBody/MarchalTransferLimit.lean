import Submission.NBody.MarchalDerivBound
import Submission.NBody.MarchalBumpIntegrable
import Submission.NBody.MarchalClusterBlowUpPotential
import Submission.NBody.MarchalClusterBlowUpDeriv

/-!
# The transfer to the blow-up limit (Ferrario–Terracini `propo:blowup`)

The variational argument of `Submission/ROADMAP.md` needs the limit

  `∫_0^T [ L_k(q^λ + v^δ) - L_k(q^λ) ] dt  ⟶  ∫_0^T [ L_k(q̄ + v^δ) - L_k(q̄) ] dt`

as `λ → 0⁺`, where `q^λ` is the blow-up of the colliding minimiser, `q̄` the parabolic
blow-up limit and `v^δ` a *fixed* standard variation.  This is a dominated-convergence
statement; the present module isolates its measure-theoretic core, taking the four
analytic inputs (pointwise convergence of `q^λ`, of `(q^λ)'`, the velocity bound and the
potential bound) as hypotheses.

All results in this file are fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **Dominated convergence for a `(0,T]`-integral.**  If `F λ → F₀` pointwise and the `F λ` are
eventually dominated by an integrable `bound`, then the integrals converge. -/
theorem tendsto_intervalIntegral_of_dominated {T : ℝ} (hT : 0 < T) {ι : Type*}
    {l : Filter ι} [l.IsCountablyGenerated] {F : ι → ℝ → ℝ} {F₀ : ℝ → ℝ}
    (bound : ℝ → ℝ) (hInt : Integrable bound (volume.restrict (Ioc (0:ℝ) T)))
    (hae : ∀ᶠ lam in l, AEStronglyMeasurable (F lam) (volume.restrict (Ioc (0:ℝ) T)))
    (hbd : ∀ᶠ lam in l, ∀ᵐ t ∂(volume.restrict (Ioc (0:ℝ) T)), ‖F lam t‖ ≤ bound t)
    (hpt : ∀ᵐ t ∂(volume.restrict (Ioc (0:ℝ) T)), Tendsto (fun lam => F lam t) l (nhds (F₀ t))) :
    Tendsto (fun lam => ∫ t in (0:ℝ)..T, F lam t) l (nhds (∫ t in (0:ℝ)..T, F₀ t)) := by
  have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioc (0:ℝ) T)) (l := l) bound hae hbd hInt hpt
  simpa only [intervalIntegral.integral_of_le hT.le] using h

/-- **Continuity of the cluster potential along a convergent family.**  If `y n → y₀` and the
configuration `y₀` has no collision inside `k`, then `clusterPotential m k (y n) → clusterPotential
m k y₀`. -/
lemma tendsto_clusterPotential_of_tendsto {ι : Type*} {l : Filter ι}
    {m : Fin N → ℝ} {k : Finset (Fin N)} {y : ι → EN E N} {y₀ : EN E N}
    (hy : Tendsto y l (nhds y₀)) (hnc : ClusterNoColl k y₀) :
    Tendsto (fun n => clusterPotential m k (y n)) l (nhds (clusterPotential m k y₀)) := by
  have hunfold : ∀ z : EN E N, clusterPotential m k z
      = ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k),
          m p.1 * m p.2 * (r z p.1 p.2)⁻¹ := fun z => rfl
  simp only [hunfold]
  refine tendsto_finsetSum _ fun p hp => ?_
  rw [Finset.mem_filter] at hp
  obtain ⟨hp1, hp2, hp3⟩ := hp
  have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp1).2
  have hne : p.1 ≠ p.2 := ne_of_lt hlt
  have hlim_ne : r y₀ p.1 p.2 ≠ 0 := by
    rw [r_eq_norm_sub, norm_ne_zero_iff, sub_ne_zero]
    exact hnc p.1 hp2 p.2 hp3 hne
  have happly : ∀ i : Fin N, Tendsto (fun n => y n i) l (nhds (y₀ i)) := fun i =>
    (PiLp.continuous_apply 2 (fun _ : Fin N => E) i).continuousAt.tendsto.comp hy
  have hrt : Tendsto (fun n => r (y n) p.1 p.2) l (nhds (r y₀ p.1 p.2)) := by
    have h1 : Tendsto (fun n => y n p.1 - y n p.2) l (nhds (y₀ p.1 - y₀ p.2)) :=
      (happly p.1).sub (happly p.2)
    have h2 : Tendsto (fun n => ‖y n p.1 - y n p.2‖) l (nhds ‖y₀ p.1 - y₀ p.2‖) :=
      continuous_norm.continuousAt.tendsto.comp h1
    simpa only [r_eq_norm_sub] using h2
  exact ((hrt.inv₀ hlim_ne).const_mul (m p.1 * m p.2))

lemma measurable_massInner_pair (m : Fin N → ℝ) :
    Measurable (fun p : EN E N × EN E N => massInner m p.1 p.2) := by
  have hunfold : (fun p : EN E N × EN E N => massInner m p.1 p.2)
      = fun (p : EN E N × EN E N) => ∑ i, m i * inner ℝ (p.1 i) (p.2 i) := rfl
  rw [hunfold]
  refine Finset.measurable_sum _ fun i _ => ?_
  have h1 : Measurable (fun p : EN E N × EN E N => p.1 i) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin N => E) i).measurable).comp measurable_fst
  have h2 : Measurable (fun p : EN E N × EN E N => p.2 i) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin N => E) i).measurable).comp measurable_snd
  exact measurable_const.mul (h1.inner h2)

lemma measurable_clusterPotential_pair (m : Fin N → ℝ) (k : Finset (Fin N)) :
    Measurable (fun y : EN E N => clusterPotential m k y) := by
  simp only [clusterPotential]
  refine Finset.measurable_sum _ fun p hp => ?_
  have hc : Continuous (fun y : EN E N => dist (y p.1) (y p.2)) := by fun_prop
  exact (hc.measurable.inv).const_mul (m p.1 * m p.2)

/-- **The mass inner product is continuous in its first argument.** -/
lemma tendsto_massInner {ι : Type*} {l : Filter ι} {m : Fin N → ℝ} {v : ι → EN E N}
    {w : EN E N} {v₀ : EN E N} (hv : Tendsto v l (nhds v₀)) :
    Tendsto (fun n => massInner m (v n) w) l (nhds (massInner m v₀ w)) := by
  have hunfold : ∀ z : EN E N, massInner m z w = ∑ i, m i * inner ℝ (z i) (w i) := fun z => rfl
  simp only [hunfold]
  refine tendsto_finsetSum _ fun i _ => ?_
  refine tendsto_const_nhds.mul ?_
  refine (Filter.Tendsto.inner ?_ tendsto_const_nhds)
  exact (PiLp.continuous_apply 2 (fun _ : Fin N => E) i).continuousAt.tendsto.comp hv

/-- **The transfer to the blow-up limit (Ferrario–Terracini `propo:blowup`).**  Under the
pointwise convergence of the blow-up and of its derivative, the velocity bound and the two
potential bounds, the rescaled cluster Lagrangian difference converges to the model one. -/
theorem tendsto_transfer_of_data
    {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N} {κ T : ℝ} {sbar : EN E N}
    {f f' : ℝ → EN E N}
    (hm : ∀ i, 0 < m i) (hκ : 0 < κ) (hT : 0 < T)
    (hsbarnc : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → sbar i ≠ sbar j)
    (hconv : ∀ t ∈ Ioc (0:ℝ) T, Tendsto (fun lam => rescaledCentered m k x lam t)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (blowUpProfile κ sbar t)))
    (hconvd : ∀ t ∈ Ioc (0:ℝ) T, Tendsto (fun lam => deriv (rescaledCentered m k x lam) t)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (deriv (blowUpProfile κ sbar) t)))
    (hmeasq : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0),
      AEStronglyMeasurable (rescaledCentered m k x lam) (volume.restrict (Ioc (0:ℝ) T)))
    (hmeasf : AEStronglyMeasurable f (volume.restrict (Ioc (0:ℝ) T)))
    (hmeasf' : AEStronglyMeasurable f' (volume.restrict (Ioc (0:ℝ) T)))
    {Cd Cf Cp1 Cp2 : ℝ} (hCd : 0 < Cd) (hCf : 0 ≤ Cf)
    (hd : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T,
      ‖deriv (rescaledCentered m k x lam) t‖_[m] ≤ Cd * t ^ (-(1:ℝ)/3))
    (hf' : ∀ t, ‖f' t‖_[m] ≤ Cf)
    (hfnc2 : ∀ t ∈ Ioc (0:ℝ) T, ClusterNoColl k (blowUpProfile κ sbar t + f t))
    (hp1 : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T,
      clusterPotential m k (rescaledCentered m k x lam t) ≤ Cp1 * t ^ (-(2:ℝ)/3))
    (hp2 : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T,
      clusterPotential m k (rescaledCentered m k x lam t + f t) ≤ Cp2 * t ^ (-(2:ℝ)/3)) :
    Tendsto (fun lam => ∫ t in (0:ℝ)..T,
        (massInner m (deriv (rescaledCentered m k x lam) t) (f' t) + (1/2) * ‖f' t‖_[m] ^ 2
          + clusterPotential m k (rescaledCentered m k x lam t + f t)
          - clusterPotential m k (rescaledCentered m k x lam t)))
      (nhdsWithin (0:ℝ) (Ioi 0))
      (nhds (∫ t in (0:ℝ)..T,
        (massInner m (deriv (blowUpProfile κ sbar) t) (f' t) + (1/2) * ‖f' t‖_[m] ^ 2
          + clusterPotential m k (blowUpProfile κ sbar t + f t)
          - clusterPotential m k (blowUpProfile κ sbar t)))) := by
  set l := nhdsWithin (0:ℝ) (Ioi 0) with hl
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
      Tendsto (fun lam => massInner m (deriv (rescaledCentered m k x lam) t) (f' t)
          + (1/2) * ‖f' t‖_[m] ^ 2 + clusterPotential m k (rescaledCentered m k x lam t + f t)
          - clusterPotential m k (rescaledCentered m k x lam t)) l
        (nhds (massInner m (deriv (blowUpProfile κ sbar) t) (f' t)
          + (1/2) * ‖f' t‖_[m] ^ 2 + clusterPotential m k (blowUpProfile κ sbar t + f t)
          - clusterPotential m k (blowUpProfile κ sbar t))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hA : Tendsto (fun lam => massInner m (deriv (rescaledCentered m k x lam) t) (f' t))
        l (nhds (massInner m (deriv (blowUpProfile κ sbar) t) (f' t))) :=
      tendsto_massInner (m := m) (hconvd t ht)
    have hB : Tendsto (fun _ : ℝ => (1/2) * ‖f' t‖_[m] ^ 2) l
        (nhds ((1/2) * ‖f' t‖_[m] ^ 2)) := tendsto_const_nhds
    have hC : Tendsto (fun lam => clusterPotential m k (rescaledCentered m k x lam t + f t))
        l (nhds (clusterPotential m k (blowUpProfile κ sbar t + f t))) :=
      tendsto_clusterPotential_of_tendsto ((hconv t ht).add tendsto_const_nhds) (hfnc2 t ht)
    have hD : Tendsto (fun lam => clusterPotential m k (rescaledCentered m k x lam t)) l
        (nhds (clusterPotential m k (blowUpProfile κ sbar t))) :=
      tendsto_clusterPotential_of_tendsto (hconv t ht) (hfnc1 t ht)
    exact ((hA.add hB).add hC).sub hD
  -- measurability
  have hmpot : Measurable (fun y : EN E N => clusterPotential m k y) :=
    measurable_clusterPotential_pair m k
  have hmeasmass : Measurable (fun p : EN E N × EN E N => massInner m p.1 p.2) :=
    measurable_massInner_pair m
  have hae : ∀ᶠ lam in l,
      AEStronglyMeasurable (fun t : ℝ => massInner m (deriv (rescaledCentered m k x lam) t) (f' t)
          + (1/2) * ‖f' t‖_[m] ^ 2 + clusterPotential m k (rescaledCentered m k x lam t + f t)
          - clusterPotential m k (rescaledCentered m k x lam t))
        (volume.restrict (Ioc (0:ℝ) T)) := by
    filter_upwards [hmeasq] with lam hq
    have hderiv : Measurable (deriv (rescaledCentered m k x lam)) := measurable_deriv _
    have hmass : AEMeasurable (fun t : ℝ =>
        massInner m (deriv (rescaledCentered m k x lam) t) (f' t))
        (volume.restrict (Ioc (0:ℝ) T)) :=
      (hmeasmass.comp_aemeasurable (hderiv.aemeasurable.prodMk hmeasf'.aemeasurable))
    have hnorm : AEMeasurable (fun t : ℝ => ‖f' t‖_[m] ^ 2) (volume.restrict (Ioc (0:ℝ) T)) :=
      ((continuous_weightedNorm (fun i => (hm i).le)).measurable.comp_aemeasurable
        hmeasf'.aemeasurable).pow_const 2
    have hsum : AEMeasurable (fun t : ℝ => rescaledCentered m k x lam t + f t)
        (volume.restrict (Ioc (0:ℝ) T)) := hq.aemeasurable.add hmeasf.aemeasurable
    have hc1 : AEMeasurable (fun t : ℝ =>
        clusterPotential m k (rescaledCentered m k x lam t + f t))
        (volume.restrict (Ioc (0:ℝ) T)) := hmpot.comp_aemeasurable hsum
    have hc2 : AEMeasurable (fun t : ℝ =>
        clusterPotential m k (rescaledCentered m k x lam t)) (volume.restrict (Ioc (0:ℝ) T)) :=
      hmpot.comp_aemeasurable hq.aemeasurable
    exact ((hmass.add (hnorm.const_mul (1/2))).add hc1).sub hc2 |>.aestronglyMeasurable
  -- domination
  have hbd : ∀ᶠ lam in l, ∀ᵐ t ∂(volume.restrict (Ioc (0:ℝ) T)),
      ‖massInner m (deriv (rescaledCentered m k x lam) t) (f' t) + (1/2) * ‖f' t‖_[m] ^ 2
          + clusterPotential m k (rescaledCentered m k x lam t + f t)
          - clusterPotential m k (rescaledCentered m k x lam t)‖
        ≤ (Cd * Cf * t ^ (-(1:ℝ)/3) + (1/2) * Cf^2) + Cp2 * t ^ (-(2:ℝ)/3)
            + Cp1 * t ^ (-(2:ℝ)/3) := by
    filter_upwards [hd, hp1, hp2] with lam hdlam hp1lam hp2lam
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hd0 : 0 < Cd * t ^ (-(1:ℝ)/3) := mul_pos hCd (Real.rpow_pos_of_pos ht.1 _)
    have hA : |massInner m (deriv (rescaledCentered m k x lam) t) (f' t)|
        ≤ Cd * Cf * t ^ (-(1:ℝ)/3) := by
      have h1 := abs_massInner_le_weightedNorm_mul m (fun i => (hm i).le)
        (deriv (rescaledCentered m k x lam) t) (f' t)
      calc |massInner m (deriv (rescaledCentered m k x lam) t) (f' t)|
          ≤ ‖deriv (rescaledCentered m k x lam) t‖_[m] * ‖f' t‖_[m] := h1
        _ ≤ (Cd * t ^ (-(1:ℝ)/3)) * Cf :=
            mul_le_mul (hdlam t ht) (hf' t) (weightedNorm_nonneg m (f' t)) (le_of_lt hd0)
        _ = Cd * Cf * t ^ (-(1:ℝ)/3) := by ring
    have hB : ‖(1/2) * ‖f' t‖_[m] ^ 2‖ ≤ (1/2) * Cf^2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (weightedNorm_nonneg m (f' t)) (hf' t) 2) (by norm_num)
    have hC : ‖clusterPotential m k (rescaledCentered m k x lam t + f t)‖
        ≤ Cp2 * t ^ (-(2:ℝ)/3) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (clusterPotential_nonneg (fun i => (hm i).le) k _)]
      exact hp2lam t ht
    have hD : ‖clusterPotential m k (rescaledCentered m k x lam t)‖
        ≤ Cp1 * t ^ (-(2:ℝ)/3) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (clusterPotential_nonneg (fun i => (hm i).le) k _)]
      exact hp1lam t ht
    have hA0 : |massInner m (deriv (rescaledCentered m k x lam) t) (f' t)|
        ≤ Cd * Cf * t ^ (-(1:ℝ)/3) := hA
    have hB0 : 0 ≤ (1/2) * ‖f' t‖_[m] ^ 2 := by positivity
    have hC0 : 0 ≤ clusterPotential m k (rescaledCentered m k x lam t + f t) :=
      clusterPotential_nonneg (fun i => (hm i).le) k _
    have hD0 : 0 ≤ clusterPotential m k (rescaledCentered m k x lam t) :=
      clusterPotential_nonneg (fun i => (hm i).le) k _
    have h1 : ‖massInner m (deriv (rescaledCentered m k x lam) t) (f' t)
          + (1/2) * ‖f' t‖_[m] ^ 2 + clusterPotential m k (rescaledCentered m k x lam t + f t)
          - clusterPotential m k (rescaledCentered m k x lam t)‖
        ≤ ‖massInner m (deriv (rescaledCentered m k x lam) t) (f' t)
            + (1/2) * ‖f' t‖_[m] ^ 2
            + clusterPotential m k (rescaledCentered m k x lam t + f t)‖
          + ‖clusterPotential m k (rescaledCentered m k x lam t)‖ := norm_sub_le _ _
    have h2 : ‖massInner m (deriv (rescaledCentered m k x lam) t) (f' t)
            + (1/2) * ‖f' t‖_[m] ^ 2
            + clusterPotential m k (rescaledCentered m k x lam t + f t)‖
        ≤ ‖massInner m (deriv (rescaledCentered m k x lam) t) (f' t)
            + (1/2) * ‖f' t‖_[m] ^ 2‖
          + ‖clusterPotential m k (rescaledCentered m k x lam t + f t)‖ := norm_add_le _ _
    have h3 : ‖massInner m (deriv (rescaledCentered m k x lam) t) (f' t)
            + (1/2) * ‖f' t‖_[m] ^ 2‖
        ≤ ‖massInner m (deriv (rescaledCentered m k x lam) t) (f' t)‖
          + ‖(1/2) * ‖f' t‖_[m] ^ 2‖ := norm_add_le _ _
    have h4 : ‖massInner m (deriv (rescaledCentered m k x lam) t) (f' t)‖
        = |massInner m (deriv (rescaledCentered m k x lam) t) (f' t)| :=
      Real.norm_eq_abs _
    have h5 : ‖(1/2) * ‖f' t‖_[m] ^ 2‖ = (1/2) * ‖f' t‖_[m] ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hB0]
    have h6 : ‖clusterPotential m k (rescaledCentered m k x lam t + f t)‖
        = clusterPotential m k (rescaledCentered m k x lam t + f t) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hC0]
    have h7 : ‖clusterPotential m k (rescaledCentered m k x lam t)‖
        = clusterPotential m k (rescaledCentered m k x lam t) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hD0]
    linarith [h1, h2, h3, h4, h5, h6, h7, hA, hB, hC, hD]
  exact tendsto_intervalIntegral_of_dominated
    (F := fun lam t => massInner m (deriv (rescaledCentered m k x lam) t) (f' t)
      + (1/2) * ‖f' t‖_[m] ^ 2 + clusterPotential m k (rescaledCentered m k x lam t + f t)
      - clusterPotential m k (rescaledCentered m k x lam t))
    (F₀ := fun t => massInner m (deriv (blowUpProfile κ sbar) t) (f' t)
      + (1/2) * ‖f' t‖_[m] ^ 2 + clusterPotential m k (blowUpProfile κ sbar t + f t)
      - clusterPotential m k (blowUpProfile κ sbar t))
    hT
    (fun t : ℝ => (Cd * Cf * t ^ (-(1:ℝ)/3) + (1/2) * Cf^2) + Cp2 * t ^ (-(2:ℝ)/3)
      + Cp1 * t ^ (-(2:ℝ)/3))
    hInt hae hbd hpt

end Submission.NBody
