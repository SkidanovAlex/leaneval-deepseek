import Submission.NBody.MarchalClusterShape
import Submission.NBody.MarchalBumpTransfer
import Submission.NBody.MarchalClusterAsymptotic3

/-!
# The shape sphere and its compactness (sequential blow-up, part 1)

This module begins the *sequential* (Ferrario--Terracini) form of the blow-up argument, the only form
in which the limit of the normalised configuration is available: FT's `propo:srcblowup` produces
convergence of `s(λ t)` only along a sequence `λ = λ_n` for which `s(λ_n)` converges.

Here we collect the elementary geometry of the shape:

* the shape of a non-degenerate configuration lies in the compact set
  `shapeSet m k = {s | I_k(s) = 1, cm_k(s) = 0, s = 0 outside k}`;
* hence along any sequence of times one can extract a subsequence for which the shape converges.

All results are fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The centre of mass of the centre-of-mass-relative configuration is zero. -/
lemma clusterCM_cmRel {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N}
    (hmk : clusterMass m k ≠ 0) : clusterCM m k (cmRel m k x) = 0 := by
  rw [clusterCM]
  have h : (∑ i ∈ k, m i • (cmRel m k x) i) = 0 := by
    have h1 : ∀ i ∈ k, m i • (cmRel m k x) i = m i • (x i - clusterCM m k x) := by
      intro i hi; rw [cmRel_apply_of_mem hi]
    rw [Finset.sum_congr rfl h1]
    exact clusterCM_sum hmk
  rw [h, smul_zero]

/-- `cmRel` is idempotent. -/
lemma cmRel_cmRel {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N}
    (hmk : clusterMass m k ≠ 0) : cmRel m k (cmRel m k x) = cmRel m k x := by
  refine PiLp.ext fun i => ?_
  by_cases hi : i ∈ k
  · rw [cmRel_apply_of_mem hi, cmRel_apply_of_mem hi, clusterCM_cmRel hmk, sub_zero]
  · rw [cmRel_apply_of_notMem hi, cmRel_apply_of_notMem hi]


/-- Scaling of the centre of mass (stated without the extra type-class assumptions of the
`MarchalBumpTransfer` version, so that it can be used in the geometry of the shape sphere). -/
lemma clusterCM_smul' (m : Fin N → ℝ) (k : Finset (Fin N)) (c : ℝ) (x : EN E N) :
    clusterCM m k (c • x) = c • clusterCM m k x := by
  have hsum : (∑ i ∈ k, m i • ((c • x : EN E N) i)) = c • ∑ i ∈ k, m i • x i := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PiLp.smul_apply, smul_comm]
  rw [clusterCM, clusterCM, hsum, smul_comm]

/-- The moment of inertia is unchanged by passing to the centre-of-mass-relative configuration. -/
lemma clusterInertia_cmRel {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N}
    (hmk : clusterMass m k ≠ 0) : clusterInertia m k (cmRel m k x) = clusterInertia m k x := by
  rw [clusterInertia, clusterInertia, clusterCM_cmRel hmk]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [cmRel_apply_of_mem hi, sub_zero]

/-- Scaling of the moment of inertia of a cluster. -/
lemma clusterInertia_smul' (m : Fin N → ℝ) (k : Finset (Fin N)) (c : ℝ) (x : EN E N) :
    clusterInertia m k (c • x) = c ^ 2 * clusterInertia m k x := by
  rw [clusterInertia, clusterInertia, clusterCM_smul']
  have hpt : ∀ i ∈ k, m i * ‖(c • x : EN E N) i - c • clusterCM m k x‖ ^ 2
      = c ^ 2 * (m i * ‖x i - clusterCM m k x‖ ^ 2) := by
    intro i hi
    have h1 : (c • x : EN E N) i - c • clusterCM m k x = c • (x i - clusterCM m k x) := by
      rw [PiLp.smul_apply, ← smul_sub]
    rw [h1, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum]

/-- Continuity of the centre of mass. -/
lemma continuous_clusterCM (m : Fin N → ℝ) (k : Finset (Fin N)) :
    Continuous (clusterCM m k : EN E N → E) := by
  have hunfold : clusterCM m k = fun x : EN E N => (clusterMass m k)⁻¹ • ∑ i ∈ k, m i • x i := rfl
  rw [hunfold]
  refine continuous_const.smul ?_
  exact continuous_finsetSum _ fun i _ =>
    continuous_const.smul (PiLp.continuous_apply 2 (fun _ : Fin N => E) i)

/-- Continuity of the moment of inertia. -/
lemma continuous_clusterInertia (m : Fin N → ℝ) (k : Finset (Fin N)) :
    Continuous (clusterInertia m k : EN E N → ℝ) := by
  have hunfold : clusterInertia m k
      = fun x : EN E N => ∑ i ∈ k, m i * ‖x i - clusterCM m k x‖ ^ 2 := rfl
  rw [hunfold]
  refine continuous_finsetSum _ fun i _ => ?_
  refine continuous_const.mul ?_
  exact (((PiLp.continuous_apply 2 (fun _ : Fin N => E) i).sub
    (continuous_clusterCM m k)).norm).pow 2

/-- The shape of a non-degenerate configuration has unit moment of inertia. -/
lemma clusterInertia_clusterShape {m : Fin N → ℝ} {k : Finset (Fin N)}
    {y : EN E N} (hmk : clusterMass m k ≠ 0) (hy : 0 < clusterInertia m k y) :
    clusterInertia m k (clusterShape m k y) = 1 := by
  have hc : clusterShape m k y = (Real.sqrt (clusterInertia m k y))⁻¹ • cmRel m k y := rfl
  rw [hc, clusterInertia_smul', clusterInertia_cmRel hmk]
  have hsq : Real.sqrt (clusterInertia m k y) ^ 2 = clusterInertia m k y :=
    Real.sq_sqrt hy.le
  rw [inv_pow, hsq, inv_mul_cancel₀ (ne_of_gt hy)]

/-- The centre of mass of the shape is zero. -/
lemma clusterCM_clusterShape {m : Fin N → ℝ} {k : Finset (Fin N)} {y : EN E N}
    (hmk : clusterMass m k ≠ 0) : clusterCM m k (clusterShape m k y) = 0 := by
  have hc : clusterShape m k y = (Real.sqrt (clusterInertia m k y))⁻¹ • cmRel m k y := rfl
  rw [hc, clusterCM_smul', clusterCM_cmRel hmk, smul_zero]

/-- The shape vanishes outside the cluster. -/
lemma clusterShape_apply_of_notMem {m : Fin N → ℝ} {k : Finset (Fin N)} {y : EN E N} {i : Fin N}
    (hi : i ∉ k) : clusterShape m k y i = 0 := by
  rw [clusterShape_apply, cmRel_apply_of_notMem hi, smul_zero]

/-- The compact set of normalised configurations of a cluster. -/
noncomputable def shapeSet (m : Fin N → ℝ) (k : Finset (Fin N)) : Set (EN E N) :=
  {s : EN E N | clusterInertia m k s = 1 ∧ clusterCM m k s = 0 ∧ ∀ i ∉ k, s i = 0}

lemma clusterShape_mem_shapeSet {m : Fin N → ℝ} {k : Finset (Fin N)}
    {y : EN E N} (hmk : clusterMass m k ≠ 0) (hy : 0 < clusterInertia m k y) :
    clusterShape m k y ∈ shapeSet m k :=
  ⟨clusterInertia_clusterShape hmk hy, clusterCM_clusterShape hmk,
    fun _ hi => clusterShape_apply_of_notMem hi⟩

/-- The set of normalised configurations of a cluster is compact. -/
theorem isCompact_shapeSet {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)}
    (_hk : k.Nonempty) : IsCompact (shapeSet m k : Set (EN E N)) := by
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  refine isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
  · have h1 : IsClosed {s : EN E N | clusterInertia m k s = 1} :=
      isClosed_eq (continuous_clusterInertia m k) continuous_const
    have h2 : IsClosed {s : EN E N | clusterCM m k s = 0} :=
      isClosed_eq (continuous_clusterCM m k) continuous_const
    have h3 : IsClosed {s : EN E N | ∀ i ∉ k, s i = 0} := by
      have heq : {s : EN E N | ∀ i ∉ k, s i = 0}
          = ⋂ i ∈ (Finset.univ \ k), {s : EN E N | s i = 0} := by
        ext s
        simp [Finset.mem_sdiff, Finset.mem_univ]
      rw [heq]
      exact isClosed_biInter fun i _ =>
        isClosed_singleton.preimage (PiLp.continuous_apply 2 (fun _ : Fin N => E) i)
    exact h1.inter (h2.inter h3)
  · refine (Metric.isBounded_closedBall (x := (0 : EN E N))
      (r := Real.sqrt (∑ i ∈ k, (m i)⁻¹))).subset ?_
    intro s hs
    rw [Metric.mem_closedBall, dist_zero_right]
    obtain ⟨hI, hcm, hout⟩ := hs
    have hIeq : ∑ i ∈ k, m i * ‖s i‖ ^ 2 = 1 := by
      rw [← hI]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcm, sub_zero]
    have hnorm : ‖s‖ ^ 2 = ∑ i ∈ k, ‖s i‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      exact (Finset.sum_subset (Finset.subset_univ k)
        (fun i _ hi => by rw [hout i hi, norm_zero]; ring)).symm
    have hle : ∑ i ∈ k, ‖s i‖ ^ 2 ≤ ∑ i ∈ k, (m i)⁻¹ := by
      have step1 : ∑ i ∈ k, ‖s i‖ ^ 2 = ∑ i ∈ k, (m i)⁻¹ * (m i * ‖s i‖ ^ 2) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (hm i)), one_mul]
      rw [step1]
      calc ∑ i ∈ k, (m i)⁻¹ * (m i * ‖s i‖ ^ 2)
          ≤ ∑ i ∈ k, (∑ j ∈ k, (m j)⁻¹) * (m i * ‖s i‖ ^ 2) := by
            refine Finset.sum_le_sum fun i hi => ?_
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (hm0 i) (sq_nonneg _))
            exact Finset.single_le_sum (fun j _ => inv_nonneg.mpr (hm0 j)) hi
        _ = (∑ j ∈ k, (m j)⁻¹) * (∑ i ∈ k, m i * ‖s i‖ ^ 2) := by
            rw [Finset.mul_sum]
        _ = ∑ i ∈ k, (m i)⁻¹ := by rw [hIeq, mul_one]
    rw [← hnorm] at hle
    calc ‖s‖ = Real.sqrt (‖s‖ ^ 2) := (Real.sqrt_sq (norm_nonneg s)).symm
      _ ≤ Real.sqrt (∑ i ∈ k, (m i)⁻¹) := Real.sqrt_le_sqrt hle

/-- **Existence of a converging sequence of shapes** (the compactness behind FT's
`propo:srcblowup`).  Given two curves whose shapes lie in the shape sphere on `(0,ε)`, there is a
sequence of times `λ_n → 0⁺` for which both shapes converge. -/
theorem exists_seq_shape {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)} (hk : k.Nonempty)
    {xR xL : ℝ → EN E N} {ε : ℝ} (hε : 0 < ε)
    (hR : ∀ t ∈ Ioo (0:ℝ) ε, clusterShape m k (xR t) ∈ shapeSet m k)
    (hL : ∀ t ∈ Ioo (0:ℝ) ε, clusterShape m k (xL t) ∈ shapeSet m k) :
    ∃ lam : ℕ → ℝ, (∀ n, 0 < lam n) ∧ Tendsto lam atTop (nhdsWithin (0:ℝ) (Ioi 0)) ∧
      ∃ sbarR sbarL : EN E N, sbarR ∈ shapeSet m k ∧ sbarL ∈ shapeSet m k ∧
        Tendsto (fun n => clusterShape m k (xR (lam n))) atTop (nhds sbarR) ∧
        Tendsto (fun n => clusterShape m k (xL (lam n))) atTop (nhds sbarL) := by
  have hcomp := (isCompact_shapeSet (E := E) hm hk).prod (isCompact_shapeSet (E := E) hm hk)
  set u : ℕ → EN E N × EN E N := fun n =>
    (clusterShape m k (xR (1 / ((n : ℝ) + 1))), clusterShape m k (xL (1 / ((n : ℝ) + 1))))
    with hu
  have hfreq : ∃ᶠ n in atTop, u n ∈ shapeSet m k ×ˢ shapeSet m k := by
    refine Filter.Eventually.frequently ?_
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_gt_atTop (1 / ε))] with n hn
    have hpos : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hmul : 1 < ε * (n : ℝ) := by rw [mul_comm]; exact (div_lt_iff₀ hε).mp hn
    have hlt : 1 / ((n : ℝ) + 1) < ε := by
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < (n : ℝ) + 1)]
      nlinarith [hε]
    exact ⟨hR _ ⟨hpos, hlt⟩, hL _ ⟨hpos, hlt⟩⟩
  obtain ⟨a, ha, φ, hφmono, hφlim⟩ := hcomp.tendsto_subseq' hfreq
  refine ⟨fun n => 1 / ((φ n : ℝ) + 1), fun n => by positivity, ?_, a.1, a.2, ha.1, ha.2, ?_, ?_⟩
  · rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hφtop : Tendsto (fun n : ℕ => ((φ n : ℕ) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp hφmono.tendsto_atTop
      have hden : Tendsto (fun n : ℕ => ((φ n : ℕ) : ℝ) + 1) atTop atTop :=
        hφtop.atTop_add tendsto_const_nhds
      simpa using (tendsto_const_nhds (x := (1:ℝ))).div_atTop hden
    · filter_upwards with n
      show (0:ℝ) < 1 / ((φ n : ℝ) + 1)
      positivity
  · exact ((continuous_fst.tendsto a).comp hφlim)
  · exact ((continuous_snd.tendsto a).comp hφlim)

end Submission.NBody
