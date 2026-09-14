import Submission.NBody.MarchalClusterBound
import Submission.NBody.MarchalSeqShape

/-!
# Collision classes

The first layer of the geometry of the Marchal chapter (F1): the **collision class** of a body at a
time `t₀`, i.e. the set of bodies which coincide with it.  This is the candidate cluster for the
blow-up at `t₀`.

Recorded here:

* `collClass` and its basic algebra;
* the *one-sided* separation of a collision class from its complement (only bounds between `k` and
  `kᶜ`, not between two bodies of `kᶜ` — see `Submission/ROADMAP.md`, SESSION 40 (cont.), for why
  the two-sided form is unattainable in the multi-cluster case);
* `clusterInertia m k (γ t₀) = 0` and hence `clusterInertia m k (γ t) → 0` at `t₀`.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The **collision class** of the body `i₀` at the time `t₀`: the set of bodies which occupy the
same position as `i₀` at `t₀`. -/
noncomputable def collClass (γ : ℝ → EN E N) (t₀ : ℝ) (i₀ : Fin N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun j => γ t₀ j = γ t₀ i₀)

lemma mem_collClass {γ : ℝ → EN E N} {t₀ : ℝ} {i₀ j : Fin N} :
    j ∈ collClass γ t₀ i₀ ↔ γ t₀ j = γ t₀ i₀ := by
  classical
  simp [collClass]

lemma collClass_eq_of_mem {γ : ℝ → EN E N} {t₀ : ℝ} {i₀ j : Fin N}
    (hj : j ∈ collClass γ t₀ i₀) : γ t₀ j = γ t₀ i₀ := mem_collClass.mp hj

lemma mem_collClass_self (γ : ℝ → EN E N) (t₀ : ℝ) (i₀ : Fin N) :
    i₀ ∈ collClass γ t₀ i₀ := mem_collClass.mpr rfl

/-- If all bodies of a cluster occupy the same point, the centre of mass of the cluster is that
point. -/
lemma clusterCM_eq_of_all_eq {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N} {c : E}
    (hmk : clusterMass m k ≠ 0) (h : ∀ i ∈ k, x i = c) : clusterCM m k x = c := by
  have h1 : (∑ i ∈ k, m i • x i) = (clusterMass m k) • c := by
    rw [clusterMass, Finset.sum_smul]
    exact Finset.sum_congr rfl fun i hi => by rw [h i hi]
  rw [clusterCM, h1, smul_smul, inv_mul_cancel₀ hmk, one_smul]

/-- **The inertia of a collision class vanishes at the collision time.** -/
lemma clusterInertia_collClass_eq_zero {m : Fin N → ℝ} {γ : ℝ → EN E N} {t₀ : ℝ} {i₀ : Fin N}
    (hmk : clusterMass m (collClass γ t₀ i₀) ≠ 0) :
    clusterInertia m (collClass γ t₀ i₀) (γ t₀) = 0 := by
  have hcm : clusterCM m (collClass γ t₀ i₀) (γ t₀) = γ t₀ i₀ :=
    clusterCM_eq_of_all_eq hmk (fun i hi => collClass_eq_of_mem hi)
  rw [clusterInertia, hcm]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [collClass_eq_of_mem hi, sub_self, norm_zero]
  ring

/-- **The one-sided separation of a collision class from its complement.**  Only pairs with exactly
one body in the class are constrained (see the ROADMAP for why the two-sided form is not
available in the multi-cluster case). -/
lemma exists_clusterSeparatedWeak_of_collClass {γ : ℝ → EN E N} {a b t₀ : ℝ} {i₀ : Fin N}
    (hcont : ContinuousOn γ (Icc a b)) (ht₀ : t₀ ∈ Ioo a b) :
    ∃ ν > 0, ∃ ε > 0, ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      ∀ i ∈ collClass γ t₀ i₀, ∀ j ∉ collClass γ t₀ i₀, ν ≤ r (γ t) i j := by
  classical
  set S : Finset (Fin N × Fin N) :=
    (collClass γ t₀ i₀ ×ˢ Finset.univ).filter (fun p => p.2 ∉ collClass γ t₀ i₀) with hSdef
  have hS : ∀ i j : Fin N, (i, j) ∈ S ↔
      (i ∈ collClass γ t₀ i₀ ∧ j ∉ collClass γ t₀ i₀) := by
    intro i j
    rw [hSdef, Finset.mem_filter, Finset.mem_product]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, Finset.mem_univ j⟩, h.2⟩⟩
  obtain ⟨ν, hνpos, hν⟩ : ∃ ν > 0, ∀ i ∈ collClass γ t₀ i₀, ∀ j ∉ collClass γ t₀ i₀,
      ν ≤ r (γ t₀) i j := by
    have hpos : ∀ p ∈ S, 0 < r (γ t₀) p.1 p.2 := by
      intro p hp
      obtain ⟨h1, h2⟩ := (hS p.1 p.2).mp hp
      rw [r_eq_norm_sub]
      refine norm_pos_iff.mpr (sub_ne_zero.mpr fun h => h2 ?_)
      rw [mem_collClass]
      exact h.symm.trans (collClass_eq_of_mem h1)
    by_cases hSne : S.Nonempty
    · obtain ⟨p, hp, hpmin⟩ := Finset.exists_min_image S (fun p => r (γ t₀) p.1 p.2) hSne
      refine ⟨r (γ t₀) p.1 p.2, hpos p hp, fun i hi j hj => hpmin (i, j) ((hS i j).mpr ⟨hi, hj⟩)⟩
    · exact ⟨1, one_pos, fun i hi j hj => absurd ⟨(i, j), (hS i j).mpr ⟨hi, hj⟩⟩ hSne⟩
  have hcontAt : ContinuousAt γ t₀ := hcont.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  have hcontp : ∀ p : Fin N × Fin N, ContinuousAt (fun t => r (γ t) p.1 p.2) t₀ := by
    intro p
    have h1 : ContinuousAt (fun t : ℝ => γ t p.1) t₀ :=
      ((PiLp.continuous_apply 2 (fun _ : Fin N => E) p.1).continuousAt).comp hcontAt
    have h2 : ContinuousAt (fun t : ℝ => γ t p.2) t₀ :=
      ((PiLp.continuous_apply 2 (fun _ : Fin N => E) p.2).continuousAt).comp hcontAt
    have hfun : (fun t : ℝ => r (γ t) p.1 p.2) = fun t : ℝ => ‖γ t p.1 - γ t p.2‖ := by
      funext t; rw [r_eq_norm_sub]
    rw [hfun]
    exact (h1.sub h2).norm
  have hev : ∀ᶠ t in 𝓝 t₀, ∀ p ∈ S, ν / 2 ≤ r (γ t) p.1 p.2 := by
    refine (Finset.eventually_all S).mpr fun p hp => ?_
    obtain ⟨h1, h2⟩ := (hS p.1 p.2).mp hp
    filter_upwards [(hcontp p).eventually (eventually_ge_nhds
      (show ν / 2 < r (γ t₀) p.1 p.2 from by linarith [hν p.1 h1 p.2 h2]))] with t ht
    exact ht
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff_ball.mp hev
  set ε' : ℝ := min ε (min (t₀ - a) (b - t₀)) / 2 with hε'def
  have hε'pos : 0 < ε' := by
    rw [hε'def]
    exact div_pos (lt_min hεpos (lt_min (by linarith [ht₀.1]) (by linarith [ht₀.2]))) (by norm_num)
  refine ⟨ν / 2, by linarith, ε', hε'pos, ?_⟩
  intro t ht i hi j hj
  have hε'le : ε' ≤ ε := by
    rw [hε'def]
    have h1 : min ε (min (t₀ - a) (b - t₀)) ≤ ε := min_le_left _ _
    linarith
  have hball : t ∈ Metric.ball t₀ ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1, hε'le], by linarith [ht.2, hε'le]⟩
  exact hε t hball (i, j) ((hS i j).mpr ⟨hi, hj⟩)

/-- **The inertia of a collision class tends to `0` at the collision time.** -/
lemma tendsto_clusterInertia_collClass {m : Fin N → ℝ} {γ : ℝ → EN E N} {t₀ : ℝ} {i₀ : Fin N}
    (hmk : clusterMass m (collClass γ t₀ i₀) ≠ 0) (hγ : ContinuousAt γ t₀) :
    Tendsto (fun t : ℝ => clusterInertia m (collClass γ t₀ i₀) (γ t)) (𝓝 t₀) (𝓝 0) := by
  have h := (continuous_clusterInertia m (collClass γ t₀ i₀)).continuousAt.tendsto.comp hγ
  rw [clusterInertia_collClass_eq_zero hmk] at h
  exact h

/-- The same, one-sided at `0⁺` for the shifted curve `u ↦ γ (t₀ + u)`. -/
lemma tendsto_clusterInertia_collClass_shift {m : Fin N → ℝ} {γ : ℝ → EN E N} {t₀ : ℝ}
    {i₀ : Fin N} (hmk : clusterMass m (collClass γ t₀ i₀) ≠ 0)
    (hγ : ContinuousAt γ t₀) :
    Tendsto (fun u : ℝ => clusterInertia m (collClass γ t₀ i₀) (shiftCurve γ t₀ u))
      (nhdsWithin (0:ℝ) (Ioi 0)) (𝓝 0) := by
  have h1 : Tendsto (fun u : ℝ => t₀ + u) (nhdsWithin (0:ℝ) (Ioi 0)) (𝓝 t₀) := by
    have a : Tendsto (fun _ : ℝ => t₀) (nhdsWithin (0:ℝ) (Ioi 0)) (𝓝 t₀) := tendsto_const_nhds
    have b : Tendsto (fun u : ℝ => u) (nhdsWithin (0:ℝ) (Ioi 0)) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    simpa using a.add b
  exact (tendsto_clusterInertia_collClass hmk hγ).comp h1

end Submission.NBody
