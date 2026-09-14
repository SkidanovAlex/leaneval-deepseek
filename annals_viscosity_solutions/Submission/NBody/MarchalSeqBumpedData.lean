import Submission.NBody.MarchalSeqWindow

/-!
# The bumped data along the blow-up sequence

`seq_action_window_bound` computes, on its way, the *geometric* data of the bumped rescaled
configuration: the bumped configuration is collision-free inside the cluster, and its cluster
potential is bounded by `Cp2 · t^{-2/3}`.  Those facts are also exactly the inputs of the finiteness
argument for the action of the bumped curve (`actionOn_bumpCurve_lt_top`), so we expose them here as
a standalone theorem.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The geometric data of the bumped configuration along the blow-up sequence.** -/
theorem seq_bumped_data {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)} {i₀ : Fin N}
    (hi₀ : i₀ ∈ k) (hk2 : 2 ≤ k.card) {δ : E} (hδ : δ ≠ 0)
    {γ : ℝ → EN E N} {t₀ T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) (hδT : 2 * ‖δ‖ ≤ T)
    {κ : ℝ} (hκ : 0 < κ) {sbar : EN E N}
    (hgood : ∀ j ∈ k.erase i₀,
      (inner ℝ (sbar i₀ - sbar j) δ) ^ 2 < ‖sbar i₀ - sbar j‖ ^ 2 * ‖δ‖ ^ 2)
    {lam : ℕ → ℝ} (hlampos : ∀ n, 0 < lam n)
    (hlamT : Tendsto lam atTop (nhds (0:ℝ)))
    (hs : Tendsto (fun n => clusterShape m k (shiftCurve γ t₀ (lam n))) atTop (nhds sbar))
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (shiftCurve γ t₀ t))
    (hIn : Tendsto (fun s : ℝ => clusterInertia m k (shiftCurve γ t₀ s) / s ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hUlim : Tendsto (fun s : ℝ => clusterPotential m k (shiftCurve γ t₀ s) * s ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((2:ℝ)/9 * κ)))
    (hseqUG : ∀ t₁ ∈ Ioo (0:ℝ) T, ∀ η > (0:ℝ), ∀ᶠ n in atTop, ∀ t ∈ Ioc t₁ T,
      ‖clusterShape m k (shiftCurve γ t₀ (t * lam n)) - sbar‖ < η) :
    ∃ Cp2 : ℝ, 0 < Cp2 ∧
      (∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T, clusterPotential m k
        (bumpRescaled m k γ t₀ (lam n) t + stdVarVec m k i₀ δ T t) ≤ Cp2 * t ^ (-(2:ℝ)/3)) ∧
      (∀ᶠ n in atTop, ∀ t ∈ Ioo (0:ℝ) T, ClusterNoColl k
        (bumpRescaled m k γ t₀ (lam n) t + stdVarVec m k i₀ δ T t)) := by
  classical
  have hδ0 : (0:ℝ) < ‖δ‖ := norm_pos_iff.mpr hδ
  have hlam0 : Tendsto lam atTop (nhdsWithin (0:ℝ) (Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlamT, Filter.Eventually.of_forall hlampos⟩
  have hp1 := seq_potential_bound (m := m) (k := k) (x := shiftCurve γ t₀) (κ := κ)
    (T := T) hκ hT hUlim hlam0
  obtain ⟨Cup, hCuppos, hUp⟩ := seq_pair_upper_bound (m := m) (k := k) (x := shiftCurve γ t₀)
    (κ := κ) (ε := ε) (T := T) hm hk2 hκ hε hT hnc hIn hlam0
  set t₁ : ℝ := min (T / 2) ((‖δ‖ / (2 * Cup)) ^ ((3:ℝ)/2)) with ht₁def
  have ht₁pos : 0 < t₁ := by
    rw [ht₁def]
    exact lt_min (by linarith) (Real.rpow_pos_of_pos (div_pos hδ0 (by linarith)) _)
  have ht₁T : t₁ ≤ T / 2 := by rw [ht₁def]; exact min_le_left _ _
  have hd₁ : Cup * t₁ ^ ((2:ℝ)/3) ≤ ‖δ‖ / 2 := by
    have ht₁2 : t₁ ≤ (‖δ‖ / (2 * Cup)) ^ ((3:ℝ)/2) := by rw [ht₁def]; exact min_le_right _ _
    have hnn : 0 < ‖δ‖ / (2 * Cup) := div_pos hδ0 (by linarith)
    have hpow : t₁ ^ ((2:ℝ)/3) ≤ ‖δ‖ / (2 * Cup) := by
      calc t₁ ^ ((2:ℝ)/3) ≤ ((‖δ‖ / (2 * Cup)) ^ ((3:ℝ)/2)) ^ ((2:ℝ)/3) :=
            Real.rpow_le_rpow ht₁pos.le ht₁2 (by norm_num)
        _ = ‖δ‖ / (2 * Cup) := by
            rw [← Real.rpow_mul hnn.le]
            norm_num
    calc Cup * t₁ ^ ((2:ℝ)/3) ≤ Cup * (‖δ‖ / (2 * Cup)) :=
          mul_le_mul_of_nonneg_left hpow hCuppos.le
      _ = ‖δ‖ / 2 := by field_simp
  have hseqU := hseqUG t₁ ⟨ht₁pos, by linarith⟩
  obtain ⟨cb, hcbpos, hblow⟩ := seq_bumped_pair_lower (m := m) (k := k) (x := shiftCurve γ t₀)
    (κ := κ) (ε := ε) (T := T) (Cu := Cup) (t₁ := t₁) (sbar := sbar) (i₀ := i₀) (δ := δ)
    hm hk2 hδ hκ hε hT hδT hi₀ hnc hIn (by positivity : (0:ℝ) < (2:ℝ)/9 * κ + 1) hCuppos
    ht₁pos ht₁T hd₁ hlam0 hp1 hUp hseqU hgood
  have hp2 := seq_bumped_potential_bound (m := m) (k := k) (x := shiftCurve γ t₀) (i₀ := i₀)
    (δ := δ) (T := T) (c := cb) (fun i => (hm i).le) hT hcbpos hblow
  have hnnB := seq_bumped_noColl (m := m) (k := k) (x := shiftCurve γ t₀) (i₀ := i₀)
    (δ := δ) (T := T) (c := cb) hT hcbpos hblow
  set Cp2 : ℝ := ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k),
      m p.1 * m p.2 / cb with hCp2def
  have hCp2pos : 0 < Cp2 := by
    rw [hCp2def]
    refine Finset.sum_pos ?_ ?_
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact div_pos (mul_pos (hm _) (hm _)) hcbpos
    · rw [Finset.filter_nonempty_iff]
      obtain ⟨i, hi⟩ : ∃ i, i ∈ k := by
        rcases Finset.eq_empty_or_nonempty k with h | ⟨i, hi⟩
        · rw [h] at hk2; simp at hk2
        · exact ⟨i, hi⟩
      obtain ⟨j, hj, hji⟩ : ∃ j ∈ k, j ≠ i := by
        by_contra hcon
        push Not at hcon
        have hsub : k ⊆ {i} := fun j hj => Finset.mem_singleton.mpr (hcon j hj)
        have := Finset.card_le_card hsub
        simp at this
        omega
      rcases lt_or_gt_of_ne hji with hlt | hgt
      · exact ⟨(j, i), ⟨by rw [pairFinset]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, hj, hi⟩⟩
      · exact ⟨(i, j), ⟨by rw [pairFinset]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩, hi, hj⟩⟩
  refine ⟨Cp2, hCp2pos, ?_, ?_⟩
  · filter_upwards [hp2] with n hn
    intro t ht
    rw [hCp2def]
    simpa only [bumpRescaled] using hn t ht
  · filter_upwards [hnnB] with n hn
    intro t ht
    simpa only [bumpRescaled] using hn t ht

end Submission.NBody
