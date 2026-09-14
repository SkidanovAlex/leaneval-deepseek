import Submission.NBody.MarchalSeqGlue
import Submission.NBody.MarchalSeqIntegrable
import Submission.NBody.MarchalSeqTransfer
import Submission.NBody.MarchalSeqBump
import Submission.NBody.MarchalStdVarGeometry
import Submission.Commons.Analysis.Asymptotic.eventually_rpow_one_third_mul_add_rpow_five_thirds_mul_neg

/-!
# The window bound along the blow-up sequence

For one *side* of the collision (`x = shiftCurve γ t₀`, so that the collision sits at the origin of
the rescaled time) the transfer identity `bump_real_action_eq` gives

  `∫_{t₀}^{t₀+λT} (L(γ̃) - L(γ)) = λ^{1/3} · J(λ) + λ · W(λ)`

with `J(λ)` the rescaled (kinetic + cluster potential) difference and `W(λ)` the interaction
potential difference.  This file records

* `J(λ_n) → modelDiff m k i₀ κ s̄ T δ`  (the sequential transfer plus the transfer glue), and
* `λ_n · W(λ_n) ≤ λ_n^{5/3} · restBound`  (the interaction potential is `O(λ^{2/3})`),

so that the whole window integral is `≤ λ_n^{1/3} · K n + λ_n^{5/3} · restBound` with
`K n → modelDiff m k i₀ κ s̄ T δ`.
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

/-- The bound for the interaction-potential difference of the bump, in the normalisation used by the
window estimate. -/
noncomputable def restBound (m : Fin N → ℝ) (k : Finset (Fin N)) (δ : E) (T ν : ℝ) : ℝ :=
  2 * T * ‖δ‖ * (∑ p ∈ (pairFinset N).filter
      (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)), m p.1 * m p.2) / ν ^ 2

/-- **The window bound for one side of the collision.** -/
theorem seq_action_window_bound
    {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {h : ℝ}
    {k : Finset (Fin N)} {i₀ : Fin N} (hi₀ : i₀ ∈ k) (hk2 : 2 ≤ k.card)
    {δ : E} (hδ : δ ≠ 0)
    {γ : ℝ → EN E N} {t₀ T : ℝ} (hT : 0 < T) (hδT : 2 * ‖δ‖ ≤ T)
    {κ : ℝ} (hκ : 0 < κ) {sbar : EN E N}
    (hsbarnc : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → sbar i ≠ sbar j)
    (hgood : ∀ j ∈ k.erase i₀, (inner ℝ (sbar i₀ - sbar j) δ) ^ 2
      < ‖sbar i₀ - sbar j‖ ^ 2 * ‖δ‖ ^ 2)
    {lam : ℕ → ℝ} (hlampos : ∀ n, 0 < lam n) (hlamT : Tendsto lam atTop (nhds 0))
    {ε C Cv ν Cd : ℝ} (hε : 0 < ε) (hC : 0 < C) (hν : 0 < ν) (hCv : 0 ≤ Cv) (hCd : 0 < Cd)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (shiftCurve γ t₀ t))
    (hE : ∀ t ∈ Ioo (0:ℝ) ε,
      |clusterRelEnergy m k (shiftCurve γ t₀ t) (deriv (shiftCurve γ t₀) t)| ≤ C)
    (hW : ∀ t ∈ Ioo (0:ℝ) ε,
      |crossWork m k (shiftCurve γ t₀ t) (cmRel m k (shiftCurve γ t₀ t))| ≤ C)
    (hder : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (shiftCurve γ t₀) (deriv (shiftCurve γ t₀) t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε,
      HasDerivAt (deriv (shiftCurve γ t₀)) (iteratedDeriv 2 (shiftCurve γ t₀) t) t)
    (hd3 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv (shiftCurve γ t₀)))
      (deriv (deriv (deriv (shiftCurve γ t₀))) t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε,
      iteratedDeriv 2 (shiftCurve γ t₀) t = ∇_[m] (U m) (shiftCurve γ t₀ t))
    (hsepU : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparatedWeak k (shiftCurve γ t₀ t) ν)
    (hvU : ∀ t ∈ Ioo (0:ℝ) ε, ∀ j ∉ k,
      ‖deriv (shiftCurve γ t₀) t j‖ ≤ Cv * Real.sqrt (clusterPotential m k (shiftCurve γ t₀ t)))
    (hI0 : Tendsto (fun t : ℝ => clusterInertia m k (shiftCurve γ t₀ t))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    (hIn : Tendsto (fun s : ℝ => clusterInertia m k (shiftCurve γ t₀ s) / s ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hUlim : Tendsto (fun s : ℝ => clusterPotential m k (shiftCurve γ t₀ s) * s ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((2:ℝ)/9 * κ)))
    (hDn : Tendsto (fun s : ℝ => deriv (fun u : ℝ => clusterInertia m k (shiftCurve γ t₀ u)) s
        / s ^ ((1:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/3 * κ)))
    (hts : Tendsto (fun u : ℝ => u • deriv (fun u : ℝ => clusterShape m k (shiftCurve γ t₀ u)) u)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    (hseqUG : ∀ t₁ ∈ Ioo (0:ℝ) T, ∀ η > (0:ℝ), ∀ᶠ n in atTop, ∀ t ∈ Ioc t₁ T,
      ‖clusterShape m k (shiftCurve γ t₀ (t * lam n)) - sbar‖ < η)
    (hac : ∀ᶠ n in atTop, AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam n * T)) :
    ∃ K : ℕ → ℝ, Tendsto K atTop (nhds (modelDiff m k i₀ κ sbar T δ)) ∧
      ∀ᶠ n in atTop,
        ∫ t in t₀..(t₀ + lam n * T),
          (lagR m h (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
              (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t)
            - lagR m h (γ t) (deriv γ t))
        ≤ (lam n) ^ ((1:ℝ)/3) * K n + (lam n) ^ ((5:ℝ)/3) * restBound m k δ T ν := by
  classical
  have hlam0 : Tendsto lam atTop (nhdsWithin (0:ℝ) (Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlamT, Filter.Eventually.of_forall hlampos⟩
  -- smallness of the sequence
  have hεlam : ∀ᶠ n in atTop, lam n < ε / T :=
    hlamT.eventually (eventually_lt_nhds (div_pos hε hT))
  have hsmall : ∀ᶠ n in atTop, 4 * (lam n ^ ((2:ℝ)/3) * ‖δ‖) ≤ ν := by
    have hpow : Tendsto (fun n => lam n ^ ((2:ℝ)/3)) atTop (nhds 0) :=
      hlamT.rpow_const_nhds_zero (by norm_num)
    have hpos : (0:ℝ) < ν / (4 * ‖δ‖) :=
      div_pos hν (mul_pos (by norm_num) (norm_pos_iff.mpr hδ))
    filter_upwards [hpow.eventually (eventually_lt_nhds hpos)] with n hn
    have h2 : lam n ^ ((2:ℝ)/3) * ‖δ‖ < ν / 4 := by
      calc lam n ^ ((2:ℝ)/3) * ‖δ‖ < (ν / (4 * ‖δ‖)) * ‖δ‖ :=
            mul_lt_mul_of_pos_right hn (norm_pos_iff.mpr hδ)
        _ = ν / 4 := by field_simp
    linarith
  -- (1)  the potential bound along the sequence
  have hp1 := seq_potential_bound (m := m) (k := k) (x := shiftCurve γ t₀) (κ := κ)
    (T := T) hκ hT hUlim hlam0
  -- (2)  the pair upper bound
  obtain ⟨Cup, hCuppos, hUp⟩ := seq_pair_upper_bound (m := m) (k := k) (x := shiftCurve γ t₀)
    (κ := κ) (ε := ε) (T := T) hm hk2 hκ hε hT hnc hIn hlam0
  -- (3)  the threshold and the uniform blow-up
  set t₁ : ℝ := min (T / 2) ((‖δ‖ / (2 * Cup)) ^ ((3:ℝ)/2)) with ht₁def
  have ht₁pos : 0 < t₁ := by
    rw [ht₁def]
    exact lt_min (by linarith) (Real.rpow_pos_of_pos (div_pos (norm_pos_iff.mpr hδ) (by linarith)) _)
  have ht₁T : t₁ ≤ T / 2 := by rw [ht₁def]; exact min_le_left _ _
  have hd₁ : Cup * t₁ ^ ((2:ℝ)/3) ≤ ‖δ‖ / 2 := by
    have ht₁2 : t₁ ≤ (‖δ‖ / (2 * Cup)) ^ ((3:ℝ)/2) := by rw [ht₁def]; exact min_le_right _ _
    have hnn : 0 < ‖δ‖ / (2 * Cup) := div_pos (norm_pos_iff.mpr hδ) (by linarith)
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
  have hseqS : ∀ t ∈ Ioc (0:ℝ) T,
      Tendsto (fun n => clusterShape m k (shiftCurve γ t₀ (t * lam n))) atTop (nhds sbar) := by
    intro t ht
    have ht2 : t / 2 ∈ Ioo (0:ℝ) T := ⟨by linarith [ht.1], by linarith [ht.2, hT]⟩
    have hle : t ∈ Ioc (t / 2) T := ⟨by linarith [ht.1], ht.2⟩
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hseqUG (t / 2) ht2 η hη)
    exact ⟨N, fun n hn => by simpa [dist_eq_norm] using hN n hn t hle⟩
  -- (4)  the bumped pair lower bound and its consequences
  obtain ⟨cb, hcbpos, hblow⟩ := seq_bumped_pair_lower (m := m) (k := k) (x := shiftCurve γ t₀)
    (κ := κ) (ε := ε) (T := T) (Cu := Cup) (t₁ := t₁) (sbar := sbar) (i₀ := i₀) (δ := δ)
    hm hk2 hδ hκ hε hT hδT hi₀ hnc hIn (by positivity : (0:ℝ) < (2:ℝ)/9 * κ + 1) hCuppos
    ht₁pos ht₁T hd₁ hlam0 hp1 hUp hseqU hgood
  have hp2 := seq_bumped_potential_bound (m := m) (k := k) (x := shiftCurve γ t₀) (i₀ := i₀)
    (δ := δ) (T := T) (c := cb) (fun i => (hm i).le) hT hcbpos hblow
  have hnnB := seq_bumped_noColl (m := m) (k := k) (x := shiftCurve γ t₀) (i₀ := i₀)
    (δ := δ) (T := T) (c := cb) hT hcbpos hblow
  -- (5)  the sequential transfer
  have hconv := tendsto_rescaledCentered_seq (m := m) (k := k) (x := shiftCurve γ t₀)
    (ε := ε) (κ := κ) (T := T) (sbar := sbar) hm hk2 hε hκ hnc hIn hlam0 hseqS
  have hconvd := tendsto_deriv_rescaledCentered_seq (m := m) (k := k) (x := shiftCurve γ t₀)
    (ε := ε) (κ := κ) (T := T) (sbar := sbar) hm hk2 hε hκ hnc hder hd2 hode hIn hDn hts hlam0 hseqS
  obtain ⟨Cdv, hCdvpos, hdv⟩ := seq_vel_bound (m := m) (k := k) (x := shiftCurve γ t₀)
    (ε := ε) (C := C) (ν := ν) (Cv := Cv) (T := T) hm hk2 hε hC hν hCv hT hnc hE hW hder hd2 hd3
    hode hsepU hvU hI0 hlam0
  -- measurability of the rescaled configurations
  have hmeasq : ∀ᶠ n in atTop, AEStronglyMeasurable
      (rescaledCentered m k (shiftCurve γ t₀) (lam n)) (volume.restrict (Ioc (0:ℝ) T)) := by
    filter_upwards [hεlam] with n hn
    have hcont : ContinuousOn (shiftCurve γ t₀) (Ioo (0:ℝ) ε) :=
      fun s hs => (hder s hs).continuousAt.continuousWithinAt
    have hcont2 : ContinuousOn (fun t : ℝ => shiftCurve γ t₀ (t * lam n)) (Ioo (0:ℝ) T) :=
      hcont.comp (by fun_prop) fun t ht => ⟨mul_pos ht.1 (hlampos n), by
        have h1 : t * lam n ≤ T * lam n := mul_le_mul_of_nonneg_right (le_of_lt ht.2) (hlampos n).le
        have h2 : T * lam n < T * (ε / T) := mul_lt_mul_of_pos_left hn hT
        have h3 : T * (ε / T) = ε := by field_simp
        linarith⟩
    have hcont3 : ContinuousOn (rescaledCentered m k (shiftCurve γ t₀) (lam n)) (Ioo (0:ℝ) T) := by
      have h2 : ContinuousOn (fun t : ℝ => cmRel m k (shiftCurve γ t₀ (t * lam n)))
          (Ioo (0:ℝ) T) := (cmRelL m k).continuous.comp_continuousOn hcont2
      have h3 := h2.const_smul (lam n ^ (-(2:ℝ)/3))
      have h4 : (lam n ^ (-(2:ℝ)/3) • fun t : ℝ => cmRel m k (shiftCurve γ t₀ (t * lam n)))
          = rescaledCentered m k (shiftCurve γ t₀) (lam n) := by
        funext t
        rw [Pi.smul_apply, rescaledCentered]
      rw [h4] at h3
      exact h3
    have h1 : AEStronglyMeasurable (rescaledCentered m k (shiftCurve γ t₀) (lam n))
        (volume.restrict (Ioo (0:ℝ) T)) := hcont3.aestronglyMeasurable measurableSet_Ioo
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact h1
  have hfnc2 : ∀ t ∈ Ioc (0:ℝ) T, ClusterNoColl k
      (blowUpProfile κ sbar t + stdVarVec m k i₀ δ T t) :=
    clusterNoColl_blowUpProfile_add_stdVarVec hi₀ hκ sbar hδ hsbarnc hgood
  -- the model-side integrability (for the glue)
  have hintModel : ∀ j ∈ k.erase i₀, IntervalIntegrable (fun t : ℝ =>
      (‖(Real.sqrt κ * t ^ ((2:ℝ)/3)) • (sbar i₀ - sbar j) + stdVar δ T t‖)⁻¹
        - (Real.sqrt κ * t ^ ((2:ℝ)/3) * ‖sbar i₀ - sbar j‖)⁻¹) volume 0 T :=
    intervalIntegrable_potPairVal_of_good (m := m) (k := k) (i₀ := i₀) hκ hT.le sbar hδ hgood
  have hmeasf : AEStronglyMeasurable (stdVarVec m k i₀ δ T) (volume.restrict (Ioc (0:ℝ) T)) := by
    have hcont : Continuous (stdVarVec m k i₀ δ T) := by
      have h1 : Continuous (stdCoef δ T) :=
        continuous_const.min (continuous_const.max (by fun_prop))
      exact h1.smul continuous_const
    exact hcont.aestronglyMeasurable
  have hmeasf' : AEStronglyMeasurable (stdVarVecDeriv m k i₀ δ T)
      (volume.restrict (Ioc (0:ℝ) T)) := by
    have h : Measurable (fun s : ℝ => if s ≤ T - ‖δ‖ then (0 : EN E N)
        else (-(‖δ‖)⁻¹) • stdPertVec m k i₀ δ) :=
      Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const measurable_const
    exact h.aestronglyMeasurable
  -- the transfer
  have htrans := tendsto_transfer_of_data_seq (m := m) (k := k) (x := shiftCurve γ t₀)
    (κ := κ) (T := T) (sbar := sbar) (f := stdVarVec m k i₀ δ T)
    (f' := stdVarVecDeriv m k i₀ δ T) (lam := lam) hm hκ hT hsbarnc hconv hconvd hmeasq
    hmeasf hmeasf' hCdvpos (mul_nonneg (weightedNorm_nonneg m _) (inv_nonneg.mpr (norm_nonneg δ)))
    hdv (fun t => weightedNorm_stdVarVecDeriv_le (m := m) (k := k) (i₀ := i₀) hm hδ T t)
    hfnc2 hp1 hp2
  have hIlim : Tendsto (fun n => ∫ s in (0:ℝ)..T,
      (massInner m (deriv (rescaledCentered m k (shiftCurve γ t₀) (lam n)) s)
          (stdVarVecDeriv m k i₀ δ T s)
        + (1/2) * ‖stdVarVecDeriv m k i₀ δ T s‖_[m] ^ 2
        + clusterPotential m k (rescaledCentered m k (shiftCurve γ t₀) (lam n) s
            + stdVarVec m k i₀ δ T s)
        - clusterPotential m k (rescaledCentered m k (shiftCurve γ t₀) (lam n) s)))
      atTop (nhds (modelDiff m k i₀ κ sbar T δ)) := by
    rw [← modelDiff_eq_transfer_integrand_deriv hm hi₀ hκ hT.le sbar hδ hintModel] at htrans
    exact htrans
  have hmain : ∀ᶠ n in atTop,
      ∫ t in t₀..(t₀ + lam n * T),
        (lagR m h (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
            (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t)
          - lagR m h (γ t) (deriv γ t))
      ≤ (lam n) ^ ((1:ℝ)/3) *
          (∫ s in (0:ℝ)..T,
            (massInner m (deriv (rescaledCentered m k (shiftCurve γ t₀) (lam n)) s)
                (stdVarVecDeriv m k i₀ δ T s)
              + (1/2) * ‖stdVarVecDeriv m k i₀ δ T s‖_[m] ^ 2
              + clusterPotential m k (rescaledCentered m k (shiftCurve γ t₀) (lam n) s
                  + stdVarVec m k i₀ δ T s)
              - clusterPotential m k (rescaledCentered m k (shiftCurve γ t₀) (lam n) s)))
        + (lam n) ^ ((5:ℝ)/3) * restBound m k δ T ν := by
    filter_upwards [hac, hsmall, hnnB, hp1, hp2, hdv, hεlam,
      Filter.Eventually.of_forall hlampos] with n hacn hsmalln hnnBn hp1n hp2n hdvn hεn hposn
    -- the collision-freeness of the strip, in the `Ioo t₀ (t₀ + λT)` form
    have hncI : ∀ t ∈ Ioo t₀ (t₀ + lam n * T), WithoutCollisions (γ t) := by
      intro t ht
      have hεT : lam n * T < ε := by
        have h3 : lam n * T < (ε / T) * T := mul_lt_mul_of_pos_right hεn hT
        have h4 : (ε / T) * T = ε := by field_simp
        linarith
      have h1 : t - t₀ ∈ Ioo (0:ℝ) ε := ⟨by linarith [ht.1], by linarith [ht.2, hεT]⟩
      have := hnc (t - t₀) h1
      simpa only [shiftCurve_apply, add_sub_cancel] using this
    have hsepn : ∀ t ∈ Ioc (0:ℝ) T, ClusterSeparatedWeak k (γ (t₀ + lam n * t)) ν := by
      intro t ht
      have hεT : lam n * T < ε := by
        have h3 : lam n * T < (ε / T) * T := mul_lt_mul_of_pos_right hεn hT
        have h4 : (ε / T) * T = ε := by field_simp
        linarith
      have h2 : lam n * t ≤ lam n * T := mul_le_mul_of_nonneg_left ht.2 hposn.le
      exact hsepU (lam n * t) ⟨mul_pos hposn ht.1, by linarith⟩
    -- the integrability of the six pieces
    set Cp2 : ℝ := ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k),
      m p.1 * m p.2 / cb with hCp2def
    have hCp2nn : 0 ≤ Cp2 := by
      rw [hCp2def]
      exact Finset.sum_nonneg fun p hp => div_nonneg (mul_nonneg (hm _).le (hm _).le) hcbpos.le
    obtain ⟨h1i, h2i, h3i, h4i, h56i⟩ := bump_pieces_intervalIntegrable_good (m := m) (k := k)
      (i₀ := i₀) hm hi₀ hδ hposn hT hacn hncI (le_of_lt hCdvpos)
      (by positivity : (0:ℝ) ≤ (2:ℝ)/9 * κ + 1)
      hCp2nn hν hdvn hp1n (by simpa only [bumpRescaled] using hnnBn)
      (by simpa only [hCp2def, bumpRescaled] using hp2n)
      hsepn hsmalln
    -- the transfer identity
    have hact := bump_real_action_eq_diff (m := m) (h := h) hm hi₀ hδ hposn hT hacn h1i h2i h3i h4i h56i
    -- the bridge between `deriv (stdVarVec _)` and `stdVarVecDeriv`
    have hA : (∫ s in (0:ℝ)..T,
          massInner m (deriv (bumpRescaled m k γ t₀ (lam n)) s) (deriv (stdVarVec m k i₀ δ T) s))
        = (∫ s in (0:ℝ)..T,
          massInner m (deriv (rescaledCentered m k (shiftCurve γ t₀) (lam n)) s)
            (stdVarVecDeriv m k i₀ δ T s)) := by
      refine intervalIntegral.integral_congr_ae ?_
      rw [Set.uIoc_of_le hT.le]
      exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mp (by
        filter_upwards [deriv_stdVarVec_ae m k i₀ δ T hδ] with s hs
        rw [hs]
        rfl)
    have hB : (∫ s in (0:ℝ)..T, ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2)
        = (∫ s in (0:ℝ)..T, ‖stdVarVecDeriv m k i₀ δ T s‖_[m] ^ 2) := by
      refine intervalIntegral.integral_congr_ae ?_
      rw [Set.uIoc_of_le hT.le]
      exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mp (by
        filter_upwards [deriv_stdVarVec_ae m k i₀ δ T hδ] with s hs
        rw [hs])
    -- the splitting of the model integral
    have hcongr2 : (∫ s in (0:ℝ)..T,
          (massInner m (deriv (rescaledCentered m k (shiftCurve γ t₀) (lam n)) s)
              (stdVarVecDeriv m k i₀ δ T s)
            + (1/2) * ‖stdVarVecDeriv m k i₀ δ T s‖_[m] ^ 2
            + clusterPotential m k (rescaledCentered m k (shiftCurve γ t₀) (lam n) s
                + stdVarVec m k i₀ δ T s)
            - clusterPotential m k (rescaledCentered m k (shiftCurve γ t₀) (lam n) s)))
        = (∫ s in (0:ℝ)..T,
          (massInner m (deriv (bumpRescaled m k γ t₀ (lam n)) s) (deriv (stdVarVec m k i₀ δ T) s)
            + (1/2) * ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2
            + clusterPotential m k (bumpRescaled m k γ t₀ (lam n) s + stdVarVec m k i₀ δ T s)
            - clusterPotential m k (bumpRescaled m k γ t₀ (lam n) s))) := by
      refine intervalIntegral.integral_congr_ae ?_
      rw [Set.uIoc_of_le hT.le]
      exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mp (by
        filter_upwards [deriv_stdVarVec_ae m k i₀ δ T hδ] with s hs
        rw [hs]
        rfl)
    have hsplit : (∫ s in (0:ℝ)..T,
          (massInner m (deriv (rescaledCentered m k (shiftCurve γ t₀) (lam n)) s)
              (stdVarVecDeriv m k i₀ δ T s)
            + (1/2) * ‖stdVarVecDeriv m k i₀ δ T s‖_[m] ^ 2
            + clusterPotential m k (rescaledCentered m k (shiftCurve γ t₀) (lam n) s
                + stdVarVec m k i₀ δ T s)
            - clusterPotential m k (rescaledCentered m k (shiftCurve γ t₀) (lam n) s)))
        = (∫ s in (0:ℝ)..T, massInner m
              (deriv (rescaledCentered m k (shiftCurve γ t₀) (lam n)) s) (stdVarVecDeriv m k i₀ δ T s))
          + (1/2) * (∫ s in (0:ℝ)..T, ‖stdVarVecDeriv m k i₀ δ T s‖_[m] ^ 2)
          + ((∫ s in (0:ℝ)..T, clusterPotential m k (rescaledCentered m k (shiftCurve γ t₀) (lam n) s
                + stdVarVec m k i₀ δ T s))
            - (∫ s in (0:ℝ)..T, clusterPotential m k
                (rescaledCentered m k (shiftCurve γ t₀) (lam n) s))) := by
      rw [hcongr2, integral_lagrange_eq (q := bumpRescaled m k γ t₀ (lam n)) h1i h2i (h3i.sub h4i),
        intervalIntegral.integral_sub h3i h4i, hA, hB]
      rfl
    -- the interaction potential bound
    have hrest : (∫ s in (0:ℝ)..T, (clusterPotentialRest m k
          (bumpCurve m k i₀ δ T (lam n) t₀ γ (t₀ + lam n * s))
        - clusterPotentialRest m k (γ (t₀ + lam n * s))))
        ≤ (lam n) ^ ((2:ℝ)/3) * restBound m k δ T ν := by
      have hpoint : ∀ s ∈ Set.Ioc (0:ℝ) T, clusterPotentialRest m k
          (bumpCurve m k i₀ δ T (lam n) t₀ γ (t₀ + lam n * s))
          - clusterPotentialRest m k (γ (t₀ + lam n * s))
          ≤ (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
              m p.1 * m p.2) * (2 * (lam n ^ ((2:ℝ)/3) * ‖δ‖) / ν ^ 2) :=
        fun s hs => clusterPotentialRest_bump_le hm hi₀ hν hposn hT
          hsepn (by linarith [hsmalln]) hs
      have hb := intervalIntegral.integral_mono_on_of_le_Ioo (f := fun s : ℝ => clusterPotentialRest m k
          (bumpCurve m k i₀ δ T (lam n) t₀ γ (t₀ + lam n * s))
          - clusterPotentialRest m k (γ (t₀ + lam n * s)))
        (g := fun _ : ℝ => (∑ p ∈ (pairFinset N).filter
            (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)), m p.1 * m p.2)
            * (2 * (lam n ^ ((2:ℝ)/3) * ‖δ‖) / ν ^ 2))
        hT.le h56i intervalIntegrable_const
        (fun s hs => hpoint s ⟨hs.1, le_of_lt hs.2⟩)
      rw [intervalIntegral.integral_const, sub_zero] at hb
      refine hb.trans (le_of_eq ?_)
      rw [restBound]
      ring
    -- assembly
    rw [hact, hA, hB, show bumpRescaled m k γ t₀ (lam n)
        = rescaledCentered m k (shiftCurve γ t₀) (lam n) from rfl, ← hsplit]
    have hkey : lam n * (∫ s in (0:ℝ)..T, (clusterPotentialRest m k
          (bumpCurve m k i₀ δ T (lam n) t₀ γ (t₀ + lam n * s))
        - clusterPotentialRest m k (γ (t₀ + lam n * s))))
        ≤ (lam n) ^ ((5:ℝ)/3) * restBound m k δ T ν := by
      have h1 : (0:ℝ) < lam n := hposn
      have h2 : lam n * lam n ^ ((2:ℝ)/3) = lam n ^ ((5:ℝ)/3) := by
        have h3 : lam n * lam n ^ ((2:ℝ)/3) = lam n ^ (1:ℝ) * lam n ^ ((2:ℝ)/3) := by
          rw [Real.rpow_one]
        rw [h3, ← Real.rpow_add h1]
        norm_num
      calc lam n * (∫ s in (0:ℝ)..T, (clusterPotentialRest m k
              (bumpCurve m k i₀ δ T (lam n) t₀ γ (t₀ + lam n * s))
            - clusterPotentialRest m k (γ (t₀ + lam n * s))))
          ≤ lam n * ((lam n) ^ ((2:ℝ)/3) * restBound m k δ T ν) :=
            mul_le_mul_of_nonneg_left hrest h1.le
        _ = (lam n) ^ ((5:ℝ)/3) * restBound m k δ T ν := by
            rw [← mul_assoc, h2]
    linarith [hkey]
  exact ⟨fun n => ∫ s in (0:ℝ)..T,
      (massInner m (deriv (rescaledCentered m k (shiftCurve γ t₀) (lam n)) s)
          (stdVarVecDeriv m k i₀ δ T s)
        + (1/2) * ‖stdVarVecDeriv m k i₀ δ T s‖_[m] ^ 2
        + clusterPotential m k (rescaledCentered m k (shiftCurve γ t₀) (lam n) s
            + stdVarVec m k i₀ δ T s)
        - clusterPotential m k (rescaledCentered m k (shiftCurve γ t₀) (lam n) s)),
      hIlim, hmain⟩

/-- **The two-sided window is strictly negative.**  Combining the two side estimates
`window_side ≤ λ^{1/3} K_side + λ^{5/3} W_side` with `K_R n + K_L n → M_R + M_L < 0` gives a
positive `λ` for which the total window integral is strictly negative and the window lies inside
`[a,b]`. -/
theorem exists_bump_window_negative_seq {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {h : ℝ}
    {γ : ℝ → EN E N} {a b t₀ T : ℝ} (hT : 0 < T) (ha : a < t₀) (hb : t₀ < b)
    {k : Finset (Fin N)} {i₀ : Fin N} {δ : E} (hδ : δ ≠ 0)
    {lam : ℕ → ℝ} (hlampos : ∀ n, 0 < lam n) (hlamT : Tendsto lam atTop (nhds 0))
    {KR KL : ℕ → ℝ} {MR ML WR WL : ℝ}
    (hKR : Tendsto KR atTop (nhds MR)) (hKL : Tendsto KL atTop (nhds ML))
    (hM : MR + ML < 0)
    (hR : ∀ᶠ n in atTop, (∫ t in t₀..(t₀ + lam n * T),
        (lagR m h (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
            (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t) - lagR m h (γ t) (deriv γ t)))
        ≤ (lam n) ^ ((1:ℝ)/3) * KR n + (lam n) ^ ((5:ℝ)/3) * WR)
    (hL : ∀ᶠ n in atTop, (∫ t in (t₀ - lam n * T)..t₀,
        (lagR m h (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
            (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t) - lagR m h (γ t) (deriv γ t)))
        ≤ (lam n) ^ ((1:ℝ)/3) * KL n + (lam n) ^ ((5:ℝ)/3) * WL)
    (hintR : ∀ᶠ n in atTop, IntervalIntegrable (fun t => lagR m h
        (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
        (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t) - lagR m h (γ t) (deriv γ t))
        volume t₀ (t₀ + lam n * T))
    (hintL : ∀ᶠ n in atTop, IntervalIntegrable (fun t => lagR m h
        (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
        (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t) - lagR m h (γ t) (deriv γ t))
        volume (t₀ - lam n * T) t₀) :
    ∃ lam > (0:ℝ), a ≤ t₀ - lam * T ∧ t₀ + lam * T ≤ b ∧
      ∫ t in (t₀ - lam * T)..(t₀ + lam * T),
        (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
            (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t) - lagR m h (γ t) (deriv γ t)) < 0 := by
  classical
  have hneg := Commons.Analysis.Asymptotic.eventually_rpow_one_third_mul_add_rpow_five_thirds_mul_neg
    (A := fun n => KR n + KL n) (lam := lam) (a := MR + ML) (W := WR + WL)
    (hKR.add hKL) hM hlamT hlampos
  have hcT : (0:ℝ) < min (t₀ - a) (b - t₀) / T :=
    div_pos (lt_min (by linarith) (by linarith)) hT
  have hsmall : ∀ᶠ n in atTop, lam n ≤ min (t₀ - a) (b - t₀) / T :=
    hlamT.eventually (eventually_le_nhds hcT)
  have hAll : ∀ᶠ n in atTop, lam n ≤ min (t₀ - a) (b - t₀) / T ∧
        (∫ t in t₀..(t₀ + lam n * T),
          (lagR m h (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
              (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t) - lagR m h (γ t) (deriv γ t)))
          ≤ (lam n) ^ ((1:ℝ)/3) * KR n + (lam n) ^ ((5:ℝ)/3) * WR ∧
        (∫ t in (t₀ - lam n * T)..t₀,
          (lagR m h (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
              (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t) - lagR m h (γ t) (deriv γ t)))
          ≤ (lam n) ^ ((1:ℝ)/3) * KL n + (lam n) ^ ((5:ℝ)/3) * WL ∧
        lam n ^ ((1:ℝ)/3) * (KR n + KL n) + lam n ^ ((5:ℝ)/3) * (WR + WL) < 0 ∧
        IntervalIntegrable (fun t => lagR m h (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
            (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t) - lagR m h (γ t) (deriv γ t))
          volume t₀ (t₀ + lam n * T) ∧
        IntervalIntegrable (fun t => lagR m h (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
            (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t) - lagR m h (γ t) (deriv γ t))
          volume (t₀ - lam n * T) t₀ := by
    filter_upwards [hsmall, hR, hL, hneg, hintR, hintL] with n h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨n, hnT, hn1, hn2, hn3, hIntR, hIntL⟩ := hAll.exists
  refine ⟨lam n, hlampos n, ?_, ?_, ?_⟩
  · have h1 : lam n * T ≤ min (t₀ - a) (b - t₀) := by
      have := mul_le_mul_of_nonneg_right hnT hT.le
      rwa [div_mul_cancel₀ _ hT.ne'] at this
    linarith [min_le_left (t₀ - a) (b - t₀)]
  · have h1 : lam n * T ≤ min (t₀ - a) (b - t₀) := by
      have := mul_le_mul_of_nonneg_right hnT hT.le
      rwa [div_mul_cancel₀ _ hT.ne'] at this
    linarith [min_le_right (t₀ - a) (b - t₀)]
  · rw [← intervalIntegral.integral_add_adjacent_intervals hIntL hIntR]
    refine lt_of_le_of_lt (add_le_add hn2 hn1) ?_
    have hsplit : lam n ^ ((1:ℝ)/3) * KL n + lam n ^ ((5:ℝ)/3) * WL
        + (lam n ^ ((1:ℝ)/3) * KR n + lam n ^ ((5:ℝ)/3) * WR)
        = lam n ^ ((1:ℝ)/3) * (KR n + KL n) + lam n ^ ((5:ℝ)/3) * (WR + WL) := by ring
    linarith [hn3, hsplit]

end Submission.NBody
