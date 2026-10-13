import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.pointwise_ident
import Submission.Work.FTS.EllipticEst.AeI1Fts.zibp_cut
import Submission.Work.FTS.EllipticEst.AeI1Fts.slice_theta_ibp_cut
import Submission.Work.FTS.EllipticEst.AeI1Fts.iter_swap_compact
import Submission.Work.FTS.EllipticEst.AeI1Fts.cut_deriv_tendsto_zero
import Submission.Work.FTS.EllipticEst.AeI1Fts.N_bound
import Submission.Work.FTS.EllipticEst.SliceMixedAux.smoothCutoffIoo
import Submission.Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
import Submission.Work.FTS.EllipticEst.Dispatch.aeJointIntegrableF
import Submission.Work.FTS.EllipticEst.Dispatch.aeFirstEnergyDTools
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `I1Ae/RIFLimits` — the limiting bookkeeping of the `I₁` expansion identity

This module collects the analytic limits needed to pass from the two *cut-off* identities
(`I1Ae.zibpChain`, `I1Ae.thetaChain`) to the un-truncated expansion identity
`I1Ae.radialIdentityFts`:

* `tendsto_II_cut` — the generic dominated-convergence limit removing the radial cut-off
  `Work.FTS.EllipticEst.cut n`;
* `psideriv_tendsto_zero` — the vanishing, as `ε → 0⁺`, of the angular cut-off derivative term
  `∫_z w²χ_n ∫_θ σ ψ_ε'(θ) (U V)` (the "collar" term of the `θ`-integration by parts);  the
  proof uses that `σ = tan(2θ)²σ₂cos²(2θ)`, whence on the transition window of `ψ_ε`
  `∫ σ U² ≤ 16ε² ∫ σ₂cos²(2θ)U²`, so the `1/ε` of the derivative is beaten by the `ε` of the
  window.
* the four `n → ∞` limits and the four `ε → 0` limits of the individual terms.

-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.I1Ae

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "χ" => Work.FTS.EllipticEst.cut
local notation "ψ" => Work.FTS.EllipticEst.SliceMixedAux.cut

open Work.FTS.EllipticEst.AeI1Fts (U V Hh AA BB sigE sig1 sig2 II nuQ)

/-! ## The measure `nuQ` and its elementary properties -/

/-- Almost every point of `nuQ` lies in the open quadrant. -/
theorem ae_mem_nuQ : ∀ᵐ p ∂nuQ, p.1 ∈ Set.Ioi (0 : ℝ) ∧ p.2 ∈ Iθo := by
  rw [Work.FTS.EllipticEst.AeI1Fts.nuQ_eq]
  filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)]
    with p hp
  exact hp

/-- The `Dispatch` product measure agrees with `nuQ`. -/
theorem nuFts_eq_nuQ : Work.FTS.EllipticEst.Dispatch.nuFts = nuQ := by
  show (MeasureTheory.volume.restrict (Set.Ioi 0)).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) = nuQ
  unfold Work.FTS.EllipticEst.AeI1Fts.nuQ
  congr 1
  exact (MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc' (measure_singleton (0 : ℝ))
      (measure_singleton (Real.pi / 2)))).symm

/-- **Joint integrability of `w²f²σ`.**  For `f` of class `C^∞` on the open quadrant and
honestly in `ℋ⁰`, the quadratic integrand `w²f²σ` is integrable for the product measure
`nuQ`;  this is `HkIntegrand α 0 f` rewritten. -/
theorem integrable_w2_sig_sq {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 0 f) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (f p.1 p.2) ^ 2 * sigE p.2) nuQ := by
  have h := Work.FTS.EllipticEst.Dispatch.integrable_HkIntegrand_of_smoothOpen hf hm
  rw [nuFts_eq_nuQ] at h
  refine h.congr ?_
  filter_upwards [ae_mem_nuQ] with p hp
  have hIθ : p.2 ∈ Work.Spaces.Iθ := ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩
  rw [Work.FTS.EllipticEst.AeI1Fts.hkIntegrand_zero_eq_of_mem α f hIθ]
  ring

/-! ## The generic radial cut-off limit -/

/-- **Removing the radial cut-off.**  For an `L¹(nuQ)` function `f`,

`∫_z ∫_θ χ_n(z) f(z,θ) → ∫_z ∫_θ f(z,θ)`,

by dominated convergence (`0 ≤ χ_n ≤ 1`, `χ_n → 1` pointwise on `z > 0`). -/
theorem tendsto_II_cut {f : ℝ → ℝ → ℝ}
    (hf : MeasureTheory.Integrable (fun p : ℝ × ℝ => f p.1 p.2) nuQ) :
    Filter.Tendsto (fun n : ℕ => ∫ z in Set.Ioi (0 : ℝ), ∫ θ in Iθo, χ n z * f z θ)
      Filter.atTop
      (nhds (∫ z in Set.Ioi (0 : ℝ), ∫ θ in Iθo, f z θ)) := by
  obtain ⟨K, hKpos, hKbd, hKone, hKlim⟩ := Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
  -- ## the family is integrable on `nuQ`
  have hFint : ∀ n : ℕ, MeasureTheory.Integrable
      (fun p : ℝ × ℝ => χ n p.1 * f p.1 p.2) nuQ := by
    intro n
    refine MeasureTheory.Integrable.mono' hf.norm
      ((((Work.FTS.EllipticEst.cut_contDiff n).continuous.measurable.comp
        measurable_fst).aestronglyMeasurable).mul hf.1) ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |χ n p.1| ≤ 1 := by
      rw [abs_of_nonneg (Work.FTS.EllipticEst.cut_nonneg n p.1)]
      exact Work.FTS.EllipticEst.cut_le_one n p.1
    calc |χ n p.1| * |f p.1 p.2| ≤ 1 * |f p.1 p.2| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = |f p.1 p.2| := one_mul _
  -- ## both iterated integrals are the corresponding product integrals
  have hconvL : ∀ n : ℕ, (∫ z in Set.Ioi (0 : ℝ), ∫ θ in Iθo, χ n z * f z θ)
      = ∫ p, χ n p.1 * f p.1 p.2 ∂nuQ := by
    intro n
    rw [MeasureTheory.integral_prod (fun p : ℝ × ℝ => χ n p.1 * f p.1 p.2) (hFint n)]
  have hconvR : (∫ z in Set.Ioi (0 : ℝ), ∫ θ in Iθo, f z θ)
      = ∫ p, f p.1 p.2 ∂nuQ := by
    rw [MeasureTheory.integral_prod (fun p : ℝ × ℝ => f p.1 p.2) hf]
  -- ## dominated convergence
  have haesm : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => χ n p.1 * f p.1 p.2) nuQ := fun n =>
    (((Work.FTS.EllipticEst.cut_contDiff n).continuous.measurable.comp
      measurable_fst).aestronglyMeasurable).mul hf.1
  have hbound : ∀ n : ℕ, ∀ᵐ p ∂nuQ, ‖χ n p.1 * f p.1 p.2‖ ≤ ‖f p.1 p.2‖ := by
    intro n
    filter_upwards with p
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    have h1 : |χ n p.1| ≤ 1 := by
      rw [abs_of_nonneg (Work.FTS.EllipticEst.cut_nonneg n p.1)]
      exact Work.FTS.EllipticEst.cut_le_one n p.1
    calc |χ n p.1| * |f p.1 p.2| ≤ 1 * |f p.1 p.2| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = |f p.1 p.2| := one_mul _
  have hlim : ∀ᵐ p ∂nuQ,
      Filter.Tendsto (fun n : ℕ => χ n p.1 * f p.1 p.2) Filter.atTop
        (nhds (f p.1 p.2)) := by
    filter_upwards [ae_mem_nuQ] with p hp
    have h1 : Filter.Tendsto (fun n : ℕ => χ n p.1) Filter.atTop (nhds 1) :=
      hKone p.1 hp.1
    simpa using h1.mul_const (f p.1 p.2)
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := nuQ) (bound := fun p : ℝ × ℝ => ‖f p.1 p.2‖)
    (F := fun (n : ℕ) (p : ℝ × ℝ) => χ n p.1 * f p.1 p.2)
    (f := fun p : ℝ × ℝ => f p.1 p.2)
    haesm hf.norm hbound hlim
  simp only [hconvL, hconvR]
  exact hmain

section NT

/-- `σ₂ = sin(2θ)^{-(2+η)}` is nonnegative on the closed angular interval. -/
theorem sig2_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sig2 θ := by
  rw [sig2]
  refine Real.rpow_nonneg ?_ _
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The `z`-weight `w(z)²` is continuous on the open quadrant. -/
theorem continuousOn_w_sq_fst :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      Work.FTS.EllipticEst.Q0 := by
  have hw : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
      funext z; rw [Work.Spaces.w]
    rw [hfun]
    refine (ContinuousOn.div ?_ ?_ ?_).pow 2
    · fun_prop
    · fun_prop
    · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)
  refine hw.comp continuous_fst.continuousOn ?_
  intro p hp
  exact (Work.FTS.EllipticEst.mem_Q0.mp hp).1

/-- `σ₂ = sin(2θ)^{-(2+η)}` is continuous on the open quadrant. -/
theorem continuousOn_sig2_snd :
    ContinuousOn (fun p : ℝ × ℝ => sig2 p.2) Work.FTS.EllipticEst.Q0 := by
  have hsin : Continuous (fun p : ℝ × ℝ => Real.sin (2 * p.2)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_snd)
  refine (hsin.continuousOn.rpow_const (p := -(2 + Work.Spaces.eta)) (fun p hp => Or.inl
    (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by have := (Work.FTS.EllipticEst.mem_Q0.mp hp).2.1; linarith)
      (by have := (Work.FTS.EllipticEst.mem_Q0.mp hp).2.2; linarith [Real.pi_pos]))))).congr
    (fun p _ => rfl)

/-- **Joint integrability of the `N`-integrand** `w(z)²·U²cos²(2θ)σ₂(θ)` on `nuQ`, from the
a.e. slice integrability and the integrability of the weighted marginal. -/
theorem integrable_w2_Nterm {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hNslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => (AeI1Fts.U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) Iθo)
    (hNfin : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Iθo, (AeI1Fts.U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)
      (Set.Ioi (0 : ℝ))) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * ((AeI1Fts.U u p.1 p.2) ^ 2 * (Real.cos (2 * p.2)) ^ 2 * sig2 p.2)) nuQ := by
  set G : ℝ → ℝ → ℝ := fun z θ => (AeI1Fts.U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ
    with hG
  have hnn : ∀ z θ, 0 < z → θ ∈ Iθo →
      0 ≤ (Work.Spaces.w z) ^ 2 * G z θ := by
    intro z θ _ hθ
    refine mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) ?_)
    exact sig2_nonneg_of_mem ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- ## a.e. strong measurability
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * G p.1 p.2) nuQ := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * G p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
      have hU : ContinuousOn (fun p : ℝ × ℝ => AeI1Fts.U u p.1 p.2)
          Work.FTS.EllipticEst.Q0 := (AeI1Fts.smoothOpen_U hS).continuousOn
      have hcos : ContinuousOn (fun p : ℝ × ℝ => (Real.cos (2 * p.2)) ^ 2)
          Work.FTS.EllipticEst.Q0 :=
        ((Real.continuous_cos.comp (continuous_const.mul continuous_snd)).continuousOn.pow 2)
      exact continuousOn_w_sq_fst.mul (((hU.pow 2).mul hcos).mul continuousOn_sig2_snd)
    have h := Work.FTS.EllipticEst.Dispatch.aesm_prod_of_continuousOn_Q0 hcont
    rw [nuFts_eq_nuQ] at h
    exact h
  refine ⟨haesm, ?_⟩
  rw [MeasureTheory.HasFiniteIntegral]
  have hnn' : ∀ᵐ p ∂nuQ, 0 ≤ (Work.Spaces.w p.1) ^ 2 * G p.1 p.2 := by
    filter_upwards [ae_mem_nuQ] with p hp
    exact hnn p.1 p.2 hp.1 hp.2
  rw [show (∫⁻ p, ‖(Work.Spaces.w p.1) ^ 2 * G p.1 p.2‖ₑ ∂nuQ)
      = ∫⁻ p, ENNReal.ofReal ((Work.Spaces.w p.1) ^ 2 * G p.1 p.2) ∂nuQ from
    MeasureTheory.lintegral_congr_ae (hnn'.mono (fun p hp => Real.enorm_of_nonneg hp))]
  have hkey : (∫⁻ p, ENNReal.ofReal ((Work.Spaces.w p.1) ^ 2 * G p.1 p.2) ∂nuQ)
      = ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), ∫ θ in Iθo,
          (Work.Spaces.w z) ^ 2 * G z θ) := by
    rw [MeasureTheory.lintegral_prod _ haesm.aemeasurable.ennreal_ofReal]
    have hinner : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        (∫⁻ θ, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * G z θ)
          ∂(MeasureTheory.volume.restrict Iθo))
          = ENNReal.ofReal (∫ θ in Iθo, (Work.Spaces.w z) ^ 2 * G z θ) := by
      filter_upwards [hNslice, MeasureTheory.ae_restrict_mem measurableSet_Ioi]
        with z hz hzpos
      have hint : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2 * G z θ) Iθo :=
        hz.const_mul _
      refine (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint ?_).symm
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      exact hnn z θ hzpos hθ
    rw [MeasureTheory.lintegral_congr_ae hinner]
    have hout : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Iθo, (Work.Spaces.w z) ^ 2 * G z θ) (Set.Ioi (0 : ℝ)) :=
      hNfin.congr_fun (fun z _ => by rw [MeasureTheory.integral_const_mul]) measurableSet_Ioi
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hout
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz =>
        MeasureTheory.setIntegral_nonneg measurableSet_Ioo
          (fun θ hθ => hnn z θ hz hθ)))).symm
  rw [hkey]
  exact ENNReal.ofReal_lt_top

end NT

/-! ## The angular cut-off: support, derivative bound, and the window domination -/

/-- The transition window of the angular cut-off `ψ ε`. -/
def win (ε : ℝ) : Set ℝ :=
  Set.Icc (ε / 2) ε ∪ Set.Icc (Real.pi / 2 - ε) (Real.pi / 2 - ε / 2)

/-- The transition window of `ψ ε` is contained in the closed angular interval. -/
theorem win_subset_Iθ {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ Real.pi / 8) :
    win ε ⊆ Work.Spaces.Iθ := by
  intro θ hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc]
  rcases hθ with h | h
  · exact ⟨by linarith [h.1, hε], by linarith [h.2, hε8, Real.pi_pos]⟩
  · exact ⟨by linarith [h.1, hε], by linarith [h.2, hε, Real.pi_pos]⟩

/-- The derivative of the angular cut-off vanishes off its transition window. -/
theorem deriv_cut_eq_zero_of_notMem_win {ε θ : ℝ} (hε : 0 < ε) (h : θ ∉ win ε) :
    deriv (ψ ε) θ = 0 := by
  have h1 : θ < ε / 2 ∨ ε < θ := by
    by_contra hc
    rw [not_or] at hc
    refine h (Or.inl ?_)
    rw [Set.mem_Icc]
    exact ⟨not_lt.mp hc.1, not_lt.mp hc.2⟩
  have h2 : θ < Real.pi / 2 - ε ∨ Real.pi / 2 - ε / 2 < θ := by
    by_contra hc
    rw [not_or] at hc
    refine h (Or.inr ?_)
    rw [Set.mem_Icc]
    exact ⟨not_lt.mp hc.1, not_lt.mp hc.2⟩
  have hlt : ∀ s : ℝ, s < 1 / 2 → s ∉ Set.Icc (1 / 2 : ℝ) 1 := fun s hs hmem =>
    absurd hmem.1 (not_le_of_gt hs)
  have hgt : ∀ s : ℝ, 1 < s → s ∉ Set.Icc (1 / 2 : ℝ) 1 := fun s hs hmem =>
    absurd hmem.2 (not_le_of_gt hs)
  rw [Work.FTS.EllipticEst.SliceMixedAux.deriv_cut ε θ]
  rcases h1 with h1 | h1
  · have hp : θ / ε < 1 / 2 := by rw [div_lt_iff₀ hε]; linarith
    have hz : Work.FTS.EllipticEst.SliceMixedAux.prof (θ / ε) = 0 :=
      Work.FTS.EllipticEst.SliceMixedAux.prof_eq_zero hp.le
    have hd : deriv Work.FTS.EllipticEst.SliceMixedAux.prof (θ / ε) = 0 :=
      Work.FTS.EllipticEst.SliceMixedAux.prof_deriv_eq_zero_of_notMem (hlt _ hp)
    rw [hz, hd]; ring
  · have hd : deriv Work.FTS.EllipticEst.SliceMixedAux.prof (θ / ε) = 0 :=
      Work.FTS.EllipticEst.SliceMixedAux.prof_deriv_eq_zero_of_notMem (hgt _ (by
        rw [lt_div_iff₀ hε]; linarith))
    rw [hd]
    rcases h2 with h2 | h2
    · have hd2 : deriv Work.FTS.EllipticEst.SliceMixedAux.prof ((Real.pi / 2 - θ) / ε) = 0 :=
        Work.FTS.EllipticEst.SliceMixedAux.prof_deriv_eq_zero_of_notMem (hgt _ (by
          rw [lt_div_iff₀ hε]; linarith))
      rw [hd2]; ring
    · have hd2 : deriv Work.FTS.EllipticEst.SliceMixedAux.prof ((Real.pi / 2 - θ) / ε) = 0 :=
        Work.FTS.EllipticEst.SliceMixedAux.prof_deriv_eq_zero_of_notMem (hlt _ (by
          rw [div_lt_iff₀ hε]; linarith))
      rw [hd2]; ring

/-- A uniform bound `|(ψ ε)'(θ)| ≤ M/ε`. -/
theorem exists_bound_deriv_cut : ∃ M : ℝ, 0 < M ∧ ∀ ε : ℝ, 0 < ε → ∀ θ : ℝ,
    |deriv (ψ ε) θ| ≤ M / ε := by
  obtain ⟨S1, hS1⟩ := Work.FTS.EllipticEst.SliceMixedAux.exists_prof_deriv_bound
  refine ⟨2 * |S1| + 1, by positivity, fun ε hε θ => ?_⟩
  refine le_trans (Work.FTS.EllipticEst.SliceMixedAux.abs_deriv_cut_le hε hS1 θ) ?_
  refine div_le_div_of_nonneg_right ?_ hε.le
  linarith [le_abs_self S1]

/-- `tan x ≤ 2x` on `(0, π/4]`. -/
private theorem tan_le_two_mul {x : ℝ} (hx0 : 0 < x) (hx : x ≤ Real.pi / 4) :
    Real.tan x ≤ 2 * x := by
  have hcos : (1 / 2 : ℝ) ≤ Real.cos x := by
    have h1 := Real.one_sub_sq_div_two_le_cos (x := x)
    have h2 : x ^ 2 ≤ 1 := by nlinarith [Real.pi_lt_four, hx, hx0]
    linarith
  have hsin : Real.sin x ≤ x := Real.sin_le hx0.le
  have hpos : 0 < Real.cos x := by linarith
  rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hpos]
  nlinarith [hsin, hcos, hx0, Real.cos_le_one x]

/-- `σ = tan(2θ)²·σ₂·cos(2θ)²`. -/
private theorem sigE_eq_tan_sq {θ : ℝ} (hs : 0 < Real.sin (2 * θ))
    (hc : Real.cos (2 * θ) ≠ 0) :
    sigE θ = sig2 θ * (Real.cos (2 * θ)) ^ 2 * (Real.tan (2 * θ)) ^ 2 := by
  have hη : -(Work.Spaces.eta) = -(2 + Work.Spaces.eta) + 2 := by ring
  have h1 : sigE θ = sig2 θ * (Real.sin (2 * θ)) ^ 2 := by
    have hrw : sigE θ = (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta) + 2) := by
      rw [sigE, hη]
    rw [hrw, Real.rpow_add hs, sig2, Real.rpow_ofNat]
  have h2 : (Real.sin (2 * θ)) ^ 2
      = (Real.cos (2 * θ)) ^ 2 * (Real.tan (2 * θ)) ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  rw [h1, h2]
  ring

/-- `|tan(2θ)| ≤ 4ε` on the two transition windows of `ψ ε`. -/
private theorem window_tan {ε θ : ℝ} (hε : 0 < ε) (hε8 : ε ≤ Real.pi / 8)
    (h : θ ∈ win ε) : (Real.tan (2 * θ)) ^ 2 ≤ 16 * ε ^ 2 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  rcases h with h | h
  · have hθ0 : 0 < θ := by linarith [h.1, hε]
    have h1 : 0 < 2 * θ := by linarith [hθ0]
    have h2 : 2 * θ ≤ Real.pi / 4 := by linarith [h.2, hε8, hπ]
    have h3 : Real.tan (2 * θ) ≤ 2 * (2 * θ) := tan_le_two_mul h1 h2
    have h4 : 0 ≤ Real.tan (2 * θ) :=
      le_of_lt (Real.tan_pos_of_pos_of_lt_pi_div_two h1 (by linarith [h2, hπ]))
    have h5 : 2 * (2 * θ) ≤ 4 * ε := by linarith [h.2]
    nlinarith [h3, h4, h5, hε]
  · have h1 : 0 < Real.pi - 2 * θ := by linarith [h.2, hε]
    have h2 : Real.pi - 2 * θ ≤ Real.pi / 4 := by linarith [h.1, hε8, hπ]
    have h3 : Real.tan (Real.pi - 2 * θ) ≤ 2 * (Real.pi - 2 * θ) := tan_le_two_mul h1 h2
    have h4 : Real.tan (2 * θ) = -Real.tan (Real.pi - 2 * θ) := by
      have hsub := Real.tan_pi_sub (Real.pi - 2 * θ)
      rwa [show Real.pi - (Real.pi - 2 * θ) = 2 * θ by ring] at hsub
    have h6 : 0 ≤ Real.tan (Real.pi - 2 * θ) :=
      le_of_lt (Real.tan_pos_of_pos_of_lt_pi_div_two h1 (by linarith [h2, hπ]))
    have h5 : 2 * (Real.pi - 2 * θ) ≤ 4 * ε := by linarith [h.1]
    rw [h4]
    nlinarith [h3, h5, h6, hε]

/-- **The window domination**: on the transition windows of `ψ ε` (`ε ≤ π/8`),
`σ(θ)·f² ≤ 16ε²·σ₂(θ)·f²·cos²(2θ)`. -/
theorem sigE_mul_le_window {ε θ : ℝ} (hε : 0 < ε) (hε8 : ε ≤ Real.pi / 8)
    (h : θ ∈ win ε) (f : ℝ) :
    sigE θ * f ^ 2 ≤ 16 * ε ^ 2 * (sig2 θ * f ^ 2 * (Real.cos (2 * θ)) ^ 2) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hs : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · rcases h with h | h
      · linarith [h.1, hε]
      · linarith [h.1, hε, hπ]
    · rcases h with h | h
      · linarith [h.2, hε8, hπ]
      · linarith [h.2, hε, hπ]
  have hc : Real.cos (2 * θ) ≠ 0 := by
    rcases h with h | h
    · have h2θ0 : 0 < 2 * θ := by linarith [h.1, hε]
      have h2θ1 : 2 * θ ≤ Real.pi / 4 := by linarith [h.2, hε8, hπ]
      exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [h2θ0], by linarith [h2θ1, hπ]⟩)
    · have h1 : 0 < Real.pi - 2 * θ := by linarith [h.2, hε]
      have h2 : Real.pi - 2 * θ ≤ Real.pi / 4 := by linarith [h.1, hε8, hπ]
      have hpos : 0 < Real.cos (Real.pi - 2 * θ) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [h1], by linarith [h2, hπ]⟩
      have hid : Real.cos (2 * θ) = -Real.cos (Real.pi - 2 * θ) := by
        have hsub := Real.cos_pi_sub (Real.pi - 2 * θ)
        rwa [show Real.pi - (Real.pi - 2 * θ) = 2 * θ by ring] at hsub
      rw [hid]
      exact ne_of_lt (by linarith)
  have htan : (Real.tan (2 * θ)) ^ 2 ≤ 16 * ε ^ 2 := window_tan hε hε8 h
  have hK : 0 ≤ sig2 θ * f ^ 2 * (Real.cos (2 * θ)) ^ 2 :=
    mul_nonneg (mul_nonneg (sig2_nonneg_of_mem (win_subset_Iθ hε hε8 h)) (sq_nonneg f))
      (sq_nonneg _)
  have heq : sigE θ * f ^ 2
      = (sig2 θ * f ^ 2 * (Real.cos (2 * θ)) ^ 2) * (Real.tan (2 * θ)) ^ 2 := by
    rw [sigE_eq_tan_sq hs hc]
    ring
  rw [heq]
  calc (sig2 θ * f ^ 2 * (Real.cos (2 * θ)) ^ 2) * (Real.tan (2 * θ)) ^ 2
      ≤ (sig2 θ * f ^ 2 * (Real.cos (2 * θ)) ^ 2) * (16 * ε ^ 2) :=
        mul_le_mul_of_nonneg_left htan hK
    _ = 16 * ε ^ 2 * (sig2 θ * f ^ 2 * (Real.cos (2 * θ)) ^ 2) := by ring

end Work.FTS.EllipticEst.I1Ae
