import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.N_bound
import Submission.Work.FTS.EllipticEst.AeI1Fts.slice_rate
import Submission.Work.FTS.EllipticEst.AeI1Fts.cut_deriv_tendsto_zero
import Submission.Work.FTS.EllipticEst.AeI1Fts.hardy_slice_ae
import Submission.Work.FTS.EllipticEst.SliceMixedAux.smoothCutoffIoo
import Submission.Work.FTS.EllipticEst.I1Ae.AuxInt
import Submission.Work.FTS.EllipticEst.I1Ae.RIFLimits
import Submission.Work.FTS.EllipticEst.I1Ae.RIFMain
import Submission.Work.FTS.EllipticEst.I1Ae.RIFMainB
import Submission.Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
import Submission.Work.FTS.EllipticEst.TT.aeSliceAesm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts.TendstoTermsCut.TTAux`

The analytic toolbox for the four `k → ∞` limits of the doubly truncated `I₁` identity
(`AeI1Fts.TendstoTermsCut.tendsto_terms_cut`): the two dominated-convergence limits that remove
the radial cut-off `cut k` and the angular cut-off `SliceMixedAux.cut (1/(k+1))` *simultaneously*
on the product measure `nuQ`, and the joint integrability of the four untruncated slots.

The marginal finiteness `ntFin` of the `N`-term (`z ↦ w²∫_θ U²cos²(2θ)σ₂`) is derived from
`hardy_slice_ae` (`∫_θ U²cos²(2θ)σ₂ ≤ (1+η)⁻²∫_θ V²σ` a.e.) together with a.e. strong
measurability of the marginal (`TT.aeSliceAesm`) and the `ℋ⁰`-honesty of `V u`.
-/

namespace Work.FTS.EllipticEst.AeI1Fts.TendstoTermsCut

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.I1Ae

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "χ" => Work.FTS.EllipticEst.cut
local notation "ψ" => Work.FTS.EllipticEst.SliceMixedAux.cut
local notation "wt" => Work.Spaces.w
local notation "cwt" => Work.FTS.EllipticEst.AngSecond.cw

/-- The sequential angular cut-off parameter `δ_k = 1/(k+1)`. -/
abbrev dk (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

/-! ## Elementary facts -/

/-- `|cw z| ≤ 2` for `z ≥ 0` (`cw z = 2(z-1)/(1+z)`). -/
theorem abs_cw_le_two {z : ℝ} (hz : 0 ≤ z) : |cwt z| ≤ 2 := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  rw [Work.FTS.EllipticEst.AngSecond.cw, abs_div, abs_of_pos h1]
  rw [show |2 * (z - 1)| = 2 * |z - 1| by rw [abs_mul]; norm_num]
  rw [div_le_iff₀ h1]
  have h : |z - 1| ≤ z + 1 := by
    rw [abs_le]; constructor <;> linarith
  linarith

/-- For `0 < θ < π/2` the angular cut-off is eventually `1` along `δ_k = 1/(k+1)`. -/
theorem psi_eventually_one {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi / 2) :
    ∀ᶠ k : ℕ in atTop, ψ (dk k) θ = 1 := by
  have hd : Tendsto (fun k : ℕ => dk k) atTop (nhds 0) := by
    simpa only [dk] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h1 : ∀ᶠ k : ℕ in atTop, dk k < θ := (tendsto_order.1 hd).2 θ h0
  have h2 : ∀ᶠ k : ℕ in atTop, dk k < Real.pi / 2 - θ :=
    (tendsto_order.1 hd).2 _ (by linarith)
  filter_upwards [h1, h2] with k hk1 hk2
  exact Work.FTS.EllipticEst.SliceMixedAux.cut_eq_one (by rw [dk]; positivity)
    (le_of_lt hk1) (by linarith [hk2])

private theorem abs_psi_le_one (ε θ : ℝ) : |ψ ε θ| ≤ 1 := by
  rw [abs_of_nonneg (Work.FTS.EllipticEst.SliceMixedAux.cut_nonneg ε θ)]
  exact Work.FTS.EllipticEst.SliceMixedAux.cut_le_one ε θ

private theorem abs_chi_le_one (k : ℕ) (z : ℝ) : |χ k z| ≤ 1 := by
  rw [abs_of_nonneg (Work.FTS.EllipticEst.cut_nonneg k z)]
  exact Work.FTS.EllipticEst.cut_le_one k z

private theorem measurable_chi (k : ℕ) : Measurable fun p : ℝ × ℝ => χ k p.1 :=
  ((Work.FTS.EllipticEst.cut_contDiff k).continuous.measurable).comp measurable_fst

private theorem measurable_psi (ε : ℝ) : Measurable fun p : ℝ × ℝ => ψ ε p.2 :=
  ((Work.FTS.EllipticEst.SliceMixedAux.cut_contDiff ε).continuous.measurable).comp measurable_snd

/-! ## The two dominated-convergence limits on `nuQ` -/

/-- **Simultaneous removal of the two cut-offs.**  For integrable `A` on the quadrant,
`∫ χ_k(z) ψ_{δ_k}(θ) A(z,θ) → ∫ A`. -/
theorem tendsto_integral_cut_pair {G : ℝ × ℝ → ℝ}
    (hG : MeasureTheory.Integrable G nuQ) :
    Tendsto (fun k : ℕ => ∫ p, (χ k p.1 * ψ (dk k) p.2) * G p ∂nuQ)
      atTop (nhds (∫ p, G p ∂nuQ)) := by
  obtain ⟨K, hKpos, hKbd, hKone, hKlim⟩ :=
    Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := nuQ) (l := atTop)
    (F := fun (k : ℕ) (p : ℝ × ℝ) => (χ k p.1 * ψ (dk k) p.2) * G p)
    (f := G)
    (bound := fun p : ℝ × ℝ => ‖G p‖) ?_ ?_ hG.norm ?_
  · refine Filter.Eventually.of_forall (fun k => ?_)
    exact ((measurable_chi k).mul (measurable_psi (dk k))).aestronglyMeasurable.mul hG.1
  · refine Filter.Eventually.of_forall (fun k => Filter.Eventually.of_forall (fun p => ?_))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    calc |χ k p.1| * |ψ (dk k) p.2| * |G p|
        ≤ 1 * 1 * |G p| := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul (abs_chi_le_one k p.1)
            (abs_psi_le_one (dk k) p.2) (abs_nonneg _) zero_le_one) (abs_nonneg _)
      _ = |G p| := by ring
  · filter_upwards [ae_mem_nuQ] with p hp
    obtain ⟨hz, hθ⟩ := hp
    have hχ : Tendsto (fun k : ℕ => χ k p.1) atTop (nhds 1) := hKone p.1 hz
    have hψ : Tendsto (fun k : ℕ => ψ (dk k) p.2) atTop (nhds 1) :=
      (tendsto_const_nhds (x := (1 : ℝ))).congr'
        ((psi_eventually_one hθ.1 hθ.2).mono (fun k hk => hk.symm))
    simpa using (hχ.mul hψ).mul_const (G p)

/-- **Vanishing of the radial-derivative slot.**  `∫ z χ_k'(z) ψ_{δ_k}(θ) A(z,θ) → 0`. -/
theorem tendsto_integral_dcut_pair {G : ℝ × ℝ → ℝ}
    (hG : MeasureTheory.Integrable G nuQ) :
    Tendsto (fun k : ℕ => ∫ p, (p.1 * deriv (χ k) p.1 * ψ (dk k) p.2) * G p ∂nuQ)
      atTop (nhds 0) := by
  obtain ⟨K, hKpos, hKbd, hKone, hKlim⟩ :=
    Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
  have hKnn : (0 : ℝ) ≤ K := le_of_lt hKpos
  have haesm : ∀ᶠ k : ℕ in atTop, MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (p.1 * deriv (χ k) p.1 * ψ (dk k) p.2) * G p) nuQ := by
    refine Filter.Eventually.of_forall (fun k => ?_)
    exact ((((measurable_id.comp measurable_fst).mul
      ((measurable_deriv (χ k)).comp measurable_fst)).mul
        (measurable_psi (dk k))).aestronglyMeasurable).mul hG.1
  have hbound : ∀ᶠ k : ℕ in atTop, ∀ᵐ p ∂nuQ,
      ‖(p.1 * deriv (χ k) p.1 * ψ (dk k) p.2) * G p‖ ≤ K * ‖G p‖ := by
    refine Filter.Eventually.of_forall (fun k => Filter.Eventually.of_forall (fun p => ?_))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    have hψ := abs_psi_le_one (dk k) p.2
    have hd : |p.1| * |deriv (χ k) p.1| ≤ K := by
      rw [← abs_mul]; exact hKbd k p.1
    calc |p.1| * |deriv (χ k) p.1| * |ψ (dk k) p.2| * |G p|
        ≤ K * 1 * |G p| := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul hd hψ (abs_nonneg _) hKnn)
            (abs_nonneg _)
      _ = K * |G p| := by ring
  have hlim : ∀ᵐ p ∂nuQ, Tendsto
      (fun k : ℕ => (p.1 * deriv (χ k) p.1 * ψ (dk k) p.2) * G p) atTop (nhds 0) := by
    filter_upwards [ae_mem_nuQ] with p hp
    have hψ : Tendsto (fun k : ℕ => ψ (dk k) p.2) atTop (nhds 1) :=
      (tendsto_const_nhds (x := (1 : ℝ))).congr'
        ((psi_eventually_one hp.2.1 hp.2.2).mono (fun k hk => hk.symm))
    have h := ((hKlim p.1).mul hψ).mul_const (G p)
    simpa using h
  have hmain := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := nuQ) (l := atTop)
    (F := fun (k : ℕ) (p : ℝ × ℝ) => (p.1 * deriv (χ k) p.1 * ψ (dk k) p.2) * G p)
    (f := fun _ => (0 : ℝ)) (fun p : ℝ × ℝ => K * ‖G p‖)
    haesm hbound (hG.norm.const_mul K) hlim
  simpa using hmain

/-! ## The truncated integrands are integrable -/

/-- The product of the two cut-offs preserves integrability. -/
theorem integrable_cut_pair_mul {G : ℝ × ℝ → ℝ}
    (hG : MeasureTheory.Integrable G nuQ) (k : ℕ) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (χ k p.1 * ψ (dk k) p.2) * G p) nuQ := by
  refine MeasureTheory.Integrable.mono' hG.norm
    (((measurable_chi k).mul (measurable_psi (dk k))).aestronglyMeasurable.mul hG.1) ?_
  filter_upwards with p
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
  calc |χ k p.1| * |ψ (dk k) p.2| * |G p|
      ≤ 1 * 1 * |G p| := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul (abs_chi_le_one k p.1)
          (abs_psi_le_one (dk k) p.2) (abs_nonneg _) zero_le_one) (abs_nonneg _)
    _ = |G p| := by ring

/-- The derivative of the radial cut-off preserves integrability. -/
theorem integrable_cut_pair_dmul {G : ℝ × ℝ → ℝ}
    (hG : MeasureTheory.Integrable G nuQ) (k : ℕ) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (p.1 * deriv (χ k) p.1 * ψ (dk k) p.2) * G p) nuQ := by
  obtain ⟨K, hKpos, hKbd, hKone, hKlim⟩ :=
    Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
  have hKnn : (0 : ℝ) ≤ K := le_of_lt hKpos
  refine MeasureTheory.Integrable.mono' (hG.norm.const_mul K)
    ((((measurable_id.comp measurable_fst).mul
      ((measurable_deriv (χ k)).comp measurable_fst)).mul
        (measurable_psi (dk k))).aestronglyMeasurable.mul hG.1) ?_
  filter_upwards with p
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
  have hψ := abs_psi_le_one (dk k) p.2
  have hd : |p.1| * |deriv (χ k) p.1| ≤ K := by
    rw [← abs_mul]; exact hKbd k p.1
  calc |p.1| * |deriv (χ k) p.1| * |ψ (dk k) p.2| * |G p|
      ≤ K * 1 * |G p| := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul hd hψ (abs_nonneg _) hKnn) (abs_nonneg _)
    _ = K * |G p| := by ring

/-! ## Joint integrability of the untruncated slots -/

/-- Joint integrability of the `AA·BB + cw·U·BB` slot. -/
theorem integrable_AB_slot {α : ℝ} {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hA : Work.Spaces.HkMem α 0 (AA u)) (hB : Work.Spaces.HkMem α 0 (BB u))
    (hU : Work.Spaces.HkMem α 0 (U u)) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (wt p.1) ^ 2 * sigE p.2
      * (AA u p.1 p.2 * BB u p.1 p.2
        + cwt p.1 * U u p.1 p.2 * BB u p.1 p.2)) nuQ := by
  have hbase1 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      AA u p.1 p.2 * BB u p.1 p.2 * (wt p.1) ^ 2 * sigE p.2) nuQ :=
    integrable_w2_sig_mul (f := AA u) (h := BB u)
      (continuousOn_uncurry_AA hS) (continuousOn_uncurry_BB hS) hA hB
  have hbase2 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      U u p.1 p.2 * BB u p.1 p.2 * (wt p.1) ^ 2 * sigE p.2) nuQ :=
    integrable_w2_sig_mul (f := U u) (h := BB u)
      (continuousOn_uncurry_U hS) (continuousOn_uncurry_BB hS) hU hB
  have hcw : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      cwt p.1 * (U u p.1 p.2 * BB u p.1 p.2 * (wt p.1) ^ 2 * sigE p.2)) nuQ := by
    refine integrable_mul_of_bound (c := fun p : ℝ × ℝ => cwt p.1) (M := 2) hbase2
      (by norm_num) ?_ ?_
    · filter_upwards [ae_mem_nuQ] with p hp
      exact abs_cw_le_two (le_of_lt hp.1)
    · refine aesm_nuQ_of_continuousOn ?_
      exact continuousOn_cw_fst.mul ((((continuousOn_uncurry_U hS).mul
        (continuousOn_uncurry_BB hS)).mul continuousOn_w_sq_fst).mul
          continuousOn_uncurry_sigE)
  refine (hbase1.add hcw).congr (Filter.Eventually.of_forall (fun p => ?_))
  simp only [Pi.add_apply]
  ring

/-- Joint integrability of the `U·BB` slot. -/
theorem integrable_UBB_slot {α : ℝ} {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hB : Work.Spaces.HkMem α 0 (BB u)) (hU : Work.Spaces.HkMem α 0 (U u)) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (wt p.1) ^ 2 * sigE p.2 * (U u p.1 p.2 * BB u p.1 p.2)) nuQ :=
  (integrable_w2_sig_mul (f := U u) (h := BB u)
    (continuousOn_uncurry_U hS) (continuousOn_uncurry_BB hS)
    hU hB).congr (Filter.Eventually.of_forall (fun p => by ring))

/-- Joint integrability of the `V²` slot. -/
theorem integrable_Vsq_slot {α : ℝ} {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hV : Work.Spaces.HkMem α 0 (V u)) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (wt p.1) ^ 2 * sigE p.2 * (V u p.1 p.2) ^ 2) nuQ :=
  (integrable_w2_sig_sq (Work.FTS.EllipticEst.AeI1Fts.smoothOpen_V hS) hV).congr
    (Filter.Eventually.of_forall (fun p => by ring))

/-! ## Finiteness of the marginal of the `N`-term -/

/-- **Marginal finiteness of the `N`-term.**  From `hardy_slice_ae`
(`∫_θ U²cos²(2θ)σ₂ ≤ (1+η)⁻²∫_θ V²σ` a.e.) and the `ℋ⁰`-honesty of `V u`, the `z`-function
`w²∫_θ U²cos²(2θ)σ₂` is integrable on `(0,∞)`. -/
theorem ntFinAux {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (U u)) (hV : Work.Spaces.HkMem α 0 (V u)) :
    MeasureTheory.IntegrableOn (fun z : ℝ => (wt z) ^ 2
        * ∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) (Set.Ioi 0) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hVjoint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (wt p.1) ^ 2 * (V u p.1 p.2) ^ 2 * sigE p.2) nuQ :=
    integrable_w2_sig_sq (Work.FTS.EllipticEst.AeI1Fts.smoothOpen_V hS) hV
  have hVint : MeasureTheory.IntegrableOn
      (fun z : ℝ => (wt z) ^ 2 * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ) (Set.Ioi 0) := by
    refine hVjoint.integral_prod_left.congr (Filter.Eventually.of_forall (fun z => ?_))
    change (∫ θ in Iθo, (wt z) ^ 2 * (V u z θ) ^ 2 * sigE θ)
      = (wt z) ^ 2 * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by ring)
  have haesm : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => (wt z) ^ 2
      * ∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ => (wt p.1) ^ 2
        * ((U u p.1 p.2) ^ 2 * (Real.cos (2 * p.2)) ^ 2 * sig2 p.2))
        Work.FTS.EllipticEst.Q0 :=
      continuousOn_w_sq_fst.mul ((((continuousOn_uncurry_U hS).pow 2).mul
        ((continuousOn_uncurry_cos2).pow 2)).mul continuousOn_sig2_snd)
    have h1 := Work.FTS.EllipticEst.TT.aeSliceAesm_sliceIntegral_of_continuousOn hcont
    refine h1.congr (Filter.Eventually.of_forall (fun z => ?_))
    change (∫ θ in Work.Spaces.Iθ,
        (wt z) ^ 2 * ((U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ))
      = (wt z) ^ 2 * ∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ
    rw [← MeasureTheory.integral_const_mul]
    exact (MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2))).symm
  refine MeasureTheory.Integrable.mono'
    (hVint.const_mul (1 / (1 + Work.Spaces.eta) ^ 2)) haesm ?_
  filter_upwards [Work.FTS.EllipticEst.AeI1Fts.hardy_slice_ae h hU hV] with z hz
  have hθnn : 0 ≤ ∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun θ hθ =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
          (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _))
  have hw2 : (0 : ℝ) ≤ (wt z) ^ 2 := sq_nonneg _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw2, abs_of_nonneg hθnn]
  calc (wt z) ^ 2 * ∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ
      ≤ (wt z) ^ 2 * ((1 / (1 + Work.Spaces.eta) ^ 2)
          * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ) :=
        mul_le_mul_of_nonneg_left hz hw2
    _ = (1 / (1 + Work.Spaces.eta) ^ 2)
          * ((wt z) ^ 2 * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ) := by ring

end

end Work.FTS.EllipticEst.AeI1Fts.TendstoTermsCut
