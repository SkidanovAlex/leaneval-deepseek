import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.BaseCase
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPair_conv_transfer_iter
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.leaf_logW_shift_uniform
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integrable_prod_of_lintegral_iterated
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `RawE6Aux/Jeps_IP6_transfer_aux.lean` — the level-six `J_ε`-transfer estimate

This file proves `Jeps_IP6_transfer_aux`: the weighted near-self-adjointness of the log-coordinate
mollifier `J_ε` at level six,

`|IP6o α (J_ε f) h − IP6o α f (J_ε h)| ≤ C ε ‖f‖_{ℋ⁶} ‖h‖_{ℋ⁶}`   (`ρ` even),

with **no derivative loss**.  The assembly is the log-coordinate transfer machinery of
`E4R3/Apriori4Proofs/JepsTransfer` (`delta_bound_of`), which reduces everything to three analytic
inputs:

* `JT.LogPlaneTransfer` — the abstract plane transfer estimate, proved in
  `JepsTransfer.logPair_conv_transfer_iter`;
* `JT.LeafShiftUniform` — the uniform two-sided log-shift bound for the three leaf weights, proved
  in `JepsTransfer.leaf_logW_shift_uniform`;
* `JT.LeafPairIntegrable ρ` — the joint integrability of the level-one slot pairings.

The last one is *not* part of the shipped `JepsTransfer` files (`integrable_pairing_Jeps` is still
unproved there), and it is the one input proved here from scratch: the `ℋ¹`-weighted `L²`-bounds of
the un-mollified slots come from `JT.lintegral_leaf_le_HkSq` + `HkMem_Jeps`, and the cross term is
then AM–GM/Hölder.  Route for `LeafPairIntegrable ρ`:

* `w · (D_z^b D_θ^a u)²` is integrable on the flat quadrant because its iterated lintegral is
  finite (`JT.lintegral_leaf_le_HkSq`) and it is continuous there (`continuousOn_leafW'`);
* `w · (J_ε (D_z^b D_θ^a u))²` is integrable for the same reason, using `HkMem_Jeps` to see
  `HkMem α 1 (J_ε u)`, `mixed_Jeps` to move `J_ε` inside the mixed derivative, and
  `JT.lintegral_leaf_le_HkSq` at the profile `J_ε u`;
* the cross term `w · J_ε(D_z^b D_θ^a u) · D_z^b D_θ^a v` is then (weighted) Cauchy–Schwarz.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.RawE6Aux

open Work.FTS.Galerkin (Fn)

set_option maxHeartbeats 800000

/-! ## Continuity of the leaf weights on the open quadrant -/

/-- The radial factor `z ↦ w z = (1+z)²/z²` of the leaf weights is continuous on the open
quadrant (its pole at `z = 0` lies outside `Quad`). -/
private theorem continuousOn_w_quad :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.StrongEps.Quad := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt (Work.FTS.StrongEps.mem_Quad.mp hp).1)

/-- The angular factor `θ ↦ sin(2θ)^q` is continuous on the open quadrant for every real
exponent `q` (the base is positive there, so no junk value of `Real.rpow` occurs). -/
private theorem continuousOn_sinpow_quad (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ q) Work.FTS.StrongEps.Quad := by
  have hsinpos : ∀ p ∈ Work.FTS.StrongEps.Quad, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  refine ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

/-- **Every leaf weight of the `IP4`-unfolding is continuous on the open quadrant.** -/
private theorem continuousOn_leafW' {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (h : Work.FTS.TransportS.IsLeafW α a ρ) :
    ContinuousOn (Function.uncurry ρ) Work.FTS.StrongEps.Quad := by
  rcases h with rfl | rfl | ⟨_, rfl⟩
  · have he : Function.uncurry Work.FTS.TransportS.leafEta = fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := rfl
    rw [he]
    exact (continuousOn_w_quad.pow 2).mul (continuousOn_sinpow_quad (-(Work.Spaces.eta)))
  · have he : Function.uncurry Work.FTS.TransportS.leafOne = fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 := rfl
    rw [he]
    exact continuousOn_w_quad.pow 2
  · have he : Function.uncurry (Work.FTS.TransportS.leafGam α) = fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)) := rfl
    rw [he]
    exact (continuousOn_w_quad.pow 2).mul (continuousOn_sinpow_quad (-(Work.Spaces.gam α)))

/-! ## Two measure-theoretic tools -/

/-- Exchange the iterated `∫⁻` over `Iz × Iθ` for the iterated `∫⁻` over the open quadrant. -/
private theorem lintegral_Iz_Iθ_eq_Ioi_Ioo (f : ℝ → ℝ → ℝ≥0∞) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, f z θ)
      = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2), f z θ := by
  have hz : Work.Spaces.Iz =ᵐ[(volume : Measure ℝ)] Set.Ioi (0 : ℝ) := by
    show Set.Ici (0 : ℝ) =ᵐ[(volume : Measure ℝ)] Set.Ioi 0
    exact (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  have hθ : Work.Spaces.Iθ =ᵐ[(volume : Measure ℝ)] Set.Ioo (0 : ℝ) (π / 2) := by
    show Set.Icc (0 : ℝ) (π / 2) =ᵐ[(volume : Measure ℝ)] Set.Ioo 0 (π / 2)
    exact (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  rw [MeasureTheory.setLIntegral_congr hz]
  exact MeasureTheory.lintegral_congr fun z => MeasureTheory.setLIntegral_congr hθ

/-- **Integrability on the flat quadrant from an iterated `∫⁻`-bound.**  If `F` is a.e. strongly
measurable on the open quadrant, nonnegative there, and the iterated (Tonelli) lintegral of
`ENNReal.ofReal (F z θ)` over `Iz × Iθ` is finite, then `F` is integrable on the open
quadrant. -/
private theorem integrable_prod_of_lintegral_Iz_Iθ {F : ℝ → ℝ → ℝ}
    (hae : AEStronglyMeasurable (Function.uncurry F)
      (volume.restrict Work.FTS.StrongEps.Quad))
    (hnn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → 0 ≤ F z θ)
    (hfin : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (F z θ)) < ⊤) :
    Integrable (Function.uncurry F) (volume.restrict Work.FTS.StrongEps.Quad) := by
  refine Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integrable_prod_of_lintegral_iterated
    hae (ne_of_lt ?_)
  calc (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal ‖F z θ‖)
      ≤ (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (F z θ)) := by
        refine MeasureTheory.lintegral_mono_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        refine MeasureTheory.lintegral_mono_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
        exact ENNReal.ofReal_le_ofReal (le_of_eq (Real.norm_of_nonneg (hnn z θ hz hθ.1 hθ.2)))
    _ = (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (F z θ)) :=
        (lintegral_Iz_Iθ_eq_Ioi_Ioo (fun z θ => ENNReal.ofReal (F z θ))).symm
    _ < ⊤ := hfin

/-- **Weighted Cauchy–Schwarz / AM–GM.**  From the weighted `L²`-integrability of two functions
against a weight `ρ ≥ 0` a.e., the weighted product is integrable. -/
private theorem integrable_mul_of_weight_sq {β : Type*} [MeasurableSpace β] {μ : Measure β}
    {ρ f g : β → ℝ}
    (hρ0 : 0 ≤ᵐ[μ] ρ) (hρm : AEMeasurable ρ μ) (hfm : AEMeasurable f μ) (hgm : AEMeasurable g μ)
    (hρf : Integrable (fun x => ρ x * f x ^ 2) μ)
    (hρg : Integrable (fun x => ρ x * g x ^ 2) μ) :
    Integrable (fun x => ρ x * f x * g x) μ := by
  refine (hρf.add hρg).mono' ((hρm.mul hfm).mul hgm).aestronglyMeasurable ?_
  filter_upwards [hρ0] with x hρx
  show ‖ρ x * f x * g x‖ ≤ ρ x * f x ^ 2 + ρ x * g x ^ 2
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hρx]
  have hρx' : (0 : ℝ) ≤ ρ x := by simpa using hρx
  have h2 : 2 * |f x| * |g x| ≤ f x ^ 2 + g x ^ 2 := by
    nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x)]
  have h3 : ρ x * (2 * |f x| * |g x|) ≤ ρ x * (f x ^ 2 + g x ^ 2) :=
    mul_le_mul_of_nonneg_left h2 hρx'
  nlinarith [h3]

/-! ## The weighted `L²`-integrability of the level-one slots -/

/-- `w · (D_z^b D_θ^a u)²` is integrable on the flat quadrant for every level-one leaf slot of an
`ℋ¹`-honest, open-smooth profile. -/
private theorem integrable_leaf_sq {α : ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ} {u : Fn}
    (hα : 0 < α) (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (hab : a + b ≤ 1)
    (hsm : Work.FTS.EllipticEst.SmoothOpen u) (hmem : Work.Spaces.HkMem α 1 u) :
    Integrable (Function.uncurry fun z θ => ρ z θ * (Work.Spaces.mixed b a u z θ) ^ 2)
      (volume.restrict Work.FTS.StrongEps.Quad) := by
  refine integrable_prod_of_lintegral_Iz_Iθ ?_ ?_ ?_
  · refine ((continuousOn_leafW' hleaf).mul
      ((hsm.mixed b a).continuousOn.pow 2)).aestronglyMeasurable
      Work.FTS.StrongEps.isOpen_Quad.measurableSet
  · intro z θ hz hθ hθ2
    exact mul_nonneg ((Work.FTS.TransportS.IsLeafW_le α hα hleaf).1 z θ hz hθ hθ2)
      (sq_nonneg _)
  · exact lt_of_le_of_lt
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.lintegral_leaf_le_HkSq hα hmem hab hleaf)
      ENNReal.ofReal_lt_top

/-- `w · (J_ε (D_z^b D_θ^a u))²` is integrable on the flat quadrant for every level-one leaf slot
of an `ℋ¹`-honest, open-smooth profile.  The mollified profile is again `ℋ¹`-honest
(`HkMem_Jeps`), and `J_ε` commutes with the mixed derivatives on the open quadrant
(`mixed_Jeps`). -/
private theorem integrable_Jeps_mixed_sq {α : ℝ} {a b : ℕ} {ρ : ℝ × ℝ → ℝ} {wt : ℝ → ℝ → ℝ}
    {u : Fn} {ε : ℝ}
    (hρ : Work.FTS.StrongEps.IsMollKernel ρ) (hα : 0 < α) (hα1 : α ≤ 1) (hε : 0 < ε)
    (hleaf : Work.FTS.TransportS.IsLeafW α a wt) (hab : a + b ≤ 1)
    (hsm : Work.FTS.EllipticEst.SmoothOpen u) (hmem : Work.Spaces.HkMem α 1 u) :
    Integrable (Function.uncurry fun z θ =>
        wt z θ * (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a u) z θ) ^ 2)
      (volume.restrict Work.FTS.StrongEps.Quad) := by
  have hJcont : ContinuousOn (fun q : ℝ × ℝ =>
      Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a u) q.1 q.2)
      Work.FTS.StrongEps.Quad :=
    Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps hρ hε (hsm.mixed b a).continuousOn
  have hJmem : Work.Spaces.HkMem α 1 (Work.FTS.StrongEps.Jeps ρ ε u) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ ⟨hα, hα1⟩ hε (fun n => hsm.forall n) hmem
  -- the two integrands agree on the open quadrant, where `J_ε` commutes with `mixed`
  have hswap : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        (wt z θ * (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a u) z θ) ^ 2))
      = (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        (wt z θ * (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε u) z θ) ^ 2)) := by
    rw [lintegral_Iz_Iθ_eq_Ioi_Ioo
        (fun z θ => ENNReal.ofReal (wt z θ
          * (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a u) z θ) ^ 2)),
      lintegral_Iz_Iθ_eq_Ioi_Ioo
        (fun z θ => ENNReal.ofReal (wt z θ
          * (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε u) z θ) ^ 2))]
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [show (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε u) z θ)
        = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a u) z θ from
      Work.FTS.StrongEps.mixed_Jeps ρ hρ hε (fun n => hsm.forall n) hz hθ b a]
  refine integrable_prod_of_lintegral_Iz_Iθ ?_ ?_ ?_
  · refine ((continuousOn_leafW' hleaf).mul
      (hJcont.pow 2)).aestronglyMeasurable Work.FTS.StrongEps.isOpen_Quad.measurableSet
  · intro z θ hz hθ hθ2
    exact mul_nonneg ((Work.FTS.TransportS.IsLeafW_le α hα hleaf).1 z θ hz hθ hθ2)
      (sq_nonneg _)
  · rw [hswap]
    exact lt_of_le_of_lt
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.lintegral_leaf_le_HkSq hα hJmem hab hleaf)
      ENNReal.ofReal_lt_top

/-! ## The joint integrability of the level-one slot pairings -/

/-- **The level-one joint integrability of the `J_ε`-pairings**, i.e. `JT.LeafPairIntegrable`.

The cross term is `w · J_ε(D_z^b D_θ^a u) · D_z^b D_θ^a v`: both factors have finite weighted
`L²`-norm (`integrable_Jeps_mixed_sq` for the first, `integrable_leaf_sq` for the second), so the
weighted product is integrable by `integrable_mul_of_weight_sq`; the two diagonal terms are exactly
`integrable_leaf_sq`. -/
theorem leafPairIntegrable_of {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.LeafPairIntegrable ρ := by
  intro α ε hα hε w a b hleaf hab u v hu hv
  have hα0 : 0 < α := hα.1
  have hε0 : 0 < ε := hε.1
  have hQ0 : 0 ≤ᵐ[volume.restrict Work.FTS.StrongEps.Quad] Function.uncurry w := by
    filter_upwards [MeasureTheory.ae_restrict_mem Work.FTS.StrongEps.isOpen_Quad.measurableSet]
      with q hq
    exact (Work.FTS.TransportS.IsLeafW_le α hα0 hleaf).1 q.1 q.2 hq.1 hq.2.1 hq.2.2
  have hQm : AEMeasurable (Function.uncurry w)
      (volume.restrict Work.FTS.StrongEps.Quad) :=
    ((continuousOn_leafW' hleaf).aestronglyMeasurable
      Work.FTS.StrongEps.isOpen_Quad.measurableSet).aemeasurable
  have hJm : AEMeasurable (fun q : ℝ × ℝ =>
      Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a u) q.1 q.2)
      (volume.restrict Work.FTS.StrongEps.Quad) :=
    ((Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps hρ.moll hε0
      (hu.1.mixed b a).continuousOn).aestronglyMeasurable
        Work.FTS.StrongEps.isOpen_Quad.measurableSet).aemeasurable
  have hGm : AEMeasurable (fun q : ℝ × ℝ => Work.Spaces.mixed b a v q.1 q.2)
      (volume.restrict Work.FTS.StrongEps.Quad) :=
    (((hv.1.mixed b a).continuousOn).aestronglyMeasurable
      Work.FTS.StrongEps.isOpen_Quad.measurableSet).aemeasurable
  have hQg := integrable_leaf_sq hα0 hleaf hab hv.1 hv.2
  have hQf := integrable_Jeps_mixed_sq hρ.moll hα0 hα.2 hε0 hleaf hab hu.1 hu.2
  exact ⟨integrable_mul_of_weight_sq hQ0 hQm hJm hGm hQf hQg,
    integrable_leaf_sq hα0 hleaf hab hu.1 hu.2, hQg⟩

/-! ## The target -/

theorem Jeps_IP6_transfer_aux {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hρs : ∀ p : ℝ × ℝ, ρ (-p) = ρ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      ∀ f h : Work.FTS.Galerkin.Fn,
      Work.FTS.VocabO.HQo α 6 f → Work.FTS.VocabO.HQo α 6 h →
      |Work.FTS.StrongEps.EpsE4Thr.E4R4.IP6o α (Work.FTS.StrongEps.Jeps ρ ε f) h
        - Work.FTS.StrongEps.EpsE4Thr.E4R4.IP6o α f (Work.FTS.StrongEps.Jeps ρ ε h)|
        ≤ C * ε * Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 h := by
  have hLT : Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.LogPlaneTransfer :=
    fun {k ε Cw} hε0 hε1 hCw hkcont hk0 hkmass hksupp hkeven hkmomint {Q} hQ0 hQm hQsh hQsh'
        {G₁ G₂} hG1m hG2m hconv1 hconv2 hI1 hI2 =>
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPair_conv_transfer_iter
        hε0 hε1 hCw hkcont hk0 hkmass hksupp hkeven hkmomint hQ0 hQm hQsh hQsh' hG1m hG2m
        hconv1 hconv2 hI1 hI2
  have hShift : Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.LeafShiftUniform :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.leaf_logW_shift_uniform
  have hInt : Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.LeafPairIntegrable ρ :=
    leafPairIntegrable_of hρ
  obtain ⟨K, hK0, hK⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.delta_bound_of hρ hρs hLT hShift hInt
  refine ⟨K, hK0, ?_⟩
  intro α hα ε hε f h hf hh
  have hb := hK α hα ε hε f h hf hh
  simpa only [Work.FTS.StrongEps.EpsE4Thr.E4R4.IP6o,
    Work.FTS.StrongPersist.N6TPPriced.IP6_one_eq_IPn_five] using hb

end Work.FTS.StrongEps.E4R3.RawE6Aux
