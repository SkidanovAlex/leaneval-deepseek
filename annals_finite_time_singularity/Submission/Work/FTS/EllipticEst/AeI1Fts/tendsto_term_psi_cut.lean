import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.slice_rate
import Submission.Work.FTS.EllipticEst.AeI1Fts.N_bound
import Submission.Work.FTS.EllipticEst.SliceMixedAux.smoothCutoffIoo
import Submission.Work.FTS.EllipticEst.AeI1Fts.psiDeriv_setup
import Submission.Work.FTS.EllipticEst.AeI1Fts.psiDeriv_layer

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/tendsto_term_psi_cut`

The `θ`-layer (boundary) term of the angular integration by parts, along the *sequential*
angular cut-off `χ_{1/(k+1)}` and with the *radial* cut-off `cut k → 1`:

`∫_z cut k z · w z² · ∫_θ σ θ (χ_{1/(k+1)})' θ (U u z θ · V u z θ) ⟶ 0` as `k → ∞`,

where `U u = z ∂_z u`, `V u = z ∂_z ∂_θ u = ∂_θ (U u)` (Clairaut),
`σ = sigE θ = sin(2θ)^{-η}`, `w z = (1+z)²/z²` and `cut k` is the radial cut-off of
`Submission/Work/FTS/EllipticEst/interpol_trunc_defs.lean`.

## Route

* the angular layer bound `layer_bound_theta` (module `psiDeriv_layer`) bounds the inner
  `θ`-integral, for `0 < ε ≤ π/4`, by
  `2S₁√(2·(2^η/(1+η))·(π/4)^η)·√A_z·√(L_ε + R_ε)` with `A_z` the total `σ`-energy of the slice
  of `V u` and `L_ε`, `R_ε` its two shrinking layer energies;
* the a.e. slice data `sliceBoundAe` (module `psiDeriv_setup`) supplies the two endpoint rates
  of the slice of `U u` and the slicewise integrability, and `tendsto_layerEnergy_zero` gives
  `L_ε, R_ε → 0`;
* `w²·A_· ∈ L¹((0,∞))` is `TT.AeI1.integrableOn_w2_sliceEnergy`;
* `cut k z → 1` for every `z > 0` and `cut k ≤ 1` pointwise, and `1/((k:ℝ)+1) → 0⁺`; the
  dominated convergence theorem in `k` then gives the limit `0`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-! ## Arithmetic helpers -/

/-- `√(AL + AR) ≤ 2√A` when both layer energies are dominated by the total energy `A ≥ 0`. -/
private theorem sqrt_add_two_le {A AL AR : ℝ} (hALle : AL ≤ A) (hARle : AR ≤ A)
    (hA : 0 ≤ A) : Real.sqrt (AL + AR) ≤ 2 * Real.sqrt A := by
  have h1 : Real.sqrt (AL + AR) ≤ Real.sqrt (2 * A) := Real.sqrt_le_sqrt (by linarith)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at h1
  have h2 : Real.sqrt (2 : ℝ) ≤ 2 := by rw [Real.sqrt_le_iff]; norm_num
  nlinarith [Real.sqrt_nonneg A]

/-- `√(2·(2^η/(1+η))·(π/4)^η) ≤ 2`. -/
private theorem sqrt_const_le_two :
    Real.sqrt (2 * (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta))
      * (Real.pi / 4) ^ Work.Spaces.eta) ≤ 2 := by
  have h2η : (2 : ℝ) ^ Work.Spaces.eta ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
      (le_of_lt Work.Spaces.eta_lt_one)
  have hCs : (2 : ℝ) ^ Work.Spaces.eta / (1 + Work.Spaces.eta) ≤ 2 := by
    rw [div_le_iff₀ (by linarith [Work.Spaces.eta_pos])]
    nlinarith [h2η, Work.Spaces.eta_nonneg]
  have hpi : (Real.pi / 4) ^ Work.Spaces.eta ≤ 1 :=
    Real.rpow_le_one (x := Real.pi / 4) (z := Work.Spaces.eta) (by positivity)
      (by linarith [Real.pi_lt_four]) Work.Spaces.eta_nonneg
  have hpi0 : (0 : ℝ) ≤ (Real.pi / 4) ^ Work.Spaces.eta := Real.rpow_nonneg (by positivity) _
  have h2Cs : 2 * (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) ≤ 4 := by linarith
  have h4 : 2 * (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * (Real.pi / 4) ^ Work.Spaces.eta
      ≤ 4 := by
    have hmul := mul_le_mul h2Cs hpi hpi0 (by norm_num : (0 : ℝ) ≤ 4)
    simpa using hmul
  have h := Real.sqrt_le_sqrt h4
  rw [show Real.sqrt (4 : ℝ) = 2 from by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  exact h

/-- The layer arithmetic with the constant `8`. -/
private theorem layer_arith_two {M K A L : ℝ} (hM : 0 ≤ M) (hK : K ≤ 2) (hA : 0 ≤ A)
    (hL0 : 0 ≤ L) (hL : L ≤ 2 * Real.sqrt A) : 2 * M * K * Real.sqrt A * L ≤ 8 * M * A := by
  have h1 : 2 * M * K * Real.sqrt A ≤ 2 * M * 2 * Real.sqrt A := by
    have h3 : (0 : ℝ) ≤ 2 * M := by linarith
    calc 2 * M * K * Real.sqrt A = (2 * M) * K * Real.sqrt A := by ring
      _ ≤ (2 * M) * 2 * Real.sqrt A :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK h3) (Real.sqrt_nonneg A)
  have h4 : (0 : ℝ) ≤ 2 * M * 2 * Real.sqrt A := by positivity
  have hs : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA
  calc 2 * M * K * Real.sqrt A * L ≤ 2 * M * 2 * Real.sqrt A * L :=
        mul_le_mul_of_nonneg_right h1 hL0
    _ ≤ 2 * M * 2 * Real.sqrt A * (2 * Real.sqrt A) := mul_le_mul_of_nonneg_left hL h4
    _ = 8 * M * A := by
        rw [show (2 * M * 2 * Real.sqrt A) * (2 * Real.sqrt A)
            = 8 * M * (Real.sqrt A * Real.sqrt A) by ring, hs]

/-- The sequential angular cut-off parameter `1/((k:ℝ)+1)` lies in `(0, π/4)` for `k ≥ 1`. -/
private theorem one_div_succ_mem {k : ℕ} (hk : 1 ≤ k) :
    1 / ((k : ℝ) + 1) ∈ Set.Ioo (0 : ℝ) (Real.pi / 4) := by
  have hk2 : (2 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  constructor
  · positivity
  · have h1 : 1 / ((k : ℝ) + 1) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hk2
    have h2 : (1 : ℝ) / 2 < Real.pi / 4 := by linarith [Real.pi_gt_three]
    linarith

/-- The radial cut-off `cut k` is eventually `1` at every fixed `z > 0`. -/
private theorem cut_eventually_one {z : ℝ} (hz : 0 < z) :
    ∀ᶠ k : ℕ in Filter.atTop, Work.FTS.EllipticEst.cut k z = 1 := by
  obtain ⟨N, hN1, hN2⟩ : ∃ N : ℕ, 2 / z ≤ (N : ℝ) ∧ z / 2 ≤ (N : ℝ) :=
    ⟨max ⌈2 / z⌉₊ ⌈z / 2⌉₊,
      le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_left _ _),
      le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right _ _)⟩
  refine Filter.eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
  have hkN : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  refine Work.FTS.EllipticEst.cut_eq_one_of_mem k ?_ ?_
  · rw [div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
    have h2 : 2 / z ≤ (k : ℝ) := le_trans hN1 hkN
    calc (2 : ℝ) = z * (2 / z) := by
          rw [mul_comm, div_mul_cancel₀ 2 (ne_of_gt hz)]
      _ ≤ z * (k : ℝ) := mul_le_mul_of_nonneg_left h2 (le_of_lt hz)
      _ ≤ z * ((k : ℝ) + 1) := by nlinarith [hz]
  · have h2 : z / 2 ≤ (k : ℝ) := le_trans hN2 hkN
    nlinarith

/-! ## The target -/

theorem tendsto_term_psi_cut {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.U u))
    (hV : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.V u)) :
    Filter.Tendsto (fun k : ℕ => ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut k z
        * (Work.Spaces.w z) ^ 2 * ∫ θ in Set.Ioo 0 (Real.pi / 2),
          Work.FTS.EllipticEst.AeI1Fts.sigE θ
            * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1))) θ
            * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ))
      Filter.atTop (nhds 0) := by
  classical
  obtain ⟨M, hM⟩ := Work.FTS.EllipticEst.SliceMixedAux.exists_prof_deriv_bound
  have hMnn : 0 ≤ M :=
    le_trans (abs_nonneg (deriv Work.FTS.EllipticEst.SliceMixedAux.prof 0)) (hM 0)
  have hS : SmoothOpen u := smoothOpen_of_forall h.smooth
  have hMix := hkMem_pz_pth hS hV
  -- the a.e.-in-`z` slice data and the nonnegativity of the slice energy
  have hslice := sliceBoundAe h hU hV
  have hANonneg : ∀ z, 0 ≤ ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ := fun z =>
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo fun θ hθ =>
      mul_nonneg (sq_nonneg _) (sigE_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  -- the dominating function is integrable
  have hw2A : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ))
      (Set.Ioi 0) := by
    refine ((Work.FTS.EllipticEst.TT.AeI1.integrableOn_w2_sliceEnergy hS hMix).mono_set
      (fun z hz => le_of_lt hz)).congr_fun (fun z _ => ?_) measurableSet_Ioi
    show (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.TT.AeI1.sliceEnergy u z
      = (Work.Spaces.w z) ^ 2 * (∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ)
    rw [Work.FTS.EllipticEst.TT.AeI1.sliceEnergy_eq_Ioo]
    congr 1
  have hbound_int : MeasureTheory.Integrable
      (fun z => 8 * M * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (hw2A.const_mul (8 * M)).congr (Filter.Eventually.of_forall (fun z => by ring))
  -- the per-slice bound on the inner integral, for every `ε ∈ (0, π/4)`
  have hinner_bound : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∀ ε ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
        ‖∫ θ in Iθo, sigE θ
            * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) θ
            * (U u z θ * V u z θ)‖
          ≤ 2 * M * Real.sqrt (2 * (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta))
                * (Real.pi / 4) ^ Work.Spaces.eta)
              * Real.sqrt (∫ θ' in Iθo, (V u z θ') ^ 2 * sigE θ')
              * Real.sqrt ((∫ θ in Set.Ioo 0 ε, (V u z θ) ^ 2 * sigE θ)
                + ∫ θ in Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2),
                    (V u z θ) ^ 2 * sigE θ) := by
    filter_upwards [hslice, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hzs hzpos
    intro ε hε
    have hL := layer_bound_theta (A := ∫ θ' in Iθo, (V u z θ') ^ 2 * sigE θ')
        (ε := ε) (S₁ := M)
        (Uloc := fun θ => U u z θ) (Vloc := fun θ => V u z θ)
        (hANonneg z) hε.1 (le_of_lt hε.2) hMnn hM
        (contDiffOn_slice_U_one hS hzpos).continuousOn
        (contDiffOn_slice_V_one hS hzpos).continuousOn
        hzs.1 hzs.2.1 hzs.2.2.1 hzs.2.2.2
    simpa only [Real.norm_eq_abs] using hL
  -- the two layer energies shrink to `0`
  have hshrink : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun ε : ℝ => Real.sqrt ((∫ θ in Set.Ioo 0 ε, (V u z θ) ^ 2 * sigE θ)
          + ∫ θ in Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2), (V u z θ) ^ 2 * sigE θ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    filter_upwards [hslice, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hzs hzpos
    obtain ⟨h1, h2⟩ := tendsto_layerEnergy_zero (hzs.2.2.2)
    have hsum := h1.add h2
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hsum
    simpa only [Function.comp_def, Real.sqrt_zero, zero_add] using hs
  -- the sequential parameter tends to `0` within `(0,∞)`
  have hdelta : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      (Filter.Eventually.of_forall fun k => by
        simp only [Set.mem_Ioi]; exact div_pos one_pos (by positivity))
  -- the pointwise convergence of the integrand
  have hpointwise : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun k : ℕ => Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2
          * ∫ θ in Iθo, sigE θ
              * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1))) θ
              * (U u z θ * V u z θ))
        Filter.atTop (nhds 0) := by
    filter_upwards [hinner_bound, hshrink, MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with z hz hsh hzpos
    have hlim : Filter.Tendsto (fun ε : ℝ => ∫ θ in Iθo, sigE θ
          * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) θ * (U u z θ * V u z θ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hsmall : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          ε ∈ Set.Ioo (0 : ℝ) (Real.pi / 4) := by
        have h4 : Set.Iio (Real.pi / 4) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
          nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (by rw [Set.mem_Iio]; positivity))
        filter_upwards [self_mem_nhdsWithin, h4] with ε hε hε4
        exact ⟨hε, hε4⟩
      have hb : Filter.Tendsto (fun ε : ℝ => 2 * M * Real.sqrt (2 * (2 ^ Work.Spaces.eta
            / (1 + Work.Spaces.eta)) * (Real.pi / 4) ^ Work.Spaces.eta)
            * Real.sqrt (∫ θ' in Iθo, (V u z θ') ^ 2 * sigE θ')
            * Real.sqrt ((∫ θ in Set.Ioo 0 ε, (V u z θ) ^ 2 * sigE θ)
              + ∫ θ in Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2),
                  (V u z θ) ^ 2 * sigE θ))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        have hc := hsh.const_mul (2 * M * Real.sqrt (2 * (2 ^ Work.Spaces.eta
            / (1 + Work.Spaces.eta)) * (Real.pi / 4) ^ Work.Spaces.eta)
            * Real.sqrt (∫ θ' in Iθo, (V u z θ') ^ 2 * sigE θ'))
        simpa using hc
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [hsmall] with ε hε
      exact hz ε hε
    have hcomp := hlim.comp hdelta
    have hcutlim : Filter.Tendsto (fun k : ℕ => Work.FTS.EllipticEst.cut k z)
        Filter.atTop (nhds 1) :=
      Filter.Tendsto.congr'
        ((cut_eventually_one hzpos).mono (fun k hk => hk.symm)) tendsto_const_nhds
    have hprod : Filter.Tendsto (fun k : ℕ => Work.FTS.EllipticEst.cut k z
        * ∫ θ in Iθo, sigE θ
            * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1))) θ
            * (U u z θ * V u z θ)) Filter.atTop (nhds (1 * 0)) := hcutlim.mul hcomp
    have hprod2 := hprod.const_mul ((Work.Spaces.w z) ^ 2)
    have hprod3 : Filter.Tendsto (fun k : ℕ => (Work.Spaces.w z) ^ 2
        * (Work.FTS.EllipticEst.cut k z
          * ∫ θ in Iθo, sigE θ
              * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1))) θ
              * (U u z θ * V u z θ))) Filter.atTop (nhds 0) := by
      simpa using hprod2
    exact Filter.Tendsto.congr' (Filter.Eventually.of_forall fun k => by ring) hprod3
  -- dominated convergence in `k`
  have hDCT : Filter.Tendsto (fun k : ℕ => ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut k z
        * (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo,
          sigE θ * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1))) θ
            * (U u z θ * V u z θ))
      Filter.atTop (nhds (∫ z in (Set.Ioi 0 : Set ℝ), (0 : ℝ))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := MeasureTheory.volume.restrict (Set.Ioi 0))
      (l := Filter.atTop)
      (F := fun (k : ℕ) (z : ℝ) => Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2
        * ∫ θ in Iθo, sigE θ
            * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1))) θ
            * (U u z θ * V u z θ))
      (f := fun _ => 0)
      (fun z => 8 * M * (Work.Spaces.w z) ^ 2
        * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ) ?_ ?_ hbound_int ?_
    · filter_upwards with k
      exact (((measurable_cut k).aestronglyMeasurable).mul aestronglyMeasurable_w_sq).mul
        (aestronglyMeasurable_inner hS (1 / ((k : ℝ) + 1)))
    · filter_upwards [Filter.eventually_ge_atTop 1] with k hk
      filter_upwards [hinner_bound, hslice, MeasureTheory.ae_restrict_mem measurableSet_Ioi]
        with z hz hzs hzpos
      have hkδ := one_div_succ_mem hk
      have hL := hz (1 / ((k : ℝ) + 1)) hkδ
      have hcut0 : 0 ≤ Work.FTS.EllipticEst.cut k z := Work.FTS.EllipticEst.cut_nonneg k z
      have hcut1 : Work.FTS.EllipticEst.cut k z ≤ 1 := Work.FTS.EllipticEst.cut_le_one k z
      have hw : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have hALle : (∫ θ in Set.Ioo 0 (1 / ((k : ℝ) + 1)), (V u z θ) ^ 2 * sigE θ)
          ≤ ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ := by
        refine MeasureTheory.setIntegral_mono_set hzs.2.2.2 ?_ ?_
        · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
          exact mul_nonneg (sq_nonneg _) (sigE_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
        · filter_upwards with θ hθ
          exact ⟨hθ.1, by linarith [hθ.2, hkδ.2, Real.pi_pos]⟩
      have hARle : (∫ θ in Set.Ioo (Real.pi / 2 - 1 / ((k : ℝ) + 1)) (Real.pi / 2),
              (V u z θ) ^ 2 * sigE θ)
          ≤ ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ := by
        refine MeasureTheory.setIntegral_mono_set hzs.2.2.2 ?_ ?_
        · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
          exact mul_nonneg (sq_nonneg _) (sigE_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
        · filter_upwards with θ hθ
          exact ⟨by linarith [hkδ.1, hkδ.2, hθ.1, Real.pi_pos], hθ.2⟩
      have hsum := sqrt_add_two_le hALle hARle (hANonneg z)
      have harith := layer_arith_two (M := M) (K := Real.sqrt (2 * (2 ^ Work.Spaces.eta
            / (1 + Work.Spaces.eta)) * (Real.pi / 4) ^ Work.Spaces.eta))
        (A := ∫ θ' in Iθo, (V u z θ') ^ 2 * sigE θ')
        (L := Real.sqrt ((∫ θ in Set.Ioo 0 (1 / ((k : ℝ) + 1)), (V u z θ) ^ 2 * sigE θ)
          + ∫ θ in Set.Ioo (Real.pi / 2 - 1 / ((k : ℝ) + 1)) (Real.pi / 2),
              (V u z θ) ^ 2 * sigE θ))
        hMnn sqrt_const_le_two (hANonneg z) (Real.sqrt_nonneg _) hsum
      have hinner_le : ‖∫ θ in Iθo, sigE θ
            * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1))) θ
            * (U u z θ * V u z θ)‖
          ≤ 8 * M * (∫ θ' in Iθo, (V u z θ') ^ 2 * sigE θ') := hL.trans harith
      have hcutw : Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2
          ≤ 1 * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hcut1 hw
      have hJ : Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2
            * |∫ θ in Iθo, sigE θ
                * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1))) θ
                * (U u z θ * V u z θ)|
          ≤ 8 * M * (Work.Spaces.w z) ^ 2 * (∫ θ' in Iθo, (V u z θ') ^ 2 * sigE θ') := by
        have h1 := mul_le_mul hcutw hinner_le (abs_nonneg _) (by positivity :
            (0 : ℝ) ≤ 1 * (Work.Spaces.w z) ^ 2)
        calc Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2
              * |∫ θ in Iθo, sigE θ
                  * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1))) θ
                  * (U u z θ * V u z θ)|
            ≤ (1 * (Work.Spaces.w z) ^ 2)
                * (8 * M * (∫ θ' in Iθo, (V u z θ') ^ 2 * sigE θ')) := h1
          _ = 8 * M * (Work.Spaces.w z) ^ 2 * (∫ θ' in Iθo, (V u z θ') ^ 2 * sigE θ') := by
              ring
      calc ‖Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2
              * ∫ θ in Iθo, sigE θ
                  * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1))) θ
                  * (U u z θ * V u z θ)‖
          = Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2
              * |∫ θ in Iθo, sigE θ
                  * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1))) θ
                  * (U u z θ * V u z θ)| := by
            rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hcut0, abs_of_nonneg hw]
        _ ≤ 8 * M * (Work.Spaces.w z) ^ 2 * (∫ θ' in Iθo, (V u z θ') ^ 2 * sigE θ') := hJ
    · exact hpointwise
  simpa only [Pi.zero_apply, integral_zero] using hDCT

end Work.FTS.EllipticEst.AeI1Fts
