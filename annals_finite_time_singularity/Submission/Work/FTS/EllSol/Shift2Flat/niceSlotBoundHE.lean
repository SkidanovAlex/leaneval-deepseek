/-
Copyright: work module for the Elgindi finite-time singularity project.

# The heavy-weight shifted flat 2-D Agmon slot bound

`Work.FTS.EllSol.Shift2Flat.niceSlotBoundHE` is the *heavy-weight* form of the shifted flat
2-D Agmon estimate: the `lintegral`-level statement of
`Work.FTS.EllSol.SpecAux.shiftedSlot11Lin_core`, but with the light angular weight
`wA α = sin(2θ)^{2-γ(α)}` on the left-hand side replaced by the heavy weight
`wE = sin(2θ)^{-η}` (which is the weight `Work.FTS.EllipticEst.thEta` of the one-dimensional
slot hypothesis `hCc`).

The proof is the same Plancherel-in-`t` derivation: the per-frequency (`ξ`) angular Agmon
inequality `hCc` is applied to the slices `Φ_ξ(θ) = ∫_t u(t,θ) e^{-2πiξt} dt`, then
multiplied by the shifted frequency weight `μ(ξ) = (2πξ)² + b²` and integrated in `ξ`.  The
three Plancherel data are supplied as hypotheses (`hplanch1`, `hplanch2`, `hplanchlhs`); the
light/heavy comparison step of `shiftedSlot11Lin_core` disappears because the left-hand weight
of `hCc` *is* the heavy weight.

* the four Plancherel identifications `hidShiftOne/Two/Three` (from
  `SpecAux.ShiftSlot11Idents`) and `hidShiftLhsE` (below) identify the `(ξ,θ)`-integrals with
  the `(t,θ)`-integrals;
* Cauchy–Schwarz uses `μ √(A·D) = √((μ² A)·D)`, which produces exactly the `(∂_t-b)²u`-slot
  times the `∂_θ²u`-slot.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.SpecAux.ShiftSlot11Lin
import Submission.Work.FTS.EllSol.SpecAux.ShiftSlot11Idents
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Shift2Flat

open MeasureTheory Set Filter
open scoped Real Topology ContDiff ENNReal
open Work.Spaces
open Work.FTS.EllSol.FlatFT
open Work.FTS.EllSol.SpecAux

noncomputable section

set_option maxHeartbeats 4000000

local notation "thEta" => Work.FTS.EllipticEst.thEta

/-- The left-hand Plancherel identification of the shifted slot, with the *heavy* angular
weight `wE`: the `ξ`-integral of `μ(ξ) = (2πξ)² + b²` times the slice energy of `∂_θu` equals
the `(t,θ)`-integral of `(∂_θ(∂_t - b)u)² wE`.  (This is `hidShiftLhs` with `wA α` replaced
by `wE`.) -/
theorem hidShiftLhsE {u : ℝ → ℝ → ℝ} {b : ℝ} (hg : NiceFlat u)
    (hJ : ∀ ξ : ℝ, MeasureTheory.IntegrableOn
      (fun θ : ℝ => ‖slice (pth u) ξ θ‖ ^ 2 * wE θ) Iθ)
    (hplanch : ∀ᵐ θ ∂((volume : Measure ℝ).restrict Iθ),
      MeasureTheory.Integrable (fun ξ : ℝ => muW b ξ * ‖slice (pth u) ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, muW b ξ * ‖slice (pth u) ξ θ‖ ^ 2)
        = ∫ t : ℝ, (pth (pz u) t θ - b * pth u t θ) ^ 2) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal (muW b ξ
        * ∫ θ in Iθ, ‖slice (pth u) ξ θ‖ ^ 2 * wE θ))
      = ∫⁻ p in Set.univ ×ˢ Iθ, ENNReal.ofReal
          ((pth (pz u) p.1 p.2 - b * pth u p.1 p.2) ^ 2 * wE p.2) := by
  obtain ⟨M, hM0, hM⟩ := niceFlat_supp hg
  have hcd_u : ContDiffOn ℝ 2 (Function.uncurry u) flStrip := hg.1
  have hcd_pth : ContDiffOn ℝ 1 (Function.uncurry (pth u)) flStrip :=
    pth_contDiffOn_succ flStrip_isOpen hcd_u
  have hcd_pz : ContDiffOn ℝ 1 (Function.uncurry (pz u)) flStrip :=
    pz_contDiffOn_succ flStrip_isOpen hcd_u
  have hsupp_pz : ∀ t θ : ℝ, M < |t| → pz u t θ = 0 := supp_pz hM
  have hsupp_pth : ∀ t θ : ℝ, M < |t| → pth u t θ = 0 := supp_pth hM
  have hsupp_pthpz : ∀ t θ : ℝ, M < |t| → pth (pz u) t θ = 0 :=
    fun t θ ht => pth_eq_zero_of_forall (fun θ' => hsupp_pz t θ' ht)
  have hsupp_lhsψ : ∀ t θ : ℝ, M < |t| → pth (pz u) t θ - b * pth u t θ = 0 :=
    fun t θ ht => by rw [hsupp_pthpz t θ ht, hsupp_pth t θ ht]; ring
  have hcont_lhsψ : ContinuousOn
      (Function.uncurry (fun t θ : ℝ => pth (pz u) t θ - b * pth u t θ)) flStrip :=
    ((pth_contDiffOn_succ flStrip_isOpen hcd_pz).continuousOn).sub
      (hcd_pth.continuousOn.const_mul b)
  have hsl_pth : ContinuousOn (fun p : ℝ × ℝ => slice (pth u) p.1 p.2) flStrip :=
    continuousOn_slice_joint hcd_pth.continuousOn ⟨M, hM0, hsupp_pth⟩
  have hφ : ∀ᵐ θ ∂((volume : Measure ℝ).restrict Iθ),
      MeasureTheory.Integrable (fun t : ℝ => (pth (pz u) t θ - b * pth u t θ) ^ 2) :=
    ae_mem_Ioo_Iθ.mono (fun θ hθ => integrable_sq_slice hM0 hcont_lhsψ hsupp_lhsψ hθ)
  exact lintegral_slice_plancherel (pth u) (fun t θ : ℝ => pth (pz u) t θ - b * pth u t θ)
    (muW b) wE (muW_nonneg b) (fun θ hθ => wE_nonneg hθ) hJ hφ hplanch
    (aemeasurable_ofReal_weight_mul hsl_pth (measurable_muW b) measurable_wE)
    (aemeasurable_ofReal_sq_mul_snd hcont_lhsψ measurable_wE)

theorem niceSlotBoundHE {Cc : ℝ} (hCcpos : 0 < Cc)
    (hCc : ∀ F : ℝ → ℂ, ContDiffOn ℝ 2 F (Set.Ioo 0 (Real.pi / 2)) → F 0 = 0 →
      F (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn (fun θ : ℝ => ‖F θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => ‖deriv F θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => ‖deriv (deriv F) θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, ‖deriv F θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) ≤
        Cc * ((∫ θ in Work.Spaces.Iθ, ‖F θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) +
          Real.sqrt ((∫ θ in Work.Spaces.Iθ, ‖F θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) *
            (∫ θ in Work.Spaces.Iθ, ‖deriv (deriv F) θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ))))
    (b : ℝ) (u : ℝ → ℝ → ℝ) (hg : Work.FTS.EllSol.FlatFT.NiceFlat u)
    (hplanch1 : ∀ᵐ θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ),
      MeasureTheory.Integrable (fun ξ : ℝ => Work.FTS.EllSol.SpecAux.muW b ξ * ‖Work.FTS.EllSol.FlatFT.slice u ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, Work.FTS.EllSol.SpecAux.muW b ξ * ‖Work.FTS.EllSol.FlatFT.slice u ξ θ‖ ^ 2) = ∫ t : ℝ, (Work.Spaces.pz u t θ - b * u t θ) ^ 2)
    (hplanch2 : ∀ᵐ θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ),
      MeasureTheory.Integrable (fun ξ : ℝ => (Work.FTS.EllSol.SpecAux.muW b ξ) ^ 2 * ‖Work.FTS.EllSol.FlatFT.slice u ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, (Work.FTS.EllSol.SpecAux.muW b ξ) ^ 2 * ‖Work.FTS.EllSol.FlatFT.slice u ξ θ‖ ^ 2) = ∫ t : ℝ, (Work.Spaces.pz (Work.Spaces.pz u) t θ - 2 * b * Work.Spaces.pz u t θ + b ^ 2 * u t θ) ^ 2)
    (hplanchlhs : ∀ᵐ θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ),
      MeasureTheory.Integrable (fun ξ : ℝ => Work.FTS.EllSol.SpecAux.muW b ξ * ‖Work.FTS.EllSol.FlatFT.slice (Work.Spaces.pth u) ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, Work.FTS.EllSol.SpecAux.muW b ξ * ‖Work.FTS.EllSol.FlatFT.slice (Work.Spaces.pth u) ξ θ‖ ^ 2) = ∫ t : ℝ, (Work.Spaces.pth (Work.Spaces.pz u) t θ - b * Work.Spaces.pth u t θ) ^ 2)
    (hSp : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ))
    (hSpp : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ))
    (hQ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ)) :
    (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pz u) p.1 p.2 - b * Work.Spaces.pth u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2))
      ≤ ENNReal.ofReal (Cc * ((∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
          + Real.sqrt ((∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2) * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)))) := by
  obtain ⟨M, hM0, hM⟩ := niceFlat_supp hg
  have hs : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Iθ) :=
    MeasurableSet.univ.prod measurableSet_Iθ
  have hcd_u : ContDiffOn ℝ 2 (Function.uncurry u) flStrip := hg.1
  have hsupp_pthpth : ∀ t θ : ℝ, M < |t| → pth (pth u) t θ = 0 := supp_pthpth hM
  have hsl_u : ContinuousOn (fun p : ℝ × ℝ => slice u p.1 p.2) flStrip :=
    continuousOn_slice_joint hcd_u.continuousOn ⟨M, hM0, hM⟩
  have hsl_q : ContinuousOn (fun p : ℝ × ℝ => slice (pth (pth u)) p.1 p.2) flStrip :=
    continuousOn_slice_joint
      (pth_contDiffOn_succ flStrip_isOpen
        (pth_contDiffOn_succ flStrip_isOpen hcd_u)).continuousOn
      ⟨M, hM0, hsupp_pthpth⟩
  -- ## the slice integrabilities of the three heavy slots (and of the light slot, unused)
  obtain ⟨hJg, hJpth, -, hJq⟩ := slotSliceFacts 0 (by norm_num) hg hQ
  -- ## the four Plancherel identifications
  have hid1 := hidShiftOne hg hJg hplanch1
  have hid2 := hidShiftTwo hg hJg hplanch2
  have hid3 := hidShiftThree hg hJq
  have hidlhs := hidShiftLhsE hg hJpth hplanchlhs
  -- ## the `∫⁻`/`∫` conversion of the three right-hand slots
  have hnn_s : 0 ≤ᵐ[((volume : Measure (ℝ × ℝ))).restrict (Set.univ ×ˢ Iθ)]
      (fun p : ℝ × ℝ => (pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * wE p.2) :=
    (ae_restrict_mem hs).mono fun p hp => mul_nonneg (sq_nonneg _) (wE_nonneg hp.2)
  have hnn_s2 : 0 ≤ᵐ[((volume : Measure (ℝ × ℝ))).restrict (Set.univ ×ˢ Iθ)]
      (fun p : ℝ × ℝ => (pz (pz u) p.1 p.2 - 2 * b * pz u p.1 p.2
        + b ^ 2 * u p.1 p.2) ^ 2 * wE p.2) :=
    (ae_restrict_mem hs).mono fun p hp => mul_nonneg (sq_nonneg _) (wE_nonneg hp.2)
  have hnn_q : 0 ≤ᵐ[((volume : Measure (ℝ × ℝ))).restrict (Set.univ ×ˢ Iθ)]
      (fun p : ℝ × ℝ => (pth (pth u) p.1 p.2) ^ 2 * wE p.2) :=
    (ae_restrict_mem hs).mono fun p hp => mul_nonneg (sq_nonneg _) (wE_nonneg hp.2)
  have hP : (∫⁻ p in Set.univ ×ˢ Iθ, ENNReal.ofReal
        ((pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * wE p.2))
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Iθ,
          (pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * wE p.2) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hSp hnn_s).symm
  have hP2 : (∫⁻ p in Set.univ ×ˢ Iθ, ENNReal.ofReal
        ((pz (pz u) p.1 p.2 - 2 * b * pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2 * wE p.2))
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Iθ,
          (pz (pz u) p.1 p.2 - 2 * b * pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2 * wE p.2) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hSpp hnn_s2).symm
  have hQ2 : (∫⁻ p in Set.univ ×ˢ Iθ, ENNReal.ofReal
        ((pth (pth u) p.1 p.2) ^ 2 * wE p.2))
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Iθ,
          (pth (pth u) p.1 p.2) ^ 2 * wE p.2) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hQ hnn_q).symm
  -- ## the per-frequency angular Agmon bound (this is where `hCc` enters)
  have hξA : ∀ ξ : ℝ,
      (∫ θ in Iθ, ‖slice (pth u) ξ θ‖ ^ 2 * wE θ)
        ≤ Cc * ((∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
          + Real.sqrt ((∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
              * (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ))) := by
    intro ξ
    have hΦcd : ContDiffOn ℝ 2 (fun θ : ℝ => slice u ξ θ) (Set.Ioo 0 (Real.pi / 2)) :=
      sliceContDiffOn (n := 2) (by norm_num) hcd_u ⟨M, hM0, hM⟩ ξ
    have hderiv_ae : (fun θ : ℝ => deriv (fun θ' => slice u ξ θ') θ)
        =ᵐ[(volume : Measure ℝ).restrict Iθ]
          (fun θ : ℝ => slice (pth u) ξ θ) := by
      have hcongr : Set.Ioo (0 : ℝ) (Real.pi / 2) =ᵐ[(volume : Measure ℝ)] Iθ :=
        MeasureTheory.Ioo_ae_eq_Icc
      rw [← MeasureTheory.Measure.restrict_congr_set hcongr]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact (slice_hasDerivAt u hg ξ hθ).1.deriv
    have hderiv2_ae : (fun θ : ℝ => deriv (deriv (fun θ'' => slice u ξ θ'')) θ)
        =ᵐ[(volume : Measure ℝ).restrict Iθ]
          (fun θ : ℝ => slice (pth (pth u)) ξ θ) := by
      have hcongr : Set.Ioo (0 : ℝ) (Real.pi / 2) =ᵐ[(volume : Measure ℝ)] Iθ :=
        MeasureTheory.Ioo_ae_eq_Icc
      rw [← MeasureTheory.Measure.restrict_congr_set hcongr]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hev : (fun θ' => deriv (fun θ'' => slice u ξ θ'') θ')
          =ᶠ[𝓝 θ] (fun θ' => slice (pth u) ξ θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact (slice_hasDerivAt u hg ξ hθ').1.deriv
      rw [hev.deriv_eq, (slice_hasDerivAt u hg ξ hθ).2.deriv]
    have hI1 : MeasureTheory.IntegrableOn
        (fun θ : ℝ => ‖deriv (fun θ' => slice u ξ θ') θ‖ ^ 2 * thEta θ) Iθ :=
      (hJpth ξ).congr (by filter_upwards [hderiv_ae] with θ hθ; rw [hθ]; rfl)
    have hI2 : MeasureTheory.IntegrableOn
        (fun θ : ℝ => ‖deriv (deriv (fun θ'' => slice u ξ θ'')) θ‖ ^ 2 * thEta θ) Iθ :=
      (hJq ξ).congr (by filter_upwards [hderiv2_ae] with θ hθ; rw [hθ]; rfl)
    have hkey := hCc (fun θ : ℝ => slice u ξ θ) hΦcd (slice_eq_zero hg ξ)
      (slice_eq_zero_pi hg ξ) (hJg ξ) hI1 hI2
    have e1 : (∫ θ in Iθ, ‖deriv (fun θ' => slice u ξ θ') θ‖ ^ 2 * thEta θ)
        = ∫ θ in Iθ, ‖slice (pth u) ξ θ‖ ^ 2 * wE θ :=
      integral_congr_ae (by filter_upwards [hderiv_ae] with θ hθ; rw [hθ]; rfl)
    have e2 : (∫ θ in Iθ, ‖deriv (deriv (fun θ'' => slice u ξ θ'')) θ‖ ^ 2 * thEta θ)
        = ∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ :=
      integral_congr_ae (by filter_upwards [hderiv2_ae] with θ hθ; rw [hθ]; rfl)
    rw [e1, e2] at hkey
    exact hkey
  -- ## the three right-hand real integrals and their non-negativity
  have hPnn : 0 ≤ ∫ p in Set.univ ×ˢ Iθ,
      (pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * wE p.2 :=
    integral_nonneg_of_ae ((ae_restrict_mem hs).mono fun p hp =>
      mul_nonneg (sq_nonneg _) (wE_nonneg hp.2))
  have hP2nn : 0 ≤ ∫ p in Set.univ ×ˢ Iθ,
      (pz (pz u) p.1 p.2 - 2 * b * pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2 * wE p.2 :=
    integral_nonneg_of_ae ((ae_restrict_mem hs).mono fun p hp =>
      mul_nonneg (sq_nonneg _) (wE_nonneg hp.2))
  have hQ2nn : 0 ≤ ∫ p in Set.univ ×ˢ Iθ,
      (pth (pth u) p.1 p.2) ^ 2 * wE p.2 :=
    integral_nonneg_of_ae ((ae_restrict_mem hs).mono fun p hp =>
      mul_nonneg (sq_nonneg _) (wE_nonneg hp.2))
  -- ## the slice energies as functions of `ξ`
  have hAnon : ∀ ξ : ℝ, 0 ≤ ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ :=
    fun ξ => integral_nonneg_of_ae
      (ae_mem_Iθ.mono fun θ hθ => mul_nonneg (sq_nonneg _) (wE_nonneg hθ))
  have hDnon : ∀ ξ : ℝ, 0 ≤ ∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ :=
    fun ξ => integral_nonneg_of_ae
      (ae_mem_Iθ.mono fun θ hθ => mul_nonneg (sq_nonneg _) (wE_nonneg hθ))
  have hAmeas : AEStronglyMeasurable
      (fun ξ : ℝ => ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
      (volume : Measure ℝ) :=
    (aemeasurable_slice_sq_mul_snd hsl_u measurable_wE).aestronglyMeasurable
      |>.integral_prod_right'
  have hDmeas : AEStronglyMeasurable
      (fun ξ : ℝ => ∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ)
      (volume : Measure ℝ) :=
    (aemeasurable_slice_sq_mul_snd hsl_q measurable_wE).aestronglyMeasurable
      |>.integral_prod_right'
  -- ## the two heavy slots, as `lintegral`s of the shifted squares
  have hlimA : (∫⁻ ξ : ℝ, ENNReal.ofReal (muW b ξ
        * ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ))
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Iθ,
          (pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * wE p.2) := hid1.trans hP
  have hlimA2 : (∫⁻ ξ : ℝ, ENNReal.ofReal ((muW b ξ) ^ 2
        * ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ))
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Iθ,
          (pz (pz u) p.1 p.2 - 2 * b * pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2 * wE p.2) :=
    hid2.trans hP2
  have hlimD : (∫⁻ ξ : ℝ, ENNReal.ofReal
        (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ))
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Iθ,
          (pth (pth u) p.1 p.2) ^ 2 * wE p.2) := by
    have h := hid3
    rw [show (∫⁻ ξ : ℝ, ENNReal.ofReal ((1 : ℝ)
          * ∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ))
        = ∫⁻ ξ : ℝ, ENNReal.ofReal
            (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ) from
      lintegral_congr fun ξ => by rw [one_mul]] at h
    rw [h, hQ2]
  -- ## integrability of the two `ξ`-side heavy slots
  have hintA2 : MeasureTheory.Integrable (fun ξ : ℝ => (muW b ξ) ^ 2
      * ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ) := by
    refine (lintegral_ofReal_ne_top_iff_integrable ?_ ?_).mp ?_
    · exact (measurable_muW b |>.pow_const 2).aestronglyMeasurable.mul hAmeas
    · exact Eventually.of_forall fun ξ => mul_nonneg (by positivity) (hAnon ξ)
    · rw [hlimA2]
      exact ENNReal.ofReal_ne_top
  have hintD : MeasureTheory.Integrable
      (fun ξ : ℝ => ∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ) := by
    refine (lintegral_ofReal_ne_top_iff_integrable ?_ ?_).mp ?_
    · exact hDmeas
    · exact Eventually.of_forall hDnon
    · rw [hlimD]
      exact ENNReal.ofReal_ne_top
  -- ## Cauchy–Schwarz for the geometric-mean term
  have hcs := integral_mul_le_sqrt_mul
    (fun ξ : ℝ => muW b ξ * Real.sqrt (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ))
    (fun ξ : ℝ => Real.sqrt (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ))
    (fun ξ => mul_nonneg (muW_nonneg b ξ) (Real.sqrt_nonneg _))
    (fun ξ => Real.sqrt_nonneg _)
    (by
      refine hintA2.congr (Eventually.of_forall fun ξ => ?_)
      show (muW b ξ) ^ 2 * ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ
        = (muW b ξ * Real.sqrt (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)) ^ 2
      have hsq : (Real.sqrt (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)) ^ 2
          = ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ := Real.sq_sqrt (hAnon ξ)
      calc (muW b ξ) ^ 2 * ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ
          = (muW b ξ) ^ 2
              * (Real.sqrt (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)) ^ 2 := by
            rw [hsq]
        _ = (muW b ξ
              * Real.sqrt (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)) ^ 2 := by
            ring)
    (by
      refine hintD.congr (Eventually.of_forall fun ξ => ?_)
      show ∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ
        = (Real.sqrt (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ)) ^ 2
      rw [Real.sq_sqrt (hDnon ξ)])
  have h1sq : (∫ ξ : ℝ, (muW b ξ
        * Real.sqrt (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)) ^ 2)
      = ∫ p in Set.univ ×ˢ Iθ,
          (pz (pz u) p.1 p.2 - 2 * b * pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2
            * wE p.2 := by
    have h : (∫ ξ : ℝ, (muW b ξ
          * Real.sqrt (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)) ^ 2)
        = ∫ ξ : ℝ, (muW b ξ) ^ 2
            * ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ :=
      integral_congr_ae (Eventually.of_forall fun ξ => by
        show (muW b ξ
            * Real.sqrt (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)) ^ 2
          = (muW b ξ) ^ 2 * ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ
        rw [mul_pow, Real.sq_sqrt (hAnon ξ)])
    rw [h]
    refine (ENNReal.ofReal_eq_ofReal_iff ?_ ?_).mp ?_
    · exact integral_nonneg fun ξ => mul_nonneg (by positivity) (hAnon ξ)
    · exact hP2nn
    · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintA2
        (Eventually.of_forall fun ξ => mul_nonneg (by positivity) (hAnon ξ))]
      exact hlimA2
  have h2sq : (∫ ξ : ℝ, (Real.sqrt (∫ θ in Iθ,
        ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ)) ^ 2)
      = ∫ p in Set.univ ×ˢ Iθ, (pth (pth u) p.1 p.2) ^ 2 * wE p.2 := by
    have h : (∫ ξ : ℝ, (Real.sqrt (∫ θ in Iθ,
          ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ)) ^ 2)
        = ∫ ξ : ℝ, ∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ :=
      integral_congr_ae (Eventually.of_forall fun ξ => by
        show (Real.sqrt (∫ θ in Iθ,
            ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ)) ^ 2
          = ∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ
        rw [Real.sq_sqrt (hDnon ξ)])
    rw [h]
    refine (ENNReal.ofReal_eq_ofReal_iff ?_ ?_).mp ?_
    · exact integral_nonneg fun ξ => hDnon ξ
    · exact hQ2nn
    · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintD
        (Eventually.of_forall fun ξ => hDnon ξ)]
      exact hlimD
  have hcs' : (∫ ξ : ℝ, muW b ξ
        * Real.sqrt ((∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
            * (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ)))
      ≤ Real.sqrt ((∫ p in Set.univ ×ˢ Iθ,
              (pz (pz u) p.1 p.2 - 2 * b * pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2
                * wE p.2)
          * (∫ p in Set.univ ×ˢ Iθ, (pth (pth u) p.1 p.2) ^ 2 * wE p.2)) := by
    have hL : (∫ ξ : ℝ, muW b ξ
          * Real.sqrt ((∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
              * (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ)))
        = ∫ ξ : ℝ, (muW b ξ
              * Real.sqrt (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ))
            * Real.sqrt (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ) :=
      integral_congr_ae (Eventually.of_forall fun ξ => by
        show muW b ξ
            * Real.sqrt ((∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
              * (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ))
          = (muW b ξ * Real.sqrt (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ))
              * Real.sqrt (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ)
        rw [Real.sqrt_mul (hAnon ξ)]
        ring)
    rw [hL]
    have h := hcs.2
    rw [h1sq, h2sq] at h
    exact h
  -- ## the pointwise (in `ξ`) bound after multiplying by `μ`
  have hptw : ∀ ξ : ℝ,
      ENNReal.ofReal (muW b ξ
          * ∫ θ in Iθ, ‖slice (pth u) ξ θ‖ ^ 2 * wE θ)
        ≤ ENNReal.ofReal Cc * (ENNReal.ofReal (muW b ξ
              * ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
          + ENNReal.ofReal (muW b ξ
              * Real.sqrt ((∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
                  * (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ)))) := by
    intro ξ
    have hW0 : (0 : ℝ) ≤ muW b ξ := muW_nonneg b ξ
    have hAξ : 0 ≤ ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ := hAnon ξ
    have hkey : muW b ξ * (∫ θ in Iθ, ‖slice (pth u) ξ θ‖ ^ 2 * wE θ)
        ≤ Cc * (muW b ξ * (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
          + muW b ξ * Real.sqrt ((∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
              * (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ))) := by
      have h1 := mul_le_mul_of_nonneg_left (hξA ξ) hW0
      refine h1.trans (le_of_eq ?_)
      ring
    refine (ENNReal.ofReal_le_ofReal hkey).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (le_of_lt hCcpos),
      ENNReal.ofReal_add (mul_nonneg hW0 hAξ) (mul_nonneg hW0 (Real.sqrt_nonneg _))]
  have hpair_int : MeasureTheory.Integrable (fun ξ : ℝ => muW b ξ
      * Real.sqrt ((∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
          * (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ))) :=
    hcs.1.congr (Eventually.of_forall fun ξ => by
      show (muW b ξ * Real.sqrt (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ))
            * Real.sqrt (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ)
          = muW b ξ * Real.sqrt ((∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
              * (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ))
      rw [Real.sqrt_mul (hAnon ξ)]
      ring)
  have hpair_nn : ∀ ξ : ℝ, 0 ≤ muW b ξ
      * Real.sqrt ((∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
          * (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ)) :=
    fun ξ => mul_nonneg (muW_nonneg b ξ) (Real.sqrt_nonneg _)
  have hAmeas2 : AEMeasurable (fun ξ : ℝ => ENNReal.ofReal (muW b ξ
      * ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)) (volume : Measure ℝ) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((measurable_muW b).aemeasurable).mul hAmeas.aemeasurable)
  -- ## the final chain
  rw [← hidlhs]
  refine (lintegral_mono hptw).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' hAmeas2,
    ENNReal.ofReal_mul (le_of_lt hCcpos),
    ENNReal.ofReal_add hPnn (Real.sqrt_nonneg _)]
  refine mul_le_mul' le_rfl (add_le_add ?_ ?_)
  · exact le_of_eq hlimA
  · rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hpair_int
      (Eventually.of_forall hpair_nn)]
    exact ENNReal.ofReal_le_ofReal hcs'

end

end Work.FTS.EllSol.Shift2Flat
