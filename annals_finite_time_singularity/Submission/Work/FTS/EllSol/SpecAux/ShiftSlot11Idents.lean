/-
Copyright: work module for the Elgindi finite-time singularity project.

# The shifted Plancherel identifications for the flat 2-D Agmon slot `(1,1)`

Auxiliary module of `Work.FTS.EllSol.SpecAux.ShiftSlot11Lin`: the four
`lintegral`-identifications of the shifted slots (heavy slot one with weight `μ`, heavy slot two
with weight `μ²`, the `θ`-slot with weight `1`, and the left-hand slot with weight `μ`), all of
them instances of the general Tonelli/Plancherel lemma `lintegral_slice_plancherel`, together
with the fixed-`ξ` slice integrability facts of the five slots.

Here `μ(ξ) = (2πξ)² + b²` is the squared modulus of the shifted Fourier multiplier
`2πiξ - b`, and `wE = sin(2θ)^{-η}`, `wA α = sin(2θ)^{2-γ(α)}` are the two angular weights.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.FTS.EllSol.FlatFT.Flat2DAgmonNiceBPrelim1
import Submission.Work.FTS.EllSol.FlatFT.Flat2DAgmonNiceBPrelim2
import Submission.Work.FTS.EllSol.FlatFT.continuousOn_slice_joint
import Submission.Work.FTS.EllSol.FlatFT.sliceContDiffOn
import Submission.Work.FTS.EllSol.FlatFT.dthBound
import Submission.Work.FTS.EllSol.FlatFT.integrableOn_energy_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.SpecAux

open MeasureTheory Set Filter
open scoped Real Topology ContDiff ENNReal
open Work.Spaces
open Work.FTS.EllSol.FlatFT

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The shifted frequency weight `μ(ξ) = (2πξ)² + b² = ‖2πiξ - b‖²`. -/
abbrev muW (b ξ : ℝ) : ℝ := (2 * Real.pi * ξ) ^ 2 + b ^ 2

theorem muW_nonneg (b ξ : ℝ) : 0 ≤ muW b ξ := by
  unfold muW
  positivity

theorem measurable_muW (b : ℝ) : Measurable (muW b) := by
  unfold muW
  fun_prop

/-! ## The fixed-`ξ` slice integrabilities -/

/-- The slice integrabilities of the five slots appearing in the shifted estimate, for
`NiceFlat` data whose `θ`-slot is integrable against `wE`. -/
theorem slotSliceFacts {u : ℝ → ℝ → ℝ} (α : ℝ) (hα1 : α ≤ 1) (hg : NiceFlat u)
    (hQ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (pth (pth u) p.1 p.2) ^ 2 * wE p.2) (Set.univ ×ˢ Iθ)) :
    (∀ ξ : ℝ, MeasureTheory.IntegrableOn (fun θ : ℝ => ‖slice u ξ θ‖ ^ 2 * wE θ) Iθ) ∧
    (∀ ξ : ℝ, MeasureTheory.IntegrableOn (fun θ : ℝ => ‖slice (pth u) ξ θ‖ ^ 2 * wE θ) Iθ) ∧
    (∀ ξ : ℝ, MeasureTheory.IntegrableOn (fun θ : ℝ => ‖slice (pth u) ξ θ‖ ^ 2 * wA α θ)
      Iθ) ∧
    (∀ ξ : ℝ, MeasureTheory.IntegrableOn
      (fun θ : ℝ => ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ) Iθ) := by
  obtain ⟨M, hM0, hM⟩ := niceFlat_supp hg
  have hcd_u : ContDiffOn ℝ 2 (Function.uncurry u) flStrip := hg.1
  have hcd_pth : ContDiffOn ℝ 1 (Function.uncurry (pth u)) flStrip :=
    pth_contDiffOn_succ flStrip_isOpen hcd_u
  have hcd_pthpth : ContDiffOn ℝ 0 (Function.uncurry (pth (pth u))) flStrip :=
    pth_contDiffOn_succ flStrip_isOpen hcd_pth
  have hsupp_pth : ∀ t θ : ℝ, M < |t| → pth u t θ = 0 := supp_pth hM
  have hsupp_pthpth : ∀ t θ : ℝ, M < |t| → pth (pth u) t θ = 0 := supp_pthpth hM
  have hwEnn : ∀ θ ∈ Iθ, 0 ≤ wE θ := fun θ hθ => wE_nonneg hθ
  have hwAnn : ∀ θ ∈ Iθ, 0 ≤ wA α θ := fun θ hθ => wA_nonneg hθ
  have hwAle : ∀ θ ∈ Iθ, wA α θ ≤ wE θ := fun θ hθ => wA_le_wE hα1 hθ
  have hslice_u : ∀ ξ : ℝ,
      ContinuousOn (fun θ : ℝ => slice u ξ θ) (Set.Ioo 0 (Real.pi / 2)) :=
    fun ξ => (sliceContDiffOn (n := 2) (by norm_num) hcd_u ⟨M, hM0, hM⟩ ξ).continuousOn
  have hslice_pth : ∀ ξ : ℝ,
      ContinuousOn (fun θ : ℝ => slice (pth u) ξ θ) (Set.Ioo 0 (Real.pi / 2)) :=
    fun ξ => (sliceContDiffOn (n := 1) (by norm_num) hcd_pth
      ⟨M, hM0, hsupp_pth⟩ ξ).continuousOn
  have hslice_q : ∀ ξ : ℝ,
      ContinuousOn (fun θ : ℝ => slice (pth (pth u)) ξ θ) (Set.Ioo 0 (Real.pi / 2)) :=
    fun ξ => (sliceContDiffOn (n := 0) (by norm_num) hcd_pthpth
      ⟨M, hM0, hsupp_pthpth⟩ ξ).continuousOn
  have hdth := dthBound u hg hQ
  have hA1 : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (pth u p.1 p.2) ^ 2 * wE p.2) (Set.univ ×ˢ Iθ) := hdth.1
  have hA0 : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (u p.1 p.2) ^ 2 * wE p.2) (Set.univ ×ˢ Iθ) := hdth.2
  have he0 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (∫ t : ℝ, (u t θ) ^ 2) * wE θ) Iθ :=
    integrableOn_energy_mul measurable_wE hA0
  have he1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (∫ t : ℝ, (pth u t θ) ^ 2) * wE θ) Iθ :=
    integrableOn_energy_mul measurable_wE hA1
  have heq : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (∫ t : ℝ, (pth (pth u) t θ) ^ 2) * wE θ) Iθ :=
    integrableOn_energy_mul measurable_wE hQ
  have hJg : ∀ ξ : ℝ,
      MeasureTheory.IntegrableOn (fun θ : ℝ => ‖slice u ξ θ‖ ^ 2 * wE θ) Iθ :=
    fun ξ => integrableOn_slice_sq_mul hM0 hcd_u.continuousOn hM hwEnn measurable_wE
      (hslice_u ξ) he0
  have hJpth : ∀ ξ : ℝ,
      MeasureTheory.IntegrableOn (fun θ : ℝ => ‖slice (pth u) ξ θ‖ ^ 2 * wE θ) Iθ :=
    fun ξ => integrableOn_slice_sq_mul hM0 hcd_pth.continuousOn hsupp_pth hwEnn measurable_wE
      (hslice_pth ξ) he1
  have hJq : ∀ ξ : ℝ,
      MeasureTheory.IntegrableOn (fun θ : ℝ => ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ) Iθ :=
    fun ξ => integrableOn_slice_sq_mul hM0 hcd_pthpth.continuousOn hsupp_pthpth hwEnn
      measurable_wE (hslice_q ξ) heq
  have hJpthA : ∀ ξ : ℝ,
      MeasureTheory.IntegrableOn (fun θ : ℝ => ‖slice (pth u) ξ θ‖ ^ 2 * wA α θ) Iθ :=
    fun ξ => integrableOn_slice_sq_mul_le hwAnn hwEnn hwAle (hslice_pth ξ) (measurable_wA α)
      (hJpth ξ)
  exact ⟨hJg, hJpth, hJpthA, hJq⟩

/-! ## The four Plancherel identifications -/

/-- Identification of the shifted first heavy slot. -/
theorem hidShiftOne {u : ℝ → ℝ → ℝ} {b : ℝ} (hg : NiceFlat u)
    (hJ : ∀ ξ : ℝ, MeasureTheory.IntegrableOn
      (fun θ : ℝ => ‖slice u ξ θ‖ ^ 2 * wE θ) Iθ)
    (hplanch : ∀ᵐ θ ∂((volume : Measure ℝ).restrict Iθ),
      MeasureTheory.Integrable (fun ξ : ℝ => muW b ξ * ‖slice u ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, muW b ξ * ‖slice u ξ θ‖ ^ 2)
        = ∫ t : ℝ, (pz u t θ - b * u t θ) ^ 2) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal (muW b ξ
        * ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ))
      = ∫⁻ p in Set.univ ×ˢ Iθ, ENNReal.ofReal
          ((pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * wE p.2) := by
  obtain ⟨M, hM0, hM⟩ := niceFlat_supp hg
  have hcd_u : ContDiffOn ℝ 2 (Function.uncurry u) flStrip := hg.1
  have hsupp_sp : ∀ t θ : ℝ, M < |t| → pz u t θ - b * u t θ = 0 :=
    fun t θ ht => by rw [supp_pz hM t θ ht, hM t θ ht]; ring
  have hcont_sp : ContinuousOn
      (Function.uncurry (fun t θ : ℝ => pz u t θ - b * u t θ)) flStrip :=
    ((pz_contDiffOn_succ flStrip_isOpen hcd_u).continuousOn).sub
      (hcd_u.continuousOn.const_mul b)
  have hsl_u : ContinuousOn (fun p : ℝ × ℝ => slice u p.1 p.2) flStrip :=
    continuousOn_slice_joint hcd_u.continuousOn ⟨M, hM0, hM⟩
  have hφ : ∀ᵐ θ ∂((volume : Measure ℝ).restrict Iθ),
      MeasureTheory.Integrable (fun t : ℝ => (pz u t θ - b * u t θ) ^ 2) :=
    ae_mem_Ioo_Iθ.mono (fun θ hθ => integrable_sq_slice hM0 hcont_sp hsupp_sp hθ)
  exact lintegral_slice_plancherel u (fun t θ : ℝ => pz u t θ - b * u t θ) (muW b) wE
    (muW_nonneg b) (fun θ hθ => wE_nonneg hθ) hJ hφ hplanch
    (aemeasurable_ofReal_weight_mul hsl_u (measurable_muW b) measurable_wE)
    (aemeasurable_ofReal_sq_mul_snd hcont_sp measurable_wE)

/-- Identification of the shifted second heavy slot. -/
theorem hidShiftTwo {u : ℝ → ℝ → ℝ} {b : ℝ} (hg : NiceFlat u)
    (hJ : ∀ ξ : ℝ, MeasureTheory.IntegrableOn
      (fun θ : ℝ => ‖slice u ξ θ‖ ^ 2 * wE θ) Iθ)
    (hplanch : ∀ᵐ θ ∂((volume : Measure ℝ).restrict Iθ),
      MeasureTheory.Integrable (fun ξ : ℝ => (muW b ξ) ^ 2 * ‖slice u ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, (muW b ξ) ^ 2 * ‖slice u ξ θ‖ ^ 2)
        = ∫ t : ℝ, (pz (pz u) t θ - 2 * b * pz u t θ + b ^ 2 * u t θ) ^ 2) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal ((muW b ξ) ^ 2
        * ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ))
      = ∫⁻ p in Set.univ ×ˢ Iθ, ENNReal.ofReal
          ((pz (pz u) p.1 p.2 - 2 * b * pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2
            * wE p.2) := by
  obtain ⟨M, hM0, hM⟩ := niceFlat_supp hg
  have hcd_u : ContDiffOn ℝ 2 (Function.uncurry u) flStrip := hg.1
  have hcd_pz : ContDiffOn ℝ 1 (Function.uncurry (pz u)) flStrip :=
    pz_contDiffOn_succ flStrip_isOpen hcd_u
  have hsupp_spp : ∀ t θ : ℝ, M < |t| →
      pz (pz u) t θ - 2 * b * pz u t θ + b ^ 2 * u t θ = 0 := by
    intro t θ ht
    rw [supp_pzpz hM t θ ht, supp_pz hM t θ ht, hM t θ ht]
    ring
  have hcont_spp : ContinuousOn
      (Function.uncurry (fun t θ : ℝ =>
        pz (pz u) t θ - 2 * b * pz u t θ + b ^ 2 * u t θ)) flStrip :=
    (((pz_contDiffOn_succ flStrip_isOpen hcd_pz).continuousOn).sub
      (hcd_pz.continuousOn.const_mul (2 * b))).add
      (hcd_u.continuousOn.const_mul (b ^ 2))
  have hsl_u : ContinuousOn (fun p : ℝ × ℝ => slice u p.1 p.2) flStrip :=
    continuousOn_slice_joint hcd_u.continuousOn ⟨M, hM0, hM⟩
  have hφ : ∀ᵐ θ ∂((volume : Measure ℝ).restrict Iθ),
      MeasureTheory.Integrable (fun t : ℝ =>
        (pz (pz u) t θ - 2 * b * pz u t θ + b ^ 2 * u t θ) ^ 2) :=
    ae_mem_Ioo_Iθ.mono (fun θ hθ => integrable_sq_slice hM0 hcont_spp hsupp_spp hθ)
  exact lintegral_slice_plancherel u
    (fun t θ : ℝ => pz (pz u) t θ - 2 * b * pz u t θ + b ^ 2 * u t θ)
    (fun ξ : ℝ => (muW b ξ) ^ 2) wE
    (fun ξ => by positivity) (fun θ hθ => wE_nonneg hθ) hJ hφ hplanch
    (aemeasurable_ofReal_weight_mul hsl_u ((measurable_muW b).pow_const 2) measurable_wE)
    (aemeasurable_ofReal_sq_mul_snd hcont_spp measurable_wE)

/-- Identification of the (unshifted) third heavy slot. -/
theorem hidShiftThree {u : ℝ → ℝ → ℝ} (hg : NiceFlat u)
    (hJ : ∀ ξ : ℝ, MeasureTheory.IntegrableOn
      (fun θ : ℝ => ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ) Iθ) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal ((1 : ℝ)
        * ∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ))
      = ∫⁻ p in Set.univ ×ˢ Iθ, ENNReal.ofReal
          ((pth (pth u) p.1 p.2) ^ 2 * wE p.2) := by
  obtain ⟨M, hM0, hM⟩ := niceFlat_supp hg
  have hcd_u : ContDiffOn ℝ 2 (Function.uncurry u) flStrip := hg.1
  have hcd_pth : ContDiffOn ℝ 1 (Function.uncurry (pth u)) flStrip :=
    pth_contDiffOn_succ flStrip_isOpen hcd_u
  have hcd_pthpth : ContDiffOn ℝ 0 (Function.uncurry (pth (pth u))) flStrip :=
    pth_contDiffOn_succ flStrip_isOpen hcd_pth
  have hsupp_pthpth : ∀ t θ : ℝ, M < |t| → pth (pth u) t θ = 0 := supp_pthpth hM
  have hcont_pthpth : ContinuousOn (Function.uncurry (pth (pth u))) flStrip :=
    hcd_pthpth.continuousOn
  have hsl_q : ContinuousOn (fun p : ℝ × ℝ => slice (pth (pth u)) p.1 p.2) flStrip :=
    continuousOn_slice_joint hcont_pthpth ⟨M, hM0, hsupp_pthpth⟩
  have hφ : ∀ᵐ θ ∂((volume : Measure ℝ).restrict Iθ),
      MeasureTheory.Integrable (fun t : ℝ => (pth (pth u) t θ) ^ 2) :=
    ae_mem_Ioo_Iθ.mono (fun θ hθ => integrable_sq_slice hM0 hcont_pthpth hsupp_pthpth hθ)
  have hplanch : ∀ᵐ θ ∂((volume : Measure ℝ).restrict Iθ),
      MeasureTheory.Integrable (fun ξ : ℝ => (1 : ℝ) * ‖slice (pth (pth u)) ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, (1 : ℝ) * ‖slice (pth (pth u)) ξ θ‖ ^ 2)
        = ∫ t : ℝ, (pth (pth u) t θ) ^ 2 := by
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    obtain ⟨h1, h2⟩ := plancherel_pthpth hg hθ
    refine ⟨h1.congr (Eventually.of_forall fun ξ => by simp), ?_⟩
    rw [show (∫ ξ : ℝ, (1 : ℝ) * ‖slice (pth (pth u)) ξ θ‖ ^ 2)
        = ∫ ξ : ℝ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 from
      integral_congr_ae (Eventually.of_forall fun ξ => by simp)]
    exact h2
  exact lintegral_slice_plancherel (pth (pth u)) (pth (pth u)) (fun _ : ℝ => (1 : ℝ)) wE
    (fun _ => zero_le_one) (fun θ hθ => wE_nonneg hθ) hJ hφ hplanch
    (aemeasurable_ofReal_weight_mul hsl_q measurable_const measurable_wE)
    (aemeasurable_ofReal_sq_mul_snd hcont_pthpth measurable_wE)

/-- Identification of the left-hand slot of the shifted estimate. -/
theorem hidShiftLhs {u : ℝ → ℝ → ℝ} {b : ℝ} {α : ℝ}
    (hg : NiceFlat u)
    (hJ : ∀ ξ : ℝ, MeasureTheory.IntegrableOn
      (fun θ : ℝ => ‖slice (pth u) ξ θ‖ ^ 2 * wA α θ) Iθ)
    (hplanch : ∀ᵐ θ ∂((volume : Measure ℝ).restrict Iθ),
      MeasureTheory.Integrable (fun ξ : ℝ => muW b ξ * ‖slice (pth u) ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, muW b ξ * ‖slice (pth u) ξ θ‖ ^ 2)
        = ∫ t : ℝ, (pth (pz u) t θ - b * pth u t θ) ^ 2) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal (muW b ξ
        * ∫ θ in Iθ, ‖slice (pth u) ξ θ‖ ^ 2 * wA α θ))
      = ∫⁻ p in Set.univ ×ˢ Iθ, ENNReal.ofReal
          ((pth (pz u) p.1 p.2 - b * pth u p.1 p.2) ^ 2 * wA α p.2) := by
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
    (muW b) (wA α) (muW_nonneg b) (fun θ hθ => wA_nonneg hθ) hJ hφ hplanch
    (aemeasurable_ofReal_weight_mul hsl_pth (measurable_muW b) (measurable_wA α))
    (aemeasurable_ofReal_sq_mul_snd hcont_lhsψ (measurable_wA α))

end

end Work.FTS.EllSol.SpecAux
