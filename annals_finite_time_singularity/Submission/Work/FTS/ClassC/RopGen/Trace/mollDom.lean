import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllipticEst.ThetaU.K1Aux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs
import Submission.Work.FTS.EllSol.EllPkgAux.mollAdm
import Submission.Work.FTS.EllSol.EllPkgAux.logJensen
import Submission.Work.FTS.EllSol.EllPkgAux.kernelJensen
import Submission.Work.FTS.EllSol.EllPkgAux.wExpCmp
import Submission.Work.FTS.EllSol.EllPkgAux.MollSliceDom
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.mollMasterUnif
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_dDom
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_ddDom
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_ttDom
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_mixIntS_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.ClassC.RopGen.Trace.mollDom` — the dominations of the four functionals of `Φ`

The statement below is the "domination" ingredient of the trace-class single-function
interpolation estimate: for every datum `G` in the trace class (`TraceClass G`) with integrable
weighted functionals (`FourInts G`) and every pair of mollification parameters `δ, ε ∈ (0,1/2]`,
the doubly-mollified datum `Φ := zmoll G δ ε` has

* `∫ ddIntS Φ ≤ K ∫ ddIntS G`, `∫ ttIntS Φ ≤ K ∫ ttIntS G`, `∫ dIntS Φ ≤ K ∫ dIntS G`
  (the `D_z²`-, `∂_θ²`- and `D_z`-slots) with a constant `K` **uniform** in `G`, `δ`, `ε`;
* `mixIntS Φ`, `ddIntS Φ`, `ttIntS Φ`, `dIntS Φ` integrable on `Iz`.

## Proof

The obstruction to a direct proof is that `zmoll` probes `G` at a whole window of radii
`[z e^{-δ}, z e^{δ}]` and of angles, so the pointwise commutation of `D_z^j` with the angular
mollification fails on a null set; the transfer identity for the *log-radial* mollification is
however exact and is what the estimate is built on.  The argument is assembled here from the
following independently proved components of the `EllPkgAux/MollDom` directory:

* `MollDom.mollMasterUnif` — the two-kernel domination estimate with a constant uniform in
  `F, X, δ, ε`: if `|F z θ| ≤ ∫_t sKer δ (log z - t) (∫_s KJ ε θ s |X (e^t) s| ds) dt` for a.e.
  `z > 0` and all `θ ∈ Iθ`, and the slices of `F` and of `X` are `σ_η`-honest, the `X`-functional
  is `w²`-integrable and `F`, `(t,s) ↦ X (e^t) s` are jointly measurable, then
  `∫_z w² ∫_θ F² σ_η ≤ K ∫_z w² ∫_θ X² σ_η` and the left-hand side is integrable.  (Its proof is
  Jensen/Cauchy–Schwarz for the product kernel `sKer δ (log z - ·) ⊗ KJ ε`, Tonelli, the two
  Schur/weight comparisons (`KJ_schur_ae` from `K5cAux.thWeightCmp`, and `wExpCmp`) and the
  change of variables `z = e^t`.)
* `MollDom.zmoll_ddDom`, `MollDom.zmoll_dDom`, `MollDom.zmoll_ttDom` — the pointwise (a.e. in
  `z`, all `θ ∈ Iθ`) dominations of `D_z²Φ`, `D_zΦ` and `∂_θ²Φ` by the double convolution of the
  corresponding derivative of `G` with the two kernels; these are the *transfer identities* for
  the two mollifications together with the three-piece angular fold `|Kern| ≤ KJ`.
* `MollDom.zmoll_mixIntS_integrable` — the integrability of the mixed functional `mixIntS Φ`.
* `EllPkgAux.mollAdm` — `Φ` is `C^∞` on the half-strip `(0,∞) × (-1, π/2+1)` and vanishes on both
  angular boundary lines; this supplies the smoothness, measurability and `σ_η`-honesty of the
  `Φ`-side of `mollMasterUnif`.

The helpers below extract the `σ_η`-honesty and the joint measurability of the four slot
functions from `mollAdm` (for `Φ`), from `SliceHonestOpen G` and `SmoothOpen G` (for `G`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.RopGen.Trace

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "σθ" => Work.FTS.EllipticEst.thEta
local notation "OStrip" => Work.FTS.EllipticEst.ThetaU.OStrip

/-! ## helpers -/

/-- `1 ≤ w z²` for `z > 0`. -/
lemma one_le_w_sq {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 := by
  have hz2 : (0 : ℝ) < z ^ 2 := by positivity
  have h1 : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div hz2]
    nlinarith
  calc (1 : ℝ) = 1 ^ 2 := by norm_num
    _ ≤ (Work.Spaces.w z) ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2

/-- `SliceHonestOpen` gives the `σ_η`-honesty of the three right-hand-side slices, by dividing
out the (strictly positive) radial weight. -/
lemma sliceHon_of_sliceHonestOpen {G : ℝ → ℝ → ℝ}
    (h : Work.EllipticEst.Core.i0Aux.SliceHonestOpen G) :
    (∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ =>
        (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * σθ θ) Iθ) ∧
    (∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ =>
        (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * σθ θ) Iθ) ∧
    (∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ =>
        (Work.Spaces.Dz G z θ) ^ 2 * σθ θ) Iθ) := by
  obtain ⟨h1, h2, h3⟩ := h
  have key : ∀ (slot : ℝ → ℝ → ℝ) (z : ℝ), 0 < z →
      IntegrableOn (fun θ : ℝ => (slot z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * σθ θ) Iθ →
      IntegrableOn (fun θ : ℝ => (slot z θ) ^ 2 * σθ θ) Iθ := by
    intro slot z hz hint
    have hw2 : (0 : ℝ) < (Work.Spaces.w z) ^ 2 := by
      have := one_le_w_sq hz; linarith
    have hw2ne : (Work.Spaces.w z) ^ 2 ≠ 0 := ne_of_gt hw2
    have haesm : AEStronglyMeasurable (fun θ : ℝ => (slot z θ) ^ 2 * σθ θ)
        (volume.restrict Iθ) := by
      have heq : (fun θ : ℝ => (slot z θ) ^ 2 * σθ θ)
          = fun θ : ℝ => ((slot z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * σθ θ)
              * ((Work.Spaces.w z) ^ 2)⁻¹ := by
        funext θ
        rw [show ((slot z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * σθ θ) * ((Work.Spaces.w z) ^ 2)⁻¹
            = (slot z θ) ^ 2 * σθ θ
              * ((Work.Spaces.w z) ^ 2 * ((Work.Spaces.w z) ^ 2)⁻¹) by ring,
          mul_inv_cancel₀ hw2ne, mul_one]
      rw [heq]
      exact hint.aestronglyMeasurable.mul_const _
    refine Integrable.mono' hint haesm ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hσ : 0 ≤ σθ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
    have hsq : 0 ≤ (slot z θ) ^ 2 := sq_nonneg _
    rw [Real.norm_of_nonneg (mul_nonneg hsq hσ)]
    have hw1 : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_w_sq hz
    have hstep : σθ θ ≤ σθ θ * (Work.Spaces.w z) ^ 2 := by
      calc σθ θ = σθ θ * 1 := (mul_one _).symm
        _ ≤ σθ θ * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_left hw1 hσ
    calc (slot z θ) ^ 2 * σθ θ
        ≤ (slot z θ) ^ 2 * (σθ θ * (Work.Spaces.w z) ^ 2) :=
          mul_le_mul_of_nonneg_left hstep hsq
      _ = (slot z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * σθ θ := by ring
  exact ⟨fun z hz => key _ z hz (h1 z hz),
         fun z hz => key _ z hz (h2 z hz),
         fun z hz => key _ z hz (h3 z hz)⟩

/-- A function continuous on the half strip has `σ_η`-honest angular slices. -/
lemma sliceHon_of_cont_on_strip {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) OStrip) :
    ∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ => (F z θ) ^ 2 * σθ θ) Iθ := by
  intro z hz
  have hmem : ∀ θ : ℝ, θ ∈ Iθ → (z, θ) ∈ OStrip := by
    intro θ hθ
    refine ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
  have hslice : ContinuousOn (fun θ : ℝ => F z θ) Iθ :=
    hF.comp (continuousOn_const.prodMk continuousOn_id) (fun θ hθ => hmem θ hθ)
  have hsq : ContinuousOn (fun θ : ℝ => (F z θ) ^ 2) Iθ := hslice.pow 2
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hsq
  have hσ : Integrable (fun θ : ℝ => σθ θ) (volume.restrict Iθ) :=
    Work.FTS.EllipticEst.integrableOn_thEta.1
  have hg : Integrable (fun θ : ℝ => C * σθ θ) (volume.restrict Iθ) := hσ.const_mul C
  have haesm : AEStronglyMeasurable (fun θ : ℝ => (F z θ) ^ 2 * σθ θ)
      (volume.restrict Iθ) :=
    (hsq.aestronglyMeasurable measurableSet_Icc).mul hσ.aestronglyMeasurable
  refine Integrable.mono' hg haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  have hσnn : 0 ≤ σθ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
  have hb := hC θ hθ
  have hb' : F z θ ^ 2 ≤ C := by
    rwa [Real.norm_of_nonneg (sq_nonneg _)] at hb
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hσnn)]
  nlinarith [hb', hσnn]

lemma Ioi_prod_subset_strip : Set.Ioi (0:ℝ) ×ˢ Iθ ⊆ OStrip := by
  intro p hp
  obtain ⟨hz, hθ⟩ := hp
  exact ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩

/-- A function continuous on the half strip is a.e. measurable for the product of the
restrictions to `(0,∞)` and `Iθ`. -/
lemma aemeasurable_strip {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) OStrip) :
    AEMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
      ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod
        (MeasureTheory.volume.restrict Iθ)) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Set.Ioi (0:ℝ) ×ˢ Iθ) := hF.mono Ioi_prod_subset_strip
  have h := hcont.aemeasurable (measurableSet_Ioi.prod measurableSet_Icc)
    (μ := MeasureTheory.volume.prod MeasureTheory.volume)
  rwa [← MeasureTheory.Measure.prod_restrict] at h

lemma volume_insert_pair : MeasureTheory.volume ({(0:ℝ), Real.pi/2} : Set ℝ) = 0 := by
  rw [show ({(0:ℝ), Real.pi/2} : Set ℝ) = {0} ∪ {Real.pi/2} by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
  exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton (0:ℝ))
    (MeasureTheory.measure_singleton (Real.pi/2))

lemma null_univ_prod_endpoints :
    (MeasureTheory.volume.prod MeasureTheory.volume)
      ((Set.univ : Set ℝ) ×ˢ ({(0:ℝ), Real.pi/2} : Set ℝ)) = 0 := by
  rw [MeasureTheory.Measure.prod_prod, volume_insert_pair, mul_zero]

lemma Ioo_ae_eq_Icc_prod :
    (Set.univ : Set ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi/2)
      =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume] (Set.univ : Set ℝ) ×ˢ Iθ := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · have hempty : ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi/2)) \
        ((Set.univ : Set ℝ) ×ˢ Iθ) = ∅ := by
      rw [Set.sdiff_eq_empty]
      intro p hp
      obtain ⟨-, hp2⟩ := hp
      have h2 : 0 < p.2 ∧ p.2 < Real.pi/2 := hp2
      exact ⟨trivial, ⟨le_of_lt h2.1, le_of_lt h2.2⟩⟩
    rw [hempty, MeasureTheory.measure_empty]
  · have hsub : ((Set.univ : Set ℝ) ×ˢ Iθ) \
        ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi/2)) ⊆
        (Set.univ : Set ℝ) ×ˢ ({(0:ℝ), Real.pi/2} : Set ℝ) := by
      intro p hp
      obtain ⟨hpB, hpA⟩ := hp
      obtain ⟨-, hB⟩ := hpB
      have hB' : 0 ≤ p.2 ∧ p.2 ≤ Real.pi/2 := hB
      have hA' : ¬ (0 < p.2 ∧ p.2 < Real.pi/2) := by
        intro hcon
        exact hpA ⟨trivial, hcon⟩
      refine ⟨trivial, ?_⟩
      rcases lt_or_ge (0:ℝ) p.2 with h | h
      · rcases lt_or_ge p.2 (Real.pi/2) with h' | h'
        · exact absurd ⟨h, h'⟩ hA'
        · exact Or.inr (le_antisymm hB'.2 h')
      · exact Or.inl (le_antisymm h hB'.1)
    exact MeasureTheory.measure_mono_null hsub null_univ_prod_endpoints

/-- A function continuous on the open quadrant is a.e. measurable for the product of `volume`
with the restriction to `Iθ`, after the substitution `z = e^t`. -/
lemma aemeasurable_exp {X : ℝ → ℝ → ℝ}
    (hX : ContinuousOn (Function.uncurry X) Work.FTS.EllipticEst.Q0) :
    AEMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Iθ)) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (Set.univ ×ˢ Set.Ioo (0:ℝ) (Real.pi/2)) := by
    have hexp : Continuous (fun p : ℝ × ℝ => Real.exp p.1) :=
      Real.continuous_exp.comp continuous_fst
    have hpair : Continuous (fun p : ℝ × ℝ => (Real.exp p.1, p.2)) :=
      hexp.prodMk continuous_snd
    exact hX.comp hpair.continuousOn (fun p hp => ⟨Real.exp_pos _, hp.2⟩)
  have h := hcont.aemeasurable (MeasurableSet.univ.prod measurableSet_Ioo)
    (μ := MeasureTheory.volume.prod MeasureTheory.volume)
  rw [MeasureTheory.Measure.restrict_congr_set Ioo_ae_eq_Icc_prod] at h
  have h2 : (MeasureTheory.volume.prod MeasureTheory.volume).restrict ((Set.univ : Set ℝ) ×ˢ Iθ)
      = MeasureTheory.volume.prod (MeasureTheory.volume.restrict Iθ) := by
    rw [← MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_univ]
  rwa [h2] at h

/-- Smoothness of the slot functions of the mollified datum. -/
lemma continuousOn_DzIter_zmoll (G : ℝ → ℝ → ℝ)
    (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) (hF : Work.FTS.EllSol.EllPkgAux.FourInts G)
    (δ ε : ℝ) (hP : Work.FTS.EllSol.EllPkgAux.Params δ ε) :
    ContinuousOn (Function.uncurry (Work.Spaces.Dz (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε))) OStrip ∧
    ContinuousOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dz (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)))) OStrip ∧
    ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)))) OStrip := by
  obtain ⟨hstrip, -, -⟩ := Work.FTS.EllSol.EllPkgAux.mollAdm G hT hF δ ε hP
  refine ⟨?_, ?_, ?_⟩
  · exact ((Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin
      (G := Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)
      (n := 1) (hstrip 2)) : ContDiffOn ℝ 1 _ OStrip).continuousOn
  · exact ((Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin
      (G := Work.Spaces.Dz (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)) (n := 1)
      (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin
        (G := Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) (n := 2) (hstrip 3)))
      : ContDiffOn ℝ 1 _ OStrip).continuousOn
  · exact ((Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin
      (G := Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)) (n := 1)
      (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin
        (G := Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) (n := 2) (hstrip 3)))
      : ContDiffOn ℝ 1 _ OStrip).continuousOn

/-- Continuity on the open quadrant of the slot functions of the datum. -/
lemma continuousOn_slot_datum {G : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen G) :
    ContinuousOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dz G))) Work.FTS.EllipticEst.Q0 ∧
    ContinuousOn (Function.uncurry (Work.Spaces.Dz G)) Work.FTS.EllipticEst.Q0 ∧
    ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth G))) Work.FTS.EllipticEst.Q0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact ((Work.FTS.EllipticEst.SmoothOpen.DzIter hS 2).forall 1).continuousOn
  · exact ((Work.FTS.EllipticEst.SmoothOpen.DzIter hS 1).forall 1).continuousOn
  · exact ((Work.FTS.EllipticEst.SmoothOpen.pth (Work.FTS.EllipticEst.SmoothOpen.pth hS)).forall 1).continuousOn

/-! ## the target -/

theorem mollDom : ∃ K : ℝ, 0 < K ∧ ∀ (G : ℝ → ℝ → ℝ),
    Work.FTS.EllSol.EllPkgAux.TraceClass G → Work.FTS.EllSol.EllPkgAux.FourInts G →
    ∀ (δ ε : ℝ), Work.FTS.EllSol.EllPkgAux.Params δ ε →
      (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.ddIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z
          ≤ K * ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ddIntS G z) ∧
      (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.ttIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z
          ≤ K * ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ttIntS G z) ∧
      (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.dIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z
          ≤ K * ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.dIntS G z) ∧
      MeasureTheory.IntegrableOn
        (fun z : ℝ => Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)
        Work.Spaces.Iz ∧
      MeasureTheory.IntegrableOn
        (fun z : ℝ => Work.EllipticEst.Core.ddIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)
        Work.Spaces.Iz ∧
      MeasureTheory.IntegrableOn
        (fun z : ℝ => Work.EllipticEst.Core.ttIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)
        Work.Spaces.Iz ∧
      MeasureTheory.IntegrableOn
        (fun z : ℝ => Work.EllipticEst.Core.dIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)
        Work.Spaces.Iz := by
  obtain ⟨K, hK, hMaster⟩ := Work.FTS.EllSol.EllPkgAux.MollDom.mollMasterUnif
  refine ⟨K, hK, ?_⟩
  intro G hT hF δ ε hP
  obtain ⟨hε0, hε1, hδ0, hδ1⟩ := hP
  have hT0 : Work.FTS.EllSol.EllPkgAux.TraceClass G := hT
  have hF0 : Work.FTS.EllSol.EllPkgAux.FourInts G := hF
  have hP0 : Work.FTS.EllSol.EllPkgAux.Params δ ε := ⟨hε0, hε1, hδ0, hδ1⟩
  obtain ⟨hS, -, -, -, -, -, -, hsh⟩ := hT
  obtain ⟨hmi, hddG, httG, hdG⟩ := hF
  obtain ⟨hsl1, hsl2, hsl3⟩ := sliceHon_of_sliceHonestOpen hsh
  obtain ⟨hc1, hc2, hc3⟩ := continuousOn_DzIter_zmoll G hT0 hF0 δ ε hP0
  obtain ⟨hd1, hd2, hd3⟩ := continuousOn_slot_datum hS
  have hdd := hMaster (Work.Spaces.Dz (Work.Spaces.Dz (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)))
      (Work.Spaces.Dz (Work.Spaces.Dz G)) δ ε hδ0 hδ1 hε0 hε1
      (Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_ddDom G hT0 hF0 δ ε hP0)
      (sliceHon_of_cont_on_strip hc2) hsl2
      (by simpa only [Work.EllipticEst.Core.ddIntS] using hddG)
      (aemeasurable_strip hc2) (aemeasurable_exp hd1)
  have htt := hMaster (Work.Spaces.pth (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)))
      (Work.Spaces.pth (Work.Spaces.pth G)) δ ε hδ0 hδ1 hε0 hε1
      (Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_ttDom G hT0 hF0 δ ε hP0)
      (sliceHon_of_cont_on_strip hc3) hsl1
      (by simpa only [Work.EllipticEst.Core.ttIntS] using httG)
      (aemeasurable_strip hc3) (aemeasurable_exp hd3)
  have hd := hMaster (Work.Spaces.Dz (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε))
      (Work.Spaces.Dz G) δ ε hδ0 hδ1 hε0 hε1
      (Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_dDom G hT0 hF0 δ ε hP0)
      (sliceHon_of_cont_on_strip hc1) hsl3
      (by simpa only [Work.EllipticEst.Core.dIntS] using hdG)
      (aemeasurable_strip hc1) (aemeasurable_exp hd2)
  exact ⟨by simpa only [Work.EllipticEst.Core.ddIntS] using hdd.1,
         by simpa only [Work.EllipticEst.Core.ttIntS] using htt.1,
         by simpa only [Work.EllipticEst.Core.dIntS] using hd.1,
         Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_mixIntS_integrable G hT0 hF0 δ ε hP0,
         by simpa only [Work.EllipticEst.Core.ddIntS] using hdd.2,
         by simpa only [Work.EllipticEst.Core.ttIntS] using htt.2,
         by simpa only [Work.EllipticEst.Core.dIntS] using hd.2⟩

end Work.FTS.ClassC.RopGen.Trace
