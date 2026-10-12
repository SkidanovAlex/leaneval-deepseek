import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.tBdiagFormInd_cube_eq_sum_sectorPiece
import Submission.Work.BoseFixB1B.sbWord_descent_atSizes
import Submission.Work.BoseFixB1S.sbKinSliceSplitW
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.SliceSuperaddCube` — FS Step E at the **cube cutoff**

The grouping step (FS Step E, `final_v2.tex` ll. 3960–4045) for the **matched-window** word
`sbWordCube = sbKinCube + sbPot` of `Work.BoseFixB1B.matchedWindowDefs`:

    sbWordCube h μ u Φ
      ≥ ∫_{w ∈ abox N₂ ℓ} sbWordCube h μ u (fun y ↦ Φ (merge(y,w)))
        + ∫_{y ∈ abox N₁ ℓ} sbWordCube h μ u (fun w ↦ Φ (merge(y,w))),   ℓ = sideAt μ (a v),

together with the block-splittability (`Work.KinPSuperadd.SlotSplit`) of its kinetic half
`sbKinCube = bGapCoeff·n₊(B) + Q_Bχ_B[√−Δ−c]₊²χ_BQ_B` at the cube window `chiSmallB`.

## The route

* **the potential half** is *verbatim* the frozen one: `sbPot` is the same object
  (`Work.BoseFixB1.sbPot`), so `Work.BoseFixB1S.sbPot_slice_superadd_regime` and
  `Work.BoseFixB1S.sbPot_slice_integrable_regime` apply unchanged;
* **the kinetic half**: `sbKinCube` is `cubeWord` at FS's parameters
  (`Work.BoseFixB1B.sbKinCube_eq_cubeWord`, `rfl`-level), the count row is the proved
  `Work.BoseFixB1S.slotSplitCnPlusBoxInd` (window-free) and the spectral row is handled by the
  abstract engine `Work.BoseFixB1S.slotSplit_tBdiagForm`, whose only hypothesis is the `p ↔ box`
  swap `SlotSwapProp` — proved here from the already-proved uniform decay of the cube-windowed
  box-projected amplitude (`Work.BoseB1Cube.tBamp_chiSmallB_boxQInd_decay`) transported from
  `boxQInd` to `boxQ` along `Work.UBBInputs9.A.tBamp_boxQInd`.

Everything is stated first in the raw `(ℓ, d, M, c)` parameters and only then instantiated at
FS's parameters, so that no definitional unpacking is needed inside the proofs.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal ContDiff

namespace Work.BoseB1Cube

open Submission.BoseGases
open _root_.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 0. The cube window, off its box -/

/-- The cube window `chiSmallB M ℓ d u` vanishes off the sliding box `dlBox ℓ d u`. -/
theorem chiSmallB_eq_zero_off_dlBox {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u z : E3) (hz : z ∉ Submission.BoseGases.dlBox ℓ d u) :
    Submission.BoseGases.chiSmallB M ℓ d u z = 0 := by
  by_contra hne
  exact hz (Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hne)

/-! ## 1. Uniform decay of the cube-windowed box-projected amplitude at the corpus projection
`boxQ` (the `SlotSwapProp` spelling) -/

/-- **Uniform `(1+‖p‖)⁻³` decay of the cube-windowed `boxQ`-amplitude.**  The FS-faithful decay
`Work.BoseB1Cube.tBamp_chiSmallB_boxQInd_decay` is about FS's own projection `boxQInd`; since the
window is supported in the box the two projections have the same amplitude
(`Work.UBBInputs9.A.tBamp_boxQInd`), so the bound transfers to `boxQ`. -/
theorem tBamp_chiSmallB_boxQ_decay {N : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {M : ℕ} (hM : 4 ≤ M) (u : E3)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Submission.BoseGases.X N), x ∈ Submission.BoseGases.abox N ℓ →
      ∀ (i : Fin N) (p : E3),
      ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
        (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ≤ C / (1 + ‖p‖) ^ 3 := by
  obtain ⟨C, hC0, hCd⟩ :=
    Work.BoseB1Cube.tBamp_chiSmallB_boxQInd_decay (n := N) hℓ hd hM u hΦ
  refine ⟨C, hC0, fun x hx i p => ?_⟩
  rw [← Work.UBBInputs9.A.tBamp_boxQInd (volA := Work.SmallBoxSliding.boxMass ℓ d u)
    (A := Submission.BoseGases.dlBox ℓ d u)
    (χ := Submission.BoseGases.chiSmallB M ℓ d u)
    (chiSmallB_eq_zero_off_dlBox (by omega) hℓ hd u) Φ i p x]
  exact hCd x hx i p

/-! ## 2. The `p ↔ box` swap at the cube window

`SlotSwapProp ℓ B V χ F` is the hypothesis of the abstract block-split engine
`Work.BoseFixB1S.slotSplit_tBdiagForm`: joint integrability of
`(p,x) ↦ F‖p‖·‖tBamp χ p (Q_{B,i}Ψ) i x‖²` on `volume.prod (volume.restrict B)`, plus Fubini.
Both follow from the uniform decay of §1 and the integrability of the `fsKinCoeff`-weighted
decay profile `Work.SlotWord.integrable_fsKinCoeff_decay`. -/

/-- **The `p ↔ box` swap at the cube window.** -/
theorem cubeSpectral_slotSwap {ℓ d c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {M : ℕ} (hM : 4 ≤ M)
    (u : E3) :
    Work.BoseFixB1S.SlotSwapProp ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u)
      (Submission.BoseGases.fsKinCoeff c) := by
  intro N Ψ hΨ i
  have hA : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hχc : Continuous (Submission.BoseGases.chiSmallB M ℓ d u) :=
    (Work.BoseFixB1S.win.contDiff_three_chiSmallB hM hℓ hd u).continuous
  have hχE : ∀ z : E3, z ∉ Submission.BoseGases.dlBox ℓ d u →
      Submission.BoseGases.chiSmallB M ℓ d u z = 0 :=
    chiSmallB_eq_zero_off_dlBox (by omega) hℓ hd u
  haveI hfin : IsFiniteMeasure ((volume : Measure (X N)).restrict
      (Submission.BoseGases.abox N ℓ)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr
      (Submission.BoseGases.abox_lt_top N ℓ hℓ.le).ne
  obtain ⟨C, hC0, hCd⟩ :=
    Work.BoseB1Cube.tBamp_chiSmallB_boxQInd_decay (n := N) hℓ hd hM u hΨ
  have hpt : ∀ (p : E3) (x : X N),
      Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Ψ) i x
      = Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
        (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Ψ) i x :=
    fun p x => Work.UBBInputs9.A.tBamp_boxQInd hχE Ψ i p x
  have hFcont : Continuous (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖) := by
    rw [show (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖)
        = (fun r : ℝ => (max (r - c) 0) ^ 2) ∘ fun p : E3 => ‖p‖ from rfl]
    exact (((continuous_id.sub continuous_const).max continuous_const).pow 2).comp continuous_norm
  have hmeas_int : AEStronglyMeasurable (fun q : E3 × X N =>
      Submission.BoseGases.fsKinCoeff c ‖q.1‖ *
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) q.1
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Ψ) i q.2‖ ^ 2)
      ((volume : Measure E3).prod
        ((volume : Measure (X N)).restrict (Submission.BoseGases.abox N ℓ))) := by
    have h1 : AEStronglyMeasurable (fun q : E3 × X N =>
        Submission.BoseGases.fsKinCoeff c ‖q.1‖)
        ((volume : Measure E3).prod
          ((volume : Measure (X N)).restrict (Submission.BoseGases.abox N ℓ))) :=
      (hFcont.comp continuous_fst).aestronglyMeasurable
    have h2 : Measurable (fun q : E3 × X N =>
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) q.1
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Ψ) i q.2‖ ^ 2) :=
      Work.BoseFixB1.measurable_tBamp_boxQInd_pair hA hχc hΨ.continuous.measurable i
    exact h1.mul h2.aestronglyMeasurable
  have hdom : Integrable (fun q : E3 × X N =>
      Submission.BoseGases.fsKinCoeff c ‖q.1‖ * (C / (1 + ‖q.1‖) ^ 3) ^ 2)
      ((volume : Measure E3).prod
        ((volume : Measure (X N)).restrict (Submission.BoseGases.abox N ℓ))) :=
    (Work.SlotWord.integrable_fsKinCoeff_decay c C).comp_fst _
  have hjointInd : Integrable (fun q : E3 × X N =>
      Submission.BoseGases.fsKinCoeff c ‖q.1‖ *
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) q.1
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Ψ) i q.2‖ ^ 2)
      ((volume : Measure E3).prod
        ((volume : Measure (X N)).restrict (Submission.BoseGases.abox N ℓ))) := by
    refine hdom.mono' hmeas_int ?_
    have hae : ∀ᵐ q ∂((volume : Measure E3).prod
        ((volume : Measure (X N)).restrict (Submission.BoseGases.abox N ℓ))),
        q.2 ∈ Submission.BoseGases.abox N ℓ := by
      rw [MeasureTheory.ae_iff]
      rw [show {q : E3 × X N | ¬ q.2 ∈ Submission.BoseGases.abox N ℓ}
          = Set.univ ×ˢ (Submission.BoseGases.abox N ℓ)ᶜ by ext q; simp]
      rw [Measure.prod_prod]
      have hc0 : ((volume : Measure (X N)).restrict (Submission.BoseGases.abox N ℓ))
          (Submission.BoseGases.abox N ℓ)ᶜ = 0 := by
        rw [Measure.restrict_apply (Submission.BoseGases.abox_measurable N ℓ).compl,
          Set.compl_inter_self, measure_empty]
      rw [hc0, mul_zero]
    filter_upwards [hae] with q hq
    have hF0 : 0 ≤ Submission.BoseGases.fsKinCoeff c ‖q.1‖ :=
      Submission.BoseGases.fsKinCoeff_nonneg c ‖q.1‖
    have hsquare : ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) q.1
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Ψ) i q.2‖ ^ 2
        ≤ (C / (1 + ‖q.1‖) ^ 3) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hCd q.2 hq i q.1) 2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hF0, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left hsquare hF0
  have hjoint : Integrable (fun q : E3 × X N =>
      Submission.BoseGases.fsKinCoeff c ‖q.1‖ *
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) q.1
          (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Ψ) i q.2‖ ^ 2)
      ((volume : Measure E3).prod
        ((volume : Measure (X N)).restrict (Submission.BoseGases.abox N ℓ))) :=
    hjointInd.congr (Filter.Eventually.of_forall (fun q => by simp only [hpt]))
  refine ⟨hjoint, ?_⟩
  rw [MeasureTheory.integral_integral_swap hjoint]

/-! ## 3. `SlotSplit` for the cube spectral slot and for the matched kinetic word `cubeWord` -/

/-- **The cube-windowed spectral slot is block-splittable**: the abstract engine
`Work.BoseFixB1S.slotSplit_tBdiagForm` fed the swap `cubeSpectral_slotSwap`, transported to
`tBdiagFormInd` along the support identity `chiSmallB M ℓ d u ≡ 0` off `dlBox ℓ d u`. -/
theorem slotSplit_tBwordKinInd_cube {ℓ d c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {M : ℕ} (hM : 4 ≤ M)
    (u : E3) :
    Work.KinPSuperadd.SlotSplit ℓ
      (fun (N : ℕ) (Φ : X N → ℝ) =>
        Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u) c Φ) := by
  refine (Work.BoseFixB1S.slotSplit_tBdiagForm (s := ℓ) (A := Submission.BoseGases.dlBox ℓ d u)
    (V := Work.SmallBoxSliding.boxMass ℓ d u) (χ := Submission.BoseGases.chiSmallB M ℓ d u)
    (F := Submission.BoseGases.fsKinCoeff c)
    (cubeSpectral_slotSwap (ℓ := ℓ) (d := d) (c := c) hℓ hd hM u)).congr_word
    (fun N Φ => ?_)
  simp only [Work.UBBInputs8.tBwordKinInd]
  exact (Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm (Submission.BoseGases.fsKinCoeff c) Φ
    (chiSmallB_eq_zero_off_dlBox (by omega) hℓ hd u)).symm

/-- **The matched kinetic word `cubeWord` is block-splittable**: the count row
(`Work.BoseFixB1S.slotSplitCnPlusBoxInd`, window-free) plus the cube spectral row. -/
theorem slotSplit_cubeWord {ℓ d ε c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {M : ℕ} (hM : 4 ≤ M)
    (u : E3) :
    Work.KinPSuperadd.SlotSplit ℓ
      (fun (N : ℕ) (Φ : X N → ℝ) => Work.BoseFixB1B.cubeWord M ℓ d ε c u Φ) := by
  have hcn : Work.KinPSuperadd.SlotSplit ℓ
      (fun (N : ℕ) (Φ : X N → ℝ) =>
        Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) Φ) :=
    Work.BoseFixB1S.slotSplitCnPlusBoxInd hℓ
      (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)
      (Work.BoseFixB1B.cns_split_dlBox_subset ℓ d u)
      (Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u)
  refine ((hcn.const_mul (Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε)).add
    (slotSplit_tBwordKinInd_cube (ℓ := ℓ) (d := d) (c := c) hℓ hd hM u)).congr_word
    (fun N Φ => ?_)
  simp only [Work.BoseFixB1B.cubeWord, Work.UBBInputs8.tBwordInd]

/-! ## 4. The FS-parameter instances -/

/-- **`SlotSplit` for the matched kinetic word `sbKinCube`.** -/
theorem sbKinCube_slice_slotSplit {v : E3 → ℝ} {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (u : E3) :
    Work.KinPSuperadd.SlotSplit (Work.BoseFixB1.bSide v μ)
      (fun (N : ℕ) (Φ : X N → ℝ) => Work.BoseFixB1B.sbKinCube v μ u Φ) := by
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hM4 : 4 ≤ Work.BoseFixB1.bM v μ := by
    rw [Work.BoseFixB1.bM, Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  refine (slotSplit_cubeWord (ℓ := Work.BoseFixB1.bSide v μ) (d := Work.BoseFixB1.bD v μ)
    (ε := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) (M := Work.BoseFixB1.bM v μ)
    hℓ hd hM4 u).congr_word (fun N Φ => ?_)
  simp only [Work.BoseFixB1B.cubeWord, Work.UBBInputs8.tBwordInd, Work.BoseFixB1B.sbKinCube,
    Work.BoseFixB1B.cubeSpectral, Work.UBBInputs8.tBwordKinInd, Work.BoseFixB1.bGapCoeff,
    Work.BoseFixB1.bA, Work.BoseFixB1.bV]

/-! ## 5. The word-level grouping at the cube cutoff -/

/-- **FS Step E (grouping) at the sliding box, single cube cutoff.** -/
theorem sbWordCube_slice_superadd_regime {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hR16 : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    (u : E3) {N₁ N₂ : ℕ}
    {Φ : Submission.BoseGases.X (N₁ + N₂) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    Work.BoseFixB1B.sbWordCube v h μ u Φ
      ≥ (∫ w in Submission.BoseGases.abox N₂ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            Work.BoseFixB1B.sbWordCube v h μ u
              (fun y => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w))))
        + (∫ y in Submission.BoseGases.abox N₁ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            Work.BoseFixB1B.sbWordCube v h μ u
              (fun w => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w)))) := by
  have hpot := Work.BoseFixB1S.sbPot_slice_superadd_regime (v := v) h hv hv1 hvrad hR hv_supp
    hav hAdm hR16 hRχ u (N₁ := N₁) (N₂ := N₂) hΦ
  have hint := Work.BoseFixB1S.sbPot_slice_integrable_regime (v := v) h hv hv1 hvrad hR hv_supp
    hav hAdm hR16 hRχ u (N₁ := N₁) (N₂ := N₂) hΦ
  have hKin := sbKinCube_slice_slotSplit (v := v) hAdm u
  -- rewrite the `bSide`-spelling of the block boxes into the statement's `sideAt`-spelling
  have hkin : Work.BoseFixB1B.sbKinCube v μ u Φ
      = (∫ w in Submission.BoseGases.abox N₂ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            Work.BoseFixB1B.sbKinCube v μ u
              (fun y => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w))))
        + (∫ y in Submission.BoseGases.abox N₁ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            Work.BoseFixB1B.sbKinCube v μ u
              (fun w => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w)))) := by
    simpa only [Work.BoseFixB1.bSide] using hKin.split Φ hΦ
  have hkin1 : IntegrableOn (fun w : X N₂ =>
        Work.BoseFixB1B.sbKinCube v μ u
          (fun y => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w))))
      (Submission.BoseGases.abox N₂ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) volume := by
    simpa only [Work.BoseFixB1.bSide] using hKin.int₁ Φ hΦ
  have hkin2 : IntegrableOn (fun y : X N₁ =>
        Work.BoseFixB1B.sbKinCube v μ u
          (fun w => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w))))
      (Submission.BoseGases.abox N₁ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) volume := by
    simpa only [Work.BoseFixB1.bSide] using hKin.int₂ Φ hΦ
  have hsw : ∀ {n : ℕ} (Ψ : X n → ℝ),
      Work.BoseFixB1B.sbWordCube v h μ u Ψ
        = Work.BoseFixB1B.sbKinCube v μ u Ψ + Work.BoseFixB1.sbPot h μ u Ψ := fun Ψ => rfl
  have h1 : (∫ w in Submission.BoseGases.abox N₂ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        Work.BoseFixB1B.sbWordCube v h μ u
          (fun y => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w))))
      = (∫ w in Submission.BoseGases.abox N₂ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            Work.BoseFixB1B.sbKinCube v μ u
              (fun y => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w))))
        + (∫ w in Submission.BoseGases.abox N₂ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            Work.BoseFixB1.sbPot h μ u
              (fun y => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w)))) := by
    rw [← integral_add hkin1 hint.1]
    apply integral_congr_ae
    filter_upwards with w
    exact hsw _
  have h2 : (∫ y in Submission.BoseGases.abox N₁ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        Work.BoseFixB1B.sbWordCube v h μ u
          (fun w => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w))))
      = (∫ y in Submission.BoseGases.abox N₁ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            Work.BoseFixB1B.sbKinCube v μ u
              (fun w => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w))))
        + (∫ y in Submission.BoseGases.abox N₁ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            Work.BoseFixB1.sbPot h μ u
              (fun w => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w)))) := by
    rw [← integral_add hkin2 hint.2]
    apply integral_congr_ae
    filter_upwards with y
    exact hsw _
  rw [h1, h2, hsw Φ]
  linarith [hkin, hpot]

end Work.BoseB1Cube
