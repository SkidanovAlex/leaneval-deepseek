import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.K1lim_mul_integrable_pair
import Submission.Work.BoseBoxFock.lintegral_boxPow_eval_pair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiImages_block_aux` — kernel-level toolkit for `chiChiImages ℓ ↑W`, `W ∈ L¹`

The kernel-level facts about the `χχ`-images kernel
`chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ))`, for an integrable (not necessarily measurable,
bounded or compactly supported) weight `W`:

* the pointwise `ℝ≥0∞`-bound by the lattice periodisation `k1PerEnorm ℓ W` of `‖W‖ₑ`
  (`chiImBlk_enorm_le`);
* a.e. strong measurability of `(w,y) ↦ chiChiImages ℓ ↑W w y` and of its transposed version
  (`chiImBlk_aesm`, `chiImBlk_aesm_swap`);
* the a.e. congruence of `k1PerEnorm ℓ W` under an a.e. change of `W`
  (`chiImBlk_perEnorm_ae_congr`);
* finiteness of the `ℝ≥0∞`-integral of the kernel over the box squared
  (`chiImBlk_pair_lintegral_lt_top`) and of a slot pairing over the `n`-particle box
  (`chiImBlk_boxPow_lintegral_lt_top`).

These are the `χχ`-row analogues of the lemmas of `K1lim_mul_integrable`; they are stated for an
*integrable* weight through a measurable representative plus the a.e. congruence, so that the
consumers only need `Integrable W`.

Everything here is `sorry`-free.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

set_option maxHeartbeats 1000000

/-! ## 1. The pointwise bound -/

/-- The sup-bound of `χ_ℓ`, `(√chiNormSq)⁻¹`, as an `ℝ≥0∞` constant. -/
noncomputable def chiImBlkSup : ENNReal :=
  ENNReal.ofReal ((Real.sqrt Submission.BoseGases.chiNormSq)⁻¹)

theorem chiImBlkSup_lt_top : chiImBlkSup < ⊤ := ENNReal.ofReal_lt_top

theorem chiImBlkSup_ne_top : chiImBlkSup ≠ ⊤ := chiImBlkSup_lt_top.ne

/-- The cutoff `χ_ℓ` is bounded by `(√chiNormSq)⁻¹`. -/
theorem chiImBlk_chiScale_enorm_le (ℓ : ℝ) (z : E3) :
    ‖(((Submission.BoseGases.chiScale ℓ z : ℝ)) : ℂ)‖ₑ ≤ chiImBlkSup := by
  rw [chiImBlkSup, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (k1chiScale_norm_le ℓ z)

/-- **The pointwise norm bound** of the `χχ`-images kernel by the lattice periodisation of `‖W‖ₑ`
(unconditional in the weight). -/
theorem chiImBlk_enorm_le (ℓ : ℝ) {W : E3 → ℝ} (w y : E3) :
    ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y‖ₑ
      ≤ chiImBlkSup * chiImBlkSup * k1PerEnorm ℓ W (w - y) := by
  have hsum : ‖∑' m : Fin 3 → ℤ,
        if m = 0 then (0 : ℂ) else ((W (w - y + ℓ • latVec m) : ℝ) : ℂ)‖ₑ
      ≤ k1PerEnorm ℓ W (w - y) := by
    refine le_trans enorm_tsum_le_tsum_enorm ?_
    refine ENNReal.tsum_le_tsum (fun m => ?_)
    by_cases hm : m = 0
    · rw [if_pos hm]; simp
    · rw [if_neg hm, k1enorm_ofReal_cast]
  rw [chiChiImages, enorm_mul, enorm_mul]
  exact mul_le_mul' (mul_le_mul' (chiImBlk_chiScale_enorm_le ℓ w)
    (chiImBlk_chiScale_enorm_le ℓ y)) hsum

/-! ## 2. The periodisation: measurability and a.e. congruence -/

/-- The periodisation of `‖U‖ₑ` is measurable as soon as `U` is. -/
theorem chiImBlk_measurable_perEnorm {ℓ : ℝ} {U : E3 → ℝ} (hUm : Measurable U) :
    Measurable (k1PerEnorm ℓ U) := by
  have hterm : ∀ m : Fin 3 → ℤ, Measurable (fun z : E3 => ‖U (z + ℓ • latVec m)‖ₑ) := fun m =>
    (hUm.comp (continuous_id.add continuous_const).measurable).enorm
  change Measurable (fun z : E3 => ∑' m : Fin 3 → ℤ, ‖U (z + ℓ • latVec m)‖ₑ)
  exact Measurable.tsum (L := SummationFilter.unconditional (Fin 3 → ℤ)) hterm

/-- **The a.e. congruence of the periodisation**: `k1PerEnorm ℓ W` only depends on the a.e. class
of `W`.  (The bad sets are the countably many lattice translates of `{W ≠ U}`.) -/
theorem chiImBlk_perEnorm_ae_congr {ℓ : ℝ} {W U : E3 → ℝ} (h : W =ᵐ[volume] U) :
    (fun z : E3 => k1PerEnorm ℓ W z) =ᵐ[volume] (fun z : E3 => k1PerEnorm ℓ U z) := by
  have h1 : ∀ m : Fin 3 → ℤ, (fun z : E3 => W (z + ℓ • latVec m)) =ᵐ[volume]
      (fun z : E3 => U (z + ℓ • latVec m)) := fun m =>
    ((measurePreserving_add_right (volume : Measure E3) (ℓ • latVec m)).quasiMeasurePreserving).ae_eq h
  refine (eventually_countable_forall.mpr h1).mono (fun z hz => ?_)
  simp only [k1PerEnorm]
  exact tsum_congr (fun m => by
    rw [show W (z + ℓ • latVec m) = U (z + ℓ • latVec m) from by simpa using hz m])

/-! ## 3. A.e. strong measurability of the kernel -/

/-- **A.e. strong measurability of the lattice sum** of the `χχ`-row, at a phase `φ` whose
translations `φ + ℓ•latVec m` are all quasi-measure-preserving. -/
theorem chiImBlk_tsum_aesm {α : Type*} [MeasurableSpace α] {μ : Measure α} {ℓ : ℝ} {W : E3 → ℝ}
    (hW : AEStronglyMeasurable W volume) {φ : α → E3}
    (hφ : ∀ m : Fin 3 → ℤ, Measure.QuasiMeasurePreserving
      (fun p : α => φ p + ℓ • latVec m) μ volume) :
    AEStronglyMeasurable (fun p : α => ∑' m : Fin 3 → ℤ,
      if m = 0 then (0 : ℂ) else ((W (φ p + ℓ • latVec m) : ℝ) : ℂ)) μ := by
  have hWc : AEStronglyMeasurable (fun z : E3 => ((W z : ℝ) : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hW
  refine AEStronglyMeasurable.tsum (L := SummationFilter.unconditional (Fin 3 → ℤ)) (fun m => ?_)
  by_cases hm : m = 0
  · have hfun : (fun p : α => if m = 0 then (0 : ℂ)
        else ((W (φ p + ℓ • latVec m) : ℝ) : ℂ)) = fun _ => (0 : ℂ) := by
      funext p; rw [if_pos hm]
    rw [hfun]; exact aestronglyMeasurable_const
  · have hfun : (fun p : α => if m = 0 then (0 : ℂ)
        else ((W (φ p + ℓ • latVec m) : ℝ) : ℂ))
        = fun p : α => ((W (φ p + ℓ • latVec m) : ℝ) : ℂ) := by
      funext p; rw [if_neg hm]
    rw [hfun]
    exact hWc.comp_quasiMeasurePreserving (hφ m)

/-- The two `χ`-factors of the `χχ`-row are a.e. strongly measurable. -/
theorem chiImBlk_chiScale_aesm {α : Type*} [MeasureSpace α] (ℓ : ℝ)
    (i : α → E3) (hi : Measurable i) :
    AEStronglyMeasurable (fun p : α => ((Submission.BoseGases.chiScale ℓ (i p) : ℝ) : ℂ))
      (volume : Measure α) :=
  (Complex.continuous_ofReal.measurable.comp
    ((Submission.BoseGases.chiScale_continuous ℓ).measurable.comp hi)).aestronglyMeasurable

/-- **A.e. strong measurability of the `χχ`-images kernel** for an a.e. strongly measurable weight.
(The `χ`-factors are continuous and the lattice summands are the weight composed with the
quasi-measure-preserving translations of the difference map.) -/
theorem chiImBlk_aesm {ℓ : ℝ} {W : E3 → ℝ} (hW : AEStronglyMeasurable W volume) :
    AEStronglyMeasurable (fun p : E3 × E3 => chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.1 p.2)
      (volume : Measure (E3 × E3)) := by
  have hχ1 := chiImBlk_chiScale_aesm ℓ (fun p : E3 × E3 => p.1) measurable_fst
  have hχ2 := chiImBlk_chiScale_aesm ℓ (fun p : E3 × E3 => p.2) measurable_snd
  have hT : AEStronglyMeasurable (fun p : E3 × E3 => ∑' m : Fin 3 → ℤ,
      if m = 0 then (0 : ℂ) else ((W (p.1 - p.2 + ℓ • latVec m) : ℝ) : ℂ)) volume :=
    chiImBlk_tsum_aesm (ℓ := ℓ) hW (φ := fun p : E3 × E3 => p.1 - p.2) (fun m =>
      ((measurePreserving_add_right (volume : Measure E3) (ℓ • latVec m)).quasiMeasurePreserving).comp
        (quasiMeasurePreserving_sub (volume : Measure E3) (volume : Measure E3)))
  show AEStronglyMeasurable (fun p : E3 × E3 => (((Submission.BoseGases.chiScale ℓ p.1 : ℝ) : ℂ))
        * (((Submission.BoseGases.chiScale ℓ p.2 : ℝ) : ℂ))
        * (∑' m : Fin 3 → ℤ, if m = 0 then (0 : ℂ)
            else ((W (p.1 - p.2 + ℓ • latVec m) : ℝ) : ℂ))) volume
  exact (hχ1.mul hχ2).mul hT

/-- The same, with the two arguments of the kernel transposed. -/
theorem chiImBlk_aesm_swap {ℓ : ℝ} {W : E3 → ℝ} (hW : AEStronglyMeasurable W volume) :
    AEStronglyMeasurable (fun p : E3 × E3 => chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.2 p.1)
      (volume : Measure (E3 × E3)) := by
  have hχ1 := chiImBlk_chiScale_aesm ℓ (fun p : E3 × E3 => p.1) measurable_fst
  have hχ2 := chiImBlk_chiScale_aesm ℓ (fun p : E3 × E3 => p.2) measurable_snd
  have hT : AEStronglyMeasurable (fun p : E3 × E3 => ∑' m : Fin 3 → ℤ,
      if m = 0 then (0 : ℂ) else ((W (p.2 - p.1 + ℓ • latVec m) : ℝ) : ℂ)) volume :=
    chiImBlk_tsum_aesm (ℓ := ℓ) hW (φ := fun p : E3 × E3 => p.2 - p.1) (fun m =>
      ((measurePreserving_add_right (volume : Measure E3) (ℓ • latVec m)).quasiMeasurePreserving).comp
        ((quasiMeasurePreserving_sub (volume : Measure E3) (volume : Measure E3)).comp
          (MeasureTheory.Measure.measurePreserving_swap (μ := (volume : Measure E3))
            (ν := (volume : Measure E3))).quasiMeasurePreserving))
  show AEStronglyMeasurable (fun p : E3 × E3 => (((Submission.BoseGases.chiScale ℓ p.2 : ℝ) : ℂ))
        * (((Submission.BoseGases.chiScale ℓ p.1 : ℝ) : ℂ))
        * (∑' m : Fin 3 → ℤ, if m = 0 then (0 : ℂ)
            else ((W (p.2 - p.1 + ℓ • latVec m) : ℝ) : ℂ))) volume
  exact (hχ2.mul hχ1).mul hT

/-- **A.e. strong measurability of the kernel at two configuration slots** `p.1`, `p.2`. -/
theorem chiImBlk_aesm_pairSlots {n : ℕ} {ℓ : ℝ} {W : E3 → ℝ}
    (hW : AEStronglyMeasurable W volume) (p : Fin n × Fin n) (hp : p.1 ≠ p.2) :
    AEStronglyMeasurable (fun x : Work.BoseDict.Xn n =>
      chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (x p.1) (x p.2))
      (volume : Measure (Work.BoseDict.Xn n)) := by
  have hχ1 := chiImBlk_chiScale_aesm ℓ (fun x : Work.BoseDict.Xn n => x p.1)
    (measurable_pi_apply p.1)
  have hχ2 := chiImBlk_chiScale_aesm ℓ (fun x : Work.BoseDict.Xn n => x p.2)
    (measurable_pi_apply p.2)
  have hT : AEStronglyMeasurable (fun x : Work.BoseDict.Xn n => ∑' m : Fin 3 → ℤ,
      if m = 0 then (0 : ℂ) else ((W (x p.1 - x p.2 + ℓ • latVec m) : ℝ) : ℂ)) volume :=
    chiImBlk_tsum_aesm (ℓ := ℓ) hW (φ := fun x : Work.BoseDict.Xn n => x p.1 - x p.2) (fun m =>
      ((measurePreserving_add_right (volume : Measure E3) (ℓ • latVec m)).quasiMeasurePreserving).comp
        ((quasiMeasurePreserving_sub (volume : Measure E3) (volume : Measure E3)).comp
          (quasiMeasurePreserving_eval_pair_fst p hp)))
  show AEStronglyMeasurable (fun x : Work.BoseDict.Xn n =>
        (((Submission.BoseGases.chiScale ℓ (x p.1) : ℝ) : ℂ))
        * (((Submission.BoseGases.chiScale ℓ (x p.2) : ℝ) : ℂ))
        * (∑' m : Fin 3 → ℤ, if m = 0 then (0 : ℂ)
            else ((W (x p.1 - x p.2 + ℓ • latVec m) : ℝ) : ℂ))) volume
  exact (hχ1.mul hχ2).mul hT

/-! ## 4. Finiteness of the two integrated majorants -/

/-- **Finiteness over the box squared.**  The `ℝ≥0∞`-integral of the `χχ`-images kernel over the
box squared is finite for an integrable weight. -/
theorem chiImBlk_pair_lintegral_lt_top {ℓ : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWi : MeasureTheory.Integrable W) :
    (∫⁻ p : E3 × E3, (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.1
        * (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.2
        * ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.1 p.2‖ₑ) < ⊤ := by
  obtain ⟨U, hUm, hWU⟩ : ∃ U : E3 → ℝ, Measurable U ∧ W =ᵐ[volume] U :=
    ⟨AEStronglyMeasurable.mk W hWi.aestronglyMeasurable,
      (hWi.aestronglyMeasurable.stronglyMeasurable_mk).measurable,
      hWi.aestronglyMeasurable.ae_eq_mk⟩
  have hUfin : ∫⁻ z : E3, ‖U z‖ₑ < ⊤ := by
    have h1 : ∫⁻ z : E3, ‖U z‖ₑ = ∫⁻ z : E3, ‖W z‖ₑ :=
      lintegral_congr_ae (hWU.mono (fun z hz => by show ‖U z‖ₑ = ‖W z‖ₑ; rw [hz]))
    rw [h1]
    exact hWi.hasFiniteIntegral
  have hae : (fun p : E3 × E3 => k1PerEnorm ℓ W (p.1 - p.2)) =ᵐ[volume]
      (fun p : E3 × E3 => k1PerEnorm ℓ U (p.1 - p.2)) :=
    (quasiMeasurePreserving_sub (volume : Measure E3) (volume : Measure E3)).ae_eq
      (chiImBlk_perEnorm_ae_congr (ℓ := ℓ) hWU)
  have hpt : ∀ p : E3 × E3, (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.1
      * (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.2
      * ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.1 p.2‖ₑ
      ≤ chiImBlkSup * chiImBlkSup
        * ((boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.1
          * (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.2
          * k1PerEnorm ℓ W (p.1 - p.2)) := by
    intro p
    have h1 := chiImBlk_enorm_le ℓ (W := W) p.1 p.2
    calc (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.1
          * (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.2
          * ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.1 p.2‖ₑ
        ≤ (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.1
          * (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.2
          * (chiImBlkSup * chiImBlkSup * k1PerEnorm ℓ W (p.1 - p.2)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = chiImBlkSup * chiImBlkSup
          * ((boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.1
            * (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.2
            * k1PerEnorm ℓ W (p.1 - p.2)) := by ring
  calc ∫⁻ p : E3 × E3, (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.1
        * (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.2
        * ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.1 p.2‖ₑ
      ≤ ∫⁻ p : E3 × E3, chiImBlkSup * chiImBlkSup
          * ((boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.1
            * (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.2
            * k1PerEnorm ℓ W (p.1 - p.2)) := lintegral_mono hpt
    _ = chiImBlkSup * chiImBlkSup
        * ∫⁻ p : E3 × E3, (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.1
            * (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.2
            * k1PerEnorm ℓ W (p.1 - p.2) :=
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top chiImBlkSup_ne_top chiImBlkSup_ne_top)
    _ = chiImBlkSup * chiImBlkSup
        * ∫⁻ p : E3 × E3, (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.1
            * (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.2
            * k1PerEnorm ℓ U (p.1 - p.2) := by
        congr 1
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with p hp
        rw [hp]
    _ = chiImBlkSup * chiImBlkSup
        * ∫⁻ p : E3 × E3, (boxL ℓ ×ˢ boxL ℓ).indicator
            (fun p : E3 × E3 => k1PerEnorm ℓ U (p.1 - p.2)) p := by
        congr 1
        exact lintegral_congr (fun p =>
          (prod_indicator_eq (boxL ℓ) (boxL ℓ) (fun a b => k1PerEnorm ℓ U (a - b)) p).symm)
    _ ≤ chiImBlkSup * chiImBlkSup * (ENNReal.ofReal (ℓ ^ 3) * ∫⁻ z : E3, ‖U z‖ₑ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact k1lintegral_indicator_perEnorm_le hℓ hUm.aestronglyMeasurable
    _ < ⊤ := ENNReal.mul_lt_top
        (ENNReal.mul_lt_top chiImBlkSup_lt_top chiImBlkSup_lt_top)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hUfin)

/-- **Finiteness over the `n`-particle box** at the two configuration slots `p.1`, `p.2`. -/
theorem chiImBlk_boxPow_lintegral_lt_top {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWi : MeasureTheory.Integrable W) (p : Fin n × Fin n) (hp : p.1 ≠ p.2) :
    (∫⁻ x : Xn n, (Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) x
        * ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (x p.1) (x p.2)‖ₑ) < ⊤ := by
  obtain ⟨U, hUm, hWU⟩ : ∃ U : E3 → ℝ, Measurable U ∧ W =ᵐ[volume] U :=
    ⟨AEStronglyMeasurable.mk W hWi.aestronglyMeasurable,
      (hWi.aestronglyMeasurable.stronglyMeasurable_mk).measurable,
      hWi.aestronglyMeasurable.ae_eq_mk⟩
  have hUfin : ∫⁻ z : E3, ‖U z‖ₑ < ⊤ := by
    have h1 : ∫⁻ z : E3, ‖U z‖ₑ = ∫⁻ z : E3, ‖W z‖ₑ :=
      lintegral_congr_ae (hWU.mono (fun z hz => by show ‖U z‖ₑ = ‖W z‖ₑ; rw [hz]))
    rw [h1]
    exact hWi.hasFiniteIntegral
  have hqmp : Measure.QuasiMeasurePreserving (fun x : Xn n => x p.1 - x p.2)
      (volume : Measure (Xn n)) volume :=
    (quasiMeasurePreserving_sub (volume : Measure E3) (volume : Measure E3)).comp
      (quasiMeasurePreserving_eval_pair_fst p hp)
  have hae : (fun x : Xn n => k1PerEnorm ℓ W (x p.1 - x p.2)) =ᵐ[volume]
      (fun x : Xn n => k1PerEnorm ℓ U (x p.1 - x p.2)) :=
    hqmp.ae_eq (chiImBlk_perEnorm_ae_congr (ℓ := ℓ) hWU)
  have hgU : Measurable (Function.uncurry (fun a b : E3 => k1PerEnorm ℓ U (a - b))) :=
    (chiImBlk_measurable_perEnorm (ℓ := ℓ) hUm).comp (by fun_prop)
  have hpt : ∀ x : Xn n, (Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) x
      * ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (x p.1) (x p.2)‖ₑ
      ≤ chiImBlkSup * chiImBlkSup
        * ((Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) x
          * k1PerEnorm ℓ W (x p.1 - x p.2)) := by
    intro x
    have h1 := chiImBlk_enorm_le ℓ (W := W) (x p.1) (x p.2)
    calc (Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) x
          * ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (x p.1) (x p.2)‖ₑ
        ≤ (Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) x
          * (chiImBlkSup * chiImBlkSup * k1PerEnorm ℓ W (x p.1 - x p.2)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = chiImBlkSup * chiImBlkSup
          * ((Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) x
            * k1PerEnorm ℓ W (x p.1 - x p.2)) := by ring
  calc ∫⁻ x : Xn n, (Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) x
        * ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (x p.1) (x p.2)‖ₑ
      ≤ ∫⁻ x : Xn n, chiImBlkSup * chiImBlkSup
          * ((Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) x
            * k1PerEnorm ℓ W (x p.1 - x p.2)) := lintegral_mono hpt
    _ = chiImBlkSup * chiImBlkSup
        * ∫⁻ x : Xn n, (Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) x
            * k1PerEnorm ℓ W (x p.1 - x p.2) :=
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top chiImBlkSup_ne_top chiImBlkSup_ne_top)
    _ = chiImBlkSup * chiImBlkSup
        * ∫⁻ x : Xn n, (Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) x
            * k1PerEnorm ℓ U (x p.1 - x p.2) := by
        congr 1
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with x hx
        rw [hx]
    _ = chiImBlkSup * chiImBlkSup
        * (MeasureTheory.volume (Set.univ.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} =>
              boxL ℓ))
          * ∫⁻ q : E3 × E3, (boxL ℓ).indicator (fun _ => (1 : ENNReal)) q.1
              * ((boxL ℓ).indicator (fun _ => (1 : ENNReal)) q.2
                * k1PerEnorm ℓ U (q.1 - q.2))) := by
        rw [lintegral_boxPow_eval_pair (i := p.1) (j := p.2) hp
          (g := fun a b : E3 => k1PerEnorm ℓ U (a - b)) hgU]
    _ = chiImBlkSup * chiImBlkSup
        * (MeasureTheory.volume (Set.univ.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} =>
              boxL ℓ))
          * ∫⁻ q : E3 × E3, (boxL ℓ ×ˢ boxL ℓ).indicator
              (fun q : E3 × E3 => k1PerEnorm ℓ U (q.1 - q.2)) q) := by
        congr 1
        congr 1
        refine lintegral_congr (fun q => ?_)
        rw [prod_indicator_eq (boxL ℓ) (boxL ℓ) (fun a b => k1PerEnorm ℓ U (a - b)) q, mul_assoc]
    _ ≤ chiImBlkSup * chiImBlkSup
        * (MeasureTheory.volume (Set.univ.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} =>
              boxL ℓ))
          * (ENNReal.ofReal (ℓ ^ 3) * ∫⁻ z : E3, ‖U z‖ₑ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact k1lintegral_indicator_perEnorm_le hℓ hUm.aestronglyMeasurable
    _ < ⊤ := by
        refine ENNReal.mul_lt_top
          (ENNReal.mul_lt_top chiImBlkSup_lt_top chiImBlkSup_lt_top) ?_
        refine ENNReal.mul_lt_top ?_ (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hUfin)
        have hvol : MeasureTheory.volume
            (Set.univ.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => boxL ℓ)) < ⊤ :=
          (isCompact_boxPiSet (ι := {k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) hℓ).measure_lt_top
        exact hvol

/-! ## 5. The pair form (box-squared pairing) and its transpose -/

/-- **The `χχ`-images kernel is `L¹` against a bounded, box-squared-supported kernel** for an
integrable weight — the direct analogue of `K1lim_mul_integrable` for the single `χχ`-row. -/
theorem chiImBlk_pair_integrable {ℓ : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWi : MeasureTheory.Integrable W) {G : E3 → E3 → ℂ}
    (hGm : MeasureTheory.AEStronglyMeasurable (Function.uncurry G)
      (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)))
    (hGb : ∃ C : ℝ, ∀ w y, ‖G w y‖ ≤ C)
    (hGs : Function.support (Function.uncurry G) ⊆ boxL ℓ ×ˢ boxL ℓ) :
    MeasureTheory.Integrable
      (Function.uncurry (fun w y : E3 => chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y))
      (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) := by
  obtain ⟨Cg, hCg⟩ := hGb
  have hCg0 : 0 ≤ max Cg 0 := le_max_right _ _
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : E3 × E3 => chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.1 p.2)
      (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) :=
    chiImBlk_aesm (ℓ := ℓ) hWi.aestronglyMeasurable
  refine ⟨haesm.mul hGm, ?_⟩
  have hpt : ∀ p : E3 × E3,
      ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.1 p.2 * G p.1 p.2‖ₑ
      ≤ ENNReal.ofReal (max Cg 0)
        * ((boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.1
          * (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.2
          * ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.1 p.2‖ₑ) := by
    intro p
    rw [enorm_mul]
    by_cases hp : p ∈ boxL ℓ ×ˢ boxL ℓ
    · obtain ⟨h1, h2⟩ := Set.mem_prod.mp hp
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
      simp only [one_mul]
      have hGbd : ‖G p.1 p.2‖ₑ ≤ ENNReal.ofReal (max Cg 0) := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (le_trans (hCg p.1 p.2) (le_max_left Cg 0))
      calc ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.1 p.2‖ₑ * ‖G p.1 p.2‖ₑ
          ≤ ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.1 p.2‖ₑ
            * ENNReal.ofReal (max Cg 0) :=
            mul_le_mul_of_nonneg_left hGbd (by positivity)
        _ = ENNReal.ofReal (max Cg 0)
            * ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.1 p.2‖ₑ := mul_comm _ _
    · have hG0 : G p.1 p.2 = 0 := by
        by_contra hne
        exact hp (hGs (Function.mem_support.mpr hne))
      rw [hG0]
      simp
  calc ∫⁻ p : E3 × E3,
        ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.1 p.2 * G p.1 p.2‖ₑ
      ≤ ∫⁻ p : E3 × E3, ENNReal.ofReal (max Cg 0)
          * ((boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.1
            * (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.2
            * ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.1 p.2‖ₑ) := lintegral_mono hpt
    _ = ENNReal.ofReal (max Cg 0)
        * ∫⁻ p : E3 × E3, (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.1
            * (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.2
            * ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.1 p.2‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (chiImBlk_pair_lintegral_lt_top hℓ hWi)

/-- The transposed pair form: the kernel is evaluated at `(u,y)` while the test function reads
`(y,u)`.  Obtained from `chiImBlk_pair_integrable` by the measure-preserving coordinate swap. -/
theorem chiImBlk_pair_integrable_swap {ℓ : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWi : MeasureTheory.Integrable W) {G : E3 → E3 → ℂ}
    (hGm : MeasureTheory.AEStronglyMeasurable (Function.uncurry G)
      (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)))
    (hGb : ∃ C : ℝ, ∀ w y, ‖G w y‖ ≤ C)
    (hGs : Function.support (Function.uncurry G) ⊆ boxL ℓ ×ˢ boxL ℓ) :
    MeasureTheory.Integrable
      (Function.uncurry (fun y u : E3 => chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) u y * G y u))
      (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) := by
  have hmp : MeasurePreserving (Prod.swap : E3 × E3 → E3 × E3)
      (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3))
      (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) :=
    MeasureTheory.Measure.measurePreserving_swap (μ := (volume : Measure E3))
      (ν := (volume : Measure E3))
  have hG'm : MeasureTheory.AEStronglyMeasurable (Function.uncurry (fun a b : E3 => G b a))
      (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) := by
    have h : (Function.uncurry (fun a b : E3 => G b a))
        = (Function.uncurry G) ∘ (Prod.swap : E3 × E3 → E3 × E3) := rfl
    rw [h]
    exact hGm.comp_measurePreserving hmp
  have hG'b : ∃ C : ℝ, ∀ a b, ‖G b a‖ ≤ C := hGb.imp fun C hC a b => hC b a
  have hG's : Function.support (Function.uncurry (fun a b : E3 => G b a)) ⊆ boxL ℓ ×ˢ boxL ℓ := by
    intro z hz
    have h2 : Function.uncurry G (Prod.swap z) ≠ 0 := hz
    obtain ⟨h1, h2⟩ := Set.mem_prod.mp (hGs h2)
    exact Set.mem_prod.mpr ⟨h2, h1⟩
  have h := chiImBlk_pair_integrable hℓ hWi hG'm hG'b hG's
  have hg : MeasureTheory.AEStronglyMeasurable
      (fun p : E3 × E3 => chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.1 p.2 * G p.2 p.1)
      (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) := h.aestronglyMeasurable
  exact ((hmp.integrable_comp hg).mpr h).congr (Filter.Eventually.of_forall fun _ => rfl)

end Work.BoseBoxFock
