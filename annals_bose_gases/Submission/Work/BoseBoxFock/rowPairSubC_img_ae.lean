import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiChiImages_mul_integrable_prod
import Submission.Work.BoseBoxFock.chiChiImages_mul_integrable_swapJoint
import Submission.Work.BoseBoxFock.chiImages_mul_integrable
import Submission.Work.BoseBoxFock.rowPairSubC_stripImages
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.rowPairSubC_img_ae` — the a.e. form of the `χχ`-images strip at the row level

`Work.BoseBoxFock.rowPairSubC_stripImages` proves the row-level (S3) step

    rowPairSubC a Θ A (K1lim ℓ W₁') (K1lim ℓ W₂')
      − rowPairSubC a Θ A (K1lim ℓ W₁' − χχW₁) (K1lim ℓ W₂' − χχW₂)

is bounded by `2|a|ε Σ_{p}(…)` under the hypothesis that the four weights `W₁, W₂, W₁', W₂'` are
**measurable, bounded and compactly supported**.  Its proof uses those hypotheses only in order to
produce the integrability/Fubini facts (at the two kernels) required by the generic block lemmas
`block13_KsubDir`, `blockII1_KsubDir`, `blockTwo3_KsubDir`; the measurability of the weights
themselves is never used.

This file replays that argument with the weights assumed **only integrable**.  The integrability
facts for the `χχ`-images kernel at an `L¹` weight are supplied by the `a.e.`-level toolkit
`chiImBlk_pair_integrable`, `chiImBlk_pair_integrable_swap`, `chiImBlk_boxPow_lintegral_lt_top`
(and the consumers `chiImages_mul_integrable`, `chiChiImages_mul_integrable_swapJoint`,
`chiChiImages_mul_integrable_prod`), which replace the weight by a measurable representative and
transport along the proved a.e. congruence `ae_chiChiImages_congr`.

The three block-level helpers below are the `a.e.` versions of the proved
`block13_KsubDir_stripImages` / `blockII1_KsubDir_stripImages` / `blockTwo3_KsubDir_stripImages`,
and the final theorem is the row assembly through the proved `rowPairSubC_KsubDir`.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 0. Elementary helpers -/

/-- Pointwise-equal function to an integrable function: integrable. -/
private lemma imgSub_congr_pt {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℂ}
    (h : Integrable f μ) (hfg : ∀ a, f a = g a) : Integrable g μ :=
  h.congr (Filter.Eventually.of_forall hfg)

/-- The two-fold update keeps the value inserted first. -/
private lemma imgUpd_fst {n : ℕ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2) {z : Xn n} {y u : E3} :
    Function.update (Function.update z p.1 y) p.2 u p.1 = y := by
  rw [Function.update_apply, if_neg hp, Function.update_self]

/-- The two-fold update keeps the value inserted second. -/
private lemma imgUpd_snd {n : ℕ} {p : Fin n × Fin n} {z : Xn n} {y u : E3} :
    Function.update (Function.update z p.1 y) p.2 u p.2 = u := by
  rw [Function.update_apply, if_pos rfl]

/-- **The `χχ`-images kernel at the two configuration slots `p.1`, `p.2`** is `L¹` against a
bounded, `boxPow n ℓ`-supported functional `F`, for an integrable weight — the `χχ`-row analogue of
`K1lim_mul_integrable_pair`. -/
private theorem imgPairSlots_integrable {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {W : E3 → ℝ} (hWi : MeasureTheory.Integrable W)
    {F : Xn n → ℂ} (hFm : MeasureTheory.AEStronglyMeasurable F (volume : Measure (Xn n)))
    (hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C)
    (hFs : Function.support F ⊆ Work.MB.boxPow n ℓ) :
    MeasureTheory.Integrable (fun x : Xn n => chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (x p.1) (x p.2) * F x)
      (volume : Measure (Xn n)) := by
  obtain ⟨C, hC⟩ := hFb
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun x : Xn n => chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (x p.1) (x p.2)) (volume : Measure (Xn n)) :=
    chiImBlk_aesm_pairSlots (ℓ := ℓ) hWi.aestronglyMeasurable p hp
  refine ⟨haesm.mul hFm, ?_⟩
  have hbnd : ∀ x : Xn n, ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (x p.1) (x p.2) * F x‖ₑ
      ≤ ENNReal.ofReal (max C 0)
        * ((Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) x
          * ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (x p.1) (x p.2)‖ₑ) := by
    intro x
    rw [enorm_mul]
    have hFbd : ‖F x‖ₑ ≤ ENNReal.ofReal (max C 0)
        * (Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) x := by
      by_cases hx : x ∈ Work.MB.boxPow n ℓ
      · rw [Set.indicator_of_mem hx, mul_one, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (le_trans (hC x) (le_max_left C 0))
      · rw [show F x = 0 from by
            by_contra hne; exact hx (hFs (Function.mem_support.mpr hne)), enorm_zero]
        simp
    calc ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (x p.1) (x p.2)‖ₑ * ‖F x‖ₑ
        ≤ ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (x p.1) (x p.2)‖ₑ
          * (ENNReal.ofReal (max C 0)
            * (Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) x) :=
          mul_le_mul_of_nonneg_left hFbd (by positivity)
      _ = ENNReal.ofReal (max C 0)
          * ((Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) x
            * ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (x p.1) (x p.2)‖ₑ) := by ring
  calc ∫⁻ x : Xn n, ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (x p.1) (x p.2) * F x‖ₑ
      ≤ ∫⁻ x : Xn n, ENNReal.ofReal (max C 0)
          * ((Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) x
            * ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (x p.1) (x p.2)‖ₑ) := lintegral_mono hbnd
    _ = ENNReal.ofReal (max C 0)
        * ∫⁻ x : Xn n, (Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) x
            * ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (x p.1) (x p.2)‖ₑ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (chiImBlk_boxPow_lintegral_lt_top hℓ hWi p hp)

/-- **The slot form** of the `χχ`-images integrability at an integrable weight: the kernel read at
the slot `p.2` of the configuration and at a free variable, against a bounded, box-supported
functional `H`.  (Extracted from `chiImages_mul_integrable`, whose slot conjunct is bundled with an
unused pair conjunct.) -/
private theorem imgSlot_integrable {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {W : E3 → ℝ} (hWi : MeasureTheory.Integrable W)
    {H : Xn n × E3 → ℂ}
    (hHm : MeasureTheory.AEStronglyMeasurable H (volume : Measure (Xn n × E3)))
    (hHb : ∃ C : ℝ, ∀ z, ‖H z‖ ≤ C)
    (hHs : Function.support H ⊆ Set.prod (Work.MB.boxPow n ℓ) (boxL ℓ)) :
    MeasureTheory.Integrable (fun z : Xn n × E3 => chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (z.1 p.2) z.2 * H z)
      (volume : Measure (Xn n × E3)) :=
  (chiImages_mul_integrable (n := n) (ℓ := ℓ) hℓ p (W := W) hWi
      (G := fun _ _ : E3 => (0 : ℂ)) measurable_const.aestronglyMeasurable
      ⟨0, fun _ _ => by simp⟩ (fun x hx => absurd rfl hx)).2 hHm hHb hHs

/-! ## 1. The three block-level (S2) bounds at an integrable weight -/

/-- **Block I, `a.e.` form.**  For an integrable weight the block-I row shape at the limit kernel
`K1lim ℓ W'` differs from its value at the images-stripped kernel `K1lim ℓ W' − χχW` by
`ε·(√pairEnergy + √massBox)` of the fibre `pairG13`. -/
theorem rowImg_block13 {n : ℕ} {ℓ ε : ℝ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (hℓ : 0 < ℓ)
    {Θ Θ₀ : Xn n → ℂ} {A B : E3 → ℂ} {W W' : E3 → ℝ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (hΘind : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x)
    (hAm : Measurable A) (hAb : ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C)
    (hBm : Measurable B) (hBb : ∃ C : ℝ, ∀ x, ‖B x‖ ≤ C)
    (hCutA : CutSmooth1 ℓ A) (hCutB : CutSmooth1 ℓ B)
    (hW'i : MeasureTheory.Integrable W') (hWi : MeasureTheory.Integrable W) (hε : 0 ≤ ε)
    (hPair : ∀ G : E3 → E3 → ℂ, BoxSmooth ℓ G →
      ‖∫ w in boxL ℓ, ∫ y in boxL ℓ,
          chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y‖
        ≤ ε * (Real.sqrt (L1Tails.pairEnergy ℓ G) + Real.sqrt (massBox ℓ G))) :
    ‖rowShape13 Θ A B (K1lim ℓ W') p
      - rowShape13 Θ A B (fun w y => K1lim ℓ W' w y
          - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y) p‖
      ≤ ε * (Real.sqrt (L1Tails.pairEnergy ℓ (pairG13 p Θ A B))
          + Real.sqrt (massBox ℓ (pairG13 p Θ A B))) := by
  classical
  have hCsupp : Function.support (Function.uncurry (pairG13 p Θ A B)) ⊆
      Set.prod (boxL ℓ) (boxL ℓ) := (pairG_supports p hp hΘs).1
  have hbs : BoxSmooth ℓ (pairG13 p Θ A B) :=
    (boxSmooth_fibres hℓ p hp ⟨Θ₀, hΘ₀, hΘind⟩ hCutA hCutB).1
  have hGm : Measurable (Function.uncurry (pairG13 p Θ A B)) :=
    pairG13_measurable p hp hΘm hAm hBm
  obtain ⟨CG, _hCG0, hCG⟩ := pairG13_bounded p hp hΘm hΘb hΘs hAm hAb hBm hBb
  have hGb : ∃ C : ℝ, ∀ w y, ‖pairG13 p Θ A B w y‖ ≤ C := ⟨CG, hCG⟩
  -- the kernel difference is the images kernel, so the pairing hypothesis applies verbatim
  have hPair' : ∀ G : E3 → E3 → ℂ, BoxSmooth ℓ G →
      ‖∫ w in boxL ℓ, ∫ y in boxL ℓ,
          (K1lim ℓ W' w y - (fun w y => K1lim ℓ W' w y - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y) w y) * G w y‖
        ≤ ε * (Real.sqrt (L1Tails.pairEnergy ℓ G) + Real.sqrt (massBox ℓ G)) := by
    intro G hG
    have hcongr : (∫ w in boxL ℓ, ∫ y in boxL ℓ,
          (K1lim ℓ W' w y - (fun w y => K1lim ℓ W' w y - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y) w y) * G w y)
        = ∫ w in boxL ℓ, ∫ y in boxL ℓ, chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y := by
      refine MeasureTheory.setIntegral_congr_fun
        (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ) (fun w hw => ?_)
      refine MeasureTheory.setIntegral_congr_fun
        (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ) (fun y hy => ?_)
      ring
    rw [hcongr]
    exact hPair G hG
  -- the two pair integrability facts
  have hIntK : MeasureTheory.Integrable (Function.uncurry (fun w y : E3 =>
      K1lim ℓ W' w y * pairG13 p Θ A B w y)) (volume : Measure (E3 × E3)) :=
    K1lim_mul_integrable hℓ hW'i hGm.aestronglyMeasurable hGb hCsupp
  have hIntKchi : MeasureTheory.Integrable (Function.uncurry (fun w y : E3 =>
      chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * pairG13 p Θ A B w y)) (volume : Measure (E3 × E3)) :=
    chiImBlk_pair_integrable hℓ hWi hGm.aestronglyMeasurable hGb hCsupp
  have hIntK' : MeasureTheory.Integrable (Function.uncurry (fun w y : E3 =>
      (K1lim ℓ W' w y - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y) * pairG13 p Θ A B w y))
      (volume : Measure (E3 × E3)) :=
    imgSub_congr_pt (hIntK.sub hIntKchi) (fun q => by
      show K1lim ℓ W' q.1 q.2 * pairG13 p Θ A B q.1 q.2
          - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) q.1 q.2 * pairG13 p Θ A B q.1 q.2
        = (K1lim ℓ W' q.1 q.2 - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) q.1 q.2) * pairG13 p Θ A B q.1 q.2
      ring)
  -- the two slot integrability facts
  obtain ⟨hHm, hHn, hHs⟩ := block13_inner_weak p hp hΘm hΘb hΘs hAm hAb hBm hBb
  have hHbd : ∃ C : ℝ, ∀ z : Xn n × E3, ‖(∫ u : E3, star (Θ z.1) * A (z.1 p.1) * star (B u)
      * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u))‖ ≤ C :=
    hHn.imp fun C hC => hC.2
  have hHsp : Function.support (fun z : Xn n × E3 => ∫ u : E3, star (Θ z.1) * A (z.1 p.1)
      * star (B u) * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u))
      ⊆ Set.prod (Work.MB.boxPow n ℓ) (boxL ℓ) :=
    fun z hz => by_contra fun h => hz (hHs z h)
  have hInt1 : MeasureTheory.Integrable (fun z : Xn n × E3 => K1lim ℓ W' (z.1 p.2) z.2
      * (∫ u : E3, star (Θ z.1) * A (z.1 p.1) * star (B u)
          * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u)))
      (volume : Measure (Xn n × E3)) :=
    K1lim_mul_integrable_slot hℓ p hW'i hHm.aestronglyMeasurable hHbd hHsp
  have hInt1chi : MeasureTheory.Integrable (fun z : Xn n × E3 => chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (z.1 p.2) z.2
      * (∫ u : E3, star (Θ z.1) * A (z.1 p.1) * star (B u)
          * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u)))
      (volume : Measure (Xn n × E3)) :=
    imgSlot_integrable hℓ p hWi hHm.aestronglyMeasurable hHbd hHsp
  have hInt1' : MeasureTheory.Integrable (fun z : Xn n × E3 =>
      (K1lim ℓ W' (z.1 p.2) z.2 - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (z.1 p.2) z.2)
        * (∫ u : E3, star (Θ z.1) * A (z.1 p.1) * star (B u)
            * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u)))
      (volume : Measure (Xn n × E3)) :=
    imgSub_congr_pt (hInt1.sub hInt1chi) (fun z => by
      show K1lim ℓ W' (z.1 p.2) z.2
            * (∫ u : E3, star (Θ z.1) * A (z.1 p.1) * star (B u)
                * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u))
          - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (z.1 p.2) z.2
            * (∫ u : E3, star (Θ z.1) * A (z.1 p.1) * star (B u)
                * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u))
        = (K1lim ℓ W' (z.1 p.2) z.2 - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (z.1 p.2) z.2)
            * (∫ u : E3, star (Θ z.1) * A (z.1 p.1) * star (B u)
                * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u))
      ring)
  exact block13_KsubDir (K := K1lim ℓ W') (K' := fun w y => K1lim ℓ W' w y - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y)
    p hp hℓ hε hCsupp hPair' hbs hIntK hIntK' hInt1 hInt1'

/-- **Block II.2, `a.e.` form.**  The same statement for the block-II.2 shape (the kernel at the two
configuration slots) and the fibre `pairG23`. -/
theorem rowImg_blockTwo3 {n : ℕ} {ℓ ε : ℝ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (hℓ : 0 < ℓ)
    {Θ Θ₀ : Xn n → ℂ} {A B : E3 → ℂ} {W W' : E3 → ℝ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (hΘind : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x)
    (hAm : Measurable A) (hAb : ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C)
    (hBm : Measurable B) (hBb : ∃ C : ℝ, ∀ x, ‖B x‖ ≤ C)
    (hCutA : CutSmooth1 ℓ A) (hCutB : CutSmooth1 ℓ B)
    (hW'i : MeasureTheory.Integrable W') (hWi : MeasureTheory.Integrable W) (hε : 0 ≤ ε)
    (hPair : ∀ G : E3 → E3 → ℂ, BoxSmooth ℓ G →
      ‖∫ w in boxL ℓ, ∫ y in boxL ℓ,
          chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y‖
        ≤ ε * (Real.sqrt (L1Tails.pairEnergy ℓ G) + Real.sqrt (massBox ℓ G))) :
    ‖rowShape23 Θ A B (K1lim ℓ W') p
      - rowShape23 Θ A B (fun w y => K1lim ℓ W' w y
          - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y) p‖
      ≤ ε * (Real.sqrt (L1Tails.pairEnergy ℓ (pairG23 p Θ A B))
          + Real.sqrt (massBox ℓ (pairG23 p Θ A B))) := by
  classical
  have hCsupp : Function.support (Function.uncurry (pairG23 p Θ A B)) ⊆
      Set.prod (boxL ℓ) (boxL ℓ) := (pairG_supports p hp hΘs).2.1
  have hbs : BoxSmooth ℓ (pairG23 p Θ A B) :=
    (boxSmooth_fibres hℓ p hp ⟨Θ₀, hΘ₀, hΘind⟩ hCutA hCutB).2.1
  have hGm : Measurable (Function.uncurry (pairG23 p Θ A B)) :=
    pairG23_measurable p hΘm hAm hBm
  have hGb : ∃ C : ℝ, ∀ w y, ‖pairG23 p Θ A B w y‖ ≤ C :=
    pairG23_bounded p hp hΘs hΘb hAb hBb
  have hPair' : ∀ G : E3 → E3 → ℂ, BoxSmooth ℓ G →
      ‖∫ w in boxL ℓ, ∫ y in boxL ℓ,
          (K1lim ℓ W' w y - (fun w y => K1lim ℓ W' w y - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y) w y) * G w y‖
        ≤ ε * (Real.sqrt (L1Tails.pairEnergy ℓ G) + Real.sqrt (massBox ℓ G)) := by
    intro G hG
    have hcongr : (∫ w in boxL ℓ, ∫ y in boxL ℓ,
          (K1lim ℓ W' w y - (fun w y => K1lim ℓ W' w y - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y) w y) * G w y)
        = ∫ w in boxL ℓ, ∫ y in boxL ℓ, chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y := by
      refine MeasureTheory.setIntegral_congr_fun
        (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ) (fun w hw => ?_)
      refine MeasureTheory.setIntegral_congr_fun
        (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ) (fun y hy => ?_)
      ring
    rw [hcongr]
    exact hPair G hG
  have hIntK : MeasureTheory.Integrable (Function.uncurry (fun w y : E3 =>
      K1lim ℓ W' w y * pairG23 p Θ A B w y)) (volume : Measure (E3 × E3)) :=
    K1lim_mul_integrable hℓ hW'i hGm.aestronglyMeasurable hGb hCsupp
  have hIntKchi : MeasureTheory.Integrable (Function.uncurry (fun w y : E3 =>
      chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * pairG23 p Θ A B w y)) (volume : Measure (E3 × E3)) :=
    chiImBlk_pair_integrable hℓ hWi hGm.aestronglyMeasurable hGb hCsupp
  have hIntK' : MeasureTheory.Integrable (Function.uncurry (fun w y : E3 =>
      (K1lim ℓ W' w y - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y) * pairG23 p Θ A B w y))
      (volume : Measure (E3 × E3)) :=
    imgSub_congr_pt (hIntK.sub hIntKchi) (fun q => by
      show K1lim ℓ W' q.1 q.2 * pairG23 p Θ A B q.1 q.2
          - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) q.1 q.2 * pairG23 p Θ A B q.1 q.2
        = (K1lim ℓ W' q.1 q.2 - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) q.1 q.2) * pairG23 p Θ A B q.1 q.2
      ring)
  obtain ⟨hφb, hφs⟩ := phi23_bound_support p hp hΘs hΘb hAb hBb
  have hφm : Measurable (phi23 p Θ A B) := phi23_measurable p hΘm hAm hBm
  have hInt1 : MeasureTheory.Integrable (fun x : Xn n => K1lim ℓ W' (x p.1) (x p.2)
      * (∫ y : E3, ∫ u : E3, star (Θ x) * star (A y) * star (B u)
          * Θ (Function.update (Function.update x p.1 y) p.2 u)))
      (volume : Measure (Xn n)) :=
    K1lim_mul_integrable_pair (F := phi23 p Θ A B) hℓ p hp hW'i hφm.aestronglyMeasurable hφb hφs
  have hInt1chi : MeasureTheory.Integrable (fun x : Xn n => chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (x p.1) (x p.2)
      * (∫ y : E3, ∫ u : E3, star (Θ x) * star (A y) * star (B u)
          * Θ (Function.update (Function.update x p.1 y) p.2 u)))
      (volume : Measure (Xn n)) :=
    imgPairSlots_integrable (F := phi23 p Θ A B) hℓ p hp hWi hφm.aestronglyMeasurable hφb hφs
  have hInt1' : MeasureTheory.Integrable (fun x : Xn n =>
      (K1lim ℓ W' (x p.1) (x p.2) - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (x p.1) (x p.2))
        * (∫ y : E3, ∫ u : E3, star (Θ x) * star (A y) * star (B u)
            * Θ (Function.update (Function.update x p.1 y) p.2 u)))
      (volume : Measure (Xn n)) :=
    imgSub_congr_pt (hInt1.sub hInt1chi) (fun x => by
      show K1lim ℓ W' (x p.1) (x p.2)
            * (∫ y : E3, ∫ u : E3, star (Θ x) * star (A y) * star (B u)
                * Θ (Function.update (Function.update x p.1 y) p.2 u))
          - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (x p.1) (x p.2)
            * (∫ y : E3, ∫ u : E3, star (Θ x) * star (A y) * star (B u)
                * Θ (Function.update (Function.update x p.1 y) p.2 u))
        = (K1lim ℓ W' (x p.1) (x p.2) - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (x p.1) (x p.2))
            * (∫ y : E3, ∫ u : E3, star (Θ x) * star (A y) * star (B u)
                * Θ (Function.update (Function.update x p.1 y) p.2 u))
      ring)
  exact blockTwo3_KsubDir (K := K1lim ℓ W')
    (K' := fun w y => K1lim ℓ W' w y - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y)
    p hp hℓ hε hCsupp hPair' hbs hIntK hIntK' hInt1 hInt1'

/-- **Block II.1, `a.e.` form.**  The same statement for the block-II.1 shape (both kernel
arguments free) and the fibre `pairG21`; here the Fubini chain of `blockII1_KsubDir` needs six
integrability facts at each of the two kernels. -/
theorem rowImg_blockII1 {n : ℕ} {ℓ ε : ℝ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (hℓ : 0 < ℓ)
    {Θ Θ₀ : Xn n → ℂ} {A : E3 → ℂ} {W W' : E3 → ℝ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (hΘind : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x)
    (hAm : Measurable A) (hAb : ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C)
    (hCutA : CutSmooth1 ℓ A)
    (hW'i : MeasureTheory.Integrable W') (hWi : MeasureTheory.Integrable W) (hε : 0 ≤ ε)
    (hPair : ∀ G : E3 → E3 → ℂ, BoxSmooth ℓ G →
      ‖∫ w in boxL ℓ, ∫ y in boxL ℓ,
          chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y‖
        ≤ ε * (Real.sqrt (L1Tails.pairEnergy ℓ G) + Real.sqrt (massBox ℓ G))) :
    ‖rowShape21 Θ A (K1lim ℓ W') p
      - rowShape21 Θ A (fun w y => K1lim ℓ W' w y
          - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y) p‖
      ≤ ε * (Real.sqrt (L1Tails.pairEnergy ℓ (pairG21 p Θ A))
          + Real.sqrt (massBox ℓ (pairG21 p Θ A))) := by
  classical
  have hPm : Measurable (Function.uncurry (pairG21 p Θ A)) := pairG21_measurable p hΘm hAm
  have hPb : ∃ C : ℝ, ∀ u y : E3, ‖pairG21 p Θ A u y‖ ≤ C := pairG21_bounded p hΘb hΘs hAb
  have hCsupp : Function.support (Function.uncurry (pairG21 p Θ A)) ⊆
      Set.prod (boxL ℓ) (boxL ℓ) :=
    (pairG_supports p hp (A := A) (B := A) hΘs).2.2
  have hbs : BoxSmooth ℓ (pairG21 p Θ A) :=
    (boxSmooth_fibres hℓ p hp ⟨Θ₀, hΘ₀, hΘind⟩ (A := A) (B := A) hCutA hCutA).2.2
  have hPair' : ∀ G : E3 → E3 → ℂ, BoxSmooth ℓ G →
      ‖∫ w in boxL ℓ, ∫ y in boxL ℓ,
          (K1lim ℓ W' w y - (fun w y => K1lim ℓ W' w y - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y) w y) * G w y‖
        ≤ ε * (Real.sqrt (L1Tails.pairEnergy ℓ G) + Real.sqrt (massBox ℓ G)) := by
    intro G hG
    have hcongr : (∫ w in boxL ℓ, ∫ y in boxL ℓ,
          (K1lim ℓ W' w y - (fun w y => K1lim ℓ W' w y - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y) w y) * G w y)
        = ∫ w in boxL ℓ, ∫ y in boxL ℓ, chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y := by
      refine MeasureTheory.setIntegral_congr_fun
        (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ) (fun w hw => ?_)
      refine MeasureTheory.setIntegral_congr_fun
        (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ) (fun y hy => ?_)
      ring
    rw [hcongr]
    exact hPair G hG
  -- the two bounds on the state factors
  obtain ⟨CT, hCT⟩ := hΘb
  obtain ⟨CA, hCA⟩ := hAb
  have hCT0 : (0 : ℝ) ≤ CT := le_trans (norm_nonneg _) (hCT 0)
  have hCA0 : (0 : ℝ) ≤ CA := le_trans (norm_nonneg _) (hCA 0)
  have hbnd : ∀ (x : Xn n) (y u : E3), ‖star (Θ x) * A (x p.1) * A (x p.2)
      * Θ (Function.update (Function.update x p.1 y) p.2 u)‖ ≤ CT * CA * CA * CT := by
    intro x y u
    have h1 : ‖Θ x‖ ≤ CT := hCT x
    have h2 : ‖A (x p.1)‖ ≤ CA := hCA _
    have h3 : ‖A (x p.2)‖ ≤ CA := hCA _
    have h4 : ‖Θ (Function.update (Function.update x p.1 y) p.2 u)‖ ≤ CT := hCT _
    rw [norm_mul, norm_mul, norm_mul, norm_star]
    exact mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hCT0) h3 (norm_nonneg _)
      (mul_nonneg hCT0 hCA0)) h4 (norm_nonneg _) (mul_nonneg (mul_nonneg hCT0 hCA0) hCA0)
  -- the two joint state functionals of the Fubini chain, with their support
  have hfacm : Measurable (fun w : Xn n × (E3 × E3) => star (Θ w.1) * A (w.1 p.1)
      * A (w.1 p.2) * Θ (Function.update (Function.update w.1 p.1 w.2.1) p.2 w.2.2)) := by
    fun_prop
  have hfacb : ∃ C : ℝ, ∀ w : Xn n × (E3 × E3), ‖star (Θ w.1) * A (w.1 p.1)
      * A (w.1 p.2) * Θ (Function.update (Function.update w.1 p.1 w.2.1) p.2 w.2.2)‖ ≤ C :=
    ⟨CT * CA * CA * CT, fun w => hbnd w.1 w.2.1 w.2.2⟩
  have hfacs : Function.support (fun w : Xn n × (E3 × E3) => star (Θ w.1) * A (w.1 p.1)
      * A (w.1 p.2) * Θ (Function.update (Function.update w.1 p.1 w.2.1) p.2 w.2.2))
      ⊆ Set.prod (Work.MB.boxPow n ℓ) (Set.prod (boxL ℓ) (boxL ℓ)) := by
    intro w hw
    rw [Function.mem_support] at hw
    refine ⟨?_, ?_, ?_⟩
    · by_contra hx
      refine hw ?_
      have h0 : Θ w.1 = 0 := by
        by_contra h
        exact hx (hΘs (Function.mem_support.mpr h))
      simp [h0]
    · by_contra hy
      refine hw ?_
      have h0 : Θ (Function.update (Function.update w.1 p.1 w.2.1) p.2 w.2.2) = 0 :=
        theta_eq_zero_of_coord_notMem hΘs (j := p.1) (by rw [imgUpd_fst hp]; exact hy)
      simp [h0]
    · by_contra hu
      refine hw ?_
      have h0 : Θ (Function.update (Function.update w.1 p.1 w.2.1) p.2 w.2.2) = 0 :=
        theta_eq_zero_of_coord_notMem hΘs (j := p.2) (by rw [imgUpd_snd]; exact hu)
      simp [h0]
  have hfacm' : Measurable (fun w : Xn n × (E3 × E3) => star (Θ w.1) * A (w.1 p.1)
      * A (w.1 p.2) * Θ (Function.update (Function.update w.1 p.1 w.2.2) p.2 w.2.1)) := by
    fun_prop
  have hfacb' : ∃ C : ℝ, ∀ w : Xn n × (E3 × E3), ‖star (Θ w.1) * A (w.1 p.1)
      * A (w.1 p.2) * Θ (Function.update (Function.update w.1 p.1 w.2.2) p.2 w.2.1)‖ ≤ C :=
    ⟨CT * CA * CA * CT, fun w => hbnd w.1 w.2.2 w.2.1⟩
  have hfacs' : Function.support (fun w : Xn n × (E3 × E3) => star (Θ w.1) * A (w.1 p.1)
      * A (w.1 p.2) * Θ (Function.update (Function.update w.1 p.1 w.2.2) p.2 w.2.1))
      ⊆ Set.prod (Work.MB.boxPow n ℓ) (Set.prod (boxL ℓ) (boxL ℓ)) := by
    intro w hw
    rw [Function.mem_support] at hw
    refine ⟨?_, ?_, ?_⟩
    · by_contra hx
      refine hw ?_
      have h0 : Θ w.1 = 0 := by
        by_contra h
        exact hx (hΘs (Function.mem_support.mpr h))
      simp [h0]
    · by_contra hy
      refine hw ?_
      have h0 : Θ (Function.update (Function.update w.1 p.1 w.2.2) p.2 w.2.1) = 0 :=
        theta_eq_zero_of_coord_notMem hΘs (j := p.2) (by rw [imgUpd_snd]; exact hy)
      simp [h0]
    · by_contra hu
      refine hw ?_
      have h0 : Θ (Function.update (Function.update w.1 p.1 w.2.2) p.2 w.2.1) = 0 :=
        theta_eq_zero_of_coord_notMem hΘs (j := p.1) (by rw [imgUpd_fst hp]; exact hu)
      simp [h0]
  -- the six integrability facts for the image kernel
  have hchi_int : MeasureTheory.Integrable (Function.uncurry (fun w y : E3 =>
      chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * pairG21 p Θ A w y)) (volume : Measure (E3 × E3)) :=
    chiImBlk_pair_integrable hℓ hWi hPm.aestronglyMeasurable hPb hCsupp
  have hchi_x : ∀ x : Xn n, MeasureTheory.Integrable (Function.uncurry (fun y u : E3 =>
      chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) u y * (star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 y) p.2 u))))
      (volume : Measure (E3 × E3)) := by
    intro x
    refine chiImBlk_pair_integrable_swap (G := fun y u : E3 => star (Θ x) * A (x p.1)
      * A (x p.2) * Θ (Function.update (Function.update x p.1 y) p.2 u))
      hℓ hWi ?_ ⟨CT * CA * CA * CT, fun y u => hbnd x y u⟩ ?_
    · exact (by fun_prop : Measurable (Function.uncurry (fun y u : E3 =>
        star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 y) p.2 u)))).aestronglyMeasurable
    · intro q hq
      rw [Function.mem_support] at hq
      refine ⟨?_, ?_⟩
      · by_contra hy
        refine hq ?_
        have h0 : Θ (Function.update (Function.update x p.1 q.1) p.2 q.2) = 0 :=
          theta_eq_zero_of_coord_notMem hΘs (j := p.1) (by rw [imgUpd_fst hp]; exact hy)
        show star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 q.1) p.2 q.2) = 0
        rw [h0, mul_zero]
      · by_contra hu
        refine hq ?_
        have h0 : Θ (Function.update (Function.update x p.1 q.1) p.2 q.2) = 0 :=
          theta_eq_zero_of_coord_notMem hΘs (j := p.2) (by rw [imgUpd_snd]; exact hu)
        show star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 q.1) p.2 q.2) = 0
        rw [h0, mul_zero]
  have hchi_swap : MeasureTheory.Integrable (Function.uncurry (fun x : Xn n =>
      fun z : E3 × E3 => chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) z.2 z.1 * (star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 z.1) p.2 z.2))))
      (volume : Measure (Xn n × (E3 × E3))) :=
    chiChiImages_mul_integrable_swapJoint (H := fun w : Xn n × (E3 × E3) =>
      star (Θ w.1) * A (w.1 p.1) * A (w.1 p.2)
        * Θ (Function.update (Function.update w.1 p.1 w.2.1) p.2 w.2.2))
      hℓ hWi hfacm.aestronglyMeasurable hfacb hfacs
  have hchi_prod : MeasureTheory.Integrable (fun z : E3 × E3 => ∫ x : Xn n,
      chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) z.1 z.2 * (star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1)))
      (volume : Measure (E3 × E3)) :=
    chiChiImages_mul_integrable_prod (H := fun w : Xn n × (E3 × E3) =>
      star (Θ w.1) * A (w.1 p.1) * A (w.1 p.2)
        * Θ (Function.update (Function.update w.1 p.1 w.2.2) p.2 w.2.1))
      hℓ hWi hfacm'.aestronglyMeasurable hfacb' hfacs'
  -- the six integrability facts for `K1lim ℓ W'`
  have hK_int : MeasureTheory.Integrable (Function.uncurry (fun w y : E3 =>
      K1lim ℓ W' w y * pairG21 p Θ A w y)) (volume : Measure (E3 × E3)) :=
    K1lim_mul_integrable (G := pairG21 p Θ A) hℓ hW'i hPm.aestronglyMeasurable hPb hCsupp
  have hK_x : ∀ x : Xn n, MeasureTheory.Integrable (Function.uncurry (fun y u : E3 =>
      K1lim ℓ W' u y * (star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 y) p.2 u))))
      (volume : Measure (E3 × E3)) := by
    intro x
    refine K1lim_mul_integrable_swap (G := fun y u : E3 => star (Θ x) * A (x p.1)
      * A (x p.2) * Θ (Function.update (Function.update x p.1 y) p.2 u))
      hℓ hW'i ?_ ⟨CT * CA * CA * CT, fun y u => hbnd x y u⟩ ?_
    · exact (by fun_prop : Measurable (Function.uncurry (fun y u : E3 =>
        star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 y) p.2 u)))).aestronglyMeasurable
    · intro q hq
      rw [Function.mem_support] at hq
      refine ⟨?_, ?_⟩
      · by_contra hy
        refine hq ?_
        have h0 : Θ (Function.update (Function.update x p.1 q.1) p.2 q.2) = 0 :=
          theta_eq_zero_of_coord_notMem hΘs (j := p.1) (by rw [imgUpd_fst hp]; exact hy)
        show star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 q.1) p.2 q.2) = 0
        rw [h0, mul_zero]
      · by_contra hu
        refine hq ?_
        have h0 : Θ (Function.update (Function.update x p.1 q.1) p.2 q.2) = 0 :=
          theta_eq_zero_of_coord_notMem hΘs (j := p.2) (by rw [imgUpd_snd]; exact hu)
        show star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 q.1) p.2 q.2) = 0
        rw [h0, mul_zero]
  have hK_swap : MeasureTheory.Integrable (Function.uncurry (fun x : Xn n =>
      fun z : E3 × E3 => K1lim ℓ W' z.2 z.1 * (star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 z.1) p.2 z.2))))
      (volume : Measure (Xn n × (E3 × E3))) :=
    K1lim_mul_integrable_swapJoint (H := fun w : Xn n × (E3 × E3) =>
      star (Θ w.1) * A (w.1 p.1) * A (w.1 p.2)
        * Θ (Function.update (Function.update w.1 p.1 w.2.1) p.2 w.2.2))
      hℓ hW'i hfacm.aestronglyMeasurable hfacb hfacs
  have hK_prod : MeasureTheory.Integrable (fun z : E3 × E3 => ∫ x : Xn n,
      K1lim ℓ W' z.1 z.2 * (star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1)))
      (volume : Measure (E3 × E3)) :=
    K1lim_mul_integrable_prod (H := fun w : Xn n × (E3 × E3) =>
      star (Θ w.1) * A (w.1 p.1) * A (w.1 p.2)
        * Θ (Function.update (Function.update w.1 p.1 w.2.2) p.2 w.2.1))
      hℓ hW'i hfacm'.aestronglyMeasurable hfacb' hfacs'
  -- the same six facts for the difference kernel `K1lim ℓ W' − χχW`
  have hK'_int : MeasureTheory.Integrable (Function.uncurry (fun w y : E3 =>
      (K1lim ℓ W' w y - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y) * pairG21 p Θ A w y))
      (volume : Measure (E3 × E3)) :=
    imgSub_congr_pt (hK_int.sub hchi_int) (fun q => by
      show K1lim ℓ W' q.1 q.2 * pairG21 p Θ A q.1 q.2
          - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) q.1 q.2 * pairG21 p Θ A q.1 q.2
        = (K1lim ℓ W' q.1 q.2 - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) q.1 q.2) * pairG21 p Θ A q.1 q.2
      ring)
  have hK'_x : ∀ x : Xn n, MeasureTheory.Integrable (Function.uncurry (fun y u : E3 =>
      (K1lim ℓ W' u y - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) u y) * (star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 y) p.2 u))))
      (volume : Measure (E3 × E3)) := by
    intro x
    refine imgSub_congr_pt ((hK_x x).sub (hchi_x x)) (fun q => ?_)
    show K1lim ℓ W' q.2 q.1 * (star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 q.1) p.2 q.2))
        - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) q.2 q.1 * (star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 q.1) p.2 q.2))
      = (K1lim ℓ W' q.2 q.1 - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) q.2 q.1)
        * (star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 q.1) p.2 q.2))
    ring
  have hK'_swap : MeasureTheory.Integrable (Function.uncurry (fun x : Xn n =>
      fun z : E3 × E3 => (K1lim ℓ W' z.2 z.1 - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) z.2 z.1)
        * (star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 z.1) p.2 z.2))))
      (volume : Measure (Xn n × (E3 × E3))) :=
    imgSub_congr_pt (hK_swap.sub hchi_swap) (fun q => by
      show K1lim ℓ W' q.2.2 q.2.1 * (star (Θ q.1) * A (q.1 p.1) * A (q.1 p.2)
              * Θ (Function.update (Function.update q.1 p.1 q.2.1) p.2 q.2.2))
          - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) q.2.2 q.2.1 * (star (Θ q.1) * A (q.1 p.1) * A (q.1 p.2)
              * Θ (Function.update (Function.update q.1 p.1 q.2.1) p.2 q.2.2))
        = (K1lim ℓ W' q.2.2 q.2.1 - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) q.2.2 q.2.1)
          * (star (Θ q.1) * A (q.1 p.1) * A (q.1 p.2)
              * Θ (Function.update (Function.update q.1 p.1 q.2.1) p.2 q.2.2))
      ring)
  have hK_prod_mul : MeasureTheory.Integrable (fun z : E3 × E3 => K1lim ℓ W' z.1 z.2 *
      (∫ x : Xn n, star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1)))
      (volume : Measure (E3 × E3)) :=
    imgSub_congr_pt hK_prod (fun z => MeasureTheory.integral_const_mul _ _)
  have hchi_prod_mul : MeasureTheory.Integrable (fun z : E3 × E3 => chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) z.1 z.2 *
      (∫ x : Xn n, star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1)))
      (volume : Measure (E3 × E3)) :=
    imgSub_congr_pt hchi_prod (fun z => MeasureTheory.integral_const_mul _ _)
  have hK'_prod : MeasureTheory.Integrable (fun z : E3 × E3 => ∫ x : Xn n,
      (K1lim ℓ W' z.1 z.2 - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) z.1 z.2) * (star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1)))
      (volume : Measure (E3 × E3)) := by
    have hmain : MeasureTheory.Integrable (fun z : E3 × E3 =>
        (K1lim ℓ W' z.1 z.2 - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) z.1 z.2) *
          (∫ x : Xn n, star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1)))
        (volume : Measure (E3 × E3)) :=
      imgSub_congr_pt (hK_prod_mul.sub hchi_prod_mul) (fun z => by
        show K1lim ℓ W' z.1 z.2 * (∫ x : Xn n, star (Θ x) * A (x p.1) * A (x p.2)
                * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1))
            - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) z.1 z.2 * (∫ x : Xn n, star (Θ x) * A (x p.1) * A (x p.2)
                * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1))
          = (K1lim ℓ W' z.1 z.2 - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) z.1 z.2)
            * (∫ x : Xn n, star (Θ x) * A (x p.1) * A (x p.2)
                * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1))
        ring)
    exact imgSub_congr_pt hmain (fun z => (MeasureTheory.integral_const_mul _ _).symm)
  exact blockII1_KsubDir (K := K1lim ℓ W') (K' := fun w y => K1lim ℓ W' w y - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y)
    p hp hℓ hε hCsupp hPair' hbs hK_int hK'_int hK_x hK'_x hK_swap hK'_swap hK_prod hK'_prod

/-! ## 2. The row-level assembly -/

theorem rowPairSubC_img_ae {n : ℕ} {ℓ a ε : ℝ} {Θ : Work.BoseDict.Xn n → ℂ}
    {A : EuclideanSpace ℝ (Fin 3) → ℂ} {Θ₀ : Work.BoseDict.Xn n → ℂ}
    {W₁ W₂ W₁' W₂' : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hℓ : 0 < ℓ) (hε : 0 ≤ ε)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (hΘind : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hΘL : MeasureTheory.Integrable (fun x => ‖Θ x‖ ^ 2))
    (hAm : Measurable A) (hAb : ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C)
    (hAL : MeasureTheory.Integrable (fun x => ‖A x‖ ^ 2))
    (hCutA : Work.BoseBoxFock.CutSmooth1 ℓ A)
    (hW₁'i : MeasureTheory.Integrable W₁')
    (hW₂'i : MeasureTheory.Integrable W₂')
    (hW₁i : MeasureTheory.Integrable W₁)
    (hW₂i : MeasureTheory.Integrable W₂)
    (hPairI : ∀ G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ,
      Work.BoseBoxFock.BoxSmooth ℓ G →
      ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W₁ z : ℝ) : ℂ)) w y * G w y‖
        ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ G)
            + Real.sqrt (Work.BoseBoxFock.massBox ℓ G)))
    (hPairII : ∀ G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ,
      Work.BoseBoxFock.BoxSmooth ℓ G →
      ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W₂ z : ℝ) : ℂ)) w y * G w y‖
        ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ G)
            + Real.sqrt (Work.BoseBoxFock.massBox ℓ G))) :
    ‖Work.BoseBoxFock.rowPairSubC a Θ A (Work.BoseBoxFock.K1lim ℓ W₁') (Work.BoseBoxFock.K1lim ℓ W₂')
        - Work.BoseBoxFock.rowPairSubC a Θ A
            (fun w y => Work.BoseBoxFock.K1lim ℓ W₁' w y
              - Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W₁ z : ℝ) : ℂ)) w y)
            (fun w y => Work.BoseBoxFock.K1lim ℓ W₂' w y
              - Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W₂ z : ℝ) : ℂ)) w y)‖
      ≤ 2 * |a| * ε * ∑ p ∈ Submission.BoseGases.pairSet n,
          ((Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (Work.BoseBoxFock.pairG13 p Θ A A))
              + Real.sqrt (Work.BoseBoxFock.massBox ℓ (Work.BoseBoxFock.pairG13 p Θ A A)))
            + (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (Work.BoseBoxFock.pairG21 p Θ A))
              + Real.sqrt (Work.BoseBoxFock.massBox ℓ (Work.BoseBoxFock.pairG21 p Θ A)))
            + (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (Work.BoseBoxFock.pairG23 p Θ A A))
              + Real.sqrt (Work.BoseBoxFock.massBox ℓ (Work.BoseBoxFock.pairG23 p Θ A A)))) := by
  refine rowPairSubC_KsubDir (n := n) (ℓ := ℓ) (ε := ε) (a := a) (Θ := Θ) (A := A)
    (KI := K1lim ℓ W₁')
    (KI' := fun w y => K1lim ℓ W₁' w y
      - chiChiImages ℓ (fun z => ((W₁ z : ℝ) : ℂ)) w y)
    (KII := K1lim ℓ W₂')
    (KII' := fun w y => K1lim ℓ W₂' w y
      - chiChiImages ℓ (fun z => ((W₂ z : ℝ) : ℂ)) w y)
    hε ?_ ?_ ?_
  · intro p hp
    exact rowImg_block13 p (mem_pairSet_iff.mp hp) hℓ hΘm hΘb hΘs hΘ₀ hΘind hAm hAb hAm hAb
      hCutA hCutA hW₁'i hW₁i hε hPairI
  · intro p hp
    exact rowImg_blockII1 p (mem_pairSet_iff.mp hp) hℓ hΘm hΘb hΘs hΘ₀ hΘind hAm hAb
      hCutA hW₂'i hW₂i hε hPairII
  · intro p hp
    exact rowImg_blockTwo3 p (mem_pairSet_iff.mp hp) hℓ hΘm hΘb hΘs hΘ₀ hΘind hAm hAb hAm hAb
      hCutA hCutA hW₂'i hW₂i hε hPairII

end Work.BoseBoxFock
