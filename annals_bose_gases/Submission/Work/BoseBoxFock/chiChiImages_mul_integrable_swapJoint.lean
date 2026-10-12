import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiImages_block_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiChiImages_mul_integrable_swapJoint`

The `χχ`-images kernel `chiChiImages ℓ ↑W` taken with the two free position variables **swapped**
against a bounded, box-supported kernel `H` on the `n`-particle space `Xn n × (ℝ³ × ℝ³)`:

    `z ↦ chiChiImages ℓ ↑W z.2.2 z.2.1 * H z`.

This is the joint (two free position slots) analogue of `chiImages_mul_integrable` and the
`chiChiImages` twin of `K1lim_mul_integrable_swapJoint`; the weight `W` is only *integrable*.

## Route

* **Pointwise bound.**  `H` vanishes unless `z.1 ∈ boxPow n ℓ` and `z.2 ∈ boxL ℓ × boxL ℓ`
  (`hHs`), so on the latter region
  `‖ker(z.2.2, z.2.1) * H z‖ₑ ≤ C · 1_{boxPow}(z.1) · ‖ker‖ₑ(z.2.swap)`; the kernel factor is kept
  as is (no periodisation loss).
* **A.e. strong measurability.**  `chiImBlk_aesm_swap` gives a.e. strong measurability of the
  swapped kernel on the pair space, and the projection onto `z.2` is quasi-measure-preserving.
* **Finiteness.**  The majorant factorises over the product measure
  (`MeasureTheory.lintegral_prod_mul`), the `boxPow` factor has finite measure
  (`Work.MB.volume_boxPow_lt_top`), and the pair factor is finite by
  `chiImBlk_pair_lintegral_swap_lt_top`, which reduces (via the measure-preserving swap of the two
  coordinates and `prod_indicator_eq`) to `chiImBlk_pair_lintegral_lt_top`.

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
set_option linter.unusedVariables false

/-- **Finiteness of the swapped kernel over the box squared.**  The `ℝ≥0∞`-integral of the
`χχ`-images kernel with its two arguments transposed, restricted to the box squared, is finite for
an integrable weight.  (Reduced to `chiImBlk_pair_lintegral_lt_top` by the measure-preserving swap,
which leaves `boxL ℓ ×ˢ boxL ℓ` invariant.) -/
theorem chiImBlk_pair_lintegral_swap_lt_top {ℓ : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWi : MeasureTheory.Integrable W) :
    (∫⁻ p : E3 × E3, (boxL ℓ ×ˢ boxL ℓ).indicator
        (fun p : E3 × E3 => ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.2 p.1‖ₑ) p) < ⊤ := by
  have hswap := MeasureTheory.lintegral_prod_swap (μ := (volume : Measure E3))
      (ν := (volume : Measure E3))
      (f := (boxL ℓ ×ˢ boxL ℓ).indicator
        (fun q : E3 × E3 => ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) q.1 q.2‖ₑ))
  calc ∫⁻ p : E3 × E3, (boxL ℓ ×ˢ boxL ℓ).indicator
        (fun p : E3 × E3 => ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.2 p.1‖ₑ) p
      = ∫⁻ p : E3 × E3, (boxL ℓ ×ˢ boxL ℓ).indicator
        (fun q : E3 × E3 => ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) q.1 q.2‖ₑ) p.swap := by
        refine lintegral_congr (fun p => ?_)
        by_cases hp : p ∈ boxL ℓ ×ˢ boxL ℓ
        · have hp' : p.swap ∈ boxL ℓ ×ˢ boxL ℓ := by
            obtain ⟨h1, h2⟩ := Set.mem_prod.mp hp
            exact Set.mem_prod.mpr ⟨h2, h1⟩
          rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp']
          rfl
        · have hp' : p.swap ∉ boxL ℓ ×ˢ boxL ℓ := by
            intro h
            refine hp ?_
            obtain ⟨h1, h2⟩ := Set.mem_prod.mp h
            exact Set.mem_prod.mpr ⟨h2, h1⟩
          rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp']
    _ = ∫⁻ p : E3 × E3, (boxL ℓ ×ˢ boxL ℓ).indicator
        (fun q : E3 × E3 => ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) q.1 q.2‖ₑ) p := hswap
    _ = ∫⁻ p : E3 × E3, (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.1
          * (boxL ℓ).indicator (fun _ => (1 : ENNReal)) p.2
          * ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.1 p.2‖ₑ := by
        refine lintegral_congr (fun p => ?_)
        rw [prod_indicator_eq (boxL ℓ) (boxL ℓ)
          (fun a b => ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) a b‖ₑ) p]
    _ < ⊤ := chiImBlk_pair_lintegral_lt_top hℓ hWi

theorem chiChiImages_mul_integrable_swapJoint {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWi : MeasureTheory.Integrable W)
    {H : Work.BoseDict.Xn n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) → ℂ}
    (hHm : MeasureTheory.AEStronglyMeasurable H MeasureTheory.volume)
    (hHb : ∃ C : ℝ, ∀ z, ‖H z‖ ≤ C)
    (hHs : Function.support H ⊆ Set.prod (Work.MB.boxPow n ℓ)
      (Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ))) :
    MeasureTheory.Integrable
      (fun z : Work.BoseDict.Xn n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
        Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) z.2.2 z.2.1 * H z)
      (MeasureTheory.volume : MeasureTheory.Measure
        (Work.BoseDict.Xn n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))) := by
  obtain ⟨C₀, hC₀⟩ := hHb
  set C' : ENNReal := ENNReal.ofReal (max C₀ 0) with hC'def
  have hC'ne : C' ≠ ⊤ := by rw [hC'def]; exact ENNReal.ofReal_ne_top
  have hBlm : MeasurableSet (boxL ℓ ×ˢ boxL ℓ) :=
    (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ).prod
      (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ)
  -- the bound of `H` by the `boxPow` indicator
  have hHbd : ∀ z : Xn n × (E3 × E3),
      ‖H z‖ₑ ≤ C' * ((Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) z.1) := by
    intro z
    by_cases hz : z.1 ∈ Work.MB.boxPow n ℓ
    · rw [Set.indicator_of_mem hz, mul_one, hC'def, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (le_trans (hC₀ z) (le_max_left C₀ 0))
    · have hz0 : H z = 0 := by
        by_contra hne
        exact hz (Set.mem_prod.mp (hHs (Function.mem_support.mpr hne))).1
      rw [hz0, enorm_zero]
      exact bot_le
  -- the pointwise bound of the whole integrand
  have hfpt : ∀ z : Xn n × (E3 × E3),
      ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) z.2.2 z.2.1 * H z‖ₑ ≤
        C' * ((Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) z.1 *
          (boxL ℓ ×ˢ boxL ℓ).indicator
            (fun p : E3 × E3 => ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.2 p.1‖ₑ) z.2) := by
    intro z
    rw [enorm_mul]
    by_cases hz : z.2 ∈ boxL ℓ ×ˢ boxL ℓ
    · rw [Set.indicator_of_mem hz]
      calc ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) z.2.2 z.2.1‖ₑ * ‖H z‖ₑ
          ≤ ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) z.2.2 z.2.1‖ₑ
              * (C' * ((Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) z.1)) :=
            mul_le_mul_of_nonneg_left (hHbd z) (by simp)
        _ = C' * ((Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) z.1 *
              ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) z.2.2 z.2.1‖ₑ) := by ring
    · have hz0 : H z = 0 := by
        by_contra hne
        exact hz (Set.mem_prod.mp (hHs (Function.mem_support.mpr hne))).2
      rw [hz0, Set.indicator_of_notMem hz]
      simp
  -- finiteness of the two factors of the majorant
  have hXfin : (∫⁻ x : Xn n, (Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) x) < ⊤ := by
    rw [MeasureTheory.lintegral_indicator (Work.MB.measurableSet_boxPow n ℓ)
        (fun _ => (1 : ENNReal)),
      MeasureTheory.setLIntegral_one]
    exact lt_top_iff_ne_top.mpr (Work.MB.volume_boxPow_lt_top n ℓ)
  have hΨfin : (∫⁻ p : E3 × E3, (boxL ℓ ×ˢ boxL ℓ).indicator
      (fun p : E3 × E3 => ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.2 p.1‖ₑ) p) < ⊤ :=
    chiImBlk_pair_lintegral_swap_lt_top hℓ hWi
  -- a.e. measurability of the two factors of the majorant
  have hfX : AEMeasurable (fun x : Xn n =>
      (Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) x) (volume : Measure (Xn n)) :=
    (measurable_const.indicator (Work.MB.measurableSet_boxPow n ℓ)).aemeasurable
  have hfΨ : AEMeasurable (fun p : E3 × E3 =>
      (boxL ℓ ×ˢ boxL ℓ).indicator
        (fun p : E3 × E3 => ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.2 p.1‖ₑ) p)
      (volume : Measure (E3 × E3)) :=
    ((chiImBlk_aesm_swap (ℓ := ℓ) hWi.aestronglyMeasurable).enorm).indicator hBlm
  refine ⟨?_, ?_⟩
  · -- a.e. strong measurability: the swapped kernel composed with the projection onto the pair
    exact ((chiImBlk_aesm_swap (ℓ := ℓ) hWi.aestronglyMeasurable).comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd).mul hHm
  · refine lt_of_le_of_lt (lintegral_mono hfpt) ?_
    rw [show (MeasureTheory.volume : MeasureTheory.Measure (Xn n × (E3 × E3)))
        = (MeasureTheory.volume : MeasureTheory.Measure (Xn n)).prod
          (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) from rfl]
    rw [MeasureTheory.lintegral_const_mul' C' _ hC'ne]
    rw [MeasureTheory.lintegral_prod_mul (μ := (volume : Measure (Xn n)))
      (ν := (volume : Measure (E3 × E3)))
      (f := fun x : Xn n => (Work.MB.boxPow n ℓ).indicator (fun _ => (1 : ENNReal)) x)
      (g := fun p : E3 × E3 => (boxL ℓ ×ˢ boxL ℓ).indicator
        (fun p : E3 × E3 => ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.2 p.1‖ₑ) p)
      hfX hfΨ]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC'ne)
      (ENNReal.mul_lt_top hXfin hΨfin)

end Work.BoseBoxFock
