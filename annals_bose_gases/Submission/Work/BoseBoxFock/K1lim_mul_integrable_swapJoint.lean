import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.K1lim_mul_integrable
import Submission.Work.BoseBoxFock.K1lim_mul_integrable_slot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1lim_mul_integrable_swapJoint`

The limit pair kernel `K1lim ℓ W` (`pinQLimDefs`) taken with the two position slots **swapped**
against a bounded, box-supported kernel `H` on the `n`-particle space `Xn n × (ℝ³ × ℝ³)`:

    `(z.1 : Xn n, z.2.1, z.2.2) ↦ K1lim ℓ W z.2.2 z.2.1 * H z`.

The weight `W` is only *integrable* (no boundedness, no compact support), `H` is a.e. strongly
measurable, everywhere bounded and supported in `boxPow n ℓ × (boxL ℓ × boxL ℓ)` (the two
"position" slots live in the one-particle box `corpusBox.boxL ℓ`).

## Route

* **Measurability.** `aesm_uncurry_K1lim_of_integrable` gives a.e. strong measurability of the
  *unswapped* kernel; swapping the two arguments is a measure-preserving (hence
  quasi-measure-preserving) operation, and the projection onto the pair of position slots is
  quasi-measure-preserving (`Measure.quasiMeasurePreserving_snd`), so the composed kernel is
  a.e. strongly measurable.

* **Finiteness.** The three `χ̂`-rows of `K1lim` are *uniformly bounded* (`errBdd_pinQBl_bdd`
  etc.), and the `χχ`-row is bounded pointwise by the periodisation `k1PerEnorm ℓ W` of `‖W‖ₑ`
  (`k1enorm_mul_le`), so on the box

      `‖K1lim ℓ W w y‖ₑ ≤ K · 1_{boxL²}(w,y)·(k1PerEnorm ℓ W (w - y) + 1)`.

  `H` is bounded by `C` on `boxPow` and vanishes outside, so the integrand is dominated by a
  constant times `1_{boxPow}(z.1) · Ψ(z.2)` with
  `Ψ p = 1_{boxL²}(p.swap)·(k1PerEnorm ℓ W (p.2 - p.1) + 1)`.  The `≥0∞`-integral of that
  majorant factorises over the product measure (`MeasureTheory.lintegral_prod_mul`), the
  `boxPow` factor is finite by `Work.MB.volume_boxPow_lt_top`, and the pair factor is the
  (swapped) version of `k1lintegral_indicator_add_le`, which is finite because `W ∈ L¹`
  (the swap is `MeasureTheory.lintegral_prod_swap`).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

theorem K1lim_mul_integrable_swapJoint {n : ℕ} {l : ℝ} (hl : 0 < l)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWi : MeasureTheory.Integrable W)
    {H : Work.BoseDict.Xn n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) → ℂ}
    (hHm : MeasureTheory.AEStronglyMeasurable H MeasureTheory.volume)
    (hHb : ∃ C : ℝ, ∀ z, ‖H z‖ ≤ C)
    (hHs : Function.support H ⊆ Set.prod (Work.MB.boxPow n l)
      (Set.prod (Work.BoseK15.corpusBox.boxL l) (Work.BoseK15.corpusBox.boxL l))) :
    MeasureTheory.Integrable
      (fun z : Work.BoseDict.Xn n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
        Work.BoseBoxFock.K1lim l W z.2.2 z.2.1 * H z)
      (MeasureTheory.volume : MeasureTheory.Measure
        (Work.BoseDict.Xn n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))) := by
  have hWme : AEStronglyMeasurable W volume := hWi.aestronglyMeasurable
  obtain ⟨CB, hCB0, hCB⟩ := errBdd_pinQBl_bdd hl W
  obtain ⟨CC, hCC0, hCC⟩ := errBdd_pinQCl_bdd hl W
  obtain ⟨CD, hCD0, hCD⟩ := errBdd_pinQDl_bdd hl W
  set M : ℝ := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hMle : ∀ w : E3, ‖((Submission.BoseGases.chiScale l w : ℝ) : ℂ)‖ ≤ M := fun w => by
    rw [hMdef]; exact k1chiScale_norm_le l w
  -- the constant dominating the kernel
  set K : ENNReal := ENNReal.ofReal (1 : ℝ) * ‖(((l ^ 3)⁻¹ : ℝ) : ℂ)‖ₑ *
      (ENNReal.ofReal M * ENNReal.ofReal M * ‖(((l ^ 3 : ℝ)) : ℂ)‖ₑ
        + (ENNReal.ofReal M * ENNReal.ofReal CB + ENNReal.ofReal M * ENNReal.ofReal CC
            + ENNReal.ofReal CD)) with hKdef
  have hKne : K ≠ ⊤ := by
    rw [hKdef]
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top) ?_
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top) enorm_ne_top, ?_⟩
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top
      ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top⟩, ENNReal.ofReal_ne_top⟩
  have hBlm : MeasurableSet (Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l) :=
    (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox l).prod
      (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox l)
  -- pointwise bound of the kernel on the box
  have hKpt : ∀ w y : E3, (w, y) ∈ Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l →
      ‖K1lim l W w y‖ₑ ≤ K *
        ((Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l).indicator
          (fun p : E3 × E3 => k1PerEnorm l W (p.1 - p.2) + 1) (w, y)) := by
    intro w y hmem
    have hmain : ‖K1lim l W w y *
        ((Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l).indicator
          (fun _ : E3 × E3 => (1 : ℂ)) (w, y))‖ₑ ≤ K *
        ((Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l).indicator
          (fun p : E3 × E3 => k1PerEnorm l W (p.1 - p.2) + 1) (w, y)) := by
      rw [hKdef]
      exact k1enorm_mul_le (l := l) (W := W)
        (G := fun w y => (Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l).indicator
          (fun _ : E3 × E3 => (1 : ℂ)) (w, y))
        (by
          intro p hp
          by_contra h
          exact (Function.mem_support.mp hp) (by
            show (Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l).indicator
              (fun _ : E3 × E3 => (1 : ℂ)) (p.1, p.2) = 0
            exact Set.indicator_of_notMem h _))
        (Cg := 1) (M := M) (CB := CB) (CC := CC) (CD := CD) zero_le_one
        (by
          intro a b
          by_cases hab : (a, b) ∈ Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l
          · rw [Set.indicator_of_mem hab]; simp
          · rw [Set.indicator_of_notMem hab]; simp)
        hM0 hMle hCB0 hCB hCC0 hCC hCD0 hCD (w, y)
    rw [Set.indicator_of_mem hmem (fun _ : E3 × E3 => (1 : ℂ)), mul_one] at hmain
    exact hmain
  -- the bound of `H` by the box indicator
  obtain ⟨C₀, hC₀⟩ := hHb
  set C' : ENNReal := ENNReal.ofReal (max C₀ 0) with hC'def
  have hC'ne : C' ≠ ⊤ := by rw [hC'def]; exact ENNReal.ofReal_ne_top
  have hHbd : ∀ z : Work.BoseDict.Xn n × (E3 × E3),
      ‖H z‖ₑ ≤ C' * ((Work.MB.boxPow n l).indicator (fun _ => (1 : ENNReal)) z.1) := by
    intro z
    by_cases hz : z.1 ∈ Work.MB.boxPow n l
    · have h1 : ‖H z‖ₑ ≤ ENNReal.ofReal (max C₀ 0) := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (le_trans (hC₀ z) (le_max_left C₀ 0))
      rw [Set.indicator_of_mem hz (fun _ => (1 : ENNReal)), mul_one, hC'def]
      exact h1
    · have hz0 : H z = 0 := by
        by_contra hne
        exact hz (Set.mem_prod.mp (hHs (Function.mem_support.mpr hne))).1
      rw [hz0, enorm_zero]
      exact bot_le
  -- the pointwise bound of the whole integrand
  have hfpt : ∀ z : Work.BoseDict.Xn n × (E3 × E3),
      ‖K1lim l W z.2.2 z.2.1 * H z‖ₑ ≤ K * C' *
        ((Work.MB.boxPow n l).indicator (fun _ => (1 : ENNReal)) z.1 *
          (Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l).indicator
            (fun p : E3 × E3 => k1PerEnorm l W (p.1 - p.2) + 1) (z.2.2, z.2.1)) := by
    intro z
    by_cases hz : z.2 ∈ Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l
    · have hmem : (z.2.2, z.2.1) ∈
          Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l := by
        rw [Set.mem_prod] at hz ⊢
        exact ⟨hz.2, hz.1⟩
      have hk := hKpt z.2.2 z.2.1 hmem
      have hh := hHbd z
      rw [enorm_mul]
      calc ‖K1lim l W z.2.2 z.2.1‖ₑ * ‖H z‖ₑ
          ≤ (K * ((Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l).indicator
                (fun p : E3 × E3 => k1PerEnorm l W (p.1 - p.2) + 1) (z.2.2, z.2.1)))
            * (C' * ((Work.MB.boxPow n l).indicator (fun _ => (1 : ENNReal)) z.1)) :=
            mul_le_mul hk hh (by simp) (by simp)
        _ = K * C' * ((Work.MB.boxPow n l).indicator (fun _ => (1 : ENNReal)) z.1 *
              (Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l).indicator
                (fun p : E3 × E3 => k1PerEnorm l W (p.1 - p.2) + 1) (z.2.2, z.2.1)) := by
            ac_rfl
    · have hz0 : H z = 0 := by
        by_contra hne
        exact hz (Set.mem_prod.mp (hHs (Function.mem_support.mpr hne))).2
      rw [hz0]
      simp
  -- a.e. strong measurability
  have haesm : AEStronglyMeasurable
      (fun z : Work.BoseDict.Xn n × (E3 × E3) => K1lim l W z.2.2 z.2.1 * H z) volume := by
    have hΦ : AEStronglyMeasurable (fun p : E3 × E3 => K1lim l W p.1 p.2) (volume.prod volume) :=
      aesm_uncurry_K1lim_of_integrable (ℓ := l) hWi
    have hΦsw := hΦ.comp_quasiMeasurePreserving
      (MeasureTheory.Measure.measurePreserving_swap (μ := (volume : Measure E3))
        (ν := (volume : Measure E3))).quasiMeasurePreserving
    have hk : AEStronglyMeasurable (fun z : Work.BoseDict.Xn n × (E3 × E3) =>
        K1lim l W z.2.2 z.2.1) (volume : Measure (Work.BoseDict.Xn n × (E3 × E3))) :=
      hΦsw.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    exact hk.mul hHm
  -- a.e. measurability of the two factors of the majorant
  have hfX : AEMeasurable (fun x : Work.BoseDict.Xn n =>
      (Work.MB.boxPow n l).indicator (fun _ => (1 : ENNReal)) x) volume :=
    (measurable_const.indicator (Work.MB.measurableSet_boxPow n l)).aemeasurable
  have hfΨ : AEMeasurable (fun p : E3 × E3 =>
      (Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l).indicator
        (fun q : E3 × E3 => k1PerEnorm l W (q.1 - q.2) + 1) (p.2, p.1)) (volume.prod volume) := by
    have hb : AEMeasurable (fun p : E3 × E3 =>
        (Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l).indicator
          (fun q : E3 × E3 => k1PerEnorm l W (q.1 - q.2) + 1) p) (volume.prod volume) :=
      ((k1aemeasurable_perEnorm_sub hWme).add_const 1).indicator hBlm
    exact hb.comp_quasiMeasurePreserving
      (MeasureTheory.Measure.measurePreserving_swap (μ := (volume : Measure E3))
        (ν := (volume : Measure E3))).quasiMeasurePreserving
  -- finiteness of the two factors
  have hXfin : (∫⁻ x : Work.BoseDict.Xn n,
      (Work.MB.boxPow n l).indicator (fun _ => (1 : ENNReal)) x) < ⊤ := by
    rw [MeasureTheory.lintegral_indicator (Work.MB.measurableSet_boxPow n l)
        (fun _ => (1 : ENNReal)),
      MeasureTheory.setLIntegral_one]
    exact lt_top_iff_ne_top.mpr (Work.MB.volume_boxPow_lt_top n l)
  have hΨfin : (∫⁻ p : E3 × E3,
      (Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l).indicator
        (fun q : E3 × E3 => k1PerEnorm l W (q.1 - q.2) + 1) p.swap
        ∂(volume.prod volume)) < ⊤ := by
    have hsw := MeasureTheory.lintegral_prod_swap (μ := (volume : Measure E3))
      (ν := (volume : Measure E3))
      (f := (Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l).indicator
        (fun q : E3 × E3 => k1PerEnorm l W (q.1 - q.2) + 1))
    rw [hsw]
    refine lt_of_le_of_lt (k1lintegral_indicator_add_le hl hWi hWme) ?_
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hWi.hasFiniteIntegral,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top⟩
  refine ⟨haesm, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono hfpt) ?_
  rw [show (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn n × (E3 × E3)))
      = (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn n)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) from rfl]
  rw [MeasureTheory.lintegral_const_mul' (K * C') _ (ENNReal.mul_ne_top hKne hC'ne)]
  rw [MeasureTheory.lintegral_prod_mul (μ := (volume : Measure (Work.BoseDict.Xn n)))
    (ν := (volume : Measure (E3 × E3)))
    (f := fun x : Work.BoseDict.Xn n => (Work.MB.boxPow n l).indicator (fun _ => (1 : ENNReal)) x)
    (g := fun p : E3 × E3 =>
      (Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l).indicator
        (fun q : E3 × E3 => k1PerEnorm l W (q.1 - q.2) + 1) (p.2, p.1))
    hfX hfΨ]
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hKne) (lt_top_iff_ne_top.mpr hC'ne))
    (ENNReal.mul_lt_top hXfin hΨfin)

end Work.BoseBoxFock
