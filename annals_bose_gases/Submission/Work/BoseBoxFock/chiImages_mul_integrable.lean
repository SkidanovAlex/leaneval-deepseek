import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.K1lim_mul_integrable
import Submission.Work.BoseBoxFock.K1lim_mul_integrable_slot
import Submission.Work.BoseBoxFock.K1lim_sub_chiChiImages
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiImages_mul_integrable`

Integrability of the `χχ`-images kernel `chiChiImages ℓ ↑W` against a bounded test function
supported in the box squared (pair form) and against a bounded function of one slot and a free
variable (slot form), for an **integrable** weight `W`.

The route mirrors `K1lim_mul_integrable` / `K1lim_mul_integrable_slot`, but the kernel here is the
single `χχ`-row `χ(w)χ(y)Σ'_{m≠0}W(w−y+ℓm)`, so only the periodisation row needs analysis:

* `‖chiChiImages ℓ ↑W w y‖ₑ ≤ (sup χ)² · Σ'_m ‖W(w−y+ℓ•latVec m)‖ₑ` (unconditional, in `ℝ≥0∞`);
* the periodisation is dominated by the covering multiplicity of the lattice translates of the box
  (`k1lintegral_indicator_perEnorm_le`);
* the transport from the two-particle box to the `n`-particle box is the proved
  `lintegral_boxPow_eval_snd` (which asks for a *measurable* pair kernel), so the argument is run
  for a measurable representative `U =ᵐ W` and transported back along `ae_chiChiImages_congr`.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## Elementary helpers -/

/-- The sup-bound of `χ_ℓ`, `(√chiNormSq)⁻¹`, as an `ℝ≥0∞` constant. -/
noncomputable def chiSupBound : ENNReal :=
  ENNReal.ofReal ((Real.sqrt Submission.BoseGases.chiNormSq)⁻¹)

theorem chiSupBound_lt_top : chiSupBound < ⊤ := ENNReal.ofReal_lt_top

/-- The periodisation of `‖U‖ₑ` is measurable as soon as `U` is. -/
theorem measurable_k1PerEnorm {ℓ : ℝ} {U : E3 → ℝ} (hUm : Measurable U) :
    Measurable (k1PerEnorm ℓ U) := by
  have hterm : ∀ m : Fin 3 → ℤ, Measurable (fun z : E3 => ‖U (z + ℓ • latVec m)‖ₑ) := fun m =>
    (hUm.comp (continuous_id.add continuous_const).measurable).enorm
  change Measurable (fun z : E3 => ∑' m : Fin 3 → ℤ, ‖U (z + ℓ • latVec m)‖ₑ)
  exact Measurable.tsum (L := SummationFilter.unconditional (Fin 3 → ℤ)) hterm

/-- The `χχ`-images kernel is measurable as soon as the (complex) weight is. -/
theorem measurable_uncurry_chiChiImages {ℓ : ℝ} {U : E3 → ℂ} (hU : Measurable U) :
    Measurable (Function.uncurry (chiChiImages ℓ U)) := by
  change Measurable (fun p : E3 × E3 =>
    ((Submission.BoseGases.chiScale ℓ p.1 : ℝ) : ℂ)
      * ((Submission.BoseGases.chiScale ℓ p.2 : ℝ) : ℂ)
      * (∑' m : Fin 3 → ℤ, if m = 0 then (0 : ℂ) else U (p.1 - p.2 + ℓ • latVec m)))
  have hχ1 : Measurable (fun p : E3 × E3 =>
      ((Submission.BoseGases.chiScale ℓ p.1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      ((Submission.BoseGases.chiScale_continuous ℓ).measurable.comp measurable_fst)
  have hχ2 : Measurable (fun p : E3 × E3 =>
      ((Submission.BoseGases.chiScale ℓ p.2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      ((Submission.BoseGases.chiScale_continuous ℓ).measurable.comp measurable_snd)
  have hT : Measurable (fun p : E3 × E3 => ∑' m : Fin 3 → ℤ,
      if m = 0 then (0 : ℂ) else U (p.1 - p.2 + ℓ • latVec m)) := by
    refine Measurable.tsum (L := SummationFilter.unconditional (Fin 3 → ℤ)) (fun m => ?_)
    by_cases hm : m = 0
    · have hfun : (fun p : E3 × E3 => if m = 0 then (0 : ℂ) else U (p.1 - p.2 + ℓ • latVec m))
          = fun _ : E3 × E3 => (0 : ℂ) := by funext p; rw [if_pos hm]
      rw [hfun]
      exact measurable_const
    · have hfun : (fun p : E3 × E3 => if m = 0 then (0 : ℂ) else U (p.1 - p.2 + ℓ • latVec m))
          = fun p : E3 × E3 => U (p.1 - p.2 + ℓ • latVec m) := by funext p; rw [if_neg hm]
      rw [hfun]
      exact hU.comp (by fun_prop)
  exact (hχ1.mul hχ2).mul hT

/-- **The pointwise norm bound** of the `χχ`-images kernel in terms of the lattice periodisation
of `‖W‖ₑ`. -/
theorem enorm_chiChiImages_le {ℓ : ℝ} {W : E3 → ℝ} (w y : E3) :
    ‖chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y‖ₑ
      ≤ chiSupBound * chiSupBound * k1PerEnorm ℓ W (w - y) := by
  have hχ : ∀ z : E3, ‖(((Submission.BoseGases.chiScale ℓ z : ℝ)) : ℂ)‖ₑ ≤ chiSupBound := by
    intro z
    rw [chiSupBound, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (k1chiScale_norm_le ℓ z)
  have hsum : ‖∑' m : Fin 3 → ℤ,
        if m = 0 then (0 : ℂ) else ((W (w - y + ℓ • latVec m) : ℝ) : ℂ)‖ₑ
      ≤ k1PerEnorm ℓ W (w - y) := by
    refine le_trans enorm_tsum_le_tsum_enorm ?_
    refine ENNReal.tsum_le_tsum (fun m => ?_)
    by_cases hm : m = 0
    · rw [if_pos hm]; simp
    · rw [if_neg hm, k1enorm_ofReal_cast]
  rw [chiChiImages, enorm_mul, enorm_mul]
  exact mul_le_mul' (mul_le_mul' (hχ w) (hχ y)) hsum

/-- **The a.e. congruence** of the `χχ`-images kernel: it only depends on the a.e. class of the
weight.  The countably many shifts of the null set where `W ≠ U` are avoided.  (Stated in the
`∀ᵐ`-form; the `EventuallyEq`-form below is the one used downstream.) -/
theorem ae_chiChiImages_congr_aux {ℓ : ℝ} {W U : E3 → ℝ} (h : W =ᵐ[volume] U) :
    ∀ᵐ p ∂(volume.prod volume),
      chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.1 p.2
        = chiChiImages ℓ (fun z => ((U z : ℝ) : ℂ)) p.1 p.2 := by
  have hh : ∀ᵐ x ∂volume, W x = U x := h
  have hN0 : volume {x : E3 | ¬ (W x = U x)} = 0 := MeasureTheory.ae_iff.mp hh
  set N : Set E3 := toMeasurable volume {x : E3 | ¬ (W x = U x)} with hNdef
  have hN0' : volume N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact hN0
  have hNsub : {x : E3 | ¬ (W x = U x)} ⊆ N := by
    rw [hNdef]; exact subset_toMeasurable _ _
  have hBad0 : (volume.prod volume)
      (⋃ m : Fin 3 → ℤ, {p : E3 × E3 | p.1 - p.2 + ℓ • latVec m ∈ N}) = 0 :=
    measure_iUnion_null fun m => measure_prod_sub_add_mem_null hN0' (ℓ • latVec m)
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hBad0
  intro p hp
  rw [Set.mem_iUnion]
  by_contra hcon
  push_neg at hcon
  refine hp ?_
  have htsum : (∑' m : Fin 3 → ℤ,
        if m = 0 then (0 : ℂ) else ((W (p.1 - p.2 + ℓ • latVec m) : ℝ) : ℂ))
      = ∑' m : Fin 3 → ℤ,
        if m = 0 then (0 : ℂ) else ((U (p.1 - p.2 + ℓ • latVec m) : ℝ) : ℂ) := by
    refine tsum_congr (fun m => ?_)
    by_cases hm : m = 0
    · rw [if_pos hm, if_pos hm]
    · rw [if_neg hm, if_neg hm]
      have hWU : W (p.1 - p.2 + ℓ • latVec m) = U (p.1 - p.2 + ℓ • latVec m) := by
        by_contra hne
        exact hcon m (hNsub hne)
      rw [hWU]
  simp only [chiChiImages]
  rw [htsum]

/-- The `EventuallyEq` form of `ae_chiChiImages_congr_aux`. -/
theorem ae_chiChiImages_congr {ℓ : ℝ} {W U : E3 → ℝ} (h : W =ᵐ[volume] U) :
    (fun p : E3 × E3 => chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) p.1 p.2)
      =ᵐ[volume.prod volume]
    (fun p : E3 × E3 => chiChiImages ℓ (fun z => ((U z : ℝ) : ℂ)) p.1 p.2) :=
  ae_chiChiImages_congr_aux h

/-! ## The pair form, for a measurable weight -/

/-- The pair-form integrability at a **measurable** weight. -/
theorem chiChiImages_mul_integrable_pair_of_measurable {ℓ : ℝ} (hℓ : 0 < ℓ) {U : E3 → ℝ}
    (hUm : Measurable U) (hUfin : ∫⁻ z : E3, ‖U z‖ₑ < ⊤)
    {G : E3 → E3 → ℂ}
    (hGm : MeasureTheory.AEStronglyMeasurable (Function.uncurry G)
      (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)))
    (hGb : ∃ C : ℝ, ∀ w y, ‖G w y‖ ≤ C)
    (hGs : Function.support (Function.uncurry G) ⊆
      Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ)) :
    MeasureTheory.Integrable
      (Function.uncurry (fun w y : E3 =>
        chiChiImages ℓ (fun z => ((U z : ℝ) : ℂ)) w y * G w y))
      (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) := by
  obtain ⟨Cg, hCg⟩ := hGb
  have hCg0 : 0 ≤ Cg := le_trans (norm_nonneg _) (hCg 0 0)
  have hUmc : Measurable (fun z : E3 => ((U z : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hUm
  have hmeas : Measurable
      (fun p : E3 × E3 => chiChiImages ℓ (fun z => ((U z : ℝ) : ℂ)) p.1 p.2) :=
    measurable_uncurry_chiChiImages hUmc
  refine ⟨?_, ?_⟩
  · exact hmeas.aestronglyMeasurable.mul hGm
  · have hpt : ∀ p : E3 × E3,
        ‖chiChiImages ℓ (fun z => ((U z : ℝ) : ℂ)) p.1 p.2 * G p.1 p.2‖ₑ
          ≤ (ENNReal.ofReal Cg * chiSupBound * chiSupBound)
            * (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ).indicator
                (fun p : E3 × E3 => k1PerEnorm ℓ U (p.1 - p.2)) p := by
      intro p
      rw [enorm_mul]
      by_cases hp : p ∈ Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ
      · rw [Set.indicator_of_mem hp]
        have hGp : ‖G p.1 p.2‖ₑ ≤ ENNReal.ofReal Cg := by
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hCg p.1 p.2)
        calc ‖chiChiImages ℓ (fun z => ((U z : ℝ) : ℂ)) p.1 p.2‖ₑ * ‖G p.1 p.2‖ₑ
            ≤ (chiSupBound * chiSupBound * k1PerEnorm ℓ U (p.1 - p.2))
                * ENNReal.ofReal Cg :=
              mul_le_mul' (enorm_chiChiImages_le (ℓ := ℓ) (W := U) p.1 p.2) hGp
          _ = (ENNReal.ofReal Cg * chiSupBound * chiSupBound)
                * k1PerEnorm ℓ U (p.1 - p.2) := by ring
      · have hG0 : G p.1 p.2 = 0 := by
          by_contra hne
          exact hp (hGs (Function.mem_support.mpr hne))
        rw [Set.indicator_of_notMem hp, hG0]
        simp
    have hfin : (∫⁻ p : E3 × E3, (ENNReal.ofReal Cg * chiSupBound * chiSupBound)
        * (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ).indicator
            (fun p : E3 × E3 => k1PerEnorm ℓ U (p.1 - p.2)) p) < ⊤ := by
      have hclt : ENNReal.ofReal Cg * chiSupBound * chiSupBound < ⊤ :=
        ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top chiSupBound_lt_top)
          chiSupBound_lt_top
      rw [MeasureTheory.lintegral_const_mul' (ENNReal.ofReal Cg * chiSupBound * chiSupBound) _
        hclt.ne]
      refine ENNReal.mul_lt_top hclt ?_
      exact lt_of_le_of_lt
        (k1lintegral_indicator_perEnorm_le (ℓ := ℓ) hℓ hUm.aestronglyMeasurable)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hUfin)
    exact lt_of_le_of_lt (lintegral_mono hpt) hfin

/-! ## The slot form, for a measurable weight -/

/-- The slot-form integrability at a **measurable** weight. -/
theorem chiChiImages_mul_integrable_slot_of_measurable {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (p : Fin n × Fin n) {U : E3 → ℝ} (hUm : Measurable U) (hUfin : ∫⁻ z : E3, ‖U z‖ₑ < ⊤)
    {H : Work.BoseDict.Xn n × E3 → ℂ}
    (hHm : MeasureTheory.AEStronglyMeasurable H MeasureTheory.volume)
    (hHb : ∃ C : ℝ, ∀ z, ‖H z‖ ≤ C)
    (hHs : Function.support H ⊆ Set.prod (Work.MB.boxPow n ℓ)
      (Work.BoseK15.corpusBox.boxL ℓ)) :
    MeasureTheory.Integrable (fun z : Work.BoseDict.Xn n × E3 =>
      chiChiImages ℓ (fun z => ((U z : ℝ) : ℂ)) (z.1 p.2) z.2 * H z)
      (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn n × E3)) := by
  rcases n with _ | d
  · exact Fin.elim0 p.1
  obtain ⟨C, hC⟩ := hHb
  have hUmc : Measurable (fun z : E3 => ((U z : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hUm
  have hpairMeas : AEStronglyMeasurable
      (fun q : E3 × E3 => chiChiImages ℓ (fun z => ((U z : ℝ) : ℂ)) q.1 q.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    (measurable_uncurry_chiChiImages hUmc).aestronglyMeasurable
  have hcomp : AEStronglyMeasurable
      (fun z : Work.BoseDict.Xn (d + 1) × E3 =>
        chiChiImages ℓ (fun z => ((U z : ℝ) : ℂ)) (z.1 p.2) z.2)
      (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn (d + 1) × E3)) :=
    aesm_comp_eval_gen (d := d) (p := p.2) hpairMeas
  refine ⟨hcomp.mul hHm, ?_⟩
  have hPer : Measurable (k1PerEnorm ℓ U) := measurable_k1PerEnorm hUm
  have hF : Measurable (Function.uncurry (fun w y : E3 => k1PerEnorm ℓ U (w - y))) :=
    hPer.comp (by fun_prop : Measurable fun q : E3 × E3 => q.1 - q.2)
  have hHbd : ∀ z : Work.BoseDict.Xn (d + 1) × E3,
      ‖H z‖ₑ ≤ ENNReal.ofReal (max C 0)
        * ((Work.MB.boxPow (d + 1) ℓ).indicator (fun _ => 1) z.1
          * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => 1) z.2) := by
    intro z
    by_cases hz : z ∈ Set.prod (Work.MB.boxPow (d + 1) ℓ) (Work.BoseK15.corpusBox.boxL ℓ)
    · obtain ⟨hz1, hz2⟩ := Set.mem_prod.mp hz
      rw [Set.indicator_of_mem hz1, Set.indicator_of_mem hz2, mul_one, mul_one, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (le_trans (hC z) (le_max_left C 0))
    · have hz0 : H z = 0 := by
        by_contra hne
        exact hz (hHs (Function.mem_support.mpr hne))
      rw [hz0]
      simp
  have hbd : ∀ z : Work.BoseDict.Xn (d + 1) × E3,
      ‖chiChiImages ℓ (fun z => ((U z : ℝ) : ℂ)) (z.1 p.2) z.2 * H z‖ₑ
        ≤ (ENNReal.ofReal (max C 0) * chiSupBound * chiSupBound)
          * ((Work.MB.boxPow (d + 1) ℓ).indicator (fun _ => 1) z.1
            * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => 1) z.2
            * k1PerEnorm ℓ U (z.1 p.2 - z.2)) := by
    intro z
    rw [enorm_mul]
    calc ‖chiChiImages ℓ (fun z => ((U z : ℝ) : ℂ)) (z.1 p.2) z.2‖ₑ * ‖H z‖ₑ
        ≤ (chiSupBound * chiSupBound * k1PerEnorm ℓ U (z.1 p.2 - z.2))
            * (ENNReal.ofReal (max C 0)
              * ((Work.MB.boxPow (d + 1) ℓ).indicator (fun _ => 1) z.1
                * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => 1) z.2)) :=
          mul_le_mul' (enorm_chiChiImages_le (ℓ := ℓ) (W := U) (z.1 p.2) z.2) (hHbd z)
      _ = (ENNReal.ofReal (max C 0) * chiSupBound * chiSupBound)
            * ((Work.MB.boxPow (d + 1) ℓ).indicator (fun _ => 1) z.1
              * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => 1) z.2
              * k1PerEnorm ℓ U (z.1 p.2 - z.2)) := by ring
  have hfin : (∫⁻ z : Work.BoseDict.Xn (d + 1) × E3,
      (ENNReal.ofReal (max C 0) * chiSupBound * chiSupBound)
        * ((Work.MB.boxPow (d + 1) ℓ).indicator (fun _ => 1) z.1
          * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => 1) z.2
          * k1PerEnorm ℓ U (z.1 p.2 - z.2))) < ⊤ := by
    have hclt : ENNReal.ofReal (max C 0) * chiSupBound * chiSupBound < ⊤ :=
      ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top chiSupBound_lt_top)
        chiSupBound_lt_top
    rw [MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (max C 0) * chiSupBound * chiSupBound)
      _ hclt.ne]
    refine ENNReal.mul_lt_top hclt ?_
    rw [lintegral_boxPow_eval_snd (d := d) (p := p.2) (l := ℓ)
      (F := fun w y : E3 => k1PerEnorm ℓ U (w - y)) hF]
    refine ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr (Work.MB.volume_boxPow_lt_top d ℓ)) ?_
    have hbridge : (fun q : E3 × E3 => (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => 1) q.1
          * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => 1) q.2
          * k1PerEnorm ℓ U (q.1 - q.2))
        = fun q : E3 × E3 =>
            (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ).indicator
              (fun q : E3 × E3 => k1PerEnorm ℓ U (q.1 - q.2)) q := by
      funext q
      by_cases h1 : q.1 ∈ Work.BoseK15.corpusBox.boxL ℓ <;>
        by_cases h2 : q.2 ∈ Work.BoseK15.corpusBox.boxL ℓ <;>
        simp [Set.mem_prod, h1, h2]
    rw [hbridge]
    exact lt_of_le_of_lt
      (k1lintegral_indicator_perEnorm_le (ℓ := ℓ) hℓ hUm.aestronglyMeasurable)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hUfin)
  exact lt_of_le_of_lt (lintegral_mono hbd) hfin

/-- The `χχ`-images kernel `chiChiImages ℓ ↑W` is *integrable* against a bounded test function
supported in the box squared (pair form), and against a bounded function of the slot `p.2` and a
free variable (slot form), as soon as `W` is integrable — mirroring `K1lim_mul_integrable` and
`K1lim_mul_integrable_slot` for the single `χχ`-row.  (Reviewers' suggested route: obtain
integrability of `K1lim ℓ W · G` from the sibling, then subtract the integrable remainder
`K1lim − chiChiImages` given by `K1lim_sub_chiChiImages`, whose three `χ̂`-rows are bounded
(`errBdd_pinQBl/Cl/Dl_bdd`) and whose `m = 0` term is bounded on the box squared.)

The hypotheses are exactly those of `K1lim_mul_integrable` / `K1lim_mul_integrable_slot`, so the
two a.e.-measurability/`lintegral` estimates in those files (`k1enorm_latPer3_le`,
`k1aemeasurable_perEnorm(_sub)`, `lintegral_latPer3_pair_le`, `K1lim_pair_box_lt_top`,
`k1lintegral_indicator_perEnorm_le`, `k1lintegral_indicator_add_le`, `k1lintegral_majorant_lt_top`,
and `AEStronglyMeasurable` of the translated summands from `Integrable W`) can be replayed. -/
theorem chiImages_mul_integrable {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWi : MeasureTheory.Integrable W)
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hGm : MeasureTheory.AEStronglyMeasurable (Function.uncurry G) MeasureTheory.volume)
    (hGb : ∃ C : ℝ, ∀ w y, ‖G w y‖ ≤ C)
    (hGs : Function.support (Function.uncurry G) ⊆
      Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ)) :
    MeasureTheory.Integrable (Function.uncurry (fun w y : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y))
      (MeasureTheory.volume : MeasureTheory.Measure
        (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))
    ∧ (∀ {H : Work.BoseDict.Xn n × EuclideanSpace ℝ (Fin 3) → ℂ},
        MeasureTheory.AEStronglyMeasurable H MeasureTheory.volume →
        (∃ C : ℝ, ∀ z, ‖H z‖ ≤ C) →
        Function.support H ⊆ Set.prod (Work.MB.boxPow n ℓ)
          (Work.BoseK15.corpusBox.boxL ℓ) →
        MeasureTheory.Integrable (fun z : Work.BoseDict.Xn n × EuclideanSpace ℝ (Fin 3) =>
          Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (z.1 p.2) z.2 * H z)
          (MeasureTheory.volume : MeasureTheory.Measure
            (Work.BoseDict.Xn n × EuclideanSpace ℝ (Fin 3)))) := by
  obtain ⟨U, hUm, hWU⟩ : ∃ U : E3 → ℝ, Measurable U ∧ W =ᵐ[volume] U :=
    ⟨AEStronglyMeasurable.mk W hWi.aestronglyMeasurable,
      (hWi.aestronglyMeasurable.stronglyMeasurable_mk).measurable,
      hWi.aestronglyMeasurable.ae_eq_mk⟩
  have hUfin : ∫⁻ z : E3, ‖U z‖ₑ < ⊤ := by
    have h1 : ∫⁻ z : E3, ‖U z‖ₑ = ∫⁻ z : E3, ‖W z‖ₑ :=
      lintegral_congr_ae (hWU.mono (fun z hz => by show ‖U z‖ₑ = ‖W z‖ₑ; rw [hz]))
    rw [h1]
    exact hWi.hasFiniteIntegral
  have hae := ae_chiChiImages_congr (ℓ := ℓ) hWU
  constructor
  · refine (chiChiImages_mul_integrable_pair_of_measurable (ℓ := ℓ) hℓ hUm hUfin hGm hGb
      hGs).congr ?_
    filter_upwards [hae.symm] with q hq
    show chiChiImages ℓ (fun z => ((U z : ℝ) : ℂ)) q.1 q.2 * G q.1 q.2
      = chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) q.1 q.2 * G q.1 q.2
    rw [hq]
  · rcases n with _ | d
    · exact Fin.elim0 p.1
    · intro H hHm hHb hHs
      refine (chiChiImages_mul_integrable_slot_of_measurable (ℓ := ℓ) hℓ p hUm hUfin hHm hHb
        hHs).congr ?_
      filter_upwards [ae_eq_comp_eval_gen (d := d) (p := p.2)
        (φ := fun w y => chiChiImages ℓ (fun z => ((U z : ℝ) : ℂ)) w y)
        (φ' := fun w y => chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y) hae.symm] with z hz
      rw [hz]

end Work.BoseBoxFock
