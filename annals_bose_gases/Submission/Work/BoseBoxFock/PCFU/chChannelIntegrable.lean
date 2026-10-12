import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.ChWordChains
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chChannelIntegrable` — the channel integrands are integrable

The four channel integrals of the cubic dictionary `chAint …chDint` are Bochner integrals of the
integrands `chAintand …chDintand` (`ChWordChains.lean`), each of the shape

    q ↦ Θ(q.1) · θ_ℓ(q.1 i) · K(q.2.1, q.1 j, q.2.2) · Θ(q.1[i↦q.2.1][j↦q.2.2])

on `X n × (E3 × E3)`, where `θ_ℓ = corpusBox.thetaFun ℓ` is the sharp box indicator of the corpus
box `boxL ℓ = ℓ • cell` and `K` is the channel kernel (`ChAU`, `ChBU`, `ChCU`, `ChDU`).

This module proves the **general integrability lemma** `chChannelIntegrable`: whenever

* `K` is measurable and pointwise bounded,
* `K` vanishes when its first slot `y` is outside `boxL ℓ` (the `A`,`B` channels: the factor
  `χ_Λ(y)`) and when its last slot `u` is outside `boxL ℓ` (the `B`,`D` channels: the factor
  `θ_Λ(u)`; the `A`,`C` channels: the factor `χ_Λ(u)`),

then the channel integrand is integrable — *no* hypothesis on `Θ` beyond measurability,
boundedness and support in `abox n ℓ`.

The mechanism is the only one available here: the integrand is measurable, bounded by
`(max Cθ 0)² · max CK 0`, and its support is contained in the *finite measure* set

    `abox n ℓ ×ˢ (boxL ℓ ×ˢ boxL ℓ)`

(`abox_lt_top`, `boxL_compact.measure_lt_top`), so `Integrable.mono'` against the indicator of
that set closes it.  Note that the `E3 × E3` factor is *not* finite measure: it is the support of
the kernel in the two replacement slots that saves the day.

The file also carries the small facts the four instantiations need:
`ch_thetaFun_norm_le`, `ch_measurable_thetaFun`, `ch_thetaFun_eq_zero_of_notMem`,
`ch_chiLam_eq_zero_of_notMem`, `ch_measurable_update_update` and the "bounded on a box-supported
integrand ⇒ bounded integral" lemma `ch_norm_integral_le_of_support_boxL`.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 2000000

/-! ## Elementary facts about the corpus box -/

/-- The sharp box indicator is bounded by one. -/
theorem ch_thetaFun_norm_le (ℓ : ℝ) (z : E3) :
    ‖Work.BoseK15.corpusBox.thetaFun ℓ z‖ ≤ 1 := by
  rw [Work.BoseB4.BoxData.thetaFun_apply]; split_ifs <;> simp

/-- The sharp box indicator is measurable (it is the indicator of `boxL ℓ`). -/
theorem ch_measurable_thetaFun (ℓ : ℝ) : Measurable (Work.BoseK15.corpusBox.thetaFun ℓ) := by
  have h : Work.BoseK15.corpusBox.thetaFun ℓ
      = Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : E3 => (1 : ℂ)) := by
    funext z
    rw [Work.BoseB4.BoxData.thetaFun_apply]
    by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ <;> simp [hz]
  rw [h]
  exact measurable_const.indicator (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ)

/-- The sharp box indicator vanishes off the box. -/
theorem ch_thetaFun_eq_zero_of_notMem {ℓ : ℝ} {y : E3}
    (hy : y ∉ Work.BoseK15.corpusBox.boxL ℓ) : Work.BoseK15.corpusBox.thetaFun ℓ y = 0 := by
  rw [Work.BoseB4.BoxData.thetaFun_apply, if_neg hy]

/-- The corpus localisation function vanishes off the box. -/
theorem ch_chiLam_eq_zero_of_notMem {ℓ : ℝ} (hℓ : 0 < ℓ) {y : E3}
    (hy : y ∉ Work.BoseK15.corpusBox.boxL ℓ) : Work.BoseK15.corpusBox.chiLam ℓ y = 0 :=
  Function.notMem_support.mp (fun hmem =>
    hy (Work.BoseB4.BoxData.chiLam_supp _ hℓ hmem))

/-! ## Measurability of the double replacement -/

/-- `q ↦ q.1[i↦q.2.1][j↦q.2.2]` is measurable. -/
theorem ch_measurable_update_update {n : ℕ} (i j : Fin n) :
    Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      Function.update (Function.update q.1 i q.2.1) j q.2.2) := by
  refine Measurable.of_eval (fun k => ?_)
  by_cases hk : k = j
  · have h : (fun q : Submission.BoseGases.X n × (E3 × E3) =>
        Function.update (Function.update q.1 i q.2.1) j q.2.2 k)
        = fun q : Submission.BoseGases.X n × (E3 × E3) => q.2.2 := by
      funext q; rw [Function.update_apply, if_pos hk]
    rw [h]; exact measurable_snd.comp measurable_snd
  · have h : (fun q : Submission.BoseGases.X n × (E3 × E3) =>
        Function.update (Function.update q.1 i q.2.1) j q.2.2 k)
        = fun q : Submission.BoseGases.X n × (E3 × E3) => Function.update q.1 i q.2.1 k := by
      funext q; rw [Function.update_apply, if_neg hk]
    rw [h]
    by_cases hki : k = i
    · have h2 : (fun q : Submission.BoseGases.X n × (E3 × E3) =>
          Function.update q.1 i q.2.1 k)
          = fun q : Submission.BoseGases.X n × (E3 × E3) => q.2.1 := by
        funext q; rw [Function.update_apply, if_pos hki]
      rw [h2]; exact measurable_fst.comp measurable_snd
    · have h2 : (fun q : Submission.BoseGases.X n × (E3 × E3) =>
          Function.update q.1 i q.2.1 k)
          = fun q : Submission.BoseGases.X n × (E3 × E3) => q.1 k := by
        funext q; rw [Function.update_apply, if_neg hki]
      rw [h2]; exact (measurable_pi_apply k).comp measurable_fst

/-! ## A box-supported bounded integrand has a bounded integral -/

/-- If a function is bounded by `CF` and supported in the corpus box `boxL ℓ`, then its integral
is bounded by `CF · ℓ³`.  (The box has volume `ℓ³`, which is what turns the pointwise bound into
a bound on the Bochner integral.) -/
theorem ch_norm_integral_le_of_support_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) {F : E3 → ℂ} {CF : ℝ}
    (hsupp : ∀ w : E3, w ∉ Work.BoseK15.corpusBox.boxL ℓ → F w = 0)
    (hbdd : ∀ w : E3, ‖F w‖ ≤ CF) :
    ‖∫ w : E3, F w‖ ≤ CF * ℓ ^ 3 := by
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
  have h1 : ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ, F w‖
      ≤ CF * (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal :=
    MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (Work.BoseB4.BoxData.boxL_compact _ ℓ).measure_lt_top (fun w _ => hbdd w)
  have h2 : (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal = ℓ ^ 3 := by
    rw [Work.BoseB4.BoxData.volume_boxL _ hℓ, ENNReal.toReal_ofReal (by positivity)]
  rwa [h2] at h1

/-! ## The general integrability lemma -/

/-- **The channel integrand is integrable.**  For a measurable bounded state `Θ` supported in
`abox n ℓ` and a measurable bounded channel kernel `K` vanishing off `boxL ℓ` in its first and
last slots, the integrand

    `q ↦ Θ(q.1) · θ_ℓ(q.1 i) · K(q.2.1, q.1 j, q.2.2) · Θ(q.1[i↦q.2.1][j↦q.2.2])`

is Bochner integrable on `X n × (E3 × E3)`. -/
theorem chChannelIntegrable {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ)
    (i j : Fin n) (K : E3 × (E3 × E3) → ℂ)
    (hKm : Measurable K) (CK : ℝ) (hKb : ∀ p, ‖K p‖ ≤ CK)
    (hKs1 : ∀ y x u, y ∉ Work.BoseK15.corpusBox.boxL ℓ → K (y, x, u) = 0)
    (hKs2 : ∀ y x u, u ∉ Work.BoseK15.corpusBox.boxL ℓ → K (y, x, u) = 0) :
    Integrable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      ((Θ q.1 : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ (q.1 i)
        * K (q.2.1, q.1 j, q.2.2)
        * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)) := by
  classical
  obtain ⟨Cθ, hCθ⟩ := hΘb
  have hupd : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      Function.update (Function.update q.1 i q.2.1) j q.2.2) := ch_measurable_update_update i j
  set F : Submission.BoseGases.X n × (E3 × E3) → ℂ := fun q =>
    ((Θ q.1 : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ (q.1 i)
      * K (q.2.1, q.1 j, q.2.2)
      * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ) with hFdef
  have hmeas : Measurable F := by
    have h1 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) => ((Θ q.1 : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp (hΘm.comp measurable_fst)
    have h2 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
        Work.BoseK15.corpusBox.thetaFun ℓ (q.1 i)) :=
      (ch_measurable_thetaFun ℓ).comp ((measurable_pi_apply i).comp measurable_fst)
    have h3 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
        K (q.2.1, q.1 j, q.2.2)) :=
      hKm.comp (((measurable_fst.comp measurable_snd)).prodMk
        (((measurable_pi_apply j).comp measurable_fst).prodMk
          (measurable_snd.comp measurable_snd)))
    have h4 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
        ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp (hΘm.comp hupd)
    exact ((h1.mul h2).mul h3).mul h4
  set Cb : ℝ := max Cθ 0 * max CK 0 * max Cθ 0 with hCbdef
  have hbound : ∀ q, ‖F q‖ ≤ Cb := by
    intro q
    have hA : ‖((Θ q.1 : ℝ) : ℂ)‖ ≤ max Cθ 0 := by
      rw [show ‖((Θ q.1 : ℝ) : ℂ)‖ = |Θ q.1| from by simp]
      exact (hCθ q.1).trans (le_max_left _ _)
    have hB : ‖Work.BoseK15.corpusBox.thetaFun ℓ (q.1 i)‖ ≤ 1 := ch_thetaFun_norm_le ℓ _
    have hK' : ‖K (q.2.1, q.1 j, q.2.2)‖ ≤ max CK 0 := (hKb _).trans (le_max_left _ _)
    have hD : ‖((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)‖
        ≤ max Cθ 0 := by
      rw [show ‖((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)‖
        = |Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2)| from by simp]
      exact (hCθ _).trans (le_max_left _ _)
    rw [hFdef]
    simp only
    rw [norm_mul, norm_mul, norm_mul]
    have hger : ‖((Θ q.1 : ℝ) : ℂ)‖ * ‖Work.BoseK15.corpusBox.thetaFun ℓ (q.1 i)‖
        * ‖K (q.2.1, q.1 j, q.2.2)‖
        * ‖((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)‖
        ≤ (max Cθ 0) * 1 * (max CK 0) * (max Cθ 0) := by
      gcongr
    exact hger.trans (le_of_eq (by rw [hCbdef]; ring))
  have hsupp : Function.support F ⊆
      Submission.BoseGases.abox n ℓ
        ×ˢ (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ) := by
    intro q hq
    rw [Function.mem_support] at hq
    rw [Set.mem_prod]
    by_cases h1 : q.1 ∈ Submission.BoseGases.abox n ℓ
    · by_cases h2 : q.2.1 ∈ Work.BoseK15.corpusBox.boxL ℓ
      · have h3 : q.2.2 ∈ Work.BoseK15.corpusBox.boxL ℓ := by
          by_contra h3
          exact hq (by rw [hFdef]; simp [hKs2 q.2.1 (q.1 j) q.2.2 h3])
        exact ⟨h1, by rw [Set.mem_prod]; exact ⟨h2, h3⟩⟩
      · exact absurd (by rw [hFdef]; simp [hKs1 q.2.1 (q.1 j) q.2.2 h2]) hq
    · have h0 : Θ q.1 = 0 := by
        by_contra hc
        exact h1 (hΘs (Function.mem_support.mpr hc))
      exact absurd (by rw [hFdef]; simp [h0]) hq
  have hSm : MeasurableSet (Submission.BoseGases.abox n ℓ
      ×ˢ (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)) :=
    (Submission.BoseGases.abox_measurable n ℓ).prod
      ((Work.BoseB4.BoxData.boxL_measurableSet _ ℓ).prod
        (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ))
  have hSfin : (volume : Measure (Submission.BoseGases.X n × (E3 × E3)))
      (Submission.BoseGases.abox n ℓ
        ×ˢ (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)) < ⊤ := by
    have h1 : (volume : Measure (Submission.BoseGases.X n × (E3 × E3)))
        (Submission.BoseGases.abox n ℓ
          ×ˢ (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ))
        = (volume : Measure (Submission.BoseGases.X n)) (Submission.BoseGases.abox n ℓ)
          * (volume : Measure (E3 × E3))
              (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ) :=
      Measure.prod_prod _ _
    have h2 : (volume : Measure (E3 × E3))
        (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)
        = (volume : Measure E3) (Work.BoseK15.corpusBox.boxL ℓ)
          * (volume : Measure E3) (Work.BoseK15.corpusBox.boxL ℓ) :=
      Measure.prod_prod _ _
    rw [h1, h2]
    exact ENNReal.mul_lt_top (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
      (ENNReal.mul_lt_top (Work.BoseB4.BoxData.boxL_compact _ ℓ).measure_lt_top
        (Work.BoseB4.BoxData.boxL_compact _ ℓ).measure_lt_top)
  have hg : Integrable ((Submission.BoseGases.abox n ℓ
      ×ˢ (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)).indicator
        (fun _ => Cb)) (volume : Measure (Submission.BoseGases.X n × (E3 × E3))) := by
    rw [integrable_indicator_iff hSm]
    exact integrableOn_const (ne_of_lt hSfin) (by simp)
  refine Integrable.mono' hg hmeas.aestronglyMeasurable ?_
  filter_upwards with q
  by_cases hq : q ∈ Submission.BoseGases.abox n ℓ
        ×ˢ (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)
  · rw [Set.indicator_of_mem hq]; exact hbound q
  · rw [Set.indicator_of_notMem hq]
    have h0 : F q = 0 := by
      by_contra hc
      exact hq (hsupp (Function.mem_support.mpr hc))
    rw [h0, norm_zero]

end Work.BoseBoxFock.PCFU
