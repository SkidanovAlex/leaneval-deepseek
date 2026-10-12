import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.deb_le_sixBall
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.debCredit_lintegral_le_sixBall` — the `∫⁻`-form of the six-ball debit comparison

This is the `ℝ≥0∞`-valued (Lebesgue `lintegral`) companion of the Bochner-integral comparison
`Work.BoseFixR.deb_le_sixBall`.  The statement is the *same* inequality, with each of the seven
Bochner integrals `∫ …` replaced by `∫⁻ … , ENNReal.ofReal (…)`; only the formalisation differs.

## Route

The naive route (rewrite each `∫⁻ u in s, ENNReal.ofReal (f u)` as `ENNReal.ofReal (∫ u in s, f u)`
via `MeasureTheory.lintegral_ofReal`, apply `deb_le_sixBall`, convert back) is **not** available:
`lintegral_ofReal` needs `IntegrableOn f s`, and `deb_le_sixBall` gets its integrability from a
*global uniform bound* `∃ C, ∀ x, |W x| ≤ C` on `W`, which the present hypotheses
(`Integrable W`, `0 ≤ᵐ W`, compact support) do **not** provide — an `L¹ ∩` compactly supported
function need not be bounded, and then the real quantity `∫ x, W x * W (x+u)` is a Bochner
integral of a possibly non-integrable integrand (hence `0` by the `integral_undef` convention),
which is *not* what the `∫⁻` of the `ofReal` of it computes.

Instead the proof works **directly at the level of `∫⁻`**, where no integrability at all is
needed:

* replace `W` by its pointwise-nonnegative representative `Wp = fun x => max (W x) 0`; the
  autocorrelations agree *pointwise* (`debPair Wp u = debPair W u` for **all** `u`, because
  `Wp =ᵐ W` and Lebesgue measure is translation invariant) — `debPair_max_zero`;
* for pointwise-nonnegative `Wp` the comparison is a **pointwise** inequality of real numbers,
  exactly the `hpoint` block of `deb_le_sixBall` (no boundedness used anywhere) —
  `debPointwise_le_sixBall`;
* `MeasureTheory.lintegral_mono` (no measurability hypotheses) upgrades it to `∫⁻`;
* `ENNReal.ofReal_add` / `ENNReal.ofReal_sum_of_nonneg` split the `ofReal` of the sum into the
  `ENNReal`-sum of the six terms (all six are pointwise nonnegative);
* `MeasureTheory.lintegral_add_left'` and `MeasureTheory.lintegral_finsetSum'` distribute the
  `∫⁻` over the finite sum — the only place where a.e.-measurability of the six integrands is
  used, supplied by `debPair_aestronglyMeasurable` (`AEMeasurable.ennreal_ofReal`,
  `AEMeasurable.indicator`, `AEMeasurable.div`);
* `Set.indicator` is pushed through `ENNReal.ofReal` (`ofReal_indicator`) and eliminated by
  `MeasureTheory.lintegral_indicator`, turning `∫⁻ u, ofReal (1_{ball} f u)` into
  `∫⁻ u in ball, ofReal (f u)`.
-/

namespace Work.BoseFixR

noncomputable section

open scoped Real BigOperators ENNReal
open MeasureTheory Metric

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The pointwise six-ball comparison.**  For a *pointwise* nonnegative `W` supported in
`ball 0 R` with `2R < ℓ`, the crescent integrand `debPair W u / debLatD ℓ u` is dominated
pointwise by the sum of the six ball terms.  This is verbatim the `hpoint` block of the proof of
`Work.BoseFixR.deb_le_sixBall`; note that no boundedness of `W` is used. -/
private theorem debPointwise_le_sixBall {ℓ R : ℝ} (hℓ : 0 < ℓ) (h2R : 2 * R < ℓ)
    {W : E3 → ℝ} (hWnn : 0 ≤ W) (hsupp : tsupport W ⊆ Metric.ball 0 R) (u : E3) :
    (debSet ℓ).indicator (fun u => debPair W u / debLatD ℓ u) u
      ≤ (∑ i : Fin 3, debTermP ℓ W i u) + (∑ i : Fin 3, debTermN ℓ W i u) := by
  have hnonneg : 0 ≤ (∑ i : Fin 3, debTermP ℓ W i u) + (∑ i : Fin 3, debTermN ℓ W i u) :=
    add_nonneg (Finset.sum_nonneg fun i _ => debTermP_nonneg hWnn i u)
      (Finset.sum_nonneg fun i _ => debTermN_nonneg hWnn i u)
  by_cases hu : u ∈ debSet ℓ
  · rw [Set.indicator_of_mem hu]
    by_cases h2u : ‖u‖ < 2 * R
    · obtain ⟨i, hi | hi⟩ := deb_cover hℓ h2R hu h2u
      · have hQi : debLatD ℓ u = ‖u - debLC ℓ i‖ := by
          have h := debLatD_ball (ℓ := ℓ) hℓ (n := Pi.single i (1 : ℤ)) hi
          simpa [debLC] using h
        have hval : debTermP ℓ W i u = debPair W u / debLatD ℓ u := by
          rw [debTermP_of_mem hi, hQi]
        calc debPair W u / debLatD ℓ u = debTermP ℓ W i u := hval.symm
          _ ≤ ∑ j : Fin 3, debTermP ℓ W j u :=
              Finset.single_le_sum (fun j _ => debTermP_nonneg hWnn j u) (Finset.mem_univ i)
          _ ≤ (∑ j : Fin 3, debTermP ℓ W j u) + (∑ j : Fin 3, debTermN ℓ W j u) :=
              le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => debTermN_nonneg hWnn j u)
      · have hQi : debLatD ℓ u = ‖u + debLC ℓ i‖ := by
          have h := debLatD_ball_neg (ℓ := ℓ) hℓ (n := Pi.single i (1 : ℤ)) hi
          simpa [debLC] using h
        have hval : debTermN ℓ W i u = debPair W u / debLatD ℓ u := by
          rw [debTermN_of_mem hi, hQi]
        calc debPair W u / debLatD ℓ u = debTermN ℓ W i u := hval.symm
          _ ≤ ∑ j : Fin 3, debTermN ℓ W j u :=
              Finset.single_le_sum (fun j _ => debTermN_nonneg hWnn j u) (Finset.mem_univ i)
          _ ≤ (∑ j : Fin 3, debTermP ℓ W j u) + (∑ j : Fin 3, debTermN ℓ W j u) :=
              le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => debTermP_nonneg hWnn j u)
    · have hz : debPair W u = 0 := debPair_eq_zero_of_norm_ge hsupp (le_of_not_gt h2u)
      rw [hz, zero_div]
      exact hnonneg
  · rw [Set.indicator_of_notMem hu]
    exact hnonneg

/-- `ENNReal.ofReal` commutes with `Set.indicator` (because `ENNReal.ofReal 0 = 0`). -/
private lemma ofReal_indicator (s : Set E3) (f : E3 → ℝ) (x : E3) :
    ENNReal.ofReal (s.indicator f x) = s.indicator (fun x => ENNReal.ofReal (f x)) x := by
  by_cases h : x ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

/-- The `i`-th positive-centre term of the six-ball comparison, pushed into `ℝ≥0∞`, is
a.e.-measurable whenever `debPair W` is. -/
private lemma aemeasurable_ofReal_debTermP {W : E3 → ℝ} (hW : AEMeasurable (debPair W) volume)
    (ℓ : ℝ) (i : Fin 3) :
    AEMeasurable (fun u : E3 => ENNReal.ofReal (debTermP ℓ W i u)) volume := by
  rw [debTermP_eq]
  refine (AEMeasurable.indicator ?_ measurableSet_ball).ennreal_ofReal
  exact hW.div ((continuous_norm.comp (continuous_id.sub continuous_const)).measurable.aemeasurable)

/-- The `i`-th negative-centre term of the six-ball comparison, pushed into `ℝ≥0∞`, is
a.e.-measurable whenever `debPair W` is. -/
private lemma aemeasurable_ofReal_debTermN {W : E3 → ℝ} (hW : AEMeasurable (debPair W) volume)
    (ℓ : ℝ) (i : Fin 3) :
    AEMeasurable (fun u : E3 => ENNReal.ofReal (debTermN ℓ W i u)) volume := by
  rw [debTermN_eq]
  refine (AEMeasurable.indicator ?_ measurableSet_ball).ennreal_ofReal
  exact hW.div ((continuous_norm.comp (continuous_id.add continuous_const)).measurable.aemeasurable)

/-- The pointwise-nonnegative representative of `W` has the same autocorrelation: if
`0 ≤ᵐ W` then `debPair (fun x => max (W x) 0) u = debPair W u` for **every** `u` (translation
invariance of Lebesgue measure). -/
private lemma debPair_max_zero {W : E3 → ℝ} (hWnn : 0 ≤ᵐ[volume] W) (u : E3) :
    debPair (fun x => max (W x) 0) u = debPair W u := by
  set Wp : E3 → ℝ := fun x => max (W x) 0 with hWp_def
  have hWp_ae : Wp =ᵐ[volume] W := by
    filter_upwards [hWnn] with x hx
    rw [hWp_def]
    exact max_eq_left hx
  show (∫ x, Wp x * Wp (x + u)) = ∫ x, W x * W (x + u)
  refine integral_congr_ae ?_
  filter_upwards [hWp_ae,
    (measurePreserving_add_right volume u).quasiMeasurePreserving.ae hWp_ae] with x hx hx2
  rw [hx, hx2]

theorem debCredit_lintegral_le_sixBall {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R) (h2R : 2 * R < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW1 : MeasureTheory.Integrable W)
    (hWnn : 0 ≤ᵐ[MeasureTheory.volume] W)
    (hsupp : tsupport W ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    (∫⁻ u in {u : EuclideanSpace ℝ (Fin 3) | Metric.infDist u (Set.range (fun n : Fin 3 → ℤ => Work.BoseFixR.lat ℓ n)) < ‖u‖ / 3},
        ENNReal.ofReal ((∫ x, W x * W (x + u)) / Metric.infDist u (Set.range (fun n : Fin 3 → ℤ => Work.BoseFixR.lat ℓ n))))
      ≤ (∑ i : Fin 3, ∫⁻ u in Metric.ball (Work.BoseFixR.lat ℓ (Pi.single i (1 : ℤ))) (ℓ / 2),
            ENNReal.ofReal ((∫ x, W x * W (x + u)) / ‖u - Work.BoseFixR.lat ℓ (Pi.single i (1 : ℤ))‖))
        + (∑ i : Fin 3, ∫⁻ u in Metric.ball (-(Work.BoseFixR.lat ℓ (Pi.single i (1 : ℤ)))) (ℓ / 2),
            ENNReal.ofReal ((∫ x, W x * W (x + u)) / ‖u + Work.BoseFixR.lat ℓ (Pi.single i (1 : ℤ))‖)) := by
  change (∫⁻ u in debSet ℓ, ENNReal.ofReal (debPair W u / debLatD ℓ u))
      ≤ (∑ i : Fin 3, ∫⁻ u in Metric.ball (debLC ℓ i) (ℓ / 2),
            ENNReal.ofReal (debPair W u / ‖u - debLC ℓ i‖))
        + (∑ i : Fin 3, ∫⁻ u in Metric.ball (-(debLC ℓ i)) (ℓ / 2),
            ENNReal.ofReal (debPair W u / ‖u + debLC ℓ i‖))
  set Wp : E3 → ℝ := fun x => max (W x) 0 with hWp_def
  have hWp_nn : 0 ≤ Wp := by intro x; rw [hWp_def]; exact le_max_right _ _
  have hWp_supp : tsupport Wp ⊆ Metric.ball 0 R := by
    have h1 : tsupport Wp ⊆ tsupport W := by
      apply closure_mono
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro h
      exact hx (by rw [hWp_def]; simp [h])
    intro x hx
    exact hsupp (h1 hx)
  have hpair : ∀ u : E3, debPair Wp u = debPair W u := by
    intro u
    rw [show Wp = (fun x : E3 => max (W x) 0) from hWp_def]
    exact debPair_max_zero hWnn u
  have hpair_meas : AEMeasurable (debPair Wp) volume :=
    (debPair_aestronglyMeasurable hW1).aemeasurable.congr
      (Filter.Eventually.of_forall (fun u => (hpair u).symm))
  have hmeasP : AEMeasurable (fun u : E3 => ∑ i : Fin 3, ENNReal.ofReal (debTermP ℓ Wp i u))
      volume :=
    Finset.aemeasurable_sum Finset.univ (fun i _ => aemeasurable_ofReal_debTermP hpair_meas ℓ i)
  have hmeasN : AEMeasurable (fun u : E3 => ∑ i : Fin 3, ENNReal.ofReal (debTermN ℓ Wp i u))
      volume :=
    Finset.aemeasurable_sum Finset.univ (fun i _ => aemeasurable_ofReal_debTermN hpair_meas ℓ i)
  calc (∫⁻ u in debSet ℓ, ENNReal.ofReal (debPair W u / debLatD ℓ u))
      = ∫⁻ u, ENNReal.ofReal ((debSet ℓ).indicator (fun u => debPair Wp u / debLatD ℓ u) u) := by
        rw [← MeasureTheory.lintegral_indicator (debSet_measurable ℓ)]
        apply MeasureTheory.lintegral_congr
        intro u
        rw [ofReal_indicator]
        by_cases hu : u ∈ debSet ℓ
        · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, hpair u]
        · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
    _ ≤ ∫⁻ u, ENNReal.ofReal
          ((∑ i : Fin 3, debTermP ℓ Wp i u) + (∑ i : Fin 3, debTermN ℓ Wp i u)) := by
        refine MeasureTheory.lintegral_mono (fun u => ?_)
        exact ENNReal.ofReal_le_ofReal (debPointwise_le_sixBall hℓ h2R hWp_nn hWp_supp u)
    _ = ∫⁻ u, ((∑ i : Fin 3, ENNReal.ofReal (debTermP ℓ Wp i u))
            + (∑ i : Fin 3, ENNReal.ofReal (debTermN ℓ Wp i u))) := by
        apply MeasureTheory.lintegral_congr
        intro u
        have hP : 0 ≤ ∑ i : Fin 3, debTermP ℓ Wp i u :=
          Finset.sum_nonneg fun i _ => debTermP_nonneg hWp_nn i u
        have hN : 0 ≤ ∑ i : Fin 3, debTermN ℓ Wp i u :=
          Finset.sum_nonneg fun i _ => debTermN_nonneg hWp_nn i u
        rw [ENNReal.ofReal_add hP hN,
          ENNReal.ofReal_sum_of_nonneg (fun i _ => debTermP_nonneg hWp_nn i u),
          ENNReal.ofReal_sum_of_nonneg (fun i _ => debTermN_nonneg hWp_nn i u)]
    _ = (∑ i : Fin 3, ∫⁻ u, ENNReal.ofReal (debTermP ℓ Wp i u))
        + (∑ i : Fin 3, ∫⁻ u, ENNReal.ofReal (debTermN ℓ Wp i u)) := by
        rw [MeasureTheory.lintegral_add_left' hmeasP]
        rw [MeasureTheory.lintegral_finsetSum' Finset.univ
          (fun i _ => aemeasurable_ofReal_debTermP hpair_meas ℓ i)]
        rw [MeasureTheory.lintegral_finsetSum' Finset.univ
          (fun i _ => aemeasurable_ofReal_debTermN hpair_meas ℓ i)]
    _ = (∑ i : Fin 3, ∫⁻ u in Metric.ball (debLC ℓ i) (ℓ / 2),
            ENNReal.ofReal (debPair Wp u / ‖u - debLC ℓ i‖))
        + (∑ i : Fin 3, ∫⁻ u in Metric.ball (-(debLC ℓ i)) (ℓ / 2),
            ENNReal.ofReal (debPair Wp u / ‖u + debLC ℓ i‖)) := by
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          have hfun : (fun u : E3 => ENNReal.ofReal (debTermP ℓ Wp i u))
              = (Metric.ball (debLC ℓ i) (ℓ / 2)).indicator
                  (fun u => ENNReal.ofReal (debPair Wp u / ‖u - debLC ℓ i‖)) := by
            funext u
            rw [debTermP_eq]
            exact ofReal_indicator _ _ u
          rw [hfun, MeasureTheory.lintegral_indicator measurableSet_ball]
        · apply Finset.sum_congr rfl
          intro i _
          have hfun : (fun u : E3 => ENNReal.ofReal (debTermN ℓ Wp i u))
              = (Metric.ball (-(debLC ℓ i)) (ℓ / 2)).indicator
                  (fun u => ENNReal.ofReal (debPair Wp u / ‖u + debLC ℓ i‖)) := by
            funext u
            rw [debTermN_eq]
            exact ofReal_indicator _ _ u
          rw [hfun, MeasureTheory.lintegral_indicator measurableSet_ball]
    _ = (∑ i : Fin 3, ∫⁻ u in Metric.ball (debLC ℓ i) (ℓ / 2),
            ENNReal.ofReal (debPair W u / ‖u - debLC ℓ i‖))
        + (∑ i : Fin 3, ∫⁻ u in Metric.ball (-(debLC ℓ i)) (ℓ / 2),
            ENNReal.ofReal (debPair W u / ‖u + debLC ℓ i‖)) := by
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          apply MeasureTheory.lintegral_congr
          intro u
          rw [hpair u]
        · apply Finset.sum_congr rfl
          intro i _
          apply MeasureTheory.lintegral_congr
          intro u
          rw [hpair u]

end

end Work.BoseFixR
