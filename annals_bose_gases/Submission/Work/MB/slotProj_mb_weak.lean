import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.slotProj_finsetSum_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MB

open MeasureTheory

/-- **The slot projection preserves measurability and everywhere boundedness, for weak modes.**

The modes `e l` are only assumed measurable, *everywhere* bounded and supported in the box
`boxL ℓ` (no `Continuous` and no `HasCompactSupport`); the state `Φ` is only measurable and
everywhere bounded.  Then the slot projection
`slotProj e U Φ x = ∫ z : (↥U → E3), (∏ i, PV e (x i.1) (z i)) * Φ (updateFinset x U z)` is
measurable and everywhere bounded by a constant independent of `x`.

Proof sketch.  Write `slotProj e U Φ = slotInt e U Φ` (`slotProj_eq_slotInt_fun`).
*Measurability*: the two-variable integrand on `E3^N × (↥U → E3)` is honestly `Measurable` (the
kernel factor is a finite sum of products of the measurable coordinate maps, and
`(x,z) ↦ Φ (Function.updateFinset x U z)` is measurable by
`Work.BoseBoxFock.measurable_updateFinset_pair`); `Measurable` gives `StronglyMeasurable`
(`Measurable.stronglyMeasurable`, `ℂ` second countable), so
`StronglyMeasurable.integral_prod_right'` gives measurability of the partial integral.
*Boundedness*: with everywhere bounds `‖e l x‖ ≤ Bl l` and `‖Φ y‖ ≤ C` put
`K := ∑ l, Bl l * Bl l`.  Each factor `PV e (x i.1) (z i)` is bounded by `K` for every `x`, and
vanishes pointwise once `z i ∉ boxL ℓ` (`Work.BoseBoxFock.PV_eq_zero_of_factors` + `hsupp`), so
`‖slotProj e U Φ x‖ ≤ ∫ z, (Set.univ.pi (fun _ : ↥U => boxL ℓ)).indicator (fun _ => K ^ U.card * C) z`,
a constant equal to `(ℓ^3 * K) ^ U.card * C` (`Measure.pi_pi` + finiteness of `boxL ℓ`).
The same pattern (with a.e. bounds replaced by everywhere bounds) is carried out in
`Work.BoseBoxFock.integrable_slotKernel_finset` / `Work.BoseBoxFock.slotInt_measurable_bounded`. -/
theorem slotProj_mb_weak {m N : ℕ} {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (U : Finset (Fin N)) {Φ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ}
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    Measurable (Work.BoseBoxFock.slotProj e U Φ)
      ∧ ∃ C, ∀ x, ‖Work.BoseBoxFock.slotProj e U Φ x‖ ≤ C := by
  classical
  rw [Work.BoseBoxFock.slotProj_eq_slotInt_fun e U Φ]
  -- everywhere bounds for the modes, made nonnegative
  obtain ⟨Bl, hBlnn, hBl⟩ : ∃ Bl : Fin m → ℝ, (∀ l, 0 ≤ Bl l) ∧ ∀ l y, ‖e l y‖ ≤ Bl l := by
    choose B hB using hbdE
    exact ⟨fun l => max (B l) 0, fun l => le_max_right _ _,
      fun l y => (hB l y).trans (le_max_left _ _)⟩
  set K : ℝ := ∑ l : Fin m, Bl l * Bl l with hKdef
  have hKnn : 0 ≤ K := Finset.sum_nonneg fun l _ => mul_nonneg (hBlnn l) (hBlnn l)
  obtain ⟨CΦ, hCΦ⟩ := hΦb
  set C : ℝ := max CΦ 0 with hCdef
  have hCnn : 0 ≤ C := le_max_right _ _
  -- the support box of the fibre variables, of finite measure
  set Z : Set (↑U → EuclideanSpace ℝ (Fin 3)) :=
    Set.univ.pi (fun _ : ↑U => Work.BoseK15.corpusBox.boxL ℓ) with hZdef
  have hZmeas : MeasurableSet Z := by
    rw [hZdef]
    exact MeasurableSet.pi Set.countable_univ
      (fun _ _ => Work.BoseK15.corpusBox.boxL_measurableSet ℓ)
  have hZfin : volume Z ≠ ⊤ := by
    rw [hZdef]
    show (Measure.pi (fun _ : ↑U => (volume : Measure (EuclideanSpace ℝ (Fin 3)))))
        (Set.univ.pi (fun _ : ↑U => Work.BoseK15.corpusBox.boxL ℓ)) ≠ ⊤
    rw [Measure.pi_pi]
    exact ENNReal.prod_ne_top
      (fun i _ => (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne)
  constructor
  · -- ## measurability
    have h1 : ∀ i : ↑U,
        Measurable (fun p : (Fin N → EuclideanSpace ℝ (Fin 3)) × (↑U → EuclideanSpace ℝ (Fin 3))
          => p.1 i.1) :=
      fun i => (measurable_pi_apply i.1).comp measurable_fst
    have h2 : ∀ i : ↑U,
        Measurable (fun p : (Fin N → EuclideanSpace ℝ (Fin 3)) × (↑U → EuclideanSpace ℝ (Fin 3))
          => p.2 i) :=
      fun i => (measurable_pi_apply i).comp measurable_snd
    have hfac : ∀ i : ↑U,
        Measurable (fun p : (Fin N → EuclideanSpace ℝ (Fin 3)) × (↑U → EuclideanSpace ℝ (Fin 3))
          => Work.BoseBoxFock.PV e (p.1 i.1) (p.2 i)) := by
      intro i
      simp only [Work.BoseBoxFock.PV]
      exact Finset.measurable_sum _ (fun l _ => ((hmeas l).comp (h1 i)).mul
        ((continuous_star.measurable.comp ((hmeas l).comp (h2 i)))))
    have hjoint : Measurable (fun p : (Fin N → EuclideanSpace ℝ (Fin 3)) ×
          (↑U → EuclideanSpace ℝ (Fin 3)) =>
        (∏ i : ↑U, Work.BoseBoxFock.PV e (p.1 i.1) (p.2 i)) *
          Φ (Function.updateFinset p.1 U p.2)) :=
      (Finset.measurable_prod _ (fun i _ => hfac i)).mul
        (hΦm.comp (Work.BoseBoxFock.measurable_updateFinset_pair U))
    have hsm : StronglyMeasurable (fun x : Fin N → EuclideanSpace ℝ (Fin 3) =>
        ∫ z : ↑U → EuclideanSpace ℝ (Fin 3),
          (∏ i : ↑U, Work.BoseBoxFock.PV e (x i.1) (z i)) *
            Φ (Function.updateFinset x U z)) :=
      hjoint.stronglyMeasurable.integral_prod_right'
    exact hsm.measurable
  · -- ## everywhere boundedness
    refine ⟨(volume Z).toReal * (K ^ U.card * C), fun x => ?_⟩
    have hgint : Integrable (Z.indicator (fun _ : ↑U → EuclideanSpace ℝ (Fin 3) =>
        K ^ U.card * C)) (volume : Measure (↑U → EuclideanSpace ℝ (Fin 3))) := by
      haveI : IsFiniteMeasure
          ((volume : Measure (↑U → EuclideanSpace ℝ (Fin 3))).restrict Z) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hZfin⟩
      rw [integrable_indicator_iff hZmeas]
      exact integrable_const _
    have hbound : ∀ z : ↑U → EuclideanSpace ℝ (Fin 3),
        ‖(∏ i : ↑U, Work.BoseBoxFock.PV e (x i.1) (z i)) *
            Φ (Function.updateFinset x U z)‖
          ≤ Z.indicator (fun _ => K ^ U.card * C) z := by
      intro z
      by_cases hzZ : z ∈ Z
      · rw [Set.indicator_of_mem hzZ]
        have hPV : ∀ i : ↑U, ‖Work.BoseBoxFock.PV e (x i.1) (z i)‖ ≤ K := by
          intro i
          calc ‖Work.BoseBoxFock.PV e (x i.1) (z i)‖
              = ‖∑ l : Fin m, e l (x i.1) * star (e l (z i))‖ := rfl
            _ ≤ ∑ l : Fin m, ‖e l (x i.1) * star (e l (z i))‖ := norm_sum_le _ _
            _ = ∑ l : Fin m, ‖e l (x i.1)‖ * ‖e l (z i)‖ := by
                simp only [norm_mul, norm_star]
            _ ≤ ∑ l : Fin m, Bl l * Bl l := Finset.sum_le_sum (fun l _ =>
                  mul_le_mul (hBl l (x i.1)) (hBl l (z i)) (norm_nonneg _) (hBlnn l))
            _ = K := hKdef.symm
        have hprodK : (∏ i : ↑U, ‖Work.BoseBoxFock.PV e (x i.1) (z i)‖) ≤ ∏ _ : ↑U, K :=
          Finset.prod_le_prod₀ (s := Finset.univ)
            (f := fun i : ↑U => ‖Work.BoseBoxFock.PV e (x i.1) (z i)‖)
            (g := fun _ : ↑U => K) (fun i _ => norm_nonneg _) (fun i _ => hPV i)
        calc ‖(∏ i : ↑U, Work.BoseBoxFock.PV e (x i.1) (z i)) *
              Φ (Function.updateFinset x U z)‖
            = (∏ i : ↑U, ‖Work.BoseBoxFock.PV e (x i.1) (z i)‖) *
                ‖Φ (Function.updateFinset x U z)‖ := by rw [norm_mul, norm_prod]
          _ ≤ (∏ _ : ↑U, K) * C := mul_le_mul hprodK
                ((hCΦ _).trans (le_max_left _ _)) (norm_nonneg _)
                (Finset.prod_nonneg (fun i _ => hKnn))
          _ = K ^ U.card * C := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
      · rw [Set.indicator_of_notMem hzZ]
        have hzex : ∃ i : ↑U, z i ∉ Work.BoseK15.corpusBox.boxL ℓ := by
          by_contra h
          exact hzZ (by
            rw [hZdef, Set.mem_univ_pi]
            intro i
            exact not_not.mp (not_exists.mp h i))
        obtain ⟨i, hi⟩ := hzex
        have hzero : Work.BoseBoxFock.PV e (x i.1) (z i) = 0 :=
          Work.BoseBoxFock.PV_eq_zero_of_factors e (fun l => by
            by_contra hne
            exact hi (hsupp l (Function.mem_support.mpr hne)))
        rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero, zero_mul, norm_zero]
    calc ‖Work.BoseBoxFock.slotInt e U Φ x‖
        = ‖∫ z : ↑U → EuclideanSpace ℝ (Fin 3),
              (∏ i : ↑U, Work.BoseBoxFock.PV e (x i.1) (z i)) *
                Φ (Function.updateFinset x U z)‖ := rfl
      _ ≤ ∫ z : ↑U → EuclideanSpace ℝ (Fin 3),
            ‖(∏ i : ↑U, Work.BoseBoxFock.PV e (x i.1) (z i)) *
              Φ (Function.updateFinset x U z)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z : ↑U → EuclideanSpace ℝ (Fin 3),
            Z.indicator (fun _ => K ^ U.card * C) z :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _) hgint
            (Filter.Eventually.of_forall hbound)
      _ = (volume Z).toReal * (K ^ U.card * C) := by
          rw [integral_indicator_const _ hZmeas, Measure.real, smul_eq_mul]

end Work.MB
