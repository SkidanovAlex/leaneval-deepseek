import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.SlotProjAux
import Submission.Work.BoseK15.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MB

open MeasureTheory

set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
## The weak-mode inputs of the one-slot idempotence

The measurable/bounded ("weak") line of the box ↔ model bridge replaces the *continuous*,
*compactly supported* mode hypotheses of the strong chain by

* `Measurable (e l)`,
* `∃ C, ∀ x, ‖e l x‖ ≤ C` (everywhere bounded),
* `Function.support (e l) ⊆ boxL ℓ` (supported in the corpus box),

and the state hypotheses by measurability and everywhere boundedness.  The four lemmas below
isolate exactly what the idempotence computation needs in this weaker setting: the uniform bound
of the projection kernel `PV e`, its vanishing in the second variable off the box, its joint
measurability, and the integrability of the mode overlaps (the `hint` input of
`Work.BoseBoxFock.integral_PV_mul_PV`).
-/

/-- The projection kernel of everywhere bounded modes is uniformly bounded. -/
theorem PV_weak_idem_bound {m : ℕ} {e : Fin m → ℝ³ → ℂ}
    (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a w : ℝ³, ‖Work.BoseBoxFock.PV e a w‖ ≤ K := by
  classical
  choose Bl hBl using hbdE
  have hBl0 : ∀ l, 0 ≤ Bl l := fun l => (norm_nonneg (e l 0)).trans (hBl l 0)
  refine ⟨∑ l : Fin m, Bl l * Bl l,
    Finset.sum_nonneg fun l _ => mul_nonneg (hBl0 l) (hBl0 l), fun a w => ?_⟩
  calc ‖Work.BoseBoxFock.PV e a w‖
      = ‖∑ l : Fin m, e l a * star (e l w)‖ := rfl
    _ ≤ ∑ l : Fin m, ‖e l a * star (e l w)‖ := norm_sum_le _ _
    _ = ∑ l : Fin m, ‖e l a‖ * ‖e l w‖ := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [norm_mul, norm_star]
    _ ≤ ∑ l : Fin m, Bl l * Bl l :=
          Finset.sum_le_sum fun l _ => mul_le_mul (hBl l a) (hBl l w) (norm_nonneg _) (hBl0 l)

/-- The projection kernel vanishes in its second variable outside the box. -/
theorem PV_weak_idem_eq_zero {m : ℕ} {ℓ : ℝ} {e : Fin m → ℝ³ → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {a w : ℝ³} (hw : w ∉ Work.BoseK15.corpusBox.boxL ℓ) :
    Work.BoseBoxFock.PV e a w = 0 := by
  refine Work.BoseBoxFock.PV_eq_zero_of_factors e (fun l => ?_)
  by_contra h
  exact hw (hsupp l h)

/-- The projection kernel is jointly measurable in its two arguments. -/
theorem PV_weak_idem_measurable {m : ℕ} {e : Fin m → ℝ³ → ℂ} (hmeas : ∀ l, Measurable (e l)) :
    Measurable (fun p : ℝ³ × ℝ³ => Work.BoseBoxFock.PV e p.1 p.2) := by
  have hfun : (fun p : ℝ³ × ℝ³ => Work.BoseBoxFock.PV e p.1 p.2)
      = fun p : ℝ³ × ℝ³ => ∑ l : Fin m, e l p.1 * star (e l p.2) := rfl
  rw [hfun]
  exact Finset.measurable_sum _ (fun l _ => ((hmeas l).comp measurable_fst).mul
    (continuous_star.measurable.comp ((hmeas l).comp measurable_snd)))

/-- The mode overlaps `star (e l z) * e l' z` are integrable for weak box-supported modes:
they are measurable, everywhere bounded, and vanish off the finite-measure box `boxL ℓ`. -/
theorem PV_weak_idem_integrable_overlaps {m : ℕ} {ℓ : ℝ} {e : Fin m → ℝ³ → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    ∀ l l' : Fin m, Integrable (fun z : ℝ³ => star (e l z) * e l' z) volume := by
  classical
  choose Bl hBl using hbdE
  have hBl0 : ∀ l, 0 ≤ Bl l := fun l => (norm_nonneg (e l 0)).trans (hBl l 0)
  intro l l'
  have hfmeas : Measurable (fun z : ℝ³ => star (e l z) * e l' z) :=
    (continuous_star.measurable.comp (hmeas l)).mul (hmeas l')
  have hf0 : ∀ z : ℝ³, z ∉ Work.BoseK15.corpusBox.boxL ℓ → star (e l z) * e l' z = 0 := by
    intro z hz
    by_contra h
    obtain ⟨-, h2⟩ := mul_ne_zero_iff.mp h
    exact hz (hsupp l' h2)
  refine Integrable.mono'
    (g := (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ : ℝ³ => Bl l * Bl l'))
    ?_ hfmeas.aestronglyMeasurable ?_
  · rw [integrable_indicator_iff (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)]
    exact integrableOn_const (C := Bl l * Bl l')
      (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
  · refine Filter.Eventually.of_forall fun z => ?_
    by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ
    · rw [Set.indicator_of_mem hz, norm_mul, norm_star]
      exact mul_le_mul (hBl l z) (hBl l' z) (norm_nonneg _) (hBl0 l)
    · rw [Set.indicator_of_notMem hz, hf0 z hz, norm_zero]

/-- **Idempotence of the single-slot projection, for weak modes.**

The modes `e l` are only assumed measurable, *everywhere* bounded and supported in the box
`boxL ℓ` (no `Continuous`/`HasCompactSupport`), the state `Φ` only measurable and everywhere
bounded.  Then `slotProj1 e i (slotProj1 e i Φ) = slotProj1 e i Φ`, where
`slotProj1 e i Φ x = ∫ w, PV e (x i) w * Φ (Function.update x i w)`.

Proof sketch (mirror of `Work.BoseBoxFock.slotProj1_idemMB`, which assumes continuous compactly
supported modes).  Unfold both sides at a fixed `x`; rewrite with
`Function.update_self`/`Function.update_idem`; turn `∫ w, PV (x i) w * (∫ v, f w v)` into
`∫ w, ∫ v, PV (x i) w * f w v` with `integral_const_mul` (hypothesis-free for Bochner integrals);
swap with `MeasureTheory.integral_integral_swap`, and the required
`Integrable (Function.uncurry fun w v ↦ PV e (x i) w * (PV e w v * Φ (Function.update x i v)))`
holds because that integrand is (honestly) measurable and supported in the compact set
`boxL ℓ ×ˢ boxL ℓ` (`PV e (x i) ·` and `PV e · ·` both vanish pointwise off `⋃ l, support (e l)`,
use `hsupp`) where it is bounded — so it is dominated by
`(boxL ℓ ×ˢ boxL ℓ).indicator (fun _ => K * C)` with `K = ∑ l, Bl l * Bl l`, `C` a bound for `Φ`
(`Integrable.mono'` + `integrable_indicator_iff` + `integrableOn_const`, the product set having
finite measure).  Finally compute the inner integral with `integral_mul_const` (again
hypothesis-free) and `Work.BoseBoxFock.integral_PV_mul_PV e horth hint (x i) v`, where
`hint : ∀ l l', Integrable (fun z => star (e l z) * e l' z)` follows from `hmeas`, `hbdE`, `hsupp`
(the function is measurable, bounded, and pointwise supported in the finite-measure set
`boxL ℓ`). -/
theorem slotProj1_idem_weak {m N : ℕ} {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    {Φ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ} (hΦm : Measurable Φ)
    (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) (i : Fin N) :
    Work.BoseBoxFock.slotProj1 e i (Work.BoseBoxFock.slotProj1 e i Φ)
      = Work.BoseBoxFock.slotProj1 e i Φ := by
  classical
  set B : Set ℝ³ := Work.BoseK15.corpusBox.boxL ℓ with hB
  have hBmeas : MeasurableSet B := by
    rw [hB]; exact Work.BoseK15.corpusBox.boxL_measurableSet ℓ
  have hBfin : volume B ≠ ⊤ := by
    rw [hB]; exact (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
  obtain ⟨K, hK0, hPVbd⟩ := PV_weak_idem_bound hbdE
  have hPV0 : ∀ a w : ℝ³, w ∉ B → Work.BoseBoxFock.PV e a w = 0 := by
    intro a w hw
    exact PV_weak_idem_eq_zero hsupp hw
  obtain ⟨CΦ, hCΦ⟩ := hΦb
  have hPVpair : Measurable (fun p : ℝ³ × ℝ³ => Work.BoseBoxFock.PV e p.1 p.2) :=
    PV_weak_idem_measurable hmeas
  have hint : ∀ l l' : Fin m, Integrable (fun z : ℝ³ => star (e l z) * e l' z) volume :=
    PV_weak_idem_integrable_overlaps hmeas hbdE hsupp
  -- the product box has finite measure
  have hvolB2 : volume (B ×ˢ B) ≠ ⊤ := by
    have h2 : ((volume : Measure ℝ³).prod (volume : Measure ℝ³) : Measure (ℝ³ × ℝ³)) (B ×ˢ B)
        = volume B * volume B := Measure.prod_prod B B
    rw [show (volume : Measure (ℝ³ × ℝ³)) (B ×ˢ B) = volume B * volume B from h2]
    exact ENNReal.mul_ne_top hBfin hBfin
  funext x
  have hupd : Measurable (fun p : ℝ³ × ℝ³ => Function.update x i p.2) := by
    refine measurable_pi_iff.mpr (fun j => ?_)
    by_cases hj : j = i
    · subst hj
      simpa [Function.update_self] using (measurable_snd : Measurable (fun p : ℝ³ × ℝ³ => p.2))
    · simp [Function.update_of_ne hj]
  have hPVsnd : Measurable (fun w : ℝ³ => Work.BoseBoxFock.PV e (x i) w) := by
    have hfun : (fun w : ℝ³ => Work.BoseBoxFock.PV e (x i) w)
        = fun w : ℝ³ => ∑ l : Fin m, e l (x i) * star (e l w) := rfl
    rw [hfun]
    exact Finset.measurable_sum _ (fun l _ => measurable_const.mul
      (continuous_star.measurable.comp (hmeas l)))
  have hGmeas : Measurable (fun p : ℝ³ × ℝ³ => Work.BoseBoxFock.PV e (x i) p.1 *
      (Work.BoseBoxFock.PV e p.1 p.2 * Φ (Function.update x i p.2))) :=
    (hPVsnd.comp measurable_fst).mul (hPVpair.mul (hΦm.comp hupd))
  have hGbound : ∀ p : ℝ³ × ℝ³,
      ‖Work.BoseBoxFock.PV e (x i) p.1 * (Work.BoseBoxFock.PV e p.1 p.2 *
        Φ (Function.update x i p.2))‖
      ≤ (B ×ˢ B).indicator (fun _ : ℝ³ × ℝ³ => K * (K * CΦ)) p := by
    intro p
    by_cases hp : p ∈ B ×ˢ B
    · rw [Set.indicator_of_mem hp, norm_mul, norm_mul]
      exact mul_le_mul (hPVbd _ _)
        (mul_le_mul (hPVbd _ _) (hCΦ _) (norm_nonneg _) hK0)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hK0
    · rw [Set.indicator_of_notMem hp]
      have hp' : p.1 ∈ B → p.2 ∉ B := by rwa [Set.mem_prod, not_and] at hp
      have hz : Work.BoseBoxFock.PV e (x i) p.1 * (Work.BoseBoxFock.PV e p.1 p.2 *
          Φ (Function.update x i p.2)) = 0 := by
        by_cases h1 : p.1 ∈ B
        · rw [hPV0 p.1 p.2 (hp' h1), zero_mul, mul_zero]
        · rw [hPV0 (x i) p.1 h1, zero_mul]
      rw [hz, norm_zero]
  have hmaj : Integrable ((B ×ˢ B).indicator (fun _ : ℝ³ × ℝ³ => K * (K * CΦ))) volume := by
    rw [integrable_indicator_iff (hBmeas.prod hBmeas)]
    exact integrableOn_const (C := K * (K * CΦ)) hvolB2
  have hInt : Integrable (fun p : ℝ³ × ℝ³ => Work.BoseBoxFock.PV e (x i) p.1 *
      (Work.BoseBoxFock.PV e p.1 p.2 * Φ (Function.update x i p.2))) volume :=
    Integrable.mono' hmaj hGmeas.aestronglyMeasurable (Filter.Eventually.of_forall hGbound)
  have hstep : ∀ w : ℝ³, Work.BoseBoxFock.slotProj1 e i Φ (Function.update x i w)
      = ∫ v, Work.BoseBoxFock.PV e w v * Φ (Function.update x i v) := by
    intro w
    rw [Work.BoseBoxFock.slotProj1]
    apply integral_congr_ae
    filter_upwards with v
    rw [Function.update_self, Function.update_idem]
  have hinner : ∀ v : ℝ³, ∫ w, Work.BoseBoxFock.PV e (x i) w *
        (Work.BoseBoxFock.PV e w v * Φ (Function.update x i v))
      = Work.BoseBoxFock.PV e (x i) v * Φ (Function.update x i v) := by
    intro v
    have hassoc : (fun w : ℝ³ => Work.BoseBoxFock.PV e (x i) w *
          (Work.BoseBoxFock.PV e w v * Φ (Function.update x i v)))
        = (fun w : ℝ³ => (Work.BoseBoxFock.PV e (x i) w * Work.BoseBoxFock.PV e w v) *
            Φ (Function.update x i v)) := by
      funext w; ring
    rw [hassoc, integral_mul_const,
      Work.BoseBoxFock.integral_PV_mul_PV e horth hint (x i) v]
  have hIntu : Integrable (Function.uncurry (fun w v : ℝ³ => Work.BoseBoxFock.PV e (x i) w *
      (Work.BoseBoxFock.PV e w v * Φ (Function.update x i v)))) volume := hInt
  have hswap := integral_integral_swap hIntu
  calc Work.BoseBoxFock.slotProj1 e i (Work.BoseBoxFock.slotProj1 e i Φ) x
      = ∫ w, Work.BoseBoxFock.PV e (x i) w *
          (Work.BoseBoxFock.slotProj1 e i Φ (Function.update x i w)) := rfl
    _ = ∫ w, Work.BoseBoxFock.PV e (x i) w *
          (∫ v, Work.BoseBoxFock.PV e w v * Φ (Function.update x i v)) := by
          apply integral_congr_ae
          filter_upwards with w
          rw [hstep w]
    _ = ∫ w, ∫ v, Work.BoseBoxFock.PV e (x i) w *
          (Work.BoseBoxFock.PV e w v * Φ (Function.update x i v)) := by
          apply integral_congr_ae
          filter_upwards with w
          rw [← integral_const_mul]
    _ = ∫ v, ∫ w, Work.BoseBoxFock.PV e (x i) w *
          (Work.BoseBoxFock.PV e w v * Φ (Function.update x i v)) := hswap
    _ = ∫ v, Work.BoseBoxFock.PV e (x i) v * Φ (Function.update x i v) := by
          apply integral_congr_ae
          filter_upwards with v
          exact hinner v
    _ = Work.BoseBoxFock.slotProj1 e i Φ x := rfl

end Work.MB
