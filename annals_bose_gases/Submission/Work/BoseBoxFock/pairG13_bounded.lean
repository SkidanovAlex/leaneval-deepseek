import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairG_supports
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairG13_bounded` — the fibre `pairG13` is bounded

The fibre function `pairG13 p Θ A B` (step (S2) of `FINDING_PotPairRows_exists.md`) is a *double*
integral: over the fibre `{k // k ≠ p.2} → ℝ³` of the configuration space and over the free
variable `u ∈ ℝ³`.  Both integrations are over spaces of *infinite* volume, so boundedness of the
integrand does not by itself bound the integral: what makes `pairG13` bounded is that the two
integrands vanish off sets of finite measure.

Concretely, with `Λ = boxL ℓ` (`volume Λ < ⊤`) and `Λ^n = boxPow n ℓ`:

* the `u`-integrand has `Θ` evaluated at the configuration whose slot `p.2` is `u`; since `Θ` is
  supported in `boxPow n ℓ`, the integrand vanishes unless `u ∈ Λ`, so the `u`-integral is bounded
  by `‖Θ‖_∞·‖A‖_∞·‖B‖_∞·‖Θ‖_∞·|Λ|` **uniformly in the fibre variable**;
* the resulting function of the fibre variable `x'` is supported in the fibre box
  `Set.univ.pi (fun _ => Λ)`, whose measure is `|Λ|^{#(fibre index)}` (a finite product), because
  `Θ (insertCoord p.2 w x')` vanishes as soon as one coordinate of `x'` leaves `Λ`.

No regularity beyond a.e. measurability, everywhere boundedness and the box support is used
(measurability is in fact not needed for the bounds themselves; the hypotheses are part of the
consumers' bundle).  The bound is completely explicit,
`C = ‖Θ‖_∞‖A‖_∞‖B‖_∞‖Θ‖_∞ · |Λ| · |Λ|^{#fibre}`.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The fibre box `(boxL ℓ)^{#fibre}` is measurable. -/
theorem pairG13_fibBox_measurable {n : ℕ} (p : Fin n × Fin n) (ℓ : ℝ) :
    MeasurableSet (Set.univ.pi (fun _ : {k : Fin n // k ≠ p.2} =>
      Work.BoseK15.corpusBox.boxL ℓ)) :=
  MeasurableSet.univ_pi fun _ => Work.BoseB4.BoxData.boxL_measurableSet _ ℓ

/-- The fibre box `(boxL ℓ)^{#fibre}` has finite volume (the product of the finite volumes of the
one-particle boxes over the fibre index set). -/
theorem pairG13_fibBox_volume_ne_top {n : ℕ} (p : Fin n × Fin n) (ℓ : ℝ) :
    (volume : Measure ({k : Fin n // k ≠ p.2} → E3))
      (Set.univ.pi (fun _ : {k : Fin n // k ≠ p.2} => Work.BoseK15.corpusBox.boxL ℓ)) ≠ ⊤ := by
  have h : (volume : Measure ({k : Fin n // k ≠ p.2} → E3))
      (Set.univ.pi (fun _ : {k : Fin n // k ≠ p.2} => Work.BoseK15.corpusBox.boxL ℓ))
      = ∏ _i : {k : Fin n // k ≠ p.2},
          (volume : Measure E3) (Work.BoseK15.corpusBox.boxL ℓ) := by
    change MeasureTheory.Measure.pi (fun _ : {k : Fin n // k ≠ p.2} => (volume : Measure E3))
      (Set.univ.pi (fun _ : {k : Fin n // k ≠ p.2} => Work.BoseK15.corpusBox.boxL ℓ)) = _
    rw [MeasureTheory.Measure.pi_pi]
  rw [h]
  exact ENNReal.prod_ne_top fun _ _ =>
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top.ne

theorem pairG13_bounded {n : ℕ} {ℓ : ℝ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hAm : Measurable A) (hAb : ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C)
    (hBm : Measurable B) (hBb : ∃ C : ℝ, ∀ x, ‖B x‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w y, ‖pairG13 p Θ A B w y‖ ≤ C := by
  classical
  obtain ⟨CΘ₀, hCΘ₀⟩ := hΘb
  obtain ⟨CA₀, hCA₀⟩ := hAb
  obtain ⟨CB₀, hCB₀⟩ := hBb
  have hCΘ : ∀ x, ‖Θ x‖ ≤ max CΘ₀ 0 := fun x => (hCΘ₀ x).trans (le_max_left _ _)
  have hCA : ∀ x, ‖A x‖ ≤ max CA₀ 0 := fun x => (hCA₀ x).trans (le_max_left _ _)
  have hCB : ∀ x, ‖B x‖ ≤ max CB₀ 0 := fun x => (hCB₀ x).trans (le_max_left _ _)
  have hsmeas : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ) :=
    Work.BoseB4.BoxData.boxL_measurableSet _ ℓ
  have hsfib : (volume : Measure E3) (Work.BoseK15.corpusBox.boxL ℓ) ≠ ⊤ :=
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top.ne
  have hbmeas : MeasurableSet (Set.univ.pi (fun _ : {k : Fin n // k ≠ p.2} =>
      Work.BoseK15.corpusBox.boxL ℓ)) := pairG13_fibBox_measurable p ℓ
  have hbfib : (volume : Measure ({k : Fin n // k ≠ p.2} → E3))
      (Set.univ.pi (fun _ : {k : Fin n // k ≠ p.2} => Work.BoseK15.corpusBox.boxL ℓ)) ≠ ⊤ :=
    pairG13_fibBox_volume_ne_top p ℓ
  refine ⟨max CΘ₀ 0 * max CA₀ 0 * max CB₀ 0 * max CΘ₀ 0 *
      (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal *
      (volume (Set.univ.pi (fun _ : {k : Fin n // k ≠ p.2} =>
        Work.BoseK15.corpusBox.boxL ℓ))).toReal, by positivity, ?_⟩
  intro w y
  -- the `u`-integral is bounded uniformly in the fibre variable `x'`
  have hinner : ∀ x' : {k : Fin n // k ≠ p.2} → E3,
      ‖∫ u : E3, star (Θ (insertCoord p.2 w x')) * A ((insertCoord p.2 w x') p.1)
        * star (B u)
        * Θ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u)‖
      ≤ max CΘ₀ 0 * max CA₀ 0 * max CB₀ 0 * max CΘ₀ 0 *
        (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal := by
    intro x'
    refine (norm_integral_le_integral_norm _).trans ?_
    have hpt : ∀ u : E3,
        ‖star (Θ (insertCoord p.2 w x')) * A ((insertCoord p.2 w x') p.1) * star (B u)
          * Θ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u)‖
        ≤ max CΘ₀ 0 * max CA₀ 0 * max CB₀ 0 * max CΘ₀ 0 *
            ((Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1:ℝ)) u) := by
      intro u
      -- the last `Θ`-factor vanishes off the box (its slot `p.2` is `u`)
      have h4 : ‖Θ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u)‖
          ≤ max CΘ₀ 0 * ((Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1:ℝ)) u) := by
        by_cases hu : u ∈ Work.BoseK15.corpusBox.boxL ℓ
        · rw [Set.indicator_of_mem hu, mul_one]; exact hCΘ _
        · rw [Set.indicator_of_notMem hu, mul_zero]
          have hz : Θ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u) = 0 :=
            theta_eq_zero_of_coord_notMem hΘs (j := p.2)
              (by rw [Function.update_apply, if_pos rfl]; exact hu)
          rw [hz, norm_zero]
      calc ‖star (Θ (insertCoord p.2 w x')) * A ((insertCoord p.2 w x') p.1) * star (B u)
            * Θ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u)‖
          = ‖Θ (insertCoord p.2 w x')‖ * ‖A ((insertCoord p.2 w x') p.1)‖ * ‖B u‖
            * ‖Θ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u)‖ := by
              simp
        _ ≤ max CΘ₀ 0 * max CA₀ 0 * max CB₀ 0 * (max CΘ₀ 0 *
              ((Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1:ℝ)) u)) := by
              gcongr
              · exact hCΘ _
              · exact hCA _
              · exact hCB _
        _ = max CΘ₀ 0 * max CA₀ 0 * max CB₀ 0 * max CΘ₀ 0 *
              ((Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1:ℝ)) u) := by ring
    have hmaj : Integrable (fun u : E3 => max CΘ₀ 0 * max CA₀ 0 * max CB₀ 0 * max CΘ₀ 0 *
        ((Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1:ℝ)) u)) :=
      ((integrable_indicator_iff hsmeas).mpr (integrableOn_const hsfib)).const_mul _
    calc ∫ u : E3, ‖star (Θ (insertCoord p.2 w x')) * A ((insertCoord p.2 w x') p.1)
            * star (B u)
            * Θ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u)‖
        ≤ ∫ u : E3, max CΘ₀ 0 * max CA₀ 0 * max CB₀ 0 * max CΘ₀ 0 *
            ((Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1:ℝ)) u) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _) hmaj
            (Filter.Eventually.of_forall hpt)
      _ = max CΘ₀ 0 * max CA₀ 0 * max CB₀ 0 * max CΘ₀ 0 *
            (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal := by
          rw [MeasureTheory.integral_const_mul,
            MeasureTheory.integral_indicator_const (1:ℝ) hsmeas, MeasureTheory.Measure.real,
            smul_eq_mul, mul_one]
  rw [pairG13]
  -- the fibre integrand vanishes off the fibre box
  have hpt2 : ∀ x' : {k : Fin n // k ≠ p.2} → E3,
      ‖∫ u : E3, star (Θ (insertCoord p.2 w x')) * A ((insertCoord p.2 w x') p.1)
        * star (B u)
        * Θ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u)‖
      ≤ max CΘ₀ 0 * max CA₀ 0 * max CB₀ 0 * max CΘ₀ 0 *
        (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal *
        ((Set.univ.pi (fun _ : {k : Fin n // k ≠ p.2} =>
          Work.BoseK15.corpusBox.boxL ℓ)).indicator (fun _ => (1:ℝ)) x') := by
    intro x'
    by_cases hx : x' ∈ Set.univ.pi (fun _ : {k : Fin n // k ≠ p.2} =>
        Work.BoseK15.corpusBox.boxL ℓ)
    · rw [Set.indicator_of_mem hx, mul_one]; exact hinner x'
    · rw [Set.indicator_of_notMem hx, mul_zero]
      rw [Set.mem_univ_pi] at hx
      obtain ⟨k, hk⟩ := not_forall.mp hx
      have hzk : insertCoord p.2 w x' k.1 = x' k := by rw [insertCoord_eq]; simp [k.2]
      have hz : Θ (insertCoord p.2 w x') = 0 :=
        theta_eq_zero_of_coord_notMem hΘs (j := k.1) (by rw [hzk]; exact hk)
      have hzero : (fun u : E3 => star (Θ (insertCoord p.2 w x')) *
            A ((insertCoord p.2 w x') p.1) * star (B u)
            * Θ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u))
          = fun _ => (0 : ℂ) := by
        funext u; rw [hz]; simp
      rw [hzero]; simp
  have hmaj2 : Integrable (fun x' : {k : Fin n // k ≠ p.2} → E3 =>
      max CΘ₀ 0 * max CA₀ 0 * max CB₀ 0 * max CΘ₀ 0 *
        (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal *
        ((Set.univ.pi (fun _ : {k : Fin n // k ≠ p.2} =>
          Work.BoseK15.corpusBox.boxL ℓ)).indicator (fun _ => (1:ℝ)) x')) :=
    ((integrable_indicator_iff hbmeas).mpr (integrableOn_const hbfib)).const_mul _
  calc ‖∫ x' : {k : Fin n // k ≠ p.2} → E3, ∫ u : E3,
          star (Θ (insertCoord p.2 w x')) * A ((insertCoord p.2 w x') p.1) * star (B u)
          * Θ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u)‖
      ≤ ∫ x' : {k : Fin n // k ≠ p.2} → E3, ‖∫ u : E3,
          star (Θ (insertCoord p.2 w x')) * A ((insertCoord p.2 w x') p.1) * star (B u)
          * Θ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x' : {k : Fin n // k ≠ p.2} → E3, max CΘ₀ 0 * max CA₀ 0 * max CB₀ 0 * max CΘ₀ 0 *
        (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal *
        ((Set.univ.pi (fun _ : {k : Fin n // k ≠ p.2} =>
          Work.BoseK15.corpusBox.boxL ℓ)).indicator (fun _ => (1:ℝ)) x') :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x' => norm_nonneg _) hmaj2
          (Filter.Eventually.of_forall hpt2)
    _ = max CΘ₀ 0 * max CA₀ 0 * max CB₀ 0 * max CΘ₀ 0 *
        (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal *
        (volume (Set.univ.pi (fun _ : {k : Fin n // k ≠ p.2} =>
          Work.BoseK15.corpusBox.boxL ℓ))).toReal := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_indicator_const (1:ℝ) hbmeas, MeasureTheory.Measure.real,
          smul_eq_mul, mul_one]

end Work.BoseBoxFock
