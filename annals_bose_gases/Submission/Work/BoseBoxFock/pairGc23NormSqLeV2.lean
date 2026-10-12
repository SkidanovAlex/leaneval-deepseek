import Mathlib
import Submission.Work.BoseBoxFock.pairGc23Aux
import Submission.Work.BoseBoxFock.pairGc23_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.BoseBoxFock.pairGc23NormSqLeV2` — the `L²` (Cauchy–Schwarz) bound for the `pairGc23` fibre

The clean fibre `pairGc23 ℓ p hp Θ₀ A B w y` (`pairGCore`) is the set integral over the product box
`box23 ℓ p` of

    z ↦ (star (Θ₀ (insertCoord2 p w y z.1)) * star (A z.2.1) * star (B z.2.2))
           * Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1) ,

i.e. it is the pairing `∫ f · g` of the two functions

* `f z = star (Θ₀ (insertCoord2 p w y z.1)) * star (A z.2.1) * star (B z.2.2)`,
* `g z = Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)`.

Cauchy–Schwarz in `L²` for the Bochner integral
(`Work.BoseBoxFock.enorm_integral_conj_mul_sq_le`, in `ℝ≥0∞`-`enorm` form, with **no**
integrability hypothesis) gives

    ‖pairGc23 ℓ p hp Θ₀ A B w y‖ₑ² ≤ (∫⁻ ‖f‖²) · (∫⁻ ‖g‖²) ,

and the two quadratic integrals are evaluated as follows:

* `∫⁻ ‖g‖² = ENNReal.ofReal (pinL2 ℓ Θ₀)`: the measure preserving insertion `splitEquiv` carries
  the box `box23 ℓ p` onto the `n`-particle box `abox n ℓ`
  (`Work.BoseBoxFock.integral_second_eq_pinL2`, `Work.BoseBoxFock.lintegral_box23_snd_sq`);
* `∫⁻ ‖f‖² ≤ ENNReal.ofReal (cA²·cB²·ℓ⁶·memX23 ℓ p Θ₀ w y)`: pointwise `‖f z‖² ≤ cA²cB²·‖Θ₀ ‖²`,
  and the Fubini identity `Work.BoseBoxFock.lintegral_box23_fst_sq` evaluates the `(w,y)`-slice
  mass over the box as `ℓ⁶ · memX23 ℓ p Θ₀ w y` (the `ℓ⁶` is the volume of the two kernel boxes).

`sorry`-free.
-/

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-! ## 1. The two box identities -/

/-- **The `(w,y)`-slice mass over the box is `memX23 · ℓ⁶`.**

This is the already-proved `setIntegral_first_eq` (`pairGc23_aux`) at the constant kernels
`A = B = 1`: it evaluates the Fubini integral of a function of `z.1` only, the two kernel boxes
`boxL ℓ` contributing the volume `ℓ⁶`. -/
private lemma box23_integral_state_sq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {Θ₀ : Xn n → ℂ} (w y : E3) :
    (∫ z in box23 ℓ p, ‖Θ₀ (insertCoord2 p w y z.1)‖ ^ 2) = memX23 ℓ p Θ₀ w y * ℓ ^ 6 := by
  have hbox : (∫ a in Work.BoseK15.corpusBox.boxL ℓ, (1 : ℝ)) = ℓ ^ 3 := by
    rw [MeasureTheory.setIntegral_const, Measure.real, ofReal_volume_boxL ℓ hℓ,
      ENNReal.toReal_ofReal (by positivity)]
    simp
  have h := setIntegral_first_eq (ℓ := ℓ) (p := p) Θ₀ (fun _ : E3 => (1 : ℂ))
    (fun _ : E3 => (1 : ℂ)) w y
  simp only [norm_one, one_pow, mul_one] at h
  rw [hbox] at h
  rw [h]
  ring

/-- **The `ℝ≥0∞`-form of `box23_integral_state_sq`**: the `lintegral` of
`ENNReal.ofReal ‖Θ₀ (insertCoord2 p w y z.1)‖²` over the box is
`ENNReal.ofReal (ℓ⁶) · ENNReal.ofReal (memX23 ℓ p Θ₀ w y)`. -/
private theorem lintegral_box23_fst_sq' {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {Θ₀ : Xn n → ℂ} (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (w y : E3) :
    (∫⁻ z in box23 ℓ p, ENNReal.ofReal (‖Θ₀ (insertCoord2 p w y z.1)‖ ^ 2))
      = ENNReal.ofReal (ℓ ^ 6) * ENNReal.ofReal (memX23 ℓ p Θ₀ w y) := by
  have hmem0 : (0 : ℝ) ≤ memX23 ℓ p Θ₀ w y := integral_nonneg fun x => by positivity
  have hint : IntegrableOn (fun z : (Fib23 n p → E3) × (E3 × E3) =>
      ‖Θ₀ (insertCoord2 p w y z.1)‖ ^ 2) (box23 ℓ p) :=
    (((hΘ₀.continuous.comp ((continuous_insertCoord2_fixed_pg23 p w y).comp
      continuous_fst)).norm.pow 2).continuousOn).integrableOn_compact (isCompact_box23 hℓ p)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun z => by positivity)]
  rw [show (∫ z, ‖Θ₀ (insertCoord2 p w y z.1)‖ ^ 2 ∂(volume.restrict (box23 ℓ p)))
      = memX23 ℓ p Θ₀ w y * ℓ ^ 6 from box23_integral_state_sq hℓ p w y]
  rw [ENNReal.ofReal_mul hmem0]
  exact mul_comm _ _

/-- **The `ℝ≥0∞`-form of the `pinL2`-identity** `integral_second_eq_pinL2` (`pairGc23_aux`): the
`lintegral` of `ENNReal.ofReal ‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖²` over the box is
`ENNReal.ofReal (pinL2 ℓ Θ₀)`. -/
private theorem lintegral_box23_snd_sq' {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    (hp : p.1 ≠ p.2)
    {Θ₀ : Xn n → ℂ} (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) :
    (∫⁻ z in box23 ℓ p, ENNReal.ofReal (‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖ ^ 2))
      = ENNReal.ofReal (pinL2 ℓ Θ₀) := by
  have hint : IntegrableOn (fun z : (Fib23 n p → E3) × (E3 × E3) =>
      ‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖ ^ 2) (box23 ℓ p) :=
    (((hΘ₀.continuous.comp (continuous_insertCoord2_joint_pg23 p)).norm.pow 2).continuousOn).integrableOn_compact
      (isCompact_box23 hℓ p)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun z => by positivity)]
  rw [show (∫ z, ‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖ ^ 2 ∂(volume.restrict (box23 ℓ p)))
      = pinL2 ℓ Θ₀ from integral_second_eq_pinL2 hℓ hp Θ₀]

/-! ## 2. The bound on the `(w, A, B)`-factor -/

/-- **The `ℝ≥0∞`-integral of `‖f‖²` over the box**, for the `(w, A, B)`-factor
`f z = star (Θ₀ (insertCoord2 p w y z.1)) * star (A z.2.1) * star (B z.2.2)`.

The pointwise bound `‖f z‖² ≤ cA²cB²·‖Θ₀ (insertCoord2 p w y z.1)‖²` (`norm_first_factor_sq`)
together with the Fubini identity `lintegral_box23_fst_sq` gives exactly the `A`/`B`-bookkeeping
`cA²·cB²·ℓ⁶·memX23`. -/
private lemma lintegral_box23_first_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {Θ₀ : Xn n → ℂ} (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    {A B : E3 → ℂ} {cA cB : ℝ} (hAb : ∀ x, ‖A x‖ ≤ cA) (hBb : ∀ x, ‖B x‖ ≤ cB)
    (w y : E3) :
    (∫⁻ z in box23 ℓ p,
        ENNReal.ofReal (‖star (Θ₀ (insertCoord2 p w y z.1)) * star (A z.2.1)
          * star (B z.2.2)‖ ^ 2))
      ≤ ENNReal.ofReal (cA ^ 2 * cB ^ 2 * ℓ ^ 6 * memX23 ℓ p Θ₀ w y) := by
  have hmeas : AEMeasurable (fun z : (Fib23 n p → E3) × (E3 × E3) =>
      ENNReal.ofReal (‖Θ₀ (insertCoord2 p w y z.1)‖ ^ 2))
      (volume.restrict (box23 ℓ p)) :=
    (((hΘ₀.continuous.comp ((continuous_insertCoord2_fixed_pg23 p w y).comp
      continuous_fst)).norm.pow 2).measurable.ennreal_ofReal).aemeasurable
  have hpt : ∀ z : (Fib23 n p → E3) × (E3 × E3),
      ENNReal.ofReal (‖star (Θ₀ (insertCoord2 p w y z.1)) * star (A z.2.1)
          * star (B z.2.2)‖ ^ 2)
        ≤ ENNReal.ofReal (cA ^ 2 * cB ^ 2)
            * ENNReal.ofReal (‖Θ₀ (insertCoord2 p w y z.1)‖ ^ 2) := by
    intro z
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ cA ^ 2 * cB ^ 2)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_first_factor_sq]
    have h1 : ‖A z.2.1‖ ^ 2 ≤ cA ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hAb _) 2
    have h2 : ‖B z.2.2‖ ^ 2 ≤ cB ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hBb _) 2
    have h3 : ‖A z.2.1‖ ^ 2 * ‖B z.2.2‖ ^ 2 ≤ cA ^ 2 * cB ^ 2 :=
      mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)
    calc ‖Θ₀ (insertCoord2 p w y z.1)‖ ^ 2 * (‖A z.2.1‖ ^ 2 * ‖B z.2.2‖ ^ 2)
        ≤ ‖Θ₀ (insertCoord2 p w y z.1)‖ ^ 2 * (cA ^ 2 * cB ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      _ = cA ^ 2 * cB ^ 2 * ‖Θ₀ (insertCoord2 p w y z.1)‖ ^ 2 := by ring
  calc (∫⁻ z in box23 ℓ p, ENNReal.ofReal (‖star (Θ₀ (insertCoord2 p w y z.1))
          * star (A z.2.1) * star (B z.2.2)‖ ^ 2))
      ≤ ∫⁻ z in box23 ℓ p, ENNReal.ofReal (cA ^ 2 * cB ^ 2)
          * ENNReal.ofReal (‖Θ₀ (insertCoord2 p w y z.1)‖ ^ 2) := lintegral_mono hpt
    _ = ENNReal.ofReal (cA ^ 2 * cB ^ 2)
          * (∫⁻ z in box23 ℓ p,
              ENNReal.ofReal (‖Θ₀ (insertCoord2 p w y z.1)‖ ^ 2)) :=
        lintegral_const_mul'' _ hmeas
    _ = ENNReal.ofReal (cA ^ 2 * cB ^ 2)
          * (ENNReal.ofReal (ℓ ^ 6) * ENNReal.ofReal (memX23 ℓ p Θ₀ w y)) := by
        rw [lintegral_box23_fst_sq' hℓ p hΘ₀ w y]
    _ = ENNReal.ofReal (cA ^ 2 * cB ^ 2 * ℓ ^ 6 * memX23 ℓ p Θ₀ w y) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ℓ ^ 6),
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ cA ^ 2 * cB ^ 2)]
        congr 1
        ring

/-! ## 3. The Cauchy–Schwarz bound -/

theorem pairGc23NormSqLeV2 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ₀ : Work.BoseDict.Xn n → ℂ} {A B : EuclideanSpace ℝ (Fin 3) → ℂ} {cA cB : ℝ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (hA : Measurable A) (hB : Measurable B)
    (hAb : ∀ x, ‖A x‖ ≤ cA) (hBb : ∀ x, ‖B x‖ ≤ cB) (hcA : 0 ≤ cA) (hcB : 0 ≤ cB) :
    ∀ w y : EuclideanSpace ℝ (Fin 3),
      ‖Work.BoseBoxFock.pairGc23 ℓ p hp Θ₀ A B w y‖ ^ 2
        ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * Work.BoseBoxFock.memX23 ℓ p Θ₀ w y
            * Work.BoseBoxFock.pinL2 ℓ Θ₀ := by
  intro w y
  set f : (Fib23 n p → E3) × (E3 × E3) → ℂ :=
    fun z => star (Θ₀ (insertCoord2 p w y z.1)) * star (A z.2.1) * star (B z.2.2)
    with hf
  set g : (Fib23 n p → E3) × (E3 × E3) → ℂ :=
    fun z => Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1) with hg
  set μ : Measure ((Fib23 n p → E3) × (E3 × E3)) :=
    (volume : Measure ((Fib23 n p → E3) × (E3 × E3))).restrict (box23 ℓ p) with hμ
  have hfm : Measurable f := by
    rw [hf]
    have h1 : Measurable (fun z : (Fib23 n p → E3) × (E3 × E3) =>
        Θ₀ (insertCoord2 p w y z.1)) :=
      hΘ₀.continuous.measurable.comp
        (((continuous_insertCoord2_fixed_pg23 p w y).comp continuous_fst).measurable)
    have h2 : Measurable (fun z : (Fib23 n p → E3) × (E3 × E3) => A z.2.1) :=
      hA.comp (continuous_snd.fst).measurable
    have h3 : Measurable (fun z : (Fib23 n p → E3) × (E3 × E3) => B z.2.2) :=
      hB.comp (continuous_snd.snd).measurable
    exact ((Complex.continuous_conj.measurable.comp h1).mul
        (Complex.continuous_conj.measurable.comp h2)).mul
      (Complex.continuous_conj.measurable.comp h3)
  have hgm : Measurable g := by
    rw [hg]
    exact hΘ₀.continuous.measurable.comp (continuous_insertCoord2_joint_pg23 p).measurable
  -- the representation of the fibre as `∫ f · g`
  have hrepr : pairGc23 ℓ p hp Θ₀ A B w y = ∫ z, f z * g z ∂μ := rfl
  -- Cauchy–Schwarz
  have hh1 : (fun z => (starRingEnd ℂ) (star (f z)) * g z) = fun z => f z * g z := by
    funext z
    simp only [starRingEnd_apply, star_star]
  have hh2 : (fun z => ‖star (f z)‖ₑ ^ 2) = fun z => ENNReal.ofReal (‖f z‖ ^ 2) := by
    funext z
    rw [← ofReal_norm, norm_star, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
  have hh3 : (fun z => ‖g z‖ₑ ^ 2) = fun z => ENNReal.ofReal (‖g z‖ ^ 2) := by
    funext z
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
  have hCS : ‖pairGc23 ℓ p hp Θ₀ A B w y‖ₑ ^ 2
      ≤ (∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) ∂μ)
        * (∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2) ∂μ) := by
    have h := enorm_integral_conj_mul_sq_le (μ := μ) (v := fun z => star (f z)) (Λ := g)
      ((Complex.continuous_conj.measurable.comp hfm).aemeasurable) hgm.aemeasurable
    rw [hh1, hh2, hh3] at h
    rw [hrepr]
    exact h
  -- the two quadratic integrals
  have hfirst := lintegral_box23_first_le hℓ p hΘ₀ hAb hBb w y
  have hsecond : (∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2) ∂μ) = ENNReal.ofReal (pinL2 ℓ Θ₀) :=
    lintegral_box23_snd_sq' hℓ p hp hΘ₀
  have hbound : ‖pairGc23 ℓ p hp Θ₀ A B w y‖ₑ ^ 2
      ≤ ENNReal.ofReal (cA ^ 2 * cB ^ 2 * ℓ ^ 6 * memX23 ℓ p Θ₀ w y)
        * ENNReal.ofReal (pinL2 ℓ Θ₀) :=
    hCS.trans (mul_le_mul' hfirst hsecond.le)
  -- positivity of the two real factors
  have hmem0 : (0 : ℝ) ≤ memX23 ℓ p Θ₀ w y := integral_nonneg fun x => by positivity
  have hpin0 : (0 : ℝ) ≤ pinL2 ℓ Θ₀ := integral_nonneg fun x => by positivity
  have hA2 : (0 : ℝ) ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * memX23 ℓ p Θ₀ w y :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (pow_nonneg hℓ.le 6)) hmem0
  have hR : (0 : ℝ) ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * memX23 ℓ p Θ₀ w y * pinL2 ℓ Θ₀ :=
    mul_nonneg hA2 hpin0
  -- unwind the `enorm`/`ofReal` bookkeeping
  have hmain : ENNReal.ofReal (‖pairGc23 ℓ p hp Θ₀ A B w y‖ ^ 2)
      ≤ ENNReal.ofReal
          (cA ^ 2 * cB ^ 2 * ℓ ^ 6 * memX23 ℓ p Θ₀ w y * pinL2 ℓ Θ₀) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
    refine hbound.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul hA2]
  exact (ENNReal.ofReal_le_ofReal_iff hR).mp hmain

end Work.BoseBoxFock

end
