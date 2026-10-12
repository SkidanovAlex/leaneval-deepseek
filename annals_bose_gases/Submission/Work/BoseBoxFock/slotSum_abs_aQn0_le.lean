import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiRowDefs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotSum_abs_aQn0_le` — the slot-sum Cauchy–Schwarz bound

For a continuous state `Φ : X n → ℝ` on the `n`-particle centred box `abox n ℓ` and the slot
mean `Pᵢ = aP ℓ i` (`(PᵢΦ)(x) = ℓ⁻³ ∫_{acube ℓ} Φ(x[i ↦ y]) dy`) with complement `Qᵢ = 1 − Pᵢ`,

    ∑ᵢ ∫_{abox n ℓ} |PᵢΦ| · |Qᵢ (∑ⱼ PⱼΦ)|  ≤  n² ∫_{abox n ℓ} Φ² .

## Mathematical content

Write `‖·‖` for the `L²` norm on `(abox n ℓ, dx)`, `N := ‖Φ‖²` and `Ψ := ∑ⱼ PⱼΦ`.  The whole
content is a two-stage Cauchy–Schwarz.

* **Per slot** (weighted AM–GM, i.e. the sharp `L²` Cauchy–Schwarz in the form
  `ab ≤ (t a² + b²/t)/2` with the optimal weight `t = n`):
  `∫ |PᵢΦ| |QᵢΨ| ≤ (n/2)‖PᵢΦ‖² + (1/(2n))‖QᵢΨ‖²`.
* **Summing** and applying the discrete Cauchy–Schwarz in `i` gives
  `∑ᵢ ∫ |PᵢΦ||QᵢΨ| ≤ √(∑ᵢ ‖PᵢΦ‖²) · √(∑ᵢ ‖QᵢΨ‖²)`, with

  `∑ᵢ ‖PᵢΦ‖² ≤ n N` (`Pᵢ` is an `L²`-contraction, `aP_sq_le`, applied slotwise),
  `∑ᵢ ‖QᵢΨ‖² ≤ n‖Ψ‖² ≤ n·n·∑ⱼ‖PⱼΦ‖² ≤ n³ N` (`Qᵢ` is an `L²`-contraction and
  `‖Ψ‖² ≤ n ∑ⱼ ‖PⱼΦ‖²`).

  Hence the total is at most `√(nN)·√(n³N) = n²N`.  The constant `n²` is exactly the two
  factors `n` coming from (a) the number of slots and (b) the `n` summands of `Ψ`; no slack is
  dropped.  (The `n = 0` case is vacuous.)

## Route in this file

* `aQn0_aQ_sq_le_box` — `Qᵢ = 1 − Pᵢ` is an `L²`-contraction on the box
  (Pythagoras: `∫(QᵢG)² = ∫G² − 2∫(PᵢG)(QᵢG) − ∫(PᵢG)² = ∫G² − ∫(PᵢG)²`, using the
  self-adjointness `aP_sym_box` and the orthogonality `aQ_ortho_box`).
* `aQn0_abs_mul_le` — the weighted AM–GM `∫|F||G| ≤ (n/2)∫F² + (1/(2n))∫G²`.
* `aQn0_sum_sq_le` — `∫Ψ² ≤ n ∑ⱼ ∫ (PⱼΦ)²` (`(∑ⱼ aⱼ)² ≤ n ∑ⱼ aⱼ²`, pointwise, integrated).
* `slotSum_abs_aQn0_le` — the assembly.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

open Submission.BoseGases

set_option autoImplicit false

/-- The mean subtraction `Qᵢ = 1 − Pᵢ` is an `L²`-contraction on the centred box:
`∫_{abox} (QᵢG)² ≤ ∫_{abox} G²`.

This is the Pythagorean identity `∫(QᵢG)² = ∫G² − ∫(PᵢG)²` together with the nonnegativity of
the second term; the structural inputs are the box projection algebra (`aP_sym_box`,
`aQ_ortho_box`, `aP_idem`). -/
theorem aQn0_aQ_sq_le_box {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {G : X n → ℝ}
    (hGc : Continuous G) :
    (∫ x in abox n ℓ, (aQ ℓ i G x) ^ 2) ≤ ∫ x in abox n ℓ, (G x) ^ 2 := by
  have hPc : Continuous (aP ℓ i G) := aP_continuous hℓ i hGc
  have hQc : Continuous (aQ ℓ i G) := hGc.sub hPc
  have hI1 : Integrable (fun x : X n => (G x) ^ 2) (volume.restrict (abox n ℓ)) :=
    integrableOn_abox_of_continuous hℓ (hGc.pow 2)
  have hI2 : Integrable (fun x : X n => 2 * (aP ℓ i G x * aQ ℓ i G x))
      (volume.restrict (abox n ℓ)) :=
    integrableOn_abox_of_continuous hℓ (continuous_const.mul (hPc.mul hQc))
  have hI3 : Integrable (fun x : X n => (aP ℓ i G x) ^ 2) (volume.restrict (abox n ℓ)) :=
    integrableOn_abox_of_continuous hℓ (hPc.pow 2)
  have hI12 : Integrable (fun x : X n => (G x) ^ 2 - 2 * (aP ℓ i G x * aQ ℓ i G x))
      (volume.restrict (abox n ℓ)) := hI1.sub hI2
  have e1 : (∫ x in abox n ℓ,
        ((G x) ^ 2 - 2 * (aP ℓ i G x * aQ ℓ i G x)) - (aP ℓ i G x) ^ 2)
      = (∫ x in abox n ℓ, ((G x) ^ 2 - 2 * (aP ℓ i G x * aQ ℓ i G x)))
        - (∫ x in abox n ℓ, (aP ℓ i G x) ^ 2) := integral_sub hI12 hI3
  have e2 : (∫ x in abox n ℓ, ((G x) ^ 2 - 2 * (aP ℓ i G x * aQ ℓ i G x)))
      = (∫ x in abox n ℓ, (G x) ^ 2)
        - (∫ x in abox n ℓ, 2 * (aP ℓ i G x * aQ ℓ i G x)) := integral_sub hI1 hI2
  have e3 : (∫ x in abox n ℓ, 2 * (aP ℓ i G x * aQ ℓ i G x))
      = 2 * (∫ x in abox n ℓ, aP ℓ i G x * aQ ℓ i G x) := integral_const_mul 2 _
  have hexp : (∫ x in abox n ℓ, (aQ ℓ i G x) ^ 2)
      = (∫ x in abox n ℓ, (G x) ^ 2)
        - 2 * (∫ x in abox n ℓ, aP ℓ i G x * aQ ℓ i G x)
        - (∫ x in abox n ℓ, (aP ℓ i G x) ^ 2) := by
    rw [show (∫ x in abox n ℓ, (aQ ℓ i G x) ^ 2)
        = ∫ x in abox n ℓ,
            ((G x) ^ 2 - 2 * (aP ℓ i G x * aQ ℓ i G x)) - (aP ℓ i G x) ^ 2 from
      integral_congr_ae (Filter.Eventually.of_forall (fun x : X n => by
        simp only []
        rw [show aQ ℓ i G x = G x - aP ℓ i G x from rfl]
        ring))]
    rw [e1, e2, e3]
  have horth := aQ_ortho_box hℓ i hGc
  have hnn : (0 : ℝ) ≤ ∫ x in abox n ℓ, (aP ℓ i G x) ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  rw [hexp, horth]
  linarith [hnn]

/-- **Weighted AM–GM / sharp `L²` Cauchy–Schwarz on the box.**  For continuous `F`, `G` and
`t > 0`,
`∫_{abox} |F·G| ≤ (t/2) ∫_{abox} F² + (1/(2t)) ∫_{abox} G²`.

The pointwise input is `2 t |F| |G| ≤ t² F² + G²` (i.e. `(t|F| − |G|)² ≥ 0`), integrated
against the finite measure `volume.restrict (abox n ℓ)`; the optimal choice `t = n` in the main
theorem makes the two `L²`-contractions `aP_sq_le` and `aQn0_aQ_sq_le_box` cancel exactly. -/
theorem aQn0_abs_mul_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {F G : X n → ℝ}
    (hFc : Continuous F) (hGc : Continuous G) (ht : (0 : ℝ) < (n : ℝ)) :
    ∫ x in abox n ℓ, |F x| * |G x|
      ≤ ((n : ℝ) / 2) * (∫ x in abox n ℓ, (F x) ^ 2)
        + (1 / (2 * (n : ℝ))) * (∫ x in abox n ℓ, (G x) ^ 2) := by
  have hpt : ∀ x : X n,
      |F x| * |G x| ≤ (n : ℝ) / 2 * (F x) ^ 2 + (1 / (2 * (n : ℝ))) * (G x) ^ 2 := by
    intro x
    have h := (show |F x| * |G x|
        ≤ (n : ℝ) / 2 * |F x| ^ 2 + (1 / (2 * (n : ℝ))) * |G x| ^ 2 from by
      have h2t : (0 : ℝ) < 2 * (n : ℝ) := by linarith
      have key : |F x| * |G x| * (2 * (n : ℝ)) ≤ (n : ℝ) ^ 2 * |F x| ^ 2 + |G x| ^ 2 := by
        nlinarith [sq_nonneg ((n : ℝ) * |F x| - |G x|)]
      calc |F x| * |G x| ≤ ((n : ℝ) ^ 2 * |F x| ^ 2 + |G x| ^ 2) / (2 * (n : ℝ)) :=
            (le_div_iff₀ h2t).mpr key
        _ = (n : ℝ) / 2 * |F x| ^ 2 + (1 / (2 * (n : ℝ))) * |G x| ^ 2 := by field_simp)
    simpa [sq_abs] using h
  have hmaj_int : Integrable
      (fun x : X n => (n : ℝ) / 2 * (F x) ^ 2 + (1 / (2 * (n : ℝ))) * (G x) ^ 2)
      (volume.restrict (abox n ℓ)) :=
    integrableOn_abox_of_continuous hℓ
      ((continuous_const.mul (hFc.pow 2)).add (continuous_const.mul (hGc.pow 2)))
  have hmain := integral_mono_of_nonneg
    (μ := volume.restrict (abox n ℓ))
    (f := fun x : X n => |F x| * |G x|)
    (g := fun x : X n => (n : ℝ) / 2 * (F x) ^ 2 + (1 / (2 * (n : ℝ))) * (G x) ^ 2)
    (Filter.Eventually.of_forall (fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    hmaj_int
    (Filter.Eventually.of_forall hpt)
  have hval : (∫ x in abox n ℓ,
        ((n : ℝ) / 2 * (F x) ^ 2 + (1 / (2 * (n : ℝ))) * (G x) ^ 2))
      = (n : ℝ) / 2 * (∫ x in abox n ℓ, (F x) ^ 2)
        + (1 / (2 * (n : ℝ))) * (∫ x in abox n ℓ, (G x) ^ 2) := by
    rw [MeasureTheory.integral_add (f := fun x : X n => (n : ℝ) / 2 * (F x) ^ 2)
      (g := fun x : X n => (1 / (2 * (n : ℝ))) * (G x) ^ 2)
      (integrableOn_abox_of_continuous hℓ (continuous_const.mul (hFc.pow 2)))
      (integrableOn_abox_of_continuous hℓ (continuous_const.mul (hGc.pow 2)))]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hval] at hmain
  exact hmain

/-- **The `n`-fold sum is an `L²`-bounded superposition of its slot means**:
`∫_{abox} (∑ⱼ PⱼΦ)² ≤ n ∑ⱼ ∫_{abox} (PⱼΦ)²`.

Pointwise this is `(∑ⱼ aⱼ)² ≤ n ∑ⱼ aⱼ²` (`sq_sum_le_card_mul_sum_sq`), integrated against the
finite box measure. -/
theorem aQn0_sum_sq_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X n → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox n ℓ, (∑ j : Fin n, aP ℓ j Φ x) ^ 2)
      ≤ (n : ℝ) * ∑ j : Fin n, (∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2) := by
  set G : Fin n → X n → ℝ := fun j x => (aP ℓ j Φ x) ^ 2 with hG
  have hGc : ∀ j, Continuous (G j) := by
    intro j; rw [hG]; exact (aP_continuous hℓ j hΦc).pow 2
  have hpt : ∀ x : X n, (∑ j : Fin n, aP ℓ j Φ x) ^ 2 ≤ (n : ℝ) * ∑ j : Fin n, G j x := by
    intro x
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun j : Fin n => aP ℓ j Φ x)
    rw [hG]
    simpa using h
  have hmaj_int : Integrable (fun x : X n => (n : ℝ) * ∑ j : Fin n, G j x)
      (volume.restrict (abox n ℓ)) :=
    integrableOn_abox_of_continuous hℓ
      (continuous_const.mul (continuous_finsetSum _ (fun j _ => hGc j)))
  have hmain := integral_mono_of_nonneg (μ := volume.restrict (abox n ℓ))
    (f := fun x : X n => (∑ j : Fin n, aP ℓ j Φ x) ^ 2)
    (g := fun x : X n => (n : ℝ) * ∑ j : Fin n, G j x)
    (Filter.Eventually.of_forall (fun x => sq_nonneg _))
    hmaj_int
    (Filter.Eventually.of_forall hpt)
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finsetSum _ (fun j _ => integrableOn_abox_of_continuous hℓ (hGc j))]
    at hmain
  rw [hG] at hmain
  simpa using hmain

/-- **The slot-sum Cauchy–Schwarz bound** (the target of this file):

    ∑ᵢ ∫_{abox n ℓ} |PᵢΦ| · |Qᵢ (∑ⱼ PⱼΦ)|  ≤  n² ∫_{abox n ℓ} Φ² .

See the module docstring for the proof (per-slot weighted Cauchy–Schwarz with weight `t = n`,
then the two `L²`-contractions `aP_sq_le` and `aQn0_aQ_sq_le_box`, and `aQn0_sum_sq_le`). -/
theorem slotSum_abs_aQn0_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) :
    ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        |Submission.BoseGases.aP ℓ i Φ x| *
          |Submission.BoseGases.aQ ℓ i (fun y : Submission.BoseGases.X n =>
            ∑ j : Fin n, Submission.BoseGases.aP ℓ j Φ y) x|
      ≤ (n : ℝ) ^ 2 * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
  by_cases hn : n = 0
  · subst hn
    simp
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  set Ψ : X n → ℝ := fun y : X n => ∑ j : Fin n, aP ℓ j Φ y with hΨ
  have hΨc : Continuous Ψ := by
    rw [hΨ]; exact continuous_finsetSum _ (fun j _ => aP_continuous hℓ j hΦc)
  have hQcont : ∀ i : Fin n, Continuous (aQ ℓ i Ψ) :=
    fun i => hΨc.sub (aP_continuous hℓ i hΨc)
  -- per-slot weighted bound
  have hA : ∀ i : Fin n,
      ∫ x in abox n ℓ, |aP ℓ i Φ x| * |aQ ℓ i Ψ x|
        ≤ ((n : ℝ) / 2) * (∫ x in abox n ℓ, (aP ℓ i Φ x) ^ 2)
          + (1 / (2 * (n : ℝ))) * (∫ x in abox n ℓ, (aQ ℓ i Ψ x) ^ 2) :=
    fun i => aQn0_abs_mul_le hℓ (aP_continuous hℓ i hΦc) (hQcont i) hnpos
  -- `∑ᵢ ‖PᵢΦ‖² ≤ n ‖Φ‖²`
  have hB : ∑ i : Fin n, (∫ x in abox n ℓ, (aP ℓ i Φ x) ^ 2)
      ≤ (n : ℝ) * (∫ x in abox n ℓ, (Φ x) ^ 2) := by
    calc ∑ i : Fin n, (∫ x in abox n ℓ, (aP ℓ i Φ x) ^ 2)
        ≤ ∑ _i : Fin n, (∫ x in abox n ℓ, (Φ x) ^ 2) :=
          Finset.sum_le_sum (fun i _ => aP_sq_le hℓ i hΦc)
      _ = (n : ℝ) * (∫ x in abox n ℓ, (Φ x) ^ 2) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  -- `‖Ψ‖² ≤ n ∑ᵢ ‖PᵢΦ‖²`
  have hC : (∫ x in abox n ℓ, (Ψ x) ^ 2)
      ≤ (n : ℝ) * ∑ i : Fin n, (∫ x in abox n ℓ, (aP ℓ i Φ x) ^ 2) := by
    rw [hΨ]
    exact aQn0_sum_sq_le hℓ hΦc
  -- `∑ᵢ ‖QᵢΨ‖² ≤ n ‖Ψ‖²`
  have hD : ∑ i : Fin n, (∫ x in abox n ℓ, (aQ ℓ i Ψ x) ^ 2)
      ≤ (n : ℝ) * (∫ x in abox n ℓ, (Ψ x) ^ 2) := by
    calc ∑ i : Fin n, (∫ x in abox n ℓ, (aQ ℓ i Ψ x) ^ 2)
        ≤ ∑ _i : Fin n, (∫ x in abox n ℓ, (Ψ x) ^ 2) :=
          Finset.sum_le_sum (fun i _ => aQn0_aQ_sq_le_box hℓ i hΨc)
      _ = (n : ℝ) * (∫ x in abox n ℓ, (Ψ x) ^ 2) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have hMN : (∫ x in abox n ℓ, (Ψ x) ^ 2)
      ≤ (n : ℝ) * ((n : ℝ) * (∫ x in abox n ℓ, (Φ x) ^ 2)) := by
    refine le_trans hC ?_
    exact mul_le_mul_of_nonneg_left hB (by positivity)
  calc ∑ i : Fin n, ∫ x in abox n ℓ, |aP ℓ i Φ x| * |aQ ℓ i Ψ x|
      ≤ ∑ i : Fin n, (((n : ℝ) / 2) * (∫ x in abox n ℓ, (aP ℓ i Φ x) ^ 2)
          + (1 / (2 * (n : ℝ))) * (∫ x in abox n ℓ, (aQ ℓ i Ψ x) ^ 2)) :=
        Finset.sum_le_sum (fun i _ => hA i)
    _ = ((n : ℝ) / 2) * (∑ i : Fin n, (∫ x in abox n ℓ, (aP ℓ i Φ x) ^ 2))
        + (1 / (2 * (n : ℝ))) * (∑ i : Fin n, (∫ x in abox n ℓ, (aQ ℓ i Ψ x) ^ 2)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ ((n : ℝ) / 2) * ((n : ℝ) * (∫ x in abox n ℓ, (Φ x) ^ 2))
        + (1 / (2 * (n : ℝ))) * ((n : ℝ) * (∫ x in abox n ℓ, (Ψ x) ^ 2)) := by
        have h1 : ((n : ℝ) / 2) * (∑ i : Fin n, (∫ x in abox n ℓ, (aP ℓ i Φ x) ^ 2))
            ≤ ((n : ℝ) / 2) * ((n : ℝ) * (∫ x in abox n ℓ, (Φ x) ^ 2)) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
        have h2 : (1 / (2 * (n : ℝ))) * (∑ i : Fin n, (∫ x in abox n ℓ, (aQ ℓ i Ψ x) ^ 2))
            ≤ (1 / (2 * (n : ℝ))) * ((n : ℝ) * (∫ x in abox n ℓ, (Ψ x) ^ 2)) :=
          mul_le_mul_of_nonneg_left hD (by positivity)
        linarith
    _ ≤ ((n : ℝ) / 2) * ((n : ℝ) * (∫ x in abox n ℓ, (Φ x) ^ 2))
        + (1 / (2 * (n : ℝ)))
            * ((n : ℝ) * ((n : ℝ) * ((n : ℝ) * (∫ x in abox n ℓ, (Φ x) ^ 2)))) := by
        have h4 : (1 / (2 * (n : ℝ))) * ((n : ℝ) * (∫ x in abox n ℓ, (Ψ x) ^ 2))
            ≤ (1 / (2 * (n : ℝ)))
                * ((n : ℝ) * ((n : ℝ) * ((n : ℝ) * (∫ x in abox n ℓ, (Φ x) ^ 2)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMN (by positivity))
            (by positivity)
        linarith
    _ = (n : ℝ) ^ 2 * ∫ x in abox n ℓ, (Φ x) ^ 2 := by
        field_simp
        ring

end Work.BoseBoxFock
