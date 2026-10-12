import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PairGc21Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PairGc21Bounds` — the `L²` and Dirichlet bounds on the clean `pairG21` fibre

The clean fibre

    pairGc21 ℓ p hp Θ₀ A u y
      = ∫ z in triBox ℓ p, star (Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)) * A z.1.1 * A z.1.2
          * Θ₀ (insertCoord2 p y u z.2)

is a Cauchy–Schwarz product of two factors: the `A`-weighted state prefactor (whose `L²`-mass over
the triple box is bounded by `cA⁴ · pinL2 ℓ Θ₀`, by the change of variables
`lintegral_abox_eq_lintegral_triBox`) and the `(y,u)`-dependent factor (whose `L²`-mass is
`ℓ⁶ · memY21 ℓ p Θ₀ y u`, and whose *derivative* mass is `ℓ⁶ · dirY21 ℓ p Θ₀ y u`).  This module
proves the two resulting bounds

* `pairGc21_mass_le` (conjunct 4 of `Work.BoseBoxFock.pairGc21_core`),
* `pairGc21_dir_le_of_fderiv` (conjunct 5, given the parametric derivative formula of
  `Work.BoseBoxFock.pairGc21_fderiv`).

`sorry`-free.
-/

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-- The `A`-weighted state prefactor of the clean `pairG21` fibre. -/
def gc21F {n : ℕ} (p : Fin n × Fin n) (Θ₀ : Xn n → ℂ) (A : E3 → ℂ)
    (z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) : ℂ :=
  star (Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)) * A z.1.1 * A z.1.2

lemma gc21F_eq {n : ℕ} (p : Fin n × Fin n) (Θ₀ : Xn n → ℂ) (A : E3 → ℂ)
    (z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) :
    gc21F p Θ₀ A z = star (Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)) * A z.1.1 * A z.1.2 := rfl

theorem measurable_gc21F {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ₀ : Xn n → ℂ} {A : E3 → ℂ} (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (hA : Measurable A) :
    Measurable (gc21F p Θ₀ A) := by
  have hins : Measurable (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
      insertCoord2 p z.1.1 z.1.2 z.2) := (continuous_insertCoord2 p hp).measurable
  have h1 : Measurable (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
      Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)) := hΘ₀.continuous.measurable.comp hins
  have h2 : Measurable (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
      A z.1.1) := hA.comp (by fun_prop)
  have h3 : Measurable (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
      A z.1.2) := hA.comp (by fun_prop)
  have h : Measurable (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
      star (Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)) * A z.1.1 * A z.1.2) :=
    (((Complex.continuous_conj.measurable.comp h1).mul h2).mul h3)
  exact h

/-- The pointwise bound on the prefactor. -/
theorem norm_gc21F_sq_le {n : ℕ} {p : Fin n × Fin n} {Θ₀ : Xn n → ℂ} {A : E3 → ℂ} {cA : ℝ}
    (hAb : ∀ x, ‖A x‖ ≤ cA) (hcA : 0 ≤ cA)
    (z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) :
    ‖gc21F p Θ₀ A z‖ ^ 2 ≤ cA ^ 4 * ‖Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)‖ ^ 2 := by
  have hnorm : ‖gc21F p Θ₀ A z‖
      = ‖Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)‖ * ‖A z.1.1‖ * ‖A z.1.2‖ := by
    rw [gc21F_eq, norm_mul, norm_mul, norm_star]
  rw [hnorm]
  have ha : ‖A z.1.1‖ ^ 2 ≤ cA ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hAb _) 2
  have hb : ‖A z.1.2‖ ^ 2 ≤ cA ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hAb _) 2
  have hc : (0 : ℝ) ≤ cA ^ 2 := by positivity
  have hstep : ‖A z.1.1‖ ^ 2 * ‖A z.1.2‖ ^ 2 ≤ cA ^ 2 * cA ^ 2 :=
    mul_le_mul ha hb (by positivity) hc
  calc (‖Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)‖ * ‖A z.1.1‖ * ‖A z.1.2‖) ^ 2
      = ‖A z.1.1‖ ^ 2 * ‖A z.1.2‖ ^ 2 * ‖Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)‖ ^ 2 := by ring
    _ ≤ cA ^ 2 * cA ^ 2 * ‖Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hstep (sq_nonneg _)
    _ = cA ^ 4 * ‖Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)‖ ^ 2 := by ring

/-- The measurability of the `(y,u)`-dependent factor. -/
theorem measurable_gc21G {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (y u : E3)
    {Θ₀ : Xn n → ℂ} (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) :
    Measurable (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
      Θ₀ (insertCoord2 p y u z.2)) :=
  hΘ₀.continuous.measurable.comp (by
    rw [show (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
        insertCoord2 p y u z.2)
      = (fun x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3 => insertCoord2 p y u x')
        ∘ Prod.snd from rfl]
    exact (continuous_insertCoord2_fixed p hp y u).comp continuous_snd |>.measurable)

/-- The `ℝ≥0∞`-valued Cauchy–Schwarz bound on the fibre. -/
theorem pairGc21_normSq_le_cs {n : ℕ} {ℓ : ℝ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ₀ : Xn n → ℂ} {A : E3 → ℂ} (u y : E3)
    (hF : Measurable (gc21F p Θ₀ A))
    (hG : Measurable (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
      Θ₀ (insertCoord2 p y u z.2))) :
    ‖pairGc21 ℓ p hp Θ₀ A u y‖ₑ ^ 2
      ≤ (∫⁻ z in triBox ℓ p, ENNReal.ofReal (‖gc21F p Θ₀ A z‖ ^ 2))
        * (∫⁻ z in triBox ℓ p, ENNReal.ofReal (‖Θ₀ (insertCoord2 p y u z.2)‖ ^ 2)) := by
  have hCS := enorm_integral_conj_mul_sq_le (μ := (volume : Measure ((E3 × E3) ×
      ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3))).restrict (triBox ℓ p))
    (v := fun z => star (gc21F p Θ₀ A z))
    (Λ := fun z => Θ₀ (insertCoord2 p y u z.2))
    ((Complex.continuous_conj.measurable.comp hF).aemeasurable) (hG.aemeasurable)
  rw [show (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
        (starRingEnd ℂ) (star (gc21F p Θ₀ A z)) * Θ₀ (insertCoord2 p y u z.2))
      = fun z => gc21F p Θ₀ A z * Θ₀ (insertCoord2 p y u z.2) from by
        funext z; simp only [starRingEnd_apply, star_star]] at hCS
  rw [show (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
        ‖star (gc21F p Θ₀ A z)‖ₑ ^ 2)
      = fun z => ENNReal.ofReal (‖gc21F p Θ₀ A z‖ ^ 2) from by
        funext z
        have h1 : ‖star (gc21F p Θ₀ A z)‖ₑ = ‖gc21F p Θ₀ A z‖ₑ := by
          rw [← ofReal_norm, ← ofReal_norm, norm_star]
        rw [h1, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _) 2]] at hCS
  rw [show (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
        ‖Θ₀ (insertCoord2 p y u z.2)‖ₑ ^ 2)
      = fun z => ENNReal.ofReal (‖Θ₀ (insertCoord2 p y u z.2)‖ ^ 2) from by
        funext z
        rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _) 2]] at hCS
  rw [pairGc21]
  exact hCS

/-- The `L²`-mass of the prefactor over the triple box. -/
theorem lintegral_gc21F_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ₀ : Xn n → ℂ} {A : E3 → ℂ} {cA : ℝ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (hA : Measurable A) (hAb : ∀ x, ‖A x‖ ≤ cA)
    (hcA : 0 ≤ cA) :
    (∫⁻ z in triBox ℓ p, ENNReal.ofReal (‖gc21F p Θ₀ A z‖ ^ 2))
      ≤ ENNReal.ofReal (cA ^ 4 * pinL2 ℓ Θ₀) := by
  have hΘm : Measurable (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
      ENNReal.ofReal (‖Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)‖ ^ 2)) :=
    (((hΘ₀.continuous.comp (continuous_insertCoord2 p hp)).norm.pow 2).measurable.ennreal_ofReal)
  calc (∫⁻ z in triBox ℓ p, ENNReal.ofReal (‖gc21F p Θ₀ A z‖ ^ 2))
      ≤ ∫⁻ z in triBox ℓ p, (ENNReal.ofReal (cA ^ 4) *
          ENNReal.ofReal (‖Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)‖ ^ 2)) := by
        refine lintegral_mono fun z => ?_
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ cA ^ 4)]
        exact ENNReal.ofReal_le_ofReal (norm_gc21F_sq_le hAb hcA z)
    _ = ENNReal.ofReal (cA ^ 4) * (∫⁻ z in triBox ℓ p,
          ENNReal.ofReal (‖Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)‖ ^ 2)) :=
        lintegral_const_mul'' _ hΘm.aemeasurable
    _ = ENNReal.ofReal (cA ^ 4) * (∫⁻ x in Submission.BoseGases.abox n ℓ,
          ENNReal.ofReal (‖Θ₀ x‖ ^ 2)) := by
        rw [(lintegral_abox_eq_lintegral_triBox hℓ p hp
          (fun x => ENNReal.ofReal (‖Θ₀ x‖ ^ 2))).symm]
    _ = ENNReal.ofReal (cA ^ 4) * ENNReal.ofReal (pinL2 ℓ Θ₀) := by
        rw [lintegral_abox_ofReal_sq hℓ hΘ₀]
    _ = ENNReal.ofReal (cA ^ 4 * pinL2 ℓ Θ₀) :=
        (ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ cA ^ 4)).symm

/-- The `L²`-mass of the `(y,u)`-dependent factor over the triple box. -/
theorem lintegral_gc21G_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ₀ : Xn n → ℂ} (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (y u : E3) :
    (∫⁻ z in triBox ℓ p, ENNReal.ofReal (‖Θ₀ (insertCoord2 p y u z.2)‖ ^ 2))
      = ENNReal.ofReal (ℓ ^ 6 * memY21 ℓ p Θ₀ y u) := by
  rw [lintegral_triBox_ofReal_sq hℓ p hp hΘ₀ y u]
  have hpow : ENNReal.ofReal (ℓ ^ 3) ^ 2 = ENNReal.ofReal (ℓ ^ 6) := by
    rw [← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ ℓ ^ 3) 2]
    congr 1
    ring
  rw [hpow, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ℓ ^ 6)]

/-- **The `L²` bound on the clean `pairG21` fibre** (conjunct 4 of `pairGc21_core`). -/
theorem pairGc21_mass_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ₀ : Xn n → ℂ} {A : E3 → ℂ} {cA : ℝ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (hA : Measurable A) (hAb : ∀ x, ‖A x‖ ≤ cA)
    (hcA : 0 ≤ cA) (u y : E3) :
    ‖pairGc21 ℓ p hp Θ₀ A u y‖ ^ 2
      ≤ cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * memY21 ℓ p Θ₀ y u := by
  have hpin : (0 : ℝ) ≤ pinL2 ℓ Θ₀ := integral_nonneg fun x => by positivity
  have hmem : (0 : ℝ) ≤ memY21 ℓ p Θ₀ y u := integral_nonneg fun x => by positivity
  have hR : (0 : ℝ) ≤ cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * memY21 ℓ p Θ₀ y u :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hpin) hmem
  have h1 : ‖pairGc21 ℓ p hp Θ₀ A u y‖ₑ ^ 2
      ≤ ENNReal.ofReal (cA ^ 4 * pinL2 ℓ Θ₀) * ENNReal.ofReal (ℓ ^ 6 * memY21 ℓ p Θ₀ y u) :=
    (pairGc21_normSq_le_cs p hp u y (measurable_gc21F p hp hΘ₀ hA)
      (measurable_gc21G p hp y u hΘ₀)).trans
      (mul_le_mul' (lintegral_gc21F_le hℓ p hp hΘ₀ hA hAb hcA)
        (le_of_eq (lintegral_gc21G_eq hℓ p hp hΘ₀ y u)))
  have h2 : ENNReal.ofReal (cA ^ 4 * pinL2 ℓ Θ₀) * ENNReal.ofReal (ℓ ^ 6 * memY21 ℓ p Θ₀ y u)
      = ENNReal.ofReal (cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * memY21 ℓ p Θ₀ y u) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg (by positivity) hpin)]
    congr 1
    ring
  rw [h2] at h1
  have h3 : ENNReal.ofReal (‖pairGc21 ℓ p hp Θ₀ A u y‖ ^ 2)
      ≤ ENNReal.ofReal (cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * memY21 ℓ p Θ₀ y u) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
    exact h1
  exact (ENNReal.ofReal_le_ofReal_iff hR).mp h3

/-- **The Dirichlet bound on the clean `pairG21` fibre** (conjunct 5 of `pairGc21_core`), given the
parametric derivative formula. -/
theorem pairGc21_dir_le_of_fderiv {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    (hp : p.1 ≠ p.2) {Θ₀ : Xn n → ℂ} {A : E3 → ℂ} {cA : ℝ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (hA : Measurable A) (hAb : ∀ x, ‖A x‖ ≤ cA)
    (hcA : 0 ≤ cA) (y u : E3)
    (hderiv : ∀ j : Fin 3,
      fderiv ℝ (fun u' => pairGc21 ℓ p hp Θ₀ A u' y) u (EuclideanSpace.single j (1 : ℝ))
        = ∫ z in triBox ℓ p,
            gc21F p Θ₀ A z
              * fderiv ℝ Θ₀ (insertCoord2 p y u z.2) (slotDirVec p.2 j)) :
    (∑ j : Fin 3, ‖fderiv ℝ (fun u' => pairGc21 ℓ p hp Θ₀ A u' y) u
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      ≤ cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * dirY21 ℓ p Θ₀ y u := by
  have hpin : (0 : ℝ) ≤ pinL2 ℓ Θ₀ := integral_nonneg fun x => by positivity
  have hdir : (0 : ℝ) ≤ dirY21 ℓ p Θ₀ y u := by
    rw [dirY21]
    exact Finset.sum_nonneg fun j _ => integral_nonneg fun x => by positivity
  have hR : (0 : ℝ) ≤ cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * dirY21 ℓ p Θ₀ y u :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hpin) hdir
  have hFm : Measurable (gc21F p Θ₀ A) := measurable_gc21F p hp hΘ₀ hA
  -- the C–S bound for one derivative
  have hCS : ∀ j : Fin 3,
      ‖fderiv ℝ (fun u' => pairGc21 ℓ p hp Θ₀ A u' y) u
          (EuclideanSpace.single j (1 : ℝ))‖ₑ ^ 2
        ≤ ENNReal.ofReal (cA ^ 4 * pinL2 ℓ Θ₀) * (∫⁻ z in triBox ℓ p,
            ENNReal.ofReal (‖fderiv ℝ Θ₀ (insertCoord2 p y u z.2) (slotDirVec p.2 j)‖ ^ 2)) := by
    intro j
    have hHm : Measurable (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
        fderiv ℝ Θ₀ (insertCoord2 p y u z.2) (slotDirVec p.2 j)) := by
      have h2 : Continuous (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
          fderiv ℝ Θ₀ (insertCoord2 p y u z.2)) :=
        (hΘ₀.continuous_fderiv (by simp)).comp
          ((continuous_insertCoord2_fixed p hp y u).comp continuous_snd)
      exact (h2.clm_apply continuous_const).measurable
    have hcs := enorm_integral_conj_mul_sq_le (μ := (volume : Measure ((E3 × E3) ×
        ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3))).restrict (triBox ℓ p))
      (v := fun z => star (gc21F p Θ₀ A z))
      (Λ := fun z => fderiv ℝ Θ₀ (insertCoord2 p y u z.2) (slotDirVec p.2 j))
      ((Complex.continuous_conj.measurable.comp hFm).aemeasurable) (hHm.aemeasurable)
    rw [show (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
          (starRingEnd ℂ) (star (gc21F p Θ₀ A z))
            * fderiv ℝ Θ₀ (insertCoord2 p y u z.2) (slotDirVec p.2 j))
        = fun z => gc21F p Θ₀ A z
            * fderiv ℝ Θ₀ (insertCoord2 p y u z.2) (slotDirVec p.2 j) from by
          funext z; simp only [starRingEnd_apply, star_star]] at hcs
    rw [show (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
          ‖star (gc21F p Θ₀ A z)‖ₑ ^ 2)
        = fun z => ENNReal.ofReal (‖gc21F p Θ₀ A z‖ ^ 2) from by
          funext z
          have h1 : ‖star (gc21F p Θ₀ A z)‖ₑ = ‖gc21F p Θ₀ A z‖ₑ := by
            rw [← ofReal_norm, ← ofReal_norm, norm_star]
          rw [h1, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _) 2]] at hcs
    rw [show (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
          ‖fderiv ℝ Θ₀ (insertCoord2 p y u z.2) (slotDirVec p.2 j)‖ₑ ^ 2)
        = fun z => ENNReal.ofReal
            (‖fderiv ℝ Θ₀ (insertCoord2 p y u z.2) (slotDirVec p.2 j)‖ ^ 2) from by
          funext z
          rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _) 2]] at hcs
    rw [hderiv j]
    exact hcs.trans (mul_le_mul' (lintegral_gc21F_le hℓ p hp hΘ₀ hA hAb hcA) (le_refl _))
  -- sum over the three derivatives
  have hsum : ENNReal.ofReal (∑ j : Fin 3, ‖fderiv ℝ (fun u' => pairGc21 ℓ p hp Θ₀ A u' y) u
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      ≤ ENNReal.ofReal (cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * dirY21 ℓ p Θ₀ y u) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]
    have hterm : ∀ j : Fin 3, ENNReal.ofReal (‖fderiv ℝ (fun u' => pairGc21 ℓ p hp Θ₀ A u' y) u
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        = ‖fderiv ℝ (fun u' => pairGc21 ℓ p hp Θ₀ A u' y) u
            (EuclideanSpace.single j (1 : ℝ))‖ₑ ^ 2 := fun j => by
      rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
    simp only [hterm]
    calc (∑ j : Fin 3, ‖fderiv ℝ (fun u' => pairGc21 ℓ p hp Θ₀ A u' y) u
            (EuclideanSpace.single j (1 : ℝ))‖ₑ ^ 2)
        ≤ ∑ j : Fin 3, ENNReal.ofReal (cA ^ 4 * pinL2 ℓ Θ₀) * (∫⁻ z in triBox ℓ p,
            ENNReal.ofReal (‖fderiv ℝ Θ₀ (insertCoord2 p y u z.2) (slotDirVec p.2 j)‖ ^ 2)) :=
          Finset.sum_le_sum fun j _ => hCS j
      _ = ENNReal.ofReal (cA ^ 4 * pinL2 ℓ Θ₀) * (∑ j : Fin 3, ∫⁻ z in triBox ℓ p,
            ENNReal.ofReal (‖fderiv ℝ Θ₀ (insertCoord2 p y u z.2) (slotDirVec p.2 j)‖ ^ 2)) :=
          (Finset.mul_sum _ _ _).symm
      _ = ENNReal.ofReal (cA ^ 4 * pinL2 ℓ Θ₀)
            * (ENNReal.ofReal (ℓ ^ 3) ^ 2 * ENNReal.ofReal (dirY21 ℓ p Θ₀ y u)) := by
          rw [lintegral_triBox_ofReal_fderiv_sum hℓ p hp hΘ₀ y u]
      _ = ENNReal.ofReal (cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * dirY21 ℓ p Θ₀ y u) := by
          rw [show ENNReal.ofReal (ℓ ^ 3) ^ 2 = ENNReal.ofReal (ℓ ^ 6) from by
            rw [← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ ℓ ^ 3) 2]; congr 1; ring]
          rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ℓ ^ 6)]
          rw [← ENNReal.ofReal_mul (mul_nonneg (by positivity) hpin)]
          congr 1
          ring
  exact (ENNReal.ofReal_le_ofReal_iff hR).mp hsum

end Work.BoseBoxFock
