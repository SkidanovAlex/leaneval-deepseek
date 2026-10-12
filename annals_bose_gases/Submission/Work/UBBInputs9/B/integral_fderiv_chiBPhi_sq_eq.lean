import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.UBBInputs9.B.Basic
import Submission.Work.UBBInputs9.B.integrable_chiScale_sub_smul_mul_fderiv
import Submission.Work.UBBInputs9.B.integral_chiScale_sub_smul_mul_fderiv_eq_zero
import Submission.Work.UBBInputs9.B.integral_chiScale_sub_smul_sq
import Submission.Work.UBBInputs9.B.integral_fderiv_chiScale_sub_smul_sq
import Submission.Work.UBBInputs9.C.integrable_partialDeriv_chiScale_sub_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs9.B.integral_fderiv_chiBPhi_sq_eq`

The **pointwise `u`-integral of the squared derivative** of the sliding window applied to a state:

    `∫_u (∂_k (χ_{B(u)}·Φ)(x))² du
       = (∂_k (χ(x/ℓ)·Φ)(x))² + (∫_z (∂_k χ (z))² dz)/(ℓd)² · χ(x/ℓ)² Φ(x)²`.

## The mathematics

`Basic.fderiv_chiBPhi_eq` splits the derivative of the product along `kcDir 1 0 k` into the
Leibniz two-term form

    `∂_k (χ_{B(u)}·Φ)(x)
       = A·P(u) + B·Q(u)`,

where `A := ∂_k (χ(x/ℓ)·Φ)(x)` and `B := χ(x/ℓ)Φ(x)` are **independent of `u`**, while

    `P(u) := chiScale (ℓd) (x₀ − (ℓd)•u)`,   `Q(u) := ∂_k chiScale (ℓd) (x₀ − (ℓd)•u)`

carry the whole `u`-dependence (`x₀ := x 0`).  Expanding the square,

    `∫_u (A P + B Q)² = A² ∫_u P² + 2AB ∫_u P·Q + B² ∫_u Q²`,

and the three integrals are:

* `∫_u P² = 1` — the `L²`-normalisation of the sliding family
  (`B/integral_chiScale_sub_smul_sq`);
* `∫_u P·Q = 0` — the cross term: with `w := (ℓd)⁻¹•x₀` the integrand is
  `(ℓd)⁻¹ χ(w−u)·(∂_k χ)(w−u)`, and `v ↦ χ v·∂_k χ v` is odd, so its integral vanishes
  (`B/integral_chiScale_sub_smul_mul_fderiv_eq_zero`, from `ChiDeriv`);
* `∫_u Q² = (∫_z (∂_k χ z)²)/(ℓd)²` — the rescaling rule `(chiScale s)'(x) = s⁻¹ χ'(s⁻¹x)`
  applied inside the measure-preserving substitution `u ↦ w − u`
  (`B/integral_fderiv_chiScale_sub_smul_sq`).

The three integrals are the `L²`-input of the sliding localisation; this is the pointwise-in-`x`
form, integrated over the box in `B/integral_dirichlet_chiB_eq`.

## Contents

* `integral_sq_add_eq` — the abstract expansion `∫(AP+BQ)² = A² + B²C` from `∫P² = 1`, `∫PQ = 0`,
  `∫Q² = C` (the only algebra, isolated so that the assembly is pure bookkeeping);
* `integrable_chiScale_sub_smul_sq` — integrability of `u ↦ P(u)²`;
* `integral_fderiv_chiBPhi_sq_eq` — the target identity.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs9.B

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "X1" => Submission.BoseGases.X 1

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The abstract `L²`-expansion -/

/-- **The abstract two-term expansion.**  If `∫_u P(u)² = 1`, `∫_u P(u)Q(u) = 0` and
`∫_u Q(u)² = C` (with all three integrands integrable), then

    `∫_u (A·P(u) + B·Q(u))² = A² + B²·C`.

This is the whole algebra of the sliding `L²`-computation: the mixed term drops out. -/
lemma integral_sq_add_eq (A B C : ℝ) {P Q : ℝ³ → ℝ}
    (hPi : Integrable (fun u : ℝ³ => (P u) ^ 2))
    (hPQi : Integrable (fun u : ℝ³ => P u * Q u))
    (hQi : Integrable (fun u : ℝ³ => (Q u) ^ 2))
    (hP : (∫ u : ℝ³, (P u) ^ 2) = 1)
    (hPQ : (∫ u : ℝ³, P u * Q u) = 0)
    (hQ : (∫ u : ℝ³, (Q u) ^ 2) = C) :
    (∫ u : ℝ³, (A * P u + B * Q u) ^ 2) = A ^ 2 + B ^ 2 * C := by
  have hint1 : Integrable (fun u : ℝ³ => A ^ 2 * (P u) ^ 2) := hPi.const_mul _
  have hint2 : Integrable (fun u : ℝ³ => (2 * A * B) * (P u * Q u)) := hPQi.const_mul _
  have hint3 : Integrable (fun u : ℝ³ => B ^ 2 * (Q u) ^ 2) := hQi.const_mul _
  have hsum : (∫ u : ℝ³, (A * P u + B * Q u) ^ 2)
      = (∫ u : ℝ³, (A ^ 2 * (P u) ^ 2 + (2 * A * B) * (P u * Q u) + B ^ 2 * (Q u) ^ 2)) :=
    integral_congr_ae (ae_of_all _ (fun u => by ring))
  have e1 : (∫ u : ℝ³, A ^ 2 * (P u) ^ 2 + (2 * A * B) * (P u * Q u) + B ^ 2 * (Q u) ^ 2)
      = (∫ u : ℝ³, A ^ 2 * (P u) ^ 2) + (∫ u : ℝ³, (2 * A * B) * (P u * Q u))
        + (∫ u : ℝ³, B ^ 2 * (Q u) ^ 2) := by
    rw [integral_add (f := fun u : ℝ³ => A ^ 2 * (P u) ^ 2 + (2 * A * B) * (P u * Q u))
          (g := fun u : ℝ³ => B ^ 2 * (Q u) ^ 2) (hint1.add hint2) hint3,
        integral_add (f := fun u : ℝ³ => A ^ 2 * (P u) ^ 2)
          (g := fun u : ℝ³ => (2 * A * B) * (P u * Q u)) hint1 hint2]
  rw [hsum, e1, integral_const_mul, integral_const_mul, integral_const_mul, hP, hPQ, hQ]
  ring

/-! ## Integrability of the `chiScale`-square along the sliding substitution -/

/-- `u ↦ chiScale a (c − a•u)²` is integrable: `chiScale a` is continuous with compact support
(`chiScale_hasCompactSupport`), so its square is too, and the affine substitution `u ↦ c − a•u`
preserves integrability (`Integrable.comp_sub_left`, `Integrable.comp_smul`). -/
lemma integrable_chiScale_sub_smul_sq (a : ℝ) (ha : 0 < a) (c : ℝ³) :
    Integrable (fun u : ℝ³ => (chiScale a (c - a • u)) ^ 2) := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hcont : Continuous (fun y : ℝ³ => (chiScale a y) ^ 2) :=
    (ChiDeriv.chiScale_contDiff_any a).continuous.pow 2
  have hcs : HasCompactSupport (fun y : ℝ³ => (chiScale a y) ^ 2) :=
    (chiScale_hasCompactSupport ha').comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  exact ((hcont.integrable_of_hasCompactSupport hcs).comp_sub_left c).comp_smul ha'

/-! ## The target identity -/

theorem integral_fderiv_chiBPhi_sq_eq (ℓ d : ℝ) (hℓ : 0 < ℓ) (hd : 0 < d)
    {Φ : Submission.BoseGases.X 1 → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (x : Submission.BoseGases.X 1) (k : Fin 3) :
    (∫ u : EuclideanSpace ℝ (Fin 3),
        (fderiv ℝ (fun y : Submission.BoseGases.X 1 =>
          Submission.BoseGases.chiB ℓ d u (y 0) * Φ y) x
            (Submission.BoseGases.kcDir 1 0 k)) ^ 2)
      = (fderiv ℝ (fun y : Submission.BoseGases.X 1 =>
            Submission.BoseGases.chiScale ℓ (y 0) * Φ y) x
              (Submission.BoseGases.kcDir 1 0 k)) ^ 2
        + ((∫ z : EuclideanSpace ℝ (Fin 3),
              (fderiv ℝ Submission.BoseGases.chi z
                (Submission.BoseGases.kcStdBasis k)) ^ 2) / (ℓ * d) ^ 2)
          * ((Submission.BoseGases.chiScale ℓ (x 0)) ^ 2 * (Φ x) ^ 2) := by
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  -- the three `u`-independent constants of the expansion
  set A : ℝ := fderiv ℝ (fun y : X1 => chiScale ℓ (y 0) * Φ y) x (kcDir 1 0 k) with hA
  set B : ℝ := chiScale ℓ (x 0) * Φ x with hB
  set C : ℝ := (∫ z : ℝ³, (fderiv ℝ chi z (kcStdBasis k)) ^ 2) / (ℓ * d) ^ 2 with hC
  -- Leibniz: the integrand is `(A·P u + B·Q u)²` with `P`, `Q` the sliding factors
  have hpt : ∀ u : ℝ³, (fderiv ℝ (fun y : X1 => chiB ℓ d u (y 0) * Φ y) x (kcDir 1 0 k)) ^ 2
      = (A * chiScale (ℓ*d) (x 0 - (ℓ*d) • u)
          + B * fderiv ℝ (chiScale (ℓ*d)) (x 0 - (ℓ*d) • u) (kcStdBasis k)) ^ 2 := by
    intro u
    rw [fderiv_chiBPhi_eq ℓ d hΦ u x k, ← hA, ← hB]
  -- the three integrals: `∫P² = 1`, `∫PQ = 0`, `∫Q² = C`
  have hmain := integral_sq_add_eq A B C
    (P := fun u : ℝ³ => chiScale (ℓ * d) (x 0 - (ℓ * d) • u))
    (Q := fun u : ℝ³ => fderiv ℝ (chiScale (ℓ * d)) (x 0 - (ℓ * d) • u) (kcStdBasis k))
    (integrable_chiScale_sub_smul_sq (ℓ*d) hld (x 0))
    (integrable_chiScale_sub_smul_mul_fderiv (ℓ*d) hld (x 0) (kcStdBasis k))
    (Work.UBBInputs9.C.integrable_partialDeriv_chiScale_sub_smul (ℓ*d) hld (x 0) k)
    (integral_chiScale_sub_smul_sq (ℓ*d) hld (x 0))
    (integral_chiScale_sub_smul_mul_fderiv_eq_zero (ℓ*d) hld (x 0) (kcStdBasis k))
    (integral_fderiv_chiScale_sub_smul_sq (ℓ*d) hld (x 0) (kcStdBasis k))
  rw [integral_congr_ae (ae_of_all _ hpt), hmain, hA, hB, hC]
  ring

end Work.UBBInputs9.B
