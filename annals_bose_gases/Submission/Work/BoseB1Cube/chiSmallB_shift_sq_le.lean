import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.AprioriCount.cubeDenseAliveRow
import Submission.Work.BoseB1Cube.chiSmallBShiftSqLE
import Submission.Work.BoseFixB1S.fibreAeTransfer
import Submission.Work.BoseFixB1S.flatFibDeviationB1
import Submission.Work.BoseFixB1S.flatOmegaAllStateB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.chiSmallB_shift_sq_le`

The *global* `L²`-translation-difference bound for the two-factor sliding-box cutoff of
Fournais--Solovej (`eq:chiBdefinition`)

    χ_B(x) = chiScale ℓ x · chiSmall 48 ((ℓ d)⁻¹ • (x − (ℓ d) • u)) ,

i.e. **without** the restriction `‖w‖ ≤ R` that the delegated `Work.BoseB1Cube.chiSmallBShiftSqLE`
carries: if the corpus bump `chi` is `L`-Lipschitz then

    ∫ x, (χ_B(x + w) − χ_B(x))² ≤ C ‖w‖² (ℓ d + L² (ℓ d)³ / ℓ²)

with a constant `C ≥ 0` *independent of `L`, `ℓ`, `d`, `u` and `w`*.

## Proof

Write `χ_B = A · B` with `A = chiScale ℓ` (`= χ(·/ℓ)`) and
`B = chiSmall 48 ((ℓd)⁻¹ • (· − (ℓd)•u))`.  The pointwise product identity

    A(x+w)B(x+w) − A(x)B(x) = A(x+w)·(B(x+w) − B(x)) + (A(x+w) − A(x))·B(x)

together with `(a+b)² ≤ 2a² + 2b²`, `A² ≤ chiSupAbs² =: κ²` and
`(A(x+w) − A(x))² ≤ (L‖w‖/ℓ)²` (the hypothesis, rescaled by `ℓ⁻¹`) gives

    (χ_B(x+w) − χ_B(x))² ≤ 2κ² (B(x+w) − B(x))² + 2(L‖w‖/ℓ)² B(x+w)² .

This is exactly the pointwise estimate underlying the delegated (and proved) template
`Work.BoseB1Cube.chiSmallBShiftSqLE`, whose two analytic inputs we supply here at `R = ‖w‖`:

* `A` is `L/ℓ`-Lipschitz (rescaling the hypothesis on `chi` by the factor `ℓ⁻¹`);
* the *scaled* `L²`-modulus of the small-box factor `chiSmall 48`, taken at scale `c = ℓ d`:
  `Work.BoseFixB1.MDelta.chiSmallScaledModulus` (delegated, proved) gives directly
  `∫ (B(x+w) − B(x))² ≤ C₃ (ℓd) ‖w‖²`.

Integrating, `∫ B(· + w)² = (ℓd)³` (the `L²`-normalisation of `chiSmall`, scaled;
`Work.BoseFixB1.MDelta.integral_chiSmall_scale_sq`) yields

    ∫ (χ_B(·+w) − χ_B)² ≤ 2 (L/ℓ)² ‖w‖² (ℓd)³ + 2 κ² C₃ (ℓd) ‖w‖² ,

which is the claim with `C = max 2 (2κ²C₃)`, since `L²/ℓ² = (L/ℓ)²` and `ℓd > 0`.
-/

namespace Work.BoseB1Cube

open MeasureTheory

set_option autoImplicit false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem chiSmallB_shift_sq_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L ℓ d : ℝ) (u w : EuclideanSpace ℝ (Fin 3)), 0 ≤ L → 0 < ℓ → 0 < d →
      (∀ x v : EuclideanSpace ℝ (Fin 3),
        |Submission.BoseGases.chi (x + v) - Submission.BoseGases.chi x| ≤ L * ‖v‖) →
      (∫ x : EuclideanSpace ℝ (Fin 3),
          (Submission.BoseGases.chiSmallB 48 ℓ d u (x + w)
            - Submission.BoseGases.chiSmallB 48 ℓ d u x) ^ 2)
        ≤ C * ‖w‖ ^ 2 * ((ℓ * d) + L ^ 2 * (ℓ * d) ^ 3 / ℓ ^ 2) := by
  -- the scaled `L²`-modulus constant of the small-box factor, and the sup of the big-box factor
  obtain ⟨C3, hC30, hmod3⟩ :=
    Work.BoseFixB1.MDelta.chiSmallScaledModulus (M := 48) (by norm_num)
  refine ⟨max 2 (2 * Submission.BoseGases.chiSupAbs ^ 2 * C3), le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro L ℓ d u w hL hℓ hd hchi
  -- ### (a) `chiScale ℓ` is `L/ℓ`-Lipschitz, from the hypothesis rescaled by `ℓ⁻¹`
  have hLip : ∀ x y : E3,
      |Submission.BoseGases.chiScale ℓ x - Submission.BoseGases.chiScale ℓ y|
        ≤ L * ‖x - y‖ / ℓ := by
    intro x y
    have h := hchi ((ℓ⁻¹) • y) ((ℓ⁻¹) • (x - y))
    have hxs : Submission.BoseGases.chiScale ℓ x
        = Submission.BoseGases.chi ((ℓ⁻¹) • y + (ℓ⁻¹) • (x - y)) := by
      show Submission.BoseGases.chi ((ℓ⁻¹) • x)
        = Submission.BoseGases.chi ((ℓ⁻¹) • y + (ℓ⁻¹) • (x - y))
      rw [← smul_add]
      congr 1
      abel
    have hys : Submission.BoseGases.chiScale ℓ y = Submission.BoseGases.chi ((ℓ⁻¹) • y) := rfl
    have hn : ‖(ℓ⁻¹) • (x - y)‖ = ‖x - y‖ / ℓ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ), inv_mul_eq_div]
    rw [hn] at h
    rw [hxs, hys]
    calc |Submission.BoseGases.chi ((ℓ⁻¹) • y + (ℓ⁻¹) • (x - y))
            - Submission.BoseGases.chi ((ℓ⁻¹) • y)|
        ≤ L * (‖x - y‖ / ℓ) := h
      _ = L * ‖x - y‖ / ℓ := by ring
  -- ### (b) the scaled `L²`-modulus of `chiSmall 48` at scale `c = ℓ d`
  have hmod : ∀ w t : E3,
      (∫ x : E3, (Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • (x - w))
          - Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • (x - t - w))) ^ 2)
        ≤ C3 * (ℓ * d) * ‖t‖ ^ 2 :=
    fun w t => hmod3 (ℓ * d) w t (mul_pos hℓ hd)
  -- ### (c) the product template, at the shift `w`
  have hmain := chiSmallBShiftSqLE (M := 48) (ℓ := ℓ) (d := d) (R := ‖w‖) (L := L) (C3 := C3)
    (by norm_num) hℓ hd (norm_nonneg w) hL hC30 hLip hmod u (le_refl ‖w‖)
  -- ### (d) the arithmetic: `2(L/ℓ)²‖w‖²(ℓd)³ + 2κ²C₃(ℓd)‖w‖² ≤ C‖w‖²(ℓd + L²(ℓd)³/ℓ²)`
  have hD : 0 ≤ ℓ * d := le_of_lt (mul_pos hℓ hd)
  have hX : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
  set Q : ℝ := (L / ℓ) ^ 2 * (ℓ * d) ^ 2 with hQdef
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hM2 : (2 : ℝ) ≤ max 2 (2 * Submission.BoseGases.chiSupAbs ^ 2 * C3) := le_max_left _ _
  have hMk : 2 * Submission.BoseGases.chiSupAbs ^ 2 * C3 ≤ max 2 (2 * Submission.BoseGases.chiSupAbs ^ 2 * C3) := le_max_right _ _
  have hkey : L ^ 2 * (ℓ * d) ^ 3 / ℓ ^ 2 = Q * (ℓ * d) := by
    rw [hQdef, div_pow, div_mul_eq_mul_div]
    ring
  have hbracket : 2 * Q + 2 * Submission.BoseGases.chiSupAbs ^ 2 * C3
      ≤ max 2 (2 * Submission.BoseGases.chiSupAbs ^ 2 * C3) + max 2 (2 * Submission.BoseGases.chiSupAbs ^ 2 * C3) * Q := by
    have h1 : 2 * Q ≤ max 2 (2 * Submission.BoseGases.chiSupAbs ^ 2 * C3) * Q := mul_le_mul_of_nonneg_right hM2 hQ0
    linarith
  have hLHS : 2 * (L / ℓ) ^ 2 * ‖w‖ ^ 2 * (ℓ * d) ^ 3
        + 2 * Submission.BoseGases.chiSupAbs ^ 2 * C3 * (ℓ * d) * ‖w‖ ^ 2
      = ‖w‖ ^ 2 * (ℓ * d) * (2 * Q + 2 * Submission.BoseGases.chiSupAbs ^ 2 * C3) := by
    rw [hQdef]; ring
  have hRHS : max 2 (2 * Submission.BoseGases.chiSupAbs ^ 2 * C3) * ‖w‖ ^ 2 * ((ℓ * d) + L ^ 2 * (ℓ * d) ^ 3 / ℓ ^ 2)
      = ‖w‖ ^ 2 * (ℓ * d) * (max 2 (2 * Submission.BoseGases.chiSupAbs ^ 2 * C3) + max 2 (2 * Submission.BoseGases.chiSupAbs ^ 2 * C3) * Q) := by
    rw [hkey]; ring
  have harith : 2 * (L / ℓ) ^ 2 * ‖w‖ ^ 2 * (ℓ * d) ^ 3
        + 2 * Submission.BoseGases.chiSupAbs ^ 2 * C3 * (ℓ * d) * ‖w‖ ^ 2
      ≤ max 2 (2 * Submission.BoseGases.chiSupAbs ^ 2 * C3) * ‖w‖ ^ 2 * ((ℓ * d) + L ^ 2 * (ℓ * d) ^ 3 / ℓ ^ 2) := by
    calc 2 * (L / ℓ) ^ 2 * ‖w‖ ^ 2 * (ℓ * d) ^ 3 + 2 * Submission.BoseGases.chiSupAbs ^ 2 * C3 * (ℓ * d) * ‖w‖ ^ 2
        = ‖w‖ ^ 2 * (ℓ * d) * (2 * Q + 2 * Submission.BoseGases.chiSupAbs ^ 2 * C3) := hLHS
      _ ≤ ‖w‖ ^ 2 * (ℓ * d) * (max 2 (2 * Submission.BoseGases.chiSupAbs ^ 2 * C3) + max 2 (2 * Submission.BoseGases.chiSupAbs ^ 2 * C3) * Q) :=
          mul_le_mul_of_nonneg_left hbracket (mul_nonneg hX hD)
      _ = max 2 (2 * Submission.BoseGases.chiSupAbs ^ 2 * C3) * ‖w‖ ^ 2 * ((ℓ * d) + L ^ 2 * (ℓ * d) ^ 3 / ℓ ^ 2) := hRHS.symm
  -- the template states the shift as `w + ·`; the target integrates the shift as `· + w`
  have heq : (∫ x : E3, (Submission.BoseGases.chiSmallB 48 ℓ d u (x + w)
        - Submission.BoseGases.chiSmallB 48 ℓ d u x) ^ 2)
      = ∫ y : E3, (Submission.BoseGases.chiSmallB 48 ℓ d u (w + y)
        - Submission.BoseGases.chiSmallB 48 ℓ d u y) ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (Submission.BoseGases.chiSmallB 48 ℓ d u (x + w)
          - Submission.BoseGases.chiSmallB 48 ℓ d u x) ^ 2
        = (Submission.BoseGases.chiSmallB 48 ℓ d u (w + x)
          - Submission.BoseGases.chiSmallB 48 ℓ d u x) ^ 2
    rw [add_comm w x]
  calc (∫ x : E3, (Submission.BoseGases.chiSmallB 48 ℓ d u (x + w)
          - Submission.BoseGases.chiSmallB 48 ℓ d u x) ^ 2)
      = ∫ y : E3, (Submission.BoseGases.chiSmallB 48 ℓ d u (w + y)
          - Submission.BoseGases.chiSmallB 48 ℓ d u y) ^ 2 := heq
    _ ≤ 2 * (L / ℓ) ^ 2 * ‖w‖ ^ 2 * (ℓ * d) ^ 3
          + 2 * Submission.BoseGases.chiSupAbs ^ 2 * C3 * (ℓ * d) * ‖w‖ ^ 2 := hmain
    _ ≤ max 2 (2 * Submission.BoseGases.chiSupAbs ^ 2 * C3) * ‖w‖ ^ 2
          * ((ℓ * d) + L ^ 2 * (ℓ * d) ^ 3 / ℓ ^ 2) := harith

end Work.BoseB1Cube
