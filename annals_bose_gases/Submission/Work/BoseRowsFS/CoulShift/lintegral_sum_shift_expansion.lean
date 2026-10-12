import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseRowsFS.CoulShift.lintegral_prod_diag_shift
import Submission.Work.BoseRowsFS.CoulShift.ofReal_shift_expansion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `CoulShift` double-integral expansion

For a nonnegative (a.e.-measurable) weight `W` on `ℝ³` and a shift `a`, the
iterated Lebesgue integral of the shifted square factorises:

`∫⁻x ∫⁻y ofReal ((W x + W (x+a)) (W y + W (y+a)) / ‖x-y‖)
   = 2 ∫⁻x ∫⁻y ofReal (W x W y / ‖x-y‖) + 2 ∫⁻x ∫⁻y ofReal (W x W (y+a) / ‖x-y‖)`.

The mathematics: expand the product into four terms; the term
`W(x+a) W(y+a)` is the first term after the translation `(x,y) ↦ (x+a,y+a)`
(Lebesgue measure is translation invariant), and the cross term
`W(x+a) W(y)` is the second term after the transposition `(x,y) ↦ (y,x)`
(the product measure is symmetric and `‖x-y‖ = ‖y-x‖`).

Everything is organised on the product space `ℝ³ × ℝ³`, where `lintegral` of a
sum of four terms splits by `lintegral_add_right'` and both symmetries are
measure-preserving changes of variables.
-/

namespace Work.BoseRowsFS.CoulShift

open MeasureTheory

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- First summand: `W x W y / ‖x-y‖`. -/
private noncomputable def k1 (W : E3 → ℝ) (z : E3 × E3) : ENNReal :=
  ENNReal.ofReal (W z.1 * W z.2 / ‖z.1 - z.2‖)

/-- Second summand: `W x W (y+a) / ‖x-y‖`. -/
private noncomputable def k2 (W : E3 → ℝ) (a : E3) (z : E3 × E3) : ENNReal :=
  ENNReal.ofReal (W z.1 * W (z.2 + a) / ‖z.1 - z.2‖)

/-- Third summand: `W (x+a) W y / ‖x-y‖`. -/
private noncomputable def k3 (W : E3 → ℝ) (a : E3) (z : E3 × E3) : ENNReal :=
  ENNReal.ofReal (W (z.1 + a) * W z.2 / ‖z.1 - z.2‖)

/-- Fourth summand: `W (x+a) W (y+a) / ‖x-y‖`. -/
private noncomputable def k4 (W : E3 → ℝ) (a : E3) (z : E3 × E3) : ENNReal :=
  ENNReal.ofReal (W (z.1 + a) * W (z.2 + a) / ‖z.1 - z.2‖)

/-- The full shifted-square integrand. -/
private noncomputable def kG (W : E3 → ℝ) (a : E3) (z : E3 × E3) : ENNReal :=
  ENNReal.ofReal ((W z.1 + W (z.1 + a)) * (W z.2 + W (z.2 + a)) / ‖z.1 - z.2‖)

/-- The pointwise expansion of the shifted square integrand into its four
nonnegative pieces is the delegated lemma `ofReal_shift_expansion` (nonnegativity
of `W` is what makes `ENNReal.ofReal` additive there), and the translation
invariance of the product Lebesgue measure under the diagonal shift
`(x,y) ↦ (x+a, y+a)` is the delegated lemma `lintegral_prod_diag_shift`. -/

theorem lintegral_sum_shift_expansion {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWm : AEMeasurable W MeasureTheory.volume)
    (hW0 : ∀ x, 0 ≤ W x) (a : EuclideanSpace ℝ (Fin 3)) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal ((W x + W (x + a)) * (W y + W (y + a)) / ‖x - y‖))
      = 2 * (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖))
        + 2 * (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W (y + a) / ‖x - y‖)) := by
  -- measurability of the four product summands
  have hk1m : AEMeasurable (k1 W) (volume.prod volume) := by
    unfold k1; fun_prop
  have hk2m : AEMeasurable (k2 W a) (volume.prod volume) := by
    unfold k2; fun_prop
  have hk3m : AEMeasurable (k3 W a) (volume.prod volume) := by
    unfold k3; fun_prop
  have hk4m : AEMeasurable (k4 W a) (volume.prod volume) := by
    unfold k4; fun_prop
  -- Tonelli: rewrite the iterated integral of the left-hand side on the product space
  have hL : (∫⁻ x, ∫⁻ y, ENNReal.ofReal ((W x + W (x + a)) * (W y + W (y + a)) / ‖x - y‖))
      = ∫⁻ z, kG W a z ∂(volume.prod volume) := by
    refine lintegral_lintegral (f := fun x y : E3 =>
      ENNReal.ofReal ((W x + W (x + a)) * (W y + W (y + a)) / ‖x - y‖)) ?_
    unfold Function.uncurry
    fun_prop
  -- the pointwise expansion into four summands
  have hpoint : ∀ z : E3 × E3, kG W a z = k1 W z + k2 W a z + k3 W a z + k4 W a z := by
    intro z
    simp only [kG, k1, k2, k3, k4]
    exact ofReal_shift_expansion hW0 a z.1 z.2
  have hsplit : ∫⁻ z, kG W a z ∂(volume.prod volume)
      = ∫⁻ z, (k1 W z + k2 W a z + k3 W a z + k4 W a z) ∂(volume.prod volume) :=
    lintegral_congr hpoint
  -- splitting the integral of the four-term sum
  have hadd2 : ∫⁻ z, (k1 W z + k2 W a z) ∂(volume.prod volume)
      = (∫⁻ z, k1 W z ∂(volume.prod volume)) + (∫⁻ z, k2 W a z ∂(volume.prod volume)) :=
    lintegral_add_right' (k1 W) hk2m
  have hadd3 : ∫⁻ z, (k1 W z + k2 W a z + k3 W a z) ∂(volume.prod volume)
      = ((∫⁻ z, k1 W z ∂(volume.prod volume)) + (∫⁻ z, k2 W a z ∂(volume.prod volume)))
        + (∫⁻ z, k3 W a z ∂(volume.prod volume)) := by
    rw [lintegral_add_right' (fun z => k1 W z + k2 W a z) hk3m, hadd2]
  have hadd4 : ∫⁻ z, (k1 W z + k2 W a z + k3 W a z + k4 W a z) ∂(volume.prod volume)
      = (((∫⁻ z, k1 W z ∂(volume.prod volume)) + (∫⁻ z, k2 W a z ∂(volume.prod volume)))
          + (∫⁻ z, k3 W a z ∂(volume.prod volume)))
        + (∫⁻ z, k4 W a z ∂(volume.prod volume)) := by
    rw [lintegral_add_right' (fun z => k1 W z + k2 W a z + k3 W a z) hk4m, hadd3]
  -- symmetry of the fourth term with the first: translate both variables by `a`
  have h43 : ∫⁻ z, k4 W a z ∂(volume.prod volume) = ∫⁻ z, k1 W z ∂(volume.prod volume) := by
    have hpt : ∀ z : E3 × E3, k4 W a z = k1 W (z.1 + a, z.2 + a) := by
      intro z
      simp only [k4, k1, add_sub_add_right_eq_sub]
    rw [lintegral_congr hpt, lintegral_prod_diag_shift a (k1 W)]
  -- symmetry of the third term with the second: transpose the two variables
  have h32 : ∫⁻ z, k3 W a z ∂(volume.prod volume) = ∫⁻ z, k2 W a z ∂(volume.prod volume) := by
    have hpt : ∀ z : E3 × E3, k3 W a z = k2 W a z.swap := by
      intro z
      have hz : z.swap = (z.2, z.1) := rfl
      simp only [k3, k2, hz]
      rw [mul_comm (W z.2) (W (z.1 + a)), norm_sub_rev]
    rw [lintegral_congr hpt, lintegral_prod_swap (k2 W a)]
  -- Tonelli in the reverse direction for the two surviving terms
  have hF1 : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖))
      = ∫⁻ z, k1 W z ∂(volume.prod volume) := by
    refine lintegral_lintegral (f := fun x y : E3 => ENNReal.ofReal (W x * W y / ‖x - y‖)) ?_
    unfold Function.uncurry
    fun_prop
  have hF2 : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W (y + a) / ‖x - y‖))
      = ∫⁻ z, k2 W a z ∂(volume.prod volume) := by
    refine lintegral_lintegral (f := fun x y : E3 => ENNReal.ofReal (W x * W (y + a) / ‖x - y‖)) ?_
    unfold Function.uncurry
    fun_prop
  calc (∫⁻ x, ∫⁻ y, ENNReal.ofReal ((W x + W (x + a)) * (W y + W (y + a)) / ‖x - y‖))
      = ∫⁻ z, kG W a z ∂(volume.prod volume) := hL
    _ = ∫⁻ z, (k1 W z + k2 W a z + k3 W a z + k4 W a z) ∂(volume.prod volume) := hsplit
    _ = (((∫⁻ z, k1 W z ∂(volume.prod volume)) + (∫⁻ z, k2 W a z ∂(volume.prod volume)))
          + (∫⁻ z, k3 W a z ∂(volume.prod volume)))
        + (∫⁻ z, k4 W a z ∂(volume.prod volume)) := hadd4
    _ = (((∫⁻ z, k1 W z ∂(volume.prod volume)) + (∫⁻ z, k2 W a z ∂(volume.prod volume)))
          + (∫⁻ z, k2 W a z ∂(volume.prod volume)))
        + (∫⁻ z, k1 W z ∂(volume.prod volume)) := by rw [h43, h32]
    _ = 2 * (∫⁻ z, k1 W z ∂(volume.prod volume))
        + 2 * (∫⁻ z, k2 W a z ∂(volume.prod volume)) := by ring
    _ = 2 * (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖))
        + 2 * (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W (y + a) / ‖x - y‖)) := by rw [← hF1, ← hF2]

end Work.BoseRowsFS.CoulShift
