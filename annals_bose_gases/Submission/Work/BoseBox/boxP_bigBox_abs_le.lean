import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BSKinetic.bigKinU_one_eq_oneBody
import Submission.Work.BoseBox.CNodeDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBox

open MeasureTheory

/-!
# The box mean of a box-supported state obeys the state's sup bound

`Work.SmallBoxTBWord.boxP (ℓ³) (bigBox ℓ u) i Ψ x` is the mean of `Ψ` over the
sliding box `Λ(u) = bigBox ℓ u` (of side `ℓ`, volume `ℓ³`) in slot `i`:

    boxP (ℓ³) (bigBox ℓ u) i Ψ x = (ℓ³)⁻¹ ∫_{z ∈ Λ(u)} Ψ (x_{i←z}) .

If `Ψ` is supported in the big box `BoseGases.box N L` and obeys `|Ψ| ≤ M0`
there, then `|Ψ y| ≤ M0` *everywhere* (`Ψ` vanishes off the box) and therefore
every fibre value inside the mean is bounded by `M0`.  Since the sliding box has
volume `ℓ³` (`acube_volume` + translation invariance of Lebesgue measure), the
mean is bounded by `M0` as well.
-/

/-- **The box mean over `Λ(u)` obeys the state's sup bound.**  For `ℓ > 0`,
`M0 ≥ 0` and a state `Ψ` with `tsupport Ψ ⊆ BoseGases.box N L` and `|Ψ| ≤ M0`
on that box, the sliding-box mean `boxP (ℓ³) (bigBox ℓ u) i Ψ` is bounded by
`M0` pointwise. -/
theorem boxP_bigBox_abs_le {N : ℕ} {L ℓ M0 : ℝ} (hℓ : 0 < ℓ) (hM0nn : 0 ≤ M0)
    {Ψ : Submission.BoseGases.X N → ℝ} (hsupp : tsupport Ψ ⊆ _root_.BoseGases.box N L)
    (hM0 : ∀ y : Submission.BoseGases.X N, y ∈ _root_.BoseGases.box N L → |Ψ y| ≤ M0) :
    ∀ (u : EuclideanSpace ℝ (Fin 3)) (i : Fin N) (x : Submission.BoseGases.X N),
      |Work.SmallBoxTBWord.boxP (ℓ ^ 3) (Work.BoseBox.bigBox ℓ u) i Ψ x| ≤ M0 := by
  -- `Ψ` vanishes off the big box, so the sup bound holds globally
  have hΨM : ∀ y : Submission.BoseGases.X N, |Ψ y| ≤ M0 := by
    intro y
    by_cases hy : y ∈ _root_.BoseGases.box N L
    · exact hM0 y hy
    · have h0 : Ψ y = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hy (hsupp h))
      rw [h0, abs_zero]
      exact hM0nn
  intro u i x
  -- the sliding box `Λ(u)` is a translate of the centred cube `acube ℓ`
  have hvol : (volume : Measure ℝ³) (Work.BoseBox.bigBox ℓ u) = ENNReal.ofReal (ℓ ^ 3) := by
    have h : (Work.BoseBox.bigBox ℓ u)
        = (fun z : ℝ³ => z + (-(ℓ • u))) ⁻¹' Submission.BoseGases.acube ℓ := rfl
    rw [h, MeasureTheory.measure_preimage_add_right,
      Submission.BoseGases.acube_volume ℓ hℓ.le]
  have hreal : (volume : Measure ℝ³).real (Work.BoseBox.bigBox ℓ u) = ℓ ^ 3 := by
    rw [MeasureTheory.Measure.real_def, hvol, ENNReal.toReal_ofReal (by positivity)]
  have hlt : (volume : Measure ℝ³) (Work.BoseBox.bigBox ℓ u) < ⊤ := by
    rw [hvol]
    exact ENNReal.ofReal_lt_top
  have hint : ‖∫ z in Work.BoseBox.bigBox ℓ u, Ψ (Function.update x i z)‖ ≤ M0 * ℓ ^ 3 := by
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ³))
      (s := Work.BoseBox.bigBox ℓ u) (f := fun z : ℝ³ => Ψ (Function.update x i z))
      (C := M0) hlt
      (fun z _ => by simpa [Real.norm_eq_abs] using hΨM (Function.update x i z))
    simpa [hreal] using h
  have hI' : |∫ z in Work.BoseBox.bigBox ℓ u, Ψ (Function.update x i z)| ≤ M0 * ℓ ^ 3 := by
    simpa [Real.norm_eq_abs] using hint
  unfold Work.SmallBoxTBWord.boxP
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / ℓ ^ 3)]
  calc (1 / ℓ ^ 3) * |∫ z in Work.BoseBox.bigBox ℓ u, Ψ (Function.update x i z)|
      ≤ (1 / ℓ ^ 3) * (M0 * ℓ ^ 3) := mul_le_mul_of_nonneg_left hI' (by positivity)
    _ = M0 := by field_simp

end Work.BoseBox
