import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1.WB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Pointwise domination of the localised one-body kernel at an explicit `r₀`-witness

This is the `R₀ ≤ ℓ·r₀` companion of `Work.SmallBoxSliding.abs_wSmall1Pair_le`,
stated *without* the packaged `chiR0` witness and *without* paying the `chiSupAbs`
factors: the `ℓ`-scale lower bound `1/2 ≤ (χ⋆χ)(·/ℓ)` is taken directly from the
hypothesis `hC` on the ball `‖x‖ ≤ r₀` (the `r₀` of the requested statement), and
the two `chiSmallB` factors are kept as such on the right-hand side.

The chain is the usual one.  `wSmall1Pair` factors as

    χ_{B(u)}(x) · ( g₀(x−y) / ( (χ_M⋆χ_M)((x−y)/(ℓd)) · (χ⋆χ)((x−y)/ℓ) ) ) · χ_{B(u)}(y);

on the support `‖x−y‖ ≤ R₀` of `g₀` the `(ℓd)`-denominator is `≥ smallConvLower M`
(`abs_wSmallScaled_le`, using `R₀ ≤ ℓd/16`) and the `ℓ`-denominator is `≥ 1/2`
(the hypothesis `hC`, using `R₀ ≤ ℓ·r₀`), while off the support everything vanishes.
-/

namespace Work.BoseFixB1.WB

theorem abs_wSmall1Pair_le_r0 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ} {M : ℕ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (h : Work.UBB.ScatSol v) (hM : 1 ≤ M)
    {ℓ d r₀ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hR : R0 ≤ ℓ * d / 16) (hr₀ : 0 < r₀)
    (hRℓ : R0 ≤ ℓ * r₀)
    (hC : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ r₀ →
        1 / 2 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x) :
    ∀ u x y : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
        ≤ 2 / Work.SmallBoxSliding.smallConvLower M
            * |Submission.BoseGases.chiSmallB M ℓ d u x|
            * |Submission.BoseGases.g0 v h (x - y)|
            * |Submission.BoseGases.chiSmallB M ℓ d u y| := by
  intro u x y
  have hc : 0 < ℓ * d := mul_pos hℓ hd
  have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hSnn : 0 ≤ Work.SmallBoxSliding.smallConvLower M := le_of_lt hSpos
  have hsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R0 ≤ ‖z‖ →
      Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  have hℓi : 0 ≤ ℓ⁻¹ := inv_nonneg.mpr (le_of_lt hℓ)
  -- the `ℓ`-scale denominator exceeds `1/2` wherever `g₀` can be nonzero
  have hconv : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R0 →
      1 / 2 ≤ Submission.BoseGases.convScale ℓ z := by
    intro z hz
    have hz' : ‖(ℓ⁻¹) • z‖ ≤ r₀ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hℓi]
      calc ℓ⁻¹ * ‖z‖ ≤ ℓ⁻¹ * R0 := mul_le_mul_of_nonneg_left hz hℓi
        _ ≤ ℓ⁻¹ * (ℓ * r₀) := mul_le_mul_of_nonneg_left hRℓ hℓi
        _ = r₀ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hℓ), one_mul]
    simpa [Submission.BoseGases.convScale] using hC ((ℓ⁻¹) • z) hz'
  have hmid : |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) (x - y)
      / Submission.BoseGases.convScale ℓ (x - y)| ≤
        2 * (|Submission.BoseGases.g0 v h (x - y)| / Work.SmallBoxSliding.smallConvLower M) := by
    by_cases hnorm : ‖x - y‖ ≤ R0
    · have hh := hconv (x - y) hnorm
      have hpos : 0 < Submission.BoseGases.convScale ℓ (x - y) := lt_of_lt_of_le (by norm_num) hh
      have hinv : |(Submission.BoseGases.convScale ℓ (x - y))⁻¹| ≤ 2 := by
        rw [abs_of_nonneg (inv_nonneg.mpr (le_of_lt hpos))]
        calc (Submission.BoseGases.convScale ℓ (x - y))⁻¹
              = 1 / Submission.BoseGases.convScale ℓ (x - y) := by rw [one_div]
          _ ≤ 1 / (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hh
          _ = 2 := by norm_num
      have hD2 := Work.SmallBoxSliding.abs_wSmallScaled_le (M := M) (c := ℓ * d) (R := R0)
        hM hc hsupp hR (x - y)
      rw [div_eq_mul_inv, abs_mul]
      calc |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) (x - y)|
            * |(Submission.BoseGases.convScale ℓ (x - y))⁻¹|
          ≤ (|Submission.BoseGases.g0 v h (x - y)| / Work.SmallBoxSliding.smallConvLower M) * 2 :=
            mul_le_mul hD2 hinv (abs_nonneg _) (div_nonneg (abs_nonneg _) hSnn)
        _ = 2 * (|Submission.BoseGases.g0 v h (x - y)| / Work.SmallBoxSliding.smallConvLower M) := by
            ring
    · have hz0 : Submission.BoseGases.g0 v h (x - y) = 0 :=
        hsupp (x - y) (le_of_lt (lt_of_not_ge hnorm))
      have hw0 : Submission.BoseGases.wSmallScaled M (ℓ * d)
          (Submission.BoseGases.g0 v h) (x - y) = 0 := by
        dsimp [Submission.BoseGases.wSmallScaled]
        rw [hz0]
        ring
      rw [hw0, hz0]
      simp
  have hm0 : 0 ≤ 2 * (|Submission.BoseGases.g0 v h (x - y)|
      / Work.SmallBoxSliding.smallConvLower M) :=
    mul_nonneg (by norm_num) (div_nonneg (abs_nonneg _) hSnn)
  calc
    |Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
        = |Submission.BoseGases.chiSmallB M ℓ d u x|
            * |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) (x - y)
                / Submission.BoseGases.convScale ℓ (x - y)|
            * |Submission.BoseGases.chiSmallB M ℓ d u y| := by
          unfold Submission.BoseGases.wSmall1Pair Submission.BoseGases.wSmallPair
          rw [abs_mul, abs_mul]
    _ ≤ |Submission.BoseGases.chiSmallB M ℓ d u x|
            * (2 * (|Submission.BoseGases.g0 v h (x - y)| / Work.SmallBoxSliding.smallConvLower M))
            * |Submission.BoseGases.chiSmallB M ℓ d u y| :=
          mul_le_mul (mul_le_mul_of_nonneg_left hmid (abs_nonneg _)) le_rfl (abs_nonneg _)
            (mul_nonneg (abs_nonneg _) hm0)
    _ = 2 / Work.SmallBoxSliding.smallConvLower M
            * |Submission.BoseGases.chiSmallB M ℓ d u x|
            * |Submission.BoseGases.g0 v h (x - y)|
            * |Submission.BoseGases.chiSmallB M ℓ d u y| := by ring

end Work.BoseFixB1.WB
