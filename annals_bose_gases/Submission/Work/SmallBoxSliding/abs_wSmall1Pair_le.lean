import ChallengeDeps
import Submission.Work.SmallBoxSliding.qLHSBAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxSliding

open Submission.BoseGases

/-- **Pointwise domination of the localised one-body kernel `wSmall1Pair`** at the
REPOINTED kernels.

The localised kernel factors as
`χ(x/ℓ)·(g₀(x−y)/((χ_M⋆χ_M)((x−y)/(ℓd))·(χ⋆χ)((x−y)/ℓ)))·χ(y/ℓ)`; bounding each cutoff
factor by `chiSupAbs · chiSmallDecay M` (the `ℓ`-scale corpus factor by its sup `chiSupAbs`, the
`(ℓd)`-scale factor by its sup `chiSmallDecay M`), the `(ℓd)`-denominator below by
`smallConvLower M` (viable on the support because `g₀` vanishes outside `ball 0 R₀` and
`R₀ ≤ (ℓd)/16`) and the `ℓ`-denominator below by `1/2` (viable because `R₀ ≤ ℓ·chiR0`), gives
the stated pointwise bound. -/
theorem abs_wSmall1Pair_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ (ℓ * d) / 16) (hRχ : R0 ≤ ℓ * chiR0)
    (u x y : EuclideanSpace ℝ (Fin 3)) :
    |Submission.BoseGases.wSmall1Pair h M ℓ d u x y| ≤
      (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
        * (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
            * |Submission.BoseGases.g0 v h (x - y)|) / smallConvLower M := by
  have hcpos : 0 < ℓ * d := mul_pos hℓ hd
  have hsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R0 ≤ ‖z‖ → g0 v h z = 0 :=
    fun z hz => g0_zero_of_norm_ge hv_supp hz h
  have hDnn : 0 ≤ Submission.BoseGases.chiSmallDecay M :=
    Submission.BoseGases.chiSmallDecay_nonneg M
  have hSpos : 0 < smallConvLower M := smallConvLower_pos M
  have hx : |Submission.BoseGases.chiSmallB M ℓ d u x| ≤
      Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) :=
    abs_chiSmallB_le (M := M) (ℓ := ℓ) (d := d) hM u x
  have hy : |Submission.BoseGases.chiSmallB M ℓ d u y| ≤
      Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
    refine le_trans (abs_chiSmallB_le (M := M) (ℓ := ℓ) (d := d) hM u y) ?_
    have hb2 : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)
        ≤ Submission.BoseGases.chiSmallDecay M := by
      have hb' := Submission.BoseGases.chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • y - u)
      rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at hb'
    exact mul_le_mul_of_nonneg_left hb2 Submission.BoseGases.chiSupAbs_nonneg
  have hD2 : |Submission.BoseGases.wSmallScaled M (ℓ * d) (g0 v h) (x - y)| ≤
      |g0 v h (x - y)| / smallConvLower M :=
    abs_wSmallScaled_le (M := M) (c := ℓ * d) (R := R0) hM hcpos hsupp hR (x - y)
  have hmid : |Submission.BoseGases.wSmallScaled M (ℓ * d) (g0 v h) (x - y)
      / Submission.BoseGases.convScale ℓ (x - y)| ≤
        2 * (|g0 v h (x - y)| / smallConvLower M) := by
    by_cases hnorm : ‖x - y‖ ≤ R0
    · have hinv : |(Submission.BoseGases.convScale ℓ (x - y))⁻¹| ≤ 2 :=
        Submission.BoseGases.abs_inv_convScale_le_two (ℓ := ℓ) (R := R0) hℓ hRχ hnorm
      rw [div_eq_mul_inv, abs_mul]
      calc
        |Submission.BoseGases.wSmallScaled M (ℓ * d) (g0 v h) (x - y)|
              * |(Submission.BoseGases.convScale ℓ (x - y))⁻¹|
            ≤ (|g0 v h (x - y)| / smallConvLower M) * 2 :=
              mul_le_mul hD2 hinv (abs_nonneg _) (div_nonneg (abs_nonneg _) (le_of_lt hSpos))
        _ = 2 * (|g0 v h (x - y)| / smallConvLower M) := by ring
    · have hz0 : g0 v h (x - y) = 0 := hsupp (x - y) (le_of_lt (lt_of_not_ge hnorm))
      have hw0 : Submission.BoseGases.wSmallScaled M (ℓ * d) (g0 v h) (x - y) = 0 := by
        dsimp [Submission.BoseGases.wSmallScaled]
        rw [hz0]
        ring
      rw [hw0, hz0, zero_div, abs_zero]
      simp
  have hB0 : 0 ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg hDnn
  have hA0 : 0 ≤ Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmall_nonneg M _)
  have hm0 : 0 ≤ 2 * (|g0 v h (x - y)| / smallConvLower M) :=
    mul_nonneg (by norm_num) (div_nonneg (abs_nonneg _) (le_of_lt hSpos))
  calc
    |Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
        = |Submission.BoseGases.chiSmallB M ℓ d u x|
            * |Submission.BoseGases.wSmallScaled M (ℓ * d) (g0 v h) (x - y)
                / Submission.BoseGases.convScale ℓ (x - y)|
            * |Submission.BoseGases.chiSmallB M ℓ d u y| := by
          unfold Submission.BoseGases.wSmall1Pair Submission.BoseGases.wSmallPair
          rw [abs_mul, abs_mul]
    _ ≤ (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
          * (2 * (|g0 v h (x - y)| / smallConvLower M))
          * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) :=
          mul_le_mul (mul_le_mul hx hmid (abs_nonneg _) hA0) hy (abs_nonneg _)
            (mul_nonneg hA0 hm0)
    _ = (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
          * (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
              * |Submission.BoseGases.g0 v h (x - y)|) / smallConvLower M := by ring

end Work.SmallBoxSliding
