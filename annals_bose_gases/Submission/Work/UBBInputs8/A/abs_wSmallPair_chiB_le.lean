import Mathlib.Tactic.Have
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs8.A

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- **Pointwise domination of the localised two-body kernel `wSmallPair` by the two small-box
cutoffs** (repointed kernels).

The kernel factors as `χ_{B(u)}(x)·(v(x−y)/((χ_M⋆χ_M)((x−y)/(ℓd))·(χ⋆χ)((x−y)/ℓ)))·χ_{B(u)}(y)`
with `|v| ≤ Bv`.  The `(ℓd)`-denominator is `≥ smallConvLower M` on the support of the numerator
(`abs_wSmallScaled_le`) and the `ℓ`-denominator is `≥ 1/2` there (regime `R₀ ≤ ℓ·chiR0`,
`abs_inv_convScale_le_two`); both cutoff factors are nonnegative, so

    `|wSmallPair| ≤ (2·Bv/smallConvLower M)·χ_{B(u)}(x)·χ_{B(u)}(y)`. -/
theorem abs_wSmallPair_chiB_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 Bv : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    (hvb : ∀ y : EuclideanSpace ℝ (Fin 3), |v y| ≤ Bv)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ (ℓ * d) / 16) (hRχ : R0 ≤ ℓ * chiR0) (u x y : EuclideanSpace ℝ (Fin 3)) :
    |Submission.BoseGases.wSmallPair M ℓ d u v x y| ≤
      (2 * Bv / Work.SmallBoxSliding.smallConvLower M) *
        Submission.BoseGases.chiSmallB M ℓ d u x * Submission.BoseGases.chiSmallB M ℓ d u y := by
  -- the support hypothesis in the form required by `abs_wSmallScaled_le`
  have hsupp : ∀ z : ℝ³, R0 ≤ ‖z‖ → v z = 0 := fun z hz => by
    by_contra h
    have hmem : z ∈ tsupport v := subset_tsupport v (by simpa [Function.mem_support] using h)
    have hb := hv_supp hmem
    rw [Metric.mem_ball, dist_zero_right] at hb
    exact absurd hb (not_lt.mpr hz)
  have hcpos : 0 < ℓ * d := mul_pos hℓ hd
  have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hBv : 0 ≤ Bv := le_trans (abs_nonneg (v 0)) (hvb 0)
  have hBdiv : 0 ≤ Bv / Work.SmallBoxSliding.smallConvLower M :=
    div_nonneg hBv (le_of_lt hSpos)
  have hW : |wSmallScaled M (ℓ * d) v (x - y)| ≤ Bv / Work.SmallBoxSliding.smallConvLower M :=
    le_trans
      (Work.SmallBoxSliding.abs_wSmallScaled_le (M := M) (c := ℓ * d) (R := R0)
        hM hcpos hsupp hR (x - y))
      (div_le_div_of_nonneg_right (hvb (x - y)) (le_of_lt hSpos))
  have hmid : |wSmallScaled M (ℓ * d) v (x - y) / convScale ℓ (x - y)| ≤
      2 * (Bv / Work.SmallBoxSliding.smallConvLower M) := by
    by_cases hnorm : ‖x - y‖ ≤ R0
    · have hinv : |(convScale ℓ (x - y))⁻¹| ≤ 2 :=
        abs_inv_convScale_le_two (ℓ := ℓ) (R := R0) hℓ hRχ hnorm
      rw [div_eq_mul_inv, abs_mul]
      calc |wSmallScaled M (ℓ * d) v (x - y)| * |(convScale ℓ (x - y))⁻¹|
          ≤ (Bv / Work.SmallBoxSliding.smallConvLower M) * 2 :=
            mul_le_mul hW hinv (abs_nonneg _) hBdiv
        _ = 2 * (Bv / Work.SmallBoxSliding.smallConvLower M) := by ring
    · have hz0 : v (x - y) = 0 := hsupp (x - y) (le_of_lt (lt_of_not_ge hnorm))
      have hw0 : wSmallScaled M (ℓ * d) v (x - y) = 0 := by
        dsimp [wSmallScaled]
        rw [hz0]
        ring
      rw [hw0, zero_div, abs_zero]
      positivity
  have hx0 : 0 ≤ chiSmallB M ℓ d u x := chiSmallB_nonneg M ℓ d u x
  have hy0 : 0 ≤ chiSmallB M ℓ d u y := chiSmallB_nonneg M ℓ d u y
  have hm0 : 0 ≤ 2 * (Bv / Work.SmallBoxSliding.smallConvLower M) :=
    mul_nonneg (by norm_num) hBdiv
  calc |Submission.BoseGases.wSmallPair M ℓ d u v x y|
      = chiSmallB M ℓ d u x * |wSmallScaled M (ℓ * d) v (x - y) / convScale ℓ (x - y)| *
          chiSmallB M ℓ d u y := by
        unfold Submission.BoseGases.wSmallPair
        rw [abs_mul, abs_mul, abs_of_nonneg hx0, abs_of_nonneg hy0]
    _ ≤ chiSmallB M ℓ d u x * (2 * (Bv / Work.SmallBoxSliding.smallConvLower M)) *
          chiSmallB M ℓ d u y :=
        mul_le_mul (mul_le_mul_of_nonneg_left hmid hx0) (le_refl _) hy0 (mul_nonneg hx0 hm0)
    _ = (2 * Bv / Work.SmallBoxSliding.smallConvLower M) * chiSmallB M ℓ d u x *
          chiSmallB M ℓ d u y := by ring

end Work.UBBInputs8.A
