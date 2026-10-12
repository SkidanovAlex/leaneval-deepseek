import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs8.A

open Submission.BoseGases

/-- **Pointwise domination of the localised one-body kernel `wSmall1Pair` by the two small-box
cutoffs** (repointed kernels).

The kernel factors as `χ_{B(u)}(x)·(g₀(x−y)/((χ_M⋆χ_M)((x−y)/(ℓd))·(χ⋆χ)((x−y)/ℓ)))·χ_{B(u)}(y)`;
the `(ℓd)`-denominator is `≥ smallConvLower M` on the support of `g₀`
(`abs_wSmallScaled_le`, viable because `supp v ⊆ ball 0 R₀` and `R₀ ≤ (ℓd)/16`) and the `ℓ`-denominator
is `≥ 1/2` there (regime `R₀ ≤ ℓ·chiR0`, `abs_inv_convScale_le_two`).  Both cutoff factors are
nonnegative, so

    `|wSmall1Pair| ≤ (2·smallConvLower M⁻¹)·χ_{B(u)}(x)·|g₀(x−y)|·χ_{B(u)}(y)`. -/
theorem abs_wSmall1Pair_chiB_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ (ℓ * d) / 16) (hRχ : R0 ≤ ℓ * chiR0) (u x y : EuclideanSpace ℝ (Fin 3)) :
    |Submission.BoseGases.wSmall1Pair h M ℓ d u x y| ≤
      (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) *
        Submission.BoseGases.chiSmallB M ℓ d u x *
        |Submission.BoseGases.g0 v h (x - y)| *
        Submission.BoseGases.chiSmallB M ℓ d u y := by
  have hcd : 0 < ℓ * d := mul_pos hℓ hd
  have hsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R0 ≤ ‖z‖ →
      Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  have hxnn : 0 ≤ chiSmallB M ℓ d u x := chiSmallB_nonneg M ℓ d u x
  have hynn : 0 ≤ chiSmallB M ℓ d u y := chiSmallB_nonneg M ℓ d u y
  have hW : |wSmallScaled M (ℓ * d) (g0 v h) (x - y)| ≤
      |g0 v h (x - y)| / Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.abs_wSmallScaled_le (M := M) (c := ℓ * d) (R := R0) hM hcd hsupp hR (x - y)
  have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hmid : |wSmallScaled M (ℓ * d) (g0 v h) (x - y) / convScale ℓ (x - y)| ≤
      2 * (|g0 v h (x - y)| / Work.SmallBoxSliding.smallConvLower M) := by
    by_cases hnorm : ‖x - y‖ ≤ R0
    · have hinv : |(convScale ℓ (x - y))⁻¹| ≤ 2 :=
        abs_inv_convScale_le_two (ℓ := ℓ) (R := R0) hℓ hRχ hnorm
      rw [div_eq_mul_inv, abs_mul]
      calc |wSmallScaled M (ℓ * d) (g0 v h) (x - y)| * |(convScale ℓ (x - y))⁻¹|
          ≤ (|g0 v h (x - y)| / Work.SmallBoxSliding.smallConvLower M) * 2 :=
            mul_le_mul hW hinv (abs_nonneg _) (div_nonneg (abs_nonneg _) (le_of_lt hSpos))
        _ = 2 * (|g0 v h (x - y)| / Work.SmallBoxSliding.smallConvLower M) := by ring
    · have hz0 : Submission.BoseGases.g0 v h (x - y) = 0 :=
        hsupp (x - y) (le_of_lt (lt_of_not_ge hnorm))
      have hw0 : wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) (x - y) = 0 := by
        dsimp [wSmallScaled]
        rw [hz0]
        ring
      rw [hw0, hz0, zero_div, abs_zero]
      simp
  have hm0 : 0 ≤ 2 * (|g0 v h (x - y)| / Work.SmallBoxSliding.smallConvLower M) :=
    mul_nonneg (by norm_num) (div_nonneg (abs_nonneg _) (le_of_lt hSpos))
  calc |Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
      = chiSmallB M ℓ d u x *
          |wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) (x - y) / convScale ℓ (x - y)| *
          chiSmallB M ℓ d u y := by
        unfold Submission.BoseGases.wSmall1Pair Submission.BoseGases.wSmallPair
        rw [abs_mul, abs_mul, abs_of_nonneg hxnn, abs_of_nonneg hynn]
    _ ≤ chiSmallB M ℓ d u x *
          (2 * (|g0 v h (x - y)| / Work.SmallBoxSliding.smallConvLower M)) *
          chiSmallB M ℓ d u y :=
        mul_le_mul (mul_le_mul_of_nonneg_left hmid hxnn) (le_refl _) hynn
          (mul_nonneg hxnn hm0)
    _ = (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * chiSmallB M ℓ d u x *
          |Submission.BoseGases.g0 v h (x - y)| * chiSmallB M ℓ d u y := by
        rw [div_eq_mul_inv]; ring

end Work.UBBInputs8.A
