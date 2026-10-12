import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1.abs_wSmallPair_le
import Submission.Work.UBB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

/-- **Pointwise domination of the localised two-body kernel at the numerator
`g₂`, directly against the two `chiSmallB` cutoffs.**

The kernel factors as `χ_{B(u)}(x)·(g₂(x−y)/((χ_M⋆χ_M)((x−y)/(ℓd))·(χ⋆χ)((x−y)/ℓ)))·χ_{B(u)}(y)`.
Both cutoffs are nonnegative, so `|χ_{B(u)}| = χ_{B(u)}`; the renormalisation
denominator `(χ_M⋆χ_M)(·/(ℓd))` is `≥ smallConvLower M > 0` on `supp g₂`
(viable because `supp v ⊆ ball 0 R₀` and `R₀ ≤ (ℓd)/16`, so `supp g₂ ⊆ ball 0 R₀`
as well), and the `ℓ`-denominator is `≥ 1/2` on `‖x−y‖ ≤ R₀ ≤ ℓ·chiR0`;
off the support of `g₂` the numerator vanishes and both sides are `0`. -/
theorem abs_wSmallPair_g2_chiB_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ (ℓ * d) / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u x y : EuclideanSpace ℝ (Fin 3)) :
    |Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) x y| ≤
      (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) *
        Submission.BoseGases.chiSmallB M ℓ d u x *
        |Submission.BoseGases.g2 v h (x - y)| *
        Submission.BoseGases.chiSmallB M ℓ d u y := by
  -- `g₂` inherits the support of `v`
  have hsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R0 ≤ ‖z‖ →
      Submission.BoseGases.g2 v h z = 0 :=
    fun z hz => Submission.BoseGases.g2_zero_of_norm_ge hv_supp hz h
  have hcpos : 0 < ℓ * d := mul_pos hℓ hd
  have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  -- the renormalised kernel is dominated by the numerator, on the support
  have hD2 : |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g2 v h)
        (x - y)| ≤
      |Submission.BoseGases.g2 v h (x - y)| / Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.abs_wSmallScaled_le (M := M) (c := ℓ * d) (R := R0)
      hM hcpos hsupp hR (x - y)
  -- the `ℓ`-scale denominator is `≥ 1/2` on the support of `g₂`
  have hmid : |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g2 v h) (x - y)
      / Submission.BoseGases.convScale ℓ (x - y)| ≤
        2 * (|Submission.BoseGases.g2 v h (x - y)| / Work.SmallBoxSliding.smallConvLower M) := by
    by_cases hnorm : ‖x - y‖ ≤ R0
    · have hinv : |(Submission.BoseGases.convScale ℓ (x - y))⁻¹| ≤ 2 :=
        Submission.BoseGases.abs_inv_convScale_le_two (ℓ := ℓ) (R := R0) hℓ hRχ hnorm
      rw [div_eq_mul_inv, abs_mul]
      calc
        |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g2 v h) (x - y)|
              * |(Submission.BoseGases.convScale ℓ (x - y))⁻¹|
            ≤ (|Submission.BoseGases.g2 v h (x - y)| / Work.SmallBoxSliding.smallConvLower M) * 2 :=
              mul_le_mul hD2 hinv (abs_nonneg _) (div_nonneg (abs_nonneg _) (le_of_lt hSpos))
        _ = 2 * (|Submission.BoseGases.g2 v h (x - y)| / Work.SmallBoxSliding.smallConvLower M) := by
              ring
    · have hz0 : Submission.BoseGases.g2 v h (x - y) = 0 :=
        hsupp (x - y) (le_of_lt (lt_of_not_ge hnorm))
      have hw0 : Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g2 v h)
          (x - y) = 0 := by
        dsimp [Submission.BoseGases.wSmallScaled]
        rw [hz0]
        ring
      rw [hw0, hz0]
      simp
  have hx0 : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u x :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u x
  have hy0 : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u y :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u y
  have hm0 : 0 ≤ 2 * (|Submission.BoseGases.g2 v h (x - y)| /
      Work.SmallBoxSliding.smallConvLower M) :=
    mul_nonneg (by norm_num) (div_nonneg (abs_nonneg _) (le_of_lt hSpos))
  calc
    |Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) x y|
        = |Submission.BoseGases.chiSmallB M ℓ d u x|
            * |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g2 v h) (x - y)
                / Submission.BoseGases.convScale ℓ (x - y)|
            * |Submission.BoseGases.chiSmallB M ℓ d u y| := by
          unfold Submission.BoseGases.wSmallPair
          rw [abs_mul, abs_mul]
    _ ≤ Submission.BoseGases.chiSmallB M ℓ d u x
          * (2 * (|Submission.BoseGases.g2 v h (x - y)| / Work.SmallBoxSliding.smallConvLower M))
          * Submission.BoseGases.chiSmallB M ℓ d u y := by
          rw [abs_of_nonneg hx0, abs_of_nonneg hy0]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hmid hx0) le_rfl hy0 (mul_nonneg hx0 hm0)
    _ = (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) *
          Submission.BoseGases.chiSmallB M ℓ d u x *
          |Submission.BoseGases.g2 v h (x - y)| *
          Submission.BoseGases.chiSmallB M ℓ d u y := by ring

end Work.BoseFixB1S
