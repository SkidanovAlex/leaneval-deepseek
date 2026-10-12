import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.UBBInputs2.LocPotential
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs2

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory Metric
open Submission.BoseGases

/-- **Pointwise domination of the localised two-body kernel `wSmallPair`** with
numerator `v`: same shape as `Work.SmallBoxSliding.abs_wSmall1Pair_le` but for
the potential `v` itself rather than `g0 v h`.  At the REPOINTED kernels the `ℓ`-scale corpus
cutoff is bounded by its sup `chiSupAbs` and the `ℓ`-scale denominator `(χ⋆χ)(·/ℓ)` by `1/2`
(regime `R0 ≤ ℓ·chiR0`); the `(ℓd)`-scale factor is bounded by `chiSmallDecay M` and its
denominator below by `smallConvLower M`. -/
theorem abs_wSmallPair_v_le {v : ℝ³ → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R0)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ (ℓ * d) / 16) (hRχ : R0 ≤ ℓ * chiR0) (u x y : ℝ³) :
    |wSmallPair M ℓ d u v x y| ≤
      (chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • x - u)) *
        ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M) *
          |v (x - y)|) := by
  have hcpos : 0 < ℓ * d := mul_pos hℓ hd
  have hsupp : ∀ z : ℝ³, R0 ≤ ‖z‖ → v z = 0 :=
    fun z hz => Work.SmallBoxSliding.eq_zero_of_tsupport_subset_ball hv_supp hz
  have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M := Work.SmallBoxSliding.smallConvLower_pos M
  have hx : |chiSmallB M ℓ d u x| ≤ chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • x - u) :=
    Work.SmallBoxSliding.abs_chiSmallB_le (M := M) (ℓ := ℓ) (d := d) hM u x
  have hy : |chiSmallB M ℓ d u y| ≤ chiSupAbs * chiSmallDecay M := by
    refine le_trans (Work.SmallBoxSliding.abs_chiSmallB_le (M := M) (ℓ := ℓ) (d := d) hM u y) ?_
    have hb2 : chiSmall M ((ℓ * d)⁻¹ • y - u) ≤ chiSmallDecay M := by
      have hb' := chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • y - u)
      rwa [abs_of_nonneg (chiSmall_nonneg M _)] at hb'
    exact mul_le_mul_of_nonneg_left hb2 chiSupAbs_nonneg
  have hD2 : |wSmallScaled M (ℓ * d) v (x - y)| ≤ |v (x - y)| / Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.abs_wSmallScaled_le (M := M) (c := ℓ * d) (R := R0) hM hcpos hsupp hR (x - y)
  have hmid : |wSmallScaled M (ℓ * d) v (x - y) / convScale ℓ (x - y)| ≤
      2 * (|v (x - y)| / Work.SmallBoxSliding.smallConvLower M) := by
    by_cases hnorm : ‖x - y‖ ≤ R0
    · have hinv : |(convScale ℓ (x - y))⁻¹| ≤ 2 :=
        abs_inv_convScale_le_two (ℓ := ℓ) (R := R0) hℓ hRχ hnorm
      rw [div_eq_mul_inv, abs_mul]
      calc
        |wSmallScaled M (ℓ * d) v (x - y)| * |(convScale ℓ (x - y))⁻¹|
            ≤ (|v (x - y)| / Work.SmallBoxSliding.smallConvLower M) * 2 :=
              mul_le_mul hD2 hinv (abs_nonneg _)
                (div_nonneg (abs_nonneg _) (le_of_lt hSpos))
        _ = 2 * (|v (x - y)| / Work.SmallBoxSliding.smallConvLower M) := by ring
    · have hz0 : v (x - y) = 0 := hsupp (x - y) (le_of_lt (lt_of_not_ge hnorm))
      have hw0 : wSmallScaled M (ℓ * d) v (x - y) = 0 := by
        dsimp [wSmallScaled]
        rw [hz0]
        ring
      rw [hw0, hz0, zero_div, abs_zero]
      simp
  have hA0 : 0 ≤ chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • x - u) :=
    mul_nonneg chiSupAbs_nonneg (chiSmall_nonneg M _)
  have hm0 : 0 ≤ 2 * (|v (x - y)| / Work.SmallBoxSliding.smallConvLower M) :=
    mul_nonneg (by norm_num) (div_nonneg (abs_nonneg _) (le_of_lt hSpos))
  calc
    |wSmallPair M ℓ d u v x y|
        = |chiSmallB M ℓ d u x| * |wSmallScaled M (ℓ * d) v (x - y) / convScale ℓ (x - y)|
            * |chiSmallB M ℓ d u y| := by
          unfold wSmallPair
          rw [abs_mul, abs_mul]
    _ ≤ (chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • x - u))
          * (2 * (|v (x - y)| / Work.SmallBoxSliding.smallConvLower M))
          * (chiSupAbs * chiSmallDecay M) :=
          mul_le_mul (mul_le_mul hx hmid (abs_nonneg _) hA0) hy (abs_nonneg _)
            (mul_nonneg hA0 hm0)
    _ = (chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • x - u)) *
          ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M) *
            |v (x - y)|) := by ring

/-- **Uniform-in-`(a,b)` bound for the sliding integral of `|wSmallPair · v|`.**

No integrability of `v` is needed; only that `v` vanishes outside `ball 0 R0` with
`R0 ≤ (ℓ*d)/16` (so that the `(ℓd)`-scale denominator never vanishes on the support) and the
repointing regime `R0 ≤ ℓ·chiR0` (so that the `ℓ`-scale denominator `(χ⋆χ)(·/ℓ) ≥ 1/2` there).
The constant is `chiSupAbs · (2·(chiSupAbs·chiSmallDecay M)/smallConvLower M) · ∫χ_M`. -/
theorem exists_integral_u_wSmallPair_bound {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ (ℓ * d) / 16) (hRχ : R0 ≤ ℓ * chiR0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : EuclideanSpace ℝ (Fin 3),
      ∫ u : EuclideanSpace ℝ (Fin 3),
        ‖Submission.BoseGases.wSmallPair M ℓ d u v a b‖ ≤ C * ‖v (a - b)‖ := by
  have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M := Work.SmallBoxSliding.smallConvLower_pos M
  refine ⟨chiSupAbs * (2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
      * (∫ z : ℝ³, chiSmall M z), ?_, ?_⟩
  · have hI : 0 ≤ ∫ z : ℝ³, chiSmall M z := integral_nonneg (fun z => chiSmall_nonneg M z)
    have hK : 0 ≤ 2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M :=
      div_nonneg (mul_nonneg (by norm_num) (mul_nonneg chiSupAbs_nonneg (chiSmallDecay_nonneg M)))
        (le_of_lt hSpos)
    exact mul_nonneg (mul_nonneg chiSupAbs_nonneg hK) hI
  · intro a b
    set K : ℝ := chiSupAbs * (2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
      * |v (a - b)| with hK
    have hgi : Integrable (fun u : ℝ³ => chiSmall M ((ℓ * d)⁻¹ • a - u)) :=
      Work.SmallBoxSliding.integrable_chiSmall_shift hM ((ℓ * d)⁻¹ • a)
    have hgint : Integrable (fun u : ℝ³ => K * chiSmall M ((ℓ * d)⁻¹ • a - u)) :=
      hgi.const_mul K
    have step1 : ∫ u : ℝ³, ‖wSmallPair M ℓ d u v a b‖ ≤
        ∫ u : ℝ³, K * chiSmall M ((ℓ * d)⁻¹ • a - u) := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ (fun u => norm_nonneg _)
      · exact hgint
      · filter_upwards with u
        have h := abs_wSmallPair_v_le hv_supp hM hℓ hd hR hRχ u a b
        rw [Real.norm_eq_abs]
        calc |wSmallPair M ℓ d u v a b|
            ≤ (chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • a - u)) *
                ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
                  * |v (a - b)|) := h
          _ = K * chiSmall M ((ℓ * d)⁻¹ • a - u) := by rw [hK]; ring
    calc ∫ u : ℝ³, ‖wSmallPair M ℓ d u v a b‖
        ≤ ∫ u : ℝ³, K * chiSmall M ((ℓ * d)⁻¹ • a - u) := step1
      _ = K * ∫ u : ℝ³, chiSmall M ((ℓ * d)⁻¹ • a - u) :=
            integral_const_mul K _
      _ = K * ∫ z : ℝ³, chiSmall M z := by
            rw [integral_sub_left_eq_self (f := fun z : ℝ³ => chiSmall M z)
              (μ := (volume : Measure ℝ³)) (x' := (ℓ * d)⁻¹ • a)]
      _ = (chiSupAbs * (2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
            * (∫ z : ℝ³, chiSmall M z)) * ‖v (a - b)‖ := by
            rw [hK, Real.norm_eq_abs]; ring

end Work.UBBInputs2
