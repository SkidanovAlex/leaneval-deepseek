import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseFixB1S.conv48Consts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.chiSmallBase_pair_cube_lower_conv48`

Lower bound at the cube `K = {|y_j - z_j/2| ≤ 1/48}` (`|z_j| ≤ 1/16`) for the pair
integral of the *unnormalised* small-scale bump `chiSmallBase 48`.

Everything is elementary and coordinatewise:

* if `|z_j| ≤ 1/16` and `|(y - z/2)_j| ≤ 1/48` then `|y_j| ≤ 1/32 + 1/48 = 5/96` and
  `|(z - y)_j| = |z_j/2 - (y - z/2)_j| ≤ 1/32 + 1/48 = 5/96`; since `|s| ≤ 5/96`
  implies `zeta1d s = cos(π s) ≥ conv48L` (`Work.BoseFixB1S.zeta1d_ge_conv48L`), each of
  the six factors of `chiSmallBase 48 y · chiSmallBase 48 (z-y)` is `≥ conv48L` (all
  factors are nonnegative), so on `K` the product is `≥ (conv48L³)^48 · (conv48L³)^48 =
  conv48L^288`;
* `K` is a translate of the coordinate cube `[-1/48,1/48]³`, of volume `(1/24)³ = 1/13824`;
* the integrand is bounded by `1` (each `|zeta1d| ≤ 1`), hence integrable on `K`, and
  `∫_K f ≥ ∫_K conv48L^288 = conv48L^288 · vol K` by `setIntegral_mono_on`.

Conventions: `chiSmallBase M z = (ζ(z₀)ζ(z₁)ζ(z₂))^M` with
`ζ = Submission.BoseGases.zeta1d`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option autoImplicit false

/-! ### Auxiliary facts -/

/-- `|chiSmallBase M z| ≤ 1`: the product of three `|zeta1d| ≤ 1` raised to the `M`-th power. -/
lemma pc48_abs_chiSmallBase_le_one (M : ℕ) (z : EuclideanSpace ℝ (Fin 3)) :
    |chiSmallBase M z| ≤ 1 := by
  have h0 : |zeta1d (z.ofLp 0)| ≤ 1 := abs_zeta1d_le_one _
  have h1 : |zeta1d (z.ofLp 1)| ≤ 1 := abs_zeta1d_le_one _
  have h2 : |zeta1d (z.ofLp 2)| ≤ 1 := abs_zeta1d_le_one _
  have hprod : |zeta1d (z.ofLp 0) * zeta1d (z.ofLp 1) * zeta1d (z.ofLp 2)| ≤ 1 := by
    rw [abs_mul, abs_mul]
    exact mul_le_one₀ (mul_le_one₀ h0 (abs_nonneg _) h1) (abs_nonneg _) h2
  rw [chiSmallBase, abs_pow]
  exact pow_le_one₀ (abs_nonneg _) hprod

/-- If all three coordinates of `a` satisfy `|·| ≤ 5/96` then `chiSmallBase 48 a ≥ conv48L^144`. -/
lemma pc48_conv48L_pow144_le_chiSmallBase (a : EuclideanSpace ℝ (Fin 3))
    (ha : ∀ j : Fin 3, |a.ofLp j| ≤ 5 / 96) :
    conv48L ^ 144 ≤ chiSmallBase 48 a := by
  have hL : 0 ≤ conv48L := conv48L_nonneg
  have h0 : conv48L ≤ zeta1d (a.ofLp 0) := zeta1d_ge_conv48L _ (ha 0)
  have h1 : conv48L ≤ zeta1d (a.ofLp 1) := zeta1d_ge_conv48L _ (ha 1)
  have h2 : conv48L ≤ zeta1d (a.ofLp 2) := zeta1d_ge_conv48L _ (ha 2)
  have hL3 : conv48L ^ 3 ≤ zeta1d (a.ofLp 0) * zeta1d (a.ofLp 1) * zeta1d (a.ofLp 2) := by
    have h01 : conv48L * conv48L ≤ zeta1d (a.ofLp 0) * zeta1d (a.ofLp 1) :=
      mul_le_mul h0 h1 hL (zeta1d_nonneg _)
    have h := mul_le_mul h01 h2 hL (mul_nonneg (zeta1d_nonneg _) (zeta1d_nonneg _))
    calc conv48L ^ 3 = (conv48L * conv48L) * conv48L := by ring
      _ ≤ _ := h
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ conv48L ^ 3) hL3 48
  rw [chiSmallBase]
  calc conv48L ^ 144 = (conv48L ^ 3) ^ 48 := by ring
    _ ≤ _ := hpow

/-- **Pointwise lower bound on the cube.**  For `|z_j| ≤ 1/16` and `|(y - z/2)_j| ≤ 1/48`
(all `j`), `chiSmallBase 48 y · chiSmallBase 48 (z-y) ≥ conv48L^288`. -/
lemma pc48_pointwise (z y : EuclideanSpace ℝ (Fin 3))
    (hz : ∀ j : Fin 3, |z.ofLp j| ≤ 1 / 16)
    (hy : ∀ j : Fin 3, |(y - (1 / 2 : ℝ) • z).ofLp j| ≤ 1 / 48) :
    conv48L ^ 288 ≤ chiSmallBase 48 y * chiSmallBase 48 (z - y) := by
  have hy' : ∀ j : Fin 3, |y.ofLp j - (1 / 2) * z.ofLp j| ≤ 1 / 48 := by
    intro j
    have h := hy j
    simpa only [WithLp.ofLp_sub, Pi.sub_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      using h
  have hyabs : ∀ j : Fin 3, |y.ofLp j| ≤ 5 / 96 := by
    intro j
    have h := abs_le.mp (hy' j)
    have hz' := abs_le.mp (hz j)
    rw [abs_le]
    constructor <;> linarith [h.1, h.2, hz'.1, hz'.2]
  have hzyabs : ∀ j : Fin 3, |(z - y).ofLp j| ≤ 5 / 96 := by
    intro j
    have hsub : (z - y).ofLp j = z.ofLp j - y.ofLp j := by
      simp only [WithLp.ofLp_sub, Pi.sub_apply]
    rw [hsub, abs_le]
    have h := abs_le.mp (hy' j)
    have hz' := abs_le.mp (hz j)
    constructor <;> linarith [h.1, h.2, hz'.1, hz'.2]
  have h1 := pc48_conv48L_pow144_le_chiSmallBase y hyabs
  have h2 := pc48_conv48L_pow144_le_chiSmallBase (z - y) hzyabs
  calc conv48L ^ 288 = conv48L ^ 144 * conv48L ^ 144 := by ring
    _ ≤ chiSmallBase 48 y * chiSmallBase 48 (z - y) :=
        mul_le_mul h1 h2 (pow_nonneg conv48L_nonneg 144) (chiSmallBase_nonneg 48 y)

/-- The coordinate cube `{|y_j - a_j| ≤ 1/48}` in `EuclideanSpace ℝ (Fin 3)` has volume
`(1/24)³ = 1/13824`. -/
lemma pc48_volume_cube (a : EuclideanSpace ℝ (Fin 3)) :
    volume {y : EuclideanSpace ℝ (Fin 3) | ∀ j : Fin 3, |(y - a).ofLp j| ≤ 1 / 48}
      = ENNReal.ofReal (1 / 13824) := by
  -- transport the Lebesgue measure on `EuclideanSpace ℝ (Fin 3)` to the product measure on
  -- `Fin 3 → ℝ` along the measure preserving equivalence `WithLp.toLp 2`
  have hmp : MeasurePreserving (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3))
      volume volume :=
    PiLp.volume_preserving_toLp (Fin 3)
  have hmeas : MeasurableSet
      {y : EuclideanSpace ℝ (Fin 3) | ∀ j : Fin 3, |(y - a).ofLp j| ≤ 1 / 48} := by
    have hcl : IsClosed
        {y : EuclideanSpace ℝ (Fin 3) | ∀ j : Fin 3, |(y - a).ofLp j| ≤ 1 / 48} := by
      rw [show {y : EuclideanSpace ℝ (Fin 3) | ∀ j : Fin 3, |(y - a).ofLp j| ≤ 1 / 48}
            = ⋂ j : Fin 3, {y : EuclideanSpace ℝ (Fin 3) | |(y - a).ofLp j| ≤ 1 / 48} by
          ext y; simp]
      refine isClosed_iInter (fun j => isClosed_le ?_ continuous_const)
      exact continuous_abs.comp
        ((Submission.BoseGases.coord_continuous j).comp (continuous_id.sub continuous_const))
    exact hcl.measurableSet
  have hv : volume ((WithLp.toLp 2) ⁻¹'
        {y : EuclideanSpace ℝ (Fin 3) | ∀ j : Fin 3, |(y - a).ofLp j| ≤ 1 / 48})
      = volume {y : EuclideanSpace ℝ (Fin 3) | ∀ j : Fin 3, |(y - a).ofLp j| ≤ 1 / 48} :=
    hmp.measure_preimage hmeas.nullMeasurableSet
  rw [← hv]
  have hset : (WithLp.toLp 2) ⁻¹'
        {y : EuclideanSpace ℝ (Fin 3) | ∀ j : Fin 3, |(y - a).ofLp j| ≤ 1 / 48}
      = Set.univ.pi (fun j : Fin 3 => Set.Icc (a.ofLp j - 1 / 48) (a.ofLp j + 1 / 48)) := by
    ext w
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Icc,
      WithLp.ofLp_sub, Pi.sub_apply]
    rw [forall_and]
    constructor
    · intro h
      exact ⟨fun j => by have := (abs_le.mp (h j)).1; linarith,
             fun j => by have := (abs_le.mp (h j)).2; linarith⟩
    · intro h j
      exact abs_le.mpr ⟨by have := h.1 j; linarith, by have := h.2 j; linarith⟩
  rw [hset, MeasureTheory.volume_pi_pi]
  simp only [Real.volume_Icc]
  simp_rw [show ∀ j : Fin 3,
      ENNReal.ofReal ((a.ofLp j + 1 / 48) - (a.ofLp j - 1 / 48)) = ENNReal.ofReal (1 / 24)
      from fun j => by congr 1; ring]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (show (0 : ℝ) ≤ 1 / 24 by norm_num)]
  norm_num

/-! ### The target -/

theorem chiSmallBase_pair_cube_lower_conv48 (z : EuclideanSpace ℝ (Fin 3))
    (hz : ∀ j : Fin 3, |z.ofLp j| ≤ 1 / 16) :
    Work.BoseFixB1S.conv48L ^ 288 * (1 / 13824)
      ≤ ∫ y in {y : EuclideanSpace ℝ (Fin 3) | ∀ j : Fin 3, |(y - (1 / 2 : ℝ) • z).ofLp j| ≤ 1 / 48},
          Submission.BoseGases.chiSmallBase 48 y * Submission.BoseGases.chiSmallBase 48 (z - y) := by
  set K := {y : EuclideanSpace ℝ (Fin 3) | ∀ j : Fin 3, |(y - (1 / 2 : ℝ) • z).ofLp j| ≤ 1 / 48}
    with hK
  have hvol : volume K = ENNReal.ofReal (1 / 13824) := by
    rw [hK]
    exact pc48_volume_cube ((1 / 2 : ℝ) • z)
  have hmeas : MeasurableSet K := by
    rw [hK]
    have hcl : IsClosed
        {y : EuclideanSpace ℝ (Fin 3) | ∀ j : Fin 3, |(y - (1 / 2 : ℝ) • z).ofLp j| ≤ 1 / 48} := by
      rw [show {y : EuclideanSpace ℝ (Fin 3) | ∀ j : Fin 3, |(y - (1 / 2 : ℝ) • z).ofLp j| ≤ 1 / 48}
            = ⋂ j : Fin 3,
                {y : EuclideanSpace ℝ (Fin 3) | |(y - (1 / 2 : ℝ) • z).ofLp j| ≤ 1 / 48} by
          ext y; simp]
      refine isClosed_iInter (fun j => isClosed_le ?_ continuous_const)
      exact continuous_abs.comp
        ((Submission.BoseGases.coord_continuous j).comp (continuous_id.sub continuous_const))
    exact hcl.measurableSet
  have hpoint : ∀ y ∈ K, conv48L ^ 288 ≤
      chiSmallBase 48 y * chiSmallBase 48 (z - y) := by
    intro y hy
    rw [hK] at hy
    exact pc48_pointwise z y hz hy
  have hbound : ∀ y : EuclideanSpace ℝ (Fin 3),
      ‖chiSmallBase 48 y * chiSmallBase 48 (z - y)‖ ≤ 1 := by
    intro y
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_one₀ (pc48_abs_chiSmallBase_le_one 48 y) (abs_nonneg _)
      (pc48_abs_chiSmallBase_le_one 48 (z - y))
  have hcont : Continuous
      (fun y : EuclideanSpace ℝ (Fin 3) => chiSmallBase 48 y * chiSmallBase 48 (z - y)) :=
    (chiSmallBase_continuous 48).mul
      ((chiSmallBase_continuous 48).comp (continuous_const.sub continuous_id))
  have hfint : IntegrableOn
      (fun y : EuclideanSpace ℝ (Fin 3) => chiSmallBase 48 y * chiSmallBase 48 (z - y)) K :=
    IntegrableOn.of_bound (by rw [hvol]; exact ENNReal.ofReal_lt_top)
      hcont.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbound)
  have hcint : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 3) => conv48L ^ 288) K :=
    integrableOn_const (by rw [hvol]; exact ENNReal.ofReal_ne_top)
  have hmono := setIntegral_mono_on hcint hfint hmeas hpoint
  have hconst : ∫ y in K, (conv48L ^ 288 : ℝ) = conv48L ^ 288 * (1 / 13824) := by
    rw [setIntegral_const, MeasureTheory.Measure.real_def, hvol,
      ENNReal.toReal_ofReal (by norm_num), smul_eq_mul, mul_comm]
  linarith [hmono, hconst]

end Work.BoseFixB1S
