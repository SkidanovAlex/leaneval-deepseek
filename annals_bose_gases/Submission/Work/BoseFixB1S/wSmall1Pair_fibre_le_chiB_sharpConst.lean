import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.perBoxFWeight_holds
import Submission.Work.BoseFixB1S.chiSupAbs_le_four
import Submission.Work.BoseFixB1S.cos_pi_div_sixteen_pow144_ge_inv20
import Submission.Work.BoseFixB1S.oneD_pow96_integral_le_tenth
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The sharp-constant `χ_B`-linear fibre bound of the localised one-body kernel

Target: `Work.BoseFixB1S.wSmall1Pair_fibre_le_chiB_sharpConst`.

The already-proved `Work.BoseFixB1.wSmall1Pair_fibre_le_chiB` has the *shape* needed
(`|∫_y wSmall1Pair dy| ≤ K·(a v)·χ_B(x)`) but its constant carries the global
`smallConvLower 48 = 2^{-150}` (a lower bound for the self-convolution `(χ₄₈⋆χ₄₈)` on the whole
polydisc), which dwarfs the available credits.  Here the constant is pinned down:

    K := 16·π·chiSupAbs·C₀ ,     C₀ := 81920/31 = 1/(31 · 1/81920) ,

obtained from three numerical ingredients, all elementary:

* `chiSupAbs ≤ 4`              (`Work.BoseFixB1S.chiSupAbs_le_four`);
* `31 ≤ chiSmallNormFactor 48` (from `∫_ℝ ζ^96 ≤ 1/10`,
  `Work.BoseFixB1S.oneD_pow96_integral_le_tenth`, together with
  `chiSmallNormSq 48 = (∫ ζ^96)³`);
* `1/(20·4096) ≤ ∫_y B(y)B(τ−y) dy` for `‖τ‖_∞ ≤ 1/16`
  (`Work.BoseFixB1S.chiSmallBase_pair_cube32_lower` and
  `Work.BoseFixB1S.cos_pi_div_sixteen_pow144_ge_inv20`); here `B := chiSmallBase 48`.

The mechanism is the *exact ratio* identity

    chiSmall 48 w / conv3Small 48 τ = chiSmallBase 48 w / (nf · ∫_y B(y)B(τ−y) dy) ,

in which the (large) normalisation factor `nf = chiSmallNormFactor 48` cancels, so that only the
*lower* bound `nf ≥ 31` and the *lower* bound on the pair integral are needed.  All the remaining
ingredients — the pointwise domination of `wSmallScaled` by `2|g₀|` and the `∫|g₀| = 8π a` mass
identity — are the ones already used by the proved `wSmall1Pair_fibre_le_chiB`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-! ## Elementary facts about `chiSmall`, `chiSmallNormFactor`, `conv3Small` -/

lemma conv3Small_nonneg (M : ℕ) (z : E3) : 0 ≤ Submission.BoseGases.conv3Small M z := by
  dsimp only [Submission.BoseGases.conv3Small]
  exact integral_nonneg fun y => mul_nonneg (chiSmall_nonneg M y) (chiSmall_nonneg M (z - y))

/-- `chiSmall 48 w = chiSmallNormFactor 48 · chiSmallBase 48 w`. -/
lemma chiSmall48_eq (w : E3) :
    Submission.BoseGases.chiSmall 48 w
      = Submission.BoseGases.chiSmallNormFactor 48 * Submission.BoseGases.chiSmallBase 48 w := by
  rw [Submission.BoseGases.chiSmall, Submission.BoseGases.chiSmallNormFactor,
    div_eq_mul_inv, mul_comm]

/-- `(chiSmallNormFactor 48)² = (chiSmallNormSq 48)⁻¹`. -/
lemma chiSmallNormFactor48_sq :
    Submission.BoseGases.chiSmallNormFactor 48 ^ 2
      = (Submission.BoseGases.chiSmallNormSq 48)⁻¹ := by
  have hS : 0 < Submission.BoseGases.chiSmallNormSq 48 :=
    Submission.BoseGases.chiSmallNormSq_pos (by norm_num)
  rw [Submission.BoseGases.chiSmallNormFactor, inv_pow, Real.sq_sqrt (le_of_lt hS)]

/-- `cos (A+B)·cos (A−B) = (cos (2A) + cos (2B))/2`. -/
lemma cos_mul_cos_add_sub (A B : ℝ) :
    Real.cos (A + B) * Real.cos (A - B) = (Real.cos (2 * A) + Real.cos (2 * B)) / 2 := by
  have key : Real.cos (A + B) * Real.cos (A - B) = Real.cos A ^ 2 - Real.sin B ^ 2 := by
    rw [Real.cos_add A B, Real.cos_sub A B]
    ring_nf
    nlinarith [Real.sin_sq A, Real.sin_sq B, Real.cos_sq A, Real.cos_sq B]
  have hA : Real.cos (2 * A) = 2 * Real.cos A ^ 2 - 1 := Real.cos_two_mul A
  have hB : Real.cos (2 * B) = 2 * Real.cos B ^ 2 - 1 := Real.cos_two_mul B
  have hsinB : Real.sin B ^ 2 = 1 - Real.cos B ^ 2 := Real.sin_sq B
  rw [key, hA, hB, hsinB]
  ring

/-- For `0 ≤ a`: `(a/c)·c ≤ a`. -/
lemma div_mul_self_le {a c : ℝ} (ha : 0 ≤ a) (_hc : 0 ≤ c) : (a / c) * c ≤ a := by
  by_cases h : c = 0
  · rw [h]; simpa using ha
  · rw [div_mul_cancel₀ _ h]

/-! ## The `1/32`-cube lower bound on the pair integral at `M = 48` -/

/-- **The cube bound for the pair integral.**  For `‖τ‖_∞ ≤ 1/16`,

    cos(π/16)^144 / 4096 ≤ ∫_y B(y)·B(τ−y) dy ,      B := chiSmallBase 48 .

On the cube `{|y_j − τ_j/2| ≤ 1/32}` (volume `(1/16)³ = 1/4096`) one has, using
`cos a cos b = (cos(a+b)+cos(a−b))/2` with `a = πτ_j/2`, `b = π(y_j − τ_j/2)`,

    ζ(y_j)·ζ(τ_j − y_j) = (cos(πτ_j) + cos(2π(y_j−τ_j/2)))/2 ≥ cos(π/16) ,

because both cosines are evaluated at arguments of modulus `≤ π/16`; hence
`B(y)B(τ−y) = [∏_j ζ(y_j)ζ(τ_j−y_j)]^{48} ≥ cos(π/16)^{144}` there. -/
theorem chiSmallBase_pair_cube32_lower (τ : E3) (hτ : ∀ j : Fin 3, |τ.ofLp j| ≤ 1 / 16) :
    Real.cos (Real.pi / 16) ^ 144 / 4096 ≤
      ∫ y : E3, Submission.BoseGases.chiSmallBase 48 y
        * Submission.BoseGases.chiSmallBase 48 (τ - y) := by
  set C : ℝ := Real.cos (Real.pi / 16) with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩ <;> nlinarith [Real.pi_pos]
  set K : Set E3 := {y : E3 | ∀ j : Fin 3, |(y - (1 / 2 : ℝ) • τ).ofLp j| ≤ 1 / 32} with hK
  have hKmeas : MeasurableSet K := by
    rw [hK]
    have hcl : IsClosed {y : E3 | ∀ j : Fin 3, |(y - (1 / 2 : ℝ) • τ).ofLp j| ≤ 1 / 32} := by
      rw [show {y : E3 | ∀ j : Fin 3, |(y - (1 / 2 : ℝ) • τ).ofLp j| ≤ 1 / 32}
            = ⋂ j : Fin 3, {y : E3 | |(y - (1 / 2 : ℝ) • τ).ofLp j| ≤ 1 / 32} by
          ext y; simp]
      refine isClosed_iInter (fun j => isClosed_le ?_ continuous_const)
      exact continuous_abs.comp
        ((coord_continuous j).comp (continuous_id.sub continuous_const))
    exact hcl.measurableSet
  have hKvol : volume K = ENNReal.ofReal (1 / 4096) := by
    rw [hK]
    have hmp : MeasurePreserving (WithLp.toLp 2 : (Fin 3 → ℝ) → E3) volume volume :=
      PiLp.volume_preserving_toLp (Fin 3)
    have hmeas : MeasurableSet
        {y : E3 | ∀ j : Fin 3, |(y - (1 / 2 : ℝ) • τ).ofLp j| ≤ 1 / 32} := hKmeas
    have hv : volume ((WithLp.toLp 2) ⁻¹'
          {y : E3 | ∀ j : Fin 3, |(y - (1 / 2 : ℝ) • τ).ofLp j| ≤ 1 / 32})
        = volume {y : E3 | ∀ j : Fin 3, |(y - (1 / 2 : ℝ) • τ).ofLp j| ≤ 1 / 32} :=
      hmp.measure_preimage hmeas.nullMeasurableSet
    rw [← hv]
    have hset : (WithLp.toLp 2) ⁻¹'
          {y : E3 | ∀ j : Fin 3, |(y - (1 / 2 : ℝ) • τ).ofLp j| ≤ 1 / 32}
        = Set.univ.pi (fun j : Fin 3 =>
            Set.Icc (((1 / 2 : ℝ) • τ).ofLp j - 1 / 32) (((1 / 2 : ℝ) • τ).ofLp j + 1 / 32)) := by
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
        ENNReal.ofReal ((((1 / 2 : ℝ) • τ).ofLp j + 1 / 32)
            - (((1 / 2 : ℝ) • τ).ofLp j - 1 / 32)) = ENNReal.ofReal (1 / 16) from
        fun j => by congr 1; ring]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← ENNReal.ofReal_pow (show (0 : ℝ) ≤ 1 / 16 by norm_num)]
    norm_num
  -- coordinate bookkeeping for `y ∈ K`
  have hyabs : ∀ y ∈ K, ∀ j : Fin 3, |y.ofLp j| ≤ 1 / 16 := by
    intro y hy j
    have h1 : |(y - (1 / 2 : ℝ) • τ).ofLp j| ≤ 1 / 32 := hy j
    have h2 : |τ.ofLp j| ≤ 1 / 16 := hτ j
    have h3 : y.ofLp j = (y - (1 / 2 : ℝ) • τ).ofLp j + (1 / 2) * τ.ofLp j := by
      simp only [WithLp.ofLp_sub, Pi.sub_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h3]
    calc |(y - (1 / 2 : ℝ) • τ).ofLp j + (1 / 2) * τ.ofLp j|
        ≤ |(y - (1 / 2 : ℝ) • τ).ofLp j| + |(1 / 2) * τ.ofLp j| := abs_add_le _ _
      _ ≤ 1 / 32 + 1 / 32 := by
          gcongr
          rw [abs_mul]
          simp only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          linarith
      _ ≤ 1 / 16 := by norm_num
  have hzyabs : ∀ y ∈ K, ∀ j : Fin 3, |(τ - y).ofLp j| ≤ 1 / 16 := by
    intro y hy j
    have h1 : |(y - (1 / 2 : ℝ) • τ).ofLp j| ≤ 1 / 32 := hy j
    have h2 : |τ.ofLp j| ≤ 1 / 16 := hτ j
    have h3 : (τ - y).ofLp j = (1 / 2) * τ.ofLp j - (y - (1 / 2 : ℝ) • τ).ofLp j := by
      simp only [WithLp.ofLp_sub, Pi.sub_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h3]
    calc |(1 / 2) * τ.ofLp j - (y - (1 / 2 : ℝ) • τ).ofLp j|
        ≤ |(1 / 2) * τ.ofLp j| + |(y - (1 / 2 : ℝ) • τ).ofLp j| := abs_sub _ _
      _ ≤ 1 / 32 + 1 / 32 := by
          gcongr
          rw [abs_mul]
          simp only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          linarith
      _ ≤ 1 / 16 := by norm_num
  -- the per-coordinate factor estimate on the cube
  have hfac : ∀ y ∈ K, ∀ j : Fin 3, C ≤ zeta1d (y.ofLp j) * zeta1d ((τ - y).ofLp j) := by
    intro y hy j
    have h1 : |y.ofLp j| ≤ 1 / 2 := le_trans (hyabs y hy j) (by norm_num)
    have h2 : |(τ - y).ofLp j| ≤ 1 / 2 := le_trans (hzyabs y hy j) (by norm_num)
    have hsub : (τ - y).ofLp j = τ.ofLp j - y.ofLp j := by
      simp only [WithLp.ofLp_sub, Pi.sub_apply]
    set w : ℝ := y.ofLp j - τ.ofLp j / 2 with hw
    set A : ℝ := Real.pi * τ.ofLp j / 2 with hA
    set B : ℝ := Real.pi * w with hB
    have harg1 : Real.pi * y.ofLp j = A + B := by rw [hA, hB, hw]; ring
    have harg2 : Real.pi * ((τ - y).ofLp j) = A - B := by rw [hsub, hA, hB, hw]; ring
    have hwy : |w| ≤ 1 / 32 := by
      have h3 : (y - (1 / 2 : ℝ) • τ).ofLp j = w := by
        rw [hw]
        simp only [WithLp.ofLp_sub, Pi.sub_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
        ring
      rw [← h3]; exact hy j
    have hA3 : |A| ≤ Real.pi / 16 := by
      rw [hA, abs_div, abs_mul, abs_of_nonneg Real.pi_nonneg,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have := hτ j
      nlinarith [Real.pi_pos]
    have hB3 : |B| ≤ Real.pi / 16 := by
      rw [hB, abs_mul, abs_of_nonneg Real.pi_nonneg]
      nlinarith [Real.pi_pos, hwy]
    have h2A : |2 * A| ≤ Real.pi / 16 := by
      rw [show (2 : ℝ) * A = Real.pi * τ.ofLp j by rw [hA]; ring]
      rw [abs_mul, abs_of_nonneg Real.pi_nonneg]
      have := hτ j
      nlinarith [Real.pi_pos]
    have h2B : |2 * B| ≤ Real.pi / 16 := by
      rw [show (2 : ℝ) * B = 2 * Real.pi * w by rw [hB]; ring]
      rw [show (2 : ℝ) * Real.pi * w = (2 * Real.pi) * w by ring, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      nlinarith [Real.pi_pos, hwy]
    have cos_mono : ∀ t : ℝ, |t| ≤ Real.pi / 16 → C ≤ Real.cos t := by
      intro t ht
      have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := |t|) (y := Real.pi / 16)
        (abs_nonneg t) (by linarith [Real.pi_pos]) ht
      simpa [hC, Real.cos_abs] using h
    have hcos1 : C ≤ Real.cos (2 * A) := cos_mono (2 * A) h2A
    have hcos2 : C ≤ Real.cos (2 * B) := cos_mono (2 * B) h2B
    rw [zeta1d_of_abs_le h1, zeta1d_of_abs_le h2, harg1, harg2,
      cos_mul_cos_add_sub A B]
    linarith
  -- the pointwise lower bound on the cube
  have hpoint : ∀ y ∈ K, C ^ 144 ≤ Submission.BoseGases.chiSmallBase 48 y
      * Submission.BoseGases.chiSmallBase 48 (τ - y) := by
    intro y hy
    have hbase1 : Submission.BoseGases.chiSmallBase 48 y
        = (∏ j : Fin 3, zeta1d (y.ofLp j)) ^ 48 := by
      rw [Submission.BoseGases.chiSmallBase, Fin.prod_univ_three]
    have hbase2 : Submission.BoseGases.chiSmallBase 48 (τ - y)
        = (∏ j : Fin 3, zeta1d ((τ - y).ofLp j)) ^ 48 := by
      rw [Submission.BoseGases.chiSmallBase, Fin.prod_univ_three]
    have hsplit : Submission.BoseGases.chiSmallBase 48 y
          * Submission.BoseGases.chiSmallBase 48 (τ - y)
        = (∏ j : Fin 3, zeta1d (y.ofLp j) * zeta1d ((τ - y).ofLp j)) ^ 48 := by
      rw [hbase1, hbase2, ← mul_pow, ← Finset.prod_mul_distrib]
    have hprod : (∏ _j : Fin 3, C) ≤ ∏ j : Fin 3,
        zeta1d (y.ofLp j) * zeta1d ((τ - y).ofLp j) :=
      Finset.prod_le_prod₀ (fun j _ => hC0) (fun j _ => hfac y hy j)
    have hCp : (∏ _j : Fin 3, C) = C ^ 3 := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc C ^ 144 = (C ^ 3) ^ 48 := by ring
      _ = (∏ _j : Fin 3, C) ^ 48 := by rw [hCp]
      _ ≤ (∏ j : Fin 3, zeta1d (y.ofLp j) * zeta1d ((τ - y).ofLp j)) ^ 48 :=
          pow_le_pow_left₀ (by positivity) hprod 48
      _ = Submission.BoseGases.chiSmallBase 48 y
          * Submission.BoseGases.chiSmallBase 48 (τ - y) := hsplit.symm
  -- integrate
  have hfint : IntegrableOn (fun y : E3 => Submission.BoseGases.chiSmallBase 48 y
      * Submission.BoseGases.chiSmallBase 48 (τ - y)) K volume := by
    refine IntegrableOn.of_bound (by rw [hKvol]; exact ENNReal.ofReal_lt_top)
      ((chiSmallBase_continuous 48).mul
        ((chiSmallBase_continuous 48).comp
          (continuous_const.sub continuous_id))).aestronglyMeasurable 1 ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_one₀ (pc48_abs_chiSmallBase_le_one 48 y) (abs_nonneg _)
      (pc48_abs_chiSmallBase_le_one 48 (τ - y))
  have hcint : IntegrableOn (fun _ : E3 => C ^ 144) K volume :=
    integrableOn_const (by rw [hKvol]; exact ENNReal.ofReal_ne_top)
  have hmono := setIntegral_mono_on hcint hfint hKmeas hpoint
  have hconst : ∫ _y in K, (C ^ 144 : ℝ) = C ^ 144 * (1 / 4096) := by
    rw [setIntegral_const, MeasureTheory.Measure.real_def, hKvol,
      ENNReal.toReal_ofReal (by norm_num), smul_eq_mul, mul_comm]
  have hfull : (∫ y in K, Submission.BoseGases.chiSmallBase 48 y
        * Submission.BoseGases.chiSmallBase 48 (τ - y))
      ≤ ∫ y : E3, Submission.BoseGases.chiSmallBase 48 y
        * Submission.BoseGases.chiSmallBase 48 (τ - y) :=
    setIntegral_le_integral (integrable_conv48_integrand τ)
      (Filter.Eventually.of_forall (fun y => mul_nonneg (chiSmallBase_nonneg 48 y)
        (chiSmallBase_nonneg 48 (τ - y))))
  calc C ^ 144 / 4096 = C ^ 144 * (1 / 4096) := by ring
    _ = ∫ _y in K, (C ^ 144 : ℝ) := hconst.symm
    _ ≤ ∫ y in K, Submission.BoseGases.chiSmallBase 48 y
        * Submission.BoseGases.chiSmallBase 48 (τ - y) := hmono
    _ ≤ _ := hfull

/-! ## The target -/

theorem wSmall1Pair_fibre_le_chiB_sharpConst {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v) :
    ∃ K : ℝ, 0 ≤ K ∧ K ≤ 10 ^ 6 ∧
      ∀ {ℓ d : ℝ}, 0 < ℓ → 0 < d → R0 ≤ ℓ * d / 16 → R0 ≤ ℓ * Submission.BoseGases.chiR0 →
        ∀ (u x : EuclideanSpace ℝ (Fin 3)),
          |∫ y in Submission.BoseGases.acube ℓ,
              Submission.BoseGases.wSmall1Pair h Work.BoseBox.mValue ℓ d u x y| ≤
            K * (_root_.BoseGases.a v)
              * (Submission.BoseGases.chiScale ℓ x
                  * Submission.BoseGases.chiSmall Work.BoseBox.mValue ((ℓ * d)⁻¹ • x - u)) := by
  -- the lower bound on the (large) normalisation factor
  have hnf_ge : (31 : ℝ) ≤ Submission.BoseGases.chiSmallNormFactor 48 := by
    have hpos : 0 < Submission.BoseGases.chiSmallNormSq 48 :=
      Submission.BoseGases.chiSmallNormSq_pos (by norm_num)
    have hcube := Work.SmallBoxTBWord.chiSmallNormSq_eq_cube_zeta1d_integral 48
    have h96 : (∫ s : ℝ, zeta1d s ^ (2 * 48)) ≤ 1 / 10 := by
      simpa using oneD_pow96_integral_le_tenth
    have hS : Submission.BoseGases.chiSmallNormSq 48 ≤ (1 / 1000 : ℝ) := by
      rw [hcube, show (1 / 1000 : ℝ) = ((1 : ℝ) / 10) ^ 3 by norm_num]
      exact pow_le_pow_left₀ (integral_nonneg fun s => pow_nonneg (zeta1d_nonneg s) _) h96 3
    have hsqrt_le : Real.sqrt (Submission.BoseGases.chiSmallNormSq 48) ≤ 1 / 31 := by
      refine le_trans (Real.sqrt_le_sqrt hS) ?_
      rw [show (1 / 31 : ℝ) = Real.sqrt ((1 / 31) ^ 2) by
        rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    rw [Submission.BoseGases.chiSmallNormFactor]
    have hsp : 0 < Real.sqrt (Submission.BoseGases.chiSmallNormSq 48) := Real.sqrt_pos.mpr hpos
    have h1 : ((1 / 31 : ℝ))⁻¹
        ≤ (Real.sqrt (Submission.BoseGases.chiSmallNormSq 48))⁻¹ :=
      (inv_le_inv₀ (by norm_num : (0 : ℝ) < 1 / 31) hsp).mpr hsqrt_le
    simpa using h1
  -- the lower bound on the pair integral
  have hJ : ∀ τ : E3, (∀ j : Fin 3, |τ.ofLp j| ≤ 1 / 16) →
      (1 / 81920 : ℝ) ≤ ∫ y : E3, Submission.BoseGases.chiSmallBase 48 y
        * Submission.BoseGases.chiSmallBase 48 (τ - y) := by
    intro τ hτ
    have h1 := chiSmallBase_pair_cube32_lower τ hτ
    have h2 : (1 / 20 : ℝ) ≤ Real.cos (Real.pi / 16) ^ 144 :=
      cos_pi_div_sixteen_pow144_ge_inv20
    have h3 : Real.cos (Real.pi / 16) ^ 144 / 4096
        = (Real.cos (Real.pi / 16) ^ 144) * (1 / 4096) := by ring
    have h4 : (1 / 20 : ℝ) * (1 / 4096)
        ≤ Real.cos (Real.pi / 16) ^ 144 * (1 / 4096) :=
      mul_le_mul_of_nonneg_right h2 (by norm_num)
    calc (1 / 81920 : ℝ) = (1 / 20) * (1 / 4096) := by norm_num
      _ ≤ Real.cos (Real.pi / 16) ^ 144 * (1 / 4096) := h4
      _ = Real.cos (Real.pi / 16) ^ 144 / 4096 := h3.symm
      _ ≤ _ := h1
  refine ⟨16 * Real.pi * Submission.BoseGases.chiSupAbs * (81920 / 31), ?_, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt Real.pi_pos))
      Submission.BoseGases.chiSupAbs_nonneg) (by norm_num)
  · -- `K ≤ 10 ^ 6`
    have hsup := chiSupAbs_le_four
    have hpi : Real.pi ≤ 3.1416 := by
      have := Real.pi_lt_d20
      linarith
    have hmain : Real.pi * Submission.BoseGases.chiSupAbs ≤ (3.1416 : ℝ) * 4 :=
      mul_le_mul hpi hsup Submission.BoseGases.chiSupAbs_nonneg (by norm_num)
    calc 16 * Real.pi * Submission.BoseGases.chiSupAbs * (81920 / 31)
        = (16 * (81920 / 31)) * (Real.pi * Submission.BoseGases.chiSupAbs) := by ring
      _ ≤ (16 * (81920 / 31)) * ((3.1416 : ℝ) * 4) :=
          mul_le_mul_of_nonneg_left hmain (by norm_num)
      _ ≤ 10 ^ 6 := by norm_num
  · intro ℓ d hℓ hd hR hRχ u x
    have hmv : Work.BoseBox.mValue = 48 := rfl
    rw [hmv]
    set A : ℝ := Submission.BoseGases.chiScale ℓ x
      * Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u) with hA
    have hAnn : 0 ≤ A := by
      rw [hA]
      exact mul_nonneg (chiScale_nonneg ℓ x) (chiSmall_nonneg 48 _)
    have hC₀pos : (0 : ℝ) < 81920 / 31 := by norm_num
    set B : ℝ := 2 * (81920 / 31) * Submission.BoseGases.chiSupAbs with hB
    have hBnn : 0 ≤ B := by
      rw [hB]
      exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hC₀pos))
        Submission.BoseGases.chiSupAbs_nonneg
    -- the ratio bound `chiSmall 48 w ≤ (81920/31)·conv3Small 48 τ`
    have hratio : ∀ (w τ : E3), (∀ j : Fin 3, |τ.ofLp j| ≤ 1 / 16) →
        Submission.BoseGases.chiSmall 48 w
          ≤ (81920 / 31) * Submission.BoseGases.conv3Small 48 τ := by
      intro w τ hτ
      have hS : 0 < Submission.BoseGases.chiSmallNormSq 48 :=
        Submission.BoseGases.chiSmallNormSq_pos (by norm_num)
      have hJτ := hJ τ hτ
      have h1 : Submission.BoseGases.chiSmall 48 w
          ≤ Submission.BoseGases.chiSmallNormFactor 48 := by
        rw [chiSmall48_eq w]
        calc Submission.BoseGases.chiSmallNormFactor 48 * Submission.BoseGases.chiSmallBase 48 w
            ≤ Submission.BoseGases.chiSmallNormFactor 48 * 1 :=
              mul_le_mul_of_nonneg_left (chiSmallBase_le_one 48 w)
                (Submission.BoseGases.chiSmallNormFactor_nonneg 48)
          _ = Submission.BoseGases.chiSmallNormFactor 48 := by ring
      have h2 : Submission.BoseGases.chiSmallNormFactor 48 * (31 * (1 / 81920 : ℝ))
          ≤ Submission.BoseGases.chiSmallNormFactor 48
            * (Submission.BoseGases.chiSmallNormFactor 48 * (1 / 81920 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Submission.BoseGases.chiSmallNormFactor_nonneg 48)
        exact mul_le_mul_of_nonneg_right hnf_ge (by norm_num)
      have h3 : Submission.BoseGases.chiSmallNormFactor 48
            * (Submission.BoseGases.chiSmallNormFactor 48 * (1 / 81920 : ℝ))
          = (Submission.BoseGases.chiSmallNormSq 48)⁻¹ * (1 / 81920 : ℝ) := by
        rw [← chiSmallNormFactor48_sq]; ring
      have h4 : (Submission.BoseGases.chiSmallNormSq 48)⁻¹ * (1 / 81920 : ℝ)
          ≤ (Submission.BoseGases.chiSmallNormSq 48)⁻¹
            * ∫ y : E3, Submission.BoseGases.chiSmallBase 48 y
                * Submission.BoseGases.chiSmallBase 48 (τ - y) :=
        mul_le_mul_of_nonneg_left hJτ (inv_nonneg.mpr (le_of_lt hS))
      have h5 : (Submission.BoseGases.chiSmallNormSq 48)⁻¹
            * ∫ y : E3, Submission.BoseGases.chiSmallBase 48 y
                * Submission.BoseGases.chiSmallBase 48 (τ - y)
          = Submission.BoseGases.conv3Small 48 τ := (conv3Small48_eq_inv_mul τ).symm
      have key : Submission.BoseGases.chiSmall 48 w * (31 * (1 / 81920 : ℝ))
          ≤ Submission.BoseGases.conv3Small 48 τ :=
        calc Submission.BoseGases.chiSmall 48 w * (31 * (1 / 81920 : ℝ))
            ≤ Submission.BoseGases.chiSmallNormFactor 48 * (31 * (1 / 81920 : ℝ)) :=
              mul_le_mul_of_nonneg_right h1 (by norm_num)
          _ ≤ Submission.BoseGases.chiSmallNormFactor 48
                * (Submission.BoseGases.chiSmallNormFactor 48 * (1 / 81920 : ℝ)) := h2
          _ = (Submission.BoseGases.chiSmallNormSq 48)⁻¹ * (1 / 81920 : ℝ) := h3
          _ ≤ _ := h4
          _ = Submission.BoseGases.conv3Small 48 τ := h5
      have hpos : (0 : ℝ) < 31 * (1 / 81920 : ℝ) := by norm_num
      have hmul : (31 * (1 / 81920 : ℝ)) * (81920 / 31) = 1 := by norm_num
      calc Submission.BoseGases.chiSmall 48 w
          = Submission.BoseGases.chiSmall 48 w
            * ((31 * (1 / 81920 : ℝ)) * (81920 / 31)) := by rw [hmul, mul_one]
        _ = (Submission.BoseGases.chiSmall 48 w * (31 * (1 / 81920 : ℝ))) * (81920 / 31) := by
              ring
        _ ≤ Submission.BoseGases.conv3Small 48 τ * (81920 / 31) :=
              mul_le_mul_of_nonneg_right key (by norm_num)
        _ = (81920 / 31) * Submission.BoseGases.conv3Small 48 τ := by ring
    -- the pointwise bound on the fibre integrand
    have hpt : ∀ y : E3, |Submission.BoseGases.wSmall1Pair h 48 ℓ d u x y|
        ≤ A * (B * |Submission.BoseGases.g0 v h (x - y)|) := by
      intro y
      by_cases hnorm : ‖x - y‖ ≤ R0
      · have hcpos : 0 < ℓ * d := mul_pos hℓ hd
        have hτnorm : ‖(ℓ * d)⁻¹ • (x - y)‖ ≤ 1 / 16 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcpos)]
          calc (ℓ * d)⁻¹ * ‖x - y‖ ≤ (ℓ * d)⁻¹ * (ℓ * d / 16) :=
                mul_le_mul_of_nonneg_left (le_trans hnorm hR) (le_of_lt (inv_pos.mpr hcpos))
            _ = 1 / 16 := by field_simp
        have hτ : ∀ j : Fin 3, |((ℓ * d)⁻¹ • (x - y)).ofLp j| ≤ 1 / 16 :=
          fun j => le_trans (coord_abs_le_norm _ j) hτnorm
        have hinv : |(Submission.BoseGases.convScale ℓ (x - y))⁻¹| ≤ 2 :=
          abs_inv_convScale_le_two hℓ hRχ hnorm
        have hcv0 : (0 : ℝ) ≤ Submission.BoseGases.conv3Small 48 ((ℓ * d)⁻¹ • (x - y)) :=
          conv3Small_nonneg 48 _
        have hws : |Submission.BoseGases.wSmallScaled 48 (ℓ * d) (Submission.BoseGases.g0 v h)
              (x - y)|
            = |Submission.BoseGases.g0 v h (x - y)|
              / Submission.BoseGases.conv3Small 48 ((ℓ * d)⁻¹ • (x - y)) := by
          rw [Submission.BoseGases.wSmallScaled, Submission.BoseGases.convScaleSmall, abs_div,
            abs_of_nonneg hcv0]
        have hchiB : |Submission.BoseGases.chiSmallB 48 ℓ d u y|
            ≤ Submission.BoseGases.chiSupAbs
              * Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • y - u) := by
          rw [Submission.BoseGases.chiSmallB, abs_mul, abs_of_nonneg (chiSmall_nonneg 48 _)]
          exact mul_le_mul_of_nonneg_right (chiScale_abs_le_sup ℓ y) (chiSmall_nonneg 48 _)
        have hxval : |Submission.BoseGases.chiSmallB 48 ℓ d u x| = A := by
          rw [hA, Submission.BoseGases.chiSmallB,
            abs_of_nonneg (mul_nonneg (chiScale_nonneg ℓ x) (chiSmall_nonneg 48 _))]
        have hrt := hratio ((ℓ * d)⁻¹ • y - u) ((ℓ * d)⁻¹ • (x - y)) hτ
        have hfac2 : |Submission.BoseGases.wSmallScaled 48 (ℓ * d) (Submission.BoseGases.g0 v h)
                (x - y)|
              * |(Submission.BoseGases.convScale ℓ (x - y))⁻¹|
            ≤ (|Submission.BoseGases.g0 v h (x - y)|
                / Submission.BoseGases.conv3Small 48 ((ℓ * d)⁻¹ • (x - y))) * 2 := by
          rw [hws]
          exact mul_le_mul_of_nonneg_left hinv (div_nonneg (abs_nonneg _) hcv0)
        have hsplit : |Submission.BoseGases.wSmall1Pair h 48 ℓ d u x y|
            = |Submission.BoseGases.chiSmallB 48 ℓ d u x|
              * (|Submission.BoseGases.wSmallScaled 48 (ℓ * d) (Submission.BoseGases.g0 v h)
                    (x - y)| * |(Submission.BoseGases.convScale ℓ (x - y))⁻¹|)
              * |Submission.BoseGases.chiSmallB 48 ℓ d u y| := by
          simp only [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair,
            div_eq_mul_inv, abs_mul]
        rw [hsplit, hxval]
        calc A * (|Submission.BoseGases.wSmallScaled 48 (ℓ * d) (Submission.BoseGases.g0 v h)
                  (x - y)| * |(Submission.BoseGases.convScale ℓ (x - y))⁻¹|)
                * |Submission.BoseGases.chiSmallB 48 ℓ d u y|
            ≤ A * ((|Submission.BoseGases.g0 v h (x - y)|
                    / Submission.BoseGases.conv3Small 48 ((ℓ * d)⁻¹ • (x - y))) * 2)
                  * (Submission.BoseGases.chiSupAbs
                      * Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • y - u)) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hfac2 hAnn) hchiB (abs_nonneg _) ?_
              exact mul_nonneg hAnn (mul_nonneg (div_nonneg (abs_nonneg _) hcv0) (by norm_num))
          _ ≤ A * ((|Submission.BoseGases.g0 v h (x - y)|
                    / Submission.BoseGases.conv3Small 48 ((ℓ * d)⁻¹ • (x - y))) * 2)
                  * (Submission.BoseGases.chiSupAbs
                      * ((81920 / 31)
                        * Submission.BoseGases.conv3Small 48 ((ℓ * d)⁻¹ • (x - y)))) := by
              refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrt
                Submission.BoseGases.chiSupAbs_nonneg) ?_
              exact mul_nonneg hAnn (mul_nonneg (div_nonneg (abs_nonneg _) hcv0) (by norm_num))
          _ ≤ A * (B * |Submission.BoseGases.g0 v h (x - y)|) := by
              rw [hB]
              have hle := div_mul_self_le
                (abs_nonneg (Submission.BoseGases.g0 v h (x - y))) hcv0
              calc A * ((|Submission.BoseGases.g0 v h (x - y)|
                        / Submission.BoseGases.conv3Small 48 ((ℓ * d)⁻¹ • (x - y))) * 2)
                      * (Submission.BoseGases.chiSupAbs
                          * ((81920 / 31)
                            * Submission.BoseGases.conv3Small 48 ((ℓ * d)⁻¹ • (x - y))))
                    = A * ((2 * (81920 / 31) * Submission.BoseGases.chiSupAbs)
                        * ((|Submission.BoseGases.g0 v h (x - y)|
                            / Submission.BoseGases.conv3Small 48 ((ℓ * d)⁻¹ • (x - y)))
                          * Submission.BoseGases.conv3Small 48 ((ℓ * d)⁻¹ • (x - y)))) := by
                      ring
                _ ≤ A * ((2 * (81920 / 31) * Submission.BoseGases.chiSupAbs)
                      * |Submission.BoseGases.g0 v h (x - y)|) := by
                    refine mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_left hle (by positivity)) hAnn
      · -- `g₀ (x − y) = 0`
        have hz0 : Submission.BoseGases.g0 v h (x - y) = 0 :=
          Submission.BoseGases.g0_zero_of_norm_ge hv_supp (le_of_lt (lt_of_not_ge hnorm)) h
        have hzero : Submission.BoseGases.wSmall1Pair h 48 ℓ d u x y = 0 := by
          rw [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair,
            Submission.BoseGases.wSmallScaled, hz0]
          ring
        rw [hzero, hz0]
        simp
    -- integration
    have hg0int : Integrable (Submission.BoseGases.g0 v h) :=
      Submission.BoseGases.g0_integrable hR0 hv_supp h
    have hshift_int : Integrable (fun y : E3 => |Submission.BoseGases.g0 v h (x - y)|) := by
      have h' := hg0int.abs.comp_sub_left x
      simpa [Function.comp_def] using h'
    have hdom_int : IntegrableOn (fun y : E3 => A * (B * |Submission.BoseGases.g0 v h (x - y)|))
        (Submission.BoseGases.acube ℓ) := by
      have h' := (hshift_int.const_mul B).const_mul A
      simpa only [mul_assoc] using h'.integrableOn
    have h1 : |∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h 48 ℓ d u x y|
        ≤ ∫ y in Submission.BoseGases.acube ℓ,
            A * (B * |Submission.BoseGases.g0 v h (x - y)|) := by
      have hnorm := norm_integral_le_integral_norm
        (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
        (f := fun y : E3 => Submission.BoseGases.wSmall1Pair h 48 ℓ d u x y)
      rw [Real.norm_eq_abs] at hnorm
      refine le_trans hnorm ?_
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => abs_nonneg _))
        hdom_int ?_
      filter_upwards with y
      exact hpt y
    have hshift_eq : (∫ y in Submission.BoseGases.acube ℓ,
          |Submission.BoseGases.g0 v h (x - y)|)
        ≤ ∫ y : E3, |Submission.BoseGases.g0 v h (x - y)| :=
      setIntegral_le_integral hshift_int (Filter.Eventually.of_forall (fun y => abs_nonneg _))
    have hshift_val : (∫ y : E3, |Submission.BoseGases.g0 v h (x - y)|)
        = 8 * Real.pi * (_root_.BoseGases.a v) := by
      have hsub := Submission.BoseGases.integral_comp_sub_left
        (fun z : E3 => |Submission.BoseGases.g0 v h z|) x
      have habs : (∫ z : E3, |Submission.BoseGases.g0 v h z|)
          = ∫ z : E3, Submission.BoseGases.g0 v h z := by
        refine integral_congr_ae ?_
        filter_upwards [Submission.BoseGases.g0_nonneg_ae (v := v) (R := R0) hR0 hv hvrad
          hv_supp h] with z hz
        exact abs_of_nonneg hz
      rw [hsub, habs, Submission.BoseGases.g0_integral hR0 hv_supp h]
    have h2 : (∫ y in Submission.BoseGases.acube ℓ,
          A * (B * |Submission.BoseGases.g0 v h (x - y)|))
        ≤ A * B * (8 * Real.pi * (_root_.BoseGases.a v)) := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      have hstep := mul_le_mul_of_nonneg_left
        (le_trans hshift_eq (le_of_eq hshift_val)) (mul_nonneg hAnn hBnn)
      simpa only [mul_assoc] using hstep
    calc |∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h 48 ℓ d u x y|
        ≤ ∫ y in Submission.BoseGases.acube ℓ,
            A * (B * |Submission.BoseGases.g0 v h (x - y)|) := h1
      _ ≤ A * B * (8 * Real.pi * (_root_.BoseGases.a v)) := h2
      _ = (16 * Real.pi * Submission.BoseGases.chiSupAbs * (81920 / 31))
            * (_root_.BoseGases.a v) * A := by
          rw [hA, hB]; ring

end Work.BoseFixB1S
