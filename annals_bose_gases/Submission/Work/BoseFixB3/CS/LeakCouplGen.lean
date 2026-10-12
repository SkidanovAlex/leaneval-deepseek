import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB3.CS.ContentParam
import Submission.Work.BoseFixB3.CS.Pieces.leakCoupl_core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.LeakCouplGen` — the leakage coupling at an arbitrary order

The leakage coupling bound `CS/Pieces/leakCoupl_core` (there `(ℓκ)^{-40} + R/ℓ`) is proved here
with the pure super-polynomial bound `(ℓκ)^{-N}` at an arbitrary order `N` — in particular with
*no* `R/ℓ` term, which is what the `CS` step of the `B3` chapter needs (a residual `R/ℓ` term is
polynomially small and cannot be beaten by the polynomially small budgets of `B3CSRoot`).

The route is different from the order-`40` proof and much simpler: the coupling is
`∫_y leak(y)·χ_ℓ(y)·(χ_ℓ ⋆ F)(y) dy`; substituting `t = x − y` and exchanging the two integrals
turns it into `∫_t F(t)·(∫_y leak(y)·χ_ℓ(y)χ_ℓ(y+t) dy)`, and for each `t` the inner integral is
the high-pass content of the *product bump* `χ_ℓ(·)χ_ℓ(·+t)`, which is bounded by
`3^N·M·ℓ³·(ℓκ)^{-N}` with `M` the universal product-bump constant (`bumpProd_bound_gen`).

## Main results

* `bumpProd_bound_gen` — the product bump's sup and `ℓ`-scaled derivative bounds up to order `N`;
* `leakCoupl_core_gen` — the leakage coupling bound with `(ℓκ)^{-N}` and no `R/ℓ`.
-/

noncomputable section

open MeasureTheory Filter Metric
open scoped Real Topology BigOperators

namespace Work.BoseFixB3.CS.LeakCouplGen

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

/-! ## 1. The product bump at order `N` -/

/-- The product bump `χ_ℓ(y)·χ_ℓ(y+z)`: sup bound `M` and `ℓ`-scaled derivative bounds up to
order `N`, with `M` universal. -/
theorem bumpProd_bound_gen (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (z : E3) (ℓ : ℝ), 0 < ℓ →
      (∀ y : E3, |Submission.BoseGases.chiU ℓ 0 y * Submission.BoseGases.chiU ℓ 0 (y + z)| ≤ M) ∧
      (∀ (j : ℕ), j ≤ N → ∀ y : E3,
          ‖iteratedFDeriv ℝ j
              (fun y : E3 =>
                Submission.BoseGases.chiU ℓ 0 y * Submission.BoseGases.chiU ℓ 0 (y + z)) y‖
            ≤ M / ℓ ^ j) := by
  obtain ⟨G, hG0, hG⟩ := Work.BoseFixB3.CS.Pieces.uniform_idfb_nat Submission.BoseGases.chi
      (fun k => contDiff_infty.mp Submission.BoseGases.chi_contDiff k)
      Submission.BoseGases.chi_hasCompactSupport
  have hV0 : ∀ k, 0 ≤ Work.BoseFixB3.CS.Pieces.chiProdV G k := by
    intro k
    unfold Work.BoseFixB3.CS.Pieces.chiProdV
    exact Finset.sum_nonneg
      (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hG0 i)) (hG0 (k - i)))
  refine ⟨∑ k ∈ Finset.range (N + 1), Work.BoseFixB3.CS.Pieces.chiProdV G k,
    Finset.sum_nonneg (fun k _ => hV0 k), ?_⟩
  intro z ℓ hℓ
  set M : ℝ := ∑ k ∈ Finset.range (N + 1), Work.BoseFixB3.CS.Pieces.chiProdV G k with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun k _ => hV0 k)
  have hbody : ∀ y : E3,
      Submission.BoseGases.chiU ℓ 0 y * Submission.BoseGases.chiU ℓ 0 (y + z) =
        Submission.BoseGases.chiScale ℓ y * Submission.BoseGases.chiScale ℓ (y + z) := by
    intro y
    simp only [Submission.BoseGases.chiU, Submission.BoseGases.chiScale, sub_zero]
  have hfun : (fun y : E3 =>
        Submission.BoseGases.chiU ℓ 0 y * Submission.BoseGases.chiU ℓ 0 (y + z)) =
      fun y : E3 =>
        Submission.BoseGases.chiScale ℓ y * Submission.BoseGases.chiScale ℓ (y + z) := by
    funext y
    exact hbody y
  constructor
  · intro y
    rw [hbody y]
    have hb := Work.BoseFixB3.CS.Pieces.bumpProd_deriv_le G hG z ℓ hℓ 0 y
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, mul_one] at hb
    refine hb.trans ?_
    have : Work.BoseFixB3.CS.Pieces.chiProdV G 0 ≤ M :=
      Finset.single_le_sum (f := Work.BoseFixB3.CS.Pieces.chiProdV G)
        (fun k _ => hV0 k) (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.zero_le N)))
    linarith
  · intro j hj y
    rw [hfun]
    have hb := Work.BoseFixB3.CS.Pieces.bumpProd_deriv_le G hG z ℓ hℓ j y
    have hle : Work.BoseFixB3.CS.Pieces.chiProdV G j ≤ M :=
      Finset.single_le_sum (f := Work.BoseFixB3.CS.Pieces.chiProdV G)
        (fun k _ => hV0 k) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    have hinv : 0 ≤ (ℓ⁻¹) ^ j := pow_nonneg (inv_nonneg.mpr hℓ.le) j
    calc ‖iteratedFDeriv ℝ j (fun y : E3 => Submission.BoseGases.chiScale ℓ y *
            Submission.BoseGases.chiScale ℓ (y + z)) y‖
        ≤ Work.BoseFixB3.CS.Pieces.chiProdV G j * (ℓ⁻¹) ^ j := hb
      _ ≤ M * (ℓ⁻¹) ^ j := mul_le_mul_of_nonneg_right hle hinv
      _ = M / ℓ ^ j := by rw [inv_pow, div_eq_mul_inv]

/-! ## 2. The leakage coupling with `(ℓκ)^{-N}` and no `R/ℓ` -/

/-- A local abbreviation for the scaled bump `chiU ℓ 0`. -/
private def chiL (ℓ : ℝ) : E3 → ℝ := fun y => Submission.BoseGases.chiU ℓ 0 y

private lemma chiL_apply (ℓ : ℝ) (y : E3) : chiL ℓ y = Submission.BoseGases.chiU ℓ 0 y := rfl

private lemma chiL_contDiff (ℓ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (chiL ℓ) := by
  rw [show chiL ℓ = fun y : E3 => Submission.BoseGases.chiU ℓ 0 y from rfl]
  exact Work.BoseFixB3.CS.Pieces.contDiff_chiU ℓ

private lemma chiL_continuous (ℓ : ℝ) : Continuous (chiL ℓ) := (chiL_contDiff ℓ).continuous

private lemma chiL_eq_zero_of_half_le (ℓ : ℝ) (hℓ : 0 < ℓ) {y : E3} (hy : ℓ / 2 ≤ ‖y‖) :
    chiL ℓ y = 0 := by
  rw [chiL_apply]
  exact Work.BoseFixB3.CS.Pieces.chiU_eq_zero_of_half_le_norm hℓ hy

private lemma chiL_abs_le (ℓ : ℝ) (y : E3) :
    |chiL ℓ y| ≤ Submission.BoseGases.chiSup := by
  rw [chiL, Work.BoseFixB3.chiU_zero_eq_chiScale]
  exact Submission.BoseGases.abs_chiScale_le_chiSup ℓ y

/-- **The leakage coupling bound at order `N`.**  For every cut-off `fc`, every `κ, ℓ > 0` and
every integrable `F` (no support restriction needed),

`|∫_{Λ(ℓ)} leak(y)·(∫_{Λ(ℓ)} χ_ℓ(x)F(x−y)χ_ℓ(y) dx) dy| ≤ C·(ℓκ)^{-N}·ℓ³·∫|F|`.

Route: substitute `t = x − y` in the inner integral, exchange the two integrals (Fubini), and for
each `t` apply the high-pass content bound to the product bump `χ_ℓ(·)χ_ℓ(·+t)`. -/
theorem leakCoupl_core_gen (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (fc : Work.BoseBoxFix.LowCut) (κ ℓ R : ℝ), 0 < κ → 0 < ℓ → 0 < R →
      R ≤ ℓ * Submission.BoseGases.chiR0 →
      ∀ (F : E3 → ℝ), Integrable F → (∀ z : E3, R ≤ ‖z‖ → F z = 0) →
      |∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB3.CS.leakFn fc κ ℓ y *
          (∫ x in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.chiU ℓ 0 x * F (x - y) * Submission.BoseGases.chiU ℓ 0 y)|
        ≤ C * (ℓ * κ) ^ (-(N : ℝ)) * ℓ ^ 3 * ∫ z : E3, ‖F z‖ := by
  obtain ⟨M, hM0, hMb⟩ := bumpProd_bound_gen N
  obtain ⟨Chp, hChp0, hChp⟩ := ContentParam.highpass_content_small_param N hN
  refine ⟨M * Chp, by positivity, ?_⟩
  intro fc κ ℓ R hκ hℓ hR hRℓ F hF hFsupp
  have hχcd : ContDiff ℝ (⊤ : ℕ∞) (chiL ℓ) := chiL_contDiff ℓ
  have hχcont : Continuous (chiL ℓ) := chiL_continuous ℓ
  have hχsupp : ∀ y : E3, ℓ / 2 ≤ ‖y‖ → chiL ℓ y = 0 := fun y hy => chiL_eq_zero_of_half_le ℓ hℓ hy
  have hχzero : ∀ y : E3, y ∉ Submission.BoseGases.acube ℓ → chiL ℓ y = 0 := fun y hy =>
    hχsupp y (le_of_lt (Work.BoseFixB3.CS.Pieces.half_lt_norm_of_notMem_acube hy))
  -- the leak factor is bounded and strongly measurable
  have hleak_bdd : ∀ y : E3, |Work.BoseFixB3.CS.leakFn fc κ ℓ y|
      ≤ 1 + ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
          (MeasureTheory.volume
            (Metric.closedBall (0 : E3) (2 * κ))).toReal := fun y =>
    Work.BoseFixB3.CS.Pieces.leakFn_abs_le fc hκ hℓ y
  have hleak_meas : AEStronglyMeasurable (Work.BoseFixB3.CS.leakFn fc κ ℓ) volume := by
    have hlow : StronglyMeasurable
        (fun y : E3 => Work.BoseBoxFix.lowMult fc κ ℓ Work.BoseFixB3.CS.oneFn y) :=
      Work.BoseFixB3.Conv.stronglyMeasurable_lowMult (Ψ := Work.BoseFixB3.CS.oneFn) measurable_const
    have h : Work.BoseFixB3.CS.leakFn fc κ ℓ
        = fun y : E3 => 1 - Work.BoseBoxFix.lowMult fc κ ℓ Work.BoseFixB3.CS.oneFn y := rfl
    rw [h]
    exact (stronglyMeasurable_const.sub hlow).aestronglyMeasurable
  -- the pair function and its integrability
  set Hp : E3 × E3 → ℝ := fun u =>
    Work.BoseFixB3.CS.leakFn fc κ ℓ u.1 * chiL ℓ u.1 * (chiL ℓ (u.1 + u.2) * F u.2) with hHp
  have hHp_meas : AEStronglyMeasurable Hp (volume.prod volume) := by
    have h1 : AEStronglyMeasurable
        (fun u : E3 × E3 => Work.BoseFixB3.CS.leakFn fc κ ℓ u.1) (volume.prod volume) :=
      hleak_meas.comp_fst
    have h2 : AEStronglyMeasurable (fun u : E3 × E3 => chiL ℓ u.1) (volume.prod volume) := by
      have : Measurable (fun u : E3 × E3 => chiL ℓ u.1) := hχcont.measurable.comp measurable_fst
      exact this.aestronglyMeasurable
    have h3 : AEStronglyMeasurable (fun u : E3 × E3 => chiL ℓ (u.1 + u.2)) (volume.prod volume) := by
      have : Measurable (fun u : E3 × E3 => chiL ℓ (u.1 + u.2)) :=
        hχcont.measurable.comp (measurable_fst.add measurable_snd)
      exact this.aestronglyMeasurable
    have h4 : AEStronglyMeasurable (fun u : E3 × E3 => F u.2) (volume.prod volume) :=
      hF.aestronglyMeasurable.comp_snd
    have h5 := (h1.mul h2).mul (h3.mul h4)
    have heq : (((fun u : E3 × E3 => Work.BoseFixB3.CS.leakFn fc κ ℓ u.1) *
          (fun u : E3 × E3 => chiL ℓ u.1)) *
        ((fun u : E3 × E3 => chiL ℓ (u.1 + u.2)) * (fun u : E3 × E3 => F u.2)))
        = fun u : E3 × E3 =>
            Work.BoseFixB3.CS.leakFn fc κ ℓ u.1 * chiL ℓ u.1 * (chiL ℓ (u.1 + u.2) * F u.2) := by
      funext u
      simp only [Pi.mul_apply]
      try ring
    rw [heq] at h5
    rw [hHp]
    exact h5
  have hHp_int : Integrable Hp (volume.prod volume) := by
    set K : ℝ := (1 + ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
        (MeasureTheory.volume (Metric.closedBall (0 : E3) (2 * κ))).toReal) *
      Submission.BoseGases.chiSup * Submission.BoseGases.chiSup with hK
    have hK0 : 0 ≤ K := by
      rw [hK]
      have h1 : 0 ≤ 1 + ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
          (MeasureTheory.volume (Metric.closedBall (0 : E3) (2 * κ))).toReal := by
        have := hleak_bdd 0; linarith [abs_nonneg (Work.BoseFixB3.CS.leakFn fc κ ℓ 0)]
      exact mul_nonneg (mul_nonneg h1 (le_trans (abs_nonneg _) (chiL_abs_le ℓ 0)))
        (le_of_lt Submission.BoseGases.chiSup_pos)
    have hA : Integrable
        (fun x : E3 => (Metric.closedBall (0 : E3) (ℓ / 2)).indicator (fun _ => K) x) volume := by
      rw [MeasureTheory.integrable_indicator_iff measurableSet_closedBall]
      exact MeasureTheory.integrableOn_const
        (ne_of_lt (isCompact_closedBall (0 : E3) (ℓ / 2)).measure_lt_top) (by simp)
    have hid : Integrable (fun u : E3 × E3 =>
        (Metric.closedBall (0 : E3) (ℓ / 2)).indicator (fun _ => K) u.1 * ‖F u.2‖)
        (volume.prod volume) := hA.mul_prod hF.norm
    refine Integrable.mono' hid hHp_meas (Filter.Eventually.of_forall fun u => ?_)
    have hb1 : |Work.BoseFixB3.CS.leakFn fc κ ℓ u.1|
        ≤ 1 + ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
            (MeasureTheory.volume (Metric.closedBall (0 : E3) (2 * κ))).toReal := hleak_bdd u.1
    have hb2 : |chiL ℓ u.1| ≤ Submission.BoseGases.chiSup := chiL_abs_le ℓ u.1
    have hb3 : |chiL ℓ (u.1 + u.2)| ≤ Submission.BoseGases.chiSup := chiL_abs_le ℓ (u.1 + u.2)
    have hchi0 : 0 ≤ Submission.BoseGases.chiSup := le_trans (abs_nonneg _) hb2
    have hK1 : 0 ≤ 1 + ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
        (MeasureTheory.volume (Metric.closedBall (0 : E3) (2 * κ))).toReal := by
      have := hleak_bdd 0; linarith [abs_nonneg (Work.BoseFixB3.CS.leakFn fc κ ℓ 0)]
    rw [Real.norm_eq_abs, hHp]
    have hprod : |Work.BoseFixB3.CS.leakFn fc κ ℓ u.1 * chiL ℓ u.1 *
        (chiL ℓ (u.1 + u.2) * F u.2)|
        = |Work.BoseFixB3.CS.leakFn fc κ ℓ u.1| * |chiL ℓ u.1| * |chiL ℓ (u.1 + u.2)| * |F u.2| := by
      rw [abs_mul, abs_mul, abs_mul]
      ring
    rw [hprod]
    by_cases hu : u.1 ∈ Metric.closedBall (0 : E3) (ℓ / 2)
    · rw [Set.indicator_of_mem hu]
      have hFnn : 0 ≤ |F u.2| := abs_nonneg _
      calc |Work.BoseFixB3.CS.leakFn fc κ ℓ u.1| * |chiL ℓ u.1| * |chiL ℓ (u.1 + u.2)| * |F u.2|
          ≤ (1 + ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
              (MeasureTheory.volume (Metric.closedBall (0 : E3) (2 * κ))).toReal) *
            Submission.BoseGases.chiSup * Submission.BoseGases.chiSup * |F u.2| := by
            refine mul_le_mul (mul_le_mul (mul_le_mul hb1 hb2 (abs_nonneg _) hK1) hb3
              (abs_nonneg _) (mul_nonneg hK1 hchi0)) le_rfl hFnn (by positivity)
        _ = K * |F u.2| := by rw [hK]
        _ = K * ‖F u.2‖ := by rw [Real.norm_eq_abs]
    · rw [Set.indicator_of_notMem hu]
      have h0 : chiL ℓ u.1 = 0 := by
        have hdist : ℓ / 2 < ‖u.1‖ := by
          by_contra hcon
          exact hu (by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; linarith [not_lt.mp hcon])
        exact hχsupp u.1 (le_of_lt hdist)
      simp [h0]
  -- ### Step 1: the inner integral, with the substitution `t = x − y`
  have hinner : ∀ y : E3,
      (∫ x in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.chiU ℓ 0 x * F (x - y) * Submission.BoseGases.chiU ℓ 0 y)
        = chiL ℓ y * ∫ t : E3, chiL ℓ (y + t) * F t := by
    intro y
    have h1 : (∫ x in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.chiU ℓ 0 x * F (x - y) * Submission.BoseGases.chiU ℓ 0 y)
        = (∫ x in Submission.BoseGases.acube ℓ, Submission.BoseGases.chiU ℓ 0 x * F (x - y))
            * Submission.BoseGases.chiU ℓ 0 y :=
      MeasureTheory.integral_mul_const _ _
    rw [h1, chiL_apply]
    have h2 : (∫ x in Submission.BoseGases.acube ℓ, Submission.BoseGases.chiU ℓ 0 x * F (x - y))
        = ∫ x : E3, chiL ℓ x * F (x - y) := by
      rw [← MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ Submission.BoseGases.acube ℓ
      · simp only [Set.indicator_of_mem hx, chiL_apply]
      · simp only [Set.indicator_of_notMem hx, hχzero x hx, zero_mul]
    rw [h2, mul_comm]
    have h3 : (fun t : E3 => chiL ℓ (y + t) * F t)
        = fun t : E3 => (fun u : E3 => chiL ℓ u * F (u - y)) (y + t) := by
      funext t; simp
    rw [h3, Submission.BoseGases.integral_comp_add_left
      (fun u : E3 => chiL ℓ u * F (u - y)) y]
    -- ### Step 2: Fubini
  have hFub : (∫ y : E3, Work.BoseFixB3.CS.leakFn fc κ ℓ y * chiL ℓ y *
        (∫ t : E3, chiL ℓ (y + t) * F t))
      = ∫ t : E3, F t * (∫ y : E3, Work.BoseFixB3.CS.leakFn fc κ ℓ y * chiL ℓ y * chiL ℓ (y + t)) := by
    have hstep1 : (∫ y : E3, Work.BoseFixB3.CS.leakFn fc κ ℓ y * chiL ℓ y *
          (∫ t : E3, chiL ℓ (y + t) * F t))
        = ∫ y : E3, ∫ t : E3, Hp (y, t) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show Work.BoseFixB3.CS.leakFn fc κ ℓ y * chiL ℓ y *
          (∫ t : E3, chiL ℓ (y + t) * F t) = ∫ t : E3, Hp (y, t)
      rw [hHp]
      rw [show (∫ t : E3, Work.BoseFixB3.CS.leakFn fc κ ℓ y * chiL ℓ y *
            (chiL ℓ (y + t) * F t))
          = ∫ t : E3, (Work.BoseFixB3.CS.leakFn fc κ ℓ y * chiL ℓ y) *
              (chiL ℓ (y + t) * F t) from by
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)]
      rw [MeasureTheory.integral_const_mul]
    have hstep2 : (∫ y : E3, ∫ t : E3, Hp (y, t)) = ∫ t : E3, ∫ y : E3, Hp (y, t) :=
      MeasureTheory.integral_integral_swap hHp_int
    have hstep3 : (∫ t : E3, ∫ y : E3, Hp (y, t))
        = ∫ t : E3, F t * (∫ y : E3, Work.BoseFixB3.CS.leakFn fc κ ℓ y * chiL ℓ y * chiL ℓ (y + t)) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      show (∫ y : E3, Hp (y, t)) = F t *
        (∫ y : E3, Work.BoseFixB3.CS.leakFn fc κ ℓ y * chiL ℓ y * chiL ℓ (y + t))
      rw [hHp]
      rw [show (∫ y : E3, Work.BoseFixB3.CS.leakFn fc κ ℓ y * chiL ℓ y * (chiL ℓ (y + t) * F t))
          = ∫ y : E3, (Work.BoseFixB3.CS.leakFn fc κ ℓ y * chiL ℓ y * chiL ℓ (y + t)) * F t from by
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)]
      rw [MeasureTheory.integral_mul_const, mul_comm]
    rw [hstep1, hstep2, hstep3]
  -- ### Step 3: the content bound for each `t`
  have hcontent : ∀ t : E3,
      |∫ y : E3, Work.BoseFixB3.CS.leakFn fc κ ℓ y * chiL ℓ y * chiL ℓ (y + t)|
        ≤ M * Chp * ℓ ^ 3 * ((ℓ * κ) ^ N)⁻¹ := by
    intro t
    have hGcd : ContDiff ℝ (⊤ : ℕ∞) (fun y : E3 => chiL ℓ y * chiL ℓ (y + t)) :=
      hχcd.mul (hχcd.comp (contDiff_id.add contDiff_const))
    have hGsupp' : ∀ y : E3, ℓ / 2 ≤ ‖y‖ → chiL ℓ y * chiL ℓ (y + t) = 0 := by
      intro y hy; rw [hχsupp y hy, zero_mul]
    have hGsupp : tsupport (fun y : E3 => chiL ℓ y * chiL ℓ (y + t))
        ⊆ Submission.BoseGases.acube ℓ := by
      have h1 : closure (Function.support (fun y : E3 => chiL ℓ y * chiL ℓ (y + t)))
          ⊆ Metric.closedBall (0 : E3) (ℓ / 2) :=
        closure_minimal (fun y hy => by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
          by_contra hcon
          exact hy (hGsupp' y (le_of_lt (lt_of_not_ge hcon))))
          (Metric.isClosed_closedBall (x := (0 : E3)) (ε := ℓ / 2))
      have h2 : Metric.closedBall (0 : E3) (ℓ / 2) ⊆ Submission.BoseGases.acube ℓ :=
        fun y hy => by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy
          exact Submission.BoseGases.mem_acube_of_norm_le hℓ.le hy
      exact subset_trans h1 h2
    have hGint : Integrable (fun y : E3 => chiL ℓ y * chiL ℓ (y + t)) :=
      hGcd.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (ℓ / 2))
          (fun y hy => by
            rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
            by_contra hcon
            exact hy (hGsupp' y (le_of_lt (lt_of_not_ge hcon)))))
    have hleakG_int : Integrable
        (fun y : E3 => Work.BoseFixB3.CS.leakFn fc κ ℓ y * (chiL ℓ y * chiL ℓ (y + t))) :=
      hGint.bdd_mul hleak_meas (Filter.Eventually.of_forall hleak_bdd)
    have hident : (∫ y : E3, Work.BoseFixB3.CS.leakFn fc κ ℓ y * (chiL ℓ y * chiL ℓ (y + t)))
        = ∫ y in Submission.BoseGases.acube ℓ,
            ((chiL ℓ y * chiL ℓ (y + t))
              - Work.BoseBoxFix.lowMult fc κ ℓ (fun z : E3 => chiL ℓ z * chiL ℓ (z + t)) y) := by
      have h1 : (∫ y : E3, Work.BoseFixB3.CS.leakFn fc κ ℓ y * (chiL ℓ y * chiL ℓ (y + t)))
          = ∫ y in Submission.BoseGases.acube ℓ,
              Work.BoseFixB3.CS.leakFn fc κ ℓ y * (chiL ℓ y * chiL ℓ (y + t)) := by
        rw [← MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        by_cases hy : y ∈ Submission.BoseGases.acube ℓ
        · rw [Set.indicator_of_mem hy]
        · rw [Set.indicator_of_notMem hy]
          simp [hχzero y hy]
      rw [h1]
      exact Work.BoseFixB3.CS.Pieces.integral_leakFn_mul_eq fc hκ hℓ hGint hGsupp hleakG_int
    have hcontent' : |∫ y in Submission.BoseGases.acube ℓ,
          ((chiL ℓ y * chiL ℓ (y + t))
            - Work.BoseBoxFix.lowMult fc κ ℓ (fun z : E3 => chiL ℓ z * chiL ℓ (z + t)) y)|
        ≤ Chp * M * ℓ ^ 3 / (ℓ * κ) ^ N := by
      refine hChp fc κ ℓ hκ hℓ (fun y : E3 => chiL ℓ y * chiL ℓ (y + t)) hGcd hGsupp' M hM0 ?_ ?_
      · intro y
        have h1 := (hMb t ℓ hℓ).1 y
        simpa only [chiL] using h1
      · intro j hj y
        have h1 := (hMb t ℓ hℓ).2 j hj y
        simpa only [chiL] using h1
    calc |∫ y : E3, Work.BoseFixB3.CS.leakFn fc κ ℓ y * chiL ℓ y * chiL ℓ (y + t)|
        = |∫ y : E3, Work.BoseFixB3.CS.leakFn fc κ ℓ y * (chiL ℓ y * chiL ℓ (y + t))| := by
          rw [MeasureTheory.integral_congr_ae (μ := volume)
            (f := fun y : E3 => Work.BoseFixB3.CS.leakFn fc κ ℓ y * chiL ℓ y * chiL ℓ (y + t))
            (g := fun y : E3 => Work.BoseFixB3.CS.leakFn fc κ ℓ y * (chiL ℓ y * chiL ℓ (y + t)))
            (Filter.Eventually.of_forall fun y => by ring)]
      _ = |∫ y in Submission.BoseGases.acube ℓ,
            ((chiL ℓ y * chiL ℓ (y + t))
              - Work.BoseBoxFix.lowMult fc κ ℓ (fun z : E3 => chiL ℓ z * chiL ℓ (z + t)) y)| := by
          rw [hident]
      _ ≤ Chp * M * ℓ ^ 3 / (ℓ * κ) ^ N := hcontent'
      _ = M * Chp * ℓ ^ 3 * ((ℓ * κ) ^ N)⁻¹ := by
          rw [div_eq_mul_inv]; ring
  -- ### Step 4: assembly
  have hmain : |∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB3.CS.leakFn fc κ ℓ y *
        (∫ x in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.chiU ℓ 0 x * F (x - y) * Submission.BoseGases.chiU ℓ 0 y)|
      ≤ M * Chp * ℓ ^ 3 * ((ℓ * κ) ^ N)⁻¹ * ∫ z : E3, ‖F z‖ := by
    have h1 : (∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB3.CS.leakFn fc κ ℓ y *
          (∫ x in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.chiU ℓ 0 x * F (x - y) * Submission.BoseGases.chiU ℓ 0 y))
        = ∫ y : E3, Work.BoseFixB3.CS.leakFn fc κ ℓ y * chiL ℓ y * (∫ t : E3, chiL ℓ (y + t) * F t) := by
      rw [← MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      by_cases hy : y ∈ Submission.BoseGases.acube ℓ
      · rw [Set.indicator_of_mem hy, hinner y]
        ring
      · rw [Set.indicator_of_notMem hy]
        simp only [hχzero y hy, mul_zero, zero_mul]
    rw [h1, hFub]
    calc |∫ t : E3, F t * (∫ y : E3, Work.BoseFixB3.CS.leakFn fc κ ℓ y * chiL ℓ y * chiL ℓ (y + t))|
        ≤ ∫ t : E3, |F t * (∫ y : E3, Work.BoseFixB3.CS.leakFn fc κ ℓ y * chiL ℓ y * chiL ℓ (y + t))| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ t : E3, ‖F t‖ * (M * Chp * ℓ ^ 3 * ((ℓ * κ) ^ N)⁻¹) := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun t => abs_nonneg _)
            (hF.norm.mul_const _) (Filter.Eventually.of_forall fun t => ?_)
          show |F t * (∫ y : E3, Work.BoseFixB3.CS.leakFn fc κ ℓ y * chiL ℓ y * chiL ℓ (y + t))|
            ≤ ‖F t‖ * (M * Chp * ℓ ^ 3 * ((ℓ * κ) ^ N)⁻¹)
          rw [abs_mul, ← Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hcontent t) (norm_nonneg _)
      _ = (M * Chp * ℓ ^ 3 * ((ℓ * κ) ^ N)⁻¹) * ∫ z : E3, ‖F z‖ := by
          rw [MeasureTheory.integral_mul_const, mul_comm]
  calc |∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB3.CS.leakFn fc κ ℓ y *
        (∫ x in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.chiU ℓ 0 x * F (x - y) * Submission.BoseGases.chiU ℓ 0 y)|
      ≤ M * Chp * ℓ ^ 3 * ((ℓ * κ) ^ N)⁻¹ * ∫ z : E3, ‖F z‖ := hmain
    _ = M * Chp * (ℓ * κ) ^ (-(N : ℝ)) * ℓ ^ 3 * ∫ z : E3, ‖F z‖ := by
        rw [Real.rpow_neg (by positivity), Real.rpow_natCast, inv_eq_one_div]
        ring

end Work.BoseFixB3.CS.LeakCouplGen
