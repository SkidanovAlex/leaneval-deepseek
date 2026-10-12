import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.WB.integrable_wSmall1Pair_triple_univ
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WB.mass_total2` — the total localised one-body mass at the repointed kernels

FS `eq:appw1sliding` for the corpus's repointed kernels, *with* the sign hypothesis on the
scattering length (`0 ≤ a v`) that its sibling `mass_total` is missing (see
`mass_total_REFUTED.md`):

    |∫_u ∬ w_{1,B(u)} − 8π(a v)ℓ³| ≤ convDevC M·(R0/ℓ)²·8π(a v)·ℓ³ .

At the repointed kernels the mass identity is **exact**:

* `Submission.BoseGases.dlW1Pair_triple_uInner` (the `u`-innermost cancellation
  `chiSmallB_w1_pair_uint_cancel` together with the exact double integral
  `kernel_double_integral`) gives `∫_x∫_y∫_u wSmall1Pair = ℓ³∫g₀`, and
  `Submission.BoseGases.g0_integral` gives `∫g₀ = 8π(a v)`;
* the requested left-hand side integrates `u` **outermost**
  (`w1MassB h M ℓ d u = ∫_x∫_y wSmall1Pair h M ℓ d u x y` definitionally), so it is
  identified with the `u`-innermost triple by the two Fubini moves
  `MeasureTheory.integral_prod` and `MeasureTheory.integral_integral_swap`, legitimate by the
  joint integrability `integrable_wSmall1Pair_triple_univ` (the localised kernel is bounded
  with compact support in `(u,x,y)` under the regime hypotheses).

Hence the left-hand side is `0` and the stated quadratic-weight error is pure slack: the
conclusion reduces to `0 ≤ convDevC M·(R0/ℓ)²·8π(a v)·ℓ³`, which holds because
`convDevC M ≥ 0`, `(R0/ℓ)² ≥ 0`, `ℓ³ ≥ 0` and `0 ≤ a v` — the very hypothesis whose absence
makes `mass_total` false.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators

namespace Work.BoseFixB1.WB

set_option linter.unusedVariables false

theorem mass_total2 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R0 : ℝ} {M : ℕ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hav : 0 ≤ _root_.BoseGases.a v)
    (hM : 3 ≤ M) {ℓ d r₀ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hR : R0 ≤ ℓ * d / 16) (hr₀ : 0 < r₀)
    (hRℓ : R0 ≤ ℓ * r₀)
    (hC : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ r₀ → 1 / 2 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x) :
    |(∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1.w1MassB h M ℓ d u)
        - 8 * Real.pi * _root_.BoseGases.a v * ℓ ^ 3|
      ≤ Submission.BoseGases.convDevC M * (R0 / ℓ) ^ 2 * (8 * Real.pi * _root_.BoseGases.a v) * ℓ ^ 3 := by
  have hM1 : 1 ≤ M := by omega
  -- joint integrability of the localised kernel on the product of the three Lebesgue measures
  have hInt : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) ×
          (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
        Submission.BoseGases.wSmall1Pair h M ℓ d p.1 p.2.1 p.2.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))) :=
    integrable_wSmall1Pair_triple_univ (v := v) (h := h) (R0 := R0) (M := M)
      hv_supp hR0 hM1 hℓ hd hR hr₀ hRℓ hC
  -- `w1MassB` is the `(x,y)`-double integral of the kernel
  have hwid : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1.w1MassB h M ℓ d u)
      = ∫ u, ∫ x, ∫ y, Submission.BoseGases.wSmall1Pair h M ℓ d u x y := by
    simp only [Work.BoseFixB1.w1MassB]
  -- Fubini, first move: `∫_u ∫_q = ∫_{(u,q)}`
  have h1 : (∫ p : EuclideanSpace ℝ (Fin 3) ×
        (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        Submission.BoseGases.wSmall1Pair h M ℓ d p.1 p.2.1 p.2.2)
      = ∫ u, ∫ q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wSmall1Pair h M ℓ d u q.1 q.2 :=
    MeasureTheory.integral_prod
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      (f := fun p : EuclideanSpace ℝ (Fin 3) ×
          (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
        Submission.BoseGases.wSmall1Pair h M ℓ d p.1 p.2.1 p.2.2) hInt
  -- the mass integral in the corpus order (`u` outermost)
  have hswapL : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1.w1MassB h M ℓ d u)
      = ∫ p : EuclideanSpace ℝ (Fin 3) ×
          (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
          Submission.BoseGases.wSmall1Pair h M ℓ d p.1 p.2.1 p.2.2 := by
    rw [hwid]
    have hcong : (∫ u, ∫ x, ∫ y, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
        = ∫ u, ∫ q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.wSmall1Pair h M ℓ d u q.1 q.2 := by
      refine integral_congr_ae ?_
      filter_upwards [MeasureTheory.Integrable.prod_right_ae hInt] with u hu
      exact (MeasureTheory.integral_prod
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
        (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
        (f := fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.wSmall1Pair h M ℓ d u q.1 q.2) hu).symm
    exact hcong.trans h1.symm
  -- the same triple integral in the `u`-innermost order (`dlW1Pair_triple_uInner`'s order)
  have hswapR : (∫ x, ∫ y, ∫ u, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
      = ∫ p : EuclideanSpace ℝ (Fin 3) ×
          (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
          Submission.BoseGases.wSmall1Pair h M ℓ d p.1 p.2.1 p.2.2 := by
    have hmarg : MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) ×
          EuclideanSpace ℝ (Fin 3) =>
        ∫ u, Submission.BoseGases.wSmall1Pair h M ℓ d u q.1 q.2)
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
          (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :=
      MeasureTheory.Integrable.integral_prod_right hInt
    have h2 : (∫ q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
          ∫ u, Submission.BoseGases.wSmall1Pair h M ℓ d u q.1 q.2)
        = ∫ x, ∫ y, ∫ u, Submission.BoseGases.wSmall1Pair h M ℓ d u x y :=
      MeasureTheory.integral_prod
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
        (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
        (f := fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          ∫ u, Submission.BoseGases.wSmall1Pair h M ℓ d u q.1 q.2) hmarg
    have h3 : (∫ u, ∫ q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wSmall1Pair h M ℓ d u q.1 q.2)
        = ∫ q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
          ∫ u, Submission.BoseGases.wSmall1Pair h M ℓ d u q.1 q.2 :=
      MeasureTheory.integral_integral_swap
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
        (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
          (volume : Measure (EuclideanSpace ℝ (Fin 3))))
        (f := fun u q => Submission.BoseGases.wSmall1Pair h M ℓ d u q.1 q.2) hInt
    exact h2.symm.trans (h3.symm.trans h1.symm)
  -- the mass identity `∫_u ∬ w_{1,B(u)} = ℓ³∫g₀ = 8π(a v)ℓ³`
  have hval : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1.w1MassB h M ℓ d u)
      = 8 * Real.pi * _root_.BoseGases.a v * ℓ ^ 3 := by
    rw [hswapL.trans hswapR.symm]
    rw [Submission.BoseGases.dlW1Pair_triple_uInner (v := v) (R0 := R0) hv_supp hR0 h
      (M := M) hM1 hℓ hd hR hr₀ hRℓ hC]
    rw [Submission.BoseGases.g0_integral hR0 hv_supp h]
    ring
  rw [hval, sub_self, abs_zero]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (Submission.BoseGases.convDevC_nonneg M) (sq_nonneg (R0 / ℓ)))
      (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hav))
    (by positivity)

end Work.BoseFixB1.WB
