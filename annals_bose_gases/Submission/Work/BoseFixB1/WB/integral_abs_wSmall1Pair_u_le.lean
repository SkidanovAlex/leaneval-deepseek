import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.WB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WB.integral_abs_wSmall1Pair_u_le`

The `u`-integrated *absolute-value* bound for the localised one-body kernel
`wSmall1Pair`.  Writing `z := x − y` and

    wSmall1Pair h M ℓ d u x y
      = χ_{B(u)}(x) · ( g₀(z) / ( (χ_M⋆χ_M)(z/(ℓd)) · (χ⋆χ)(z/ℓ) ) ) · χ_{B(u)}(y),

the only `u`-dependence sits in the two cutoff factors, so the exact two-point
partition identity `chiSmallB_partition_xy_u` collapses the `u`-integral:

    ∫_u |wSmall1Pair h M ℓ d u x y|
      = χ(x/ℓ)·χ(y/ℓ) · (χ_M⋆χ_M)(z/(ℓd)) · |g₀(z)| / ( (χ_M⋆χ_M)(z/(ℓd)) · (χ⋆χ)(z/ℓ) )
      = χ(x/ℓ)·χ(y/ℓ) · |g₀(z)| / (χ⋆χ)(z/ℓ),

the `(ℓd)`-denominator cancelling against the `u`-mass.  The result is exactly
the requested bound with the `(ℓd)`-renormalisation invisible, which is why the
statement carries *no* smallness hypothesis on `ℓ, d` — only positivity.
-/

namespace Work.BoseFixB1.WB

open MeasureTheory

/-- The cosine-`M` self-convolution is nonnegative (it is an integral of a
product of nonnegative bumps). -/
private lemma conv3Small_nonneg_aux (M : ℕ) (z : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Submission.BoseGases.conv3Small M z := by
  unfold Submission.BoseGases.conv3Small
  exact integral_nonneg fun w => mul_nonneg (Submission.BoseGases.chiSmall_nonneg M w)
    (Submission.BoseGases.chiSmall_nonneg M (z - w))

/-- The scaled self-convolution is nonnegative. -/
private lemma convScaleSmall_nonneg_aux (M : ℕ) (c : ℝ) (z : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Submission.BoseGases.convScaleSmall M c z := by
  unfold Submission.BoseGases.convScaleSmall
  exact conv3Small_nonneg_aux M _

/-- The elementary cancellation `X·c·(G/(c·s)) ≤ X·(G·s⁻¹)` for `X, G, s ≥ 0`
(no sign hypothesis on `c` is needed: either `c = 0` and the left side vanishes,
or `c ≠ 0` and `c` cancels). -/
private lemma arith_aux (X G c s : ℝ) (hX : 0 ≤ X) (hG : 0 ≤ G) (hs : 0 ≤ s) :
    X * c * (G / (c * s)) ≤ X * (G * s⁻¹) := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    simp only [mul_zero, zero_mul]
    exact mul_nonneg hX (mul_nonneg hG (inv_nonneg.mpr hs))
  · have h1 : c * (G / (c * s)) = G / s := by field_simp
    rw [mul_assoc, h1, div_eq_mul_inv]

theorem integral_abs_wSmall1Pair_u_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    (∫ u : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.wSmall1Pair h M ℓ d u x y|)
      ≤ Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiScale ℓ y *
          (|Submission.BoseGases.g0 v h (x - y)| * (Submission.BoseGases.convScale ℓ (x - y))⁻¹) := by
  have hsn : 0 ≤ Submission.BoseGases.convScale ℓ (x - y) :=
    Submission.BoseGases.convScale_nonneg ℓ (x - y)
  have hcn : 0 ≤ Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y) :=
    convScaleSmall_nonneg_aux M (ℓ * d) (x - y)
  -- the pointwise absolute value of the kernel, with the constants factored out
  have hpt : ∀ u : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
        = |Submission.BoseGases.chiSmallB M ℓ d u x| *
          |Submission.BoseGases.chiSmallB M ℓ d u y| *
          (|Submission.BoseGases.g0 v h (x - y)| /
            (Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y) *
             Submission.BoseGases.convScale ℓ (x - y))) := by
    intro u
    have h1 : Submission.BoseGases.wSmall1Pair h M ℓ d u x y
        = Submission.BoseGases.chiSmallB M ℓ d u x *
          (Submission.BoseGases.g0 v h (x - y) /
            Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y) /
            Submission.BoseGases.convScale ℓ (x - y)) *
          Submission.BoseGases.chiSmallB M ℓ d u y := rfl
    rw [h1]
    simp only [abs_mul, abs_div, abs_of_nonneg hcn, abs_of_nonneg hsn]
    rw [div_div]
    ring
  -- the `u`-integral of the cutoff pair, the partition identity
  have habs_int : (∫ u, |Submission.BoseGases.chiSmallB M ℓ d u x| *
        |Submission.BoseGases.chiSmallB M ℓ d u y|)
      = Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiScale ℓ y *
        Submission.BoseGases.conv3Small M ((ℓ * d)⁻¹ • (x - y)) := by
    rw [← Submission.BoseGases.chiSmallB_partition_xy_u hM hℓ hd x y]
    apply integral_congr_ae
    filter_upwards with u
    rw [abs_of_nonneg (Submission.BoseGases.chiSmallB_nonneg M ℓ d u x),
        abs_of_nonneg (Submission.BoseGases.chiSmallB_nonneg M ℓ d u y)]
  calc
    (∫ u : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.wSmall1Pair h M ℓ d u x y|)
        = ∫ u, |Submission.BoseGases.chiSmallB M ℓ d u x| *
              |Submission.BoseGases.chiSmallB M ℓ d u y| *
              (|Submission.BoseGases.g0 v h (x - y)| /
                (Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y) *
                 Submission.BoseGases.convScale ℓ (x - y))) := by
          apply integral_congr_ae; filter_upwards with u; exact hpt u
    _ = (∫ u, |Submission.BoseGases.chiSmallB M ℓ d u x| *
              |Submission.BoseGases.chiSmallB M ℓ d u y|) *
              (|Submission.BoseGases.g0 v h (x - y)| /
                (Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y) *
                 Submission.BoseGases.convScale ℓ (x - y))) := by
          rw [integral_mul_const]
    _ = (Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiScale ℓ y *
              Submission.BoseGases.conv3Small M ((ℓ * d)⁻¹ • (x - y))) *
              (|Submission.BoseGases.g0 v h (x - y)| /
                (Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y) *
                 Submission.BoseGases.convScale ℓ (x - y))) := by
          rw [habs_int]
    _ ≤ Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiScale ℓ y *
              (|Submission.BoseGases.g0 v h (x - y)| *
               (Submission.BoseGases.convScale ℓ (x - y))⁻¹) := by
          exact arith_aux _ _ _ _ (mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ x)
              (Submission.BoseGases.chiScale_nonneg ℓ y)) (abs_nonneg _) hsn

end Work.BoseFixB1.WB
