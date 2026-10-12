import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1B.cutoffDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.cutFun_lip`

Holder of `Work.BoseFixB1B.cutFun_lip`.

`cutFun c f g` is the product of six one-dimensional factors

`x ↦ (f (x 0) · f (x 1) · f (x 2)) · (g ((x-c) 0) · g ((x-c) 1) · g ((x-c) 2))`,

three of them Lipschitz with constant `L` and three with constant `M`, all of them bounded by `1`.
Because every factor is bounded by `1`, the Lipschitz constants *add* (they do not multiply):
writing `P = F·G` with `F` the product of the three `f`-factors and `G` that of the `g`-factors,

`|P y - P x| ≤ |F y - F x|·|G y| + |F x|·|G y - G x| ≤ 3L‖y-x‖ + 3M‖y-x‖`,

where a difference of three-factor products is estimated by the telescoping identity
`a·b·c - a'·b'·c' = (a-a')·b·c + a'·(b-b')·c + a'·b'·(c-c')`.

The helper lemmas below are stated exactly for this purpose (three-factor products, and products
of a one-variable function over the three coordinates); they carry a `cutFun_` prefix to avoid
clashes with Mathlib.
-/

noncomputable section

namespace Work.BoseFixB1B

set_option autoImplicit false

/-- The product of three real numbers of absolute value at most `1` has absolute value at most
`1`. -/
lemma cutFun_abs_prod3_le_one {a b c : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc : |c| ≤ 1) :
    |a * b * c| ≤ 1 := by
  rw [abs_mul, abs_mul]
  exact mul_le_one₀ (mul_le_one₀ ha (abs_nonneg b) hb) (abs_nonneg c) hc

/-- Telescoping bound for a difference of products of three factors: if the three factors move by
at most `K` in absolute value, and all six numbers are bounded by `1` in absolute value, then the
two products differ by at most `3K`. -/
lemma cutFun_abs_prod3_sub_le {a b c a' b' c' K : ℝ} (hK : 0 ≤ K)
    (ha : |a - a'| ≤ K) (hb : |b - b'| ≤ K) (hc : |c - c'| ≤ K)
    (h1 : |a| ≤ 1) (h2 : |b| ≤ 1) (h3 : |c| ≤ 1)
    (h1' : |a'| ≤ 1) (h2' : |b'| ≤ 1) (h3' : |c'| ≤ 1) :
    |a * b * c - a' * b' * c'| ≤ 3 * K := by
  have hid : a * b * c - a' * b' * c'
      = (a - a') * b * c + a' * (b - b') * c + a' * b' * (c - c') := by ring
  have t1 : |(a - a') * b * c| ≤ K := by
    calc |(a - a') * b * c| = |a - a'| * (|b| * |c|) := by rw [abs_mul, abs_mul, mul_assoc]
      _ ≤ K * 1 :=
          mul_le_mul ha (mul_le_one₀ h2 (abs_nonneg c) h3)
            (mul_nonneg (abs_nonneg b) (abs_nonneg c)) hK
      _ = K := by ring
  have t2 : |a' * (b - b') * c| ≤ K := by
    calc |a' * (b - b') * c| = |a'| * (|b - b'| * |c|) := by rw [abs_mul, abs_mul, mul_assoc]
      _ ≤ 1 * (K * 1) :=
          mul_le_mul h1' (mul_le_mul hb h3 (abs_nonneg c) hK)
            (mul_nonneg (abs_nonneg (b - b')) (abs_nonneg c)) zero_le_one
      _ = K := by ring
  have t3 : |a' * b' * (c - c')| ≤ K := by
    calc |a' * b' * (c - c')| = |a'| * (|b'| * |c - c'|) := by rw [abs_mul, abs_mul, mul_assoc]
      _ ≤ 1 * (1 * K) :=
          mul_le_mul h1' (mul_le_mul h2' hc (abs_nonneg (c - c')) zero_le_one)
            (mul_nonneg (abs_nonneg b') (abs_nonneg (c - c'))) zero_le_one
      _ = K := by ring
  calc |a * b * c - a' * b' * c'|
      = |(a - a') * b * c + a' * (b - b') * c + a' * b' * (c - c')| := by rw [hid]
    _ ≤ |(a - a') * b * c| + |a' * (b - b') * c| + |a' * b' * (c - c')| := abs_add_three _ _ _
    _ ≤ K + K + K := by linarith
    _ = 3 * K := by ring

/-- The elementary product-rule identity for the difference of two products. -/
lemma cutFun_abs_mul_sub_mul_le (u v u' v' : ℝ) :
    |u * v - u' * v'| ≤ |u - u'| * |v| + |u'| * |v - v'| := by
  have h : u * v - u' * v' = (u - u') * v + u' * (v - v') := by ring
  rw [h]
  calc |(u - u') * v + u' * (v - v')| ≤ |(u - u') * v| + |u' * (v - v')| := abs_add_le _ _
    _ = |u - u'| * |v| + |u'| * |v - v'| := by simp only [abs_mul]

/-- **The three-coordinate product of a Lipschitz, `1`-bounded function is Lipschitz with
constant `3K`.**  This is the engine of `cutFun_lip`: applied to `φ = f` at the points `y, x` and
to `φ = g` at the translated points `y - c, x - c`. -/
lemma cutFun_coordProd_lip {K : ℝ} (hK : 0 ≤ K) {φ : ℝ → ℝ}
    (hφ : ∀ t u : ℝ, |φ u - φ t| ≤ K * |u - t|) (hb : ∀ t : ℝ, |φ t| ≤ 1)
    (z w : EuclideanSpace ℝ (Fin 3)) :
    |φ (z 0) * φ (z 1) * φ (z 2) - φ (w 0) * φ (w 1) * φ (w 2)| ≤ 3 * K * ‖z - w‖ := by
  have hcoord : ∀ i : Fin 3, |z i - w i| ≤ ‖z - w‖ := fun i => abs_coord_sub_le_norm w z i
  have hstep : ∀ i : Fin 3, |φ (z i) - φ (w i)| ≤ K * ‖z - w‖ := fun i =>
    le_trans (hφ (w i) (z i)) (mul_le_mul_of_nonneg_left (hcoord i) hK)
  have hmain := cutFun_abs_prod3_sub_le (K := K * ‖z - w‖) (mul_nonneg hK (norm_nonneg _))
    (hstep 0) (hstep 1) (hstep 2)
    (hb _) (hb _) (hb _) (hb _) (hb _) (hb _)
  calc |φ (z 0) * φ (z 1) * φ (z 2) - φ (w 0) * φ (w 1) * φ (w 2)|
      ≤ 3 * (K * ‖z - w‖) := hmain
    _ = 3 * K * ‖z - w‖ := by ring

theorem cutFun_lip {c : EuclideanSpace ℝ (Fin 3)} {f g : ℝ → ℝ} {L M : ℝ} (hL : 0 ≤ L)
    (hM : 0 ≤ M) (hf : ∀ t u : ℝ, |f u - f t| ≤ L * |u - t|)
    (hg : ∀ t u : ℝ, |g u - g t| ≤ M * |u - t|) (hfb : ∀ t : ℝ, |f t| ≤ 1)
    (hgb : ∀ t : ℝ, |g t| ≤ 1) :
    ∀ x y : EuclideanSpace ℝ (Fin 3), |cutFun c f g y - cutFun c f g x| ≤ (3 * L + 3 * M) * ‖y - x‖ := by
  intro x y
  -- factor `cutFun` into the product of the three `f`-factors and the three `g`-factors
  have hcut_y : cutFun c f g y
      = (f (y 0) * f (y 1) * f (y 2)) * (g ((y - c) 0) * g ((y - c) 1) * g ((y - c) 2)) := by
    simp only [cutFun]
    ring
  have hcut_x : cutFun c f g x
      = (f (x 0) * f (x 1) * f (x 2)) * (g ((x - c) 0) * g ((x - c) 1) * g ((x - c) 2)) := by
    simp only [cutFun]
    ring
  rw [hcut_y, hcut_x]
  -- Lipschitz bounds on the two triple products, and `1`-bounds on all four of them
  have hF : |f (y 0) * f (y 1) * f (y 2) - f (x 0) * f (x 1) * f (x 2)| ≤ 3 * L * ‖y - x‖ :=
    cutFun_coordProd_lip (φ := f) hL hf hfb y x
  have hG : |g ((y - c) 0) * g ((y - c) 1) * g ((y - c) 2)
      - g ((x - c) 0) * g ((x - c) 1) * g ((x - c) 2)| ≤ 3 * M * ‖y - x‖ := by
    have h := cutFun_coordProd_lip (φ := g) hM hg hgb (y - c) (x - c)
    simpa only [sub_sub_sub_cancel_right] using h
  have hGy : |g ((y - c) 0) * g ((y - c) 1) * g ((y - c) 2)| ≤ 1 :=
    cutFun_abs_prod3_le_one (hgb _) (hgb _) (hgb _)
  have hFx : |f (x 0) * f (x 1) * f (x 2)| ≤ 1 :=
    cutFun_abs_prod3_le_one (hfb _) (hfb _) (hfb _)
  calc |(f (y 0) * f (y 1) * f (y 2)) * (g ((y - c) 0) * g ((y - c) 1) * g ((y - c) 2))
        - (f (x 0) * f (x 1) * f (x 2)) * (g ((x - c) 0) * g ((x - c) 1) * g ((x - c) 2))|
      ≤ |f (y 0) * f (y 1) * f (y 2) - f (x 0) * f (x 1) * f (x 2)|
          * |g ((y - c) 0) * g ((y - c) 1) * g ((y - c) 2)|
        + |f (x 0) * f (x 1) * f (x 2)|
          * |g ((y - c) 0) * g ((y - c) 1) * g ((y - c) 2)
             - g ((x - c) 0) * g ((x - c) 1) * g ((x - c) 2)| :=
        cutFun_abs_mul_sub_mul_le _ _ _ _
    _ ≤ (3 * L * ‖y - x‖) * 1 + 1 * (3 * M * ‖y - x‖) := by
        have h1 := mul_le_mul hF hGy
          (abs_nonneg (g ((y - c) 0) * g ((y - c) 1) * g ((y - c) 2)))
          (mul_nonneg (mul_nonneg (by norm_num) hL) (norm_nonneg _))
        have h2 := mul_le_mul hFx hG (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
        linarith
    _ = (3 * L + 3 * M) * ‖y - x‖ := by ring

end Work.BoseFixB1B
