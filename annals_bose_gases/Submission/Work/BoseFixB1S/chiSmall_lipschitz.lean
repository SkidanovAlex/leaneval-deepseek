import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.BoseFixB1S.abs_wSmallScaled_div_convScale_le
import Submission.Work.MGroupInput.newtonianSharp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lipschitz bound for the cosine-`M`-th-power bump `chiSmall M`

Intermediate lemmas (names prefixed `chiLip`) towards
`Work.BoseFixB1S.chiSmall_lipschitz`:

* `chiLip_abs_cos_sub_cos_le` — `cos` is `1`-Lipschitz;
* `chiLip_abs_cos_pi_le` / `chiLip_half_sub_abs_le_abs_sub` — the two face estimates
  used to show that the FS profile `ζ = zeta1d` is `π`-Lipschitz
  (`chiLip_zeta1d_lipschitz`);
* `chiLip_prod3_abs_sub_le`, `chiLip_pow_abs_sub_le` — the product and power
  increments on `[0,1]`;
* `chiLip_zeta3_lipschitz` — the three-fold product profile is `3π`-Lipschitz;
* `chiLip_chiSmallBase_lipschitz` — `chiSmallBase M` is `3πM`-Lipschitz;
* `chiLip_chiSmall_eq_factor` — `chiSmall M = chiSmallBase M · chiSmallNormFactor M`,
  after which the normalisation scalar only scales the constant.
-/

noncomputable section
open MeasureTheory Metric
open scoped Real BigOperators ENNReal Topology

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option maxHeartbeats 800000

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

-- ============================================================
-- 1. `cos` is `1`-Lipschitz
-- ============================================================

lemma chiLip_abs_cos_sub_cos_le (x y : ℝ) : |Real.cos x - Real.cos y| ≤ |x - y| := by
  have h := Real.lipschitzWith_cos.dist_le_mul x y
  simpa [Real.dist_eq, NNReal.coe_one, one_mul] using h

-- ============================================================
-- 2. the FS profile `zeta1d` is `π`-Lipschitz
-- ============================================================

/-- If `|a| ≤ 1/2` and `|b| > 1/2` then the face of the support of `zeta1d` is at least
as far from `b` as from `a`. -/
lemma chiLip_half_sub_abs_le_abs_sub {a b : ℝ} (ha : |a| ≤ 1 / 2) (hb : 1 / 2 < |b|) :
    1 / 2 - |a| ≤ |a - b| := by
  have ha1 : a ≤ 1 / 2 := (abs_le.mp ha).2
  have ha2 : -(1 / 2) ≤ a := (abs_le.mp ha).1
  rcases lt_or_ge b 0 with hb0 | hb0
  · have hb' : b < -(1 : ℝ) / 2 := by
      have : |b| = -b := abs_of_neg hb0
      rw [this] at hb; linarith
    have hsub : |a - b| = a - b := by
      rw [abs_of_nonneg (by linarith : 0 ≤ a - b)]
    rw [hsub]
    rcases lt_or_ge a 0 with ha0 | ha0
    · rw [abs_of_neg ha0]; linarith
    · rw [abs_of_nonneg ha0]; linarith
  · have hb' : (1 : ℝ) / 2 < b := by rwa [abs_of_nonneg hb0] at hb
    have hsub : |a - b| = b - a := by
      rw [abs_of_neg (by linarith : a - b < 0), neg_sub]
    rw [hsub]
    rcases lt_or_ge a 0 with ha0 | ha0
    · rw [abs_of_neg ha0]; linarith
    · rw [abs_of_nonneg ha0]; linarith

/-- `|cos (π a)| ≤ π (1/2 - |a|)` for `|a| ≤ 1/2`. -/
lemma chiLip_abs_cos_pi_le {a : ℝ} (ha : |a| ≤ 1 / 2) :
    |Real.cos (Real.pi * a)| ≤ Real.pi * (1 / 2 - |a|) := by
  have h1 : Real.cos (Real.pi * a) = Real.cos (Real.pi * |a|) := cos_pi_mul_eq_cos_pi_abs a
  have h2 : Real.cos (Real.pi * |a|) = Real.sin (Real.pi * (1 / 2 - |a|)) := by
    rw [← Real.sin_pi_div_two_sub]
    congr 1
    ring
  rw [h1, h2]
  have h3 : |Real.sin (Real.pi * (1 / 2 - |a|))| ≤ |Real.pi * (1 / 2 - |a|)| :=
    Real.abs_sin_le_abs
  rwa [abs_of_nonneg (mul_nonneg Real.pi_pos.le (by linarith [ha]))] at h3

/-- `zeta1d` is `π`-Lipschitz. -/
lemma chiLip_zeta1d_lipschitz (a b : ℝ) :
    |zeta1d a - zeta1d b| ≤ Real.pi * |a - b| := by
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  rcases lt_or_ge (1 / 2) |a| with ha | ha
  · rcases lt_or_ge (1 / 2) |b| with hb | hb
    · rw [zeta1d_of_one_half_lt ha, zeta1d_of_one_half_lt hb, sub_zero, abs_zero]
      exact mul_nonneg hpi (abs_nonneg _)
    · rw [zeta1d_of_one_half_lt ha, zeta1d_of_abs_le hb]
      rw [zero_sub, abs_neg]
      have h1 : |Real.cos (Real.pi * b)| ≤ Real.pi * (1 / 2 - |b|) := chiLip_abs_cos_pi_le hb
      have h2 : 1 / 2 - |b| ≤ |b - a| := chiLip_half_sub_abs_le_abs_sub hb ha
      have h3 : Real.pi * (1 / 2 - |b|) ≤ Real.pi * |a - b| := by
        rw [abs_sub_comm b a] at h2
        exact mul_le_mul_of_nonneg_left h2 hpi
      linarith
  · rcases lt_or_ge (1 / 2) |b| with hb | hb
    · rw [zeta1d_of_abs_le ha, zeta1d_of_one_half_lt hb, sub_zero]
      have h1 : |Real.cos (Real.pi * a)| ≤ Real.pi * (1 / 2 - |a|) := chiLip_abs_cos_pi_le ha
      have h2 : 1 / 2 - |a| ≤ |a - b| := chiLip_half_sub_abs_le_abs_sub ha hb
      have h3 : Real.pi * (1 / 2 - |a|) ≤ Real.pi * |a - b| :=
        mul_le_mul_of_nonneg_left h2 hpi
      linarith
    · rw [zeta1d_of_abs_le ha, zeta1d_of_abs_le hb]
      have h := chiLip_abs_cos_sub_cos_le (Real.pi * a) (Real.pi * b)
      have hpi' : |Real.pi * a - Real.pi * b| = Real.pi * |a - b| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hpi]
      rwa [hpi'] at h

-- ============================================================
-- 3. product-of-three increment on `[0,1]`
-- ============================================================

lemma chiLip_prod3_abs_sub_le {a0 a1 a2 b0 b1 b2 : ℝ}
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (ha0' : a0 ≤ 1) (ha1' : a1 ≤ 1) (ha2' : a2 ≤ 1)
    (hb0' : b0 ≤ 1) (hb1' : b1 ≤ 1) (hb2' : b2 ≤ 1) :
    |a0 * a1 * a2 - b0 * b1 * b2| ≤ |a0 - b0| + |a1 - b1| + |a2 - b2| := by
  have key : a0 * a1 * a2 - b0 * b1 * b2
      = (a0 - b0) * a1 * a2 + b0 * (a1 - b1) * a2 + b0 * b1 * (a2 - b2) := by ring
  rw [key]
  have h1 : |(a0 - b0) * a1 * a2| ≤ |a0 - b0| := by
    rw [abs_mul, abs_mul, abs_of_nonneg ha1, abs_of_nonneg ha2]
    calc |a0 - b0| * a1 * a2 ≤ |a0 - b0| * 1 * 1 := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left ha1' (abs_nonneg _)
          · exact ha2'
          · exact ha2
          · norm_num
      _ = |a0 - b0| := by ring
  have h2 : |b0 * (a1 - b1) * a2| ≤ |a1 - b1| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hb0, abs_of_nonneg ha2]
    calc b0 * |a1 - b1| * a2 ≤ 1 * |a1 - b1| * 1 := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right hb0' (abs_nonneg _)
          · exact ha2'
          · exact ha2
          · positivity
      _ = |a1 - b1| := by ring
  have h3 : |b0 * b1 * (a2 - b2)| ≤ |a2 - b2| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hb0, abs_of_nonneg hb1]
    calc b0 * b1 * |a2 - b2| ≤ 1 * 1 * |a2 - b2| := by
          apply mul_le_mul
          · exact mul_le_mul hb0' hb1' hb1 (by norm_num)
          · exact le_rfl
          · exact abs_nonneg _
          · positivity
      _ = |a2 - b2| := by ring
  calc |(a0 - b0) * a1 * a2 + b0 * (a1 - b1) * a2 + b0 * b1 * (a2 - b2)|
      ≤ |(a0 - b0) * a1 * a2| + |b0 * (a1 - b1) * a2| + |b0 * b1 * (a2 - b2)| :=
        abs_add_three _ _ _
    _ ≤ |a0 - b0| + |a1 - b1| + |a2 - b2| := by linarith

-- ============================================================
-- 4. `x ↦ x ^ M` is `M`-Lipschitz on `[0,1]`
-- ============================================================

lemma chiLip_pow_abs_sub_le {x y : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hx1 : x ≤ 1)
    (hy1 : y ≤ 1) (M : ℕ) : |x ^ M - y ^ M| ≤ M * |x - y| := by
  have h := abs_pow_sub_pow_le x y M
  have hxabs : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have hyabs : |y| ≤ 1 := by rw [abs_of_nonneg hy0]; exact hy1
  have hmax : max |x| |y| ≤ 1 := max_le hxabs hyabs
  have hmax0 : 0 ≤ max |x| |y| := le_trans (abs_nonneg x) (le_max_left _ _)
  have hp : max |x| |y| ^ (M - 1) ≤ 1 := pow_le_one₀ hmax0 hmax
  calc |x ^ M - y ^ M| ≤ |x - y| * ↑M * max |x| |y| ^ (M - 1) := h
    _ ≤ |x - y| * ↑M * 1 := by
        apply mul_le_mul_of_nonneg_left hp
        positivity
    _ = M * |x - y| := by ring

-- ============================================================
-- 5. the three-fold product profile is `3π`-Lipschitz
-- ============================================================

lemma chiLip_zeta3_lipschitz (y t : ℝ³) :
    |zeta1d (y.ofLp 0) * zeta1d (y.ofLp 1) * zeta1d (y.ofLp 2)
      - zeta1d ((y - t).ofLp 0) * zeta1d ((y - t).ofLp 1) * zeta1d ((y - t).ofLp 2)|
      ≤ 3 * Real.pi * ‖t‖ := by
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hp3 := chiLip_prod3_abs_sub_le
      (a0 := zeta1d (y.ofLp 0)) (a1 := zeta1d (y.ofLp 1)) (a2 := zeta1d (y.ofLp 2))
      (b0 := zeta1d ((y - t).ofLp 0)) (b1 := zeta1d ((y - t).ofLp 1))
      (b2 := zeta1d ((y - t).ofLp 2))
      (zeta1d_nonneg _) (zeta1d_nonneg _) (zeta1d_nonneg _)
      (zeta1d_nonneg _) (zeta1d_nonneg _) (zeta1d_nonneg _)
      (zeta1d_le_one _) (zeta1d_le_one _) (zeta1d_le_one _)
      (zeta1d_le_one _) (zeta1d_le_one _) (zeta1d_le_one _)
  have hterm : ∀ j : Fin 3, |zeta1d (y.ofLp j) - zeta1d ((y - t).ofLp j)| ≤
      Real.pi * ‖t‖ := by
    intro j
    have h := chiLip_zeta1d_lipschitz (y.ofLp j) ((y - t).ofLp j)
    have hdiff : y.ofLp j - (y - t).ofLp j = t.ofLp j := by
      rw [show (y - t).ofLp j = y.ofLp j - t.ofLp j from rfl]
      ring
    rw [hdiff] at h
    have hle : ‖t.ofLp j‖ ≤ ‖t‖ := PiLp.norm_apply_le t j
    rw [Real.norm_eq_abs] at hle
    calc |zeta1d (y.ofLp j) - zeta1d ((y - t).ofLp j)| ≤ Real.pi * |t.ofLp j| := h
      _ ≤ Real.pi * ‖t‖ := mul_le_mul_of_nonneg_left hle hpi
  have hsum : |zeta1d (y.ofLp 0) * zeta1d (y.ofLp 1) * zeta1d (y.ofLp 2)
        - zeta1d ((y - t).ofLp 0) * zeta1d ((y - t).ofLp 1) * zeta1d ((y - t).ofLp 2)|
      ≤ Real.pi * ‖t‖ + Real.pi * ‖t‖ + Real.pi * ‖t‖ := by
    linarith [hp3, hterm (0 : Fin 3), hterm (1 : Fin 3), hterm (2 : Fin 3)]
  linarith [hsum]

-- ============================================================
-- 6. `chiSmallBase M` is `3πM`-Lipschitz
-- ============================================================

lemma chiLip_chiSmallBase_lipschitz {M : ℕ} (hM : 1 ≤ M) (y t : ℝ³) :
    |chiSmallBase M y - chiSmallBase M (y - t)| ≤ (3 * Real.pi * M) * ‖t‖ := by
  change |(zeta1d (y.ofLp 0) * zeta1d (y.ofLp 1) * zeta1d (y.ofLp 2)) ^ M
      - (zeta1d ((y - t).ofLp 0) * zeta1d ((y - t).ofLp 1) * zeta1d ((y - t).ofLp 2)) ^ M|
      ≤ (3 * Real.pi * M) * ‖t‖
  have hAB := chiLip_zeta3_lipschitz y t
  have hA0 : 0 ≤ zeta1d (y.ofLp 0) * zeta1d (y.ofLp 1) * zeta1d (y.ofLp 2) :=
    mul_nonneg (mul_nonneg (zeta1d_nonneg _) (zeta1d_nonneg _)) (zeta1d_nonneg _)
  have hB0 : 0 ≤ zeta1d ((y - t).ofLp 0) * zeta1d ((y - t).ofLp 1)
      * zeta1d ((y - t).ofLp 2) :=
    mul_nonneg (mul_nonneg (zeta1d_nonneg _) (zeta1d_nonneg _)) (zeta1d_nonneg _)
  have hA1 : zeta1d (y.ofLp 0) * zeta1d (y.ofLp 1) * zeta1d (y.ofLp 2) ≤ 1 :=
    mul_le_one₀ (mul_le_one₀ (zeta1d_le_one _) (zeta1d_nonneg _) (zeta1d_le_one _))
      (zeta1d_nonneg _) (zeta1d_le_one _)
  have hB1 : zeta1d ((y - t).ofLp 0) * zeta1d ((y - t).ofLp 1)
      * zeta1d ((y - t).ofLp 2) ≤ 1 :=
    mul_le_one₀ (mul_le_one₀ (zeta1d_le_one _) (zeta1d_nonneg _) (zeta1d_le_one _))
      (zeta1d_nonneg _) (zeta1d_le_one _)
  calc |(zeta1d (y.ofLp 0) * zeta1d (y.ofLp 1) * zeta1d (y.ofLp 2)) ^ M
        - (zeta1d ((y - t).ofLp 0) * zeta1d ((y - t).ofLp 1) * zeta1d ((y - t).ofLp 2)) ^ M|
      ≤ M * |(zeta1d (y.ofLp 0) * zeta1d (y.ofLp 1) * zeta1d (y.ofLp 2))
          - (zeta1d ((y - t).ofLp 0) * zeta1d ((y - t).ofLp 1) * zeta1d ((y - t).ofLp 2))| :=
        chiLip_pow_abs_sub_le hA0 hB0 hA1 hB1 M
    _ ≤ M * (3 * Real.pi * ‖t‖) := mul_le_mul_of_nonneg_left hAB (Nat.cast_nonneg M)
    _ = (3 * Real.pi * M) * ‖t‖ := by ring

-- ============================================================
-- 7. pull out the normalisation factor
-- ============================================================

lemma chiLip_chiSmall_eq_factor (M : ℕ) (z : ℝ³) :
    chiSmall M z = chiSmallBase M z * chiSmallNormFactor M := by
  rw [chiSmall, chiSmallNormFactor, div_eq_mul_inv]

/-- **Lipschitz bound for the cosine-`M`-th-power bump `chiSmall M`** (`M ≥ 1`).

Route: `chiSmall M = chiSmallBase M / √(chiSmallNormSq M)` with
`chiSmallBase M z = (ζ(z₀)·ζ(z₁)·ζ(z₂))^M` (`Submission.Work.ChiSmall`), and
`ζ = zeta1d` is `π`-Lipschitz: for `|a|,|b| ≤ 1/2`,
`|cos(πa) − cos(πb)| = |2 sin(π(a+b)/2) sin(π(a−b)/2)| ≤ π|a−b|`; at the faces
`ζ(±1/2) = 0` and `|cos(πa)| = |sin(π(a ∓ 1/2))| ≤ π|a ∓ 1/2| ≤ π|a−b|` for `|b| ≥ 1/2`;
outside, both terms vanish.  A product of three `π`-Lipschitz functions with values in `[0,1]`
is `3π`-Lipschitz, `z ↦ z.ofLp j` is `1`-Lipschitz, `F ↦ F^M` on `[0,1]` is `M`-Lipschitz
(`|a^M − b^M| ≤ M|a−b|` for `a,b ∈ [0,1]`), and the nonnegative scalar
`chiSmallNormFactor M` only scales the constant, so `L := 3πM·chiSmallNormFactor M` works
(any positive multiple does; `chiSmallNormSq M > 0` for `M ≥ 1`, `chiSmallNormSq_pos`). -/
theorem chiSmall_lipschitz {M : ℕ} (hM : 1 ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y t : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.chiSmall M y - Submission.BoseGases.chiSmall M (y - t)|
        ≤ L * ‖t‖ := by
  refine ⟨3 * Real.pi * M * chiSmallNormFactor M, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (Nat.cast_nonneg M)) (inv_nonneg.mpr (Real.sqrt_nonneg _))
  · intro y t
    have hb := chiLip_chiSmallBase_lipschitz (M := M) hM y t
    have hf : 0 ≤ chiSmallNormFactor M := inv_nonneg.mpr (Real.sqrt_nonneg _)
    calc |chiSmall M y - chiSmall M (y - t)|
        = |chiSmallBase M y * chiSmallNormFactor M
            - chiSmallBase M (y - t) * chiSmallNormFactor M| := by
            rw [chiLip_chiSmall_eq_factor M y, chiLip_chiSmall_eq_factor M (y - t)]
      _ = |chiSmallBase M y - chiSmallBase M (y - t)| * chiSmallNormFactor M := by
            rw [← sub_mul, abs_mul, abs_of_nonneg hf]
      _ ≤ (3 * Real.pi * M * ‖t‖) * chiSmallNormFactor M :=
            mul_le_mul_of_nonneg_right hb hf
      _ = (3 * Real.pi * M * chiSmallNormFactor M) * ‖t‖ := by ring

end Work.BoseFixB1S
