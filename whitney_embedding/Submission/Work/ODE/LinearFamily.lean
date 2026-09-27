import Mathlib
import Submission.Work.ODE.GlobalFlow

/-!
# Global integral curves of a time-dependent linear family

The workspace lemma `Work.ODE.exists_isIntegralCurve_of_lipschitzWith` gives global integral curves
for an *autonomous* Lipschitz field which is globally *bounded*.  A family of linear maps
`A : ℝ → E →L[ℝ] E` gives a field `(t, z) ↦ A t z` which is neither autonomous nor bounded, but it is
*linearly* bounded (`‖A t z‖ ≤ C ‖z‖`), and global existence still holds.

The device is a **saturation**: a map `ψ : E → E` which is the identity on the ball of radius `R`,
bounded by `4R`, and Lipschitz.  Then the field `X (t, z) = (1, satCutoff R ‖z‖ • A t z)` on `ℝ × E`
is autonomous and globally bounded, so the autonomous theorem applies to it; the Gronwall estimate
`d/ds ‖γ s‖² ≤ 2 C ‖γ s‖²` keeps `γ` inside the ball of radius `R` for a window of time, where the
cutoff is `1`, so `γ` solves the *linear* equation there.

This file provides the scalar cutoff and its basic properties.  The four estimates that make the
saturated field Lipschitz (and hence make the plan above executable) are recorded at the bottom.

See `CutPush/NOTES_linear_fibered_route.md` §8; the consumer is the FRAME brick
`Work.Whitney.CutPush.plane_family_trivialisation`.
-/

set_option autoImplicit false

open scoped Topology NNReal
open Set Function

namespace Work.ODE

/-- The scalar cutoff of the saturation: `1` on `[0,R]` and `0` on `[4R,∞)`. -/
noncomputable def satCutoff (R s : ℝ) : ℝ := max 0 (min 1 ((4 * R - s) / (3 * R)))

theorem satCutoff_eq_one {R s : ℝ} (hR : 0 < R) (hs : s ≤ R) : satCutoff R s = 1 := by
  have h : 1 ≤ (4 * R - s) / (3 * R) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  rw [satCutoff, min_eq_left h, max_eq_right (by norm_num)]

theorem satCutoff_eq_zero {R s : ℝ} (hR : 0 < R) (hs : 4 * R ≤ s) : satCutoff R s = 0 := by
  have h : (4 * R - s) / (3 * R) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  rw [satCutoff, min_eq_right (h.trans (by norm_num : (0:ℝ) ≤ 1)), max_eq_left h]

theorem satCutoff_nonneg (R s : ℝ) : 0 ≤ satCutoff R s := le_max_left _ _

theorem satCutoff_le_one (R s : ℝ) : satCutoff R s ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

/-- `max 0 x ≤ x` for `0 ≤ x` (the instances are those of `ℝ`, so this composes with the `max`-lemmas
below without instance mismatch). -/
lemma max_zero_le_self {x : ℝ} (hx : 0 ≤ x) : max 0 x ≤ x := max_le hx le_rfl

/-- **Estimate 2 of the docstring.**  The scalar cutoff is `1/(3R)`-Lipschitz: this is what makes the
saturated field Lipschitz in the space variable. -/
theorem satCutoff_abs_sub_le {R : ℝ} (hR : 0 < R) (s s' : ℝ) :
    |satCutoff R s - satCutoff R s'| ≤ |s - s'| / (3 * R) := by
  set A : ℝ := min 1 ((4 * R - s) / (3 * R)) with hA
  set B : ℝ := min 1 ((4 * R - s') / (3 * R)) with hB
  have h1 : |satCutoff R s - satCutoff R s'| ≤ |A - B| := by
    have h := abs_max_sub_max_le_max (0 : ℝ) A (0 : ℝ) B
    have h' : |max 0 A - max 0 B| ≤ max (0 : ℝ) |A - B| := by
      simpa only [sub_self, abs_zero] using h
    have h'' : |max 0 A - max 0 B| ≤ |A - B| := h'.trans (max_zero_le_self (abs_nonneg _))
    simpa only [satCutoff, ← hA, ← hB] using h''
  have h2 : |A - B| ≤ |(4 * R - s) / (3 * R) - (4 * R - s') / (3 * R)| := by
    have h := abs_min_sub_min_le_max (1 : ℝ) ((4 * R - s) / (3 * R)) (1 : ℝ)
      ((4 * R - s') / (3 * R))
    have h' : |min 1 ((4 * R - s) / (3 * R)) - min 1 ((4 * R - s') / (3 * R))|
        ≤ max (0 : ℝ) |(4 * R - s) / (3 * R) - (4 * R - s') / (3 * R)| := by
      simpa only [sub_self, abs_zero] using h
    have h'' : |min 1 ((4 * R - s) / (3 * R)) - min 1 ((4 * R - s') / (3 * R))|
        ≤ |(4 * R - s) / (3 * R) - (4 * R - s') / (3 * R)| :=
      h'.trans (max_zero_le_self (abs_nonneg _))
    simpa only [hA, hB] using h''
  have h3 : |(4 * R - s) / (3 * R) - (4 * R - s') / (3 * R)| = |s - s'| / (3 * R) := by
    rw [div_sub_div_same, show 4 * R - s - (4 * R - s') = -(s - s') by ring, abs_div, abs_neg,
      abs_of_pos (by positivity : (0 : ℝ) < 3 * R)]
  exact h1.trans (h2.trans h3.le)

section RadialSaturation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radial saturation `ψ z = satCutoff R ‖z‖ • z`. -/
noncomputable def satMap (R : ℝ) (z : E) : E := (satCutoff R ‖z‖) • z

/-- `ψ` is the identity on the ball of radius `R`. -/
theorem satMap_eq_self {R : ℝ} (hR : 0 < R) {z : E} (hz : ‖z‖ ≤ R) : satMap R z = z := by
  rw [satMap, satCutoff_eq_one hR hz, one_smul]

/-- **Estimate 1 of the docstring.**  `satCutoff R ‖z‖ * ‖z‖ ≤ 4 * R`: the saturation factor times
the radius is bounded, which is what bounds the saturated field. -/
theorem satCutoff_mul_norm_le {R : ℝ} (hR : 0 < R) (z : E) :
    satCutoff R ‖z‖ * ‖z‖ ≤ 4 * R := by
  have hz0 : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
  by_cases h : ‖z‖ ≤ 4 * R
  · calc satCutoff R ‖z‖ * ‖z‖ ≤ 1 * ‖z‖ :=
        mul_le_mul_of_nonneg_right (satCutoff_le_one R ‖z‖) hz0
      _ ≤ 4 * R := by rw [one_mul]; exact h
  · have h4 : 4 * R ≤ ‖z‖ := (not_le.mp h).le
    rw [satCutoff_eq_zero hR h4, zero_mul]
    linarith

/-- **Estimate 1, geometric form.**  The radial saturation is bounded by `4 * R`. -/
theorem norm_satMap_le {R : ℝ} (hR : 0 < R) (z : E) : ‖satMap R z‖ ≤ 4 * R := by
  rw [satMap, norm_smul, Real.norm_eq_abs, abs_of_nonneg (satCutoff_nonneg R ‖z‖)]
  exact satCutoff_mul_norm_le hR z

/-- **Estimate 3 of the docstring.**  The key bound relating the cutoff of two radii: it is what
makes the saturated field Lipschitz in `z`.  The two branches are `‖z'‖ ≤ 4R` (where both values of
the cutoff are bounded by `1`) and `‖z'‖ ≥ 4R` (where the cutoff at `z'` vanishes and the cutoff at
`z` is controlled by `4R - ‖z‖`). -/
theorem satCutoff_sub_mul_norm_le {R : ℝ} (hR : 0 < R) (z z' : E) :
    |satCutoff R ‖z‖ - satCutoff R ‖z'‖| * ‖z'‖ ≤ (4 / 3) * ‖z - z'‖ := by
  by_cases h : ‖z'‖ ≤ 4 * R
  · have h1 : |satCutoff R ‖z‖ - satCutoff R ‖z'‖| ≤ |‖z‖ - ‖z'‖| / (3 * R) :=
      satCutoff_abs_sub_le hR _ _
    have h2 : |satCutoff R ‖z‖ - satCutoff R ‖z'‖| * ‖z'‖
        ≤ (|‖z‖ - ‖z'‖| / (3 * R)) * (4 * R) :=
      mul_le_mul h1 h (norm_nonneg z')
        (div_nonneg (abs_nonneg _) (by positivity))
    have h3 : (|‖z‖ - ‖z'‖| / (3 * R)) * (4 * R) = (4 / 3) * |‖z‖ - ‖z'‖| := by
      field_simp
    rw [h3] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le z z') (by norm_num))
  · have h4 : 4 * R ≤ ‖z'‖ := (not_le.mp h).le
    rw [satCutoff_eq_zero hR h4, sub_zero, abs_of_nonneg (satCutoff_nonneg R ‖z‖)]
    by_cases h5 : 4 * R ≤ ‖z‖
    · rw [satCutoff_eq_zero hR h5, zero_mul]
      positivity
    · have hzlt : ‖z‖ < 4 * R := not_le.mp h5
      have hz0 : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
      have hχ : satCutoff R ‖z‖ ≤ (4 * R - ‖z‖) / (3 * R) := by
        rw [satCutoff]
        exact max_le (div_nonneg (by linarith) (by positivity)) (min_le_right _ _)
      have hstep : satCutoff R ‖z‖ * ‖z'‖ ≤ ((4 * R - ‖z‖) / (3 * R)) * ‖z'‖ :=
        mul_le_mul_of_nonneg_right hχ (norm_nonneg z')
      have hkey : (4 * R - ‖z‖) * ‖z'‖ ≤ 4 * R * (‖z'‖ - ‖z‖) := by nlinarith
      have hfinal : ((4 * R - ‖z‖) / (3 * R)) * ‖z'‖ ≤ (4 / 3) * (‖z'‖ - ‖z‖) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      have hnorm : ‖z'‖ - ‖z‖ ≤ ‖z - z'‖ := by
        have := norm_sub_norm_le z' z
        rw [norm_sub_rev] at this
        linarith
      have : (4 / 3 : ℝ) * (‖z'‖ - ‖z‖) ≤ (4 / 3) * ‖z - z'‖ :=
        mul_le_mul_of_nonneg_left hnorm (by norm_num)
      exact hstep.trans (hfinal.trans this)

/-- **Estimate 4 of the docstring.**  The radial saturation is `3`-Lipschitz (its mean value
constant is `1 + 4/3`), which is what makes the saturated field Lipschitz on `ℝ × E`. -/
theorem satMap_lipschitzWith {R : ℝ} (hR : 0 < R) : LipschitzWith 3 (satMap (E := E) R) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro z z'
  push_cast
  rw [dist_eq_norm, dist_eq_norm]
  have hdecomp : satMap R z - satMap R z'
      = (satCutoff R ‖z‖) • (z - z') + (satCutoff R ‖z‖ - satCutoff R ‖z'‖) • z' := by
    rw [satMap, satMap, smul_sub, sub_smul]
    abel
  calc ‖satMap R z - satMap R z'‖
      = ‖(satCutoff R ‖z‖) • (z - z') + (satCutoff R ‖z‖ - satCutoff R ‖z'‖) • z'‖ := by
        rw [hdecomp]
    _ ≤ ‖(satCutoff R ‖z‖) • (z - z')‖ + ‖(satCutoff R ‖z‖ - satCutoff R ‖z'‖) • z'‖ :=
        norm_add_le _ _
    _ = |satCutoff R ‖z‖| * ‖z - z'‖ + |satCutoff R ‖z‖ - satCutoff R ‖z'‖| * ‖z'‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * ‖z - z'‖ + (4 / 3) * ‖z - z'‖ := by
        refine add_le_add ?_ (satCutoff_sub_mul_norm_le hR z z')
        rw [abs_of_nonneg (satCutoff_nonneg R ‖z‖)]
        exact mul_le_mul_of_nonneg_right (satCutoff_le_one R ‖z‖) (norm_nonneg _)
    _ = (7 / 3) * ‖z - z'‖ := by ring
    _ ≤ 3 * ‖z - z'‖ := by
        have := norm_nonneg (z - z')
        nlinarith

end RadialSaturation


section SaturatedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **saturated field** of a family `A` of linear maps: `X (t, z) = (1, χ (‖z‖) • A t z)` on
`ℝ × E`.  It is autonomous, globally bounded and Lipschitz, and on the ball `‖z‖ ≤ R` (where
`χ = 1`) it agrees with the linear field `(t, z) ↦ (1, A t z)`. -/
noncomputable def satField (A : ℝ → E →L[ℝ] E) (R : ℝ) (p : ℝ × E) : ℝ × E :=
  (1, (satCutoff R ‖p.2‖) • (A p.1 p.2))

/-- **Bound.**  The saturated field is bounded by `max 1 (4 * R * C)` when `‖A t‖ ≤ C`. -/
theorem norm_satField_le {A : ℝ → E →L[ℝ] E} {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hAb : ∀ t, ‖A t‖ ≤ C) (p : ℝ × E) :
    ‖satField A R p‖ ≤ max 1 (4 * R * C) := by
  rw [satField]
  show max ‖(1 : ℝ)‖ ‖(satCutoff R ‖p.2‖) • (A p.1 p.2)‖ ≤ max 1 (4 * R * C)
  rw [norm_one]
  refine max_le (le_max_left _ _) ?_
  calc ‖(satCutoff R ‖p.2‖) • (A p.1 p.2)‖
      = satCutoff R ‖p.2‖ * ‖A p.1 p.2‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (satCutoff_nonneg R _)]
    _ ≤ satCutoff R ‖p.2‖ * (C * ‖p.2‖) :=
        mul_le_mul_of_nonneg_left
          ((ContinuousLinearMap.le_opNorm (A p.1) p.2).trans
            (mul_le_mul_of_nonneg_right (hAb p.1) (norm_nonneg _)))
          (satCutoff_nonneg R _)
    _ = C * (satCutoff R ‖p.2‖ * ‖p.2‖) := by ring
    _ ≤ C * (4 * R) := mul_le_mul_of_nonneg_left (satCutoff_mul_norm_le hR p.2) hC
    _ ≤ max 1 (4 * R * C) := by
        rw [mul_comm C (4 * R)]
        exact le_max_right _ _

/-- **The `dist`-estimate.**  The saturated field is Lipschitz with constant `4 * C + 4 * R * LA`
(sharper: `(7 / 3) * C + 4 * R * LA`).  On the max-metric one only has
`A * a + B * b ≤ (A + B) * max a b`, so the constant is a *sum*, not a `max`.

The decomposition is chosen so that **every factor of `z'` is absorbed by estimate 3**:

`χ(‖z‖) • A t z - χ(‖z'‖) • A s z'
  = χ(‖z‖) • (A t z - A s z) + (χ(‖z‖) - χ(‖z'‖)) • A s z' + χ(‖z‖) • (A s (z - z'))`.

The first summand uses `χ(‖z‖) * ‖z‖ ≤ 4R` (same index as the cutoff!), the second is exactly
`satCutoff_sub_mul_norm_le`, the third is bounded by `C * ‖z - z'‖` since `χ ≤ 1`.  Decomposing
instead with the time-difference at `z'` does **not** work: the factor `‖z'‖` there is unbounded and
estimate 3 cannot absorb it. -/
theorem dist_satField_le {A : ℝ → E →L[ℝ] E} {R LA C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hLA : 0 ≤ LA) (hAb : ∀ t, ‖A t‖ ≤ C) (hAlip : ∀ t s, ‖A t - A s‖ ≤ LA * |t - s|)
    (p p' : ℝ × E) :
    dist (satField A R p) (satField A R p') ≤ (4 * C + 4 * R * LA) * dist p p' := by
  have hχ0 : (0:ℝ) ≤ satCutoff R ‖p.2‖ := satCutoff_nonneg R _
  have hχ1 : satCutoff R ‖p.2‖ ≤ 1 := satCutoff_le_one R _
  have hz'0 : (0:ℝ) ≤ ‖p'.2‖ := norm_nonneg _
  have hw : dist (satField A R p) (satField A R p')
      = ‖(satCutoff R ‖p.2‖) • (A p.1 p.2) - (satCutoff R ‖p'.2‖) • (A p'.1 p'.2)‖ := by
    rw [satField, satField, dist_eq_norm]
    show max ‖(1 : ℝ) - 1‖ ‖(satCutoff R ‖p.2‖) • (A p.1 p.2)
      - (satCutoff R ‖p'.2‖) • (A p'.1 p'.2)‖ = _
    rw [sub_self, norm_zero]
    exact le_antisymm (max_zero_le_self (norm_nonneg _)) (le_max_right _ _)
  have hp : dist p p' = max |p.1 - p'.1| ‖p.2 - p'.2‖ := by
    rw [dist_eq_norm]
    show max ‖p.1 - p'.1‖ ‖p.2 - p'.2‖ = max |p.1 - p'.1| ‖p.2 - p'.2‖
    rw [Real.norm_eq_abs]
  rw [hw, hp]
  have hdec : (satCutoff R ‖p.2‖) • (A p.1 p.2) - (satCutoff R ‖p'.2‖) • (A p'.1 p'.2)
      = (satCutoff R ‖p.2‖) • (A p.1 p.2 - A p'.1 p.2)
        + ((satCutoff R ‖p.2‖) - (satCutoff R ‖p'.2‖)) • (A p'.1 p'.2)
        + (satCutoff R ‖p.2‖) • (A p'.1 (p.2 - p'.2)) := by
    rw [map_sub, smul_sub, sub_smul, smul_sub]
    abel
  rw [hdec]
  have hAs : A p.1 p.2 - A p'.1 p.2 = (A p.1 - A p'.1) p.2 := by
    rw [ContinuousLinearMap.sub_apply]
  have hs1 : ‖(satCutoff R ‖p.2‖) • (A p.1 p.2 - A p'.1 p.2)‖
      ≤ (4 * R * LA) * |p.1 - p'.1| := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hχ0, hAs]
    calc satCutoff R ‖p.2‖ * ‖(A p.1 - A p'.1) p.2‖
        ≤ satCutoff R ‖p.2‖ * (LA * |p.1 - p'.1| * ‖p.2‖) :=
          mul_le_mul_of_nonneg_left
            ((ContinuousLinearMap.le_opNorm (A p.1 - A p'.1) p.2).trans
              (mul_le_mul_of_nonneg_right (hAlip p.1 p'.1) (norm_nonneg _))) hχ0
      _ = LA * |p.1 - p'.1| * (satCutoff R ‖p.2‖ * ‖p.2‖) := by ring
      _ ≤ LA * |p.1 - p'.1| * (4 * R) :=
          mul_le_mul_of_nonneg_left (satCutoff_mul_norm_le hR p.2)
            (mul_nonneg hLA (abs_nonneg _))
      _ = (4 * R * LA) * |p.1 - p'.1| := by ring
  have hs2 : ‖((satCutoff R ‖p.2‖) - (satCutoff R ‖p'.2‖)) • (A p'.1 p'.2)‖
      ≤ (3 * C) * ‖p.2 - p'.2‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |satCutoff R ‖p.2‖ - satCutoff R ‖p'.2‖| * ‖A p'.1 p'.2‖
        ≤ |satCutoff R ‖p.2‖ - satCutoff R ‖p'.2‖| * (C * ‖p'.2‖) :=
          mul_le_mul_of_nonneg_left
            ((ContinuousLinearMap.le_opNorm (A p'.1) p'.2).trans
              (mul_le_mul_of_nonneg_right (hAb p'.1) hz'0)) (abs_nonneg _)
      _ = C * (|satCutoff R ‖p.2‖ - satCutoff R ‖p'.2‖| * ‖p'.2‖) := by ring
      _ ≤ C * ((4 / 3) * ‖p.2 - p'.2‖) :=
          mul_le_mul_of_nonneg_left (satCutoff_sub_mul_norm_le hR p.2 p'.2) hC
      _ ≤ (3 * C) * ‖p.2 - p'.2‖ := by
          have := norm_nonneg (p.2 - p'.2)
          nlinarith
  have hs3 : ‖(satCutoff R ‖p.2‖) • (A p'.1 (p.2 - p'.2))‖ ≤ C * ‖p.2 - p'.2‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hχ0]
    calc satCutoff R ‖p.2‖ * ‖A p'.1 (p.2 - p'.2)‖
        ≤ satCutoff R ‖p.2‖ * (C * ‖p.2 - p'.2‖) :=
          mul_le_mul_of_nonneg_left
            ((ContinuousLinearMap.le_opNorm (A p'.1) (p.2 - p'.2)).trans
              (mul_le_mul_of_nonneg_right (hAb p'.1) (norm_nonneg _))) hχ0
      _ ≤ 1 * (C * ‖p.2 - p'.2‖) := mul_le_mul_of_nonneg_right hχ1 (by positivity)
      _ = C * ‖p.2 - p'.2‖ := by rw [one_mul]
  have hsplit : ‖(satCutoff R ‖p.2‖) • (A p.1 p.2 - A p'.1 p.2)
        + ((satCutoff R ‖p.2‖) - (satCutoff R ‖p'.2‖)) • (A p'.1 p'.2)
        + (satCutoff R ‖p.2‖) • (A p'.1 (p.2 - p'.2))‖
      ≤ (4 * R * LA) * |p.1 - p'.1| + (3 * C) * ‖p.2 - p'.2‖ + C * ‖p.2 - p'.2‖ := by
    have h1 := norm_add_le ((satCutoff R ‖p.2‖) • (A p.1 p.2 - A p'.1 p.2)
      + ((satCutoff R ‖p.2‖) - (satCutoff R ‖p'.2‖)) • (A p'.1 p'.2))
      ((satCutoff R ‖p.2‖) • (A p'.1 (p.2 - p'.2)))
    have h2 := norm_add_le ((satCutoff R ‖p.2‖) • (A p.1 p.2 - A p'.1 p.2))
      (((satCutoff R ‖p.2‖) - (satCutoff R ‖p'.2‖)) • (A p'.1 p'.2))
    linarith
  refine hsplit.trans ?_
  have h4C : (0:ℝ) ≤ 4 * C := by linarith
  have h4R : (0:ℝ) ≤ 4 * R * LA := by positivity
  have hA : (4 * C) * ‖p.2 - p'.2‖ ≤ (4 * C) * max |p.1 - p'.1| ‖p.2 - p'.2‖ :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) h4C
  have hB : (4 * R * LA) * |p.1 - p'.1|
      ≤ (4 * R * LA) * max |p.1 - p'.1| ‖p.2 - p'.2‖ :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) h4R
  have hL : (4 * R * LA) * |p.1 - p'.1| + (3 * C) * ‖p.2 - p'.2‖ + C * ‖p.2 - p'.2‖
      = (4 * R * LA) * |p.1 - p'.1| + (4 * C) * ‖p.2 - p'.2‖ := by ring
  have hR' : (4 * C) * max |p.1 - p'.1| ‖p.2 - p'.2‖
        + (4 * R * LA) * max |p.1 - p'.1| ‖p.2 - p'.2‖
      = (4 * C + 4 * R * LA) * max |p.1 - p'.1| ‖p.2 - p'.2‖ := by ring
  linarith

/-- **The saturated field is Lipschitz**, with the constant of `dist_satField_le`. -/
theorem lipschitzWith_satField {A : ℝ → E →L[ℝ] E} {R LA C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hLA : 0 ≤ LA) (hAb : ∀ t, ‖A t‖ ≤ C) (hAlip : ∀ t s, ‖A t - A s‖ ≤ LA * |t - s|) :
    LipschitzWith ⟨4 * C + 4 * R * LA, by positivity⟩ (satField A R) :=
  LipschitzWith.of_dist_le_mul (fun p p' =>
    dist_satField_le hR hC hLA hAb hAlip p p')

/-- **Existence of integral curves of the saturated field.**  This is
`Work.ODE.exists_isIntegralCurve_of_lipschitzWith` fed with `norm_satField_le` and
`lipschitzWith_satField`: the saturated field is autonomous, globally bounded and globally
Lipschitz, so it has global integral curves through every point. -/
theorem exists_isIntegralCurve_satField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {A : ℝ → E →L[ℝ] E} {R LA C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hLA : 0 ≤ LA) (hAb : ∀ t, ‖A t‖ ≤ C) (hAlip : ∀ t s, ‖A t - A s‖ ≤ LA * |t - s|)
    (y : ℝ × E) :
    ∃ γ : ℝ → ℝ × E, γ 0 = y ∧ IsIntegralCurve γ (fun _ z => satField A R z) :=
  exists_isIntegralCurve_of_lipschitzWith (satField A R)
    (L := ⟨4 * C + 4 * R * LA, by positivity⟩)
    (lipschitzWith_satField hR hC hLA hAb hAlip)
    (M := max 1 (4 * R * C)) (fun z => norm_satField_le hR hC hAb z) y

/-- **First coordinate of the graph step.**  An integral curve of the saturated field through a
point with vanishing first coordinate has first coordinate the identity: `(γ s).1 = s`.  This is the
`t' = 1`, `t 0 = 0` half of the `s ↦ (s, γ s)` reduction.

The derivative value is matched through the `Iff` form of `HasDerivAt`: `convert`/`rw` cannot reach
it, and the `toSpanSingleton` operator left by `convert` must be collapsed *as an operator* (its
argument is the `ℝ × E`-valued `satField A R (γ t)`, not its first component). -/
theorem fst_eq_of_isIntegralCurve_satField {A : ℝ → E →L[ℝ] E} {R : ℝ} {y : ℝ × E}
    {γ : ℝ → ℝ × E} (hγ : IsIntegralCurve γ (fun _ z => satField A R z)) (hγ0 : γ 0 = y)
    (hy : y.1 = 0) (s : ℝ) : (γ s).1 = s := by
  have hmain : ∀ t, HasDerivAt (fun t : ℝ => (γ t).1 - t) 0 t := by
    intro t
    have h1 := (hγ t).fst
    have h2 := h1.sub (hasDerivAt_id t)
    have hc : (ContinuousLinearMap.fst ℝ ℝ E).comp
          (ContinuousLinearMap.toSpanSingleton ℝ (satField A R (γ t)))
        - ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ)
        = ContinuousLinearMap.toSpanSingleton ℝ (0 : ℝ) := by
      ext x
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply, map_smul, one_smul, mul_one, mul_zero,
        show (ContinuousLinearMap.fst ℝ ℝ E) (satField A R (γ t)) = (satField A R (γ t)).1 from rfl,
        show (satField A R (γ t)).1 = 1 from rfl, sub_self]
    rw [hc] at h2
    exact h2
  have hdiff : Differentiable ℝ (fun t : ℝ => (γ t).1 - t) := fun t => (hmain t).differentiableAt
  have hf' : ∀ t, fderiv ℝ (fun t : ℝ => (γ t).1 - t) t = 0 := by
    intro t
    have := (hmain t).hasFDerivAt.fderiv
    simpa using this
  have hconst : (fun t : ℝ => (γ t).1 - t) 0 = (fun t : ℝ => (γ t).1 - t) s :=
    is_const_of_fderiv_eq_zero hdiff hf' 0 s
  simp only [hγ0, hy, sub_self] at hconst
  linarith

/-- **The curve is a graph over its parameter**: `γ s = (s, (γ s).2)`. -/
theorem eq_mk_snd_of_isIntegralCurve_satField {A : ℝ → E →L[ℝ] E} {R : ℝ} {y : ℝ × E}
    {γ : ℝ → ℝ × E} (hγ : IsIntegralCurve γ (fun _ z => satField A R z)) (hγ0 : γ 0 = y)
    (hy : y.1 = 0) (s : ℝ) : γ s = (s, (γ s).2) :=
  Prod.ext (fst_eq_of_isIntegralCurve_satField hγ hγ0 hy s) rfl

/-- **The second coordinate solves the saturated equation** `z' = χ (‖z‖) • A s z`.  Stated with the
raw value of the field first; the concrete form follows by collapsing the operator (see below). -/
theorem hasDerivAt_snd_of_isIntegralCurve_satField {A : ℝ → E →L[ℝ] E} {R : ℝ} {y : ℝ × E}
    {γ : ℝ → ℝ × E} (hγ : IsIntegralCurve γ (fun _ z => satField A R z)) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (γ t).2) (satField A R (γ s)).2 s :=
  (hγ s).snd

/-- **The second coordinate solves the saturated equation**, in the concrete form used by the
Gronwall estimate: the value `(satField A R (γ s)).2` is `χ (‖(γ s).2‖) • A s (γ s).2` once
`(γ s).1 = s` is substituted.  The value is matched through the operator, as in the graph step. -/
theorem hasDerivAt_snd_satField {A : ℝ → E →L[ℝ] E} {R : ℝ} {y : ℝ × E} {γ : ℝ → ℝ × E}
    (hγ : IsIntegralCurve γ (fun _ z => satField A R z)) (hγ0 : γ 0 = y) (hy : y.1 = 0) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (γ t).2) ((satCutoff R ‖(γ s).2‖) • (A s (γ s).2)) s := by
  have hfst := fst_eq_of_isIntegralCurve_satField hγ hγ0 hy s
  have hval : (satField A R (γ s)).2 = (satCutoff R ‖(γ s).2‖) • (A s (γ s).2) := by
    show (satCutoff R ‖(γ s).2‖) • (A (γ s).1 (γ s).2)
      = (satCutoff R ‖(γ s).2‖) • (A s (γ s).2)
    rw [hfst]
  exact hval ▸ hasDerivAt_snd_of_isIntegralCurve_satField (y := y) hγ s

/-- **The pointwise bound behind Gronwall.**  The right-hand side of the saturated equation is
bounded by `C * ‖z‖`: this is where `χ ≤ 1` and `‖A t‖ ≤ C` are used. -/
theorem norm_satCutoff_smul_le {A : ℝ → E →L[ℝ] E} {R C : ℝ} (hC : 0 ≤ C)
    (hAb : ∀ t, ‖A t‖ ≤ C) (s : ℝ) (z : E) :
    ‖(satCutoff R ‖z‖) • (A s z)‖ ≤ C * ‖z‖ := by
  calc ‖(satCutoff R ‖z‖) • (A s z)‖
      = satCutoff R ‖z‖ * ‖A s z‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (satCutoff_nonneg R _)]
    _ ≤ satCutoff R ‖z‖ * (C * ‖z‖) :=
        mul_le_mul_of_nonneg_left
          ((ContinuousLinearMap.le_opNorm (A s) z).trans
            (mul_le_mul_of_nonneg_right (hAb s) (norm_nonneg _)))
          (satCutoff_nonneg R _)
    _ ≤ 1 * (C * ‖z‖) :=
        mul_le_mul_of_nonneg_right (satCutoff_le_one R _) (by positivity)
    _ = C * ‖z‖ := by rw [one_mul]

/-! ### Gronwall: staged

Given `hz : ∀ s, HasDerivAt z ((satCutoff R ‖z s‖) • (A s (z s))) s`, `hC : 0 ≤ C` and
`‖A t‖ ≤ C`, the estimate to prove is

`‖z s‖ ≤ Real.exp (C * s) * ‖z 0‖`  for `0 ≤ s`.

Plan (comparison / antitone), now that `norm_satCutoff_smul_le` gives the pointwise bound:

* `f s := Real.exp (-(C * s)) * ‖z s‖` should be antitone on `Ici 0`, which is
  `antitoneOn_of_deriv_nonpos` applied on the interval `[0, s]`; equivalently (and avoiding the
  non-differentiability of `‖·‖` at `0`) use the squared norm
  `F s := Real.exp (-(2 * C * s)) * ‖z s‖ ^ 2` and show `deriv F ≤ 0` where `z s ≠ 0`, then
  `monotoneOn_of_deriv_nonneg`/`antitoneOn_of_deriv_nonpos` on `[0, s]`.
* the derivative of `‖z ·‖ ^ 2` is `2 * ⟪z s, (χ ‖z s‖) • (A s (z s))⟫` (Mathlib `HasDerivAt.inner`),
  bounded by `2 * ‖z s‖ * (C * ‖z s‖)` with `norm_satCutoff_smul_le`; the `exp` factor then makes
  `deriv F ≤ 0`.
* **Value-opacity warning (same as the graph step and the saturated equation):** the derivative value
  is opaque to `rw`/`convert`; transport facts with `▸`, and expose the definitional shape with
  `show` before rewriting.
* **Verified by `#check` (so the next attempt starts warm):** `HasDerivAt.norm_sq` **exists**
  (`HasDerivAt z z' t → HasDerivAt (fun t => ‖z t‖ ^ 2) (2 * ⟪z t, z'⟫_ℝ) t`) — so the derivative
  identity step is literally `(hz t).norm_sq`; `HasDerivAt.inner`, `antitoneOn_of_deriv_nonpos`,
  `monotoneOn_of_deriv_nonneg`, `Real.exp_le_exp` and `gronwallBound` all exist.
  `norm_le_gronwallBound_of_deriv_right_le_deriv_bound` does **not** exist in this revision (the name
  was a guess), so the direct comparison is the safer route than hunting Mathlib's Gronwall file.
* Syntax caution while writing `HasDerivAt.norm_sq`'s conclusion: the value
  `2 * ⟪z t, (satCutoff R ‖z t‖) • (A t (z t))⟫_ℝ` needs the inner-product notation with the `_ℝ`
  subscript and parenthesised arguments; a missing token there is a parse error, not a mathematical
  problem (that is what stopped the first probe).
-/

/-- **The derivative identity of the Gronwall comparison.**  For a solution `z` of the saturated
equation in a real inner product space `F`, the comparison function
`t ↦ exp ((-(2 * C)) * t) * ‖z t‖ ^ 2` has derivative
`exp ((-(2 * C)) * t) * (2 * ⟪z t, χ ‖z t‖ • A t (z t)⟫ - 2 * C * ‖z t‖ ^ 2)`.

Design points, each bought with a failed attempt: the space is a *fresh* `F` with
`InnerProductSpace ℝ F` (the section's `E` has only `NormedSpace`); the `exp` factor is built with
`HasDerivAt.const_mul` on `hasDerivAt_id` (`(hasDerivAt_const _).mul (hasDerivAt_id t)` produces a
value no rewrite can touch); and the trailing `one` in `const_mul`'s value is *not* normalized — it is
absorbed by the single `ring`-discharged identity `hval` and transported with `▸`. -/
theorem hasDerivAt_exp_mul_norm_sq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {A : ℝ → F →L[ℝ] F} {R C : ℝ} {z : ℝ → F}
    (hz : ∀ s, HasDerivAt z ((satCutoff R ‖z s‖) • (A s (z s))) s) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp ((-(2 * C)) * t) * ‖z t‖ ^ 2)
      (Real.exp ((-(2 * C)) * t) *
        (2 * inner ℝ (z t) ((satCutoff R ‖z t‖) • (A t (z t))) - 2 * C * ‖z t‖ ^ 2)) t := by
  have h1 : HasDerivAt (fun t : ℝ => ‖z t‖ ^ 2)
      (2 * inner ℝ (z t) ((satCutoff R ‖z t‖) • (A t (z t)))) t := (hz t).norm_sq
  have h3 : HasDerivAt (fun t : ℝ => (-(2 * C)) * t) (-(2 * C) * 1) t :=
    (hasDerivAt_id t).const_mul (-(2 * C))
  have h2 : HasDerivAt (fun t : ℝ => Real.exp ((-(2 * C)) * t))
      (Real.exp ((-(2 * C)) * t) * (-(2 * C) * 1)) t := h3.exp
  have h7 := h2.mul h1
  have hval : Real.exp ((-(2 * C)) * t) * (-(2 * C) * 1) * ‖z t‖ ^ 2
        + Real.exp ((-(2 * C)) * t) * (2 * inner ℝ (z t) ((satCutoff R ‖z t‖) • (A t (z t))))
      = Real.exp ((-(2 * C)) * t) *
        (2 * inner ℝ (z t) ((satCutoff R ‖z t‖) • (A t (z t))) - 2 * C * ‖z t‖ ^ 2) := by
    ring
  exact hval ▸ h7

/-- **The sign estimate behind the Gronwall comparison.**  The inner product of `z` against the
saturated right-hand side is at most `C * ‖z‖ ^ 2`: this is what makes the derivative of the
comparison function non-positive. -/
theorem inner_satCutoff_smul_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {A : ℝ → F →L[ℝ] F} {R C : ℝ} (hC : 0 ≤ C) (hAb : ∀ t, ‖A t‖ ≤ C) (s : ℝ) (z : F) :
    inner ℝ z ((satCutoff R ‖z‖) • (A s z)) ≤ C * ‖z‖ ^ 2 := by
  calc inner ℝ z ((satCutoff R ‖z‖) • (A s z))
      ≤ ‖z‖ * ‖(satCutoff R ‖z‖) • (A s z)‖ := real_inner_le_norm _ _
    _ ≤ ‖z‖ * (C * ‖z‖) :=
        mul_le_mul_of_nonneg_left (norm_satCutoff_smul_le hC hAb s z) (norm_nonneg _)
    _ = C * ‖z‖ ^ 2 := by ring

/-- **The comparison function has non-positive derivative.**  Directly from
`hasDerivAt_exp_mul_norm_sq` and the sign estimate `inner_satCutoff_smul_le`. -/
theorem deriv_exp_mul_norm_sq_nonpos {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {A : ℝ → F →L[ℝ] F} {R C : ℝ} (hC : 0 ≤ C) (hAb : ∀ t, ‖A t‖ ≤ C) {z : ℝ → F}
    (hz : ∀ s, HasDerivAt z ((satCutoff R ‖z s‖) • (A s (z s))) s) (t : ℝ) :
    deriv (fun t : ℝ => Real.exp ((-(2 * C)) * t) * ‖z t‖ ^ 2) t ≤ 0 := by
  rw [(hasDerivAt_exp_mul_norm_sq hz t).deriv]
  have hb : inner ℝ (z t) ((satCutoff R ‖z t‖) • (A t (z t))) ≤ C * ‖z t‖ ^ 2 :=
    inner_satCutoff_smul_le hC hAb t (z t)
  have hexp : 0 < Real.exp ((-(2 * C)) * t) := Real.exp_pos _
  nlinarith [hb, hexp, sq_nonneg ‖z t‖]

/-! ### The antitone step and the square-root step (final assembly)

Everything is now in place; the remaining work is assembly, and it splits cleanly:

1. **Continuity of the comparison function** `t ↦ Real.exp ((-(2 * C)) * t) * ‖z t‖ ^ 2`:
   `hz : ∀ s, HasDerivAt z … s` gives `Continuous z` by
   `continuous_iff_continuousAt.mpr (fun t => (hz t).continuousAt)`, then
   `(Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul (h.norm.pow 2)`.
2. **Antitone**: `#check`ed, so no guessing is needed.  In this revision

   `antitoneOn_of_deriv_nonpos : Convex ℝ D → ContinuousOn f D → DifferentiableOn ℝ f (interior D)
     → (∀ x ∈ interior D, deriv f x ≤ 0) → AntitoneOn f D`

   — i.e. it wants the **interior** hypothesis (and a `DifferentiableOn` on the interior).  So take
   `D := Icc 0 s` (`convex_Icc`), continuity from point 1, `DifferentiableOn ℝ f (interior D)` from
   the pointwise `HasDerivAt` (or `differentiableOn_of_hasDerivAt`), and the derivative hypothesis
   from `deriv_exp_mul_norm_sq_nonpos` restricted along `interior_subset`.
   Also `#check`ed: `Real.sqrt_sq : 0 ≤ x → √(x ^ 2) = x`, `Real.sqrt_le_sqrt : x ≤ y → √x ≤ √y`,
   `Continuous.norm`, `Continuous.pow` (all exist under those names).
3. Consequently `F s ≤ F 0`, i.e. `Real.exp ((-(2 * C)) * s) * ‖z s‖ ^ 2 ≤ ‖z 0‖ ^ 2` (using
   `hs : 0 ≤ s` for both endpoints in `Icc 0 s` and `Real.exp_zero`, `one_mul` at `0`).
4. **Square root step** (pure real algebra, no derivatives):
   from (3), `‖z s‖ ^ 2 ≤ (Real.exp (C * s) * ‖z 0‖) ^ 2` because
   `Real.exp ((C * s) + (C * s)) * Real.exp (-(2 * C) * s) = 1`; then `Real.sqrt_le_sqrt` with
   `Real.sqrt_sq (norm_nonneg _)` gives `‖z s‖ ≤ Real.exp (C * s) * ‖z 0‖`.
5. Then `R ≥ Real.exp C * (‖y‖ + 1)` (with `‖z 0‖ = ‖y.2‖ ≤ ‖y‖`) makes `χ = 1` on the window via
   `satCutoff_eq_one`, and the equation becomes the plain linear one
   `z' = A s z` — the handover to the FRAME brick.

No piece of this needs the inner-product structure except (1)–(3), which are already stated over
`{F} [InnerProductSpace ℝ F]`.
-/

/-! ### Point 1 of the assembly: continuity (shape known, one instance snag)

`Continuous z` from `∀ s, HasDerivAt z (v s) s` is one line:
`continuous_iff_continuousAt.mpr fun t => (hz t).continuousAt` — that part is fine.

For `Continuous (fun t : ℝ => Real.exp ((-(2 * C)) * t) * ‖z t‖ ^ 2)` the shape
`(Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul (hz.norm.pow 2)` **failed to
synthesize an instance** at the `.pow` step (`Continuous.pow` needs `[Monoid M] [ContinuousMul M]`
and the `Monoid` instance on the *function* type is the one being picked up, not `ℝ`'s).  Cheapest
fixes, in order:
* `fun_prop` on the whole goal (most likely to just work, and `Hz.norm` is not needed);
* or state it as `(Real.continuous_exp.comp …).mul (by fun_prop : Continuous fun t => ‖z t‖ ^ 2)`;
* or `Continuous.pow (hz.norm) 2` with `M := ℝ` given explicitly:
  `(hz.norm.pow 2 : Continuous fun t : ℝ => ‖z t‖ ^ 2)`.
Everything else in the assembly is unchanged; `Continuous.norm` and `Continuous.pow` both exist
(verified by `#check`).
-/

end SaturatedField

end Work.ODE
