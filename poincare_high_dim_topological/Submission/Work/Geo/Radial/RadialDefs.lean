import Mathlib
import Submission.Work.Geo.Radial.Basic

/-!
# Vocabulary for the sup-norm radial push in `ℝⁿ`

This file owns the two ingredients of the sup-norm radial push used by
`Work.Geo.Radial.exists_radial_push`:

* `radRho x = max_i |x i|`, the sup-norm radius of `x : ℝⁿ` (the radius of the sup-norm
  cube `Work.Geo.Radial.ocubeAround 0 r`);
* the one-parameter family of `1`-dimensional stretches
  `radStretch ε R S s t = t + s (R - ε) radTent ε S t`, where `radTent` is the tent profile
  rising linearly from `0` to `1` on `[0, ε]` and falling back to `0` on `[ε, S]`.

Applying the `1`-dimensional stretch to the sup-norm radius gives a self-map of `ℝⁿ`
(`radPush`) and its inverse (`radPushInv`); these are the building blocks of the family of
homeomorphisms requested by `exists_radial_push`.
-/

open Set Metric
open scoped Topology

namespace Work.Geo.Radial

/-- The sup-norm radius of a point of `ℝⁿ`: the largest absolute value of a coordinate. -/
noncomputable def radRho {n : ℕ} [NeZero n] (x : PL.E n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i : Fin n => |x i|

/-- The tent profile of the radial push: it rises linearly from `0` to `1` on `[0, ε]`,
falls linearly back to `0` on `[ε, S]`, and vanishes outside `[0, S]`. -/
noncomputable def radTent (ε S t : ℝ) : ℝ := max 0 (min (t / ε) ((S - t) / (S - ε)))

/-- The one-dimensional radial stretch `t ↦ t + s (R - ε) radTent ε S t`. -/
noncomputable def radStretch (ε R S s t : ℝ) : ℝ := t + s * (R - ε) * radTent ε S t

/-- The inverse of the one-dimensional stretch, as a plain function. -/
noncomputable def radStretchInv (ε R S s : ℝ) : ℝ → ℝ :=
  Function.invFun (radStretch ε R S s)

/-- The radial push of `ℝⁿ`: scale `x` by `radStretch (radRho x) / radRho x`. -/
noncomputable def radPush {n : ℕ} [NeZero n] (ε R S s : ℝ) (x : PL.E n) : PL.E n :=
  (radStretch ε R S s (radRho x) / radRho x) • x

/-- The inverse of the radial push. -/
noncomputable def radPushInv {n : ℕ} [NeZero n] (ε R S s : ℝ) (y : PL.E n) : PL.E n :=
  (radStretchInv ε R S s (radRho y) / radRho y) • y

/-! ## The tent profile -/

theorem radTent_nonneg (ε S t : ℝ) : 0 ≤ radTent ε S t := le_max_left _ _

theorem radTent_of_nonpos {ε S t : ℝ} (hε : 0 < ε) (ht : t ≤ 0) : radTent ε S t = 0 := by
  rw [radTent, max_eq_left]
  exact (min_le_left _ _).trans (div_nonpos_of_nonpos_of_nonneg ht hε.le)

theorem radTent_of_ge {ε S t : ℝ} (hεS : ε < S) (ht : S ≤ t) : radTent ε S t = 0 := by
  rw [radTent, max_eq_left]
  exact (min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

theorem radTent_of_le {ε S t : ℝ} (hε : 0 < ε) (hεS : ε < S) (h0 : 0 ≤ t) (ht : t ≤ ε) :
    radTent ε S t = t / ε := by
  rw [radTent, min_eq_left, max_eq_right (div_nonneg h0 hε.le)]
  rw [div_le_div_iff₀ hε (by linarith : (0:ℝ) < S - ε)]
  nlinarith

theorem radTent_of_between {ε S t : ℝ} (hε : 0 < ε) (hεS : ε < S) (hεt : ε ≤ t)
    (htS : t ≤ S) : radTent ε S t = (S - t) / (S - ε) := by
  rw [radTent, min_eq_right, max_eq_right (div_nonneg (by linarith) (by linarith))]
  rw [div_le_div_iff₀ (by linarith : (0:ℝ) < S - ε) hε]
  nlinarith

theorem radTent_eps {ε S : ℝ} (hε : 0 < ε) (hεS : ε < S) : radTent ε S ε = 1 := by
  rw [radTent, div_self hε.ne', div_self (by linarith : S - ε ≠ 0), min_self,
    max_eq_right zero_le_one]

theorem radTent_le_one {ε S t : ℝ} (hε : 0 < ε) (hεS : ε < S) : radTent ε S t ≤ 1 := by
  rcases le_or_gt t 0 with ht | ht
  · rw [radTent_of_nonpos hε ht]; norm_num
  rcases le_or_gt t ε with htε | hεt
  · rw [radTent_of_le hε hεS ht.le htε, div_le_one hε]; exact htε
  rcases le_or_gt t S with htS | hSt
  · rw [radTent_of_between hε hεS hεt.le htS, div_le_one (by linarith : (0:ℝ) < S - ε)]
    linarith
  · rw [radTent_of_ge hεS hSt.le]; norm_num

/-- The tent profile decreases at rate at most `1 / (S - ε)`. -/
theorem radTent_sub_le {ε S : ℝ} (hε : 0 < ε) (hεS : ε < S) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    radTent ε S t₁ - radTent ε S t₂ ≤ (t₂ - t₁) / (S - ε) := by
  have hS0 : (0:ℝ) < S := by linarith
  have hSε : (0:ℝ) < S - ε := by linarith
  have hd : 0 ≤ (t₂ - t₁) / (S - ε) := div_nonneg (by linarith) hSε.le
  rcases le_or_gt t₂ 0 with h₂ | h₂
  · rw [radTent_of_nonpos hε h₂, radTent_of_nonpos hε (le_trans h h₂), sub_zero]
    exact hd
  rcases le_or_gt t₁ 0 with h₁ | h₁
  · rw [radTent_of_nonpos hε h₁]
    linarith [radTent_nonneg ε S t₂, hd]
  rcases le_or_gt t₁ ε with h₁ε | hε₁
  · -- 0 < t₁ ≤ ε
    rw [radTent_of_le hε hεS h₁.le h₁ε]
    have ht1 : t₁ / ε ≤ 1 := by rw [div_le_one hε]; exact h₁ε
    rcases le_or_gt t₂ ε with h₂ε | hε₂
    · -- t₂ ≤ ε
      rw [radTent_of_le hε hεS h₂.le h₂ε]
      have hmono : t₁ / ε ≤ t₂ / ε := by
        rw [div_le_div_iff₀ hε hε]
        exact mul_le_mul_of_nonneg_right h hε.le
      linarith
    rcases le_or_gt t₂ S with h₂S | hS₂
    · -- ε < t₂ ≤ S
      rw [radTent_of_between hε hεS hε₂.le h₂S]
      have h3 : (1:ℝ) - (S - t₂) / (S - ε) = (t₂ - ε) / (S - ε) := by
        field_simp
        ring
      have h4 : (t₂ - ε) / (S - ε) ≤ (t₂ - t₁) / (S - ε) := by
        rw [div_le_div_iff₀ hSε hSε]
        exact mul_le_mul_of_nonneg_right (by linarith) hSε.le
      linarith
    · -- S < t₂
      rw [radTent_of_ge hεS hS₂.le]
      have hp1 : t₁ * S ≤ ε * S := mul_le_mul_of_nonneg_right h₁ε hS0.le
      have hp2 : ε * S ≤ ε * t₂ := mul_le_mul_of_nonneg_left hS₂.le hε.le
      have h5 : t₁ / ε ≤ (t₂ - t₁) / (S - ε) := by
        rw [div_le_div_iff₀ hε hSε]
        nlinarith
      linarith
  · -- ε < t₁
    rcases le_or_gt S t₁ with hS₁ | h₁S
    · rw [radTent_of_ge hεS hS₁, radTent_of_ge hεS (le_trans hS₁ h), sub_zero]
      exact hd
    -- ε < t₁ < S
    rw [radTent_of_between hε hεS hε₁.le h₁S.le]
    rcases le_or_gt t₂ S with h₂S | hS₂
    · -- t₂ ≤ S
      rw [radTent_of_between hε hεS (le_trans hε₁.le h) h₂S, ← sub_div,
        show S - t₁ - (S - t₂) = t₂ - t₁ by ring]
    · -- S < t₂
      rw [radTent_of_ge hεS hS₂.le]
      have h5 : (S - t₁) / (S - ε) ≤ (t₂ - t₁) / (S - ε) := by
        rw [div_le_div_iff₀ hSε hSε]
        exact mul_le_mul_of_nonneg_right (by linarith) hSε.le
      linarith

/-! ## The one-dimensional stretch -/

theorem radStretch_continuous (ε R S : ℝ) :
    Continuous fun p : ℝ × ℝ => radStretch ε R S p.1 p.2 := by
  unfold radStretch radTent
  fun_prop

theorem radStretch_zero_s (ε R S t : ℝ) : radStretch ε R S 0 t = t := by
  simp [radStretch]

theorem radTent_zero (ε S : ℝ) : radTent ε S 0 = 0 := by
  rw [radTent, zero_div]
  exact max_eq_left (min_le_left _ _)

theorem radStretch_at_zero (ε R S s : ℝ) : radStretch ε R S s 0 = 0 := by
  rw [radStretch, radTent_zero]
  ring

theorem radStretch_ge_self {ε R S s t : ℝ} (hs : 0 ≤ s) (hεR : ε ≤ R) :
    t ≤ radStretch ε R S s t := by
  have : 0 ≤ s * (R - ε) * radTent ε S t :=
    mul_nonneg (mul_nonneg hs (by linarith)) (radTent_nonneg _ _ _)
  simp only [radStretch]; linarith

theorem radStretch_of_ge {ε R S s t : ℝ} (hεS : ε < S) (ht : S ≤ t) :
    radStretch ε R S s t = t := by
  rw [radStretch, radTent_of_ge hεS ht]; ring

theorem radStretch_S {ε R S s : ℝ} (hεS : ε < S) : radStretch ε R S s S = S :=
  radStretch_of_ge hεS le_rfl

theorem radStretch_eps {ε R S : ℝ} (hε : 0 < ε) (hεS : ε < S) :
    radStretch ε R S 1 ε = R := by
  rw [radStretch, radTent_eps hε hεS]; ring

theorem radStretch_nonneg {ε R S s t : ℝ} (hs : 0 ≤ s) (hεR : ε ≤ R) (ht : 0 ≤ t) :
    0 ≤ radStretch ε R S s t := le_trans ht (radStretch_ge_self hs hεR)

/-- For `0 ≤ s ≤ 1` the radial stretch grows at most like `t ↦ (R / ε) t`. -/
theorem radStretch_le_mul {ε R S s t : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) (hεS : ε < S)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) :
    radStretch ε R S s t ≤ (R / ε) * t := by
  have hR : 0 < R := lt_of_lt_of_le hε hεR
  have hRε : 0 ≤ R - ε := by linarith
  have hg : radTent ε S t ≤ 1 := radTent_le_one hε hεS
  have hcoef : s * (R - ε) ≤ R - ε := by
    calc s * (R - ε) ≤ 1 * (R - ε) := by
          exact mul_le_mul_of_nonneg_right hs1 hRε
      _ = R - ε := one_mul _
  have hcoef0 : 0 ≤ s * (R - ε) := mul_nonneg hs0 hRε
  have hmain : s * (R - ε) * radTent ε S t ≤ R - ε := by
    calc s * (R - ε) * radTent ε S t ≤ s * (R - ε) * 1 := by
          exact mul_le_mul_of_nonneg_left hg hcoef0
      _ = s * (R - ε) := mul_one _
      _ ≤ R - ε := hcoef
  rcases le_or_gt t ε with htε | hεt
  · rw [radStretch, radTent_of_le hε hεS ht htε]
    have : t + s * (R - ε) * (t / ε) ≤ t + (R - ε) * (t / ε) := by
      have : s * (R - ε) * (t / ε) ≤ (R - ε) * (t / ε) := by
        apply mul_le_mul_of_nonneg_right hcoef
        exact div_nonneg ht hε.le
      linarith
    refine le_trans this ?_
    have h2 : t + (R - ε) * (t / ε) = (R / ε) * t := by
      field_simp
      ring
    rw [h2]
  · rw [radStretch]
    have h1 : t + s * (R - ε) * radTent ε S t ≤ t + (R - ε) := by linarith
    refine le_trans h1 ?_
    have h2 : (R / ε) * t - (t + (R - ε)) = (R - ε) * (t - ε) / ε := by
      field_simp; ring
    have h3 : 0 ≤ (R / ε) * t - (t + (R - ε)) := by
      rw [h2]; exact div_nonneg (mul_nonneg hRε (by linarith)) hε.le
    linarith

end Work.Geo.Radial
