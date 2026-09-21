import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.RCLike.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit

open Set
open scoped BigOperators Convex

namespace Commons.Geometry.Ulam

private lemma upper_left {a b m x : ℝ} {f : ℝ → ℝ}
    (hmb : m < b) (hxm : x ≤ m) (hx_mem : x ∈ Icc a b)
    (_hb_mem : b ∈ Icc a b)
    (hmid : m - a = b - m)
    (hconc : (b - m) / (b - x) * f x + (m - x) / (b - x) * f b ≤ f m) :
    f x ≤ 2 * |f m| + |f b| := by
  let A := b - m
  let B := m - x
  let D := b - x
  have hApos : 0 < A := by dsimp [A]; linarith
  have hBnonneg : 0 ≤ B := by dsimp [B]; linarith
  have hDpos : 0 < D := by dsimp [D]; linarith [hmb, hxm]
  have hlin : A * f x + B * f b ≤ D * f m := by
    have h_eq : A * f x + B * f b = D * (A / D * f x + B / D * f b) := by
      field_simp [hDpos.ne']
    calc
      A * f x + B * f b = D * (A / D * f x + B / D * f b) := h_eq
      _ ≤ D * f m := by
        dsimp [A, B, D] at hconc ⊢
        exact mul_le_mul_of_nonneg_left hconc hDpos.le
  have hbound : A * f x ≤ D * |f m| + B * |f b| := by
    have hfm : D * f m ≤ D * |f m| := by
      exact mul_le_mul_of_nonneg_left (le_abs_self (f m)) hDpos.le
    have hfb : B * f b ≤ B * |f b| := by
      exact mul_le_mul_of_nonneg_left (le_abs_self (f b)) hBnonneg
    have hfb' : - B * f b ≤ B * |f b| := by
      have : -f b ≤ |f b| := neg_le_abs (f b)
      have h := mul_le_mul_of_nonneg_left this hBnonneg
      nlinarith
    nlinarith
  have hD_le : D ≤ 2 * A := by
    dsimp [A, D]
    nlinarith [hx_mem.1, hmid]
  have hB_le : B ≤ A := by
    dsimp [A, B]
    nlinarith [hx_mem.1, hmid]
  have hmain : A * f x ≤ A * (2 * |f m| + |f b|) := by
    have h1 : D * |f m| ≤ (2 * A) * |f m| := mul_le_mul_of_nonneg_right hD_le (abs_nonneg _)
    have h2 : B * |f b| ≤ A * |f b| := mul_le_mul_of_nonneg_right hB_le (abs_nonneg _)
    nlinarith
  have : f x ≤ 2 * |f m| + |f b| := by
    nlinarith [hmain, hApos]
  exact this

private lemma upper_right {a b m x : ℝ} {f : ℝ → ℝ}
    (hma : a < m) (hmx : m ≤ x) (hx_mem : x ∈ Icc a b)
    (_ha_mem : a ∈ Icc a b)
    (hmid : m - a = b - m)
    (hconc : (x - m) / (x - a) * f a + (m - a) / (x - a) * f x ≤ f m) :
    f x ≤ 2 * |f m| + |f a| := by
  let A := m - a
  let B := x - m
  let D := x - a
  have hApos : 0 < A := by dsimp [A]; linarith
  have hBnonneg : 0 ≤ B := by dsimp [B]; linarith
  have hDpos : 0 < D := by dsimp [D]; linarith [hma, hmx]
  have hlin : A * f x + B * f a ≤ D * f m := by
    have h_eq : A * f x + B * f a = D * (A / D * f x + B / D * f a) := by
      field_simp [hDpos.ne']
    calc
      A * f x + B * f a = D * (A / D * f x + B / D * f a) := h_eq
      _ ≤ D * f m := by
        dsimp [A, B, D] at hconc ⊢
        nlinarith [mul_le_mul_of_nonneg_left hconc hDpos.le]
  have hbound : A * f x ≤ D * |f m| + B * |f a| := by
    have hfm : D * f m ≤ D * |f m| := by
      exact mul_le_mul_of_nonneg_left (le_abs_self (f m)) hDpos.le
    have hfa : B * f a ≤ B * |f a| := by
      exact mul_le_mul_of_nonneg_left (le_abs_self (f a)) hBnonneg
    have hfa' : - B * f a ≤ B * |f a| := by
      have : -f a ≤ |f a| := neg_le_abs (f a)
      have h := mul_le_mul_of_nonneg_left this hBnonneg
      nlinarith
    nlinarith
  have hD_le : D ≤ 2 * A := by
    dsimp [A, D]
    nlinarith [hx_mem.2, hmid]
  have hB_le : B ≤ A := by
    dsimp [A, B]
    nlinarith [hx_mem.2, hmid]
  have hmain : A * f x ≤ A * (2 * |f m| + |f a|) := by
    have h1 : D * |f m| ≤ (2 * A) * |f m| := mul_le_mul_of_nonneg_right hD_le (abs_nonneg _)
    have h2 : B * |f a| ≤ A * |f a| := mul_le_mul_of_nonneg_right hB_le (abs_nonneg _)
    nlinarith
  have : f x ≤ 2 * |f m| + |f a| := by
    nlinarith [hmain, hApos]
  exact this

lemma concaveOn_Icc_bounded {a b : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hf : ConcaveOn ℝ (Set.Icc a b) f) :
    Bornology.IsBounded (f '' Set.Icc a b) := by
  rcases lt_or_eq_of_le hab with hab_lt | rfl
  · let m := (a + b) / 2
    have hma : a < m := by dsimp [m]; linarith
    have hmb : m < b := by dsimp [m]; linarith
    have hmid : m - a = b - m := by dsimp [m]; ring
    have ha_mem : a ∈ Set.Icc a b := ⟨le_rfl, hab_lt.le⟩
    have hb_mem : b ∈ Set.Icc a b := ⟨hab_lt.le, le_rfl⟩
    have hm_mem : m ∈ Set.Icc a b := ⟨hma.le, hmb.le⟩
    let U := max (2 * |f m| + |f a|) (2 * |f m| + |f b|)
    let L := min (f a) (f b)
    have h_lower : ∀ x ∈ Set.Icc a b, L ≤ f x := by
      intro x hx
      have hxseg : x ∈ [a -[ℝ] b] := by
        rw [segment_eq_Icc hab_lt.le]
        exact hx
      dsimp [L]
      exact ConcaveOn.min_le_of_mem_segment hf ha_mem hb_mem hxseg
    have h_upper : ∀ x ∈ Set.Icc a b, f x ≤ U := by
      intro x hx
      rcases le_total x m with hxm | hmx
      · have hx_lt_b : x < b := lt_of_le_of_lt hxm hmb
        have hden : b - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx_lt_b)
        have hsum : (b - m) / (b - x) + (m - x) / (b - x) = 1 := by
          field_simp [hden]
          ring
        have hcombo : (b - m) / (b - x) * x + (m - x) / (b - x) * b = m := by
          field_simp [hden]
          ring
        have hnonneg1 : 0 ≤ (b - m) / (b - x) :=
          div_nonneg (sub_nonneg.mpr hmb.le) (sub_pos.mpr hx_lt_b).le
        have hnonneg2 : 0 ≤ (m - x) / (b - x) :=
          div_nonneg (sub_nonneg.mpr hxm) (sub_pos.mpr hx_lt_b).le
        have hconc0 := hf.2 hx hb_mem hnonneg1 hnonneg2 hsum
        have hconc : (b - m) / (b - x) * f x + (m - x) / (b - x) * f b ≤ f m := by
          simpa [hcombo] using hconc0
        have hx_upper := upper_left hmb hxm hx hb_mem hmid hconc
        dsimp [U]
        exact le_trans hx_upper (le_max_right _ _)
      · have ha_lt_x : a < x := lt_of_lt_of_le hma hmx
        have hden : x - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt ha_lt_x)
        have hsum : (x - m) / (x - a) + (m - a) / (x - a) = 1 := by
          field_simp [hden]
          ring
        have hcombo : (x - m) / (x - a) * a + (m - a) / (x - a) * x = m := by
          field_simp [hden]
          ring
        have hnonneg1 : 0 ≤ (x - m) / (x - a) :=
          div_nonneg (sub_nonneg.mpr hmx) (sub_pos.mpr ha_lt_x).le
        have hnonneg2 : 0 ≤ (m - a) / (x - a) :=
          div_nonneg (sub_nonneg.mpr hma.le) (sub_pos.mpr ha_lt_x).le
        have hconc0 := hf.2 ha_mem hx hnonneg1 hnonneg2 hsum
        have hconc : (x - m) / (x - a) * f a + (m - a) / (x - a) * f x ≤ f m := by
          simpa [hcombo] using hconc0
        have hx_upper := upper_right hma hmx hx ha_mem hmid hconc
        dsimp [U]
        exact le_trans hx_upper (le_max_left _ _)
    have hbounded : Bornology.IsBounded (f '' Set.Icc a b) := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨max |L| |U|, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      have hx_lower := h_lower x hx
      have hx_upper := h_upper x hx
      have hx_abs : |f x| ≤ max |L| |U| := by
        rw [abs_le]
        constructor
        · have hL_abs_lower : - |L| ≤ L := neg_abs_le L
          have hmax_neg_le : - max |L| |U| ≤ - |L| := by
            exact neg_le_neg (le_max_left _ _)
          exact le_trans hmax_neg_le (le_trans hL_abs_lower hx_lower)
        · have hU_abs_upper : U ≤ |U| := le_abs_self U
          exact le_trans hx_upper (le_trans hU_abs_upper (le_max_right _ _))
      exact hx_abs
    exact hbounded
  · have hIcc : Set.Icc a a = {a} := by
      ext x
      simp [le_antisymm_iff]
    rw [hIcc]
    simp

end Commons.Geometry.Ulam