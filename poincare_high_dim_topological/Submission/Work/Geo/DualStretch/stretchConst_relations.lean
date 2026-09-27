import Mathlib
import Submission.Work.Geo.DualStretch.const_defs
import Submission.Work.Geo.DualStretch.stretch_defs
import Submission.Work.Geo.DualStretch.massG_api
import Submission.Work.Geo.DualStretch.Basic

open Set Metric
open scoped Classical

namespace Work.Geo.DualStretch

open _root_.PL (E Cx)

variable {n : ℕ}

/-! ### Elementary API for `cands`, `posCands` and the mass decomposition -/

private lemma mem_cands {P : Cx n} {hP : P.faces.Finite} {τ : Finset (E n)} :
    τ ∈ cands P hP ↔ ∃ σ ∈ P.faces, τ ⊆ σ := by
  rw [cands, Finset.mem_biUnion]
  constructor
  · rintro ⟨σ, hσ, hτ⟩
    exact ⟨σ, (Set.Finite.mem_toFinset hP).mp hσ, Finset.mem_powerset.mp hτ⟩
  · rintro ⟨σ, hσ, hτ⟩
    exact ⟨σ, (Set.Finite.mem_toFinset hP).mpr hσ, Finset.mem_powerset.mpr hτ⟩

private lemma massG_nonneg (P : Cx n) (hP : P.faces.Finite) (x : E n) (τ : Finset (E n)) :
    0 ≤ massG P hP x τ := le_max_left _ _

/-- Off the level sets of positive mass of `x` (but inside `cands`) the mass of `x` vanishes. -/
private lemma massG_eq_zero_of_not_mem_posCands (P : Cx n) (hP : P.faces.Finite) {x : E n}
    {τ : Finset (E n)} (hτc : τ ∈ cands P hP) (h : τ ∉ posCands P hP x) :
    massG P hP x τ = 0 := by
  have hnn := massG_nonneg P hP x τ
  have hle : ¬ 0 < massG P hP x τ := fun hpos => h (Finset.mem_filter.mpr ⟨hτc, hpos⟩)
  linarith

/-! ### The total high mass of a point of `P.space` -/

private theorem SOf_nonneg {β : ℝ} {p : ℕ} (P : Cx n) (hP : P.faces.Finite) (x : E n) :
    0 ≤ SOf β p P hP x := by
  rw [SOf]
  exact Finset.sum_nonneg (fun τ _ => by
    by_cases hL : LowFace β p τ
    · rw [if_pos hL]
    · rw [if_neg hL]; exact massG_nonneg P hP x τ)

private theorem SOf_le_one {β : ℝ} {p : ℕ} (P : Cx n) (hP : P.faces.Finite) {x : E n}
    (hx : x ∈ P.space) : SOf β p P hP x ≤ 1 := by
  have h1 : SOf β p P hP x ≤ ∑ τ ∈ cands P hP, massG P hP x τ := by
    rw [SOf]
    exact Finset.sum_le_sum (fun τ _ => by
      by_cases hL : LowFace β p τ
      · rw [if_pos hL]; exact massG_nonneg P hP x τ
      · rw [if_neg hL])
  calc SOf β p P hP x ≤ ∑ τ ∈ cands P hP, massG P hP x τ := h1
    _ = 1 := (massG_api P hP hx).2.1

/-- The renormalisation factor `denC` of the constant-factor stretch is positive. -/
private theorem denC_pos {β : ℝ} {p : ℕ} (P : Cx n) (hP : P.faces.Finite) {m : ℝ} (hm : 0 < m)
    {x : E n} (hs0 : 0 ≤ SOf β p P hP x) (hs1 : SOf β p P hP x ≤ 1) :
    0 < denC β p P hP m x := by
  rw [denC]
  by_cases h : (1 : ℝ) ≤ m
  · have h2 : 0 ≤ (m - 1) * SOf β p P hP x := mul_nonneg (by linarith) hs0
    linarith
  · have hlt : m < 1 := not_le.mp h
    have hle : (1 - m) * SOf β p P hP x ≤ 1 - m := mul_le_of_le_one_right (by linarith) hs1
    nlinarith

/-! ### The target -/

theorem stretchConst_relations {n : ℕ} (P : PL.Cx n) (hP : P.faces.Finite) {β : ℝ} {p : ℕ}
    {m : ℝ} (hm : 0 < m) {x : PL.E n} (hx : x ∈ P.space) {y : PL.E n}
    (hy : y = Work.Geo.DualStretch.stretchM β p P hP (fun _ => m) x)
    (hwt : ∀ τ : Finset (PL.E n), Work.Geo.DualStretch.massG P hP y τ =
      if τ ∈ Work.Geo.DualStretch.posCands P hP x then
        Work.Geo.DualStretch.wtC β p P hP m x τ else 0) :
    Work.Geo.DualStretch.SOf β p P hP y =
        m * Work.Geo.DualStretch.SOf β p P hP x / Work.Geo.DualStretch.denC β p P hP m x ∧
    Work.Geo.DualStretch.AOf β p P hP y =
        (Work.Geo.DualStretch.denC β p P hP m x)⁻¹ • Work.Geo.DualStretch.AOf β p P hP x ∧
    Work.Geo.DualStretch.BOf β p P hP y =
        (m / Work.Geo.DualStretch.denC β p P hP m x) • Work.Geo.DualStretch.BOf β p P hP x ∧
    Work.Geo.DualStretch.segOf β p P hP y = Work.Geo.DualStretch.segOf β p P hP x := by
  classical
  have hs0 : 0 ≤ SOf β p P hP x := SOf_nonneg P hP x
  have hs1 : SOf β p P hP x ≤ 1 := SOf_le_one P hP hx
  have hdpos : 0 < denC β p P hP m x := denC_pos P hP hm hs0 hs1
  have hdne : denC β p P hP m x ≠ 0 := ne_of_gt hdpos
  have hmne : m ≠ 0 := ne_of_gt hm
  have hzero : ∀ τ ∈ cands P hP, τ ∉ posCands P hP x → massG P hP x τ = 0 :=
    fun τ hτc hτ => massG_eq_zero_of_not_mem_posCands P hP hτc hτ
  -- The total high mass, the low part and the high part transform by explicit factors.
  have hS : SOf β p P hP y = m * (denC β p P hP m x)⁻¹ * SOf β p P hP x := by
    have hterm : ∀ τ ∈ cands P hP,
        (if LowFace β p τ then (0 : ℝ) else massG P hP y τ) =
          m * (denC β p P hP m x)⁻¹ * (if LowFace β p τ then 0 else massG P hP x τ) := by
      intro τ hτc
      rw [hwt τ]
      by_cases hL : LowFace β p τ
      · rw [if_pos hL, if_pos hL, mul_zero]
      · rw [if_neg hL, if_neg hL]
        by_cases hp : τ ∈ posCands P hP x
        · rw [if_pos hp, wtC, if_neg hL, div_eq_mul_inv]; ring
        · rw [if_neg hp, hzero τ hτc hp, mul_zero]
    calc SOf β p P hP y
        = ∑ τ ∈ cands P hP, (if LowFace β p τ then (0 : ℝ) else massG P hP y τ) := rfl
      _ = ∑ τ ∈ cands P hP, m * (denC β p P hP m x)⁻¹ *
            (if LowFace β p τ then 0 else massG P hP x τ) := Finset.sum_congr rfl hterm
      _ = m * (denC β p P hP m x)⁻¹ *
            ∑ τ ∈ cands P hP, (if LowFace β p τ then 0 else massG P hP x τ) :=
          (Finset.mul_sum _ _ _).symm
      _ = m * (denC β p P hP m x)⁻¹ * SOf β p P hP x := rfl
  have hA : AOf β p P hP y = (denC β p P hP m x)⁻¹ • AOf β p P hP x := by
    have hterm : ∀ τ ∈ cands P hP,
        (if LowFace β p τ then massG P hP y τ • bary τ else 0) =
          (denC β p P hP m x)⁻¹ •
            (if LowFace β p τ then massG P hP x τ • bary τ else 0) := by
      intro τ hτc
      rw [hwt τ]
      by_cases hL : LowFace β p τ
      · rw [if_pos hL]
        rw [if_pos hL]
        by_cases hp : τ ∈ posCands P hP x
        · rw [if_pos hp, wtC, if_pos hL, one_mul, div_eq_mul_inv, smul_smul]
          congr 1
          ring
        · rw [if_neg hp, hzero τ hτc hp, zero_smul, smul_zero]
      · rw [if_neg hL, if_neg hL, smul_zero]
    calc AOf β p P hP y
        = ∑ τ ∈ cands P hP, (if LowFace β p τ then massG P hP y τ • bary τ else 0) := rfl
      _ = ∑ τ ∈ cands P hP, (denC β p P hP m x)⁻¹ •
            (if LowFace β p τ then massG P hP x τ • bary τ else 0) := Finset.sum_congr rfl hterm
      _ = (denC β p P hP m x)⁻¹ •
            ∑ τ ∈ cands P hP, (if LowFace β p τ then massG P hP x τ • bary τ else 0) :=
          (Finset.smul_sum).symm
      _ = (denC β p P hP m x)⁻¹ • AOf β p P hP x := rfl
  have hB : BOf β p P hP y = (m * (denC β p P hP m x)⁻¹) • BOf β p P hP x := by
    have hterm : ∀ τ ∈ cands P hP,
        (if LowFace β p τ then (0 : E n) else massG P hP y τ • bary τ) =
          (m * (denC β p P hP m x)⁻¹) •
            (if LowFace β p τ then 0 else massG P hP x τ • bary τ) := by
      intro τ hτc
      rw [hwt τ]
      by_cases hL : LowFace β p τ
      · rw [if_pos hL]
        rw [if_pos hL]
        rw [smul_zero]
      · rw [if_neg hL]
        rw [if_neg hL]
        by_cases hp : τ ∈ posCands P hP x
        · rw [if_pos hp, wtC, if_neg hL, div_eq_mul_inv, smul_smul]
          congr 1
          ring
        · rw [if_neg hp, hzero τ hτc hp, zero_smul, smul_zero]
    calc BOf β p P hP y
        = ∑ τ ∈ cands P hP, (if LowFace β p τ then (0 : E n) else massG P hP y τ • bary τ) := rfl
      _ = ∑ τ ∈ cands P hP, (m * (denC β p P hP m x)⁻¹) •
            (if LowFace β p τ then 0 else massG P hP x τ • bary τ) := Finset.sum_congr rfl hterm
      _ = (m * (denC β p P hP m x)⁻¹) •
            ∑ τ ∈ cands P hP, (if LowFace β p τ then 0 else massG P hP x τ • bary τ) :=
          (Finset.smul_sum).symm
      _ = (m * (denC β p P hP m x)⁻¹) • BOf β p P hP x := rfl
  -- The join segment is unchanged.
  have hone : 1 - SOf β p P hP y = (1 - SOf β p P hP x) * (denC β p P hP m x)⁻¹ := by
    have hdeq : denC β p P hP m x = 1 + (m - 1) * SOf β p P hP x := rfl
    have hdne' : 1 + (m - 1) * SOf β p P hP x ≠ 0 := by rw [← hdeq]; exact hdne
    rw [hS, hdeq]
    field_simp
    ring
  have hu : uOf β p P hP y = uOf β p P hP x := by
    rw [uOf, uOf]
    by_cases hs : SOf β p P hP x = 1
    · have hx0 : 1 - SOf β p P hP x = 0 := by rw [hs]; ring
      have hy0 : 1 - SOf β p P hP y = 0 := by rw [hone, hx0, zero_mul]
      rw [if_pos hy0, if_pos hx0]
    · have hxne : 1 - SOf β p P hP x ≠ 0 := fun hc => hs (by linarith)
      have hyne : 1 - SOf β p P hP y ≠ 0 := by
        rw [hone]
        exact mul_ne_zero hxne (inv_ne_zero hdne)
      have h2 : (1 - SOf β p P hP y)⁻¹ * (denC β p P hP m x)⁻¹ = (1 - SOf β p P hP x)⁻¹ := by
        rw [hone, mul_inv_rev, inv_inv]
        have h_alg : denC β p P hP m x * (1 - SOf β p P hP x)⁻¹ * (denC β p P hP m x)⁻¹ =
            (1 - SOf β p P hP x)⁻¹ * (denC β p P hP m x * (denC β p P hP m x)⁻¹) := by ring
        rw [h_alg, mul_inv_cancel₀ hdne, mul_one]
      rw [if_neg hyne, if_neg hxne, hA, smul_smul, h2]
  have hw : wOf β p P hP y = wOf β p P hP x := by
    rw [wOf, wOf]
    by_cases hs : SOf β p P hP x = 0
    · have hy0 : SOf β p P hP y = 0 := by rw [hS, hs, mul_zero]
      rw [if_pos hy0, if_pos hs]
    · have hyne : SOf β p P hP y ≠ 0 := by
        rw [hS]
        exact mul_ne_zero (mul_ne_zero hmne (inv_ne_zero hdne)) hs
      have h2 : (SOf β p P hP y)⁻¹ * (m * (denC β p P hP m x)⁻¹) = (SOf β p P hP x)⁻¹ := by
        rw [hS, mul_inv_rev]
        have h_alg : (SOf β p P hP x)⁻¹ * (m * (denC β p P hP m x)⁻¹)⁻¹ *
              (m * (denC β p P hP m x)⁻¹) =
            (SOf β p P hP x)⁻¹ *
              ((m * (denC β p P hP m x)⁻¹)⁻¹ * (m * (denC β p P hP m x)⁻¹)) := by ring
        rw [h_alg, inv_mul_cancel₀ (mul_ne_zero hmne (inv_ne_zero hdne)), mul_one]
      rw [if_neg hyne, if_neg hs, hB, smul_smul, h2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hS, div_eq_mul_inv]; ring
  · rw [hA]
  · rw [hB, div_eq_mul_inv]
  · rw [segOf, segOf]
    exact Prod.ext hu hw

end Work.Geo.DualStretch
