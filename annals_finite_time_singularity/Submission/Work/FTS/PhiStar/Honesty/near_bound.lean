import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A near-field (small `t`) weighted bound

This file proves `Work.FTS.PhiStar.Honesty.near_bound`: the `L²`-type norm
`∫_{0}^{1} (χ t * G t - c t)^2 / t^4` of the *difference* between the cutoff profile
`χ * G` and the reference profile `c` is controlled by

* `η`, a bound for the singular weight `(c t)^2/t^4` on the near interval `(0, 2r)`, and
* `ε₁`, an unweighted `L²` bound for `G - c` on `[r/2, 2N]`,

with the mild factor `r⁻⁴` on the second term.  The proof splits `(0,1)` into the three
regions
`(0, r/2)`, `[r/2, 2r]` and `(2r, 1)`:
on the first, `χ = 0` by hypothesis; on the third, `χ = 1`; on the middle one only
`|χ| ≤ 1` is used, together with the fact that `1/t^4 ≤ 16 r⁻⁴` there.
-/

namespace Work.FTS.PhiStar.Honesty

/-- Monotonicity of the set integral for an arbitrary measurable set: if `f` is
nonnegative on `s` and dominated by the integrable `g` there, then
`∫_s f ≤ ∫_s g`.  (No integrability of `f` itself is needed.) -/
private lemma setIntegral_le_of_forall_le_on {s : Set ℝ} (hs : MeasurableSet s) {f g : ℝ → ℝ}
    (hpos : ∀ x ∈ s, 0 ≤ f x) (hg : MeasureTheory.IntegrableOn g s)
    (hle : ∀ x ∈ s, f x ≤ g x) : ∫ x in s, f x ≤ ∫ x in s, g x := by
  refine MeasureTheory.integral_mono_of_nonneg ?_ hg.integrable ?_
  · change ∀ᵐ x ∂(MeasureTheory.volume.restrict s), (0 : ℝ) ≤ f x
    rw [MeasureTheory.ae_restrict_iff' hs]
    exact Filter.Eventually.of_forall (fun x hx => hpos x hx)
  · change ∀ᵐ x ∂(MeasureTheory.volume.restrict s), f x ≤ g x
    rw [MeasureTheory.ae_restrict_iff' hs]
    exact Filter.Eventually.of_forall (fun x hx => hle x hx)

/-- Monotonicity of the set integral in the set: enlarging the domain of a nonnegative
integrable function increases the integral. -/
private lemma setIntegral_le_of_le_on_of_subset {s t : Set ℝ} (hst : s ⊆ t)
    (ht : MeasurableSet t) {f : ℝ → ℝ} (hf : MeasureTheory.IntegrableOn f t)
    (hpos : ∀ x ∈ t, 0 ≤ f x) : ∫ x in s, f x ≤ ∫ x in t, f x := by
  refine MeasureTheory.setIntegral_mono_set hf ?_ ?_
  · change ∀ᵐ x ∂(MeasureTheory.volume.restrict t), (0 : ℝ) ≤ f x
    rw [MeasureTheory.ae_restrict_iff' ht]
    exact Filter.Eventually.of_forall (fun x hx => hpos x hx)
  · change ∀ᵐ x ∂(MeasureTheory.volume), x ∈ s → x ∈ t
    exact Filter.Eventually.of_forall (fun x hx => hst hx)

/-- Pointwise algebra on the middle region `r/2 ≤ x`: since `|A| ≤ 1`,
`(A * B - C)^2 ≤ 2 (B - C)^2 + 8 C^2`, and `1/x^4 ≤ 16 r⁻⁴`. -/
private lemma region2_pt {A B C x r : ℝ} (hr : 0 < r) (hx : r / 2 ≤ x) (hA : |A| ≤ 1) :
    (A * B - C) ^ 2 / x ^ 4 ≤ 2 * (16 * (r⁻¹) ^ 4 * (B - C) ^ 2) + 8 * (C ^ 2 / x ^ 4) := by
  have hx0 : 0 < x := by linarith
  have hA2 : A ^ 2 ≤ 1 := by
    have h := abs_le.mp hA
    nlinarith [h.1, h.2]
  have hkey : (A * B - C) ^ 2 ≤ 2 * (B - C) ^ 2 + 8 * C ^ 2 := by
    have h1 : A * B - C = A * (B - C) + (A - 1) * C := by ring
    rw [h1]
    have h2 := add_sq_le (a := A * (B - C)) (b := (A - 1) * C)
    have h3 : (A * (B - C)) ^ 2 ≤ (B - C) ^ 2 := by
      rw [mul_pow]
      nlinarith [sq_nonneg (B - C), hA2]
    have h4 : ((A - 1) * C) ^ 2 ≤ 4 * C ^ 2 := by
      rw [mul_pow]
      have hA1 : (A - 1) ^ 2 ≤ 4 := by
        have h := abs_le.mp hA
        nlinarith [h.1, h.2]
      nlinarith [sq_nonneg C]
    linarith
  have hK : (x ^ 4)⁻¹ ≤ 16 * (r⁻¹) ^ 4 := by
    have h1 : (1 : ℝ) / x ^ 4 ≤ 1 / (r / 2) ^ 4 := by
      apply one_div_le_one_div_of_le (pow_pos (by linarith) 4)
      exact pow_le_pow_left₀ (by linarith) hx 4
    have h2 : (1 : ℝ) / (r / 2) ^ 4 = 16 * (r⁻¹) ^ 4 := by
      have hrne : r ≠ 0 := ne_of_gt hr
      field_simp
      ring
    rw [one_div] at h1
    linarith [h1, h2.le]
  calc (A * B - C) ^ 2 / x ^ 4 ≤ (2 * (B - C) ^ 2 + 8 * C ^ 2) / x ^ 4 :=
        div_le_div_of_nonneg_right hkey (by positivity)
    _ = 2 * ((B - C) ^ 2 / x ^ 4) + 8 * (C ^ 2 / x ^ 4) := by ring
    _ ≤ 2 * (16 * (r⁻¹) ^ 4 * (B - C) ^ 2) + 8 * (C ^ 2 / x ^ 4) := by
        have hs : (B - C) ^ 2 / x ^ 4 ≤ 16 * (r⁻¹) ^ 4 * (B - C) ^ 2 := by
          rw [div_eq_mul_inv]
          calc (B - C) ^ 2 * (x ^ 4)⁻¹ = (x ^ 4)⁻¹ * (B - C) ^ 2 := by ring
            _ ≤ (16 * (r⁻¹) ^ 4) * (B - C) ^ 2 :=
                mul_le_mul_of_nonneg_right hK (sq_nonneg _)
            _ = 16 * (r⁻¹) ^ 4 * (B - C) ^ 2 := by ring
        linarith

/-- Pointwise algebra on the far region `2r ≤ x`: `1/x^4 ≤ r⁻⁴/16`. -/
private lemma region3_pt {C x r : ℝ} (hr : 0 < r) (hx : 2 * r ≤ x) :
    C ^ 2 / x ^ 4 ≤ (1 / 16) * (r⁻¹) ^ 4 * C ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hK : (x ^ 4)⁻¹ ≤ (1 / 16) * (r⁻¹) ^ 4 := by
    have h1 : (1 : ℝ) / x ^ 4 ≤ 1 / (2 * r) ^ 4 := by
      apply one_div_le_one_div_of_le (pow_pos (by linarith) 4)
      exact pow_le_pow_left₀ (by linarith) hx 4
    have h2 : (1 : ℝ) / (2 * r) ^ 4 = (1 / 16) * (r⁻¹) ^ 4 := by
      have hrne : r ≠ 0 := ne_of_gt hr
      field_simp
      ring
    rw [one_div] at h1
    linarith [h1, h2.le]
  rw [div_eq_mul_inv]
  calc C ^ 2 * (x ^ 4)⁻¹ = (x ^ 4)⁻¹ * C ^ 2 := by ring
    _ ≤ ((1 / 16) * (r⁻¹) ^ 4) * C ^ 2 := mul_le_mul_of_nonneg_right hK (sq_nonneg _)
    _ = (1 / 16) * (r⁻¹) ^ 4 * C ^ 2 := by ring

theorem near_bound {c G χ : ℝ → ℝ} {r N ε₁ η : ℝ}
    (hr : 0 < r) (hr1 : 2 * r ≤ 1) (hN : 2 ≤ N)
    (hχ0 : ∀ t : ℝ, t ≤ r / 2 → χ t = 0)
    (hχ1 : ∀ t : ℝ, r ≤ t → t ≤ N / 2 → χ t = 1)
    (hχb : ∀ t : ℝ, |χ t| ≤ 1)
    (hcH : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hcIcc : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Icc (r / 2) (2 * N)))
    (hη : ∫ t in Set.Ioo 0 (2 * r), (c t) ^ 2 / t ^ 4 ≤ η)
    (hGint : MeasureTheory.IntegrableOn (fun t : ℝ => (G t - c t) ^ 2) (Set.Icc (r / 2) (2 * N)))
    (happ : ∫ t in Set.Icc (r / 2) (2 * N), (G t - c t) ^ 2 ≤ ε₁)
    (hint : MeasureTheory.IntegrableOn (fun t : ℝ => (χ t * G t - c t) ^ 2 / t ^ 4) (Set.Ioo 0 1)) :
    ∫ t in Set.Ioo 0 1, (χ t * G t - c t) ^ 2 / t ^ 4 ≤ 67 * η + 65 * (r⁻¹) ^ 4 * ε₁ := by
  have hrinv_nn : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
  have hη_nn : 0 ≤ η := by
    have h1 : 0 ≤ ∫ t in Set.Ioo 0 (2 * r), (c t) ^ 2 / t ^ 4 :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t _ =>
        div_nonneg (sq_nonneg _) (by positivity))
    linarith
  have hε_nn : 0 ≤ ε₁ := by
    have h1 : 0 ≤ ∫ t in Set.Icc (r / 2) (2 * N), (G t - c t) ^ 2 :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun t _ => sq_nonneg _)
    linarith
  let F : ℝ → ℝ := fun t => (χ t * G t - c t) ^ 2 / t ^ 4
  have hFnn : ∀ t : ℝ, 0 ≤ F t := fun t => by
    rw [show F t = (χ t * G t - c t) ^ 2 / t ^ 4 from rfl]
    exact div_nonneg (sq_nonneg _) (by positivity)
  have hintF : MeasureTheory.IntegrableOn F (Set.Ioo 0 1) := hint
  have hGsub : Set.Icc (r / 2) (2 * r) ⊆ Set.Icc (r / 2) (2 * N) :=
    fun t ht => ⟨ht.1, by linarith [ht.2, hN]⟩
  -- integrability of `F` on the three pieces of the decomposition
  have hintIoc : MeasureTheory.IntegrableOn F (Set.Ioc (0 : ℝ) 1) :=
    hintF.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm
  have hint1 : MeasureTheory.IntegrableOn F (Set.Ioo 0 (r / 2)) :=
    hintF.mono_set (by intro t ht; exact ⟨ht.1, by linarith [ht.2]⟩)
  have hint2 : MeasureTheory.IntegrableOn F (Set.Icc (r / 2) (2 * r)) :=
    hintIoc.mono_set (by intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2, hr1]⟩)
  have hint3 : MeasureTheory.IntegrableOn F (Set.Ioc (2 * r) 1) :=
    hintIoc.mono_set (by intro t ht; exact ⟨by linarith [ht.1], ht.2⟩)
  -- the decomposition `(0,1) = (0,r/2) ∪ [r/2,2r] ∪ (2r,1)`
  have hsplit : ∫ t in Set.Ioo 0 1, F t
      = (∫ t in Set.Ioo 0 (r / 2), F t) + (∫ t in Set.Icc (r / 2) (2 * r), F t)
        + (∫ t in Set.Ioc (2 * r) 1, F t) := by
    have hIoc_eq : Set.Ioc (0 : ℝ) 1
        = Set.Ioo 0 (r / 2) ∪ (Set.Icc (r / 2) (2 * r) ∪ Set.Ioc (2 * r) 1) := by
      ext t
      simp only [Set.mem_Ioc, Set.mem_Ioo, Set.mem_Icc, Set.mem_union]
      constructor
      · rintro ⟨h0, h1⟩
        rcases lt_or_ge t (r / 2) with h | h
        · exact Or.inl ⟨h0, h⟩
        · rcases lt_or_ge (2 * r) t with h2 | h2
          · exact Or.inr (Or.inr ⟨h2, h1⟩)
          · exact Or.inr (Or.inl ⟨h, h2⟩)
      · rintro (⟨h0, h1⟩ | ⟨h1, h2⟩ | ⟨h2, h3⟩)
        · exact ⟨h0, by linarith⟩
        · exact ⟨by linarith, by linarith⟩
        · exact ⟨by linarith, by linarith⟩
    have hdisj1 : Disjoint (Set.Ioo 0 (r / 2)) (Set.Icc (r / 2) (2 * r) ∪ Set.Ioc (2 * r) 1) := by
      rw [Set.disjoint_left]
      intro t h1 h2
      rcases h2 with h2 | h2
      · exact absurd h2.1 (not_le.mpr h1.2)
      · linarith [h1.2, h2.1]
    have hdisj2 : Disjoint (Set.Icc (r / 2) (2 * r)) (Set.Ioc (2 * r) 1) := by
      rw [Set.disjoint_left]
      intro t h1 h2
      linarith [h1.2, h2.1]
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo (f := F) (x := (0 : ℝ)) (y := 1)]
    rw [hIoc_eq,
      MeasureTheory.setIntegral_union hdisj1 (measurableSet_Icc.union measurableSet_Ioc) hint1
        (hint2.union hint3),
      MeasureTheory.setIntegral_union hdisj2 measurableSet_Ioc hint2 hint3]
    ring
  -- ### Region 1: `(0, r/2)`, where `χ = 0`
  have hI1 : ∫ t in Set.Ioo 0 (r / 2), F t ≤ η := by
    have heq : ∫ t in Set.Ioo 0 (r / 2), F t = ∫ t in Set.Ioo 0 (r / 2), (c t) ^ 2 / t ^ 4 := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      show (χ t * G t - c t) ^ 2 / t ^ 4 = (c t) ^ 2 / t ^ 4
      rw [hχ0 t (le_of_lt ht.2)]
      ring
    rw [heq]
    refine le_trans (setIntegral_le_of_le_on_of_subset
      (s := Set.Ioo 0 (r / 2)) (t := Set.Ioo 0 (2 * r))
      (by intro t ht; exact ⟨ht.1, by linarith [ht.2]⟩) measurableSet_Ioo ?_
      (fun t _ => div_nonneg (sq_nonneg _) (by positivity))) hη
    exact hcH.mono_set (by intro t ht; exact ⟨ht.1, by linarith [ht.2, hr1]⟩)
  -- ### Region 2: `[r/2, 2r]`, where only `|χ| ≤ 1` is known
  have hI2 : ∫ t in Set.Icc (r / 2) (2 * r), F t ≤ 32 * ((r⁻¹) ^ 4 * ε₁) + 8 * η := by
    have hle : ∀ t ∈ Set.Icc (r / 2) (2 * r),
        F t ≤ 2 * (16 * (r⁻¹) ^ 4 * (G t - c t) ^ 2) + 8 * ((c t) ^ 2 / t ^ 4) := by
      intro t ht
      have h := region2_pt (r := r) (A := χ t) (B := G t) (C := c t) (x := t) hr ht.1 (hχb t)
      show (χ t * G t - c t) ^ 2 / t ^ 4
        ≤ 2 * (16 * (r⁻¹) ^ 4 * (G t - c t) ^ 2) + 8 * ((c t) ^ 2 / t ^ 4)
      exact h
    have hG' : MeasureTheory.IntegrableOn (fun t => (G t - c t) ^ 2) (Set.Icc (r / 2) (2 * r)) :=
      hGint.mono_set hGsub
    have hcIoc : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioc (0 : ℝ) 1) :=
      hcH.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm
    have hc' : MeasureTheory.IntegrableOn (fun t => (c t) ^ 2 / t ^ 4) (Set.Icc (r / 2) (2 * r)) :=
      hcIoc.mono_set (by intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2, hr1]⟩)
    have hgi : MeasureTheory.IntegrableOn
        (fun t => 2 * (16 * (r⁻¹) ^ 4 * (G t - c t) ^ 2) + 8 * ((c t) ^ 2 / t ^ 4))
        (Set.Icc (r / 2) (2 * r)) :=
      ((hG'.integrable.const_mul (16 * (r⁻¹) ^ 4)).const_mul 2).add (hc'.integrable.const_mul 8)
    have hstep := setIntegral_le_of_forall_le_on measurableSet_Icc (fun t _ => hFnn t) hgi hle
    have hg_eq : ∫ t in Set.Icc (r / 2) (2 * r),
          (2 * (16 * (r⁻¹) ^ 4 * (G t - c t) ^ 2) + 8 * ((c t) ^ 2 / t ^ 4))
        = 2 * (16 * (r⁻¹) ^ 4) * (∫ t in Set.Icc (r / 2) (2 * r), (G t - c t) ^ 2)
          + 8 * (∫ t in Set.Icc (r / 2) (2 * r), (c t) ^ 2 / t ^ 4) := by
      have i1 : MeasureTheory.Integrable (fun t => 2 * (16 * (r⁻¹) ^ 4 * (G t - c t) ^ 2))
          (MeasureTheory.volume.restrict (Set.Icc (r / 2) (2 * r))) :=
        (hG'.integrable.const_mul (16 * (r⁻¹) ^ 4)).const_mul 2
      have i2 : MeasureTheory.Integrable (fun t => 8 * ((c t) ^ 2 / t ^ 4))
          (MeasureTheory.volume.restrict (Set.Icc (r / 2) (2 * r))) :=
        hc'.integrable.const_mul 8
      rw [MeasureTheory.integral_add i1 i2]
      simp only [MeasureTheory.integral_const_mul]
      ring
    have hGsq : ∫ t in Set.Icc (r / 2) (2 * r), (G t - c t) ^ 2 ≤ ε₁ :=
      le_trans (setIntegral_le_of_le_on_of_subset hGsub measurableSet_Icc hGint
        (fun t _ => sq_nonneg _)) happ
    have hcsq : ∫ t in Set.Icc (r / 2) (2 * r), (c t) ^ 2 / t ^ 4 ≤ η := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioo]
      exact le_trans (setIntegral_le_of_le_on_of_subset
        (s := Set.Ioo (r / 2) (2 * r)) (t := Set.Ioo 0 (2 * r))
        (by intro t ht; exact ⟨by linarith [ht.1], ht.2⟩) measurableSet_Ioo
        (hcH.mono_set (by intro t ht; exact ⟨ht.1, by linarith [ht.2, hr1]⟩))
        (fun t _ => div_nonneg (sq_nonneg _) (by positivity))) hη
    have hc0 : (0 : ℝ) ≤ 2 * (16 * (r⁻¹) ^ 4) := by
      have h : (0 : ℝ) ≤ (r⁻¹) ^ 4 := pow_nonneg hrinv_nn 4
      linarith
    calc ∫ t in Set.Icc (r / 2) (2 * r), F t
        ≤ ∫ t in Set.Icc (r / 2) (2 * r),
            (2 * (16 * (r⁻¹) ^ 4 * (G t - c t) ^ 2) + 8 * ((c t) ^ 2 / t ^ 4)) := hstep
      _ = 2 * (16 * (r⁻¹) ^ 4) * (∫ t in Set.Icc (r / 2) (2 * r), (G t - c t) ^ 2)
            + 8 * (∫ t in Set.Icc (r / 2) (2 * r), (c t) ^ 2 / t ^ 4) := hg_eq
      _ ≤ 2 * (16 * (r⁻¹) ^ 4) * ε₁ + 8 * η := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hGsq hc0
          · exact mul_le_mul_of_nonneg_left hcsq (by norm_num)
      _ = 32 * ((r⁻¹) ^ 4 * ε₁) + 8 * η := by ring
  -- ### Region 3: `(2r, 1)`, where `χ = 1`
  have hI3 : ∫ t in Set.Ioc (2 * r) 1, F t ≤ (1 / 16) * ((r⁻¹) ^ 4 * ε₁) := by
    have heq : ∫ t in Set.Ioc (2 * r) 1, F t
        = ∫ t in Set.Ioc (2 * r) 1, (G t - c t) ^ 2 / t ^ 4 := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      show (χ t * G t - c t) ^ 2 / t ^ 4 = (G t - c t) ^ 2 / t ^ 4
      rw [hχ1 t (by linarith [ht.1]) (by linarith [ht.2, hN])]
      ring
    rw [heq]
    have hsub3 : Set.Ioc (2 * r) 1 ⊆ Set.Icc (r / 2) (2 * N) :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2, hN]⟩
    have hle : ∀ t ∈ Set.Ioc (2 * r) 1,
        (G t - c t) ^ 2 / t ^ 4 ≤ (1 / 16) * (r⁻¹) ^ 4 * (G t - c t) ^ 2 :=
      fun t ht => region3_pt (r := r) (C := G t - c t) (x := t) hr (le_of_lt ht.1)
    have hgi : MeasureTheory.IntegrableOn (fun t => (1 / 16) * (r⁻¹) ^ 4 * (G t - c t) ^ 2)
        (Set.Ioc (2 * r) 1) :=
      (hGint.mono_set hsub3).integrable.const_mul ((1 / 16) * (r⁻¹) ^ 4)
    have hc0 : (0 : ℝ) ≤ (1 / 16) * (r⁻¹) ^ 4 := by
      have h : (0 : ℝ) ≤ (r⁻¹) ^ 4 := pow_nonneg hrinv_nn 4
      linarith
    calc ∫ t in Set.Ioc (2 * r) 1, (G t - c t) ^ 2 / t ^ 4
        ≤ ∫ t in Set.Ioc (2 * r) 1, (1 / 16) * (r⁻¹) ^ 4 * (G t - c t) ^ 2 :=
          setIntegral_le_of_forall_le_on measurableSet_Ioc
            (fun t _ => div_nonneg (sq_nonneg _) (by positivity)) hgi hle
      _ = (1 / 16) * (r⁻¹) ^ 4 * (∫ t in Set.Ioc (2 * r) 1, (G t - c t) ^ 2) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ (1 / 16) * (r⁻¹) ^ 4 * ε₁ := by
          apply mul_le_mul_of_nonneg_left _ hc0
          exact le_trans (setIntegral_le_of_le_on_of_subset hsub3 measurableSet_Icc hGint
            (fun t _ => sq_nonneg _)) happ
      _ = (1 / 16) * ((r⁻¹) ^ 4 * ε₁) := by ring
  -- ### Assembly
  have hsum : ∫ t in Set.Ioo 0 1, F t ≤ 9 * η + (32 + 1 / 16) * ((r⁻¹) ^ 4 * ε₁) := by
    rw [hsplit]
    linarith [hI1, hI2, hI3]
  have hX : 0 ≤ (r⁻¹) ^ 4 * ε₁ := mul_nonneg (pow_nonneg hrinv_nn 4) hε_nn
  have hmain : ∫ t in Set.Ioo 0 1, F t ≤ 67 * η + 65 * (r⁻¹) ^ 4 * ε₁ := by
    linarith [hsum, hX, hη_nn]
  exact hmain

end Work.FTS.PhiStar.Honesty
