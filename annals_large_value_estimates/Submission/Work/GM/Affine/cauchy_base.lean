import Mathlib
import Submission.GM.Interfaces
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.fine_setup

/-!
# GM §9: the elementary (Cauchy–Schwarz) bound for the affine sum

`∫ u, (affineSum K M₁ M₂ M₃ f u)^2 ≤ (|R1| |R2| |R3|)^2 · (2 M₂/M₁) · ∫ u, f u ^ 2`.

This is the crude bound supplying the base case `ε = 100` of the downward induction in the
proof of Proposition 9.1.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- `(ΣΣΣ F)² ≤ |s| |t| |r| ΣΣΣ F²` — Cauchy–Schwarz applied on each level. -/
lemma sq_sum_sum_le (s t r : Finset ℤ) (F : ℤ → ℤ → ℤ → ℝ) :
    (∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r, F i j k)^2 ≤
      (((s.card : ℝ) * t.card * r.card) * (∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r, F i j k^2)) := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => ∑ j ∈ t, ∑ k ∈ r, F i j k)
  have h2 : ∀ i ∈ s, (∑ j ∈ t, ∑ k ∈ r, F i j k)^2 ≤
      (t.card : ℝ) * ∑ j ∈ t, (∑ k ∈ r, F i j k)^2 := by
    intro i _
    exact sq_sum_le_card_mul_sum_sq
  have h3 : ∀ i ∈ s, ∀ j ∈ t, (∑ k ∈ r, F i j k)^2 ≤ (r.card : ℝ) * ∑ k ∈ r, F i j k^2 := by
    intro i _ j _
    exact sq_sum_le_card_mul_sum_sq
  calc (∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r, F i j k)^2
      ≤ (s.card : ℝ) * ∑ i ∈ s, (∑ j ∈ t, ∑ k ∈ r, F i j k)^2 := h1
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, (t.card : ℝ) * ∑ j ∈ t, (∑ k ∈ r, F i j k)^2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum h2
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, (t.card : ℝ) * ∑ j ∈ t, (r.card : ℝ) * ∑ k ∈ r, F i j k^2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum; intro i hi
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum fun j hj => h3 i hi j hj
    _ = ((s.card : ℝ) * t.card * r.card) * (∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r, F i j k^2) := by
        simp only [Finset.mul_sum]
        ring_nf

/-- The affine term `u ↦ f ((c u + e)/d)` has compact support if `f` does (`c ≠ 0`, `d ≠ 0`). -/
lemma hasCompactSupport_affine {f : ℝ → ℝ} (hcs : HasCompactSupport f)
    {c d e : ℝ} (hc : c ≠ 0) (hd : d ≠ 0) :
    HasCompactSupport (fun u : ℝ => f ((c * u + e) / d)) := by
  have hfun : (fun u : ℝ => f ((c * u + e) / d))
      = (f ∘ ⇑(Homeomorph.mulLeft₀ (c / d) (div_ne_zero hc hd))) ∘
          ⇑(Homeomorph.addRight (e / c)) := by
    funext u
    simp only [Function.comp_apply, Homeomorph.coe_mulLeft₀, Homeomorph.coe_addRight]
    congr 1
    field_simp
  rw [hfun]
  exact (hcs.comp_homeomorph _).comp_homeomorph _

lemma integrable_affine {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f)
    {c d e : ℝ} (hc : c ≠ 0) (hd : d ≠ 0) :
    Integrable (fun u : ℝ => f ((c * u + e) / d)) := by
  have hcont : Continuous (fun u : ℝ => f ((c * u + e) / d)) :=
    hf.comp (((continuous_const.mul continuous_id).add continuous_const).div_const d)
  exact hcont.integrable_of_hasCompactSupport (hasCompactSupport_affine hcs hc hd)

/-- The square of a compactly supported function has compact support. -/
lemma hasCompactSupport_sq {f : ℝ → ℝ} (hcs : HasCompactSupport f) :
    HasCompactSupport (fun u : ℝ => f u ^ 2) := by
  have hsub : tsupport (fun u : ℝ => f u ^ 2) ⊆ tsupport f := by
    apply closure_minimal _ (isClosed_tsupport f)
    intro u hu
    rw [Function.mem_support] at hu
    exact subset_tsupport f (fun h => hu (by rw [h]; norm_num))
  exact hcs.isCompact.of_isClosed_subset (isClosed_tsupport _) hsub

lemma integrable_affine_sq {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f)
    {c d e : ℝ} (hc : c ≠ 0) (hd : d ≠ 0) :
    Integrable (fun u : ℝ => f ((c * u + e) / d)^2) := by
  have hcont : Continuous (fun u : ℝ => f ((c * u + e) / d)^2) :=
    (hf.comp (((continuous_const.mul continuous_id).add continuous_const).div_const d)).pow 2
  exact hcont.integrable_of_hasCompactSupport
    (hasCompactSupport_affine (hasCompactSupport_sq hcs) hc hd)

/-- The `L²` integral of a single affine term. -/
lemma integral_affine_sq {f : ℝ → ℝ} {c d e : ℝ} (hc : c ≠ 0) (hd : 0 < d) :
    ∫ u, f ((c * u + e) / d)^2 = (d / |c|) * ∫ u, f u^2 := by
  have h1 : ∀ u : ℝ, f ((c * u + e) / d)^2 = (fun v => f v ^ 2) ((c / d) * (u + e / c)) := by
    intro u
    have h : (c * u + e) / d = (c / d) * (u + e / c) := by field_simp
    rw [h]
  calc ∫ u, f ((c * u + e) / d)^2
      = ∫ u, (fun v => f v ^ 2) ((c / d) * (u + e / c)) := by simp only [h1]
    _ = ∫ y, (fun v => f v ^ 2) ((c / d) * y) := by
        rw [MeasureTheory.integral_add_right_eq_self
          (fun u => (fun v => f v ^ 2) ((c / d) * u)) (e / c)]
    _ = |(c / d)⁻¹| * ∫ v, f v^2 := by
        simpa using MeasureTheory.Measure.integral_comp_mul_left (fun v : ℝ => f v ^ 2) (c / d)
    _ = (d / |c|) * ∫ v, f v^2 := by
        rw [inv_div, abs_div, abs_of_pos hd]

lemma abs_of_mem_R1 {M₁ : ℝ} (hM₁ : 0 < M₁) {m : ℤ} (hm : m ∈ R1 M₁) :
    M₁ ≤ |(m : ℝ)| := (Finset.mem_filter.mp hm).2.le

lemma R1_ne_zero {M₁ : ℝ} (hM₁ : 0 < M₁) {m : ℤ} (hm : m ∈ R1 M₁) : (m : ℝ) ≠ 0 := by
  have h := abs_of_mem_R1 hM₁ hm
  intro h0
  rw [h0, abs_zero] at h
  linarith

lemma R2_pos {M₂ : ℝ} (hM₂ : 0 < M₂) {m : ℤ} (hm : m ∈ R2 M₂) : 0 < (m : ℝ) := by
  have h : M₂ < (m : ℝ) := (Finset.mem_filter.mp hm).2
  linarith

lemma R2_le {M₂ : ℝ} {m : ℤ} (hm : m ∈ R2 M₂) : (m : ℝ) ≤ 2 * M₂ := by
  have h1 : m ≤ ⌊2 * M₂⌋ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
  have h2 : ((⌊2 * M₂⌋ : ℤ) : ℝ) ≤ 2 * M₂ := Int.floor_le _
  have h3 : (m : ℝ) ≤ ((⌊2 * M₂⌋ : ℤ) : ℝ) := by exact_mod_cast h1
  linarith

/-- The crude Cauchy–Schwarz bound for the affine sum. -/
theorem sq_integral_affineSum_le {K M₁ M₂ M₃ : ℝ} (hK : 0 < K) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hM₃ : 0 < M₃) {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f)
    (hnn : ∀ u, 0 ≤ f u) :
    ∫ u, (Submission.GM.affineSum K M₁ M₂ M₃ f u)^2 ≤
      (((R1 M₁).card : ℝ) * (R2 M₂).card * (R3 K M₃).card)^2 * (2 * M₂ / M₁)
        * ∫ u, (f u)^2 := by
  set A : ℝ := ((R1 M₁).card : ℝ) with hA
  set B : ℝ := ((R2 M₂).card : ℝ) with hB
  set C : ℝ := ((R3 K M₃).card : ℝ) with hC
  have hAnn : 0 ≤ A := by positivity
  have hBnn : 0 ≤ B := by positivity
  have hCnn : 0 ≤ C := by positivity
  have hint_affine : ∀ m₁ ∈ R1 M₁, ∀ m₂ ∈ R2 M₂, ∀ m₃ ∈ R3 K M₃,
      Integrable (fun u : ℝ => f (((m₁ : ℝ) * u + m₃) / m₂)^2) := by
    intro m₁ hm₁ m₂ hm₂ m₃ _
    exact integrable_affine_sq hf hcs (R1_ne_zero hM₁ hm₁) (ne_of_gt (R2_pos hM₂ hm₂))
  have hInt_eval : ∀ m₁ ∈ R1 M₁, ∀ m₂ ∈ R2 M₂, ∀ m₃ ∈ R3 K M₃,
      ∫ u, f (((m₁ : ℝ) * u + m₃) / m₂)^2 = ((m₂ : ℝ) / |(m₁ : ℝ)|) * ∫ u, f u^2 := by
    intro m₁ hm₁ m₂ hm₂ m₃ _
    exact integral_affine_sq (c := (m₁ : ℝ)) (d := (m₂ : ℝ)) (e := (m₃ : ℝ))
      (R1_ne_zero hM₁ hm₁) (R2_pos hM₂ hm₂)
  -- the majorant
  set G : ℝ → ℝ := fun u => A * B * C *
    ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3 K M₃, f (((m₁ : ℝ) * u + m₃) / m₂)^2 with hG
  have hpt : ∀ u, (Submission.GM.affineSum K M₁ M₂ M₃ f u)^2 ≤ G u := by
    intro u
    rw [affineSum_eq, hG]
    have := sq_sum_sum_le (R1 M₁) (R2 M₂) (R3 K M₃)
      (fun m₁ m₂ m₃ => f (((m₁ : ℝ) * u + m₃) / m₂))
    simpa [hA, hB, hC] using this
  have hIntG : Integrable G := by
    rw [hG]
    refine Integrable.const_mul ?_ (A * B * C)
    refine integrable_finsetSum _ fun m₁ hm₁ => ?_
    refine integrable_finsetSum _ fun m₂ hm₂ => ?_
    exact integrable_finsetSum _ fun m₃ hm₃ => hint_affine m₁ hm₁ m₂ hm₂ m₃ hm₃
  have hsumfac :
      (∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3 K M₃, ((m₂ : ℝ) / |(m₁ : ℝ)|) * ∫ u, f u^2)
        = (∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3 K M₃, ((m₂ : ℝ) / |(m₁ : ℝ)|))
          * ∫ u, f u^2 := by
    simp only [Finset.sum_mul]
  have hGint : ∫ u, G u = A * B * C *
      ((∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3 K M₃, ((m₂ : ℝ) / |(m₁ : ℝ)|))
        * ∫ u, f u^2) := by
    rw [hG, MeasureTheory.integral_const_mul]
    congr 1
    rw [← hsumfac]
    rw [MeasureTheory.integral_finset_sum _ fun m₁ hm₁ =>
      integrable_finsetSum _ fun m₂ hm₂ =>
        integrable_finsetSum _ fun m₃ hm₃ => hint_affine m₁ hm₁ m₂ hm₂ m₃ hm₃]
    apply Finset.sum_congr rfl; intro m₁ hm₁
    rw [MeasureTheory.integral_finset_sum _ fun m₂ hm₂ =>
      integrable_finsetSum _ fun m₃ hm₃ => hint_affine m₁ hm₁ m₂ hm₂ m₃ hm₃]
    apply Finset.sum_congr rfl; intro m₂ hm₂
    rw [MeasureTheory.integral_finset_sum _ fun m₃ hm₃ => hint_affine m₁ hm₁ m₂ hm₂ m₃ hm₃]
    apply Finset.sum_congr rfl; intro m₃ hm₃
    exact hInt_eval m₁ hm₁ m₂ hm₂ m₃ hm₃
  -- bound for the sum of scale factors
  have hsum_bound :
      (∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3 K M₃, ((m₂ : ℝ) / |(m₁ : ℝ)|))
        ≤ A * B * C * (2 * M₂ / M₁) := by
    have hterm : ∀ m₁ ∈ R1 M₁, ∀ m₂ ∈ R2 M₂, ∀ m₃ ∈ R3 K M₃,
        ((m₂ : ℝ) / |(m₁ : ℝ)|) ≤ 2 * M₂ / M₁ := by
      intro m₁ hm₁ m₂ hm₂ m₃ _
      have hb : (m₂ : ℝ) ≤ 2 * M₂ := R2_le hm₂
      have ha : M₁ ≤ |(m₁ : ℝ)| := abs_of_mem_R1 hM₁ hm₁
      have h1 : 1 / |(m₁ : ℝ)| ≤ 1 / M₁ := one_div_le_one_div_of_le hM₁ ha
      calc ((m₂ : ℝ) / |(m₁ : ℝ)|) = (m₂ : ℝ) * (1 / |(m₁ : ℝ)|) := by ring
        _ ≤ (2 * M₂) * (1 / M₁) := by
            exact mul_le_mul hb h1 (by positivity) (by positivity)
        _ = 2 * M₂ / M₁ := by ring
    calc (∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3 K M₃, ((m₂ : ℝ) / |(m₁ : ℝ)|))
        ≤ ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3 K M₃, (2 * M₂ / M₁) :=
          Finset.sum_le_sum fun m₁ hm₁ => Finset.sum_le_sum fun m₂ hm₂ =>
            Finset.sum_le_sum fun m₃ hm₃ => hterm m₁ hm₁ m₂ hm₂ m₃ hm₃
      _ = A * B * C * (2 * M₂ / M₁) := by
          simp only [Finset.sum_const, nsmul_eq_mul, hA, hB, hC]
          ring
  have hInn : 0 ≤ ∫ u, (f u)^2 := integral_nonneg fun u => sq_nonneg _
  calc ∫ u, (Submission.GM.affineSum K M₁ M₂ M₃ f u)^2
      ≤ ∫ u, G u := integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => sq_nonneg _)
        hIntG (Filter.Eventually.of_forall hpt)
    _ = A * B * C * ((∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3 K M₃,
          ((m₂ : ℝ) / |(m₁ : ℝ)|)) * ∫ u, f u^2) := hGint
    _ ≤ A * B * C * (A * B * C * (2 * M₂ / M₁)) * ∫ u, f u^2 := by
        calc A * B * C * ((∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3 K M₃,
                ((m₂ : ℝ) / |(m₁ : ℝ)|)) * ∫ u, f u^2)
            = (A * B * C * (∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3 K M₃,
                ((m₂ : ℝ) / |(m₁ : ℝ)|))) * ∫ u, f u^2 := by ring
          _ ≤ (A * B * C * (A * B * C * (2 * M₂ / M₁))) * ∫ u, f u^2 := by
              apply mul_le_mul_of_nonneg_right _ hInn
              exact mul_le_mul_of_nonneg_left hsum_bound (by positivity)
    _ = (((R1 M₁).card : ℝ) * (R2 M₂).card * (R3 K M₃).card)^2 * (2 * M₂ / M₁)
        * ∫ u, (f u)^2 := by
        rw [hA, hB, hC]; ring

end

end Work.GM.Affine
