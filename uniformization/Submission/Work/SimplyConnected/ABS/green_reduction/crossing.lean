import Mathlib
import Submission.Work.SimplyConnected.ABS.RegularPieceDefs
import Submission.Work.SimplyConnected.ABS.ray_boundary_barrier
import Submission.Work.SimplyConnected.ABS.sectorCondition_of_chart_balls
import Submission.Work.SimplyConnected.ABS.region_with_sector_boundary

namespace Work.SimplyConnected.ABS.green_reduction

open scoped _root_.Topology Manifold ContDiff ComplexConjugate
open Set Filter

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

section Crossing

/-- The real inner product on `ℂ` is the functional `z ↦ Re (conj u * z)`. -/
lemma inner_eq_reConj (x y : ℂ) : inner ℝ x y = reConjCLM x y := by
  rw [Complex.inner, reConjCLM_apply, mul_comm]

/-- `Re (conj (I * v) * u) = Im (conj v * u)`. -/
lemma reConj_I_mul_im (v u : ℂ) :
    reConjCLM (Complex.I * v) u = ((starRingEnd ℂ v) * u).im := by
  rw [reConjCLM_apply]
  have h1 : (starRingEnd ℂ (Complex.I * v)) * u = -Complex.I * ((starRingEnd ℂ v) * u) := by
    rw [map_mul, Complex.conj_I]; ring
  rw [h1]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

/-- `((r : ℂ) ^ 2).im = 0`. -/
private lemma ofReal_sq_im (r : ℝ) : ((r : ℂ) ^ 2).im = 0 := by
  rw [pow_two, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- `Re (conj (I * v) * v) = 0`. -/
lemma reConj_Iv_v (v : ℂ) : reConjCLM (Complex.I * v) v = 0 := by
  rw [reConjCLM_apply, map_mul, Complex.conj_I, mul_assoc, Complex.conj_mul',
    Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  rw [ofReal_sq_im]
  ring

/-- `Re (conj v * (I * v)) = 0`. -/
lemma reConj_v_Iv (v : ℂ) : reConjCLM v (Complex.I * v) = 0 := by
  have h : (starRingEnd ℂ v) * (Complex.I * v) = Complex.I * ((starRingEnd ℂ v) * v) := by ring
  rw [reConjCLM_apply, h, Complex.conj_mul', Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [ofReal_sq_im]
  ring

/-- `Re (conj (I * v) * (I * v)) = ‖v‖ ^ 2`. -/
lemma reConj_Iv_Iv (v : ℂ) : reConjCLM (Complex.I * v) (Complex.I * v) = ‖v‖ ^ 2 := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [reConjCLM_apply, map_mul, Complex.conj_I]
  have h : (-Complex.I * starRingEnd ℂ v) * (Complex.I * v) = starRingEnd ℂ v * v := by
    rw [show (-Complex.I * starRingEnd ℂ v) * (Complex.I * v)
        = -((Complex.I * Complex.I) * (starRingEnd ℂ v * v)) by ring, hI]
    ring
  rw [h]
  exact reConjCLM_mul_self_re v

/-- The orthogonal decomposition of `u` in the real basis `{v, I * v}`, multiplicative form. -/
lemma smul_decomp_C (v u : ℂ) :
    ((‖v‖ ^ 2 : ℝ) : ℂ) * u
      = ((reConjCLM v u : ℝ) : ℂ) * v
        + ((reConjCLM (Complex.I * v) u : ℝ) : ℂ) * (Complex.I * v) := by
  have h1 : (starRingEnd ℂ v) * u = ((reConjCLM v u : ℝ) : ℂ)
      + ((reConjCLM (Complex.I * v) u : ℝ) : ℂ) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im ((starRingEnd ℂ v) * u)]
    rw [reConj_I_mul_im v u, reConjCLM_apply]
  have h2 : (starRingEnd ℂ v) * v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']; push_cast; ring
  calc ((‖v‖ ^ 2 : ℝ) : ℂ) * u = ((starRingEnd ℂ v) * v) * u := by rw [h2]
    _ = ((starRingEnd ℂ v) * u) * v := by ring
    _ = _ := by rw [h1]; ring

/-- The orthogonal decomposition of `u` in the real basis `{v, I * v}`. -/
lemma smul_decomp (v u : ℂ) :
    (‖v‖ ^ 2 : ℝ) • u
      = (reConjCLM v u) • v + (reConjCLM (Complex.I * v) u) • (Complex.I * v) := by
  rw [Complex.real_smul, Complex.real_smul, Complex.real_smul]
  exact smul_decomp_C v u

/-- `⟪u * D, A⟫ = Re (conj A * D * u)`. -/
lemma inner_mul_right_eq (A D u : ℂ) :
    inner ℝ (u * D) A = reConjCLM (A * starRingEnd ℂ D) u := by
  rw [real_inner_comm, Complex.inner, reConjCLM_apply, map_mul]
  have h : (starRingEnd ℂ) ((starRingEnd ℂ) D) = D := by simp
  rw [h]
  congr 1
  ring

set_option maxHeartbeats 4000000 in
/-- **A thin cone on which two positive functionals dominate the norm.**  If `N₁ v > 0` and
`N₂ v > 0` then there are non-zero functionals `L₁ L₂` with a non-empty common positive sector and a
constant `κ > 0` such that every `u` of the sector satisfies `κ ‖u‖ ≤ N i u`, `i = 1, 2`. -/
theorem exists_cone_of_two_positive {N₁ N₂ : ℂ →L[ℝ] ℝ} {v : ℂ} (h₁ : 0 < N₁ v)
    (h₂ : 0 < N₂ v) :
    ∃ (L₁ L₂ : ℂ →L[ℝ] ℝ) (κ : ℝ), L₁ ≠ 0 ∧ L₂ ≠ 0 ∧ 0 < κ ∧
      (∃ w : ℂ, 0 < L₁ w ∧ 0 < L₂ w) ∧
      ∀ u : ℂ, 0 < L₁ u → 0 < L₂ u → κ * ‖u‖ ≤ N₁ u ∧ κ * ‖u‖ ≤ N₂ u := by
  classical
  have hvne : v ≠ 0 := by rintro rfl; simp at h₁
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  have hWpos : 0 < ‖v‖ ^ 2 := pow_pos hvpos 2
  have hWne : ‖v‖ ^ 2 ≠ 0 := ne_of_gt hWpos
  have hWneC : ((‖v‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact hWne
  let c₁ : ℝ := N₁ v
  let c₂ : ℝ := N₂ v
  have hc₁eq : c₁ = N₁ v := rfl
  have hc₂eq : c₂ = N₂ v := rfl
  have hc₁pos : 0 < c₁ := h₁
  have hc₂pos : 0 < c₂ := h₂
  let K₁ : ℝ := |N₁ (Complex.I * v)|
  let K₂ : ℝ := |N₂ (Complex.I * v)|
  have hK₁eq : K₁ = |N₁ (Complex.I * v)| := rfl
  have hK₂eq : K₂ = |N₂ (Complex.I * v)| := rfl
  have hK₁nn : 0 ≤ K₁ := abs_nonneg _
  have hK₂nn : 0 ≤ K₂ := abs_nonneg _
  let Λ : ℝ := max 2 (max (4 * (K₁ + 1) / c₁) (4 * (K₂ + 1) / c₂))
  have hΛ2 : 2 ≤ Λ := le_max_left _ _
  have hΛpos : 0 < Λ := lt_of_lt_of_le (by norm_num) hΛ2
  have hΛA : 4 * (K₁ + 1) / c₁ ≤ Λ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hΛB : 4 * (K₂ + 1) / c₂ ≤ Λ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hεA : 1 / Λ ≤ c₁ / (4 * (K₁ + 1)) := by
    rw [div_le_div_iff₀ hΛpos (by positivity)]
    have h : 4 * (K₁ + 1) ≤ Λ * c₁ := by
      have h3 := mul_le_mul_of_nonneg_right hΛA (le_of_lt hc₁pos)
      rwa [div_mul_cancel₀ _ (ne_of_gt hc₁pos)] at h3
    linarith [h]
  have hεB : 1 / Λ ≤ c₂ / (4 * (K₂ + 1)) := by
    rw [div_le_div_iff₀ hΛpos (by positivity)]
    have h : 4 * (K₂ + 1) ≤ Λ * c₂ := by
      have h3 := mul_le_mul_of_nonneg_right hΛB (le_of_lt hc₂pos)
      rwa [div_mul_cancel₀ _ (ne_of_gt hc₂pos)] at h3
    linarith [h]
  have hKΛ₁ : K₁ / Λ ≤ c₁ / 4 := by
    have h := mul_le_mul_of_nonneg_left hεA hK₁nn
    have h2 : K₁ * (1 / Λ) = K₁ / Λ := by ring
    have h3 : K₁ * (c₁ / (4 * (K₁ + 1))) ≤ c₁ / 4 := by
      rw [show K₁ * (c₁ / (4 * (K₁ + 1))) = c₁ * K₁ / (4 * (K₁ + 1)) by ring]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hc₁pos.le, hK₁nn]
    linarith [h, h2.le, h2.ge, h3]
  have hKΛ₂ : K₂ / Λ ≤ c₂ / 4 := by
    have h := mul_le_mul_of_nonneg_left hεB hK₂nn
    have h2 : K₂ * (1 / Λ) = K₂ / Λ := by ring
    have h3 : K₂ * (c₂ / (4 * (K₂ + 1))) ≤ c₂ / 4 := by
      rw [show K₂ * (c₂ / (4 * (K₂ + 1))) = c₂ * K₂ / (4 * (K₂ + 1)) by ring]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hc₂pos.le, hK₂nn]
    linarith [h, h2.le, h2.ge, h3]
  have hL₁v : (reConjCLM v + Λ • reConjCLM (Complex.I * v)) v = ‖v‖ ^ 2 := by
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, reConj_Iv_v,
      mul_zero, add_zero]
    exact reConjCLM_mul_self_re v
  have hL₂v : (reConjCLM v - Λ • reConjCLM (Complex.I * v)) v = ‖v‖ ^ 2 := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, reConj_Iv_v,
      mul_zero, sub_zero]
    exact reConjCLM_mul_self_re v
  refine ⟨reConjCLM v + Λ • reConjCLM (Complex.I * v),
    reConjCLM v - Λ • reConjCLM (Complex.I * v), min c₁ c₂ / (4 * ‖v‖), ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    rw [h0] at hL₁v
    simp only [ContinuousLinearMap.zero_apply] at hL₁v
    linarith [hWpos, hL₁v]
  · intro h0
    rw [h0] at hL₂v
    simp only [ContinuousLinearMap.zero_apply] at hL₂v
    linarith [hWpos, hL₂v]
  · exact div_pos (lt_min hc₁pos hc₂pos) (by positivity)
  · exact ⟨v, by rw [hL₁v]; exact hWpos, by rw [hL₂v]; exact hWpos⟩
  · intro u hL₁u hL₂u
    let s : ℝ := reConjCLM v u / ‖v‖ ^ 2
    let t : ℝ := reConjCLM (Complex.I * v) u / ‖v‖ ^ 2
    have hsval : s = reConjCLM v u / ‖v‖ ^ 2 := rfl
    have htval : t = reConjCLM (Complex.I * v) u / ‖v‖ ^ 2 := rfl
    have hsW : s * ‖v‖ ^ 2 = reConjCLM v u := by rw [hsval]; field_simp
    have htW : t * ‖v‖ ^ 2 = reConjCLM (Complex.I * v) u := by rw [htval]; field_simp
    have hL₁eval : (reConjCLM v + Λ • reConjCLM (Complex.I * v)) u
        = reConjCLM v u + Λ * reConjCLM (Complex.I * v) u := by
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hL₂eval : (reConjCLM v - Λ • reConjCLM (Complex.I * v)) u
        = reConjCLM v u - Λ * reConjCLM (Complex.I * v) u := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hcone₁ : 0 < s + Λ * t := by
      have h := hL₁u
      rw [hL₁eval, ← hsW, ← htW] at h
      nlinarith [h, hWpos]
    have hcone₂ : 0 < s - Λ * t := by
      have h := hL₂u
      rw [hL₂eval, ← hsW, ← htW] at h
      nlinarith [h, hWpos]
    have hspos : 0 < s := by linarith [hcone₁, hcone₂]
    have hΛne : Λ ≠ 0 := ne_of_gt hΛpos
    have hΛt : Λ * |t| ≤ s := by
      rw [← abs_of_pos hΛpos, ← abs_mul]
      exact abs_le.mpr ⟨by linarith [hcone₁], by linarith [hcone₂]⟩
    have h2t : 2 * |t| ≤ s := by nlinarith [hΛt, hΛ2, abs_nonneg t]
    have hsq : s ^ 2 + t ^ 2 ≤ (2 * s) ^ 2 := by
      nlinarith [h2t, abs_nonneg t, hspos, sq_abs t]
    have htK₁ : |t| * K₁ ≤ s * (c₁ / 4) := by
      have h1 : |t| * K₁ = (Λ * |t|) * (K₁ / Λ) := by field_simp
      rw [h1]
      exact mul_le_mul hΛt hKΛ₁ (by positivity) (le_of_lt hspos)
    have htK₂ : |t| * K₂ ≤ s * (c₂ / 4) := by
      have h1 : |t| * K₂ = (Λ * |t|) * (K₂ / Λ) := by field_simp
      rw [h1]
      exact mul_le_mul hΛt hKΛ₂ (by positivity) (le_of_lt hspos)
    have hdecomp : u = s • v + t • (Complex.I * v) := by
      have key := congrArg (fun z : ℂ => (‖v‖ ^ 2)⁻¹ • z) (smul_decomp v u)
      simp only [smul_smul, inv_mul_cancel₀ hWne, one_smul] at key
      rw [smul_add, smul_smul, smul_smul,
        show (‖v‖ ^ 2)⁻¹ * reConjCLM v u = s from by rw [hsval]; field_simp,
        show (‖v‖ ^ 2)⁻¹ * reConjCLM (Complex.I * v) u = t from by rw [htval]; field_simp]
        at key
      exact key
    have hnorm2 : ‖u‖ ^ 2 = (s ^ 2 + t ^ 2) * ‖v‖ ^ 2 := by
      have hinner1 : inner ℝ (s • v) (t • (Complex.I * v)) = 0 := by
        rw [real_inner_smul_left, real_inner_smul_right, inner_eq_reConj, reConj_v_Iv]
        ring
      have hnorm1 : ‖s • v‖ ^ 2 = s ^ 2 * ‖v‖ ^ 2 := by
        simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      have hnorm2' : ‖t • (Complex.I * v)‖ ^ 2 = t ^ 2 * ‖v‖ ^ 2 := by
        simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_mul, Complex.norm_I,
          one_mul]
      rw [hdecomp, norm_add_sq_real, hnorm1, hnorm2', hinner1]
      ring
    have hu_le : ‖u‖ ≤ 2 * s * ‖v‖ := by
      have h4 : ‖u‖ ^ 2 ≤ (2 * s * ‖v‖) ^ 2 := by
        rw [hnorm2]
        nlinarith [hsq, hWpos, sq_nonneg (2 * s * ‖v‖), sq_nonneg s]
      have h5 : 0 ≤ 2 * s * ‖v‖ := by positivity
      nlinarith [h4, h5, norm_nonneg u]
    have hsge : ‖u‖ / (2 * ‖v‖) ≤ s := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hu_le]
    have hN₁u : N₁ u = s * c₁ + t * N₁ (Complex.I * v) := by
      rw [hdecomp, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← hc₁eq]
    have hN₂u : N₂ u = s * c₂ + t * N₂ (Complex.I * v) := by
      rw [hdecomp, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← hc₂eq]
    have hstep₁ : s * c₁ / 2 ≤ N₁ u := by
      have h1 : -(|t| * K₁) ≤ t * N₁ (Complex.I * v) := by
        have h2 : |t * N₁ (Complex.I * v)| = |t| * K₁ := by rw [abs_mul, hK₁eq]
        linarith [neg_abs_le (t * N₁ (Complex.I * v)), h2.le, h2.ge]
      have h4 : -(s * (c₁ / 4)) ≤ t * N₁ (Complex.I * v) := by linarith [h1, htK₁]
      have h5 : s * c₁ - s * (c₁ / 4) ≤ N₁ u := by linarith [hN₁u, h4]
      have h6 : s * c₁ - s * (c₁ / 4) = s * c₁ * (3 / 4) := by ring
      have h7 : 0 < s * c₁ := mul_pos hspos hc₁pos
      linarith [h5, h6.le, h6.ge, h7]
    have hstep₂ : s * c₂ / 2 ≤ N₂ u := by
      have h1 : -(|t| * K₂) ≤ t * N₂ (Complex.I * v) := by
        have h2 : |t * N₂ (Complex.I * v)| = |t| * K₂ := by rw [abs_mul, hK₂eq]
        linarith [neg_abs_le (t * N₂ (Complex.I * v)), h2.le, h2.ge]
      have h4 : -(s * (c₂ / 4)) ≤ t * N₂ (Complex.I * v) := by linarith [h1, htK₂]
      have h5 : s * c₂ - s * (c₂ / 4) ≤ N₂ u := by linarith [hN₂u, h4]
      have h6 : s * c₂ - s * (c₂ / 4) = s * c₂ * (3 / 4) := by ring
      have h7 : 0 < s * c₂ := mul_pos hspos hc₂pos
      linarith [h5, h6.le, h6.ge, h7]
    constructor
    · have h7 : c₁ * ‖u‖ / (4 * ‖v‖) ≤ N₁ u := by
        have h8 : c₁ * ‖u‖ / (4 * ‖v‖) ≤ s * c₁ / 2 := by
          rw [div_le_iff₀ (by positivity)]
          have h1 : c₁ * ‖u‖ ≤ c₁ * (2 * s * ‖v‖) := mul_le_mul_of_nonneg_left hu_le hc₁pos.le
          have h2 : c₁ * (2 * s * ‖v‖) = s * c₁ / 2 * (4 * ‖v‖) := by ring
          linarith [h1, h2.le, h2.ge]
        linarith [h8, hstep₁]
      have h9 : min c₁ c₂ / (4 * ‖v‖) ≤ c₁ / (4 * ‖v‖) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h := mul_le_mul_of_nonneg_right (min_le_left c₁ c₂)
          (by positivity : (0 : ℝ) ≤ 4 * ‖v‖)
        linarith [h]
      have h10 : min c₁ c₂ / (4 * ‖v‖) * ‖u‖ ≤ c₁ / (4 * ‖v‖) * ‖u‖ :=
        mul_le_mul_of_nonneg_right h9 (norm_nonneg u)
      have h11 : c₁ / (4 * ‖v‖) * ‖u‖ = c₁ * ‖u‖ / (4 * ‖v‖) := by ring
      linarith [h10, h11.le, h11.ge, h7]
    · have h7 : c₂ * ‖u‖ / (4 * ‖v‖) ≤ N₂ u := by
        have h8 : c₂ * ‖u‖ / (4 * ‖v‖) ≤ s * c₂ / 2 := by
          rw [div_le_iff₀ (by positivity)]
          have h1 : c₂ * ‖u‖ ≤ c₂ * (2 * s * ‖v‖) := mul_le_mul_of_nonneg_left hu_le hc₂pos.le
          have h2 : c₂ * (2 * s * ‖v‖) = s * c₂ / 2 * (4 * ‖v‖) := by ring
          linarith [h1, h2.le, h2.ge]
        linarith [h8, hstep₂]
      have h9 : min c₁ c₂ / (4 * ‖v‖) ≤ c₂ / (4 * ‖v‖) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h := mul_le_mul_of_nonneg_right (min_le_right c₁ c₂)
          (by positivity : (0 : ℝ) ≤ 4 * ‖v‖)
        linarith [h]
      have h10 : min c₁ c₂ / (4 * ‖v‖) * ‖u‖ ≤ c₂ / (4 * ‖v‖) * ‖u‖ :=
        mul_le_mul_of_nonneg_right h9 (norm_nonneg u)
      have h11 : c₂ / (4 * ‖v‖) * ‖u‖ = c₂ * ‖u‖ / (4 * ‖v‖) := by ring
      linarith [h10, h11.le, h11.ge, h7]

end Crossing


section Crossing

variable {φ ψ : OpenPartialHomeomorph X ℂ} {a b : ℂ} {ρ σ : ℝ} {p : X}

set_option maxHeartbeats 1000000 in
/-- **The free-direction (transversal crossing) lemma for two chart balls.**

Let `φ, ψ` be atlas charts, `closedBall a ρ ⊆ φ.target`, `closedBall b σ ⊆ ψ.target`, and let `p`
be a point of `φ.source ∩ ψ.source` lying on both spheres: `‖φ p - a‖ = ρ`, `‖ψ p - b‖ = σ`.
Write `w₀ = φ p`, `A = ψ p - b`, `D = deriv (ψ ∘ φ.symm) w₀`.  If the two outward normal
functionals `N₁ u = Re (conj (w₀ - a) * u)` and `N₂ u = Re (conj A * D * u)` admit a common
positive direction `v` (so they are not negatively proportional, i.e. the two balls are not
externally tangent at `p`), then `p` satisfies the *sector* condition for the union. -/
theorem hasSectorBoundary_union_two_chartBall_of_freeDirection
    (hφ : φ ∈ atlas ℂ X) (hψ : ψ ∈ atlas ℂ X) (hρ : 0 < ρ) (hσ : 0 < σ)
    (hsubφ : Metric.closedBall a ρ ⊆ φ.target) (hsubψ : Metric.closedBall b σ ⊆ ψ.target)
    (hpφ : p ∈ φ.source) (hpψ : p ∈ ψ.source) (hsφ : ‖φ p - a‖ = ρ) (hsψ : ‖ψ p - b‖ = σ)
    (hfree : ∃ v : ℂ, 0 < (starRingEnd ℂ (φ p - a) * v).re ∧
      0 < (starRingEnd ℂ ((ψ p - b) * starRingEnd ℂ
        (deriv (fun w => ψ (φ.symm w)) (φ p))) * v).re) :
    Work.SimplyConnected.ABS.HasSectorBoundary
      (φ.symm '' Metric.ball a ρ ∪ ψ.symm '' Metric.ball b σ) p := by
  classical
  let w₀ : ℂ := φ p
  let A : ℂ := ψ p - b
  let g : ℂ → ℂ := fun w => ψ (φ.symm w)
  let D : ℂ := deriv g w₀
  have hw₀val : w₀ = φ p := rfl
  have hAval : A = ψ p - b := rfl
  have hDval : D = deriv (fun w => ψ (φ.symm w)) (φ p) := rfl
  -- the chart transition is analytic, hence differentiable
  have hAnal : AnalyticAt ℂ g w₀ := by
    have h1 : w₀ ∈ φ.target := by rw [hw₀val]; exact φ.map_source hpφ
    have h2 : φ.symm w₀ ∈ ψ.source := by
      rw [hw₀val, φ.left_inv hpφ]; exact hpψ
    have h := Submission.analyticAt_transition_of_mem_atlas (c := ψ) (d := φ) hψ hφ w₀ h1 h2
    simpa only [g] using h
  have hgw₀ : g w₀ = ψ p := by
    simp only [g]; rw [hw₀val, φ.left_inv hpφ]
  have hhasderiv : HasDerivAt g D w₀ := hasDerivAt_deriv_iff.mpr hAnal.differentiableAt
  have hlittle : (fun u : ℂ => g (w₀ + u) - g w₀ - u * D) =o[𝓝 0] (fun u : ℂ => u) := by
    have h := hhasderiv.isLittleO
    have htend : Tendsto (fun u : ℂ => w₀ + u) (𝓝 (0 : ℂ)) (𝓝 w₀) := by
      have h1 : Tendsto (fun _ : ℂ => w₀) (𝓝 (0 : ℂ)) (𝓝 w₀) := tendsto_const_nhds
      have h2 : Tendsto (fun u : ℂ => u) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := tendsto_id
      have h3 := h1.add h2
      simpa using h3
    have hcomp := h.comp_tendsto htend
    simp only [Function.comp_def] at hcomp
    have hfun : (fun u : ℂ => g (w₀ + u) - g w₀ - (w₀ + u - w₀) • D)
        = fun u : ℂ => g (w₀ + u) - g w₀ - u * D := by
      funext u; rw [add_sub_cancel_left, smul_eq_mul]
    have hfun2 : (fun u : ℂ => w₀ + u - w₀) = fun u : ℂ => u := by
      funext u; rw [add_sub_cancel_left]
    rw [hfun, hfun2] at hcomp
    exact hcomp
  -- the free direction: the two normal functionals are positive at `v`
  obtain ⟨v, hv₁, hv₂⟩ := hfree
  have hc₁ : 0 < reConjCLM (w₀ - a) v := by
    rw [reConjCLM_apply]
    simpa only [hw₀val] using hv₁
  have hc₂ : 0 < reConjCLM (A * starRingEnd ℂ D) v := by
    rw [reConjCLM_apply]
    simpa only [hAval, hDval, g, hw₀val] using hv₂
  -- the thin cone on which both functionals dominate the norm
  obtain ⟨L₁, L₂, κ, hL₁ne, hL₂ne, hκpos, hwit, hbound⟩ :=
    exists_cone_of_two_positive hc₁ hc₂
  -- the quadratic remainder of the transition is absorbed by the linear term
  let η : ℝ := κ / (4 * ‖A‖)
  have hAσ : ‖A‖ = σ := by rw [hAval]; exact hsψ
  have hApos : 0 < ‖A‖ := by rw [hAσ]; exact hσ
  have hηpos : 0 < η := div_pos hκpos (by positivity)
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.eventually_nhds_iff.mp (hlittle.bound hηpos)
  let δ : ℝ := min δ₁ (κ / (4 * (‖D‖ + η) ^ 2 + 1))
  have hδpos : 0 < δ := lt_min hδ₁pos (by positivity)
  refine ⟨φ, φ.source ∩ ψ.source ∩ (φ.source ∩ φ ⁻¹' Metric.ball w₀ δ), L₁, L₂, hφ, ?_, ?_, ?_,
    hpφ, hL₁ne, hL₂ne, hwit, ?_⟩
  · refine IsOpen.inter ?_ ?_
    · exact φ.open_source.inter ψ.open_source
    · exact φ.continuousOn.isOpen_inter_preimage φ.open_source Metric.isOpen_ball
  · exact ⟨⟨hpφ, hpψ⟩, hpφ, Metric.mem_ball_self hδpos⟩
  · intro x hx; exact hx.1.1
  · rintro x ⟨hxU, hxV⟩ ⟨h1, h2⟩
    obtain ⟨⟨hxφ, hxψ⟩, hxsφ, hxball⟩ := hxV
    let u : ℂ := φ x - w₀
    have huval : u = φ x - w₀ := rfl
    have hu₁ : 0 < L₁ u := h1
    have hu₂ : 0 < L₂ u := h2
    obtain ⟨hb₁, hb₂⟩ := hbound u hu₁ hu₂
    have hune : u ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hu₁
      exact lt_irrefl 0 hu₁
    have hκu : 0 < κ * ‖u‖ := mul_pos hκpos (norm_pos_iff.mpr hune)
    have hxball' : ‖u‖ < δ := by
      have h := Metric.mem_ball.mp hxball
      rw [dist_eq_norm] at h
      rwa [← huval] at h
    rcases hxU with hxB₁ | hxB₂
    · -- `x` lies in the first ball: the exact quadratic identity gives `N₁ u ≤ 0`
      obtain ⟨y, hy, hxy⟩ := hxB₁
      have hφx : φ x = y := by
        rw [← hxy, φ.right_inv]
        exact hsubφ (Metric.ball_subset_closedBall hy)
      have hybd : ‖y - a‖ < ρ := by
        have h := Metric.mem_ball.mp hy
        rwa [dist_eq_norm] at h
      have hlt : ‖φ x - a‖ < ‖w₀ - a‖ := by
        rw [hφx, show ‖w₀ - a‖ = ρ from hsφ]
        exact hybd
      have hinner : inner ℝ (w₀ - a) u ≤ 0 := by
        have h := Work.SimplyConnected.ABS.inner_le_zero_of_norm_lt (y := φ x) (q := w₀)
          (a := a) hlt
        simpa only [huval] using h
      have hN₁u : reConjCLM (w₀ - a) u ≤ 0 := by
        rwa [inner_eq_reConj] at hinner
      linarith [hb₁, hκu, hN₁u]
    · -- `x` lies in the second ball: the Taylor remainder of the transition is absorbed
      obtain ⟨y, hy, hxy⟩ := hxB₂
      have hψx : ψ x = y := by
        rw [← hxy, ψ.right_inv]
        exact hsubψ (Metric.ball_subset_closedBall hy)
      have hybd : ‖y - b‖ < σ := by
        have h := Metric.mem_ball.mp hy
        rwa [dist_eq_norm] at h
      have hzu : w₀ + u = φ x := by rw [huval]; ring
      have hgφx : g (φ x) = ψ x := by
        simp only [g]; rw [φ.left_inv hxφ]
      let z : ℂ := g (w₀ + u) - g w₀
      let R : ℂ := z - u * D
      have hzR : z = u * D + R := by simp only [R]; ring
      have hzA : ‖z + A‖ < ‖A‖ := by
        have h1 : z + A = g (φ x) - b := by
          simp only [z, hzu, A, hgw₀]; ring
        have h2 : g (φ x) - b = y - b := by rw [hgφx, hψx]
        rw [h1, h2, show ‖A‖ = σ from hAσ]
        exact hybd
      have hinner : inner ℝ z A < 0 := by
        have h2 : ‖z + A‖ ^ 2 < ‖A‖ ^ 2 := by
          nlinarith [norm_nonneg (z + A), norm_nonneg A, hzA]
        have h3 : ‖z + A‖ ^ 2 = ‖z‖ ^ 2 + 2 * inner ℝ z A + ‖A‖ ^ 2 := norm_add_sq_real z A
        nlinarith [h2, h3, sq_nonneg ‖z‖]
      have hsplit : inner ℝ z A = reConjCLM (A * starRingEnd ℂ D) u + inner ℝ R A := by
        rw [hzR, inner_add_left, inner_mul_right_eq]
      have hRbd : ‖R‖ ≤ η * ‖u‖ := by
        have hd : dist u 0 < δ₁ := by
          rw [dist_eq_norm, sub_zero]
          exact lt_of_lt_of_le hxball' (min_le_left _ _)
        exact hδ₁ hd
      have hRinner : -inner ℝ R A ≤ η * ‖u‖ * ‖A‖ := by
        have h1 : -inner ℝ R A ≤ |inner ℝ R A| := neg_le_abs _
        have h2 : |inner ℝ R A| ≤ ‖R‖ * ‖A‖ := abs_real_inner_le_norm R A
        have h3 : ‖R‖ * ‖A‖ ≤ η * ‖u‖ * ‖A‖ :=
          mul_le_mul_of_nonneg_right hRbd (norm_nonneg A)
        linarith
      have hkey : κ * ‖u‖ < η * ‖u‖ * ‖A‖ := by
        have h4 : reConjCLM (A * starRingEnd ℂ D) u < η * ‖u‖ * ‖A‖ := by
          linarith [hsplit, hinner, hRinner]
        linarith [hb₂, h4]
      have hcon : κ < η * ‖A‖ := by
        have hu := norm_pos_iff.mpr hune
        nlinarith [hkey, hu]
      have hηA : η * ‖A‖ = κ / 4 := by
        simp only [η]; field_simp
      rw [hηA] at hcon
      linarith [hκpos]

end Crossing

end Work.SimplyConnected.ABS.green_reduction
