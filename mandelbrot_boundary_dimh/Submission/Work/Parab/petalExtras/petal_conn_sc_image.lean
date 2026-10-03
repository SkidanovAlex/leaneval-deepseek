import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Exist.fatouCoordW_image_bdd

namespace Work.Parab.petalExtras

open Set Metric

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# Connectivity and simply connectedness of a Fatou petal, and its image under the chart

For a parabolic germ `f z = z + z ^ 2 * h z` satisfying the quantitative hypotheses
`ParabolicBounds`, and for `0 < M` with `1 / r < M`, the petal
`Petal r M = {z | ‖z‖ < r ∧ z.re < -M * normSq z}` is *exactly* the open disc
`ball (-(2M)⁻¹) (2M)⁻¹`: the condition `z.re < -M * normSq z` defines the disc with diameter
`[-1/M, 0]`, and `1 / r < M` makes `ball 0 r` redundant.

Consequently the petal is connected and, being an open disc, contractible, hence simply
connected.  Finally the Fatou coordinate `Φ = fatouCoord f (1 - a)` restricted to the petal is
onto the tail of every horizontal strip: this is `fatouCoordW_image_bdd` transported along the
chart `w = -1/z` (a preimage `w` with `Re w > M` has `1 / r < M < Re w ≤ ‖w‖`, so
`chart w ∈ Petal r M`).
-/

/-- For `M > 0` and `1 / M < r` the petal `Petal r M` is the open disc of diameter `[-1/M, 0]`;
equivalently `Petal r M = ball (-(2M)⁻¹) (2M)⁻¹`. -/
lemma petal_eq_ball {r M : ℝ} (hM : 0 < M) (hrM : 1 / M < r) :
    Work.FatouCoord.Petal r M = Metric.ball (-(((2 * M)⁻¹ : ℝ) : ℂ)) ((2 * M)⁻¹) := by
  have hc : 0 < (2 * M)⁻¹ := by positivity
  have h2M : 0 < 2 * M := by positivity
  have hinv : (2 * M) * (2 * M)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt h2M)
  ext z
  rw [Work.FatouCoord.mem_Petal, Metric.mem_ball, dist_eq_norm, sub_neg_eq_add]
  have key : ‖z + (((2 * M)⁻¹ : ℝ) : ℂ)‖ < (2 * M)⁻¹ ↔ z.re < -M * Complex.normSq z := by
    have hsq : ‖z + (((2 * M)⁻¹ : ℝ) : ℂ)‖ ^ 2
        = Complex.normSq z + 2 * (2 * M)⁻¹ * z.re + (2 * M)⁻¹ * (2 * M)⁻¹ := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.conj_ofReal,
        Complex.normSq_ofReal]
      have hm : (z * (((2 * M)⁻¹ : ℝ) : ℂ)).re = (2 * M)⁻¹ * z.re := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [hm]; ring
    have hiff : ‖z + (((2 * M)⁻¹ : ℝ) : ℂ)‖ < (2 * M)⁻¹
        ↔ ‖z + (((2 * M)⁻¹ : ℝ) : ℂ)‖ ^ 2 < ((2 * M)⁻¹) ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg _) (le_of_lt hc)).symm
    have hsq' : (2 * M)⁻¹ * (2 * M)⁻¹ = ((2 * M)⁻¹) ^ 2 := by ring
    rw [hiff, hsq, hsq']
    constructor <;> intro h <;> nlinarith [Complex.normSq_nonneg z, hinv, hM, hc]
  rw [key]
  constructor
  · rintro ⟨_, h2⟩; exact h2
  · intro hA
    have hball : ‖z + (((2 * M)⁻¹ : ℝ) : ℂ)‖ < (2 * M)⁻¹ := key.mpr hA
    refine ⟨?_, hA⟩
    have hnormc : ‖(((2 * M)⁻¹ : ℝ) : ℂ)‖ = (2 * M)⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (le_of_lt hc)
    have h1 : ‖z‖ ≤ ‖z + (((2 * M)⁻¹ : ℝ) : ℂ)‖ + (2 * M)⁻¹ := by
      have h := norm_sub_le (z + (((2 * M)⁻¹ : ℝ) : ℂ)) (((2 * M)⁻¹ : ℝ) : ℂ)
      rw [add_sub_cancel_right] at h
      linarith [hnormc]
    have h2inv : (2 * M)⁻¹ + (2 * M)⁻¹ = 1 / M := by
      have hM0 : M ≠ 0 := ne_of_gt hM
      field_simp
      ring
    rw [← h2inv] at hrM
    linarith

theorem petal_conn_sc_image {f : ℂ → ℂ} {h : ℂ → ℂ} {a : ℂ} {r A A' M : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') (hM : 0 < M) (hMr : 1 / r < M)
    {Φ : ℂ → ℂ}
    (hΦ : ∀ z ∈ Work.FatouCoord.Petal r M, Φ z = Work.FatouCoord.fatouCoord f (1 - a) z) :
    IsConnected (Work.FatouCoord.Petal r M) ∧
    SimplyConnectedSpace (Work.FatouCoord.Petal r M) ∧
    (∀ b : ℝ, ∃ C : ℝ, ∀ w : ℂ, C < w.re → |w.im| ≤ b →
      ∃ z ∈ Work.FatouCoord.Petal r M, Φ z = w) := by
  have hr : 0 < r := hb.hr
  have hrM : 1 / M < r := by
    have h1 : 1 < M * r := (div_lt_iff₀ hr).mp hMr
    rw [div_lt_iff₀ hM]
    linarith
  have hρ : 0 < (2 * M)⁻¹ := by positivity
  have hball := petal_eq_ball (r := r) (M := M) hM hrM
  refine ⟨?_, ?_, ?_⟩
  · rw [hball]
    exact Metric.isConnected_ball hρ
  · haveI : ContractibleSpace ↥(Metric.ball (-(((2 * M)⁻¹ : ℝ) : ℂ)) ((2 * M)⁻¹)) :=
      Metric.contractibleSpace_ball hρ
    rw [hball]
    infer_instance
  · intro b
    obtain ⟨C, hC⟩ := Work.FatouCoord.Exist.fatouCoordW_image_bdd hb M b
    refine ⟨C, ?_⟩
    intro w hw hwim
    obtain ⟨v, hvM, hvψ⟩ := hC w hw hwim
    have hv0 : v ≠ 0 := by
      intro hv
      rw [hv] at hvM
      simp at hvM
      linarith
    have hz : Work.FatouCoord.chart v ∈ Work.FatouCoord.Petal r M := by
      rw [Work.FatouCoord.Petal_eq_preimage_chart hr, Set.mem_preimage,
        Work.FatouCoord.chart_chart hv0]
      exact ⟨hvM, by linarith [Complex.re_le_norm v]⟩
    exact ⟨Work.FatouCoord.chart v, hz,
      (hΦ (Work.FatouCoord.chart v) hz).trans
        ((Work.FatouCoord.fatouCoord_eq (Work.FatouCoord.chart v)).trans
          (by rw [Work.FatouCoord.chart_chart hv0]; exact hvψ))⟩

end Work.Parab.petalExtras
