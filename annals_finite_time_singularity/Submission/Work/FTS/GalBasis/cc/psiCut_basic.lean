/-
# `Work.FTS.GalBasis.cc.psiCut_basic` — the elementary properties of the cutoff family

This module proves the four *structural* clauses of `psiCut_spec` for the explicit family
`psiCut N z θ = cutA N z * cutB N θ` of `CutDefs`:

* joint smoothness of `(z,θ) ↦ psiCut N z θ`;
* the range `0 ≤ psiCut N z θ ≤ 1`;
* the value `1` on the plateau `InPlateau N`;
* the value `0` off the outer box `OffBox N`.

All four follow immediately from the corresponding properties of `Real.smoothTransition`
(`contDiff`, `nonneg`, `le_one`, `zero_of_nonpos`, `one_of_one_le`) together with the
elementary affine comparisons between the mesh `1/(N+1)`, the plateau ends `plo`,`phiN`,`qlo`,
`qhi` and the box ends `zlo`,`zhi`,`tlo`,`thi`.  The remaining clauses of `psiCut_spec` (the
uniform bound on the mixed derivatives of order `≤ 4` and the vanishing of the `θ`-derivatives
outside the angular layers) are proved in the companion modules.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.GalBasis.cc.CutDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.GalBasis.cc

/-- `(N : ℝ) + 1` is positive for every `N : ℕ`; this is the only arithmetic input, needed to
clear the mesh `1/(N+1)`. -/
private lemma one_add_natCast_pos (N : ℕ) : (0 : ℝ) < (N : ℝ) + 1 := by positivity

/-! ## Smoothness -/

private lemma contDiff_cutA (N : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (cutA N) := by
  unfold cutA
  fun_prop

private lemma contDiff_cutB (N : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (cutB N) := by
  unfold cutB
  fun_prop

/-! ## The range `[0,1]` -/

private lemma cutA_bounds (N : ℕ) (z : ℝ) : 0 ≤ cutA N z ∧ cutA N z ≤ 1 := by
  have h1 : 0 ≤ cutA N z := by
    unfold cutA
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  refine ⟨h1, ?_⟩
  unfold cutA
  calc Real.smoothTransition (((N : ℝ) + 1) * z - 1)
        * Real.smoothTransition (2 - z / ((N : ℝ) + 1))
      ≤ 1 * 1 := mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
          (Real.smoothTransition.nonneg _) zero_le_one
    _ = 1 := by norm_num

private lemma cutB_bounds (N : ℕ) (θ : ℝ) : 0 ≤ cutB N θ ∧ cutB N θ ≤ 1 := by
  have h1 : 0 ≤ cutB N θ := by
    unfold cutB
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  refine ⟨h1, ?_⟩
  unfold cutB
  calc Real.smoothTransition (((N : ℝ) + 1) * θ - 1)
        * Real.smoothTransition (((N : ℝ) + 1) * (Real.pi / 2 - θ) - 1)
      ≤ 1 * 1 := mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
          (Real.smoothTransition.nonneg _) zero_le_one
    _ = 1 := by norm_num

/-! ## The value `1` on the plateau -/

private lemma cutA_eq_one (N : ℕ) {z : ℝ} (hz1 : plo N ≤ z) (hz2 : z ≤ phiN N) :
    cutA N z = 1 := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := one_add_natCast_pos N
  have h1 : (1 : ℝ) ≤ ((N : ℝ) + 1) * z - 1 := by
    have h : 2 ≤ ((N : ℝ) + 1) * z := by
      rw [plo, div_le_iff₀ hN] at hz1
      linarith [hz1]
    linarith
  have h2 : (1 : ℝ) ≤ 2 - z / ((N : ℝ) + 1) := by
    have h : z / ((N : ℝ) + 1) ≤ 1 := (div_le_one hN).mpr (by simpa only [phiN] using hz2)
    linarith
  unfold cutA
  rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2]
  ring

private lemma cutB_eq_one (N : ℕ) {θ : ℝ} (hθ1 : qlo N ≤ θ) (hθ2 : θ ≤ qhi N) :
    cutB N θ = 1 := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := one_add_natCast_pos N
  have h1 : (1 : ℝ) ≤ ((N : ℝ) + 1) * θ - 1 := by
    have h : 2 ≤ ((N : ℝ) + 1) * θ := by
      rw [qlo, div_le_iff₀ hN] at hθ1
      linarith [hθ1]
    linarith
  have h2 : (1 : ℝ) ≤ ((N : ℝ) + 1) * (Real.pi / 2 - θ) - 1 := by
    have h : 2 / ((N : ℝ) + 1) ≤ Real.pi / 2 - θ := by
      have h' := hθ2
      rw [qhi] at h'
      linarith
    rw [div_le_iff₀ hN] at h
    linarith [h]
  unfold cutB
  rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2]
  ring

/-! ## The value `0` off the outer box -/

private lemma cutA_eq_zero_of_lt_zlo (N : ℕ) {z : ℝ} (hz : z < zlo N) : cutA N z = 0 := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := one_add_natCast_pos N
  have hlt : ((N : ℝ) + 1) * z - 1 < 0 := by
    have h2 : z < 1 / ((N : ℝ) + 1) := by simpa only [zlo] using hz
    have h3 : z * ((N : ℝ) + 1) < 1 := (lt_div_iff₀ hN).mp h2
    nlinarith
  unfold cutA
  rw [Real.smoothTransition.zero_of_nonpos (le_of_lt hlt)]
  ring

private lemma cutA_eq_zero_of_zhi_lt (N : ℕ) {z : ℝ} (hz : zhi N < z) : cutA N z = 0 := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := one_add_natCast_pos N
  have hlt : 2 - z / ((N : ℝ) + 1) < 0 := by
    have h2 : 2 * ((N : ℝ) + 1) < z := by simpa only [zhi] using hz
    have h3 : 2 < z / ((N : ℝ) + 1) := by rw [lt_div_iff₀ hN]; exact h2
    linarith
  unfold cutA
  rw [Real.smoothTransition.zero_of_nonpos (le_of_lt hlt)]
  ring

private lemma cutB_eq_zero_of_lt_tlo (N : ℕ) {θ : ℝ} (hθ : θ < tlo N) : cutB N θ = 0 := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := one_add_natCast_pos N
  have hlt : ((N : ℝ) + 1) * θ - 1 < 0 := by
    have h2 : θ < 1 / ((N : ℝ) + 1) := by simpa only [tlo] using hθ
    have h3 : θ * ((N : ℝ) + 1) < 1 := (lt_div_iff₀ hN).mp h2
    nlinarith
  unfold cutB
  rw [Real.smoothTransition.zero_of_nonpos (le_of_lt hlt)]
  ring

private lemma cutB_eq_zero_of_thi_lt (N : ℕ) {θ : ℝ} (hθ : thi N < θ) : cutB N θ = 0 := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := one_add_natCast_pos N
  have hlt : ((N : ℝ) + 1) * (Real.pi / 2 - θ) - 1 < 0 := by
    have h2 : Real.pi / 2 - 1 / ((N : ℝ) + 1) < θ := by simpa only [thi] using hθ
    have h3 : Real.pi / 2 - θ < 1 / ((N : ℝ) + 1) := by linarith
    have h4 : (Real.pi / 2 - θ) * ((N : ℝ) + 1) < 1 := (lt_div_iff₀ hN).mp h3
    nlinarith
  unfold cutB
  rw [Real.smoothTransition.zero_of_nonpos (le_of_lt hlt)]
  ring

/-! ## The four clauses -/

theorem psiCut_basic : ∀ N : ℕ,
      ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (psiCut N)) ∧
      (∀ z θ : ℝ, 0 ≤ psiCut N z θ ∧ psiCut N z θ ≤ 1) ∧
      (∀ z θ : ℝ, InPlateau N z θ → psiCut N z θ = 1) ∧
      (∀ z θ : ℝ, OffBox N z θ → psiCut N z θ = 0) := by
  intro N
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold psiCut cutA cutB Function.uncurry
    fun_prop
  · intro z θ
    obtain ⟨hA1, hA2⟩ := cutA_bounds N z
    obtain ⟨hB1, hB2⟩ := cutB_bounds N θ
    unfold psiCut
    exact ⟨mul_nonneg hA1 hB1, by
      calc cutA N z * cutB N θ ≤ 1 * 1 := mul_le_mul hA2 hB2 hB1 zero_le_one
        _ = 1 := by norm_num⟩
  · intro z θ h
    obtain ⟨hz, hθ⟩ := h
    simp only [Set.mem_Icc] at hz hθ
    unfold psiCut
    rw [cutA_eq_one N hz.1 hz.2, cutB_eq_one N hθ.1 hθ.2]
    ring
  · intro z θ h
    rcases h with hz | hθ
    · simp only [Set.mem_Icc, not_and_or, not_le] at hz
      rcases hz with hz | hz
      · unfold psiCut
        rw [cutA_eq_zero_of_lt_zlo N hz]
        ring
      · unfold psiCut
        rw [cutA_eq_zero_of_zhi_lt N hz]
        ring
    · simp only [Set.mem_Icc, not_and_or, not_le] at hθ
      rcases hθ with hθ | hθ
      · unfold psiCut
        rw [cutB_eq_zero_of_lt_tlo N hθ]
        ring
      · unfold psiCut
        rw [cutB_eq_zero_of_thi_lt N hθ]
        ring

end Work.FTS.GalBasis.cc
