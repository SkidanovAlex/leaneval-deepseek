import Mathlib
import Submission.Work.KMTAreas.A4.lipL1TailCaseBAux

set_option autoImplicit false
set_option maxHeartbeats 400000000
set_option maxRecDepth 20000

open scoped BigOperators FourierTransform
open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

theorem lipL1TailCaseBA (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree)
    (hPel : Work.KMTContract.PeluseInverseKMT P) :
    ∀ (A : ℝ), 1 ≤ A → ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
      ∀ (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
        (N : ℝ) ^ P.natDegree / A ≤ (N₀ : ℝ) →
        (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree →
        Work.Analysis.InverseTheory.SupportIn f N₀ →
        Work.Analysis.InverseTheory.SupportIn g N₀ →
        Work.Analysis.InverseTheory.SupportIn h N₀ →
        (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
        δ * (N : ℝ) ^ P.natDegree ≤ ‖Work.Analysis.InverseTheory.bilinPair
          (Work.Analysis.InverseTheory.AhalfZ N P f g) h‖ →
        C * δ⁻¹ ^ K < N →
        ∃ (F : ℤ → ℂ) (l : ℕ) (k : ℤ),
          (∀ x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K) ∧
          Summable (fun x : ℤ => ‖F x‖) ∧
          (∑' x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧
          (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖F x‖ else 0)
            ≤ δ ^ K * (N : ℝ) ^ P.natDegree / 2) ∧
          Work.Analysis.InverseTheory.FourierSupportIn F
            (Work.Analysis.InverseTheory.majorArc ρ l k) ∧
          (2 : ℝ) ^ l ≤ C * δ⁻¹ ^ K ∧
          (2 : ℝ) ^ k ≤ C * δ⁻¹ ^ K / (N : ℝ) ∧
          δ ^ K * (N : ℝ) ^ P.natDegree ≤ ‖Work.Analysis.InverseTheory.bilinPair f F‖ := by
  intro A hA
  classical
  obtain ⟨ψ, hψint, hψsupp⟩ := lipSchwartzExists
  obtain ⟨Kw, hKwpos, hKw⟩ := lipWeightTsumLe ψ
  obtain ⟨Cm, hCmpos, hCm⟩ := lipWeightAbsMoment ψ
  obtain ⟨C₀, K₀, hC₀pos, hK₀pos, hPel'⟩ := hPel A hA
  set u : ℕ := Nat.ceil K₀ + 1 with hudef
  have hu_ge : K₀ ≤ (u : ℝ) := by
    rw [hudef]; push_cast
    have := Nat.le_ceil K₀; linarith
  have hu1 : 1 ≤ u := by rw [hudef]; omega
  set Kc : ℕ := 5 * u + 6 with hKcdef
  have hKcu : u ≤ Kc := by rw [hKcdef]; omega
  have hKc2u : 2 * u ≤ Kc := by rw [hKcdef]; omega
  have hKc3u : 3 * u ≤ Kc := by rw [hKcdef]; omega
  have hKc4u : 4 * u ≤ Kc := by rw [hKcdef]; omega
  have hKcpos : (0 : ℝ) < (Kc : ℝ) := by positivity
  have hKcK₀ : K₀ ≤ (Kc : ℝ) := by
    have h2 : (u : ℝ) ≤ (Kc : ℝ) := by exact_mod_cast hKcu
    linarith
  set K' : ℝ := 2 * A + 5 + 2 * C₀ with hK'def
  have hK'pos : 0 < K' := by rw [hK'def]; linarith
  have hK'1 : 1 ≤ K' := by rw [hK'def]; linarith
  have hfour : 0 < 4 * C₀ * calcConst ψ * K' := by
    exact mul_pos (mul_pos (mul_pos (by norm_num) hC₀pos) (calcConst_pos ψ)) hK'pos
  set c₁ : ℝ := 1 + 4 * C₀ * calcConst ψ * K' with hc₁def
  have hc₁pos : 0 < c₁ := by rw [hc₁def]; linarith
  have hc₁1 : 1 ≤ c₁ := by rw [hc₁def]; linarith
  have hc₁big : 4 * C₀ * calcConst ψ * K' ≤ c₁ ^ 10 := by
    have h2 : 4 * C₀ * calcConst ψ * K' ≤ c₁ := by rw [hc₁def]; linarith
    calc 4 * C₀ * calcConst ψ * K' ≤ c₁ := h2
      _ ≤ c₁ ^ 10 := le_self_pow₀ hc₁1 (by norm_num)
  set c₂ : ℝ := 4 * C₀ ^ 2 * calcConst ψ * K' with hc₂def
  have hc₂pos : 0 < c₂ := by
    rw [hc₂def]
    exact mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hC₀pos 2)) (calcConst_pos ψ)) hK'pos
  set Bc : ℝ := c₁ * c₂ + 2 * c₂ + 2 * C₀ + 16 * C₀ * Cm + 16 * C₀ ^ 2
      + 16 * C₀ ^ 2 * Cm * c₁ + 8 * C₀ ^ 2 * Cm * c₁ + 4 * C₀ * Kw * K' + 4 * C₀ * Kw
      + 2 * C₀ * Kw * K' + 100 with hBcdef
  have hn1 : (0 : ℝ) ≤ c₁ * c₂ := mul_nonneg hc₁pos.le hc₂pos.le
  have hn2 : (0 : ℝ) ≤ 2 * c₂ := by linarith
  have hn3 : (0 : ℝ) ≤ 2 * C₀ := by linarith
  have hn4 : (0 : ℝ) ≤ 16 * C₀ * Cm :=
    mul_nonneg (mul_nonneg (by norm_num) hC₀pos.le) hCmpos.le
  have hn5 : (0 : ℝ) ≤ 16 * C₀ ^ 2 := mul_nonneg (by norm_num) (sq_nonneg C₀)
  have hn6 : (0 : ℝ) ≤ 16 * C₀ ^ 2 * Cm * c₁ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg C₀)) hCmpos.le) hc₁pos.le
  have hn7 : (0 : ℝ) ≤ 8 * C₀ ^ 2 * Cm * c₁ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg C₀)) hCmpos.le) hc₁pos.le
  have hn8 : (0 : ℝ) ≤ 4 * C₀ * Kw * K' :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₀pos.le) hKwpos.le) hK'pos.le
  have hn9 : (0 : ℝ) ≤ 4 * C₀ * Kw :=
    mul_nonneg (mul_nonneg (by norm_num) hC₀pos.le) hKwpos.le
  have hn10 : (0 : ℝ) ≤ 2 * C₀ * Kw * K' :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₀pos.le) hKwpos.le) hK'pos.le
  have hBc100 : (100 : ℝ) ≤ Bc := by
    rw [hBcdef]
    linarith only [hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10]
  have hBc0 : (0 : ℝ) ≤ Bc := le_trans (by norm_num) hBc100
  have hA2 : (1 : ℝ) ≤ 2 * A + 3 := by linarith
  set Cc : ℝ := (2 * A + 3) * Bc with hCcdef
  have hCcpos : 0 < Cc := mul_pos (by linarith) (lt_of_lt_of_le (by norm_num) hBc100)
  have hBcle : Bc ≤ Cc := by
    rw [hCcdef]
    calc Bc = 1 * Bc := by ring
      _ ≤ (2 * A + 3) * Bc := mul_le_mul_of_nonneg_right hA2 hBc0
  have hCc7 : 7 ≤ Cc := le_trans (by norm_num) (le_trans hBc100 hBcle)
  have hCcC₀ : C₀ ≤ Cc := by
    refine le_trans ?_ hBcle; rw [hBcdef]
    linarith only [hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10]
  have hCc2C₀ : 2 * C₀ ≤ Cc := by
    refine le_trans ?_ hBcle; rw [hBcdef]
    linarith only [hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10]
  have hCcc₁c₂ : c₁ * c₂ ≤ Cc := by
    refine le_trans ?_ hBcle; rw [hBcdef]
    linarith only [hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10]
  have hCc2c₂ : 2 * c₂ ≤ Cc := by
    refine le_trans ?_ hBcle; rw [hBcdef]
    linarith only [hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10]
  have hCcKw : 2 * C₀ * Kw * K' ≤ Cc := by
    refine le_trans ?_ hBcle; rw [hBcdef]
    linarith only [hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10]
  have h4C₀Kw : 4 * C₀ * Kw ≤ Cc := by
    refine le_trans ?_ hBcle; rw [hBcdef]
    linarith only [hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10]
  have h4C₀KwK' : 4 * C₀ * Kw * K' ≤ Cc := by
    refine le_trans ?_ hBcle; rw [hBcdef]
    linarith only [hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10]
  have h16C₀Cm : 16 * C₀ * Cm ≤ Cc := by
    refine le_trans ?_ hBcle; rw [hBcdef]
    linarith only [hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10]
  have h16C₀₂Cmc₁ : 16 * C₀ ^ 2 * Cm * c₁ ≤ Cc := by
    refine le_trans ?_ hBcle; rw [hBcdef]
    linarith only [hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10]
  have h16C₀sq : 16 * C₀ ^ 2 ≤ Cc := by
    refine le_trans ?_ hBcle; rw [hBcdef]
    linarith only [hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10]
  refine ⟨Cc, (Kc : ℝ), hCcpos, hKcpos, ?_⟩
  intro ρ hρpos hρle N N₀ δ f g h hN hδpos hδle hN₀lo hN₀hi hfs hgs hhs hfb hgb hhb hcorr
    hcaseB
  rw [Real.rpow_natCast] at hcaseB
  have hD1 : (1 : ℝ) ≤ δ⁻¹ := by rw [one_le_inv₀ hδpos]; exact hδle
  have hDpos : 0 < δ⁻¹ := inv_pos.mpr hδpos
  rcases hPel' N N₀ δ f g h hN hδpos hδle hN₀hi hfs hgs hhs hfb hgb hhb hcorr with hs | hbig
  · exfalso
    have hNbig : C₀ * δ⁻¹ ^ K₀ < N := by
      have h3 : δ⁻¹ ^ K₀ ≤ (δ⁻¹) ^ Kc := by
        simpa only [Real.rpow_natCast] using
          Real.rpow_le_rpow_of_exponent_le hD1 hKcK₀
      calc C₀ * δ⁻¹ ^ K₀ ≤ Cc * δ⁻¹ ^ K₀ :=
            mul_le_mul_of_nonneg_right hCcC₀ (Real.rpow_nonneg hDpos.le K₀)
        _ ≤ Cc * (δ⁻¹) ^ Kc := mul_le_mul_of_nonneg_left h3 hCcpos.le
        _ < (N : ℝ) := hcaseB
    linarith
  · obtain ⟨q, N', hq1, hqle, hN'1, hN'le, hN'lb, hA1⟩ := hbig
    simpa only [Real.rpow_natCast] using lipL1TailCaseB_window P hP ψ Kw Cm C₀ K₀ u Kc K' c₁ c₂ Cc A hψint hψsupp hKwpos hKw hCmpos hCm
      hC₀pos hK₀pos hu_ge hu1 hKcu hKc2u hKc3u hKc4u hKcpos hKcK₀ hK'def hK'pos hK'1 hfour
      hc₁pos hc₁1 hc₁big hc₂pos hc₂def hCcpos hCc2C₀ hCcC₀ hCc7 hCcKw hCcc₁c₂ hCc2c₂
      h4C₀Kw h4C₀KwK' h16C₀₂Cmc₁ h16C₀Cm h16C₀sq hA ρ hρpos hρle N N₀ δ f g h hN hδpos hδle
      hN₀hi hfs hfb q N' hq1 hqle hN'1 hN'le hN'lb hA1 hcaseB


end Work.KMTAreas.A4
