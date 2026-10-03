/-
# `L¹` bound for `λ_k' · (η_{≤jj})'`

For `k ≤ 0 ≤ jj` with `k + jj ≥ 0` the rescaled cutoff `η_{≤jj}'` is supported where
`2^{jj-1} ≤ |x|` (it vanishes below the inner radius of the cutoff), and it is bounded by an
absolute constant uniformly in `jj`.  Hence

  `∫⁻ ‖λ_k' · (η_{≤jj})'‖ ≤ C · ∫⁻_{2^{jj-1} ≤ |x|} ‖λ_k'‖`,

and the derivative tail estimate `offLamTail 1 N` for the rescaled kernel `λ_k = 𝓕⁻ η_{≤k}`
(bounded by `C₁ · 2^k · (max (2^k · 2^{jj-1}) 1)^{-N}`) gives the claim, since
`2^k · 2^{jj-1} = 2^{k+jj-1}`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.offBDerivBound

namespace Work.KMTAreas.A4

open MeasureTheory Filter
open scoped ENNReal Topology

theorem integralDerivLamMulDerivBmpLe (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (k jj : ℤ), k ≤ 0 → 0 ≤ jj → 0 ≤ k + jj → ∫⁻ x : ℝ, ‖deriv (Work.KMTAreas.A4.lam k) x * deriv (Work.KMTAreas.A4.bmp jj) x‖ₑ ≤ ENNReal.ofReal (C * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
  obtain ⟨Cd, hCdpos, hCd⟩ := offCutDeriv
  obtain ⟨C₁, hC₁pos, hC₁⟩ := offLamTail 1 N
  refine ⟨Cd * C₁, mul_pos hCdpos hC₁pos, ?_⟩
  intro k jj hk hjj hkj
  set R : ℝ := (2 : ℝ) ^ (jj - 1) with hR
  set T : Set ℝ := {x : ℝ | R ≤ |x|} with hT
  have hRpos : 0 < R := by rw [hR]; exact zpow_pos (by norm_num) (jj - 1)
  have hTmeas : MeasurableSet T := by
    rw [hT, absSet_eq_Ici_union_Iic hRpos.le]
    exact measurableSet_Ici.union measurableSet_Iic
  have hkR : (2 : ℝ) ^ k * R = (2 : ℝ) ^ (k + jj - 1) := by
    rw [hR, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  -- the uniform bound on `(η_{≤jj})'`
  have hbmp : ∀ x : ℝ, ‖deriv (bmp jj) x‖ ≤ Cd := by
    intro x
    have h1 : ‖deriv (bmp jj) x‖ ≤ Cd * (2 : ℝ) ^ (-jj) := by
      simpa only [bmp] using (hCd jj x).1
    have h2 : (2 : ℝ) ^ (-jj) ≤ 1 := by
      have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show (-jj : ℤ) ≤ 0 by omega)
      simpa using h
    calc ‖deriv (bmp jj) x‖ ≤ Cd * (2 : ℝ) ^ (-jj) := h1
      _ ≤ Cd * 1 := mul_le_mul_of_nonneg_left h2 hCdpos.le
      _ = Cd := mul_one _
  -- `(η_{≤jj})'` vanishes below the inner radius `2^{jj-1}`
  have hzero : ∀ x : ℝ, |x| < (2 : ℝ) ^ (jj - 1) → deriv (bmp jj) x = 0 := by
    intro x hx
    have h := (bmp_eventuallyEq_one (jj := jj) hx).deriv_eq
    simpa using h
  -- the pointwise bound
  have hpoint : ∀ x : ℝ, ‖deriv (lam k) x * deriv (bmp jj) x‖ₑ
      ≤ T.indicator (fun x => ENNReal.ofReal Cd * ‖deriv (lam k) x‖ₑ) x := by
    intro x
    by_cases hx : x ∈ T
    · rw [Set.indicator_of_mem hx]
      have hg : ‖deriv (bmp jj) x‖ₑ ≤ ENNReal.ofReal Cd := by
        rw [enorm_complex_eq_ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hbmp x)
      calc ‖deriv (lam k) x * deriv (bmp jj) x‖ₑ
          = ‖deriv (lam k) x‖ₑ * ‖deriv (bmp jj) x‖ₑ := enorm_mul _ _
        _ ≤ ‖deriv (lam k) x‖ₑ * ENNReal.ofReal Cd := by gcongr
        _ = ENNReal.ofReal Cd * ‖deriv (lam k) x‖ₑ := mul_comm _ _
    · rw [Set.indicator_of_notMem hx]
      have hx' : |x| < (2 : ℝ) ^ (jj - 1) := by
        simp only [hT, Set.mem_ofPred_eq] at hx
        rw [← hR]
        exact not_le.mp hx
      rw [hzero x hx', mul_zero]
      simp
  -- the indicator commutes with the constant multiple
  have hind : T.indicator (fun x => ENNReal.ofReal Cd * ‖deriv (lam k) x‖ₑ)
      = fun x => ENNReal.ofReal Cd * T.indicator (fun x => ‖deriv (lam k) x‖ₑ) x := by
    funext x
    by_cases hx : x ∈ T
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, mul_zero]
  -- the lintegral chain
  have hlin : ∫⁻ x : ℝ, ‖deriv (lam k) x * deriv (bmp jj) x‖ₑ
      ≤ ENNReal.ofReal Cd * ∫⁻ x in T, ‖deriv (lam k) x‖ₑ := by
    calc ∫⁻ x : ℝ, ‖deriv (lam k) x * deriv (bmp jj) x‖ₑ
        ≤ ∫⁻ x, T.indicator (fun x => ENNReal.ofReal Cd * ‖deriv (lam k) x‖ₑ) x :=
            lintegral_mono hpoint
      _ = ∫⁻ x in T, ENNReal.ofReal Cd * ‖deriv (lam k) x‖ₑ :=
            lintegral_indicator hTmeas _
      _ = ENNReal.ofReal Cd * ∫⁻ x in T, ‖deriv (lam k) x‖ₑ := by
            rw [← lintegral_indicator hTmeas
                  (f := fun x => ENNReal.ofReal Cd * ‖deriv (lam k) x‖ₑ),
                ← lintegral_indicator hTmeas (f := fun x => ‖deriv (lam k) x‖ₑ), hind,
                lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- the tail estimate for `λ_k'`
  have htail : ∫⁻ x in T, ‖deriv (lam k) x‖ₑ
      ≤ ENNReal.ofReal (C₁ * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
    have h1 := hC₁ k R hRpos.le
    rw [pow_one] at h1
    have hfun : (fun x : ℝ => ‖deriv (lam k) x‖ₑ)
        = fun x : ℝ => ‖iteratedDeriv 1 (⇑(Work.KMTAreas.A7.etaMult_K k)) x‖ₑ := by
      funext x
      simp only [iteratedDeriv_one, lam_eq_etaMult_K]
    rw [hT, hfun, ← hkR]
    exact h1
  calc ∫⁻ x : ℝ, ‖deriv (lam k) x * deriv (bmp jj) x‖ₑ
      ≤ ENNReal.ofReal Cd * ∫⁻ x in T, ‖deriv (lam k) x‖ₑ := hlin
    _ ≤ ENNReal.ofReal Cd *
          ENNReal.ofReal (C₁ * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
        gcongr
    _ = ENNReal.ofReal (Cd * (C₁ * (2 : ℝ) ^ k
          * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)))) := by
        rw [← ENNReal.ofReal_mul hCdpos.le]
    _ = ENNReal.ofReal ((Cd * C₁) * (2 : ℝ) ^ k
          * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
        congr 1
        ring

end Work.KMTAreas.A4
