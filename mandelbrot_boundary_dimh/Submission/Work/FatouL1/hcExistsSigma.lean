import Mathlib

set_option linter.unusedVariables false

namespace Work.FatouL1

open MeasureTheory intervalIntegral

/-- Averaging lemma.  If `G` is a continuous, nonnegative function whose integral over every
interval is at most `K`, then for every `N > 0` there exists `σ ∈ [N, 2N]` with
`G (y₀ + σ) + G (y₀ - σ) ≤ 2 K / N`.

Proof: assume the contrary; then the continuous function `σ ↦ G (y₀ + σ) + G (y₀ - σ)`
exceeds the constant `2K/N` on all of `[N, 2N]`, so its integral there is `> 2K`.  But by the
change of variables `σ ↦ y₀ + σ` and `σ ↦ y₀ - σ` this integral equals
`∫_{y₀+N}^{y₀+2N} G + ∫_{y₀-2N}^{y₀-N} G ≤ K + K`. -/
theorem hcExistsSigma {K : ℝ} (hK : 0 ≤ K) {G : ℝ → ℝ} (hGc : Continuous G)
    (hGnn : ∀ Y : ℝ, 0 ≤ G Y)
    (hG : ∀ Y₁ Y₂ : ℝ, Y₁ ≤ Y₂ → ∫ Y : ℝ in Y₁..Y₂, G Y ≤ K)
    {y₀ N : ℝ} (hN : 0 < N) :
    ∃ σ : ℝ, N ≤ σ ∧ σ ≤ 2 * N ∧ G (y₀ + σ) + G (y₀ - σ) ≤ 2 * K / N := by
  by_contra h
  push Not at h
  have hN2 : N < 2 * N := by linarith
  -- change of variables in the two halves of the integral
  have hI1 : ∫ σ in N..(2*N), G (y₀ + σ) = ∫ Y in (y₀ + N)..(y₀ + 2*N), G Y := by
    rw [integral_comp_add_left]
  have hI2 : ∫ σ in N..(2*N), G (y₀ - σ) = ∫ Y in (y₀ - 2*N)..(y₀ - N), G Y := by
    rw [integral_comp_sub_left]
  have hA : IntervalIntegrable (fun σ : ℝ => G (y₀ + σ)) volume N (2*N) :=
    (hGc.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun σ : ℝ => G (y₀ - σ)) volume N (2*N) :=
    (hGc.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
  have hsum : ∫ σ in N..(2*N), (G (y₀ + σ) + G (y₀ - σ))
      = (∫ Y in (y₀ + N)..(y₀ + 2*N), G Y) + (∫ Y in (y₀ - 2*N)..(y₀ - N), G Y) := by
    rw [integral_add hA hB, hI1, hI2]
  -- upper bound for the integral of the sum
  have hub : ∫ σ in N..(2*N), (G (y₀ + σ) + G (y₀ - σ)) ≤ 2 * K := by
    rw [hsum]
    have h1 := hG (y₀ + N) (y₀ + 2*N) (by linarith)
    have h2 := hG (y₀ - 2*N) (y₀ - N) (by linarith)
    linarith
  -- strict lower bound from the contradiction hypothesis
  have hlt : 2 * K < ∫ σ in N..(2*N), (G (y₀ + σ) + G (y₀ - σ)) := by
    have hcφ : ContinuousOn (fun σ : ℝ => G (y₀ + σ) + G (y₀ - σ)) (Set.Icc N (2*N)) := by
      fun_prop
    have hstrict := integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (f := fun _ : ℝ => 2 * K / N)
      (g := fun σ : ℝ => G (y₀ + σ) + G (y₀ - σ))
      hN2 continuousOn_const hcφ
      (fun x hx => le_of_lt (h x (le_of_lt hx.1) hx.2))
      ⟨N, ⟨le_refl N, le_of_lt hN2⟩, h N le_rfl (le_of_lt hN2)⟩
    have hconst : (∫ σ in N..(2*N), (fun _ : ℝ => 2 * K / N) σ) = 2 * K := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      have hNne : N ≠ 0 := ne_of_gt hN
      field_simp
      ring
    rw [hconst] at hstrict
    exact hstrict
  linarith

end Work.FatouL1
