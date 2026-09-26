import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.FunctionalEquations.DirichletExpansion
import Submission.Work.FunctionalEquations.GenSummableMulExpNeg
import Submission.Work.FunctionalEquations.SummableExpansionTerms
import Submission.Work.FunctionalEquations.CoefficientValuePattern
import Submission.Work.FunctionalEquations.DirichletCoeffOneNormLe
import Submission.Work.FunctionalEquations.SummableNormExpTail

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

theorem CoeffOneZeroOfDecay {F : ℂ → ℂ} {a b : Set.Ici (1:ℕ) → ℂ}
    {C : ℝ} {N : ℕ} {ψ : ℝ → ℝ} (hC : 0 ≤ C) (hψ : Tendsto ψ atTop (𝓝 0))
    (ha : ∀ m : Set.Ici (1:ℕ), ‖a m‖ ≤ C * ((m.1 : ℝ) + 1) ^ N)
    (hb : ∀ m : Set.Ici (1:ℕ), ‖b m‖ ≤ C * ((m.1 : ℝ) + 1) ^ N)
    (hexp : ∀ τ : ℂ, 0 < τ.im →
      F τ = (∑' m : Set.Ici (1:ℕ), a m * dirichletTerm m.1 τ)
        + (2 * (Real.pi : ℂ) * Complex.I * τ)
          * (∑' m : Set.Ici (1:ℕ), b m * dirichletTerm m.1 τ))
    (hbound : ∀ τ : ℂ, 0 < τ.im → -1 ≤ τ.re → τ.re ≤ 1 →
      ‖F τ‖ ≤ ψ τ.im * Real.exp (-(2 * Real.pi * τ.im))) :
    a ⟨1, by simp⟩ = 0 ∧ b ⟨1, by simp⟩ = 0 := by
  let A : ℂ → ℂ := fun τ => ∑' m : Set.Ici (1:ℕ), a m * dirichletTerm m.1 τ
  let B : ℂ → ℂ := fun τ => ∑' m : Set.Ici (1:ℕ), b m * dirichletTerm m.1 τ
  have summA : ∀ τ : ℂ, 0 < τ.im → Summable fun m : Set.Ici (1:ℕ) => a m * dirichletTerm m.1 τ :=
    fun τ hτ => summable_mul_dirichletTerm hC ha τ hτ
  have summB : ∀ τ : ℂ, 0 < τ.im → Summable fun m : Set.Ici (1:ℕ) => b m * dirichletTerm m.1 τ :=
    fun τ hτ => summable_mul_dirichletTerm hC hb τ hτ
  have hF : ∀ τ : ℂ, 0 < τ.im → F τ = A τ + (2 * (Real.pi : ℂ) * Complex.I * τ) * B τ :=
    fun τ hτ => hexp τ hτ
  have hAper : ∀ τ : ℂ, A (τ + 1) = A τ := fun τ => tsum_congr fun m => by
    rw [dirichletTerm_add_one]
  have hBper : ∀ τ : ℂ, B (τ + 1) = B τ := fun τ => tsum_congr fun m => by
    rw [dirichletTerm_add_one]
  -- the `τ`-linear part of the expansion is the first difference of `F`
  have hsplit : ∀ τ : ℂ, 0 < τ.im →
      (2 * (Real.pi : ℂ) * Complex.I) * B τ = F (τ + 1) - F τ := by
    intro τ hτ
    have h1 := hF τ hτ
    have h2 := hF (τ + 1) (by simpa using hτ)
    rw [hAper τ, hBper τ] at h2
    have key : F (τ + 1) - F τ = (2 * (Real.pi : ℂ) * Complex.I) * B τ := by
      rw [h2, h1]
      ring
    exact key.symm
  -- the norm of the leading coefficient `2 * pi * i`
  have hcnorm : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    have h2pi : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [h2pi, norm_mul, Complex.norm_I, mul_one]
    exact Complex.norm_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)
  -- decay of `B` on the strip `-1 <= Re <= 0`, from the bound on `F` at `τ` and `τ + 1`
  have hBstrip : ∀ (t y : ℝ), 0 < y → -1 ≤ t → t ≤ 0 →
      ‖B ((t : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ Real.exp (-(2 * Real.pi * y)) * (ψ y / Real.pi) := by
    intro t y hy htm hlt
    have hy0 : 0 < ((t : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
    have h1 := hsplit ((t : ℂ) + (y : ℂ) * Complex.I) hy0
    have hF0 : ‖F ((t : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ ψ y * Real.exp (-(2 * Real.pi * y)) := by
      have := hbound ((t : ℂ) + (y : ℂ) * Complex.I) hy0
        (by simpa using htm) (by simpa using (by linarith : t ≤ 1))
      simpa using this
    have hF1 : ‖F (((t : ℂ) + (y : ℂ) * Complex.I) + 1)‖
        ≤ ψ y * Real.exp (-(2 * Real.pi * y)) := by
      have him1 : 0 < (((t : ℂ) + (y : ℂ) * Complex.I) + 1).im := by simpa using hy
      have hre1 : -1 ≤ (((t : ℂ) + (y : ℂ) * Complex.I) + 1).re := by simp; linarith
      have hre2 : (((t : ℂ) + (y : ℂ) * Complex.I) + 1).re ≤ 1 := by simp; linarith
      have := hbound (((t : ℂ) + (y : ℂ) * Complex.I) + 1) him1 hre1 hre2
      simpa using this
    have hkey : ‖B ((t : ℂ) + (y : ℂ) * Complex.I)‖ * (2 * Real.pi)
        = ‖F (((t : ℂ) + (y : ℂ) * Complex.I) + 1) - F ((t : ℂ) + (y : ℂ) * Complex.I)‖ := by
      rw [← h1, norm_mul, hcnorm]
      ring
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    have hbd1 : ‖F (((t : ℂ) + (y : ℂ) * Complex.I) + 1) - F ((t : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ 2 * (ψ y * Real.exp (-(2 * Real.pi * y))) := by
      have := norm_sub_le (F (((t : ℂ) + (y : ℂ) * Complex.I) + 1))
        (F ((t : ℂ) + (y : ℂ) * Complex.I))
      linarith
    calc ‖B ((t : ℂ) + (y : ℂ) * Complex.I)‖
        = ‖F (((t : ℂ) + (y : ℂ) * Complex.I) + 1) - F ((t : ℂ) + (y : ℂ) * Complex.I)‖
            / (2 * Real.pi) := by
          rw [eq_div_iff h2pi.ne']
          exact hkey
      _ ≤ (2 * (ψ y * Real.exp (-(2 * Real.pi * y)))) / (2 * Real.pi) :=
          div_le_div_of_nonneg_right hbd1 h2pi.le
      _ = Real.exp (-(2 * Real.pi * y)) * (ψ y / Real.pi) := by ring_nf
  -- extraction of the coefficient of `e^{2 pi i tau}`
  have hb_le : ∀ y : ℝ, 0 < y → ‖b ⟨1, by simp⟩‖ ≤ ψ y / Real.pi := by
    intro y hy
    refine DirichletCoeffOneNormLe (c := b) (C := C) (N := N) hC hb (y := y)
      (M := ψ y / Real.pi) (A := -1) hy ?_
    intro t ht
    have ht2 : t ≤ 0 := by
      have h := ht.2
      linarith
    exact hBstrip t y hy ht.1 ht2
  have hb1 : b ⟨1, by simp⟩ = 0 := by
    have hlim : Tendsto (fun y : ℝ => ψ y / Real.pi) atTop (𝓝 0) := by
      simpa using hψ.div_const Real.pi
    have hev : ∀ᶠ y in atTop, ‖b ⟨1, by simp⟩‖ ≤ ψ y / Real.pi := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      exact hb_le y hy
    have h0 : ‖b ⟨1, by simp⟩‖ ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim hev
    exact norm_eq_zero.mp (le_antisymm h0 (norm_nonneg _))
  -- the `m >= 2` tail of `B` is of size `e^{-4 pi y}`
  obtain ⟨K, hK0, hK⟩ := SummableNormExpTail (c := b) hC hb hb1
  have hBnorm : ∀ τ : ℂ, 0 < τ.im →
      ‖B τ‖ ≤ ∑' m : Set.Ici (1:ℕ), ‖b m‖ * Real.exp (-(2 * Real.pi * (m.1:ℝ) * τ.im)) := by
    intro τ hτ
    have hs := summB τ hτ
    have hsnorm : Summable fun m : Set.Ici (1:ℕ) => ‖b m * dirichletTerm m.1 τ‖ := hs.norm
    calc ‖B τ‖ ≤ ∑' m : Set.Ici (1:ℕ), ‖b m * dirichletTerm m.1 τ‖ :=
          norm_tsum_le_tsum_norm hsnorm
      _ = ∑' m : Set.Ici (1:ℕ), ‖b m‖ * Real.exp (-(2 * Real.pi * (m.1:ℝ) * τ.im)) := by
          apply tsum_congr
          intro m
          rw [norm_mul, norm_dirichletTerm]
          congr 1
          ring_nf
  have hBtail : ∀ (t y : ℝ), 1 ≤ y →
      ‖B ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤ K * Real.exp (-(4 * Real.pi * y)) := by
    intro t y hy1
    have hy : 0 < y := by linarith
    have h := hBnorm ((t : ℂ) + (y : ℂ) * Complex.I) (by simpa using hy)
    rw [show (((t : ℂ) + (y : ℂ) * Complex.I)).im = y by simp] at h
    exact le_trans h (hK y hy1)
  -- decay of `A = F - 2 pi i tau B` on the vertical strip
  have hAbound : ∀ (t y : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → 1 ≤ y →
      ‖A ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        Real.exp (-(2 * Real.pi * y))
          * (ψ y + 2 * Real.pi * (1 + y) * K * Real.exp (-(2 * Real.pi * y))) := by
    intro t y ht hy1
    have hy : 0 < y := by linarith
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hAeq : A ((t : ℂ) + (y : ℂ) * Complex.I)
        = F ((t : ℂ) + (y : ℂ) * Complex.I)
          - (2 * (Real.pi : ℂ) * Complex.I * ((t : ℂ) + (y : ℂ) * Complex.I))
            * B ((t : ℂ) + (y : ℂ) * Complex.I) := by
      have h := hF ((t : ℂ) + (y : ℂ) * Complex.I) (by simpa using hy)
      rw [h]
      ring
    rw [hAeq]
    have hF0 : ‖F ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤ ψ y * Real.exp (-(2 * Real.pi * y)) := by
      have := hbound ((t : ℂ) + (y : ℂ) * Complex.I) (by simpa using hy)
        (by simpa using (by linarith : -1 ≤ t)) (by simpa using (by linarith : t ≤ 1))
      simpa using this
    have hB0 : ‖B ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤ K * Real.exp (-(4 * Real.pi * y)) :=
      hBtail t y hy1
    have htaunorm : ‖((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤ 1 + y := by
      calc ‖((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤ ‖((t : ℂ))‖ + ‖(y : ℂ) * Complex.I‖ :=
            norm_add_le _ _
        _ = t + y := by
            rw [Complex.norm_real, Complex.norm_mul, Complex.norm_I, mul_one,
              Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg ht0, abs_of_nonneg (by linarith : (0:ℝ) ≤ y)]
        _ ≤ 1 + y := by linarith
    have htau2 : ‖(2 * (Real.pi : ℂ) * Complex.I * ((t : ℂ) + (y : ℂ) * Complex.I))‖
        ≤ 2 * Real.pi * (1 + y) := by
      rw [norm_mul, hcnorm]
      exact mul_le_mul_of_nonneg_left htaunorm (by positivity)
    have hexp4 : Real.exp (-(4 * Real.pi * y))
        = Real.exp (-(2 * Real.pi * y)) * Real.exp (-(2 * Real.pi * y)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc ‖F ((t : ℂ) + (y : ℂ) * Complex.I)
          - (2 * (Real.pi : ℂ) * Complex.I * ((t : ℂ) + (y : ℂ) * Complex.I))
            * B ((t : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ ‖F ((t : ℂ) + (y : ℂ) * Complex.I)‖
          + ‖(2 * (Real.pi : ℂ) * Complex.I * ((t : ℂ) + (y : ℂ) * Complex.I))
            * B ((t : ℂ) + (y : ℂ) * Complex.I)‖ := norm_sub_le _ _
      _ = ‖F ((t : ℂ) + (y : ℂ) * Complex.I)‖
          + ‖(2 * (Real.pi : ℂ) * Complex.I * ((t : ℂ) + (y : ℂ) * Complex.I))‖
            * ‖B ((t : ℂ) + (y : ℂ) * Complex.I)‖ := by rw [norm_mul]
      _ ≤ ψ y * Real.exp (-(2 * Real.pi * y))
          + (2 * Real.pi * (1 + y)) * (K * Real.exp (-(4 * Real.pi * y))) :=
          add_le_add hF0 (mul_le_mul htau2 hB0 (norm_nonneg _) (by positivity))
      _ = Real.exp (-(2 * Real.pi * y))
          * (ψ y + 2 * Real.pi * (1 + y) * K * Real.exp (-(2 * Real.pi * y))) := by
          rw [hexp4]
          ring
  have ha_le : ∀ y : ℝ, 1 ≤ y → ‖a ⟨1, by simp⟩‖
      ≤ ψ y + 2 * Real.pi * (1 + y) * K * Real.exp (-(2 * Real.pi * y)) := by
    intro y hy1
    refine DirichletCoeffOneNormLe (c := a) (C := C) (N := N) hC ha (y := y)
      (M := ψ y + 2 * Real.pi * (1 + y) * K * Real.exp (-(2 * Real.pi * y))) (A := 0)
      (by linarith) ?_
    intro t ht
    exact hAbound t y (by simpa using ht) hy1
  have ha1 : a ⟨1, by simp⟩ = 0 := by
    have hM : Tendsto (fun y : ℝ => ψ y + 2 * Real.pi * (1 + y) * K * Real.exp (-(2 * Real.pi * y)))
        atTop (𝓝 0) := by
      have hbase : Tendsto (fun y : ℝ => y * Real.exp (-(2 * Real.pi * y))) atTop (𝓝 0) := by
        have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (2 * Real.pi) (by positivity)
        simpa [Real.rpow_one, neg_mul] using h
      have hexpz : Tendsto (fun y : ℝ => Real.exp (-(2 * Real.pi * y))) atTop (𝓝 0) := by
        have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (2 * Real.pi) (by positivity)
        simpa [neg_mul] using h
      have hfull : Tendsto (fun y : ℝ => (1 + y) * Real.exp (-(2 * Real.pi * y))) atTop (𝓝 0) := by
        have h2 : (fun y : ℝ => (1 + y) * Real.exp (-(2 * Real.pi * y)))
            = (fun y : ℝ => y * Real.exp (-(2 * Real.pi * y))
                + Real.exp (-(2 * Real.pi * y))) := by
          funext y
          ring
        rw [h2]
        simpa using hbase.add hexpz
      have h5 : (fun y : ℝ => ψ y + 2 * Real.pi * (1 + y) * K * Real.exp (-(2 * Real.pi * y)))
          = (fun y : ℝ => ψ y
              + (2 * Real.pi * K) * ((1 + y) * Real.exp (-(2 * Real.pi * y)))) := by
        funext y
        ring
      rw [h5]
      simpa using hψ.add (hfull.const_mul (2 * Real.pi * K))
    have hev : ∀ᶠ y in atTop, ‖a ⟨1, by simp⟩‖
        ≤ ψ y + 2 * Real.pi * (1 + y) * K * Real.exp (-(2 * Real.pi * y)) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
      exact ha_le y hy
    have h0 : ‖a ⟨1, by simp⟩‖ ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hM hev
    exact norm_eq_zero.mp (le_antisymm h0 (norm_nonneg _))
  exact ⟨ha1, hb1⟩

end Work.FunctionalEquations
