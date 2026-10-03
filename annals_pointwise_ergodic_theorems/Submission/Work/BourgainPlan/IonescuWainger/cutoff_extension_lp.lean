import Mathlib
import Submission.Work.Analysis.Fourier.comb_lintegral_le
import Submission.Work.BourgainPlan.IonescuWainger.plateau_multiplier_lp

/-!
# The smoothed band cut-off extension estimate

`cutoff_extension_lp`: the extension operator `ℓ^p(ℤ) → L^p(ℝ)` with the smoothed Nyquist
cut-off `plateau ε` as symbol is bounded uniformly in `ε ∈ (0,1/2]`.

Scheme (mirroring `band_limited_extension_lp`, the sharp cut-off case):

* `u := Σ_{m ∈ s} a_m φ(· - m)` is a Schwartz function whose Fourier transform equals the
  trigonometric polynomial `B(ξ) = Σ_m a_m e^{-2πi m ξ}` on the Nyquist band;
* since `plateau ε` is supported in the band, `B · plateau ε = plateau ε · 𝓕u`, so the left-hand
  side is `‖Op_{plateau ε} u‖_{L^p}^p`, bounded by `C₀^p ‖u‖_{L^p}^p` via the multiplier bound
  `plateau_multiplier_lp`;
* `‖u‖_{L^p}^p ≤ K^p Σ_m ‖a_m‖^p` is the elementary lattice/comb estimate `comb_lintegral_le`.
-/

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory
open scoped ENNReal FourierTransform BigOperators

noncomputable section


/-- Fourier transform of a translated Schwartz function: `𝓕(φ(·-m)) = e^{-2πi m ·} 𝓕φ`. -/
lemma fourier_translate_schwartz (m : ℤ) (φ : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    ((𝓕 ((SchwartzMap.compSubConstCLM ℂ (E:=ℝ) (F:=ℂ) (m:ℝ)) φ) : SchwartzMap ℝ ℂ) : ℝ → ℂ) ξ
      = Complex.exp (-(2 * Real.pi * Complex.I * (m : ℂ) * (ξ : ℂ))) * 𝓕 (φ : ℝ → ℂ) ξ := by
  have hcoe : (⇑((SchwartzMap.compSubConstCLM ℂ (E:=ℝ) (F:=ℂ) (m:ℝ)) φ) : ℝ → ℂ)
      = fun x : ℝ => (φ : ℝ → ℂ) (x - (m:ℝ)) := by
    funext x
    rw [SchwartzMap.compSubConstCLM_apply]
  rw [SchwartzMap.fourier_coe, hcoe, Commons.Analysis.Fourier.fourier_comp_sub]
  simp only [smul_eq_mul]
  rw [Real.inner_apply, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

/-- The finite comb `Σ_{m∈s} b_m φ(·-m)`, as a Schwartz function. -/
def comb (s : Finset ℤ) (b : ℤ → ℂ) (φ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  ∑ m ∈ s, (b m) • ((SchwartzMap.compSubConstCLM ℂ (E:=ℝ) (F:=ℂ) (m:ℝ)) φ)

lemma comb_apply (s : Finset ℤ) (b : ℤ → ℂ) (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    (comb s b φ : ℝ → ℂ) x = ∑ m ∈ s, b m * (φ : ℝ → ℂ) (x - (m:ℝ)) := by
  rw [comb]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro m hm
  rw [smul_apply, SchwartzMap.compSubConstCLM_apply]
  rfl

/-- The Fourier transform of the comb. -/
lemma comb_fourier (s : Finset ℤ) (b : ℤ → ℂ) (φ : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    𝓕 ((comb s b φ) : ℝ → ℂ) ξ
      = (∑ m ∈ s, b m * Complex.exp (-(2 * Real.pi * Complex.I * (m : ℂ) * (ξ : ℂ))))
          * 𝓕 (φ : ℝ → ℂ) ξ := by
  have key : 𝓕 (comb s b φ)
      = ∑ m ∈ s, (b m) • (𝓕 ((SchwartzMap.compSubConstCLM ℂ (E:=ℝ) (F:=ℂ) (m:ℝ)) φ) : SchwartzMap ℝ ℂ) := by
    rw [comb, FourierTransform.fourier_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [FourierSMul.fourier_smul]
  rw [show 𝓕 ((comb s b φ) : ℝ → ℂ) ξ = ((𝓕 (comb s b φ) : SchwartzMap ℝ ℂ) : ℝ → ℂ) ξ from by
        rw [SchwartzMap.fourier_coe], key, sum_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [smul_apply, smul_eq_mul, fourier_translate_schwartz]
  ring

/-- On the band the Fourier transform of the comb is the trigonometric polynomial `B`. -/
lemma comb_fourier_band (s : Finset ℤ) (b : ℤ → ℂ) (φ : SchwartzMap ℝ ℂ)
    (hφ : ∀ ξ ∈ Set.Icc (-(1/2):ℝ) (1/2), 𝓕 (φ : ℝ → ℂ) ξ = 1) (ξ : ℝ) :
    (Set.indicator (Set.Icc (-(1/2):ℝ) (1/2)) (fun _ : ℝ => (1:ℂ)) ξ)
        * 𝓕 ((comb s b φ) : ℝ → ℂ) ξ
      = (∑ m ∈ s, b m * Complex.exp (-(2 * Real.pi * Complex.I * (m : ℂ) * (ξ : ℂ))))
        * (Set.indicator (Set.Icc (-(1/2):ℝ) (1/2)) (fun _ : ℝ => (1:ℂ)) ξ) := by
  by_cases hξ : ξ ∈ Set.Icc (-(1/2):ℝ) (1/2)
  · rw [Set.indicator_of_mem hξ, one_mul, mul_one]
    rw [comb_fourier, hφ ξ hξ, mul_one]
  · rw [Set.indicator_of_notMem hξ, zero_mul, mul_zero]

/-- Existence of a Schwartz function whose Fourier transform is `1` on the Nyquist band. -/
lemma exists_schwartz_fourier_eq_one_band :
    ∃ φ : SchwartzMap ℝ ℂ, ∀ ξ ∈ Set.Icc (-(1/2):ℝ) (1/2),
      FourierTransform.fourier (φ : ℝ → ℂ) ξ = 1 := by
  obtain ⟨ψ, hψ⟩ := Commons.Analysis.Fourier.exists_schwartzMap_eq_one_Icc (1/2) (by norm_num)
  refine ⟨𝓕⁻ ψ, ?_⟩
  have hfour : FourierTransform.fourier ((𝓕⁻ ψ : SchwartzMap ℝ ℂ) : ℝ → ℂ) = (ψ : ℝ → ℂ) := by
    rw [← SchwartzMap.fourier_coe, FourierInvPair.fourier_fourierInv_eq]
  intro ξ hξ
  rw [hfour]
  exact hψ ξ hξ
/-- **The plateau as a difference of smoothed steps.**  For `0 < ε ≤ 1/2`,
`plateau ε ξ = T((ξ+1/2)/ε) − T((ξ−1/2+ε)/ε)` where `T = Real.smoothTransition`.

Indeed `plateau ε ξ = T a * (1 − T b)` with `a = (ξ+1/2)/ε`, `b = (ξ−1/2+ε)/ε`; if `T b ≠ 0` then
`b > 0`, so `a = b + (1−ε)/ε ≥ b + 1 > 1` (using `ε ≤ 1/2`) and hence `T a = 1`.  Either way
`T a * (1 − T b) = T a − T b`. -/
lemma plateau_eq_transition_sub (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (ξ : ℝ) :
    plateau ε ξ
      = Real.smoothTransition ((ξ + 1 / 2) / ε)
        - Real.smoothTransition ((ξ - 1 / 2 + ε) / ε) := by
  have hAB : Real.smoothTransition ((ξ + 1 / 2) / ε)
        * Real.smoothTransition ((ξ - 1 / 2 + ε) / ε)
      = Real.smoothTransition ((ξ - 1 / 2 + ε) / ε) := by
    by_cases hB0 : Real.smoothTransition ((ξ - 1 / 2 + ε) / ε) = 0
    · rw [hB0, mul_zero]
    · have hpos : 0 < (ξ - 1 / 2 + ε) / ε := by
        by_contra hle
        exact hB0 (Real.smoothTransition.zero_of_nonpos (le_of_not_gt hle))
      have hkey : (1 - ε) / ε ≤ (ξ + 1 / 2) / ε - (ξ - 1 / 2 + ε) / ε := by
        have h1 : (ξ + 1 / 2) / ε - (ξ - 1 / 2 + ε) / ε = (1 - ε) / ε := by
          rw [← sub_div]
          congr 1
          ring
        rw [h1]
      have h2 : 1 ≤ (1 - ε) / ε := by
        rw [le_div_iff₀ hε]
        linarith
      have hge : 1 ≤ (ξ + 1 / 2) / ε := by linarith
      rw [Real.smoothTransition.one_of_one_le hge, one_mul]
  unfold plateau
  rw [mul_sub, mul_one, hAB]

theorem cutoff_extension_lp (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1/2 → ∀ (s : Finset ℤ) (a : ℤ → ℂ),
      (∀ k, k ∉ s → a k = 0) →
      ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
          (fun ξ : ℝ => (∑ k ∈ s, a k * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (ξ : ℂ))))
            * ((plateau ε ξ : ℝ) : ℂ)) x‖ₑ ^ p
        ≤ ENNReal.ofReal (C ^ p) * ∑ k ∈ s, ENNReal.ofReal ‖a k‖ ^ p := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := plateau_multiplier_lp p hp
  obtain ⟨φ, hφ1⟩ := exists_schwartz_fourier_eq_one_band
  obtain ⟨K, hKpos, hK⟩ := Work.Analysis.Fourier.comb_lintegral_le hp φ
  refine ⟨C₀ * K, mul_pos hC₀pos hKpos, ?_⟩
  intro ε hε hε2 s a ha
  set B : ℝ → ℂ := fun ξ => ∑ m ∈ s, a m * Complex.exp (-(2 * Real.pi * Complex.I * (m : ℂ) * (ξ : ℂ))) with hBdef
  set u : SchwartzMap ℝ ℂ := comb s a φ with hudef
  have hfu : ∀ ξ : ℝ, FourierTransform.fourier (u : ℝ → ℂ) ξ
      = B ξ * FourierTransform.fourier (φ : ℝ → ℂ) ξ := by
    intro ξ
    rw [hudef, hBdef]
    exact comb_fourier s a φ ξ
  have hEq : (fun ξ : ℝ => B ξ * ((plateau ε ξ : ℝ) : ℂ))
      = fun ξ : ℝ => ((plateau ε ξ : ℝ) : ℂ) * FourierTransform.fourier (u : ℝ → ℂ) ξ := by
    funext ξ
    rw [hfu ξ]
    by_cases hξ : ξ ∈ Set.Icc (-(1/2):ℝ) (1/2)
    · rw [hφ1 ξ hξ, mul_one, mul_comm]
    · have h0 : plateau ε ξ = 0 := by
        by_contra hne
        exact hξ (plateau_support ε hε (Function.mem_support.mpr hne))
      rw [h0]
      simp
  have hu : (u : ℝ → ℂ) = fun x : ℝ => ∑ m ∈ s, a m * (φ : ℝ → ℂ) (x - (m:ℝ)) := by
    funext x
    rw [hudef, comb_apply]
  calc ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
          (fun ξ : ℝ => (∑ k ∈ s, a k * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (ξ : ℂ))))
            * ((plateau ε ξ : ℝ) : ℂ)) x‖ₑ ^ p
      = ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
          (fun ξ : ℝ => B ξ * ((plateau ε ξ : ℝ) : ℂ)) x‖ₑ ^ p := by
        apply lintegral_congr
        intro x
        rw [hBdef]
    _ = ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
          (fun ξ : ℝ => ((plateau ε ξ : ℝ) : ℂ)
            * FourierTransform.fourier (u : ℝ → ℂ) ξ) x‖ₑ ^ p := by
        apply lintegral_congr
        intro x
        rw [hEq]
    _ ≤ ENNReal.ofReal (C₀ ^ p) * ∫⁻ x : ℝ, ‖(u : ℝ → ℂ) x‖ₑ ^ p := hC₀ ε hε hε2 u
    _ = ENNReal.ofReal (C₀ ^ p) * ∫⁻ x : ℝ,
          ‖(∑ m ∈ s, a m * (φ : ℝ → ℂ) (x - (m:ℝ)))‖ₑ ^ p := by rw [hu]
    _ ≤ ENNReal.ofReal (C₀ ^ p) * (ENNReal.ofReal (K ^ p) * ∑ m ∈ s, ENNReal.ofReal ‖a m‖ ^ p) :=
        mul_le_mul_of_nonneg_left (hK s a) bot_le
    _ = ENNReal.ofReal ((C₀ * K) ^ p) * ∑ m ∈ s, ENNReal.ofReal ‖a m‖ ^ p := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), Real.mul_rpow hC₀pos.le hKpos.le]

end

end Work.BourgainPlan.IonescuWainger