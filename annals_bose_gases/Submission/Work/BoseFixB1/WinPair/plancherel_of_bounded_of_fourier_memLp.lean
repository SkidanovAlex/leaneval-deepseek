import Mathlib
import Submission.Work.BoseFixB1.WinPair.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.WinPair

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Elementary facts about the Fourier transform on `L¹(ℝ³)` -/

/-- The Fourier transform is additive on `L¹`: `𝓕 h - 𝓕 k = 𝓕 (h - k)` pointwise. -/
lemma fourier_sub_apply {h k : E3 → ℂ} (hh : Integrable h) (hk : Integrable k) (w : E3) :
    𝓕 h w - 𝓕 k w = 𝓕 (h - k) w := by
  rw [Real.fourier_eq h w, Real.fourier_eq k w, Real.fourier_eq (h - k) w]
  rw [← integral_sub]
  · congr 1 with v
    simp only [Pi.sub_apply, smul_sub]
  · exact (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      continuous_inner (L := innerₗ E3) w).2 hh
  · exact (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      continuous_inner (L := innerₗ E3) w).2 hk

/-- The uniform norm of the Fourier transform is bounded by the `L¹`-norm. -/
lemma norm_fourier_apply_le (h : E3 → ℂ) (w : E3) : ‖𝓕 h w‖ ≤ ∫ x, ‖h x‖ := by
  rw [Real.fourier_eq h w]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
    (innerₗ E3) h w

/-- The Fourier transform of an `L¹` function is continuous. -/
lemma continuous_fourier_of_integrable {h : E3 → ℂ} (hh : Integrable h) : Continuous (𝓕 h) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner
    (L := innerₗ E3) hh

/-- If `𝓕 h ∈ L¹` and `k ∈ L¹`, then `q ↦ 𝓕 h q * 𝓕 k (-q)` is integrable: the second factor is
bounded by `‖k‖₁` and the first one is integrable. -/
lemma integrable_fourier_mul_fourier_neg_of_integrable {h k : E3 → ℂ}
    (hF : Integrable (𝓕 h)) (hk : Integrable k) :
    Integrable (fun q : E3 => 𝓕 h q * 𝓕 k (-q)) := by
  have hkm : AEStronglyMeasurable (fun q : E3 => 𝓕 k (-q)) :=
    (continuous_fourier_of_integrable hk).comp continuous_neg |>.aestronglyMeasurable
  have := hF.bdd_mul hkm (ae_of_all _ (fun q => norm_fourier_apply_le k (-q)))
  simpa only [mul_comm] using this

/-- **One-sided Plancherel with a bounded `L¹` function and an `L¹` Fourier transform.**
If `f ∈ L¹ ∩ L^∞` has integrable Fourier transform and `g ∈ L¹`, then
`∫ f g = ∫ 𝓕f · 𝓕g(·−)`.  Proof: approximate `g` in `L¹` by Schwartz functions `gₙ`
(density of `SchwartzMap` in `Lp`, `SchwartzMap.denseRange_toLpCLM` at `p = 1`), apply the
corpus's `Commons.Analysis.Fourier.plancherel_one_sided_schwartz` to `(f, gₙ)`, and let
`n → ∞`: the left side converges because `‖f‖_∞ < ∞` and `‖gₙ - g‖_1 → 0`, the right side
because `‖𝓕gₙ - 𝓕g‖_∞ ≤ ‖gₙ - g‖_1 → 0` and `𝓕f ∈ L¹`. -/
theorem plancherel_of_bounded_of_fourier_memLp
    {f g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hf1 : MeasureTheory.MemLp f 1
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
    (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hfF : MeasureTheory.MemLp (FourierTransform.fourier f) 1
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
    (hg1 : MeasureTheory.MemLp g 1
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) :
    (∫ x : EuclideanSpace ℝ (Fin 3), f x * g x)
      = ∫ q : EuclideanSpace ℝ (Fin 3),
          FourierTransform.fourier f q * FourierTransform.fourier g (-q) := by
  have hf_int : Integrable f := memLp_one_iff_integrable.mp hf1
  have hg_int : Integrable g := memLp_one_iff_integrable.mp hg1
  have hF_int : Integrable (𝓕 f) := memLp_one_iff_integrable.mp hfF
  obtain ⟨C, hC⟩ := hfb
  have hCnn : 0 ≤ C := le_trans (norm_nonneg (f 0)) (hC 0)
  set L : ℂ := ∫ x, f x * g x with hLdef
  set R : ℂ := ∫ q, 𝓕 f q * 𝓕 g (-q) with hRdef
  have hFnn : 0 ≤ ∫ q : E3, ‖𝓕 f q‖ := integral_nonneg fun q => norm_nonneg _
  -- The approximation argument, with `ψ` smooth of compact support and `‖g - ψ‖₁ ≤ ε`.
  have key : ∀ ε > 0, ‖L - R‖ ≤ (C + ∫ q : E3, ‖𝓕 f q‖) * ε := by
    intro ε hε
    obtain ⟨ψ, hψcs, hψcd, hψe⟩ :=
      MemLp.exist_eLpNorm_sub_le (p := 1) (μ := (volume : Measure E3)) (F := ℂ)
        (by simp) le_rfl hg1 hε
    have hψ_int : Integrable ψ := hψcd.continuous.integrable_of_hasCompactSupport hψcs
    have hd_int : Integrable (fun x : E3 => g x - ψ x) := hg_int.sub hψ_int
    -- `‖g - ψ‖₁ ≤ ε`
    have hD : (∫ x : E3, ‖g x - ψ x‖) ≤ ε := by
      have h1 : ENNReal.ofReal (∫ x : E3, ‖g x - ψ x‖) ≤ ENNReal.ofReal ε := by
        rw [ofReal_integral_norm_eq_lintegral_enorm hd_int]
        rw [← eLpNorm_one_eq_lintegral_enorm]
        exact hψe
        all_goals first | fun_prop | measurability
      exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp h1
    -- Plancherel for the smooth compactly supported `ψ`
    have hplan : (∫ x : E3, f x * ψ x) = ∫ q : E3, 𝓕 f q * 𝓕 ψ (-q) :=
      Commons.Analysis.Fourier.plancherel_one_sided_schwartz hf_int (hψcs.toSchwartzMap hψcd)
    -- Estimate of the left-hand side
    have hfg_int : Integrable (fun x : E3 => f x * g x) :=
      hg_int.bdd_mul hf_int.aestronglyMeasurable (ae_of_all _ hC)
    have hfψ_int : Integrable (fun x : E3 => f x * ψ x) :=
      hψ_int.bdd_mul hf_int.aestronglyMeasurable (ae_of_all _ hC)
    have hLdiff : (∫ x : E3, f x * g x) - (∫ x : E3, f x * ψ x)
        = ∫ x : E3, f x * (g x - ψ x) := by
      rw [← integral_sub hfg_int hfψ_int]
      congr 1 with x
      ring
    have hLbound : ‖(∫ x : E3, f x * g x) - (∫ x : E3, f x * ψ x)‖
        ≤ C * ∫ x : E3, ‖g x - ψ x‖ := by
      rw [hLdiff]
      calc ‖∫ x : E3, f x * (g x - ψ x)‖
          ≤ ∫ x : E3, ‖f x * (g x - ψ x)‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ x : E3, C * ‖g x - ψ x‖ := by
            apply integral_mono
            · exact (hd_int.bdd_mul hf_int.aestronglyMeasurable
                (ae_of_all _ hC)).norm
            · exact hd_int.norm.const_mul C
            · intro x
              simpa only [norm_mul] using
                mul_le_mul_of_nonneg_right (hC x) (norm_nonneg (g x - ψ x))
        _ = C * ∫ x : E3, ‖g x - ψ x‖ := integral_const_mul C _
    -- Estimate of the right-hand side
    have hRψ_int : Integrable (fun q : E3 => 𝓕 f q * 𝓕 ψ (-q)) :=
      integrable_fourier_mul_fourier_neg_of_integrable (h := f) hF_int hψ_int
    have hRg_int : Integrable (fun q : E3 => 𝓕 f q * 𝓕 g (-q)) :=
      integrable_fourier_mul_fourier_neg_of_integrable (h := f) hF_int hg_int
    have hRdiff : (∫ q : E3, 𝓕 f q * 𝓕 ψ (-q)) - (∫ q : E3, 𝓕 f q * 𝓕 g (-q))
        = -(∫ q : E3, 𝓕 f q * 𝓕 (g - ψ) (-q)) := by
      rw [← integral_sub hRψ_int hRg_int]
      rw [← integral_neg]
      congr 1 with q
      have h := fourier_sub_apply hg_int hψ_int (-q)
      rw [← h]
      ring
    have hRbound : ‖(∫ q : E3, 𝓕 f q * 𝓕 ψ (-q)) - (∫ q : E3, 𝓕 f q * 𝓕 g (-q))‖
        ≤ (∫ q : E3, ‖𝓕 f q‖) * (∫ x : E3, ‖g x - ψ x‖) := by
      rw [hRdiff, norm_neg]
      calc ‖∫ q : E3, 𝓕 f q * 𝓕 (g - ψ) (-q)‖
          ≤ ∫ q : E3, ‖𝓕 f q * 𝓕 (g - ψ) (-q)‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ q : E3, ‖𝓕 f q‖ * (∫ x : E3, ‖g x - ψ x‖) := by
            apply integral_mono
            · exact (integrable_fourier_mul_fourier_neg_of_integrable
                (h := f) hF_int hd_int).norm
            · exact hF_int.norm.mul_const _
            · intro q
              simpa only [norm_mul, Pi.sub_apply] using
                mul_le_mul_of_nonneg_left (norm_fourier_apply_le (g - ψ) (-q))
                  (norm_nonneg (𝓕 f q))
        _ = (∫ q : E3, ‖𝓕 f q‖) * (∫ x : E3, ‖g x - ψ x‖) := integral_mul_const _ _
    -- Assembly
    have hLR : L - R = ((∫ x : E3, f x * g x) - (∫ x : E3, f x * ψ x))
        + ((∫ q : E3, 𝓕 f q * 𝓕 ψ (-q)) - (∫ q : E3, 𝓕 f q * 𝓕 g (-q))) := by
      rw [hLdef, hRdef, hplan]
      ring
    calc ‖L - R‖
        = ‖((∫ x : E3, f x * g x) - (∫ x : E3, f x * ψ x))
            + ((∫ q : E3, 𝓕 f q * 𝓕 ψ (-q)) - (∫ q : E3, 𝓕 f q * 𝓕 g (-q)))‖ := by
          rw [hLR]
      _ ≤ ‖(∫ x : E3, f x * g x) - (∫ x : E3, f x * ψ x)‖
            + ‖(∫ q : E3, 𝓕 f q * 𝓕 ψ (-q)) - (∫ q : E3, 𝓕 f q * 𝓕 g (-q))‖ :=
          norm_add_le _ _
      _ ≤ C * (∫ x : E3, ‖g x - ψ x‖)
            + (∫ q : E3, ‖𝓕 f q‖) * (∫ x : E3, ‖g x - ψ x‖) :=
          add_le_add hLbound hRbound
      _ = (C + ∫ q : E3, ‖𝓕 f q‖) * (∫ x : E3, ‖g x - ψ x‖) := by ring
      _ ≤ (C + ∫ q : E3, ‖𝓕 f q‖) * ε :=
          mul_le_mul_of_nonneg_left hD (by linarith)
  -- Conclude from `‖L - R‖ ≤ A * ε` for all `ε > 0`.
  have hle0 : ‖L - R‖ ≤ 0 := by
    refine le_of_forall_pos_le_add (fun δ hδ => ?_)
    set A : ℝ := C + ∫ q : E3, ‖𝓕 f q‖ with hAdef
    have hAnn : 0 ≤ A := by rw [hAdef]; linarith
    have hden : 0 < A + 1 := by linarith
    have hkey := key (δ / (A + 1)) (by positivity)
    have hb : A * (δ / (A + 1)) ≤ δ := by
      rw [← mul_div_assoc, div_le_iff₀ hden]
      nlinarith [hδ.le, hAnn]
    rw [hAdef] at hkey
    linarith
  have hz : L - R = 0 := norm_eq_zero.mp (le_antisymm hle0 (norm_nonneg _))
  rw [hLdef, hRdef] at hz
  exact sub_eq_zero.mp hz

end Work.BoseFixB1.WinPair
