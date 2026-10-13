import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
import Mathlib.Order.CompletePartialOrder
import Submission.Work.EllipticEst.InteriorRegularity.exists_contDiffOn_of_memSobolev_all

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.EllipticEst.InteriorRegularity

open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap BesselPotentialSpace ENNReal ContDiff

/-- **Fourier-side Sobolev representation.**

If `u ∈ H^m(E)` with `m > dim E / 2 + k`, then there is an `L²` function `F` whose moments up to
order `k` are integrable and which represents `𝓕 u`:

`𝓕 u = F`, `F ∈ L¹`, and `ξ ↦ ‖ξ‖^n ‖F ξ‖ ∈ L¹` for every `n ≤ k`.

Indeed `MemSobolev` gives `(1+‖ξ‖²)^{m/2} 𝓕u = f ∈ L²`; dividing by the weight produces the `L²`
function `F` with `‖F ξ‖ = (1+‖ξ‖²)^{-m/2} ‖f ξ‖`, and the moment claim is Cauchy–Schwarz against
`ξ ↦ ‖ξ‖^n (1+‖ξ‖²)^{-m/2} ∈ L²`, which holds exactly when `dim E < 2 (m - n)`. -/
theorem fourier_rep_of_memSobolev {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : 𝓢'(E, ℂ)} {k m : ℕ} (hm : (Module.finrank ℝ E : ℝ) / 2 + (k:ℝ) < (m:ℝ))
    (h : TemperedDistribution.MemSobolev (m:ℝ) 2 u) :
    ∃ G : Lp ℂ 2 (volume : Measure E),
      𝓕 u = (G : 𝓢'(E, ℂ)) ∧ Integrable (G : E → ℂ) (volume : Measure E) ∧
      (∀ n : ℕ, n ≤ k → Integrable (fun ξ : E => ‖ξ‖^n * ‖(G : E → ℂ) ξ‖) (volume : Measure E)) := by
  obtain ⟨f, hf⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp h
  have hgt : (jbC (E:=E) m).HasTemperateGrowth := jbC_temperate m
  have hgit : (jbCinv (E:=E) m).HasTemperateGrowth := jbCinv_temperate m
  let G : Lp ℂ 2 (volume : Measure E) :=
    MemLp.toLp (jbCinv (E:=E) m) (jbCinv_memLp (E:=E) m) • f
  have hG : G = MemLp.toLp (jbCinv (E:=E) m) (jbCinv_memLp (E:=E) m) • f := rfl
  have hfm : smulLeftCLM ℂ (jbC (E:=E) m) (𝓕 u) = (f : 𝓢'(E, ℂ)) := hf
  have hsm : smulLeftCLM ℂ (jbCinv (E:=E) m) (f : 𝓢'(E, ℂ)) = 𝓕 u := by
    rw [← hfm, smulLeftCLM_smulLeftCLM_apply hgt hgit, jbC_mul_jbCinv, smulLeftCLM_const,
      one_smul]
  have hFG : 𝓕 u = (G : 𝓢'(E, ℂ)) := by
    rw [← hsm, hG, Lp.toTemperedDistribution_smul_eq hgit (jbCinv_memLp (E:=E) m) f]
  have hcoe : (G : E → ℂ) =ᵐ[volume] fun ξ : E => jbCinv (E:=E) m ξ * (f : E → ℂ) ξ := by
    rw [hG]
    filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
        (MemLp.toLp (jbCinv (E:=E) m) (jbCinv_memLp (E:=E) m)) f,
      MemLp.coeFn_toLp (jbCinv_memLp (E:=E) m)] with ξ h1 h2
    rw [h1]
    simp only [Pi.mul_apply, smul_eq_mul]
    rw [h2]
  have hnorm : ∀ ξ : E, ‖jbCinv (E:=E) m ξ‖ = (1 + ‖ξ‖^2) ^ (-(m:ℝ)/2) := by
    intro ξ
    rw [jbCinv_eq m, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  have hmom : ∀ n : ℕ, n ≤ k → Integrable (fun ξ : E => ‖ξ‖^n * ‖(G : E → ℂ) ξ‖)
      (volume : Measure E) := by
    intro n hn
    have hn' : (Module.finrank ℝ E : ℝ) < 2 * ((m : ℝ) - (n : ℝ)) := by
      have h1 : ((n:ℝ) ≤ (k:ℝ)) := by exact_mod_cast hn
      have h2 : (Module.finrank ℝ E : ℝ) < 2 * ((m:ℝ) - (k:ℝ)) := by linarith [hm]
      linarith
    have hB : MemLp (fun ξ : E => ‖ξ‖^n * (1 + ‖ξ‖^2) ^ (-(m:ℝ)/2)) 2 (volume : Measure E) :=
      memLp_moment_weight (E := E) (n := n) (m := m) hn'
    have hC : MemLp (fun ξ : E => ‖(f : E → ℂ) ξ‖) 2 (volume : Measure E) :=
      (Lp.memLp f).norm
    have hBC : MemLp ((fun ξ : E => ‖ξ‖^n * (1 + ‖ξ‖^2) ^ (-(m:ℝ)/2)) *
        (fun ξ : E => ‖(f : E → ℂ) ξ‖)) 1 (volume : Measure E) := hB.mul hC
    refine (memLp_one_iff_integrable.mp hBC).congr ?_
    filter_upwards [hcoe] with ξ hξ
    rw [hξ, norm_mul, hnorm ξ]
    simp only [Pi.mul_apply]
    ring
  have hGint : Integrable (G : E → ℂ) (volume : Measure E) :=
    (hmom 0 (Nat.zero_le k)).mono' (Lp.memLp G).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => by simp)
  exact ⟨G, hFG, hGint, hmom⟩

/-- **Local Sobolev embedding `H^m ⊆ C^k`.**

If `u ∈ H^m(E)` (Mathlib's Bessel potential space `TemperedDistribution.MemSobolev m 2`) with
`m > dim E / 2 + k`, then `u` is a `C^k` function locally: for every point `x` there is a radius
`r > 0` and a function `Φ`, of class `C^k` on `Metric.ball x r`, representing `u` on test
functions supported in that ball.

The proof is the standard Fourier-analytic one.  Write `𝓕 u = F` with
`(1+‖ξ‖²)^{m/2} F ∈ L²` (this is `MemSobolev`); then `F` is integrable and, for `n ≤ k`, the
weighted moment `ξ ↦ ‖ξ‖^n ‖F ξ‖` is integrable, because `‖ξ‖^n (1+‖ξ‖²)^{-m/2}` is square
integrable exactly when `dim E < 2 (m - n)`, which is what the hypothesis gives
(`fourier_rep_of_memSobolev`).  Hence `Φ := 𝓕⁻ F` is of class `C^k` by `Real.contDiff_fourier`,
and the distributional identity `u ψ = ∫ ψ • Φ` follows from the Fourier self-adjointness
identity by Fubini. -/
theorem exists_contDiffOn_of_memSobolev {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : 𝓢'(E, ℂ)} {k m : ℕ} (hm : (Module.finrank ℝ E : ℝ) / 2 + k < m)
    (h : TemperedDistribution.MemSobolev (m : ℝ) 2 u) (x : E) :
    ∃ r : ℝ, 0 < r ∧ ∃ Φ : E → ℂ, ContDiffOn ℝ k Φ (Metric.ball x r) ∧
      (∀ ψ : 𝓢(E, ℂ), (∀ y, ψ y ≠ 0 → y ∈ Metric.ball x r) →
        u ψ = ∫ y, ψ y • Φ y) := by
  obtain ⟨F, hF, hFint, hFmom⟩ := fourier_rep_of_memSobolev hm h
  have hc : ContDiff ℝ (k : ℕ∞ω) (𝓕 (F : E → ℂ)) := by
    refine Real.contDiff_fourier (N := (k : ℕ∞)) ?_
    intro n hn
    exact hFmom n (by exact_mod_cast hn)
  refine ⟨1, one_pos, fun y => 𝓕⁻ (F : E → ℂ) y, ?_, ?_⟩
  · have h1 : ContDiff ℝ (k : ℕ∞ω) (fun y : E => 𝓕 (F : E → ℂ) (-y)) := hc.comp contDiff_neg
    have h2 : (fun y : E => 𝓕⁻ (F : E → ℂ) y) = fun y : E => 𝓕 (F : E → ℂ) (-y) :=
      funext fun y => Real.fourierInv_eq_fourier_neg (F : E → ℂ) y
    rw [h2]
    exact h1.contDiffOn
  · intro ψ _
    calc u ψ = (𝓕⁻ (𝓕 u)) ψ := by rw [fourierInv_fourier_eq]
      _ = (𝓕 u) (𝓕⁻ ψ) := by rw [TemperedDistribution.fourierInv_apply]
      _ = ((F : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ)) (𝓕⁻ ψ) := by rw [hF]
      _ = ∫ ξ, 𝓕⁻ (ψ : E → ℂ) ξ • (F : E → ℂ) ξ := by
            rw [Lp.toTemperedDistribution_apply, SchwartzMap.fourierInv_coe]
      _ = ∫ ξ, (F : E → ℂ) ξ • 𝓕⁻ (ψ : E → ℂ) ξ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
            simp only [smul_eq_mul]
            ring
      _ = ∫ y, 𝓕⁻ (F : E → ℂ) y • (ψ : E → ℂ) y :=
            (integral_fourierInv_smul_eq_of_integrable hFint (SchwartzMap.integrable ψ)).symm
      _ = ∫ y, ψ y • 𝓕⁻ (F : E → ℂ) y := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
            simp only [smul_eq_mul]
            ring

end Work.EllipticEst.InteriorRegularity
