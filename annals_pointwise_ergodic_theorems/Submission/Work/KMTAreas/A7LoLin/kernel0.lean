/-
# The height-`0` Ionescu--Wainger multiplier as a bump-dilation convolution

At arithmetic height `0` the IW frequency set is the singleton `(ℚ/ℤ)_{≤0} = {0}`
(`Work.KMTAreas.A7.iwArithFreqs_zero`), so the height-`0` multiplier is the plain discrete
convolution with the Fourier transform of the (periodised) symbol:

  `Tle ρ 0 ψ f x = Σ'_j (𝓕ψ j) f (x - j)`.

For the dyadic cutoffs `ψ = η_{≤ -L}` (`L = m₀ + n`) the Fourier transform is the dilation of the
*fixed* Schwartz kernel `K₀ = 𝓕η`:

  `𝓕(η_{≤-L}) j = 2^{-L} K₀ (j / 2^L)`,

so the family `n ↦ kmtProj ρ 0 (-(m₀+n))` is exactly the lacunary bump-dilation family
`n ↦ bumpOp K₀ (2^{m₀+n}) n` of `Work.KMTAreas.A7.lacunaryBumpDilationVar`.  This is the bridge
which lets the (unmodulated) bottom-height low-pass estimate be read off from Lépingle's
inequality.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoErrAux
import Submission.Work.KMTAreas.A7.lacDilDefs
import Submission.Work.KMTAreas.A7.lacunaryBumpGlue

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTAreas.A7LoLin

open MeasureTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
open Work.KMTAreas.A7
open Work.Analysis.IonescuWainger

noncomputable section

/-- The fixed Schwartz kernel `K₀ = 𝓕 η`: the inverse Fourier transform of the KMT bump `η`. -/
noncomputable def K0 : SchwartzMap ℝ ℂ :=
  FourierTransform.fourier (Work.KMTAreas.A7.etaCutSchwartz 0)

theorem K0_coe :
    (K0 : ℝ → ℂ) = FourierTransform.fourier (Work.KMTContract.kmtEta : ℝ → ℂ) := by
  rw [K0, SchwartzMap.fourier_coe, Work.KMTAreas.A7.etaCutSchwartz_coe]
  congr 1
  funext θ
  simp [etaCut]

/-- The rescaled cutoff at level `-(L : ℤ)` is the `2^L`-dilation of `η`. -/
theorem etaCut_neg_apply (L : ℕ) (v : ℝ) :
    etaCut Work.KMTContract.kmtEta (-(L : ℤ)) v = Work.KMTContract.kmtEta (v * (2 : ℝ) ^ L) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  simp only [etaCut]
  congr 1
  rw [zpow_neg, zpow_natCast]
  field_simp

/-- **The Fourier transform of the rescaled cutoff `η_{≤-L}` is the dilation of `K₀`.** -/
theorem fourier_etaCut_neg (L : ℕ) (w : ℝ) :
    FourierTransform.fourier (etaCut Work.KMTContract.kmtEta (-(L : ℤ))) w
      = (1 / (2 : ℝ) ^ L) * (K0 : ℝ → ℂ) (w / (2 : ℝ) ^ L) := by
  rw [K0_coe]
  conv_lhs => rw [Real.fourier_eq']
  conv_rhs => rw [Real.fourier_eq']
  set a : ℝ := (2 : ℝ) ^ L with ha
  have hapos : 0 < a := by rw [ha]; positivity
  have hinner : ∀ x y : ℝ, inner ℝ x y = y * x := fun x y => by simp
  have hstep : ∀ v : ℝ,
      Complex.exp (↑(-2 * Real.pi * inner ℝ v w) * Complex.I) •
          etaCut Work.KMTContract.kmtEta (-(L : ℤ)) v
        = (fun u : ℝ => Complex.exp (↑(-2 * Real.pi * inner ℝ u (w / a)) * Complex.I) •
            (Work.KMTContract.kmtEta u : ℂ)) (a * v) := by
    intro v
    rw [etaCut_neg_apply L v, ha]
    have harg : v * (2 : ℝ) ^ L = (2 : ℝ) ^ L * v := mul_comm _ _
    have hexp : -2 * Real.pi * inner ℝ v w
        = -2 * Real.pi * inner ℝ ((2 : ℝ) ^ L * v) (w / (2 : ℝ) ^ L) := by
      rw [hinner, hinner]
      field_simp
    rw [harg, hexp]
  have hint := MeasureTheory.integral_congr_ae (μ := MeasureTheory.volume)
    (Filter.Eventually.of_forall hstep)
  let g : ℝ → ℂ := fun u => Complex.exp (↑(-2 * Real.pi * inner ℝ u (w / a)) * Complex.I) •
      (Work.KMTContract.kmtEta u : ℂ)
  have hg : (∫ v : ℝ, (fun u : ℝ =>
          Complex.exp (↑(-2 * Real.pi * inner ℝ u (w / a)) * Complex.I) •
            (Work.KMTContract.kmtEta u : ℂ)) (a * v))
      = ∫ v : ℝ, g (a * v) := by simp only [g]
  rw [hint, hg, Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hapos)]
  simp only [smul_eq_mul, g]
  rw [ha]
  simp only [one_div, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]

/-- The `j`-th IW kernel of the level-`0` symbol is the dilated kernel `K₀`. -/
theorem iwKernel_zero_eq (ρ : ℝ) (L : ℕ) (j : ℤ) :
    Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ 0)
        (Work.Analysis.IonescuWainger.periodize
          (etaCut Work.KMTContract.kmtEta (-(L : ℤ))))) j
      = (1 / (2 : ℝ) ^ L) * (K0 : ℝ → ℂ) ((j : ℝ) / (2 : ℝ) ^ L) := by
  rw [Work.KMTAreas.A7.IwKernelEqFourier ρ 0 (-(L : ℤ)) j, Work.KMTAreas.A7.iwArithFreqs_zero]
  have h0 : ((AddCircle.equivIco (1 : ℝ) 0 (((0 : ℝ)) : AddCircle (1 : ℝ))) : ℝ) = 0 :=
    AddCircle.equivIco_coe_of_mem (p := (1 : ℝ)) (a := (0 : ℝ)) (y := (0 : ℝ)) (by simp)
  have hfun : (fun y : ℝ =>
        ∑ α ∈ ({(0 : Work.Analysis.IonescuWainger.Circle)} : Finset _),
          etaCut Work.KMTContract.kmtEta (-(L : ℤ))
            (y - (((AddCircle.equivIco (1 : ℝ) 0 α) : ℝ))))
      = fun y : ℝ => etaCut Work.KMTContract.kmtEta (-(L : ℤ)) y := by
    funext y
    rw [Finset.sum_singleton]
    congr 1
    rw [show (0 : Work.Analysis.IonescuWainger.Circle) = ((0 : ℝ) : AddCircle (1 : ℝ)) from rfl]
    rw [h0]
    ring
  rw [hfun]
  exact fourier_etaCut_neg L (j : ℝ)

/-- **The height-`0` IW projection at level `-(m₀+n)` is the bump-dilation operator.** -/
theorem kmtProj_zero_eq_bumpOp (ρ : ℝ) (m₀ n : ℕ) (f : ℤ → ℂ) :
    Work.KMTContract.kmtProj ρ 0 (-((m₀ : ℤ) + (n : ℤ))) f
      = Work.KMTAreas.A7.bumpOp K0 (fun k => 2 ^ (m₀ + k)) n f := by
  funext x
  have hcasts : (-((m₀ : ℤ) + (n : ℤ))) = -(((m₀ + n : ℕ)) : ℤ) := by push_cast; ring
  rw [Work.KMTContract.kmtProj, Work.Analysis.IWMultiplier.iwConv_apply,
    Work.KMTAreas.A7.bumpOp]
  refine tsum_congr (fun j => ?_)
  rw [hcasts, iwKernel_zero_eq ρ (m₀ + n) j]
  simp only [smul_eq_mul]
  push_cast
  ring_nf

/-- **The height-`0` IW projection at the dyadic level `m` is the bump-dilation operator.** -/
theorem kmtProj_zero_eq_bumpOp_zero (ρ : ℝ) (m : ℕ) (f : ℤ → ℂ) :
    Work.KMTContract.kmtProj ρ 0 (-(m : ℤ)) f
      = Work.KMTAreas.A7.bumpOp K0 (fun k => 2 ^ k) m f := by
  have h := kmtProj_zero_eq_bumpOp ρ 0 m f
  simpa [Nat.zero_add] using h

/-- **Additivity of `Tle` in the symbol**, for bounded input. -/
theorem Tle_add_of_bounded {ρ : ℝ} {l : ℕ} {φ ψ : ℝ → ℂ}
    (hφ : Adm (iwArithFreqs ρ l) φ) (hψ : Adm (iwArithFreqs ρ l) ψ)
    {f : ℤ → ℂ} {B : ℝ} (hf : ∀ m : ℤ, ‖f m‖ ≤ B) :
    Tle ρ l (φ + ψ) f = Tle ρ l φ f + Tle ρ l ψ f := by
  have hper : periodize (φ + ψ) = periodize φ + periodize ψ := periodize_add hφ.1 hψ.1
  simp only [Tle, hper]
  exact iwConv_add_of_bounded hf hφ.2.1 hψ.2.1 hφ.2.2 hψ.2.2

end

end Work.KMTAreas.A7LoLin
