import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Commons.Analysis.Fourier.integral_mul_eq_integral_fourier_mul
import Submission.Work.BoseFixB1.BoxPairIntGenC2.boxC2SumC2
import Submission.Work.BoseFixB1.BoxPairIntGenC2.boxFourierDens_eqC2
import Submission.Work.BoseFixB1.BoxPairIntGenC2.boxPairDensSum_evenC2
import Submission.Work.BoseFixB1.BoxPairIntGenC2.boxRelDensC2
import Submission.Work.BoseFixB1.BoxPairIntGenC2.densC2Clean
import Submission.Work.BoseFixB1.BoxPairIntGenC2.fourier_memLp_one_of_contDiff_two
import Submission.Work.BoseFixB1.WinPair.plancherel_of_bounded_of_fourier_memLp
import Submission.Work.BoseFixB1.boxTauPairingReduction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxPairIntGenC2` — the general-profile box pairing identity at a `C²` window

This module proves the `C²`-window version of the general-profile box pairing identity: for a
measurable box `Ac ⊆ acube a` of volume `volA`, a window `χ` with `ContDiff ℝ 2 χ` vanishing off
`Ac`, an integrable profile `𝒲` and a smooth state `Ψ`,

`boxA2 a volA Ac (fun x y => χ x * χ y * 𝒲 (x − y)) Ψ
    = (2π)⁻³ ∫_q pairW 𝒲 q · (volA⁻¹ · boxWinModeRGen a volA Ac χ Ψ q)`.

The proof combines three independently proved pieces:

* `Work.BoseFixB1.BoxPairIntGenC2.boxRelDensC2` — the relative-coordinate decomposition
  `boxA2 = ∫_u 𝒲 u · boxPairDensSum volA a Ac χ Ψ u`;
* `boxPlancherelC2` (below) — the one-sided Plancherel identity at the `C²` density, which needs
  the integrability of the Fourier transform of a `C²` compactly supported function
  (`BoxPairIntGenC2.fourier_memLp_one_of_contDiff_two`) and the evenness of the pair density
  (`BoxPairIntGenC2.boxPairDensSum_evenC2`) to extract the real part of the Fourier transform;
* `boxDensFourier_eq_winModeRGenC2` — the identification
  `boxPairDensFourier = volA⁻¹ · boxWinModeRGen`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal FourierTransform RealInnerProductSpace

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Elementary helpers -/

/-- `∫_q F ((2π)•q) = (2π)⁻³ ∫_q F q` (Haar measure on `ℝ³`). -/
lemma integral_comp_smul_twoPi_real (F : E3 → ℝ) :
    (∫ q : E3, F ((2 * Real.pi) • q)) = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3, F q := by
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure E3) F (2 * Real.pi)
    (hR := by positivity)
  rw [finrank_euclideanSpace, Fintype.card_fin] at h
  simpa only [smul_eq_mul] using h

/-- `pairW 𝒲 ((2π)•q) = Re (𝓕 𝒲) q`. -/
lemma pairW_twoPi_smul (W : E3 → ℝ) (q : E3) :
    Submission.BoseGases.pairW W ((2 * Real.pi) • q)
      = (FourierTransform.fourier (fun x => (W x : ℂ)) q).re := by
  rw [Submission.BoseGases.pairW]
  congr 1
  rw [smul_smul, inv_mul_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_smul]

/-! ## The one-sided Plancherel identity at the `C²` box pair density -/

/-- **One-sided Plancherel at the box pair density (C² window).**

The relative-coordinate `u`-integral of the profile `𝒲` against the box pair density is the
momentum integral of `pairW 𝒲` against the real part of the momentum-space pair content.

The density `boxPairDensSum` is `C²` with compact support (so its Fourier transform is `L¹`,
`BoxPairIntGenC2.fourier_memLp_one_of_contDiff_two`), and it is *even*, so its Fourier transform is real-valued.
The one-sided Plancherel/multiplication identity
(`Work.BoseFixB1.WinPair.plancherel_of_bounded_of_fourier_memLp`) applied with the density on the
bounded-`L¹` side and the integrable `𝒲` on the `L¹` side then gives the claim after the
`(2π)`-rescaling of the momentum variable. -/
theorem boxPlancherelC2 {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {χ : E3 → ℝ} (hχc : ContDiff ℝ 2 χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ A → χ z = 0)
    {Ψ : Submission.BoseGases.X (N + 2) → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    {W : E3 → ℝ} (hW : MeasureTheory.Integrable W) :
    (∫ u, W u * Work.BoseFixB1.boxPairDensSum volA ℓ A χ Ψ u)
      = ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ q, Submission.BoseGases.pairW W q
            * (Work.BoseFixB1.boxPairDensFourier volA ℓ A χ Ψ q).re := by
  classical
  set Dens : E3 → ℝ := Work.BoseFixB1.boxPairDensSum volA ℓ A χ Ψ with hDens
  have hDensVal : ∀ u : E3, Dens u = Work.BoseFixB1.boxPairDensSum volA ℓ A χ Ψ u :=
    fun u => rfl
  obtain ⟨hDensC2, hDensCS⟩ :=
    BoxPairIntGenC2.boxPairDensSum_contDiff_two_clean hA hℓ hAc hvolA hvolpos hχc hχs hχsupp hΨ
  have hDensCont : Continuous Dens := hDensC2.continuous
  have hDensCSC : HasCompactSupport (fun u : E3 => (Dens u : ℂ)) :=
    hDensCS.comp_left (g := fun z : ℝ => (z : ℂ)) (by simp)
  obtain ⟨Cb, hCb⟩ := hDensCS.exists_bound_of_continuous hDensCont
  have hbdd : ∃ C : ℝ, ∀ x, ‖(Dens x : ℂ)‖ ≤ C :=
    ⟨max Cb 0, fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact le_trans (hCb x) (le_max_left _ _)⟩
  have hDensInt : Integrable (fun u : E3 => (Dens u : ℂ)) :=
    (hDensCont.integrable_of_hasCompactSupport hDensCS).ofReal
  have hf1 : MeasureTheory.MemLp (fun u : E3 => (Dens u : ℂ)) 1
      (MeasureTheory.volume : Measure E3) := memLp_one_iff_integrable.mpr hDensInt
  have hFc2 : ContDiff ℝ 2 (fun u : E3 => (Dens u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hDensC2
  have hfF : MeasureTheory.MemLp
      (FourierTransform.fourier (fun u : E3 => (Dens u : ℂ))) 1
      (MeasureTheory.volume : Measure E3) :=
    BoxPairIntGenC2.fourier_memLp_one_of_contDiff_two hFc2 hDensCSC
  have hg1 : MeasureTheory.MemLp (fun u : E3 => (W u : ℂ)) 1
      (MeasureTheory.volume : Measure E3) := memLp_one_iff_integrable.mpr hW.ofReal
  have hplan := WinPair.plancherel_of_bounded_of_fourier_memLp hf1 hbdd hfF hg1
  -- the density is even, hence its Fourier transform is real-valued
  have hDensEven : ∀ u : E3, Dens (-u) = Dens u := fun u =>
    BoxPairIntGenC2.boxPairDensSum_evenC2 hA hℓ hAc hvolA hvolpos hχc.continuous hχs hχsupp
      hΨ.continuous u
  have hFcReal : ∀ v : E3, star ((fun u : E3 => (Dens u : ℂ)) v)
      = (fun u : E3 => (Dens u : ℂ)) v := fun v => Complex.conj_ofReal _
  have hFeven : ∀ q : E3,
      FourierTransform.fourier (fun u : E3 => (Dens u : ℂ)) (-q)
        = FourierTransform.fourier (fun u : E3 => (Dens u : ℂ)) q := by
    intro q
    rw [Real.fourier_eq, Real.fourier_eq]
    have key1 : (fun v : E3 => 𝐞 (-⟪v, -q⟫) • ((Dens v : ℝ) : ℂ))
        = fun v : E3 => 𝐞 (⟪v, q⟫) • ((Dens v : ℝ) : ℂ) := by
      funext v
      rw [inner_neg_right, neg_neg]
    have key2 : (fun v : E3 => 𝐞 (⟪v, q⟫) • ((Dens v : ℝ) : ℂ))
        = fun v : E3 => 𝐞 (⟪v, q⟫) • ((Dens (-v) : ℝ) : ℂ) := by
      funext v
      rw [hDensEven v]
    rw [key1, key2]
    trans ∫ x : E3, 𝐞 (-⟪-x, q⟫) • ((Dens (-x) : ℝ) : ℂ)
    · refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      simp only [inner_neg_left, neg_neg]
    · exact integral_neg_eq_self (fun w : E3 => 𝐞 (-⟪w, q⟫) • ((Dens w : ℝ) : ℂ)) volume
  have hconj : ∀ q : E3,
      FourierTransform.fourier (fun u : E3 => (Dens u : ℂ)) (-q)
        = star (FourierTransform.fourier (fun u : E3 => (Dens u : ℂ)) q) := by
    intro q
    have h := Commons.Analysis.Fourier.fourier_star_apply (V := E3)
      (fun u : E3 => (Dens u : ℂ)) (-q)
    rw [show (fun x : E3 => star ((fun u : E3 => (Dens u : ℂ)) x))
        = (fun u : E3 => (Dens u : ℂ)) from funext hFcReal] at h
    simpa using h
  have him : ∀ q : E3, (FourierTransform.fourier (fun u : E3 => (Dens u : ℂ)) q).im = 0 := by
    intro q
    have h2 : star (FourierTransform.fourier (fun u : E3 => (Dens u : ℂ)) q)
        = FourierTransform.fourier (fun u : E3 => (Dens u : ℂ)) q := by
      rw [← hconj q, hFeven q]
    exact Complex.conj_eq_iff_im.mp h2
  -- integrability of the Plancherel integrand
  have hFourierMul : Integrable (fun q : E3 =>
      FourierTransform.fourier (fun u : E3 => (Dens u : ℂ)) q
        * FourierTransform.fourier (fun u : E3 => (W u : ℂ)) (-q)) :=
    WinPair.integrable_fourier_mul_fourier_neg_of_integrable
      (memLp_one_iff_integrable.mp hfF) hW.ofReal
  have hInt2 : Integrable (fun q : E3 =>
      FourierTransform.fourier (fun u : E3 => (Dens u : ℂ)) (-q)
        * FourierTransform.fourier (fun u : E3 => (W u : ℂ)) q) := by
    have h := hFourierMul.comp_neg
    simpa only [neg_neg] using h
  have hLHS : (∫ u : E3, (Dens u : ℂ) * (W u : ℂ))
      = ((∫ u, Dens u * W u : ℝ) : ℂ) := by
    have h1 : (∫ u : E3, (Dens u : ℂ) * (W u : ℂ))
        = ∫ u : E3, ((Dens u * W u : ℝ) : ℂ) :=
      integral_congr_ae (Eventually.of_forall fun u => (Complex.ofReal_mul (Dens u) (W u)).symm)
    rw [h1]
    exact integral_ofReal
  have hneg : (∫ q : E3, FourierTransform.fourier (fun u : E3 => (Dens u : ℂ)) q
        * FourierTransform.fourier (fun u : E3 => (W u : ℂ)) (-q))
      = ∫ q : E3, FourierTransform.fourier (fun u : E3 => (Dens u : ℂ)) (-q)
          * FourierTransform.fourier (fun u : E3 => (W u : ℂ)) q := by
    have h := integral_neg_eq_self
      (fun q : E3 => FourierTransform.fourier (fun u : E3 => (Dens u : ℂ)) q
        * FourierTransform.fourier (fun u : E3 => (W u : ℂ)) (-q)) volume
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [neg_neg]
  have hkey : (∫ q : E3, FourierTransform.fourier (fun u : E3 => (Dens u : ℂ)) (-q)
        * FourierTransform.fourier (fun u : E3 => (W u : ℂ)) q)
      = ((∫ u, Dens u * W u : ℝ) : ℂ) := by
    rw [← hneg]
    exact hplan.symm.trans hLHS
  have him0 : (Complex.imCLM (∫ q : E3,
      FourierTransform.fourier (fun u : E3 => (Dens u : ℂ)) (-q)
        * FourierTransform.fourier (fun u : E3 => (W u : ℂ)) q)) = 0 := by
    have h := Complex.imCLM.integral_comp_comm
      (φ := fun q : E3 => FourierTransform.fourier (fun u : E3 => (Dens u : ℂ)) (-q)
        * FourierTransform.fourier (fun u : E3 => (W u : ℂ)) q) hInt2
    rw [hkey]
    simp
  have hre : (∫ q : E3, FourierTransform.fourier (fun u : E3 => (Dens u : ℂ)) (-q)
        * FourierTransform.fourier (fun u : E3 => (W u : ℂ)) q)
      = ((∫ q : E3, (FourierTransform.fourier (fun u : E3 => (Dens u : ℂ)) (-q)).re
          * (FourierTransform.fourier (fun u : E3 => (W u : ℂ)) q).re : ℝ) : ℂ) := by
    refine Complex.ext ?_ ?_
    · rw [Complex.ofReal_re]
      simp only [← Complex.reCLM_apply]
      have h := Complex.reCLM.integral_comp_comm
        (φ := fun q : E3 => FourierTransform.fourier (fun u : E3 => (Dens u : ℂ)) (-q)
          * FourierTransform.fourier (fun u : E3 => (W u : ℂ)) q) hInt2
      rw [← h]
      refine integral_congr_ae (Eventually.of_forall fun q => ?_)
      dsimp only
      simp only [Complex.reCLM_apply]
      rw [Complex.mul_re, him (-q), zero_mul, sub_zero]
    · rw [Complex.ofReal_im]
      simp only [← Complex.imCLM_apply]
      exact him0
  have hreal : (∫ u, Dens u * W u) = ∫ q : E3,
      (Work.BoseFixB1.boxPairDensFourier volA ℓ A χ Ψ ((2 * Real.pi) • q)).re
        * Submission.BoseGases.pairW W ((2 * Real.pi) • q) := by
    have h1 : (∫ q : E3, (FourierTransform.fourier (fun u : E3 => (Dens u : ℂ)) (-q)).re
          * (FourierTransform.fourier (fun u : E3 => (W u : ℂ)) q).re)
        = ∫ u, Dens u * W u := by
      have h := hkey
      rw [hre] at h
      exact Complex.ofReal_injective h
    rw [← h1]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [hDens]
    rw [BoxPairIntGenC2.boxFourierDens_eqC2 hA hℓ hAc hvolA hvolpos hχc.continuous hχs hχsupp
      hΨ.continuous q, ← pairW_twoPi_smul W q]
  have hgoal : (fun u => W u * Work.BoseFixB1.boxPairDensSum volA ℓ A χ Ψ u)
      = fun u => Dens u * W u := by
    funext u
    rw [hDensVal u]
    ring
  rw [hgoal, hreal]
  rw [show (∫ q : E3, (Work.BoseFixB1.boxPairDensFourier volA ℓ A χ Ψ ((2 * Real.pi) • q)).re
        * Submission.BoseGases.pairW W ((2 * Real.pi) • q))
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
          (Work.BoseFixB1.boxPairDensFourier volA ℓ A χ Ψ q).re
            * Submission.BoseGases.pairW W q from
    integral_comp_smul_twoPi_real (fun q : E3 =>
      (Work.BoseFixB1.boxPairDensFourier volA ℓ A χ Ψ q).re * Submission.BoseGases.pairW W q)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  ring

/-! ## The identification of the momentum-space contents -/

/-- `boxWinModeC` at `-p` is the complex conjugate of `boxWinModeC` at `p`. -/
lemma boxWinModeC_neg_eq_star (volA : ℝ) (A : Set E3) (χ : E3 → ℝ) (p : E3) :
    boxWinModeC volA A χ (-p) = fun z => star (boxWinModeC volA A χ p z) := by
  funext z
  simp only [Complex.star_def]
  have hE : ∀ w : E3,
      (starRingEnd ℂ) (Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ))))
        = Complex.exp (-(Complex.I * ((inner ℝ (-p) w : ℝ) : ℂ))) := by
    intro w
    rw [← Complex.exp_conj]
    congr 1
    rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, inner_neg_left]
    push_cast
    ring
  have hstar : ∀ w : E3,
      (starRingEnd ℂ) ((χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ))))
        = (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ (-p) w : ℝ) : ℂ))) := by
    intro w
    rw [map_mul, Complex.conj_ofReal, hE w]
  have hInt : (∫ w in A, (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ (-p) w : ℝ) : ℂ))))
      = (starRingEnd ℂ) (∫ w in A,
          (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ)))) := by
    rw [← integral_conj]
    exact integral_congr_ae (Filter.Eventually.of_forall fun w => (hstar w).symm)
  have hind : (starRingEnd ℂ) (A.indicator (fun _ => (1 : ℂ)) z)
      = A.indicator (fun _ => (1 : ℂ)) z := by
    by_cases hz : z ∈ A
    · rw [Set.indicator_of_mem hz, map_one]
    · rw [Set.indicator_of_notMem hz, map_zero]
  have hinner : (starRingEnd ℂ)
        ((χ z : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ)))
          - ((volA⁻¹ : ℝ) : ℂ) * ∫ w in A,
              (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ))))
      = (χ z : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ (-p) z : ℝ) : ℂ)))
        - ((volA⁻¹ : ℝ) : ℂ) * ∫ w in A,
            (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ (-p) w : ℝ) : ℂ))) := by
    rw [map_sub, hstar z, map_mul, Complex.conj_ofReal, hInt]
  rw [boxWinModeC, boxWinModeC, map_mul, hind, hinner]

/-! ## The identification of the momentum-space contents -/

theorem boxDensFourier_eq_winModeRGenC2 {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {χ : E3 → ℝ} (hχc : ContDiff ℝ 2 χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ A → χ z = 0)
    {Ψ : Submission.BoseGases.X (N + 2) → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (q : E3) :
    (Work.BoseFixB1.boxPairDensFourier volA ℓ A χ Ψ q).re
      = volA⁻¹ * Work.BoseFixB1.boxWinModeRGen ℓ volA A χ Ψ q := by
  have hχcont : Continuous χ := hχc.continuous
  have hΨcont : Continuous Ψ := hΨ.continuous
  have hC2 := boxC2SumC2 hA hℓ hAc hvolA hvolpos hχc hχs hχsupp hΨ q
  have hred := boxTauPairingReduction_core (volA := volA) (A := A) hA hℓ hAc hχcont hχs hΨcont q
    (fun x hx => boxTauDagGen_comm_smooth hA hℓ hAc
      (continuous_boxWinModeImSmooth volA A hχcont q)
      (continuous_boxWinModeReSmooth volA A hχcont q)
      (integral_boxWinModeImSmooth_eq_zero hℓ hAc hvolA hvolpos hχcont hχs q)
      (integral_boxWinModeReSmooth_eq_zero hℓ hAc hvolA hvolpos hχcont hχs q)
      hΨcont x hx)
    (boxTauDagGen_pairing_integral hA hℓ hAc hvolpos
      (continuous_boxWinModeReSmooth volA A hχcont q) hΨcont)
    (boxTauDagGen_pairing_integral hA hℓ hAc hvolpos
      (continuous_boxWinModeImSmooth volA A hχcont q) hΨcont)
  have hval : (volA : ℂ) * Work.BoseFixB1.boxPairDensFourier volA ℓ A χ Ψ q
      = ((Work.BoseFixB1.boxWinModeRGen ℓ volA A χ Ψ q : ℝ) : ℂ) := by
    rw [← hC2, boxWinModeC_neg_eq_star]
    exact hred
  have hre := congrArg Complex.re hval
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.ofReal_re] at hre
  rw [← hre, inv_mul_cancel_left₀ (ne_of_gt hvolpos)]


/-! ## The target -/

theorem boxPairIntGenC2 {n : ℕ} (hn : 2 ≤ n) {a volA : ℝ} (ha : 0 < a)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : ContDiff ℝ (2 : ℕ∞) χ)
    (hχs : HasCompactSupport χ) (hχsupp : ∀ z, z ∉ Ac → χ z = 0)
    {𝒲 : EuclideanSpace ℝ (Fin 3) → ℝ} (h𝒲int : MeasureTheory.Integrable 𝒲)
    (h𝒲c : Continuous 𝒲)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    Work.BoseFixB1.boxA2 a volA Ac (fun x y => χ x * χ y * 𝒲 (x - y)) Ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.pairW 𝒲 q
            * (volA⁻¹ * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q) := by
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = N + 2 := ⟨n - 2, by omega⟩
  rw [BoxPairIntGenC2.boxRelDensC2 hAcm ha hAcsub hvol hvolpos hχc.continuous hχs hχsupp hΨ
    h𝒲int]
  rw [boxPlancherelC2 hAcm ha hAcsub hvol hvolpos hχc hχs hχsupp hΨ h𝒲int]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  dsimp only
  rw [boxDensFourier_eq_winModeRGenC2 hAcm ha hAcsub hvol hvolpos hχc hχs hχsupp hΨ q]

end Work.BoseFixB1
