import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.FRK.kinFT_conv_mul
import Submission.Work.BoseBoxFock.hatChi_lattice_tail_le
import Submission.Work.BoseBoxFock.pinQLimDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pinQBl_eq_periodisation` — the closed form of the first `χ̂`-lattice sum

`pinQBl ℓ W w = Σ'_n Ŵ(k_n) χ̂(ℓ k_n) e^{i⟪k_n,w⟫}` (`k_n = kmomInt ℓ n = (2π/ℓ)·latVec n`)
is the *limit* of the `pinQB`-row of the `Q₂` kernel expansion.  The target identifies it with
the **periodisation of the windowed convolution**:

    `Σ'_m ∫_x W(x)·χ_ℓ(w + ℓ·latVec m − x) dx = Σ'_m (W ⋆ χ_ℓ)(w + ℓ·latVec m)`,

`χ_ℓ = chiScale ℓ = χ(·/ℓ)`.  This is the input of the word matching of
`FINDING_PotPairRows_exists.md` (there: `pinQBl = Σ_m (W⋆χ_Λ)(·+ℓm)`).

## Proof

Everything is pushed through the **lattice Poisson (aliasing) identity**
`latticePoisson_kernel`, applied to the *smooth* function `G = W ⋆ χ_ℓ` (the honest weight `W`
is only `L^∞` with compact support, so it cannot be fed to Poisson directly — but the windowed
convolution is `C^∞` with compact support, and its Fourier samples are the target's summands):

* `G` is `C^∞` with compact support: `HasCompactSupport.contDiff_convolution_right` (the `χ_ℓ`
  factor is smooth with compact support, the `W` factor is locally integrable since bounded,
  a.e. strongly measurable and compactly supported) and `HasCompactSupport.convolution`;
* the Fourier samples factorise, `kinFT G p = kinFT W p · kinFT (χ_ℓ) p`
  (`FRK.kinFT_conv_mul`, the `L¹` convolution theorem), and each factor is the target's:
  `kinFT W = chat W` for *even* `W` (`chat_eq_kinFT_of_even` — this is where `hWev` enters),
  and `kinFT (χ_ℓ) p = ℓ³·χ̂(ℓ p)` (`OneBodyKin.kinFT_chiScale` + `profHat = hatChi`);
* Poisson summation (`latticePoisson_kernel`) then gives
  `Σ_n kinFT G(k_n) e^{i⟪k_n,w⟫} = ℓ³ Σ_m G(w + ℓ·latVec m)`, whose left side is `ℓ³·pinQBl`
  (by the two factorisations above), so the `ℓ³` cancels against the dilation factor of `kinFT χ_ℓ`
  and only the termwise identity `G z = ∫_x W x·χ_ℓ(z−x)dx` remains.

No summability hypothesis has to be supplied by hand: it is exactly what
`latticePoisson_kernel` (through `summable_kinFT_lattice_phase`) provides in this `C^∞` case.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

set_option maxHeartbeats 4000000

theorem pinQBl_eq_periodisation {ℓ : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWm : MeasureTheory.AEStronglyMeasurable W MeasureTheory.volume)
    (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : HasCompactSupport W)
    (hWev : ∀ z, W (-z) = W z) (w : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.pinQBl ℓ W w
      = ∑' m : Fin 3 → ℤ, ∫ x : EuclideanSpace ℝ (Fin 3),
          ((W x : ℝ) : ℂ) * ((Submission.BoseGases.chiScale ℓ
            (w + ℓ • Work.BoseBoxFock.latVec m - x) : ℝ) : ℂ) := by
  classical
  obtain ⟨C, hC⟩ := hWb
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  -- the honest weight `W` is `L¹` (bounded, a.e. strongly measurable, compactly supported)
  have hWint : MeasureTheory.Integrable W := MeasureTheory.memLp_one_iff_integrable.mp
    (hWs.memLp_of_bound hWm C (Filter.Eventually.of_forall hC))
  have hWIntC : MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin 3) => (W y : ℂ)) :=
    hWint.ofReal
  have hWcs : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin 3) => (W y : ℂ)) := by
    simpa [Function.comp_def] using hWs.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  -- the window `chiScale ℓ` and its complexification
  have hAcd : ContDiff ℝ (⊤ : ℕ∞) (Submission.BoseGases.chiScale ℓ) :=
    Submission.BoseGases.chiScale_contDiff hℓne
  have hAcs : HasCompactSupport (Submission.BoseGases.chiScale ℓ) :=
    Submission.BoseGases.chiScale_hasCompactSupport hℓne
  have hAcCd : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 3) => (Submission.BoseGases.chiScale ℓ y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hAcd
  have hAcCs : HasCompactSupport
      (fun y : EuclideanSpace ℝ (Fin 3) => (Submission.BoseGases.chiScale ℓ y : ℂ)) := by
    simpa [Function.comp_def] using hAcs.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  have hAcInt : MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin 3) => (Submission.BoseGases.chiScale ℓ y : ℂ)) :=
    hAcCd.continuous.integrable_of_hasCompactSupport hAcCs
  -- **the smooth periodised object** `G = W ⋆ chiScale ℓ`
  set G : EuclideanSpace ℝ (Fin 3) → ℂ := MeasureTheory.convolution
      (fun y : EuclideanSpace ℝ (Fin 3) => (W y : ℂ))
      (fun y : EuclideanSpace ℝ (Fin 3) => (Submission.BoseGases.chiScale ℓ y : ℂ))
      (ContinuousLinearMap.mul ℝ ℂ) MeasureTheory.volume with hGdef
  have hGint : ∀ z : EuclideanSpace ℝ (Fin 3), G z
      = ∫ y : EuclideanSpace ℝ (Fin 3),
          (W y : ℂ) * (Submission.BoseGases.chiScale ℓ (z - y) : ℂ) := by
    intro z
    rw [hGdef, MeasureTheory.convolution_def]
    apply integral_congr_ae
    filter_upwards with t
    rfl
  have hGcd : ContDiff ℝ (⊤ : ℕ∞) G := by
    rw [hGdef]
    exact hAcCs.contDiff_convolution_right (L := ContinuousLinearMap.mul ℝ ℂ)
      hWIntC.locallyIntegrable hAcCd
  have hGcs : HasCompactSupport G := by
    rw [hGdef]
    exact hWcs.convolution (L := ContinuousLinearMap.mul ℝ ℂ) hAcCs
  -- **the Fourier samples of `G` are the target's summands**
  have hkinFT : ∀ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.kinFT G p
      = ((Work.BoseFixR.chat W p : ℝ) : ℂ)
        * ((ℓ : ℂ) ^ 3 * ((Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ)) := by
    intro p
    have h1 : Submission.BoseGases.kinFT G p
        = Submission.BoseGases.kinFT
            (fun y : EuclideanSpace ℝ (Fin 3) => (W y : ℂ)) p
          * Submission.BoseGases.kinFT
              (fun y : EuclideanSpace ℝ (Fin 3) =>
                (Submission.BoseGases.chiScale ℓ y : ℂ)) p := by
      rw [hGdef]
      exact Work.BoseBoxFock.FRK.kinFT_conv_mul hWIntC hAcInt p
    rw [h1, (Work.BoseBoxFock.chat_eq_kinFT_of_even hWev p).symm,
      Work.OneBodyKin.kinFT_chiScale hℓ p]
    rfl
  have hterm : ∀ n : Fin 3 → ℤ,
      Submission.BoseGases.kinFT G (Work.BoseBoxFock.kmomInt ℓ n)
        * Complex.exp (Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) w : ℝ) : ℂ))
      = (ℓ : ℂ) ^ 3
          * (((Work.BoseFixR.chat W (Work.BoseBoxFock.kmomInt ℓ n) : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomInt ℓ n) : ℝ) : ℂ)
          * Complex.exp (Complex.I *
              ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) w : ℝ) : ℂ))) := by
    intro n
    rw [hkinFT]
    ring
  -- the lattice sum against `G` is `ℓ³` times the target's left-hand side
  have hA : (∑' n : Fin 3 → ℤ,
        Submission.BoseGases.kinFT G (Work.BoseBoxFock.kmomInt ℓ n)
          * Complex.exp (Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) w : ℝ) : ℂ)))
      = (ℓ : ℂ) ^ 3 * Work.BoseBoxFock.pinQBl ℓ W w := by
    rw [tsum_congr hterm, tsum_mul_left]
    rfl
  -- **the lattice Poisson (aliasing) identity for `G`**
  have hP : (∑' n : Fin 3 → ℤ,
        Submission.BoseGases.kinFT G (Work.BoseBoxFock.kmomInt ℓ n)
          * Complex.exp (Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) w : ℝ) : ℂ)))
      = (ℓ : ℂ) ^ 3
          * ∑' m : Fin 3 → ℤ, G (w + ℓ • Work.BoseBoxFock.latVec m) :=
    Work.BoseBoxFock.latticePoisson_kernel ℓ hℓ G hGcd hGcs w
  -- the `ℓ³` cancels
  have hcancel : Work.BoseBoxFock.pinQBl ℓ W w
      = ∑' m : Fin 3 → ℤ, G (w + ℓ • Work.BoseBoxFock.latVec m) := by
    have h3 : ((ℓ : ℂ) ^ 3) ≠ 0 := pow_ne_zero 3 (by exact_mod_cast hℓne)
    refine mul_left_cancel₀ h3 ?_
    rw [← hA, hP]
  rw [hcancel]
  -- the convolution is the target's integrand
  refine tsum_congr (fun m => ?_)
  rw [hGint]

end Work.BoseBoxFock
