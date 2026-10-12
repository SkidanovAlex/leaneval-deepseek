import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.pinQBl_eq_periodisation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pinQBl_eq_periodisation_L1` — the closed form of the first `χ̂`-lattice sum,
for an `L¹` (merely integrable) weight

`pinQBl ℓ W w = Σ'_n Ŵ(k_n) χ̂(ℓ k_n) e^{i⟪k_n,w⟫}` (`k_n = kmomInt ℓ n = (2π/ℓ)·latVec n`)
equals the periodisation of the windowed convolution `W ⋆ χ_ℓ`:

    `Σ'_m ∫_x W(x)·χ_ℓ(w + ℓ·latVec m − x) dx = Σ'_m (W ⋆ χ_ℓ)(w + ℓ·latVec m)`.

This is the `L¹`-hypothesis version of `Work.BoseBoxFock.pinQBl_eq_periodisation`: there the
weight `W` was assumed a.e. strongly measurable and **bounded** (with compact support), and the
boundedness was used *only* to deduce integrability (`HasCompactSupport.memLp_of_bound`).  Here
integrability is assumed outright and the whole proof goes through unchanged, since the only
analytic inputs are

* `W ∈ L¹` (so its complexification is locally integrable, and the convolution `W ⋆ χ_ℓ` with the
  smooth compactly supported window `χ_ℓ` is `C^∞` with compact support),
* compact support (so `G := W ⋆ χ_ℓ` has compact support and the `L¹` convolution theorem
  `FRK.kinFT_conv_mul` applies),
* evenness (`chat_eq_kinFT_of_even`).

The rest is the lattice Poisson identity `latticePoisson_kernel` applied to `G`, exactly as in the
bounded case.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 4000000

theorem pinQBl_eq_periodisation_L1 {ℓ : ℝ} (hℓ : 0 < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWi : MeasureTheory.Integrable W)
    (hWs : HasCompactSupport W) (hWev : ∀ z, W (-z) = W z)
    (w : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.pinQBl ℓ W w
      = ∑' m : Fin 3 → ℤ, ∫ x : EuclideanSpace ℝ (Fin 3),
          ((W x : ℝ) : ℂ) * ((Submission.BoseGases.chiScale ℓ
            (w + ℓ • Work.BoseBoxFock.latVec m - x) : ℝ) : ℂ) := by
  classical
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  -- the honest weight `W` is `L¹` by hypothesis
  have hWint : MeasureTheory.Integrable W := hWi
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
