/-
# Calculus and summability of the bump transform `bumpFT`

`bumpFT φ x = ∫ θ, φ θ · e(x θ)` is the inverse Fourier transform of the bump `φ`
(`HiFibreDefs`).  This module collects the analytic facts about it that the fibre sums of the
§6 mass bound need:

* `hasDerivAt_bumpFT`, `deriv_bumpFT`: `∂_x (bumpFT φ) x = 2πi · bumpFT (θ ↦ θ φ θ) x` for a
  `C²` compactly supported `φ` (the derivative of the Fourier integral);
* `iteratedDeriv_two_bumpFT`: `∂²_x (bumpFT φ) x = (2πi)² · bumpFT (θ ↦ θ² φ θ) x`;
* `continuous_bumpFT`: `bumpFT φ` is continuous for integrable `φ` (dominated convergence /
  the continuity of the Fourier integral);
* `summable_bumpFT`: the lattice samples `p ↦ ‖bumpFT φ (u − p)‖` are summable, with the
  quadratic decay of `𝓕⁻ φ` and the lattice mass bound `latticeQuadMass`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.HiFibreDefs
import Submission.Work.KMTPlan.A6.bumpFourierMassDeriv

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators FourierTransform
open Work.Analysis.IonescuWainger
open Work.KMTContract
open Work.KMTPlan.A6

/-! ## `bumpFT` is the inverse Fourier transform -/

/-- `bumpFT φ` is the Fourier transform of `φ` at the negated variable. -/
lemma bumpFT_eq_fourier_neg (φ : ℝ → ℂ) : bumpFT φ = fun y : ℝ => 𝓕 φ (-y) := by
  funext y
  rw [show bumpFT φ y = ∫ θ : ℝ, φ θ * ee (y * θ) from rfl,
    Work.KMTPlan.A6.bfm_integral_eq_fourierInv, Real.fourierInv_eq_fourier_neg]

/-- The Fourier transform of an integrable function is continuous. -/
lemma continuous_fourier_of_integrable {h : ℝ → ℂ} (hh : Integrable h) : Continuous (𝓕 h) := by
  have hc : Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) h) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hh
  convert hc using 1

/-- `bumpFT φ` is continuous for integrable `φ`. -/
lemma continuous_bumpFT {φ : ℝ → ℂ} (hφ : Integrable φ) : Continuous (bumpFT φ) := by
  rw [bumpFT_eq_fourier_neg]
  exact (continuous_fourier_of_integrable hφ).comp continuous_neg

/-- The Fourier transform commutes with multiplication by a constant. -/
lemma fourier_const_mul (c : ℂ) (f : ℝ → ℂ) :
    (𝓕 (fun θ : ℝ => c * f θ)) = fun w : ℝ => c * 𝓕 f w := by
  have key : ∀ g : ℝ → ℂ, (fun w : ℝ => 𝓕 g w)
      = VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) g := by
    intro g
    funext w
    rw [Real.fourier_eq]
    simp only [VectorFourier.fourierIntegral]
    congr 1
  funext w
  rw [congrFun (key (fun θ : ℝ => c * f θ)) w, congrFun (key f) w]
  have hsm : (fun θ : ℝ => c * f θ) = c • f := rfl
  rw [hsm, congrFun (VectorFourier.fourierIntegral_const_smul Real.fourierChar volume
    (innerₗ ℝ) f c) w]
  rfl

/-! ## The first and second derivative of `bumpFT` -/

/-- **The derivative of the bump transform.**  For `φ` of class `C²` with compact support,
`∂_x (bumpFT φ) x = 2πi · bumpFT (θ ↦ θ φ θ) x`. -/
theorem hasDerivAt_bumpFT (φ : ℝ → ℂ) (hφ : ContDiff ℝ 2 φ) (hcs : HasCompactSupport φ)
    (x : ℝ) :
    HasDerivAt (bumpFT φ)
      (2 * (Real.pi : ℂ) * Complex.I * bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) x) x := by
  have hint : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hcs
  have hcs' : HasCompactSupport (fun θ : ℝ => (θ : ℂ) * φ θ) :=
    HasCompactSupport.mul_left (f := fun θ : ℝ => (θ : ℂ)) hcs
  have hcont' : Continuous (fun θ : ℝ => (θ : ℂ) * φ θ) :=
    Complex.continuous_ofReal.mul hφ.continuous
  have hint' : Integrable (fun θ : ℝ => (θ : ℂ) * φ θ) :=
    hcont'.integrable_of_hasCompactSupport hcs'
  have hint2 : Integrable (fun θ : ℝ => θ • φ θ) := by
    simpa only [Complex.real_smul] using hint'
  have hbase : HasDerivAt (𝓕 φ)
      (𝓕 (fun θ : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)) • φ θ) (-x)) (-x) :=
    Real.hasDerivAt_fourier hint hint2 (-x)
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1) x := hasDerivAt_neg x
  have h1 : HasDerivAt ((𝓕 φ) ∘ fun y : ℝ => -y)
      ((-1 : ℝ) • (𝓕 (fun θ : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)) • φ θ) (-x))) x :=
    HasDerivAt.scomp x (g₁ := 𝓕 φ) (h := fun y : ℝ => -y) hbase hneg
  have h1' : HasDerivAt (fun y : ℝ => 𝓕 φ (-y))
      ((-1 : ℝ) • (𝓕 (fun θ : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)) • φ θ) (-x))) x := by
    simpa only [Function.comp_def] using h1
  have hval : ((-1 : ℝ)
        • (𝓕 (fun θ : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)) • φ θ) (-x)))
      = 2 * (Real.pi : ℂ) * Complex.I * bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) x := by
    have h3 : (𝓕 (fun θ : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)) • φ θ)) (-x)
        = (-2 * (Real.pi : ℂ) * Complex.I) * (𝓕 (fun θ : ℝ => (θ : ℂ) * φ θ)) (-x) := by
      have hlin : (fun θ : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)) • φ θ)
          = fun θ : ℝ => (-2 * (Real.pi : ℂ) * Complex.I) * ((θ : ℂ) * φ θ) := by
        funext θ; rw [smul_eq_mul]; ring
      rw [hlin, fourier_const_mul]
    rw [h3]
    have h4 : (𝓕 (fun θ : ℝ => (θ : ℂ) * φ θ)) (-x)
        = 𝓕⁻ (fun θ : ℝ => (θ : ℂ) * φ θ) x := (Real.fourierInv_eq_fourier_neg _ x).symm
    rw [h4]
    have h5 : 𝓕⁻ (fun θ : ℝ => (θ : ℂ) * φ θ) x
        = bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) x :=
      (Work.KMTPlan.A6.bfm_integral_eq_fourierInv _ x).symm
    rw [h5, Complex.real_smul]
    push_cast
    ring
  rw [bumpFT_eq_fourier_neg φ, ← hval]
  exact h1'

/-- The derivative of the bump transform, in `deriv` form. -/
theorem deriv_bumpFT (φ : ℝ → ℂ) (hφ : ContDiff ℝ 2 φ) (hcs : HasCompactSupport φ) (x : ℝ) :
    deriv (bumpFT φ) x = 2 * (Real.pi : ℂ) * Complex.I * bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) x :=
  (hasDerivAt_bumpFT φ hφ hcs x).deriv

/-- The derivative of `θ ↦ θ φ θ`, again in the form needed for the second derivative. -/
theorem hasDerivAt_deriv_bumpFT (φ : ℝ → ℂ) (hφ : ContDiff ℝ 2 φ)
    (hcs : HasCompactSupport φ) (x : ℝ) :
    HasDerivAt (deriv (bumpFT φ))
      ((2 * (Real.pi : ℂ) * Complex.I) ^ 2
        * bumpFT (fun θ : ℝ => (θ : ℂ) ^ 2 * φ θ) x) x := by
  have hφ1_cd : ContDiff ℝ 2 (fun θ : ℝ => (θ : ℂ) * φ θ) := bfm_contDiff_mul_id φ hφ
  have hφ1_cs : HasCompactSupport (fun θ : ℝ => (θ : ℂ) * φ θ) :=
    bfm_hasCompactSupport_mul_id φ hcs
  have hfun : deriv (bumpFT φ) = fun y : ℝ => 2 * (Real.pi : ℂ) * Complex.I
      * bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) y :=
    funext fun y => deriv_bumpFT φ hφ hcs y
  rw [hfun]
  have h2 := (hasDerivAt_bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) hφ1_cd hφ1_cs x).const_mul
    (2 * (Real.pi : ℂ) * Complex.I)
  refine h2.congr_deriv ?_
  have hfun2 : (fun θ : ℝ => (θ : ℂ) * ((θ : ℂ) * φ θ)) = fun θ : ℝ => (θ : ℂ) ^ 2 * φ θ := by
    funext θ; ring
  rw [hfun2]
  ring

/-- **The second derivative of the bump transform.** -/
theorem iteratedDeriv_two_bumpFT (φ : ℝ → ℂ) (hφ : ContDiff ℝ 2 φ) (hcs : HasCompactSupport φ)
    (x : ℝ) :
    iteratedDeriv 2 (bumpFT φ) x
      = (2 * (Real.pi : ℂ) * Complex.I) ^ 2
          * bumpFT (fun θ : ℝ => (θ : ℂ) ^ 2 * φ θ) x := by
  rw [show iteratedDeriv 2 (bumpFT φ) x = deriv (deriv (bumpFT φ)) x by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]]
  exact (hasDerivAt_deriv_bumpFT φ hφ hcs x).deriv

/-! ## Summability of the lattice mass -/

/-- The lattice samples of `‖bumpFT φ‖` are summable for `φ` of class `C²` with compact
support, by the quadratic decay of the inverse Fourier transform. -/
lemma summable_bumpFT (φ : ℝ → ℂ) (hφ : ContDiff ℝ 2 φ) (hcs : HasCompactSupport φ) (u : ℝ) :
    Summable (fun p : ℤ => ‖bumpFT φ (u - (p : ℝ))‖) := by
  obtain ⟨C, _hC, hdec⟩ := Work.KMTPlan.A6.bfm_fourierInv_decay φ hφ hcs
  obtain ⟨hsum, _hbound⟩ := Work.KMTPlan.A6.latticeQuadMass 1 (by norm_num) u
  have hb : ∀ p : ℤ, ‖bumpFT φ (u - (p : ℝ))‖ ≤ C * (1 / (1 + |u - (p : ℝ)|) ^ 2) := by
    intro p
    rw [bumpFT, Work.KMTPlan.A6.bfm_integral_eq_fourierInv]
    calc ‖FourierTransformInv.fourierInv φ (u - ↑p)‖ ≤ C / (1 + |u - ↑p|) ^ 2 := hdec _
      _ = C * (1 / (1 + |u - ↑p|) ^ 2) := by ring
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) hb ?_
  simpa only [one_mul] using hsum.mul_left C

/-- The lattice mass of a `θ`-weighted bump is summable, being the lattice mass of the bump
`θ ↦ θ φ θ`. -/
lemma summable_bumpFT_mul_id (φ : ℝ → ℂ) (hφ : ContDiff ℝ 2 φ) (hcs : HasCompactSupport φ)
    (u : ℝ) : Summable (fun p : ℤ => ‖bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) (u - (p : ℝ))‖) :=
  summable_bumpFT _ (bfm_contDiff_mul_id φ hφ) (bfm_hasCompactSupport_mul_id φ hcs) u

/-! ## The product of the two lattice masses -/

/-- The lattice mass over `ℤ × ℤ` of a product of two one-variable masses factorises. -/
theorem tsum_prod_mul {f g : ℤ → ℝ} (hf : Summable f) (hg : Summable g)
    (hf0 : ∀ i, 0 ≤ f i) (hg0 : ∀ i, 0 ≤ g i) :
    (∑' p : ℤ × ℤ, f p.1 * g p.2) = (∑' p : ℤ, f p) * (∑' p : ℤ, g p) := by
  have hprod : Summable fun x : ℤ × ℤ => f x.1 * g x.2 := hf.mul_of_nonneg hg hf0 hg0
  rw [hprod.tsum_prod]
  rw [show (∑' (b : ℤ), ∑' (c : ℤ), f b * g c)
      = ∑' b : ℤ, f b * (∑' c : ℤ, g c) from tsum_congr fun b => tsum_mul_left]
  rw [tsum_mul_right]

end

end Work.KMTAreas.A7
