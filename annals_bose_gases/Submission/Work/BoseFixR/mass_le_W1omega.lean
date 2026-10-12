import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

open MeasureTheory
open scoped ENNReal Topology Real FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Submission.BoseGases

/-- `c * a ≤ c * b` in `ℝ≥0∞` from `a ≤ b`. -/
private lemma mul_le_mul_left_ennreal {a b c : ℝ≥0∞} (h : a ≤ b) : c * a ≤ c * b :=
  mul_le_mul_of_nonneg_left h (zero_le : (0 : ℝ≥0∞) ≤ c)

/-! ## 0. Elementary bookkeeping for the two kernels -/

/-- Pointwise identity `W₁ω = W₁·ω`: the corrected FS `eq:defW_12` kernel
`W₁ω = (g₀ω)/(χ⋆χ)` is the product `W₁·ω = (g₀/(χ⋆χ))·ω` (valid also where
`χ⋆χ = 0`, both sides being `0`). -/
lemma W1omegaFun_eq_mul (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (ℓ : ℝ) :
    W1omegaFun v h ℓ = fun x => W1fun v h ℓ x * Classical.choose h x := by
  funext x
  simp only [W1omegaFun, W1fun, Submission.BoseGases.wScaled]
  ring

/-- The mass `∫W₁ω` equals `∫ W₁·ω`. -/
lemma mass_eq (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (ℓ : ℝ) :
    (∫ x : ℝ³, W1omegaFun v h ℓ x)
      = ∫ x : ℝ³, W1fun v h ℓ x * Classical.choose h x := by
  rw [W1omegaFun_eq_mul]

/-- `W1fun` is `wScaled ℓ (g0 v h)` by definition. -/
lemma W1fun_eq_wScaled (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (ℓ : ℝ) :
    W1fun v h ℓ = wScaled ℓ (g0 v h) := rfl

/-! ## 1. The momentum side: `chat` versus `kinFT` versus the corpus lemma

`chat W q` is *by definition* the real part of `kinFT W q`, and `kinFT` is the
corpus's `(2π)⁻¹`-convention Fourier transform: `kinFT u p = 𝓕u((2π)⁻¹•p)`
(`kinFT_eq_fourier`).  Hence `(chat W q)² ≤ ‖𝓕W((2π)⁻¹•q)‖²`. -/

/-- `(chat W q)² ≤ ‖kinFT W q‖²`. -/
lemma chat_sq_le_kinFT (W : ℝ³ → ℝ) (q : ℝ³) :
    (chat W q) ^ 2 ≤ ‖kinFT (fun y : ℝ³ => ((W y : ℝ) : ℂ)) q‖ ^ 2 := by
  have h1 : |chat W q| ≤ ‖kinFT (fun y : ℝ³ => ((W y : ℝ) : ℂ)) q‖ := by
    simpa [chat] using Complex.abs_re_le_norm (kinFT (fun y : ℝ³ => ((W y : ℝ) : ℂ)) q)
  calc (chat W q) ^ 2 = |chat W q| ^ 2 := (sq_abs (chat W q)).symm
    _ ≤ ‖kinFT (fun y : ℝ³ => ((W y : ℝ) : ℂ)) q‖ ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2

/-- `chat W` is continuous for `W ∈ L¹`: `kinFT` is the Fourier transform of an
`L¹` function, and the Fourier transform of an `L¹` function is continuous. -/
lemma continuous_chat (W : ℝ³ → ℝ) (hW : Integrable W) :
    Continuous (fun q : ℝ³ => chat W q) := by
  have hcont : Continuous (fun p : ℝ³ => 𝓕 (fun y : ℝ³ => ((W y : ℝ) : ℂ)) p) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hW.ofReal
  have heq : (fun q : ℝ³ => chat W q)
      = fun q : ℝ³ => (𝓕 (fun y : ℝ³ => ((W y : ℝ) : ℂ)) ((2 * Real.pi)⁻¹ • q)).re := by
    funext q
    rw [chat, Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
  rw [heq]
  exact Complex.continuous_re.comp
    (hcont.comp (by fun_prop : Continuous fun q : ℝ³ => (2 * Real.pi)⁻¹ • q))

/-- `AEStronglyMeasurable` version of `continuous_chat`. -/
lemma aestronglyMeasurable_chat (W : ℝ³ → ℝ) (hW : Integrable W) :
    AEStronglyMeasurable (fun q : ℝ³ => chat W q) volume :=
  (continuous_chat W hW).aestronglyMeasurable

/-- The pointwise lintegral comparison: `∫⁻ ofReal((chat W q)²/(2‖q‖²))` is at
most `½·∫⁻ ofReal(‖kinFT W q‖²/‖q‖²)`. -/
lemma lintegral_chat_le_kinFT (W : ℝ³ → ℝ) :
    (∫⁻ q : ℝ³, ENNReal.ofReal ((chat W q) ^ 2 / (2 * ‖q‖ ^ 2)))
      ≤ (1 / 2 : ℝ≥0∞)
          * ∫⁻ q : ℝ³,
              ENNReal.ofReal (‖kinFT (fun y : ℝ³ => ((W y : ℝ) : ℂ)) q‖ ^ 2 / ‖q‖ ^ 2) := by
  have hofhalf : ENNReal.ofReal ((1 : ℝ) / 2) = (1 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp
  have hpt : ∀ q : ℝ³, ENNReal.ofReal ((chat W q) ^ 2 / (2 * ‖q‖ ^ 2))
      ≤ (1 / 2 : ℝ≥0∞)
          * ENNReal.ofReal (‖kinFT (fun y : ℝ³ => ((W y : ℝ) : ℂ)) q‖ ^ 2 / ‖q‖ ^ 2) := by
    intro q
    have hdecomp : (chat W q) ^ 2 / (2 * ‖q‖ ^ 2)
        = (1 / 2) * ((chat W q) ^ 2 / ‖q‖ ^ 2) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hdecomp, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), hofhalf]
    refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) (zero_le : (0 : ℝ≥0∞) ≤ 1 / 2)
    exact div_le_div_of_nonneg_right (chat_sq_le_kinFT W q) (by positivity)
  calc (∫⁻ q : ℝ³, ENNReal.ofReal ((chat W q) ^ 2 / (2 * ‖q‖ ^ 2)))
      ≤ ∫⁻ q : ℝ³, (1 / 2 : ℝ≥0∞)
          * ENNReal.ofReal (‖kinFT (fun y : ℝ³ => ((W y : ℝ) : ℂ)) q‖ ^ 2 / ‖q‖ ^ 2) :=
        lintegral_mono hpt
    _ = (1 / 2 : ℝ≥0∞)
          * ∫⁻ q : ℝ³,
              ENNReal.ofReal (‖kinFT (fun y : ℝ³ => ((W y : ℝ) : ℂ)) q‖ ^ 2 / ‖q‖ ^ 2) :=
        lintegral_const_mul' _ _ (by simp)

/-! ## 2. The Fourier side: the corpus's momentum Coulomb inequality for `W₁`

`lintegral_fourier_inv_smul_sq_div_le` needs `0 ≤ f` *pointwise*.  Our `W₁` is
nonnegative only a.e. (it is `g₀/(χ⋆χ)` with `g₀ ≥ 0` a.e.), so we apply it to
`V := max W₁ 0`, which agrees with `W₁` a.e., is pointwise nonnegative, and has
the same Fourier transform. -/

/-- `kinFT` depends only on the a.e. class of its argument. -/
lemma kinFT_congr_ae {f g : ℝ³ → ℂ} (h : f =ᵐ[volume] g) (q : ℝ³) :
    kinFT f q = kinFT g q := by
  rw [kinFT, kinFT]
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

/-- **The momentum Coulomb inequality** for the a.e.-nonnegative `L¹` kernel `W₁`:
`(2π)⁻³∫⁻‖𝓕W₁((2π)⁻¹q)‖²/‖q‖² ≤ (4π)⁻¹∫⁻∫⁻ W₁(x)W₁(y)/‖x−y‖`. -/
lemma fourier_coulomb_le (W : ℝ³ → ℝ) (hW : Integrable W)
    (hWnn : ∀ᵐ x : ℝ³, 0 ≤ W x) :
    ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)
        * (∫⁻ q : ℝ³,
            ENNReal.ofReal (‖kinFT (fun y : ℝ³ => ((W y : ℝ) : ℂ)) q‖ ^ 2 / ‖q‖ ^ 2))
      ≤ ENNReal.ofReal (1 / (4 * Real.pi))
        * (∫⁻ x : ℝ³, ∫⁻ y : ℝ³,
            ENNReal.ofReal (W x * W y / ‖x - y‖)) := by
  set V : ℝ³ → ℝ := fun x => max (W x) 0 with hV
  have hVnn : 0 ≤ V := fun x => le_max_right _ _
  have hVae : V =ᵐ[volume] W := by
    filter_upwards [hWnn] with x hx
    simp only [hV]
    exact max_eq_left hx
  have hVi : Integrable V := hW.congr hVae.symm
  have hfour := Commons.Analysis.Fourier.lintegral_fourier_inv_smul_sq_div_le
    (f := V) hVi hVnn
  have hmom : (∫⁻ q : ℝ³,
        ENNReal.ofReal (‖FourierTransform.fourier (fun x : ℝ³ => ((V x : ℝ) : ℂ))
          ((2 * Real.pi)⁻¹ • q)‖ ^ 2 / ‖q‖ ^ 2))
      = ∫⁻ q : ℝ³, ENNReal.ofReal (‖kinFT (fun y : ℝ³ => ((W y : ℝ) : ℂ)) q‖ ^ 2 / ‖q‖ ^ 2) := by
    apply lintegral_congr_ae
    filter_upwards with q
    have h1 : FourierTransform.fourier (fun x : ℝ³ => ((V x : ℝ) : ℂ)) ((2 * Real.pi)⁻¹ • q)
        = kinFT (fun x : ℝ³ => ((V x : ℝ) : ℂ)) q :=
      (Work.SmallBoxBridge.Resolve.kinFT_eq_fourier _ q).symm
    have h2 : (fun x : ℝ³ => ((V x : ℝ) : ℂ)) =ᵐ[volume] (fun x : ℝ³ => ((W x : ℝ) : ℂ)) := by
      filter_upwards [hVae] with x hx
      rw [hx]
    rw [h1, kinFT_congr_ae h2 q]
  have hpos : (∫⁻ x : ℝ³, ∫⁻ y : ℝ³, ENNReal.ofReal (V x * V y / ‖x - y‖))
      = ∫⁻ x : ℝ³, ∫⁻ y : ℝ³, ENNReal.ofReal (W x * W y / ‖x - y‖) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hVae] with x hx
    refine lintegral_congr_ae ?_
    filter_upwards [hVae] with y hy
    rw [hx, hy]
  rw [hmom, hpos] at hfour
  exact hfour

/-! ## 3. The mass identity (Newton representation)

`ω = (8π)⁻¹ K*g₀` a.e. (`scattering_newton_representation`), the slice
`y ↦ g₀(y)/‖x−y‖` is integrable for a.e. `x` (`coulPot_abs_slice_integrable_ae`),
and `W₁ = wScaled ℓ (g₀)` is `L¹`. -/

/-- The mass identity in lintegral form:
`∫⁻∫⁻ W₁(x)g₀(y)/‖x−y‖ = 8π·∫W₁ω`. -/
theorem lintegral_W1_g0_eq (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) {R ℓ : ℝ}
    (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (hℓ : 0 < ℓ) :
    (∫⁻ x : ℝ³, ∫⁻ y : ℝ³,
        ENNReal.ofReal (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖))
      = ENNReal.ofReal (8 * Real.pi)
        * ENNReal.ofReal (∫ x : ℝ³, wScaled ℓ (g0 v h) x * Classical.choose h x) := by
  have hgnn : ∀ᵐ x : ℝ³, 0 ≤ g0 v h x := g0_nonneg_ae hR hv hvrad hv_supp h
  have hWnn : ∀ᵐ x : ℝ³, 0 ≤ wScaled ℓ (g0 v h) x :=
    wScaled_g0_nonneg_ae (v := v) (R := R) hR hv hvrad hv_supp h
  have hωnn : ∀ᵐ x : ℝ³, 0 ≤ Classical.choose h x :=
    (chosen_w0_bounds_ae (v := v) (R := R) hR hv hvrad hv_supp h).1
  have hωle : ∀ᵐ x : ℝ³, Classical.choose h x ≤ 1 :=
    (chosen_w0_bounds_ae (v := v) (R := R) hR hv hvrad hv_supp h).2
  have hgi : Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hwi : Integrable (wScaled ℓ (g0 v h)) := wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  have hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 :=
    fun z hz => g0_zero_of_norm_ge hv_supp hz h
  -- a.e. integrability of the slice `y ↦ g₀(y)/‖x−y‖`
  have hslice : ∀ᵐ x : ℝ³, Integrable (fun y : ℝ³ => |g0 v h y| * (‖x - y‖ : ℝ)⁻¹) :=
    coulPot_abs_slice_integrable_ae (p := g0 v h) (R := R) hgi hsupp hR
  have hslice' : ∀ᵐ x : ℝ³, Integrable (fun y : ℝ³ => g0 v h y * (‖x - y‖ : ℝ)⁻¹) := by
    filter_upwards [hslice] with x hx
    refine hx.congr ?_
    filter_upwards [hgnn] with y hy
    rw [abs_of_nonneg hy]
  -- the Newton representation of `ω`
  have hnewt := scattering_newton_representation (v := v) (w := Classical.choose h) (R := R)
    hR hvrad hv_supp (Classical.choose_spec h).1 (Classical.choose_spec h).2
  have hnewt' : ∀ᵐ x : ℝ³,
      (∫ y : ℝ³, g0 v h y * (‖x - y‖ : ℝ)⁻¹) = 8 * Real.pi * Classical.choose h x := by
    filter_upwards [hnewt] with x hx
    have hx' : Classical.choose h x
        = (1 / (8 * Real.pi)) * ∫ y : ℝ³, g0 v h y * (‖x - y‖ : ℝ)⁻¹ := by
      simpa [Submission.BoseGases.g0] using hx
    rw [hx']
    field_simp
  -- the inner lintegral, for a.e. `x`
  have hinner : ∀ᵐ x : ℝ³, (∫⁻ y : ℝ³,
        ENNReal.ofReal (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖))
      = ENNReal.ofReal (wScaled ℓ (g0 v h) x)
        * ENNReal.ofReal (8 * Real.pi * Classical.choose h x) := by
    filter_upwards [hWnn, hslice', hnewt'] with x hx hxs hxn
    have h1 : (∫⁻ y : ℝ³,
          ENNReal.ofReal (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖))
        = ∫⁻ y : ℝ³, ENNReal.ofReal (wScaled ℓ (g0 v h) x)
            * ENNReal.ofReal (g0 v h y / ‖x - y‖) := by
      apply lintegral_congr_ae
      filter_upwards with y
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc, ENNReal.ofReal_mul hx]
    have h3 : (∫⁻ y : ℝ³, ENNReal.ofReal (g0 v h y / ‖x - y‖))
        = ENNReal.ofReal (8 * Real.pi * Classical.choose h x) := by
      have h4 : ENNReal.ofReal (∫ y : ℝ³, g0 v h y / ‖x - y‖)
          = ∫⁻ y : ℝ³, ENNReal.ofReal (g0 v h y / ‖x - y‖) :=
        ofReal_integral_eq_lintegral_ofReal hxs (by
          filter_upwards [hgnn] with y hy
          exact div_nonneg hy (norm_nonneg _))
      rw [← h4]
      exact congrArg ENNReal.ofReal (by simpa only [div_eq_mul_inv] using hxn)
    calc (∫⁻ y : ℝ³, ENNReal.ofReal (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖))
        = ∫⁻ y : ℝ³, ENNReal.ofReal (wScaled ℓ (g0 v h) x)
            * ENNReal.ofReal (g0 v h y / ‖x - y‖) := h1
      _ = ENNReal.ofReal (wScaled ℓ (g0 v h) x)
            * ∫⁻ y : ℝ³, ENNReal.ofReal (g0 v h y / ‖x - y‖) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (wScaled ℓ (g0 v h) x)
            * ENNReal.ofReal (8 * Real.pi * Classical.choose h x) := by rw [h3]
  -- integrability and positivity of `x ↦ W₁ x · ω x`
  have hωmeas : AEStronglyMeasurable (Classical.choose h) volume :=
    (Classical.choose_spec h).2.lhs_integrable.aestronglyMeasurable
  have hWωnn : 0 ≤ᵐ[volume] fun x : ℝ³ => wScaled ℓ (g0 v h) x * Classical.choose h x := by
    filter_upwards [hWnn, hωnn] with x hx hw
    exact mul_nonneg hx hw
  have hWωi : Integrable (fun x : ℝ³ => wScaled ℓ (g0 v h) x * Classical.choose h x) := by
    refine Integrable.mono' (hgi.abs.const_mul 2) (hwi.aestronglyMeasurable.mul hωmeas) ?_
    filter_upwards [hgnn, hωnn, hωle] with x hg h0 h1
    have h2 := wScaled_abs_le_two (ℓ := ℓ) (R := R) hℓ hR.le hRℓ hsupp x
    rw [Real.norm_eq_abs, abs_mul]
    calc |wScaled ℓ (g0 v h) x| * |Classical.choose h x|
        ≤ (2 * |g0 v h x|) * 1 := by
          refine mul_le_mul h2 ?_ (abs_nonneg _) (by positivity)
          rwa [abs_of_nonneg h0]
      _ = 2 * |g0 v h x| := by ring
  -- outer assembly
  calc (∫⁻ x : ℝ³, ∫⁻ y : ℝ³,
        ENNReal.ofReal (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖))
      = ∫⁻ x : ℝ³, ENNReal.ofReal (wScaled ℓ (g0 v h) x)
          * ENNReal.ofReal (8 * Real.pi * Classical.choose h x) :=
        lintegral_congr_ae hinner
    _ = ∫⁻ x : ℝ³, ENNReal.ofReal (wScaled ℓ (g0 v h) x)
          * (ENNReal.ofReal (8 * Real.pi) * ENNReal.ofReal (Classical.choose h x)) := by
        apply lintegral_congr_ae
        filter_upwards [hωnn] with x hx
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 8 * Real.pi)]
    _ = ENNReal.ofReal (8 * Real.pi)
          * ∫⁻ x : ℝ³, ENNReal.ofReal (wScaled ℓ (g0 v h) x)
              * ENNReal.ofReal (Classical.choose h x) := by
        rw [← lintegral_const_mul' (ENNReal.ofReal (8 * Real.pi))
          (fun x : ℝ³ => ENNReal.ofReal (wScaled ℓ (g0 v h) x)
            * ENNReal.ofReal (Classical.choose h x)) ENNReal.ofReal_ne_top]
        apply lintegral_congr_ae
        filter_upwards with x
        ring
    _ = ENNReal.ofReal (8 * Real.pi)
          * ∫⁻ x : ℝ³, ENNReal.ofReal (wScaled ℓ (g0 v h) x * Classical.choose h x) := by
        congr 1
        apply lintegral_congr_ae
        filter_upwards [hWnn] with x hx
        rw [ENNReal.ofReal_mul hx]
    _ = ENNReal.ofReal (8 * Real.pi)
          * ENNReal.ofReal (∫ x : ℝ³, wScaled ℓ (g0 v h) x * Classical.choose h x) := by
        congr 1
        exact (ofReal_integral_eq_lintegral_ofReal hWωi hWωnn).symm

/-- The a.e. sandwich `W₁(y) ≤ 2g₀(y)`: hence the `W₁⊗W₁` Coulomb lintegral is
at most twice the `W₁⊗g₀` one.  (Delegated, see
`Submission/Work/BoseFixR/LintegralW1W1Le.lean`.) -/
theorem lintegral_W1W1_le_two_W1g0 (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) {R ℓ : ℝ}
    (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (hℓ : 0 < ℓ) :
    (∫⁻ x : ℝ³, ∫⁻ y : ℝ³,
        ENNReal.ofReal (wScaled ℓ (g0 v h) x * wScaled ℓ (g0 v h) y / ‖x - y‖))
      ≤ 2 * ∫⁻ x : ℝ³, ∫⁻ y : ℝ³,
        ENNReal.ofReal (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖) := by
  have hgnn : ∀ᵐ x : ℝ³, 0 ≤ g0 v h x := g0_nonneg_ae hR hv hvrad hv_supp h
  have hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 :=
    fun z hz => g0_zero_of_norm_ge hv_supp hz h
  -- the a.e. sandwich `W₁ ≤ 2g₀`
  have hWy : ∀ᵐ y : ℝ³, wScaled ℓ (g0 v h) y ≤ 2 * g0 v h y := by
    filter_upwards [hgnn] with y hy
    have h2 := wScaled_abs_le_two (ℓ := ℓ) (R := R) hℓ hR.le hRℓ hsupp y
    rw [abs_of_nonneg hy] at h2
    linarith [le_abs_self (wScaled ℓ (g0 v h) y)]
  -- the inner comparison, for every `x` with `0 ≤ W₁ x`
  have hinner : ∀ x : ℝ³, 0 ≤ wScaled ℓ (g0 v h) x →
      (∫⁻ y : ℝ³,
          ENNReal.ofReal (wScaled ℓ (g0 v h) x * wScaled ℓ (g0 v h) y / ‖x - y‖))
        ≤ 2 * (∫⁻ y : ℝ³, ENNReal.ofReal
            (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖)) := by
    intro x hx
    calc (∫⁻ y : ℝ³,
            ENNReal.ofReal (wScaled ℓ (g0 v h) x * wScaled ℓ (g0 v h) y / ‖x - y‖))
        ≤ ∫⁻ y : ℝ³, 2 * ENNReal.ofReal
            (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hWy] with y hy
          have h1 : wScaled ℓ (g0 v h) x * wScaled ℓ (g0 v h) y
              ≤ wScaled ℓ (g0 v h) x * (2 * g0 v h y) :=
            mul_le_mul_of_nonneg_left hy hx
          have h2 : wScaled ℓ (g0 v h) x * wScaled ℓ (g0 v h) y / ‖x - y‖
              ≤ 2 * (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖) := by
            have h3 := div_le_div_of_nonneg_right h1 (norm_nonneg (x - y))
            calc wScaled ℓ (g0 v h) x * wScaled ℓ (g0 v h) y / ‖x - y‖
                ≤ wScaled ℓ (g0 v h) x * (2 * g0 v h y) / ‖x - y‖ := h3
              _ = 2 * (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖) := by ring
          calc ENNReal.ofReal (wScaled ℓ (g0 v h) x * wScaled ℓ (g0 v h) y / ‖x - y‖)
              ≤ ENNReal.ofReal
                  (2 * (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖)) :=
                ENNReal.ofReal_le_ofReal h2
            _ = 2 * ENNReal.ofReal
                  (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖) := by
                rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
                norm_num
      _ = 2 * (∫⁻ y : ℝ³, ENNReal.ofReal
            (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖)) :=
          lintegral_const_mul' _ _ (by simp)
  calc (∫⁻ x : ℝ³, ∫⁻ y : ℝ³,
        ENNReal.ofReal (wScaled ℓ (g0 v h) x * wScaled ℓ (g0 v h) y / ‖x - y‖))
      ≤ ∫⁻ x : ℝ³, 2 * (∫⁻ y : ℝ³, ENNReal.ofReal
          (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖)) :=
        lintegral_mono_ae ((wScaled_g0_nonneg_ae (v := v) (R := R) hR hv hvrad hv_supp h).mono
          (fun x hx => hinner x hx))
    _ = 2 * ∫⁻ x : ℝ³, ∫⁻ y : ℝ³,
        ENNReal.ofReal (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖) :=
        lintegral_const_mul' _ _ (by simp)

/-! ## 4. The main theorem -/

-- NOTE (requester): FS `eq:I2-integral` (the "mass identity"), in the direction needed by FS §9's
-- `eq:Rough2`: the kinetic integral `(2π)⁻³∫Ŵ₁(k)²/(2‖k‖²)dk` is bounded by a universal constant
-- times the *mass* `∫W₁ω = ∫ W1omegaFun = chat (W1omegaFun …) 0 = E.W1omega0` of the pinned kernel
-- `W₁ = W1fun v h ℓ = wScaled ℓ (g₀)`, `ω = w₀ = Classical.choose h`, `g₀ = v(1-ω)`.
-- The sign hypotheses `0 ≤ v`, `IsRadial v` are ESSENTIAL (and are carried by the corpus's
-- consumer `Submission.Work.BoseFixR.RB5FSHonestFix` and by FS Theorem 1.2): they give
-- `0 ≤ ω ≤ 1` a.e. (`Submission.Work.QMassUpper.chosen_w0_bounds_ae`), hence `g₀ ≥ 0` a.e. and
-- `W₁ ≥ 0` on `ball 0 R` (`Submission.BoseGases.g0_nonneg_ae`,
-- `Submission.BoseGases.convScale_ge_half_ball`), which is what makes the comparison
-- `∬W₁W₁/‖x−y‖ ≤ 2∬W₁g₀/‖x−y‖` true (pointwise `W₁ ≤ 2g₀` on the support with both sides ≥ 0).
-- Route: (i) `Submission.BoseGases.scattering_newton_representation` (module `Submission.NewtonRep`)
-- gives `ω x = (8π)⁻¹∫ g₀(y)/‖x-y‖ dy` a.e., hence `∫W₁ω = (8π)⁻¹∬ W₁(x)g₀(y)/‖x-y‖`;
-- (ii) the symmetric statement `(2π)⁻³∫Ŵ₁(k)²/(2k²)dk = (8π)⁻¹∬ W₁(x)W₁(y)/‖x-y‖dxdy` is the
-- classical Fourier transform of the Newton kernel; prove it via the heat kernel
-- `(4πt)^{-3/2}e^{-‖z‖²/(4t)} ↦ e^{-tk²}` with Fubini and `∫₀^∞t^{-3/2}e^{-a/t}dt = √(π/a)`;
-- (iii) conclude with `1/2 ≤ (χ⋆χ)(·/ℓ) ≤ 1` on `ball 0 R` (`convScale_ge_half_ball`,
-- `conv3chi_le_one`), `g₀ ≤ W₁ ≤ 2g₀` there, and `(chat f)² ≤ |f̂|²`; the constant `100` is a free
-- absolute constant (the natural one is `2`).
theorem mass_le_W1omega (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R ℓ : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (hℓ : 0 < ℓ)
    (hW : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ)) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2)
      ≤ 100 * ∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1omegaFun v h ℓ x := by
  change ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : ℝ³, (chat (wScaled ℓ (g0 v h)) q) ^ 2 / (2 * ‖q‖ ^ 2))
      ≤ 100 * (∫ x : ℝ³, W1omegaFun v h ℓ x)
  -- the a.e. positivity facts
  have hWnn : ∀ᵐ x : ℝ³, 0 ≤ wScaled ℓ (g0 v h) x :=
    wScaled_g0_nonneg_ae (v := v) (R := R) hR hv hvrad hv_supp h
  have hw0nn : ∀ᵐ x : ℝ³, 0 ≤ Classical.choose h x :=
    (chosen_w0_bounds_ae (v := v) (R := R) hR hv hvrad hv_supp h).1
  have hWi : Integrable (wScaled ℓ (g0 v h)) := hW
  -- the mass is nonnegative
  have hMnn : 0 ≤ ∫ x : ℝ³, wScaled ℓ (g0 v h) x * Classical.choose h x := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hWnn, hw0nn] with x hx hw
    exact mul_nonneg hx hw
  -- the three external inputs
  have hfour := fourier_coulomb_le (wScaled ℓ (g0 v h)) hWi hWnn
  have hPA := lintegral_W1W1_le_two_W1g0 (v := v) h (R := R) (ℓ := ℓ) hR hv hvrad hv_supp hRℓ hℓ
  have hPB := lintegral_W1_g0_eq (v := v) h (R := R) (ℓ := ℓ) hR hv hvrad hv_supp hRℓ hℓ
  -- the ENNReal chain
  have hhalf2 : (1 / 2 : ℝ≥0∞) * 2 = 1 := by
    have h := ENNReal.inv_mul_cancel (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
    simpa using h
  have hMnn' : 0 ≤ ∫ x : ℝ³, W1omegaFun v h ℓ x := by
    rw [mass_eq v h ℓ]
    exact hMnn
  have hpi8 : (1 / (4 * Real.pi)) * (8 * Real.pi) = 2 := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    norm_num
  have key : ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)
        * (∫⁻ q : ℝ³, ENNReal.ofReal ((chat (wScaled ℓ (g0 v h)) q) ^ 2 / (2 * ‖q‖ ^ 2)))
      ≤ ENNReal.ofReal (100 * ∫ x : ℝ³, W1omegaFun v h ℓ x) := by
    have hstep1 := lintegral_chat_le_kinFT (wScaled ℓ (g0 v h))
    calc ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)
          * (∫⁻ q : ℝ³, ENNReal.ofReal ((chat (wScaled ℓ (g0 v h)) q) ^ 2 / (2 * ‖q‖ ^ 2)))
        ≤ ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)
            * ((1 / 2 : ℝ≥0∞) * (∫⁻ q : ℝ³, ENNReal.ofReal
                (‖kinFT (fun y : ℝ³ => ((wScaled ℓ (g0 v h) y : ℝ) : ℂ)) q‖ ^ 2
                  / ‖q‖ ^ 2))) :=
          mul_le_mul_left_ennreal hstep1
        _ = (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)
            * (∫⁻ q : ℝ³, ENNReal.ofReal
                (‖kinFT (fun y : ℝ³ => ((wScaled ℓ (g0 v h) y : ℝ) : ℂ)) q‖ ^ 2
                  / ‖q‖ ^ 2))) := by ring
        _ ≤ (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (1 / (4 * Real.pi))
            * (∫⁻ x : ℝ³, ∫⁻ y : ℝ³, ENNReal.ofReal
                (wScaled ℓ (g0 v h) x * wScaled ℓ (g0 v h) y / ‖x - y‖))) :=
          mul_le_mul_left_ennreal hfour
        _ ≤ (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (1 / (4 * Real.pi))
            * (2 * (∫⁻ x : ℝ³, ∫⁻ y : ℝ³, ENNReal.ofReal
                (wScaled ℓ (g0 v h) x * g0 v h y / ‖x - y‖)))) :=
          mul_le_mul_left_ennreal (mul_le_mul_left_ennreal hPA)
        _ = (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (1 / (4 * Real.pi))
            * (2 * (ENNReal.ofReal (8 * Real.pi)
                * ENNReal.ofReal (∫ x : ℝ³,
                    wScaled ℓ (g0 v h) x * Classical.choose h x)))) := by
          rw [hPB]
        _ = ENNReal.ofReal (1 / (4 * Real.pi)) * ENNReal.ofReal (8 * Real.pi)
            * ENNReal.ofReal (∫ x : ℝ³,
                wScaled ℓ (g0 v h) x * Classical.choose h x) := by
          rw [show (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (1 / (4 * Real.pi))
              * (2 * (ENNReal.ofReal (8 * Real.pi)
                * ENNReal.ofReal (∫ x : ℝ³,
                    wScaled ℓ (g0 v h) x * Classical.choose h x))))
            = ((1 / 2 : ℝ≥0∞) * 2) * (ENNReal.ofReal (1 / (4 * Real.pi))
              * (ENNReal.ofReal (8 * Real.pi)
                * ENNReal.ofReal (∫ x : ℝ³,
                    wScaled ℓ (g0 v h) x * Classical.choose h x))) from by ring,
            hhalf2, one_mul, mul_assoc]
        _ = ENNReal.ofReal ((1 / (4 * Real.pi)) * (8 * Real.pi))
            * ENNReal.ofReal (∫ x : ℝ³,
                wScaled ℓ (g0 v h) x * Classical.choose h x) := by
          rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (4 * Real.pi))]
        _ = ENNReal.ofReal 2 * ENNReal.ofReal (∫ x : ℝ³,
                wScaled ℓ (g0 v h) x * Classical.choose h x) := by rw [hpi8]
        _ = ENNReal.ofReal (2 * ∫ x : ℝ³,
                wScaled ℓ (g0 v h) x * Classical.choose h x) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        _ ≤ ENNReal.ofReal (100 * ∫ x : ℝ³,
                wScaled ℓ (g0 v h) x * Classical.choose h x) :=
          ENNReal.ofReal_le_ofReal (by linarith [hMnn])
        _ = ENNReal.ofReal (100 * ∫ x : ℝ³, W1omegaFun v h ℓ x) := by
          congr 1
          congr 1
          exact (mass_eq v h ℓ).symm
  -- take `.toReal` on both sides
  have hI : (∫ q : ℝ³, (chat (wScaled ℓ (g0 v h)) q) ^ 2 / (2 * ‖q‖ ^ 2))
      = (∫⁻ q : ℝ³,
          ENNReal.ofReal ((chat (wScaled ℓ (g0 v h)) q) ^ 2 / (2 * ‖q‖ ^ 2))).toReal := by
    refine integral_eq_lintegral_of_nonneg_ae ?_ ?_
    · filter_upwards with q
      exact div_nonneg (sq_nonneg _) (by positivity)
    · have h1 : AEMeasurable (fun q : ℝ³ => (chat (wScaled ℓ (g0 v h)) q) ^ 2) volume :=
        (AEStronglyMeasurable.pow (aestronglyMeasurable_chat (wScaled ℓ (g0 v h)) hWi) 2).aemeasurable
      have h2 : AEMeasurable (fun q : ℝ³ => 2 * ‖q‖ ^ 2) volume :=
        (continuous_const.mul (continuous_norm.pow 2)).aemeasurable
      exact (h1.div h2).aestronglyMeasurable
  calc ((2 * Real.pi) ^ 3)⁻¹
        * (∫ q : ℝ³, (chat (wScaled ℓ (g0 v h)) q) ^ 2 / (2 * ‖q‖ ^ 2))
      = (ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹)
          * (∫⁻ q : ℝ³,
              ENNReal.ofReal ((chat (wScaled ℓ (g0 v h)) q) ^ 2 / (2 * ‖q‖ ^ 2)))).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hI]
    _ ≤ (ENNReal.ofReal (100 * ∫ x : ℝ³, W1omegaFun v h ℓ x)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top key
    _ = 100 * ∫ x : ℝ³, W1omegaFun v h ℓ x :=
        ENNReal.toReal_ofReal (by linarith [hMnn'])

end Work.BoseFixR
