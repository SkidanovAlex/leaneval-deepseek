import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Honest.HonSliceFinite
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonEnergyTruncIneq2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Junk-friendly comparison lemmas for the integrals over `Iz`

The Bochner integral of a non-integrable function is `0` (`MeasureTheory.integral_undef`), so a
pointwise comparison `f ≤ g` does **not** imply `∫f ≤ ∫g` unless one knows that the dominating
function `g` is integrable.  The two lemmas below exploit exactly that: the hypotheses are
`g` integrable, `g ≥ 0` (a.e.) and `f ≤ g` (a.e.); the conclusion holds both when `f` is
integrable (monotonicity of the integral) and when it is not (then `∫f = 0` and the claim reduces
to the nonnegativity of `∫g`). -/

theorem setIntegral_le_of_ae_le_of_nonneg {f g : ℝ → ℝ}
    (hle : f ≤ᵐ[volume.restrict Work.Spaces.Iz] g)
    (hg0 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iz] g)
    (hg : IntegrableOn g Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz, f z) ≤ ∫ z in Work.Spaces.Iz, g z := by
  by_cases hf : Integrable f (volume.restrict Work.Spaces.Iz)
  · exact integral_mono_ae hf hg hle
  · rw [integral_undef hf]
    exact integral_nonneg_of_ae hg0

theorem neg_setIntegral_le_of_ae_le {f G : ℝ → ℝ}
    (hle : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), -G z ≤ f z)
    (hG0 : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), 0 ≤ G z)
    (hG : IntegrableOn G Work.Spaces.Iz) :
    -(∫ z in Work.Spaces.Iz, f z) ≤ ∫ z in Work.Spaces.Iz, G z := by
  by_cases hf : Integrable f (volume.restrict Work.Spaces.Iz)
  · have h2 := integral_mono_ae hf.neg hG (hle.mono fun z hz => by
      simp only [Pi.neg_apply]; linarith)
    have h3 : (∫ x in Work.Spaces.Iz, (-f) x) = -(∫ x in Work.Spaces.Iz, f x) := by
      simp only [Pi.neg_apply]
      rw [integral_neg]
    rw [h3] at h2
    exact h2
  · rw [integral_undef hf]
    have h0 := integral_nonneg_of_ae hG0
    linarith

/-- The set `{0}` is null inside `Iz`, so a.e. statements on `Iz` may always assume `z > 0`. -/
theorem ae_pos_of_mem_Iz : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici]
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (t := ({0} : Set ℝ)) ?_ (measure_singleton 0)
  intro z hz
  simp only [Set.mem_setOf_eq, not_imp, Set.mem_Ici, Set.mem_singleton_iff] at hz
  exact le_antisymm (le_of_not_gt hz.2) hz.1

/-- The a.e. form (for the ambient measure) of `ae_pos_of_mem_Iz`, suited to
`MeasureTheory.setIntegral_congr_ae`. -/
theorem ae_pos_of_mem_Iz_vol : ∀ᵐ z ∂(volume : Measure ℝ), z ∈ Work.Spaces.Iz → 0 < z := by
  refine (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Work.Spaces.Iz)
    (p := fun z => 0 < z) measurableSet_Ici).mp ?_
  exact ae_pos_of_mem_Iz

/-- The a.e. form (for the ambient measure) of `ae_mem_Ioo_Iθ'`, suited to
`MeasureTheory.setIntegral_congr_ae`. -/
theorem ae_mem_Ioo_of_mem_Iθ_vol :
    ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Work.Spaces.Iθ → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  refine (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Work.Spaces.Iθ)
    (p := fun θ => θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) measurableSet_Icc).mp ?_
  exact ae_mem_Ioo_Iθ'

/-! ## Elementary bounds for the radial weights -/

/-- `|(z w²)'| ≤ 3 w²` for `z > 0`. -/
theorem deriv_zwSq_abs_le (z : ℝ) (hz : 0 < z) :
    |deriv (fun x : ℝ => x * (Work.Spaces.w x) ^ 2) z| ≤ 3 * (Work.Spaces.w z) ^ 2 := by
  obtain ⟨-, -, -, h4, -⟩ := Work.FTS.EllipticEst.weight_algebra_fts
  rw [h4 z (ne_of_gt hz)]
  have hw : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
    rw [Work.Spaces.w, div_pow]; ring
  rw [hw]
  have hz4 : (0:ℝ) < z^4 := by positivity
  have h1z : (0:ℝ) < (1+z)^3 := by positivity
  rw [abs_div, abs_of_pos hz4, abs_mul, abs_of_pos h1z]
  rw [div_le_iff₀ hz4]
  have h : |z - 3| ≤ 3 * (1 + z) := by
    rw [abs_le]; constructor <;> nlinarith
  calc |z - 3| * (1 + z) ^ 3 ≤ (3 * (1 + z)) * (1 + z) ^ 3 :=
        mul_le_mul_of_nonneg_right h (le_of_lt h1z)
    _ = 3 * ((1 + z) ^ 4 / z ^ 4) * z ^ 4 := by field_simp

/-- `|(z² w²)'| ≤ 2 z w²` for `z > 0`. -/
theorem deriv_zsqwSq_abs_le (z : ℝ) (hz : 0 < z) :
    |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z| ≤ 2 * z * (Work.Spaces.w z) ^ 2 := by
  obtain ⟨-, -, h3, -, -⟩ := Work.FTS.EllipticEst.weight_algebra_fts
  rw [h3 z (ne_of_gt hz)]
  have hw : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
    rw [Work.Spaces.w, div_pow]; ring
  rw [hw]
  have hz3 : (0:ℝ) < z^3 := by positivity
  have h1z : (0:ℝ) < (1+z)^3 := by positivity
  rw [abs_div, abs_of_pos hz3, abs_mul, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos h1z]
  rw [div_le_iff₀ hz3]
  have h : |z - 1| ≤ 1 + z := by
    rw [abs_le]; constructor <;> linarith
  calc 2 * |z - 1| * (1 + z) ^ 3 ≤ 2 * (1 + z) * (1 + z) ^ 3 := by
        nlinarith [h, h1z]
    _ = 2 * z * ((1 + z) ^ 4 / z ^ 4) * z ^ 3 := by field_simp

/-- `(w)²` is `C^∞` near every `z > 0`. -/
theorem contDiffAt_w_sq {z : ℝ} (hz : 0 < z) (n : ℕ) :
    ContDiffAt ℝ n (fun x : ℝ => (Work.Spaces.w x) ^ 2) z := by
  have hw : ContDiffAt ℝ n (fun x : ℝ => (1 + x) ^ 2 / x ^ 2) z :=
    ((contDiffAt_const.add contDiffAt_id).pow 2).div (contDiffAt_id.pow 2)
      (by positivity)
  simpa only [Work.Spaces.w] using hw.pow 2

/-- `iteratedDeriv 2 f = deriv (deriv f)`. -/
theorem iteratedDeriv_two_eq (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [iteratedDeriv_eq_iterate]
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply]
  rfl

/-! ## The two product rules for the truncated radial weights -/

/-- First-order product rule for `φ · w² · z`. -/
theorem TruncCutDerivOne (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ) (z : ℝ) (hz : 0 < z) :
    deriv (fun x : ℝ => φ x * (Work.Spaces.w x) ^ 2 * x) z
      = deriv φ z * (z * (Work.Spaces.w z) ^ 2)
        + φ z * deriv (fun x : ℝ => x * (Work.Spaces.w x) ^ 2) z := by
  have hφd : DifferentiableAt ℝ φ z := (hφ.contDiffAt).differentiableAt (by norm_num)
  have hWd : DifferentiableAt ℝ (fun x : ℝ => x * (Work.Spaces.w x) ^ 2) z :=
    (contDiffAt_id.mul (contDiffAt_w_sq hz 1)).differentiableAt (by norm_num)
  have hfun : (fun x : ℝ => φ x * (Work.Spaces.w x) ^ 2 * x)
      = fun x : ℝ => φ x * (x * (Work.Spaces.w x) ^ 2) := by funext x; ring
  rw [hfun, deriv_fun_mul hφd hWd]

/-- Second-order product rule for `φ · w² · z²`. -/
theorem TruncCutDerivTwo (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ) (z : ℝ) (hz : 0 < z) :
    deriv (deriv (fun x : ℝ => φ x * (Work.Spaces.w x) ^ 2 * x ^ 2)) z
      = deriv (deriv φ) z * (z ^ 2 * (Work.Spaces.w z) ^ 2)
        + 2 * deriv φ z * deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z
        + φ z * deriv (deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2)) z := by
  have hφ2 : ContDiffAt ℝ 2 φ z := hφ.contDiffAt
  have hW2 : ContDiffAt ℝ 2 (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z :=
    (contDiffAt_id.pow 2).mul (contDiffAt_w_sq hz 2)
  have hfun : (fun x : ℝ => φ x * (Work.Spaces.w x) ^ 2 * x ^ 2)
      = fun x : ℝ => φ x * (x ^ 2 * (Work.Spaces.w x) ^ 2) := by funext x; ring
  rw [hfun]
  have hleib := iteratedDeriv_fun_mul (n := 2) (x := z) hφ2 hW2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add] at hleib
  have hLHS : deriv (deriv (fun x : ℝ => φ x * (x ^ 2 * (Work.Spaces.w x) ^ 2))) z
      = iteratedDeriv 2 (fun x : ℝ => φ x * (x ^ 2 * (Work.Spaces.w x) ^ 2)) z := by
    rw [iteratedDeriv_two_eq]
  rw [hLHS, hleib]
  simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self, Nat.cast_one,
    Nat.cast_ofNat, one_mul, iteratedDeriv_zero, iteratedDeriv_one, Nat.sub_zero, Nat.sub_self,
    Nat.reduceSub, iteratedDeriv_two_eq]
  ring

/-! ## The two cutoff-derivative bounds of the truncation error -/


/-! ## Slicewise honesty of the source `F` and the angular AM–GM

These are the ingredients that turn the pointwise (in `θ`) AM–GM `F·Ψ ≤ (F²+Ψ²)/2` into a
comparison of the iterated integrals. -/

variable {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}

/-- The `θ`-slice of `∂_θθΨ` is a.e. strongly measurable. -/
theorem aesm_pthIter2_slice (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => Work.Spaces.pthIter 2 Ψ z θ)
      (volume.restrict Work.Spaces.Iθ) := by
  rw [restrict_Iθ_eq_Ioo]
  exact (continuousOn_pthIter2' h hz).aestronglyMeasurable measurableSet_Ioo

/-- The `θ`-slice of `bslOp α Ψ` is a.e. strongly measurable, for `z > 0`. -/
theorem aesm_bslOp_slice (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => Work.Elliptic.bslOp α Ψ z θ)
      (volume.restrict Work.Spaces.Iθ) := by
  have hS := smoothOpen_of_forall h.sm
  have h1 : AEStronglyMeasurable (fun θ => Work.Spaces.pzIter 2 Ψ z θ)
      (volume.restrict Work.Spaces.Iθ) := SmoothOpen.aesm_slice_pzIter hS 2 hz
  have h2 : AEStronglyMeasurable (fun θ => Work.Spaces.pz Ψ z θ)
      (volume.restrict Work.Spaces.Iθ) := SmoothOpen.aesm_slice_pzIter hS 1 hz
  have h3 : AEStronglyMeasurable (fun θ => Ψ z θ) (volume.restrict Work.Spaces.Iθ) :=
    SmoothOpen.aesm_slice_pzIter hS 0 hz
  have h4 := aesm_pthIter2_slice h hz
  have h5 := aesm_pth_tan_mul h hz
  have hgoal : (fun θ => Work.Elliptic.bslOp α Ψ z θ)
      = fun θ => (-(α ^ 2 * z ^ 2)) * Work.Spaces.pzIter 2 Ψ z θ
          - (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ
          + (-(Work.Spaces.pthIter 2 Ψ z θ)
            + Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - 6 * Ψ z θ) := by
    funext θ
    rw [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero]
  rw [hgoal]
  exact (((h1.const_mul _).sub (h2.const_mul _)).add
    (((h4.neg).add h5).sub (h3.const_mul 6)))

/-- The `θ`-slice of the source `F` is a.e. strongly measurable, for `z > 0`. -/
theorem aesm_F_slice (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => F z θ) (volume.restrict Work.Spaces.Iθ) := by
  refine (aesm_bslOp_slice h hz).congr ?_
  filter_upwards [ae_mem_Ioo_Iθ'] with θ hθ
  exact h.eq z hz θ hθ.1 hθ.2

/-- `(F z ·)²` is integrable on the angular interval, for `z > 0` (honesty of the source). -/
theorem hon_F_slice_sq_integrable (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (F z θ) ^ 2) Work.Spaces.Iθ :=
  integrableOn_sq_of_sigma (aesm_F_slice h hz) (hon_memF_sigma h hz)

/-- `F z · · Ψ z ·` is integrable on the angular interval, for `z > 0`. -/
theorem hon_F_mul_psi_slice_integrable (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => F z θ * Ψ z θ) Work.Spaces.Iθ := by
  have hF2 := hon_F_slice_sq_integrable h hz
  have hP2 := integrableOn_sq_psi' h hz
  have hmaj : IntegrableOn (fun θ => (1/2) * ((F z θ)^2 + (Ψ z θ)^2)) Work.Spaces.Iθ :=
    (hF2.add hP2).const_mul (1/2)
  refine hmaj.mono' ((aesm_F_slice h hz).mul (aesm_psi_slice h hz)) ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs, abs_mul]
  have hsq := sq_nonneg (|F z θ| - |Ψ z θ|)
  have h1 : (F z θ)^2 = |F z θ|^2 := (sq_abs _).symm
  have h2 : (Ψ z θ)^2 = |Ψ z θ|^2 := (sq_abs _).symm
  rw [h1, h2]
  nlinarith [hsq, abs_nonneg (F z θ), abs_nonneg (Ψ z θ)]

/-- **The slicewise AM–GM**: for `z > 0`, `∫_θ FΨ ≤ (1/2)∫_θ F² + (1/2)∫_θ Ψ²`. -/
theorem hon_slice_amgm (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, F z θ * Ψ z θ)
      ≤ (1/2) * (∫ θ in Work.Spaces.Iθ, (F z θ)^2)
        + (1/2) * (∫ θ in Work.Spaces.Iθ, (Ψ z θ)^2) := by
  have hFP := hon_F_mul_psi_slice_integrable h hz
  have hF2 := hon_F_slice_sq_integrable h hz
  have hP2 := integrableOn_sq_psi' h hz
  have hmaj : IntegrableOn (fun θ => (1/2) * ((F z θ)^2 + (Ψ z θ)^2)) Work.Spaces.Iθ :=
    (hF2.add hP2).const_mul (1/2)
  have hle : (∫ θ in Work.Spaces.Iθ, F z θ * Ψ z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, (1/2) * ((F z θ)^2 + (Ψ z θ)^2) :=
    integral_mono_ae hFP hmaj (Filter.Eventually.of_forall fun θ => by
      have hsq := sq_nonneg (F z θ - Ψ z θ)
      nlinarith [hsq])
  rw [integral_const_mul, integral_add hF2 hP2] at hle
  linarith

/-- **Strong measurability of the slice mass `z ↦ ∫_θ Ψ(z,θ)²`.** -/
theorem aesm_P2 (h : Hon α F Ψ) :
    AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (Ψ p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)) :=
    ((h.sm 0).continuousOn).pow 2
  have h2 := (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
  simpa using h2

/-- The weight `(w)²` is measurable. -/
theorem measurable_wSq : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
  have : (fun z : ℝ => (Work.Spaces.w z) ^ 2) = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
    funext z; simp only [Work.Spaces.w]
  rw [this]
  exact (((measurable_const.add measurable_id).pow_const 2).div
    (measurable_id.pow_const 2)).pow_const 2

/-- **`φ w² · P2` is integrable** as soon as `w² · P2` is, for `0 ≤ φ ≤ 1`. -/
theorem integrableOn_phi_wSq_P2 {φ : ℝ → ℝ} (hφ0 : ∀ z : ℝ, 0 ≤ φ z)
    (hφ1 : ∀ z : ℝ, φ z ≤ 1) (hφc : Continuous φ) (h : Hon α F Ψ)
    (hP : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz) :
    IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz := by
  have hP2nn : ∀ z : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 :=
    fun z => integral_nonneg fun θ => sq_nonneg _
  have haesm : AEStronglyMeasurable (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) (volume.restrict Work.Spaces.Iz) :=
    ((hφc.measurable.aestronglyMeasurable).mul measurable_wSq.aestronglyMeasurable).mul (aesm_P2 h)
  refine hP.mono' haesm ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (mul_nonneg (hφ0 z) (sq_nonneg _)) (hP2nn z))]
  calc φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
      ≤ 1 * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hφ1 z) (sq_nonneg _)) (hP2nn z)
    _ = (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) := by ring

/-! ## The two truncation-error integrals are honest -/

/-- The second truncation-error integral (the `φ'`-term against `z w²`) is integrable. -/
theorem integrableOn_truncErr_E2 (h : Hon α F Ψ) (φ : ℝ → ℝ)
    (hC1 : ∃ C : ℝ, ∀ z : ℝ, |deriv φ z| * z ≤ C)
    (hP : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz) :
    IntegrableOn (fun z => |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz := by
  obtain ⟨C, hC⟩ := hC1
  have hP2nn : ∀ z : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 :=
    fun z => integral_nonneg fun θ => sq_nonneg _
  have haesm : AEStronglyMeasurable (fun z => |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) (volume.restrict Work.Spaces.Iz) :=
    (((measurable_deriv φ).abs.aestronglyMeasurable).mul
      ((measurable_id.mul measurable_wSq).aestronglyMeasurable)).mul (aesm_P2 h)
  refine (hP.const_mul (max C 0)).mono' haesm ?_
  filter_upwards [ae_pos_of_mem_Iz] with z hz
  have hCz : |deriv φ z| * z ≤ C := hC z
  have hCmax : |deriv φ z| * z ≤ max C 0 := le_trans hCz (le_max_left _ _)
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hW1 : 0 ≤ z * (Work.Spaces.w z) ^ 2 := mul_nonneg (le_of_lt hz) hw2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc |deriv φ z| * (z * (Work.Spaces.w z) ^ 2) * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
      = (|deriv φ z| * z) * ((Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) := by ring
    _ ≤ max C 0 * ((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) :=
        mul_le_mul_of_nonneg_right hCmax (mul_nonneg hw2 (hP2nn z))

/-- The first truncation-error integral (the `φ'`- and `φ''`-terms against `z² w²` and `w²`) is
integrable. -/
theorem integrableOn_truncErr_E1 (h : Hon α F Ψ) (φ : ℝ → ℝ)
    (hC1 : ∃ C : ℝ, ∀ z : ℝ, |deriv φ z| * z ≤ C)
    (hC2 : ∃ C : ℝ, ∀ z : ℝ, |deriv (deriv φ) z| * z ^ 2 ≤ C)
    (hP : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz) :
    IntegrableOn (fun z => (2 * |deriv φ z|
        * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
        + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz := by
  obtain ⟨C₁, hC₁⟩ := hC1
  obtain ⟨C₂, hC₂⟩ := hC2
  have hP2nn : ∀ z : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 :=
    fun z => integral_nonneg fun θ => sq_nonneg _
  have haesm : AEStronglyMeasurable (fun z => (2 * |deriv φ z|
        * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
        + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) (volume.restrict Work.Spaces.Iz) := by
    have hA : AEStronglyMeasurable (fun z => 2 * |deriv φ z|
        * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|)
        (volume.restrict Work.Spaces.Iz) :=
      (((measurable_deriv φ).abs.const_mul 2).aestronglyMeasurable).mul
        ((measurable_deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2)).abs.aestronglyMeasurable)
    have hB : AEStronglyMeasurable (fun z => |deriv (deriv φ) z|
        * (z ^ 2 * (Work.Spaces.w z) ^ 2)) (volume.restrict Work.Spaces.Iz) :=
      ((measurable_deriv (deriv φ)).abs.aestronglyMeasurable).mul
        (((measurable_id.pow_const 2).mul measurable_wSq).aestronglyMeasurable)
    exact (hA.add hB).mul (aesm_P2 h)
  refine (hP.const_mul (max (4 * C₁ + C₂) 0)).mono' haesm ?_
  filter_upwards [ae_pos_of_mem_Iz] with z hz
  have hW2' := deriv_zsqwSq_abs_le z hz
  have hC₁z : |deriv φ z| * z ≤ C₁ := hC₁ z
  have hC₂z : |deriv (deriv φ) z| * z ^ 2 ≤ C₂ := hC₂ z
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hznn : 0 ≤ z := le_of_lt hz
  have hcoef : (2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
      + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      ≤ max (4 * C₁ + C₂) 0 * (Work.Spaces.w z) ^ 2 := by
    have h1 : 2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
        ≤ 4 * (|deriv φ z| * z) * (Work.Spaces.w z) ^ 2 := by
      calc 2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          ≤ 2 * |deriv φ z| * (2 * z * (Work.Spaces.w z) ^ 2) := by
            exact mul_le_mul_of_nonneg_left hW2' (by positivity)
        _ = 4 * (|deriv φ z| * z) * (Work.Spaces.w z) ^ 2 := by ring
    have h2 : |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ C₂ * (Work.Spaces.w z) ^ 2 := by
      calc |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)
          = (|deriv (deriv φ) z| * z ^ 2) * (Work.Spaces.w z) ^ 2 := by ring
        _ ≤ C₂ * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hC₂z hw2
    have h3 : 4 * (|deriv φ z| * z) * (Work.Spaces.w z) ^ 2 ≤ 4 * C₁ * (Work.Spaces.w z) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) hw2
    have h4 : (4 * C₁ + C₂) * (Work.Spaces.w z) ^ 2 ≤ max (4 * C₁ + C₂) 0 * (Work.Spaces.w z) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hw2
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
        + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
      ≤ (max (4 * C₁ + C₂) 0 * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) :=
        mul_le_mul_of_nonneg_right hcoef (hP2nn z)
    _ = max (4 * C₁ + C₂) 0 * ((Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) := by ring

/-! ## The three truncation bounds

Each is of the "junk-friendly" shape: the pointwise bound holds a.e., the dominating function is
nonnegative a.e. and integrable, so the comparison of the iterated integrals follows whether or not
the bounded side is integrable. -/

/-- The source pairing `∫_z φ w² ∫_θ FΨ` obeys the angular AM–GM. -/
theorem trunc_A_le (h : Hon α F Ψ) {φ : ℝ → ℝ} (hφ0 : ∀ z : ℝ, 0 ≤ φ z)
    (hPc : IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz)
    (hS : IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2)) Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, F z θ * Ψ z θ))
      ≤ (1 / 2) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2))
        + (1 / 2) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) := by
  have hgint : IntegrableOn (fun z => (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2))
      + (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))) Work.Spaces.Iz :=
    (hS.const_mul (1 / 2)).add (hPc.const_mul (1 / 2))
  have hg0 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iz] (fun z => (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2))
      + (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))) :=
    Filter.Eventually.of_forall fun z => by
      have h1 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 :=
        integral_nonneg fun θ => sq_nonneg _
      have h3 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 :=
        integral_nonneg fun θ => sq_nonneg _
      have h4 : 0 ≤ φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2) :=
        mul_nonneg (mul_nonneg (hφ0 z) h1) h2
      have h5 : 0 ≤ φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) :=
        mul_nonneg (mul_nonneg (hφ0 z) h1) h3
      first | simp only [Pi.zero_apply] | skip
      linarith
  have hle : (fun z => φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, F z θ * Ψ z θ))
      ≤ᵐ[volume.restrict Work.Spaces.Iz]
      (fun z => (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2))
        + (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))) := by
    filter_upwards [ae_pos_of_mem_Iz] with z hz
    have hamgm := hon_slice_amgm h hz
    have hw : 0 ≤ φ z * (Work.Spaces.w z) ^ 2 := mul_nonneg (hφ0 z) (sq_nonneg _)
    calc φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, F z θ * Ψ z θ)
        = (φ z * (Work.Spaces.w z) ^ 2) * (∫ θ in Work.Spaces.Iθ, F z θ * Ψ z θ) := by ring
      _ ≤ (φ z * (Work.Spaces.w z) ^ 2)
            * ((1 / 2) * (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2)
              + (1 / 2) * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hamgm hw
      _ = (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2))
          + (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) := by ring
  have hmain := setIntegral_le_of_ae_le_of_nonneg hle hg0 hgint
  rw [integral_add (hS.const_mul (1 / 2)) (hPc.const_mul (1 / 2)),
    integral_const_mul, integral_const_mul] at hmain
  exact hmain

/-- The second-order truncation term obeys the paper's pointwise weight bound. -/
theorem trunc_B2_le (h : Hon α F Ψ) {φ : ℝ → ℝ} (hφ0 : ∀ z : ℝ, 0 ≤ φ z)
    (hφ2 : ContDiff ℝ 2 φ)
    (hE1 : IntegrableOn (fun z => (2 * |deriv φ z|
        * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
        + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz)
    (hPc : IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz,
        deriv (deriv (fun z => φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      ≤ (∫ z in Work.Spaces.Iz, (2 * |deriv φ z|
          * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
        + 6 * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) := by
  have hP2nn : ∀ z : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 :=
    fun z => integral_nonneg fun θ => sq_nonneg _
  have hgint : IntegrableOn (fun z => ((2 * |deriv φ z|
        * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
        + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      + 6 * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)))
      Work.Spaces.Iz :=
    hE1.add (hPc.const_mul 6)
  have hg0 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iz] (fun z => ((2 * |deriv φ z|
        * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
        + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      + 6 * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))) :=
    Filter.Eventually.of_forall fun z => by
      have h1 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 :=
        integral_nonneg fun θ => sq_nonneg _
      have h2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have h3 : 0 ≤ 2 * |deriv φ z|
          * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2) :=
        add_nonneg (mul_nonneg (by positivity) (abs_nonneg _))
          (mul_nonneg (abs_nonneg _) (mul_nonneg (sq_nonneg _) h2))
      have h4 : 0 ≤ (2 * |deriv φ z|
          * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) := mul_nonneg h3 h1
      have h5 : 0 ≤ φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) :=
        mul_nonneg (mul_nonneg (hφ0 z) h2) h1
      first | simp only [Pi.zero_apply] | skip
      linarith
  have hle : (fun z => deriv (deriv (fun z => φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      ≤ᵐ[volume.restrict Work.Spaces.Iz]
      (fun z => ((2 * |deriv φ z|
          * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
        + 6 * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))) := by
    filter_upwards [ae_pos_of_mem_Iz] with z hz
    obtain ⟨-, -, -, -, -, hW2le, -, -, -, -, -⟩ :=
      Work.FTS.EllipticEst.weight_algebra_fts
    have hW2 := hW2le z hz
    have hderiv := TruncCutDerivTwo φ hφ2 z hz
    have hP2 := hP2nn z
    have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hw2z : 0 ≤ z ^ 2 * (Work.Spaces.w z) ^ 2 := mul_nonneg (sq_nonneg _) hw2
    have hb1 : deriv (deriv φ) z * (z ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hw2z
    have hb2 : 2 * deriv φ z * deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z
        ≤ 2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z| := by
      have h0 : deriv φ z * deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z
          ≤ |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z| := by
        rw [← abs_mul]
        exact le_abs_self _
      linarith [h0]
    have hb3 : φ z * deriv (deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2)) z
        ≤ 6 * (φ z * (Work.Spaces.w z) ^ 2) := by
      have hh := mul_le_mul_of_nonneg_left hW2 (hφ0 z)
      linarith [hh]
    have hsum : deriv (deriv (fun z => φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
        ≤ (2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
          + 6 * (φ z * (Work.Spaces.w z) ^ 2) := by
      rw [hderiv]
      linarith [hb1, hb2, hb3]
    calc deriv (deriv (fun z => φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
        ≤ ((2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
          + 6 * (φ z * (Work.Spaces.w z) ^ 2)) * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) :=
          mul_le_mul_of_nonneg_right hsum hP2
      _ = ((2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
        + 6 * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) := by ring
  have hmain := setIntegral_le_of_ae_le_of_nonneg hle hg0 hgint
  rw [integral_add hE1 (hPc.const_mul 6), integral_const_mul] at hmain
  exact hmain

/-- The first-order truncation term obeys the paper's pointwise weight bound. -/
theorem trunc_B1_le (h : Hon α F Ψ) {φ : ℝ → ℝ} (hφ0 : ∀ z : ℝ, 0 ≤ φ z)
    (hφ2 : ContDiff ℝ 2 φ)
    (hE2 : IntegrableOn (fun z => |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz)
    (hPc : IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz) :
    -(∫ z in Work.Spaces.Iz,
        deriv (fun z => φ z * (Work.Spaces.w z) ^ 2 * z) z
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      ≤ (∫ z in Work.Spaces.Iz, |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
        + 3 * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) := by
  have hP2nn : ∀ z : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 :=
    fun z => integral_nonneg fun θ => sq_nonneg _
  have hgint : IntegrableOn (fun z => (|deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      + 3 * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)))
      Work.Spaces.Iz :=
    hE2.add (hPc.const_mul 3)
  have hg0 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iz] (fun z => (|deriv φ z|
      * (z * (Work.Spaces.w z) ^ 2) * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      + 3 * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))) := by
    filter_upwards [ae_pos_of_mem_Iz] with z hz
    have h1 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 :=
      integral_nonneg fun θ => sq_nonneg _
    have h2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have h3 : 0 ≤ z * (Work.Spaces.w z) ^ 2 := mul_nonneg (le_of_lt hz) h2
    have h4 : 0 ≤ |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) h3) h1
    have h5 : 0 ≤ φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) :=
      mul_nonneg (mul_nonneg (hφ0 z) h2) h1
    first | simp only [Pi.zero_apply] | skip
    linarith
  -- the pointwise lower bound
  have hle : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      -((|deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
        + 3 * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)))
      ≤ deriv (fun z => φ z * (Work.Spaces.w z) ^ 2 * z) z
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) := by
    filter_upwards [ae_pos_of_mem_Iz] with z hz
    obtain ⟨-, -, -, -, -, -, hW1le, -, -, -, -⟩ :=
      Work.FTS.EllipticEst.weight_algebra_fts
    have hW1 := hW1le z hz
    have hderiv := TruncCutDerivOne φ hφ2 z hz
    have hP2 := hP2nn z
    have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hz1 : 0 ≤ z * (Work.Spaces.w z) ^ 2 := mul_nonneg (le_of_lt hz) hw2
    -- the two nonnegative contributions to `deriv (φ w² z) z + |deriv φ z| (z w²) + 3 φ w²`
    have hA : 0 ≤ (deriv φ z + |deriv φ z|) * (z * (Work.Spaces.w z) ^ 2) :=
      mul_nonneg (by linarith [neg_le_abs (deriv φ z)]) hz1
    have hB : 0 ≤ φ z
        * (deriv (fun z => z * (Work.Spaces.w z) ^ 2) z + 3 * (Work.Spaces.w z) ^ 2) :=
      mul_nonneg (hφ0 z) (by linarith [hW1])
    rw [hderiv]
    nlinarith [hA, hB, hP2, mul_nonneg (add_nonneg hA hB) hP2]
  have hmain := neg_setIntegral_le_of_ae_le hle hg0 hgint
  rw [integral_add hE2 (hPc.const_mul 3), integral_const_mul] at hmain
  exact hmain


/-! ## The general form of the truncated inequality, and the main statement -/



end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.Yc.HonSliceRightTendstoYc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest.Yc.RightTendsto

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Elementary facts about the angular weight `σ = sEta` -/

theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sin_two_le_one (θ : ℝ) : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _

/-- `σ = sin(2θ)^{-η} ≥ 0` on `Iθ`. -/
theorem sEta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

/-- `σ > 0` on the open interval. -/
theorem sEta_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Work.FTS.EllipticEst.sEta θ := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  simpa only [Work.FTS.EllipticEst.sEta] using Real.rpow_pos_of_pos hs (-(Work.Spaces.eta))

/-- `σ ≥ 1` on the open interval. -/
theorem one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  have hpos := sin_two_pos_of_mem_Ioo hθ
  have hle := sin_two_le_one θ
  have hz : -(Work.Spaces.eta) ≤ 0 := by
    have : (0 : ℝ) ≤ Work.Spaces.eta := by norm_num [Work.Spaces.eta]
    linarith
  simpa using Real.rpow_le_rpow_of_nonpos hpos hle hz

/-- On `Iθ`, `σ⁻¹ = sin(2θ)^{η} ≤ 1`. -/
theorem inv_sEta_le_one {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.FTS.EllipticEst.sEta θ)⁻¹ ≤ 1 := by
  have hne : -(Work.Spaces.eta) ≠ 0 := by
    have : (0 : ℝ) < Work.Spaces.eta := by norm_num [Work.Spaces.eta]
    linarith
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · rw [← h0, Work.FTS.EllipticEst.sEta]
    simp only [mul_zero, Real.sin_zero]
    rw [Real.zero_rpow hne]
    norm_num
  · rcases eq_or_lt_of_le hθ.2 with hpi | hpi
    · rw [hpi, Work.FTS.EllipticEst.sEta]
      have hzero : Real.sin (2 * (Real.pi / 2)) = 0 := by
        rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      rw [hzero, Real.zero_rpow hne]
      norm_num
    · have hs0 : 0 ≤ Real.sin (2 * θ) :=
        sin_two_nonneg_of_mem_Iθ ⟨le_of_lt h0, le_of_lt hpi⟩
      have hs1 : Real.sin (2 * θ) ≤ 1 := sin_two_le_one θ
      have hη : 0 ≤ Work.Spaces.eta := by norm_num [Work.Spaces.eta]
      have hinv : (Work.FTS.EllipticEst.sEta θ)⁻¹
          = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
        rw [Work.FTS.EllipticEst.sEta, Real.rpow_neg hs0 Work.Spaces.eta, inv_inv]
      rw [hinv]
      exact Real.rpow_le_one hs0 hs1 hη

/-- A `C^n` function on the open interval is a.e. strongly measurable for `volume.restrict Iθ`
(it agrees a.e. with a continuous function). -/
theorem aesm_of_contDiffOn_Ioo {u : ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ) := by
  obtain ⟨g, hgm, hge⟩ := h.continuousOn.aemeasurable measurableSet_Ioo
  refine ⟨g, hgm.stronglyMeasurable, ?_⟩
  have h1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (0 : ℝ) := by
    rw [MeasureTheory.ae_iff]; simpa using MeasureTheory.measure_singleton (0 : ℝ)
  have h2 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ Real.pi / 2 := by
    rw [MeasureTheory.ae_iff]; simpa using MeasureTheory.measure_singleton (Real.pi / 2)
  have h3 : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Ioo 0 (Real.pi / 2) → u x = g x := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Ioo] at hge
    exact hge
  rw [Filter.EventuallyEq, Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3 hxI
  exact hx3 ⟨lt_of_le_of_ne hxI.1 (Ne.symm hx1), lt_of_le_of_ne hxI.2 hx2⟩

/-- **Smoothness of a `θ`-slice.**  A function that is `C^n` on the open quadrant is `C^n`
along every slice `θ ↦ Ψ z θ` with `z > 0`. -/
theorem contDiffOn_slice (Ψ : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z) {n : ℕ}
    (h : ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ n (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hc : ContDiff ℝ n (fun θ : ℝ => (z, θ)) := contDiff_prodMk_right z
  have h1 : ContDiffOn ℝ n (Function.uncurry Ψ ∘ fun θ : ℝ => (z, θ))
      (Set.Ioo 0 (Real.pi / 2)) :=
    h.comp hc.contDiffOn (fun θ hθ => ⟨hz, hθ⟩)
  refine h1.congr (fun θ _ => ?_)
  simp [Function.comp, Function.uncurry]

/-- A `C¹`-function on an open subset of `ℝ × ℝ` has differentiable `z`-slices on that set,
with derivative the `z`-partial `pz`. -/
theorem hasDerivAt_slice_of_contDiffOn_open {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 (Function.uncurry G) U) {u θ : ℝ} (hmem : (u, θ) ∈ U) :
    HasDerivAt (fun u' => G u' θ) (Work.Spaces.pz G u θ) u := by
  have hd : DifferentiableAt ℝ (Function.uncurry G) (u, θ) :=
    (hG.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hmem)
  have hcur : DifferentiableAt ℝ (fun u' => G u' θ) u :=
    Work.Spaces.differentiableAt_curry_left hd
  simpa [Work.Spaces.pz] using hcur.hasDerivAt

/-- The open quadrant on which the honest class is smooth. -/
abbrev Qd : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)

theorem isOpen_Qd : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo

/-- `pzIter 2 Ψ` is `pz (pz Ψ)`. -/
theorem pzIter_two_eq (Ψ : ℝ → ℝ → ℝ) :
    Work.Spaces.pzIter 2 Ψ = Work.Spaces.pz (Work.Spaces.pz Ψ) := by
  have h2 : (2 : ℕ) = 1 + 1 := by norm_num
  rw [h2, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]

/-- `pthIter 2 Ψ` is `deriv (deriv (slice))`. -/
theorem pthIter_two_eq (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    (fun θ => Work.Spaces.pthIter 2 Ψ z θ)
      = deriv (fun θ' => deriv (fun θ'' => Ψ z θ'') θ') := rfl

/-- `pthIter 2 Ψ` is `pth (pth Ψ)`. -/
theorem pthIter_two_eq_fun (Ψ : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter 2 Ψ = Work.Spaces.pth (Work.Spaces.pth Ψ) := by
  have h2 : (2 : ℕ) = 1 + 1 := by norm_num
  rw [h2, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]

/-! ## Slice integrability from `HkMem` -/

/-- At level `0`, on the angular interval, the `Hk`-integrand is `(g z θ)² · w z² · σ θ`. -/
theorem HkIntegrand_zero_eq_Iθ (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  rw [HkIntegrand_zero_eq α g z θ, mul_pow, sq_weight_eq (sin_two_nonneg_of_mem_Iθ hθ),
    Work.FTS.EllipticEst.sEta]
  ring

/-- **Slicewise integrability from `HkMem`**: for `z > 0` the `σ`-weighted square of the slice
is integrable in `θ`. -/
theorem HkMemSliceSqSigma {α : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.HkMem α 0 g) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have hw : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]; positivity
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    (hg.1 z (Set.mem_Ici.mpr (le_of_lt hz))).congr_fun
      (fun θ hθ => HkIntegrand_zero_eq_Iθ α g hθ) measurableSet_Icc
  have h2 := h1.const_mul ((Work.Spaces.w z) ^ 2)⁻¹
  refine MeasureTheory.IntegrableOn.congr_fun h2 (fun θ _ => ?_) measurableSet_Icc
  field_simp

/-- **The `σ`-weighted square of a slice is locally `z`-integrable** (in the extended-value
sense), from the honest `z`-integral of `HkMem α 0 g`. -/
theorem HkMemSliceGammaLinTop {α : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.HkMem α 0 g) {z₀ : ℝ}
    (hz : 0 < z₀) :
    ∫⁻ s in Set.Icc z₀ (z₀ + 1), ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) < ⊤ := by
  have hG : ∀ s, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g s θ)
      = (Work.Spaces.w s) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    intro s
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ hθ => by rw [HkIntegrand_zero_eq_Iθ α g hθ]; ring)
  have hmem := hg.2.congr_fun (fun s _ => hG s) measurableSet_Ici
  have hnonneg : 0 ≤ᵐ[volume.restrict Work.Spaces.Iz]
      (fun s => (Work.Spaces.w s) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) :=
    Filter.Eventually.of_forall (fun s => mul_nonneg (sq_nonneg _)
      (MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))))
  have hfin : ∫⁻ s in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w s) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) < ⊤ := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem hnonneg]
    exact ENNReal.ofReal_lt_top
  have hAEM : AEMeasurable (fun s => ENNReal.ofReal ((Work.Spaces.w s) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      (volume.restrict Work.Spaces.Iz) :=
    hmem.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hAEMK : AEMeasurable (fun s => ENNReal.ofReal ((Work.Spaces.w s) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      (volume.restrict (Set.Icc z₀ (z₀ + 1))) :=
    ((hmem.mono_set (fun s hs => Set.mem_Ici.mpr (le_trans (le_of_lt hz) hs.1))).aestronglyMeasurable.aemeasurable).ennreal_ofReal
  have hscale : ∀ s ∈ Set.Icc z₀ (z₀ + 1),
      1 ≤ ((z₀ + 1) ^ 4) * (Work.Spaces.w s) ^ 2 := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans (le_of_lt hz) hs.1
    have hs4 : 0 < s ^ 4 := pow_pos (lt_of_lt_of_le hz hs.1) 4
    have h3 : s ^ 4 ≤ (z₀ + 1) ^ 4 * (1 + s) ^ 4 := by
      have hA : s ^ 4 ≤ (z₀ + 1) ^ 4 := pow_le_pow_left₀ hs0 hs.2 4
      have hB : (1 : ℝ) ≤ (1 + s) ^ 4 := one_le_pow₀ (by linarith)
      have hC : (0 : ℝ) ≤ (z₀ + 1) ^ 4 := by positivity
      nlinarith [hA, hB, hC]
    rw [Work.Spaces.w]
    have hws : ((1 + s) ^ 2 / s ^ 2) ^ 2 = (1 + s) ^ 4 / s ^ 4 := by ring
    rw [hws, mul_div_assoc', le_div_iff₀ hs4]
    nlinarith [h3]
  have hstep : ∫⁻ s in Set.Icc z₀ (z₀ + 1), ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ ENNReal.ofReal ((z₀ + 1) ^ 4) * ∫⁻ s in Set.Icc z₀ (z₀ + 1), ENNReal.ofReal
          (((Work.Spaces.w s) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
    rw [← MeasureTheory.lintegral_const_mul'' _ hAEMK]
    refine MeasureTheory.lintegral_mono_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun s hs => ?_)
    have hγ : 0 ≤ ∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
    have h1 : (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ (((z₀ + 1) ^ 4) * (Work.Spaces.w s) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      have := mul_le_mul_of_nonneg_right (hscale s hs) hγ
      simpa [one_mul] using this
    calc ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ ENNReal.ofReal ((((z₀ + 1) ^ 4) * (Work.Spaces.w s) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
          refine (ENNReal.ofReal_le_ofReal_iff ?_).mpr h1
          positivity
      _ = ENNReal.ofReal ((z₀ + 1) ^ 4) * ENNReal.ofReal (((Work.Spaces.w s) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
          rw [mul_assoc, ENNReal.ofReal_mul (by positivity)]
  calc ∫⁻ s in Set.Icc z₀ (z₀ + 1), ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ ENNReal.ofReal ((z₀ + 1) ^ 4) * ∫⁻ s in Set.Icc z₀ (z₀ + 1), ENNReal.ofReal
          (((Work.Spaces.w s) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := hstep
    _ ≤ ENNReal.ofReal ((z₀ + 1) ^ 4) * ∫⁻ s in Work.Spaces.Iz, ENNReal.ofReal
          (((Work.Spaces.w s) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact MeasureTheory.lintegral_mono_set
          (fun s hs => Set.mem_Ici.mpr (le_trans (le_of_lt hz) hs.1))
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-! ## Differentiation under the `θ`-integral sign -/

/-- **Differentiation under the `θ`-integral sign.**  If `ψ` is jointly continuous on the closed
rectangle `[z/2, 2z] × [a,b]`, so is its `z`-partial `pz ψ`, and `x ↦ ψ x t` has derivative
`pz ψ x t` on `(z/2, 2z)` for each `t ∈ [a,b]`, then `s ↦ ∫_a^b ψ s θ dθ` has derivative
`∫_a^b pz ψ z θ dθ` at `z`. -/
theorem hasDerivAt_sliceIntegral {ψ : ℝ → ℝ → ℝ} {a b z : ℝ} (hab : a ≤ b) (ha : 0 < a)
    (hb : b < Real.pi / 2) (hz : 0 < z)
    (hsz : ContinuousOn (fun p : ℝ × ℝ => ψ p.1 p.2)
      (Set.Icc (z / 2) (2 * z) ×ˢ Set.Icc a b))
    (hsz' : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz ψ p.1 p.2)
      (Set.Icc (z / 2) (2 * z) ×ˢ Set.Icc a b))
    (hdiff : ∀ t ∈ Set.Icc a b, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      HasDerivAt (fun x' => ψ x' t) (Work.Spaces.pz ψ x t) x) :
    HasDerivAt (fun s => ∫ θ in a..b, ψ s θ) (∫ θ in a..b, Work.Spaces.pz ψ z θ) z := by
  have hs_nhds : Set.Ioo (z / 2) (2 * z) ∈ 𝓝 z :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hsz'
  have hcurve : ContinuousOn (fun θ' : ℝ => (z, θ')) (Set.Icc a b) :=
    (show Continuous (fun θ' : ℝ => (z, θ')) by continuity).continuousOn
  have hslice : ContinuousOn (fun θ : ℝ => ψ z θ) (Set.Icc a b) :=
    hsz.comp hcurve (fun θ hθ => ⟨⟨by linarith, by linarith⟩, hθ⟩)
  have hslice' : ContinuousOn (fun θ : ℝ => Work.Spaces.pz ψ z θ) (Set.Icc a b) :=
    hsz'.comp hcurve (fun θ hθ => ⟨⟨by linarith, by linarith⟩, hθ⟩)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := a) (b := b) (F := fun x θ => ψ x θ) (F' := fun x θ => Work.Spaces.pz ψ x θ)
    (x₀ := z) (s := Set.Ioo (z / 2) (2 * z)) (μ := volume) (bound := fun _ => C)
    hs_nhds ?_ ?_ ?_ ?_ ?_ ?_).2
  · refine Filter.Eventually.mono (p := fun x => x ∈ Set.Ioo (z / 2) (2 * z)) hs_nhds
      (fun x hx => ?_)
    have h2 : ContinuousOn (fun θ : ℝ => ψ x θ) (Set.Icc a b) :=
      hsz.comp (show Continuous (fun θ : ℝ => (x, θ)) by continuity).continuousOn (fun θ hθ => ⟨⟨le_of_lt hx.1, le_of_lt hx.2⟩, hθ⟩)
    have h3 : ContinuousOn (fun θ : ℝ => ψ x θ) (Set.uIcc a b) := by
      rwa [Set.uIcc_of_le hab]
    exact (h3.aestronglyMeasurable measurableSet_uIcc).mono_measure
      (Measure.restrict_mono Set.uIoc_subset_uIcc le_rfl)
  · have h3 : ContinuousOn (fun θ : ℝ => ψ z θ) (Set.uIcc a b) := by
      rwa [Set.uIcc_of_le hab]
    exact h3.intervalIntegrable
  · have h3 : ContinuousOn (fun θ : ℝ => Work.Spaces.pz ψ z θ) (Set.uIcc a b) := by
      rwa [Set.uIcc_of_le hab]
    exact (h3.aestronglyMeasurable measurableSet_uIcc).mono_measure
      (Measure.restrict_mono Set.uIoc_subset_uIcc le_rfl)
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mp
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc (fun t ht x hx => ?_))
    rw [Set.uIoc_of_le hab] at ht
    exact hC (x, t) ⟨⟨le_of_lt hx.1, le_of_lt hx.2⟩, ⟨le_of_lt ht.1, ht.2⟩⟩
  · exact intervalIntegrable_const
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mp
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc (fun t ht x hx => ?_))
    rw [Set.uIoc_of_le hab] at ht
    exact hdiff t ⟨le_of_lt ht.1, ht.2⟩ x hx

/-- **Boundedness of a slice and of its derivative.**  If `(u'')²·σ` is integrable on `Iθ` then
`u'' ∈ L¹` on the open interval (`σ ≥ 1` there), so `u'` has the oscillation bound
`|u' x - u' y| ≤ ∫|u''|`, and `u` is bounded by integrating once more. -/
theorem SliceBddSqSigma {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
        * sEta θ) Work.Spaces.Iθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv u θ| ≤ C ∧ |u θ| ≤ C := by
  have hq0 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hq : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hIq : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hq0, hq⟩
  have hsq : MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_sq_of_integrableOn_mul_sEta u h2
  have habs2 : MeasureTheory.IntegrableOn (fun θ => |deriv (fun t => deriv u t) θ|)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_abs_of_integrableOn_sq u hsq
  have hderiv2 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t => deriv u t) x) x := by
    intro x hx
    have h2' : ContDiffAt ℝ 2 u x := (hsm.contDiffAt (isOpen_Ioo.mem_nhds hx)).of_le (by norm_num)
    have h1 : ContDiffAt ℝ 1 (deriv u) x := h2'.derivWithin (by norm_num)
    exact (h1.differentiableAt (by norm_num)).hasDerivAt
  have hMono : ∀ {a b : ℝ}, a ≤ b → Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      ∫ s in a..b, |deriv (fun t => deriv u t) s|
        ≤ ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s| := by
    intro a b hab hsub
    rw [intervalIntegral.integral_of_le hab]
    exact MeasureTheory.setIntegral_mono_set habs2
      (Filter.Eventually.of_forall fun s => abs_nonneg _)
      (Filter.Eventually.of_forall fun s hs => hsub ⟨le_of_lt hs.1, hs.2⟩)
  have hFTC2 : ∀ {a b : ℝ}, a ≤ b → Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      ∫ s in a..b, deriv (fun t => deriv u t) s = deriv u b - deriv u a := by
    intro a b hab hsub
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab ?_ ?_ ?_
    · intro z hz
      exact ((hderiv2 z (hsub hz)).continuousAt).continuousWithinAt
    · intro z hz
      exact hderiv2 z (hsub ⟨le_of_lt hz.1, le_of_lt hz.2⟩)
    · have h1 : MeasureTheory.IntegrableOn (fun s => deriv (fun t => deriv u t) s)
          (Set.Ioc a b) :=
        MeasureTheory.Integrable.mono'
          (habs2.mono_set fun z hz => hsub ⟨le_of_lt hz.1, hz.2⟩)
          (measurable_deriv _).aestronglyMeasurable
          (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs])
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr h1
  have hosc : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv u x - deriv u y|
        ≤ ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s| := by
    intro x hx y hy
    rcases le_total x y with hxy | hyx
    · have hsub : Set.Icc x y ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun z hz =>
        ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩
      rw [abs_sub_comm, ← hFTC2 hxy hsub]
      have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
        (f := fun s => deriv (fun t => deriv u t) s) hxy
      simp only [Real.norm_eq_abs] at h1
      exact h1.trans (hMono hxy hsub)
    · have hsub : Set.Icc y x ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun z hz =>
        ⟨lt_of_lt_of_le hy.1 hz.1, lt_of_le_of_lt hz.2 hx.2⟩
      rw [← hFTC2 hyx hsub]
      have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
        (f := fun s => deriv (fun t => deriv u t) s) hyx
      simp only [Real.norm_eq_abs] at h1
      exact h1.trans (hMono hyx hsub)
  have hud : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv u θ| ≤ |deriv u (Real.pi / 4)|
        + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s| := by
    intro θ hθ
    have h := hosc θ hθ (Real.pi / 4) hIq
    have h1 : |deriv u θ| ≤ |deriv u θ - deriv u (Real.pi / 4)| + |deriv u (Real.pi / 4)| := by
      have := abs_add_le (deriv u θ - deriv u (Real.pi / 4)) (deriv u (Real.pi / 4))
      simpa using this
    linarith
  have hIint : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |∫ s in (Real.pi / 4)..θ, deriv u s|
        ≤ (|deriv u (Real.pi / 4)|
            + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s|)
          * (Real.pi / 2) := by
    intro θ hθ
    have hb : ∀ s ∈ Set.uIoc (Real.pi / 4) θ,
        ‖deriv u s‖ ≤ |deriv u (Real.pi / 4)|
          + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s| := by
      intro s hs
      rw [Set.uIoc, Set.mem_Ioc] at hs
      have hs' : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨lt_trans (lt_min hq0 hθ.1) hs.1, lt_of_le_of_lt hs.2 (max_lt hq hθ.2)⟩
      rw [Real.norm_eq_abs]
      exact hud s hs'
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (f := deriv u)
      (C := |deriv u (Real.pi / 4)|
        + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s|) hb
    have h2 : |θ - Real.pi / 4| ≤ Real.pi / 2 := by
      refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
      · linarith [hθ.1, hθ.2, hq0, Real.pi_pos]
      · linarith [hθ.1, hθ.2, hq0, Real.pi_pos]
    have h3 : 0 ≤ |deriv u (Real.pi / 4)|
        + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s| := by
      have hI : 0 ≤ ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s| :=
        integral_nonneg fun s => abs_nonneg _
      linarith [abs_nonneg (deriv u (Real.pi / 4)), hI]
    calc |∫ s in (Real.pi / 4)..θ, deriv u s|
        ≤ (|deriv u (Real.pi / 4)|
            + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s|)
          * |θ - Real.pi / 4| := by
          simpa only [Real.norm_eq_abs] using h1
      _ ≤ (|deriv u (Real.pi / 4)|
            + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s|)
          * (Real.pi / 2) := mul_le_mul_of_nonneg_left h2 h3
  have hFTCu : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∫ s in (Real.pi / 4)..θ, deriv u s = u θ - u (Real.pi / 4) := by
    intro θ hθ
    rcases le_total (Real.pi / 4) θ with hle | hle
    · have hsub : Set.Icc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun z hz =>
        ⟨lt_of_lt_of_le hq0 hz.1, lt_of_le_of_lt hz.2 hθ.2⟩
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle ?_ ?_ ?_
      · intro z hz
        exact ((hsm.contDiffAt (isOpen_Ioo.mem_nhds (hsub hz))).continuousAt).continuousWithinAt
      · intro z hz
        exact ((hsm.contDiffAt (isOpen_Ioo.mem_nhds
          (hsub ⟨le_of_lt hz.1, le_of_lt hz.2⟩))).differentiableAt (by norm_num)).hasDerivAt
      · have hcd : ContinuousOn (deriv u) (Set.uIcc (Real.pi / 4) θ) := fun z hz => by
          rw [Set.uIcc_of_le hle] at hz
          exact ((hderiv2 z (hsub hz)).continuousAt).continuousWithinAt
        exact hcd.intervalIntegrable
    · have hsub : Set.Icc θ (Real.pi / 4) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun z hz =>
        ⟨lt_of_lt_of_le hθ.1 hz.1, lt_of_le_of_lt hz.2 hq⟩
      have h1 : ∫ s in θ..(Real.pi / 4), deriv u s = u (Real.pi / 4) - u θ := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle ?_ ?_ ?_
        · intro z hz
          exact ((hsm.contDiffAt (isOpen_Ioo.mem_nhds (hsub hz))).continuousAt).continuousWithinAt
        · intro z hz
          exact ((hsm.contDiffAt (isOpen_Ioo.mem_nhds
            (hsub ⟨le_of_lt hz.1, le_of_lt hz.2⟩))).differentiableAt (by norm_num)).hasDerivAt
        · have hcd : ContinuousOn (deriv u) (Set.uIcc θ (Real.pi / 4)) := fun z hz => by
            rw [Set.uIcc_of_le hle] at hz
            exact ((hderiv2 z (hsub hz)).continuousAt).continuousWithinAt
          exact hcd.intervalIntegrable
      rw [intervalIntegral.integral_symm (a := θ) (b := Real.pi / 4), h1]
      ring
  have hubd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |u θ| ≤ |u (Real.pi / 4)|
        + (|deriv u (Real.pi / 4)|
            + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s|)
          * (Real.pi / 2) := by
    intro θ hθ
    have h1 : |u θ| ≤ |u (Real.pi / 4)| + |u θ - u (Real.pi / 4)| := by
      have := abs_add_le (u (Real.pi / 4)) (u θ - u (Real.pi / 4))
      simpa using this
    have h2 : |u θ - u (Real.pi / 4)| ≤ (|deriv u (Real.pi / 4)|
        + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s|)
        * (Real.pi / 2) := by
      rw [(congrArg abs (hFTCu θ hθ)).symm]
      exact hIint θ hθ
    linarith
  set I0 : ℝ := ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s| with hI0def
  have hI0 : 0 ≤ I0 := by
    rw [hI0def]; exact integral_nonneg fun _ => abs_nonneg _
  have hA : 0 ≤ |u (Real.pi / 4)| := abs_nonneg _
  have hB : 0 ≤ |deriv u (Real.pi / 4)| := abs_nonneg _
  have hP' : 0 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h1P' : 1 ≤ 1 + Real.pi / 2 := by linarith [Real.pi_pos]
  have hS0 : 0 ≤ |u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1 := by linarith [hA, hB, hI0]
  have hSpos : 0 < |u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1 := by linarith [hA, hB, hI0]
  refine ⟨(|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * (1 + Real.pi / 2), ?_, ?_⟩
  · exact mul_pos hSpos (by linarith [h1P'])
  · intro θ hθ
    have hud' : |deriv u θ| ≤ |deriv u (Real.pi / 4)| + I0 := by
      rw [hI0def]; exact hud θ hθ
    have hubd' : |u θ| ≤ |u (Real.pi / 4)|
        + (|deriv u (Real.pi / 4)| + I0) * (Real.pi / 2) := by
      rw [hI0def]; exact hubd θ hθ
    have h9 : |deriv u θ| ≤ |deriv u (Real.pi / 4)| + I0 + 1 := by linarith [hud', hI0]
    have h10 : |deriv u (Real.pi / 4)| + I0 + 1
        ≤ (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * (1 + Real.pi / 2) := by
      have hle : |deriv u (Real.pi / 4)| + I0 + 1
          ≤ |u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1 := by linarith [hA]
      calc |deriv u (Real.pi / 4)| + I0 + 1
          ≤ (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * 1 := by
            rw [mul_one]; exact hle
        _ ≤ (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * (1 + Real.pi / 2) :=
            mul_le_mul_of_nonneg_left h1P' hS0
    have h12 : |u (Real.pi / 4)| + (|deriv u (Real.pi / 4)| + I0) * (Real.pi / 2)
        ≤ (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * (1 + Real.pi / 2) := by
      have hleA : |u (Real.pi / 4)| ≤ (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * 1 := by
        rw [mul_one]; linarith [hB, hI0]
      have hleX : (|deriv u (Real.pi / 4)| + I0) * (Real.pi / 2)
          ≤ (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * (Real.pi / 2) :=
        mul_le_mul_of_nonneg_right (by linarith [hA]) hP'
      calc |u (Real.pi / 4)| + (|deriv u (Real.pi / 4)| + I0) * (Real.pi / 2)
          ≤ (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * 1
            + (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * (Real.pi / 2) :=
            add_le_add hleA hleX
        _ = (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * (1 + Real.pi / 2) := by ring
    exact ⟨h9.trans h10, hubd'.trans h12⟩

/-! ## The `tan θ`-identity -/

/-- **The `tan θ`-identity.**  If `(tan θ · u)' = A + u'' + 6u` on `(a,b)` and the three
integrability hypotheses hold, then
`tan b · u b − tan a · u a = ∫_a^b A + (deriv u b − deriv u a) + 6 ∫_a^b u`. -/
theorem TanSliceFTC {u A : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hu : ∀ θ ∈ Set.uIcc a b, HasDerivAt u (deriv u θ) θ)
    (hu1 : ∀ θ ∈ Set.uIcc a b, HasDerivAt (deriv u) (deriv (fun t => deriv u t) θ) θ)
    (ht : ∀ θ ∈ Set.uIcc a b,
      HasDerivAt (fun t => Real.tan t * u t) (deriv (fun t => Real.tan t * u t) θ) θ)
    (hint1 : IntervalIntegrable (fun θ => deriv (fun t => deriv u t) θ) volume a b)
    (hint2 : IntervalIntegrable (fun θ => deriv (fun t => Real.tan t * u t) θ) volume a b)
    (hint3 : IntervalIntegrable A volume a b)
    (hint4 : IntervalIntegrable u volume a b)
    (heq : ∀ θ ∈ Set.Ioo a b, deriv (fun t => Real.tan t * u t) θ
              = A θ + deriv (fun t => deriv u t) θ + 6 * u θ) :
    Real.tan b * u b - Real.tan a * u a
      = (∫ θ in a..b, A θ) + (deriv u b - deriv u a) + 6 * ∫ θ in a..b, u θ := by
  have h1 : (∫ θ in a..b, deriv (fun t => Real.tan t * u t) θ)
      = Real.tan b * u b - Real.tan a * u a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt ht hint2
  have h2 : (∫ θ in a..b, deriv (fun t => deriv u t) θ) = deriv u b - deriv u a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hu1 hint1
  have h3 : (∫ θ in a..b, deriv (fun t => Real.tan t * u t) θ)
      = ∫ θ in a..b, (A θ + deriv (fun t => deriv u t) θ + 6 * u θ) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hb : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ b := by
      rw [MeasureTheory.ae_iff]; simpa using MeasureTheory.measure_singleton b
    filter_upwards [hb] with θ hθ hmem
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at hmem
    exact heq θ ⟨hmem.1, lt_of_le_of_ne hmem.2 hθ⟩
  have h4 : (∫ θ in a..b, (A θ + deriv (fun t => deriv u t) θ + 6 * u θ))
      = (∫ θ in a..b, A θ) + (∫ θ in a..b, deriv (fun t => deriv u t) θ)
        + 6 * ∫ θ in a..b, u θ := by
    rw [intervalIntegral.integral_add (hint3.add hint1) (hint4.const_mul 6),
      intervalIntegral.integral_add hint3 hint1, intervalIntegral.integral_const_mul]
  rw [← h1, h3, h4, h2]

/-! ## Elementary bounds -/

/-- For a nonnegative real function, the Bochner set integral is bounded by the `toReal` of its
`lintegral`; this needs no measurability hypothesis (the non-integrable case is `0`). -/
theorem setIntegral_le_toReal_lintegral {f : ℝ → ℝ} (s : Set ℝ)
    (hf : ∀ᵐ x ∂volume.restrict s, 0 ≤ f x) :
    (∫ x in s, f x) ≤ ENNReal.toReal (∫⁻ x in s, ENNReal.ofReal (f x)) := by
  by_cases h : AEStronglyMeasurable f (volume.restrict s)
  · rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hf h]
  · have hni : ¬ MeasureTheory.Integrable f (volume.restrict s) :=
      fun hi => h (Integrable.aestronglyMeasurable hi)
    rw [show (∫ x in s, f x) = ∫ x, f x ∂(volume.restrict s) from rfl,
      MeasureTheory.integral_undef hni]
    exact ENNReal.toReal_nonneg

/-- The AM–GM inequality `2|g| ≤ g²·σ + σ⁻¹` for `σ > 0`. -/
theorem two_mul_abs_le_sq_add_inv (g σ : ℝ) (hσ : 0 < σ) :
    2 * |g| ≤ g ^ 2 * σ + σ⁻¹ := by
  have h : 0 ≤ (|g| * Real.sqrt σ - 1 / Real.sqrt σ) ^ 2 := sq_nonneg _
  have h1 : (|g| * Real.sqrt σ) ^ 2 = g ^ 2 * σ := by
    rw [mul_pow, sq_abs, Real.sq_sqrt (le_of_lt hσ)]
  have h2 : (1 / Real.sqrt σ) ^ 2 = σ⁻¹ := by
    rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hσ), one_div]
  have h3 : 2 * (|g| * Real.sqrt σ) * (1 / Real.sqrt σ) = 2 * |g| := by
    field_simp
  nlinarith [h, h1, h2, h3]


/-- **The `θ`-`L¹` bound of a slice**: `∫_a^b |g| ≤ (1/2)(∫_{Iθ} g²σ + π/2)`. -/
theorem Ioc_abs_le_half {g : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi / 2) (hab : a ≤ b)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    (∫ θ in a..b, |g θ|)
      ≤ (1 / 2) * ((∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + Real.pi / 2) := by
  set Q : ℝ := ∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hQdef
  have hQnn : 0 ≤ Q := by
    rw [hQdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
  have hsub : Set.Ioc a b ⊆ Work.Spaces.Iθ := fun θ hθ =>
    ⟨le_of_lt (lt_trans ha hθ.1), le_of_lt (lt_of_le_of_lt hθ.2 hb)⟩
  have hQeq : ENNReal.ofReal Q = ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    rw [hQdef]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ)))
  have hpt : ∀ θ ∈ Set.Ioc a b, ENNReal.ofReal |g θ| ≤ ENNReal.ofReal (1 / 2)
      * (ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) + 1) := by
    intro θ hθ
    have hθp : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨lt_trans ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩
    have hσ : 0 < Work.FTS.EllipticEst.sEta θ := sEta_pos_of_mem_Ioo hθp
    have hσinv : (Work.FTS.EllipticEst.sEta θ)⁻¹ ≤ 1 := inv_sEta_le_one (hsub hθ)
    have h1 : |g θ| ≤ (1 / 2) * ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + 1) := by
      linarith [two_mul_abs_le_sq_add_inv (g θ) (Work.FTS.EllipticEst.sEta θ) hσ, hσinv]
    have hpos : (0 : ℝ) ≤ (1 / 2) * ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + 1) := by
      positivity
    calc ENNReal.ofReal |g θ|
        ≤ ENNReal.ofReal ((1 / 2) * ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + 1)) :=
          (ENNReal.ofReal_le_ofReal_iff hpos).mpr h1
      _ = ENNReal.ofReal (1 / 2)
            * (ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) + 1) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) (by norm_num),
            ENNReal.ofReal_one]
  have h1AEM : AEMeasurable (fun θ => ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      (volume.restrict (Set.Ioc a b)) :=
    ((hint.mono_set hsub).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hAEM : AEMeasurable (fun θ => ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      + (1 : ℝ≥0∞)) (volume.restrict (Set.Ioc a b)) :=
    h1AEM.add aemeasurable_const
  have hfin : ∫⁻ θ in Set.Ioc a b, ENNReal.ofReal (1 / 2)
      * (ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) + 1) < ⊤ := by
    rw [MeasureTheory.lintegral_const_mul'' _ hAEM, MeasureTheory.lintegral_add_left' h1AEM]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
    · exact lt_of_le_of_lt (le_trans (MeasureTheory.lintegral_mono_set hsub)
        (le_of_eq hQeq.symm)) ENNReal.ofReal_lt_top
    · rw [MeasureTheory.lintegral_const, one_mul, Measure.restrict_apply_univ]
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
  calc (∫ θ in a..b, |g θ|) = ∫ θ in Set.Ioc a b, |g θ| := intervalIntegral.integral_of_le hab
    _ ≤ ENNReal.toReal (∫⁻ θ in Set.Ioc a b, ENNReal.ofReal |g θ|) :=
        setIntegral_le_toReal_lintegral _ (Filter.Eventually.of_forall (fun θ => abs_nonneg _))
    _ ≤ ENNReal.toReal (∫⁻ θ in Set.Ioc a b, ENNReal.ofReal (1 / 2)
          * (ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) + 1)) :=
        ENNReal.toReal_mono (ne_of_lt hfin) (MeasureTheory.lintegral_mono_ae
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc hpt))
    _ = ENNReal.toReal (ENNReal.ofReal (1 / 2) * (∫⁻ θ in Set.Ioc a b,
          (ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) + 1))) := by
        rw [MeasureTheory.lintegral_const_mul'' _ hAEM]
    _ = ENNReal.toReal (ENNReal.ofReal (1 / 2) * ((∫⁻ θ in Set.Ioc a b,
          ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          + ∫⁻ θ in Set.Ioc a b, (1 : ℝ≥0∞))) := by
        rw [MeasureTheory.lintegral_add_left' h1AEM]
    _ ≤ ENNReal.toReal (ENNReal.ofReal (1 / 2) * (ENNReal.ofReal Q
          + ENNReal.ofReal (Real.pi / 2))) := by
        refine ENNReal.toReal_mono (by finiteness)
          (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by simp))
        · exact le_trans (MeasureTheory.lintegral_mono_set hsub) (le_of_eq hQeq.symm)
        · rw [MeasureTheory.lintegral_const, one_mul, Measure.restrict_apply_univ, Real.volume_Ioc]
          refine (ENNReal.ofReal_le_ofReal_iff ?_).mpr ?_
          · positivity
          · linarith [Real.pi_pos, hab]
    _ = (1 / 2) * (Q + Real.pi / 2) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
          ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal hQnn,
          ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    _ = (1 / 2) * ((∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + Real.pi / 2) := by rw [hQdef]

end Work.FTS.EllipticEst.Honest.Yc.RightTendsto

open Work.FTS.EllipticEst.Honest.Yc.RightTendsto

namespace Work.FTS.EllipticEst.Honest.Yc

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


end Work.FTS.EllipticEst.Honest.Yc
end
end
