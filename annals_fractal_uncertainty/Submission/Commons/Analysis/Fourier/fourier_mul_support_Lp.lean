import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Group.Integral
import Submission.Commons.Analysis.Fourier.fourier_mul_support_schwartz

/-!
# The Fourier transform of a product of an `L²` function with a Schwartz function

If `f ∈ L²(ℝᵈ)` has Fourier transform supported in a set `K` and `φ` is a Schwartz function whose
Fourier transform is supported in `K'`, then the pointwise product `f * φ` (an `L²` function) has
Fourier transform supported in `K + K'`.

This is the `L²` (as opposed to Schwartz) version of
`Commons.Analysis.Fourier.fourier_mul_support_schwartz`.
-/

set_option autoImplicit false

open MeasureTheory FourierTransform Topology Filter
open scoped FourierTransform ENNReal NNReal ComplexInnerProductSpace RealInnerProductSpace

namespace Commons.Analysis.Fourier

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- The pointwise product of two Schwartz functions, as a Schwartz function. -/
noncomputable def schwartzMul (ψ φ : SchwartzMap ℝᵈ ℂ) : SchwartzMap ℝᵈ ℂ :=
  (SchwartzMap.smulLeftCLM (F := ℂ) (⇑ψ)) φ

lemma schwartzMul_apply (ψ φ : SchwartzMap ℝᵈ ℂ) (x : ℝᵈ) :
    schwartzMul ψ φ x = ψ x * φ x := by
  rw [schwartzMul, SchwartzMap.smulLeftCLM_apply_apply (SchwartzMap.hasTemperateGrowth ψ)]
  simp

/-- The Fourier transform of a Schwartz function, as a Schwartz function. -/
noncomputable def schwartzFourier (ψ : SchwartzMap ℝᵈ ℂ) : SchwartzMap ℝᵈ ℂ :=
  FourierTransform.fourier ψ

lemma schwartzFourier_apply (ψ : SchwartzMap ℝᵈ ℂ) (x : ℝᵈ) :
    (schwartzFourier ψ : ℝᵈ → ℂ) x = 𝓕 (ψ : ℝᵈ → ℂ) x :=
  congrFun (SchwartzMap.fourier_coe ψ) x

lemma temperate_sub (ξ : ℝᵈ) : Function.HasTemperateGrowth (fun y : ℝᵈ => ξ - y) :=
  Function.HasTemperateGrowth.sub (Function.HasTemperateGrowth.const ξ)
    Function.HasTemperateGrowth.id'

lemma norm_le_shift (ξ : ℝᵈ) : ∃ k C, ∀ x : ℝᵈ, ‖x‖ ≤ C * (1 + ‖ξ - x‖) ^ k := by
  refine ⟨1, ‖ξ‖ + 1, fun x => ?_⟩
  rw [pow_one]
  have h1 : ‖x‖ ≤ ‖x - ξ‖ + ‖ξ‖ := by
    calc ‖x‖ = ‖(x - ξ) + ξ‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - ξ‖ + ‖ξ‖ := norm_add_le _ _
  rw [norm_sub_rev] at h1
  nlinarith [norm_nonneg (ξ - x), norm_nonneg ξ, norm_nonneg x]

/-- The Schwartz function `y ↦ ψ (ξ - y)`. -/
noncomputable def schwartzReflect (ξ : ℝᵈ) (ψ : SchwartzMap ℝᵈ ℂ) : SchwartzMap ℝᵈ ℂ :=
  SchwartzMap.compCLM ℂ (temperate_sub ξ) (norm_le_shift ξ) ψ

lemma schwartzReflect_apply (ξ : ℝᵈ) (ψ : SchwartzMap ℝᵈ ℂ) (y : ℝᵈ) :
    schwartzReflect ξ ψ y = ψ (ξ - y) := by
  simp [schwartzReflect, SchwartzMap.compCLM_apply]

/-- A uniform bound for a Schwartz function. -/
lemma exists_nnnorm_bound_schwartz (φ : SchwartzMap ℝᵈ ℂ) :
    ∃ C : ℝ≥0, ∀ x, ‖(φ : ℝᵈ → ℂ) x‖₊ ≤ C := by
  refine ⟨⟨max (((SchwartzMap.seminorm ℂ (0:ℕ) (0:ℕ)) φ : ℝ)) 0, le_max_right _ _⟩, fun x => ?_⟩
  exact NNReal.coe_le_coe.mp ((SchwartzMap.norm_le_seminorm ℂ φ x).trans (le_max_left _ _))

lemma schwartz_memLp_top (φ : SchwartzMap ℝᵈ ℂ) : MemLp (φ : ℝᵈ → ℂ) ⊤ volume := by
  obtain ⟨C, hC⟩ := exists_nnnorm_bound_schwartz φ
  exact memLp_top_of_bound φ.continuous.aestronglyMeasurable (C : ℝ)
    (Filter.Eventually.of_forall fun x => NNReal.coe_le_coe.mpr (hC x))

/-- The Fourier transform of a product of Schwartz functions as a convolution integral. -/
lemma fourier_mul_eq_integral_conv_aux (ψ φ : SchwartzMap ℝᵈ ℂ) (ξ : ℝᵈ) :
    𝓕 (fun x => (ψ : ℝᵈ → ℂ) x * (φ : ℝᵈ → ℂ) x) ξ
      = ∫ y, (𝓕 (ψ : ℝᵈ → ℂ)) y * (𝓕 (φ : ℝᵈ → ℂ)) (ξ - y) := by
  rw [fourier_mul_eq_integral_inner ψ φ ξ]
  have h : ∀ y : ℝᵈ, (𝓕⁻ (φ : ℝᵈ → ℂ)) (y - ξ) = (𝓕 (φ : ℝᵈ → ℂ)) (ξ - y) := by
    intro y
    rw [Real.fourierInv_eq_fourier_neg]
    abel
  have key : (∫ x, (𝓕⁻ (φ : ℝᵈ → ℂ)) x • (𝓕 (ψ : ℝᵈ → ℂ)) (x + ξ))
      = ∫ y, (𝓕⁻ (φ : ℝᵈ → ℂ)) (y - ξ) • (𝓕 (ψ : ℝᵈ → ℂ)) y := by
    have hsub := integral_add_right_eq_self (μ := (volume : Measure ℝᵈ))
      (fun y : ℝᵈ => (𝓕⁻ (φ : ℝᵈ → ℂ)) (y - ξ) • (𝓕 (ψ : ℝᵈ → ℂ)) y) ξ
    simpa only [add_sub_cancel_right] using hsub
  rw [key]
  apply integral_congr_ae
  filter_upwards with y
  rw [h y, smul_eq_mul, mul_comm]

/-- The Fourier transform of a product of Schwartz functions as a convolution integral,
stated with Schwartz Fourier transforms. -/
lemma fourier_mul_eq_integral_conv (ψ φ : SchwartzMap ℝᵈ ℂ) (ξ : ℝᵈ) :
    𝓕 (fun x => (ψ : ℝᵈ → ℂ) x * (φ : ℝᵈ → ℂ) x) ξ
      = ∫ y, (schwartzFourier ψ : ℝᵈ → ℂ) y * (schwartzFourier φ : ℝᵈ → ℂ) (ξ - y) := by
  rw [fourier_mul_eq_integral_conv_aux ψ φ ξ]
  apply integral_congr_ae
  filter_upwards with y
  rw [schwartzFourier_apply ψ y, schwartzFourier_apply φ (ξ - y)]

/-- The `L²` class of `y ↦ star (ψ y)` for a Schwartz function `ψ`. -/
lemma conjMemLp (ψ : SchwartzMap ℝᵈ ℂ) :
    MemLp (fun y : ℝᵈ => star ((ψ : ℝᵈ → ℂ) y)) 2 (volume : Measure ℝᵈ) :=
  (SchwartzMap.memLp ψ 2 volume).congr_norm
    ((Complex.continuous_conj.comp ψ.continuous).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun _ => (Complex.norm_conj _).symm)

noncomputable def conjSchwartz (ψ : SchwartzMap ℝᵈ ℂ) : Lp ℂ 2 (volume : Measure ℝᵈ) :=
  (conjMemLp ψ).toLp _

lemma conjSchwartz_coeFn (ψ : SchwartzMap ℝᵈ ℂ) :
    (conjSchwartz ψ : ℝᵈ → ℂ) =ᵐ[volume] fun y => star ((ψ : ℝᵈ → ℂ) y) :=
  (conjMemLp ψ).coeFn_toLp

/-- The `L²` pairing of a Schwartz function against an `L²` function, as an inner product. -/
lemma integral_mul_eq_inner (A : SchwartzMap ℝᵈ ℂ) (v : Lp ℂ 2 (volume : Measure ℝᵈ)) :
    (∫ y, (v : ℝᵈ → ℂ) y * (A : ℝᵈ → ℂ) y) = inner ℂ (conjSchwartz A) v := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [conjSchwartz_coeFn A] with y hy
  rw [hy, RCLike.inner_apply, starRingEnd_apply, star_star]

/-- The Fourier transform of a Schwartz product as an `L²` inner product. -/
lemma fourier_schwartzMul_eq_inner (ψ φ : SchwartzMap ℝᵈ ℂ) (ξ : ℝᵈ) :
    𝓕 ((schwartzMul ψ φ) : ℝᵈ → ℂ) ξ
      = inner ℂ (conjSchwartz (schwartzReflect ξ (schwartzFourier φ)))
          (𝓕 (ψ.toLp 2) : Lp ℂ 2 (volume : Measure ℝᵈ)) := by
  set v : Lp ℂ 2 (volume : Measure ℝᵈ) :=
    (𝓕 (ψ.toLp 2) : Lp ℂ 2 (volume : Measure ℝᵈ)) with hv
  have hfun : ((schwartzMul ψ φ : SchwartzMap ℝᵈ ℂ) : ℝᵈ → ℂ)
      = fun x => (ψ : ℝᵈ → ℂ) x * (φ : ℝᵈ → ℂ) x :=
    funext fun x => schwartzMul_apply ψ φ x
  have hU : ((v : ℝᵈ → ℂ)) =ᵐ[volume] (schwartzFourier ψ : ℝᵈ → ℂ) := by
    rw [hv]
    have h2 : (𝓕 (ψ.toLp 2) : Lp ℂ 2 (volume : Measure ℝᵈ))
        = ((schwartzFourier ψ).toLp 2 : Lp ℂ 2 (volume : Measure ℝᵈ)) := by
      rw [SchwartzMap.toLp_fourier_eq ψ]
      rfl
    rw [h2]
    exact MemLp.coeFn_toLp (SchwartzMap.memLp (schwartzFourier ψ) 2 volume)
  have hmain : 𝓕 ((schwartzMul ψ φ) : ℝᵈ → ℂ) ξ
      = ∫ y, (schwartzFourier ψ : ℝᵈ → ℂ) y * (schwartzFourier φ : ℝᵈ → ℂ) (ξ - y) := by
    rw [hfun, fourier_mul_eq_integral_conv ψ φ ξ]
  have hstep : (∫ y, (schwartzFourier ψ : ℝᵈ → ℂ) y * (schwartzFourier φ : ℝᵈ → ℂ) (ξ - y))
      = ∫ y, (v : ℝᵈ → ℂ) y * (schwartzReflect ξ (schwartzFourier φ) : ℝᵈ → ℂ) y := by
    apply integral_congr_ae
    filter_upwards [hU] with y hy
    rw [hy, schwartzReflect_apply]
  have hlast : (∫ y, (v : ℝᵈ → ℂ) y * (schwartzReflect ξ (schwartzFourier φ) : ℝᵈ → ℂ) y)
      = inner ℂ (conjSchwartz (schwartzReflect ξ (schwartzFourier φ))) v :=
    integral_mul_eq_inner (schwartzReflect ξ (schwartzFourier φ)) v
  rw [hv] at hlast
  exact hmain.trans (hstep.trans hlast)

/-- There is a sequence of Schwartz functions whose `L²` classes converge to a given `L²`
function. -/
lemma exists_schwartz_tendsto_toLp (f : Lp ℂ 2 (volume : Measure ℝᵈ)) :
    ∃ u : ℕ → SchwartzMap ℝᵈ ℂ,
      Tendsto (fun n : ℕ => ((u n).toLp 2 : Lp ℂ 2 (volume : Measure ℝᵈ))) atTop (𝓝 f) := by
  have hdense : DenseRange (fun g : SchwartzMap ℝᵈ ℂ => ((g.toLp 2) : Lp ℂ 2 volume)) := by
    have h := SchwartzMap.denseRange_toLpCLM (F := ℂ) (E := ℝᵈ) (p := 2) (μ := volume)
      ENNReal.ofNat_ne_top
    have h2 : (⇑(SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝᵈ)) :
        SchwartzMap ℝᵈ ℂ → Lp ℂ 2 (volume : Measure ℝᵈ))
        = fun g => (g.toLp 2 : Lp ℂ 2 (volume : Measure ℝᵈ)) := by
      funext g; rw [SchwartzMap.toLpCLM_apply]
    rwa [h2] at h
  choose u hu using fun n : ℕ =>
    Metric.denseRange_iff.mp hdense f (1 / ((n : ℝ) + 1)) (by positivity)
  refine ⟨u, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (g := fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
    (fun n => dist_nonneg) (fun n => ?_) ?_
  · rw [dist_comm]; exact (hu n).le
  · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Multiplication by a bounded function is bounded on `L²`, quantitatively. -/
lemma norm_toLp_mul_sub_le (φ : SchwartzMap ℝᵈ ℂ) {C : ℝ≥0}
    (hC : ∀ x, ‖(φ : ℝᵈ → ℂ) x‖₊ ≤ C)
    (f : Lp ℂ 2 (volume : Measure ℝᵈ)) {H : Lp ℂ 2 (volume : Measure ℝᵈ)}
    (hH : H =ᵐ[volume] fun x => (f : ℝᵈ → ℂ) x * (φ : ℝᵈ → ℂ) x)
    (ψ : SchwartzMap ℝᵈ ℂ) :
    ‖((schwartzMul ψ φ).toLp 2 : Lp ℂ 2 (volume : Measure ℝᵈ)) - H‖ ≤
      (C : ℝ) * ‖(ψ.toLp 2 : Lp ℂ 2 (volume : Measure ℝᵈ)) - f‖ := by
  set W : Lp ℂ 2 (volume : Measure ℝᵈ) := (schwartzMul ψ φ).toLp 2 with hW
  set v : Lp ℂ 2 (volume : Measure ℝᵈ) := (ψ.toLp 2 : Lp ℂ 2 (volume : Measure ℝᵈ)) - f with hv
  have hφtop : eLpNorm (φ : ℝᵈ → ℂ) ⊤ volume ≤ (C : ℝ≥0∞) := by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_nnnorm_bound (Filter.Eventually.of_forall hC)
  have hsm : AEStronglyMeasurable (fun x : ℝᵈ => (ψ : ℝᵈ → ℂ) x - (f : ℝᵈ → ℂ) x) volume :=
    ψ.continuous.aestronglyMeasurable.sub (Lp.aestronglyMeasurable f)
  have hWcoe : (W : ℝᵈ → ℂ) =ᵐ[volume] (schwartzMul ψ φ : ℝᵈ → ℂ) := by
    rw [hW]; exact MemLp.coeFn_toLp (SchwartzMap.memLp (schwartzMul ψ φ) 2 volume)
  have hvcoe : (v : ℝᵈ → ℂ) =ᵐ[volume] fun x => (ψ : ℝᵈ → ℂ) x - (f : ℝᵈ → ℂ) x := by
    rw [hv]
    filter_upwards [Lp.coeFn_sub (ψ.toLp 2) f,
      MemLp.coeFn_toLp (SchwartzMap.memLp ψ 2 volume)] with x h1 h2
    simp only [SchwartzMap.toLp] at h1 ⊢
    rw [h1, Pi.sub_apply, h2]
  have hLeq : ((W - H : Lp ℂ 2 volume) : ℝᵈ → ℂ)
      =ᵐ[volume] fun x => ((ψ : ℝᵈ → ℂ) x - (f : ℝᵈ → ℂ) x) * (φ : ℝᵈ → ℂ) x := by
    filter_upwards [Lp.coeFn_sub W H, hWcoe, hH] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, schwartzMul_apply]
    ring
  have hmul : eLpNorm (fun x : ℝᵈ => ((ψ : ℝᵈ → ℂ) x - (f : ℝᵈ → ℂ) x) * (φ : ℝᵈ → ℂ) x)
        2 volume
      = eLpNorm ((φ : ℝᵈ → ℂ) • fun x : ℝᵈ => (ψ : ℝᵈ → ℂ) x - (f : ℝᵈ → ℂ) x)
        2 volume := by
    congr 1 with x
    simp only [smul_eq_mul, Pi.mul_apply]
    ring
  have hbdd : eLpNorm ((φ : ℝᵈ → ℂ) •
        fun x : ℝᵈ => (ψ : ℝᵈ → ℂ) x - (f : ℝᵈ → ℂ) x) 2 volume
      ≤ (C : ℝ≥0∞) *
        eLpNorm (fun x : ℝᵈ => (ψ : ℝᵈ → ℂ) x - (f : ℝᵈ → ℂ) x) 2 volume := by
    calc eLpNorm ((φ : ℝᵈ → ℂ) •
          fun x : ℝᵈ => (ψ : ℝᵈ → ℂ) x - (f : ℝᵈ → ℂ) x) 2 volume
        ≤ eLpNorm (φ : ℝᵈ → ℂ) ⊤ volume *
            eLpNorm (fun x : ℝᵈ => (ψ : ℝᵈ → ℂ) x - (f : ℝᵈ → ℂ) x) 2 volume :=
          eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2 hsm (φ : ℝᵈ → ℂ)
      _ = eLpNorm (fun x : ℝᵈ => (ψ : ℝᵈ → ℂ) x - (f : ℝᵈ → ℂ) x) 2 volume *
            eLpNorm (φ : ℝᵈ → ℂ) ⊤ volume := mul_comm _ _
      _ ≤ eLpNorm (fun x : ℝᵈ => (ψ : ℝᵈ → ℂ) x - (f : ℝᵈ → ℂ) x) 2 volume *
            (C : ℝ≥0∞) := mul_le_mul_right hφtop _
      _ = (C : ℝ≥0∞) *
            eLpNorm (fun x : ℝᵈ => (ψ : ℝᵈ → ℂ) x - (f : ℝᵈ → ℂ) x) 2 volume :=
          mul_comm _ _
  have hkey : eLpNorm (((W - H : Lp ℂ 2 volume)) : ℝᵈ → ℂ) 2 volume
      ≤ (C : ℝ≥0∞) * ‖v‖ₑ := by
    rw [Lp.enorm_def, eLpNorm_congr_ae hvcoe, eLpNorm_congr_ae hLeq, hmul]
    exact hbdd
  have h1 : ‖W - H‖ = (eLpNorm (((W - H : Lp ℂ 2 volume)) : ℝᵈ → ℂ) 2 volume).toReal :=
    Lp.norm_def (W - H)
  have h2 : (eLpNorm (((W - H : Lp ℂ 2 volume)) : ℝᵈ → ℂ) 2 volume).toReal
      ≤ ((C : ℝ≥0∞) * ‖v‖ₑ).toReal :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top enorm_ne_top) hkey
  have h3 : ((C : ℝ≥0∞) * ‖v‖ₑ).toReal = (C : ℝ) * ‖v‖ := by
    rw [ENNReal.toReal_mul, enorm_eq_nnnorm]
    simp
  rw [h1]
  exact h2.trans_eq h3

/-- The `L²` representative of the Fourier transform of `ψ * φ` is, a.e. in the frequency
variable, the `L²` inner product against the reflected Schwartz Fourier transform of `φ`. -/
lemma ae_toLp_fourier_eq_inner (φ : SchwartzMap ℝᵈ ℂ) (u : ℕ → SchwartzMap ℝᵈ ℂ) :
    ∀ᵐ ξ ∂(volume : Measure ℝᵈ), ∀ n : ℕ,
      (((𝓕 ((schwartzMul (u n) φ).toLp 2) : Lp ℂ 2 (volume : Measure ℝᵈ))) : ℝᵈ → ℂ) ξ
        = inner ℂ (conjSchwartz (schwartzReflect ξ (schwartzFourier φ)))
            (𝓕 ((u n).toLp 2) : Lp ℂ 2 (volume : Measure ℝᵈ)) := by
  rw [ae_all_iff]
  intro n
  have h2 : (𝓕 ((schwartzMul (u n) φ).toLp 2) : Lp ℂ 2 (volume : Measure ℝᵈ))
      = ((schwartzFourier (schwartzMul (u n) φ)).toLp 2 : Lp ℂ 2 (volume : Measure ℝᵈ)) := by
    rw [SchwartzMap.toLp_fourier_eq (schwartzMul (u n) φ)]
    rfl
  have h1 : (((schwartzFourier (schwartzMul (u n) φ)).toLp 2 : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ)
      =ᵐ[volume] (schwartzFourier (schwartzMul (u n) φ) : ℝᵈ → ℂ) :=
    MemLp.coeFn_toLp (SchwartzMap.memLp (schwartzFourier (schwartzMul (u n) φ)) 2 volume)
  filter_upwards [h1, Filter.Eventually.of_forall (fourier_schwartzMul_eq_inner (u n) φ)]
    with ξ h1ξ h2'
  rw [h2, h1ξ, schwartzFourier_apply (schwartzMul (u n) φ) ξ, h2']

/-- The limiting inner product vanishes outside the sum of the two support sets. -/
lemma inner_fourier_eq_zero (f : Lp ℂ 2 (volume : Measure ℝᵈ)) (φ : SchwartzMap ℝᵈ ℂ)
    {K K' : Set ℝᵈ}
    (hK : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), ξ ∉ K →
      ((FourierTransform.fourier f :
        Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ = 0)
    (hK' : ∀ ξ, ξ ∉ K' → (FourierTransform.fourier φ : SchwartzMap ℝᵈ ℂ) ξ = 0)
    {ξ : ℝᵈ} (hcond : ∀ a ∈ K, ∀ b ∈ K', ξ ≠ a + b) :
    inner ℂ (conjSchwartz (schwartzReflect ξ (schwartzFourier φ)))
      (𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) = 0 := by
  rw [← integral_mul_eq_inner (schwartzReflect ξ (schwartzFourier φ)) (𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ))]
  have hz : ∀ᵐ y ∂(volume : Measure ℝᵈ), ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) y *
      (schwartzReflect ξ (schwartzFourier φ) : ℝᵈ → ℂ) y = 0 := by
    filter_upwards [hK] with y hy
    by_cases hyK : y ∈ K
    · have hb : (schwartzReflect ξ (schwartzFourier φ) : ℝᵈ → ℂ) y = 0 := by
        rw [schwartzReflect_apply]
        exact hK' (ξ - y) (fun hmem => hcond y hyK (ξ - y) hmem (by abel))
      rw [hb, mul_zero]
    · rw [hy hyK, zero_mul]
  rw [integral_congr_ae hz]
  simp

theorem fourier_mul_support_Lp_aux
    (f : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝᵈ))
    (φ : SchwartzMap ℝᵈ ℂ) {K K' : Set ℝᵈ}
    (hK : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝᵈ), ξ ∉ K →
      ((FourierTransform.fourier f :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝᵈ)) : ℝᵈ → ℂ) ξ = 0)
    (hK' : ∀ ξ, ξ ∉ K' → FourierTransform.fourier φ ξ = 0) :
    ∃ h : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝᵈ),
      h =ᵐ[MeasureTheory.volume] (fun x : ℝᵈ =>
        (f : ℝᵈ → ℂ) x * (φ : ℝᵈ → ℂ) x) ∧
      (∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝᵈ),
        (∀ a ∈ K, ∀ b ∈ K', ξ ≠ a + b) →
        ((FourierTransform.fourier h :
          MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝᵈ)) : ℝᵈ → ℂ) ξ = 0) := by
  have hφmem : MemLp (φ : ℝᵈ → ℂ) ⊤ volume := schwartz_memLp_top φ
  have hmem : MemLp (fun x : ℝᵈ => (f : ℝᵈ → ℂ) x * (φ : ℝᵈ → ℂ) x) 2 volume := by
    have h : MemLp (fun x : ℝᵈ => (φ : ℝᵈ → ℂ) x * (f : ℝᵈ → ℂ) x) 2 volume :=
      MemLp.mul (p := ⊤) (q := 2) (r := 2) (Lp.memLp f) hφmem
    have h2 : (fun x : ℝᵈ => (φ : ℝᵈ → ℂ) x * (f : ℝᵈ → ℂ) x)
        = fun x : ℝᵈ => (f : ℝᵈ → ℂ) x * (φ : ℝᵈ → ℂ) x := by
      funext x; exact mul_comm _ _
    rwa [h2] at h
  set H : Lp ℂ 2 (volume : Measure ℝᵈ) :=
    hmem.toLp (fun x : ℝᵈ => (f : ℝᵈ → ℂ) x * (φ : ℝᵈ → ℂ) x) with hHdef
  have hHeq : H =ᵐ[volume] (fun x : ℝᵈ => (f : ℝᵈ → ℂ) x * (φ : ℝᵈ → ℂ) x) := by
    rw [hHdef]; exact hmem.coeFn_toLp
  obtain ⟨C, hC⟩ := exists_nnnorm_bound_schwartz φ
  refine ⟨H, hHeq, ?_⟩
  obtain ⟨u, htendS⟩ := exists_schwartz_tendsto_toLp f
  have htendH : Tendsto (fun n : ℕ => ((schwartzMul (u n) φ).toLp 2 : Lp ℂ 2 volume))
      atTop (𝓝 H) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _)
      (fun n => norm_toLp_mul_sub_le φ hC f hHeq (u n)) ?_
    have h1 : Tendsto (fun n : ℕ => (((u n).toLp 2 : Lp ℂ 2 volume)) - f) atTop
        (𝓝 (0 : Lp ℂ 2 volume)) := by
      simpa using htendS.sub_const f
    have h2 : Tendsto (fun n : ℕ => ‖((u n).toLp 2 : Lp ℂ 2 volume) - f‖) atTop (𝓝 0) := by
      simpa using h1.norm
    simpa using h2.const_mul (C : ℝ)
  have htendF : Tendsto (fun n : ℕ => (𝓕 ((schwartzMul (u n) φ).toLp 2) : Lp ℂ 2 volume))
      atTop (𝓝 (𝓕 H : Lp ℂ 2 volume)) :=
    ((Lp.fourierTransformₗᵢ ℝᵈ ℂ).continuous.tendsto H).comp htendH
  have htendU : Tendsto (fun n : ℕ => (𝓕 ((u n).toLp 2) : Lp ℂ 2 volume))
      atTop (𝓝 (𝓕 f : Lp ℂ 2 volume)) :=
    ((Lp.fourierTransformₗᵢ ℝᵈ ℂ).continuous.tendsto f).comp htendS
  obtain ⟨ns, hnsmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp htendF).exists_seq_tendsto_ae
  have hconv : ∀ ξ : ℝᵈ, (∀ a ∈ K, ∀ b ∈ K', ξ ≠ a + b) →
      Tendsto (fun n : ℕ => inner ℂ (conjSchwartz (schwartzReflect ξ (schwartzFourier φ)))
        (𝓕 ((u n).toLp 2) : Lp ℂ 2 volume)) atTop (𝓝 0) := by
    intro ξ hcond
    have hc : Tendsto (fun n : ℕ => inner ℂ (conjSchwartz (schwartzReflect ξ (schwartzFourier φ)))
        (𝓕 ((u n).toLp 2) : Lp ℂ 2 volume)) atTop
        (𝓝 (inner ℂ (conjSchwartz (schwartzReflect ξ (schwartzFourier φ)))
          (𝓕 f : Lp ℂ 2 volume))) :=
      (((continuous_const : Continuous fun _ : Lp ℂ 2 volume =>
          conjSchwartz (schwartzReflect ξ (schwartzFourier φ)))).inner
        continuous_id).tendsto (𝓕 f : Lp ℂ 2 volume) |>.comp htendU
    rwa [inner_fourier_eq_zero f φ hK hK' hcond] at hc
  filter_upwards [hns, ae_toLp_fourier_eq_inner φ u] with ξ hnsξ hFGξ hcond
  have hseq : (fun i : ℕ => (((𝓕 ((schwartzMul (u (ns i)) φ).toLp 2) : Lp ℂ 2 volume)) :
        ℝᵈ → ℂ) ξ)
      = fun i : ℕ => inner ℂ (conjSchwartz (schwartzReflect ξ (schwartzFourier φ)))
          (𝓕 ((u (ns i)).toLp 2) : Lp ℂ 2 volume) :=
    funext fun i => hFGξ (ns i)
  rw [hseq] at hnsξ
  exact tendsto_nhds_unique hnsξ ((hconv ξ hcond).comp hnsmono.tendsto_atTop)

/-- **Fractal uncertainty: the product of an `L²` function and a Schwartz function.**

If the Fourier transform of `f ∈ L²(ℝᵈ)` vanishes outside `K` and the Fourier transform of the
Schwartz function `φ` vanishes outside `K'`, then the `L²` function `f * φ` has Fourier transform
vanishing outside `K + K'`. -/
theorem fourier_mul_support_Lp {d : ℕ}
    (f : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) {K K' : Set (EuclideanSpace ℝ (Fin d))}
    (hK : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))), ξ ∉ K →
      ((FourierTransform.fourier f :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
        EuclideanSpace ℝ (Fin d) → ℂ) ξ = 0)
    (hK' : ∀ ξ, ξ ∉ K' → FourierTransform.fourier φ ξ = 0) :
    ∃ h : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      h =ᵐ[MeasureTheory.volume] (fun x : EuclideanSpace ℝ (Fin d) =>
        (f : EuclideanSpace ℝ (Fin d) → ℂ) x * (φ : EuclideanSpace ℝ (Fin d) → ℂ) x) ∧
      (∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
        (∀ a ∈ K, ∀ b ∈ K', ξ ≠ a + b) →
        ((FourierTransform.fourier h :
          MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
          EuclideanSpace ℝ (Fin d) → ℂ) ξ = 0) :=
  fourier_mul_support_Lp_aux f φ hK hK'

end Commons.Analysis.Fourier
