import Mathlib
import Submission.Work.Analysis.CzShift.fourier_czOp
import Submission.Port.Aesm

/-!
# The `L²` bound for `czOp` from a bound on its Fourier symbol

This file proves `Work.Analysis.CzShift.l2_bound_of_fourier_symbol`: the `p = 2` case of the
shifted Calderón–Zygmund theorem of Appendix B of Krause–Mirek–Tao, via Plancherel's theorem.

The proof has three ingredients, all of them classical analysis:

* `Work.Analysis.CzShift.fourier_czOp` (imported): the Fourier transform of
  `czOp D K ε f = ∑_{i ∈ D} ε i • (K i ⋆ f)` is the multiplier
  `ξ ↦ (∑_{i ∈ D} ε i * 𝓕(K i) ξ) * 𝓕f ξ` (Mathlib's convolution theorem
  `Real.fourier_smul_convolution_eq`, valid for *integrable* functions);
* Plancherel for `L¹ ∩ L²` functions: for integrable `h ∈ L²`, the pointwise Fourier transform
  `𝓕 h` is a.e. equal to the `L²`-level Fourier transform `𝓕 (h.toLp 2)`.  Mathlib only has this
  for Schwartz functions (`SchwartzMap.toLp_fourier_eq`), together with the derived identity at the
  level of tempered distributions (`Lp.fourier_toTemperedDistribution_eq`);
* the elementary bound `eLpNorm (m • g) 2 ≤ ofReal Cm * eLpNorm g 2` for `‖m‖ ≤ Cm`.

Plancherel for `L¹ ∩ L²` is proved through the tempered-distribution picture: for `h ∈ L¹` the
Fourier transform of the regular tempered distribution of `h` is the regular distribution of
`𝓕 h` — an immediate consequence of the Fubini/self-adjointness identity
`VectorFourier.integral_bilin_fourierIntegral_eq_flip` for integrable functions.  The a.e. identity
is then extracted with the fundamental lemma of the calculus of variations
(`ae_eq_of_integral_contDiff_smul_eq`).
-/

namespace Work.Analysis.CzShift

open MeasureTheory Finset
open scoped FourierTransform RealInnerProductSpace ContDiff

set_option autoImplicit false

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Fubini / self-adjointness of the Fourier transform for `L¹` functions -/

/-- The bilinear form `(innerₗ ℝ).flip` gives the same Fourier integral as `innerₗ ℝ`, since the
inner product on `ℝ` is symmetric. -/
lemma fourierIntegral_inner_flip (f : ℝ → H) :
    VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ).flip f
      = VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) f := by
  ext x
  simp only [VectorFourier.fourierIntegral, LinearMap.flip_apply, innerₗ_apply_apply]
  congr 1 with v
  rw [real_inner_comm x v]

/-- The self-adjointness (Fubini) identity for the Fourier transform, for an integrable
`H`-valued function `f` and an integrable scalar function `g`:
`∫ 𝓕 g • f = ∫ g • 𝓕 f`.  It is the Fubini theorem for the Fourier integral,
`VectorFourier.integral_fourierIntegral_smul_eq_flip`, together with the symmetry of the inner
product on `ℝ`. -/
theorem integral_smul_fourier_eq_of_integrable {f : ℝ → H} {g : ℝ → ℂ}
    (hf : MeasureTheory.Integrable f) (hg : MeasureTheory.Integrable g) :
    ∫ x, FourierTransform.fourier g x • f x = ∫ ξ, g ξ • FourierTransform.fourier f ξ := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (𝕜 := ℝ) (e := Real.fourierChar) (μ := volume) (ν := volume) (L := innerₗ ℝ)
    (f := g) (g := f) Real.continuous_fourierChar continuous_inner hg hf
  rw [fourierIntegral_inner_flip f] at h
  exact h

/-! ## Plancherel for `L¹ ∩ L²` functions -/

/-- The distributional identity `𝓕 (T_f) = T_{𝓕 f}` for `f ∈ L¹`, tested against a Schwartz
function `G`: the pairing of the `L²`-Fourier transform of `f` with `G` equals the pairing of the
pointwise Fourier transform `𝓕 f` with `G`. -/
lemma lpFourier_test {f : ℝ → H} (hf : MeasureTheory.Integrable f)
    (hf2 : MeasureTheory.MemLp f 2 MeasureTheory.volume) (G : SchwartzMap ℝ ℂ) :
    ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ H (MeasureTheory.MemLp.toLp f hf2)
        : Lp (α := ℝ) H 2 MeasureTheory.volume) : TemperedDistribution ℝ H) G
      = ∫ x, G x • FourierTransform.fourier f x := by
  have h4 : ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ H (MeasureTheory.MemLp.toLp f hf2)
        : Lp (α := ℝ) H 2 MeasureTheory.volume) : TemperedDistribution ℝ H) G
      = (MeasureTheory.Lp.toTemperedDistribution
          (FourierTransform.fourier (MeasureTheory.MemLp.toLp f hf2))) G := rfl
  rw [h4]
  rw [← MeasureTheory.Lp.fourier_toTemperedDistribution_eq (MeasureTheory.MemLp.toLp f hf2)]
  rw [TemperedDistribution.fourier_apply]
  rw [MeasureTheory.Lp.toTemperedDistribution_apply]
  have h5 : ∫ x, FourierTransform.fourier G x • (MeasureTheory.MemLp.toLp f hf2 : ℝ → H) x
      = ∫ x, FourierTransform.fourier G x • f x := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.MemLp.coeFn_toLp hf2] with x hx
    rw [hx]
  have h6 : ∫ x, (FourierTransform.fourier G) x • f x
      = ∫ x, FourierTransform.fourier (⇑G) x • f x := by
    simp only [SchwartzMap.fourier_coe]
  rw [h5, h6, integral_smul_fourier_eq_of_integrable hf G.integrable]

/-- **Plancherel's theorem for `L¹ ∩ L²` functions (Hilbert-space valued).**  For an integrable
`L²` function `f`, the pointwise Fourier transform `𝓕 f` is a.e. equal to the `L²`-level Fourier
transform `𝓕 (f.toLp 2)`. -/
theorem ae_fourier_eq_fourier_toLp {f : ℝ → H} (hf : MeasureTheory.Integrable f)
    (hf2 : MeasureTheory.MemLp f 2 MeasureTheory.volume) :
    FourierTransform.fourier f =ᵐ[MeasureTheory.volume]
      ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ H (MeasureTheory.MemLp.toLp f hf2)) : ℝ → H) := by
  have hli : LocallyIntegrable (FourierTransform.fourier f) MeasureTheory.volume := by
    have hc : Continuous (FourierTransform.fourier f) :=
      VectorFourier.fourierIntegral_continuous (𝕜 := ℝ) (e := Real.fourierChar)
        (μ := volume) (L := innerₗ ℝ) (E := H) Real.continuous_fourierChar continuous_inner hf
    exact hc.locallyIntegrable
  have hli' : LocallyIntegrable
      ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ H (MeasureTheory.MemLp.toLp f hf2)
        : Lp (α := ℝ) H 2 MeasureTheory.volume) : ℝ → H) MeasureTheory.volume :=
    (MeasureTheory.Lp.memLp _).locallyIntegrable (by norm_num)
  refine ae_eq_of_integral_contDiff_smul_eq hli hli' (fun g hg hgs => ?_)
  have hgc : HasCompactSupport (Complex.ofRealCLM ∘ g) :=
    hgs.comp_left (map_zero Complex.ofRealCLM)
  have hgd : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  have hG : ∀ x, ((hgc.toSchwartzMap hgd : SchwartzMap ℝ ℂ)) x = (g x : ℂ) := fun x => rfl
  have hkey := lpFourier_test hf hf2 (hgc.toSchwartzMap hgd)
  have h1 : ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ H (MeasureTheory.MemLp.toLp f hf2)
        : Lp (α := ℝ) H 2 MeasureTheory.volume) : TemperedDistribution ℝ H)
        (hgc.toSchwartzMap hgd)
      = ∫ x, ((hgc.toSchwartzMap hgd : SchwartzMap ℝ ℂ) x)
          • ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ H (MeasureTheory.MemLp.toLp f hf2)
              : Lp (α := ℝ) H 2 MeasureTheory.volume) : ℝ → H) x :=
    MeasureTheory.Lp.toTemperedDistribution_apply _ _
  rw [h1] at hkey
  simp only [hG, Complex.coe_smul] at hkey
  exact hkey.symm

/-! ## Consequences of Plancherel and the multiplication bound -/

/-- `𝓕 f ∈ L²` for `f ∈ L¹ ∩ L²`, by Plancherel. -/
theorem memLp_fourier_of_memLp {f : ℝ → H} (hf : MeasureTheory.Integrable f)
    (hf2 : MeasureTheory.MemLp f 2 MeasureTheory.volume) :
    MeasureTheory.MemLp (FourierTransform.fourier f) 2 MeasureTheory.volume :=
  MeasureTheory.MemLp.ae_eq (ae_fourier_eq_fourier_toLp hf hf2).symm
    (MeasureTheory.Lp.memLp _)

/-- Plancherel's identity for `f ∈ L¹ ∩ L²`: `‖𝓕 f‖₂ = ‖f‖₂`. -/
theorem eLpNorm_fourier_eq_of_memLp {f : ℝ → H} (hf : MeasureTheory.Integrable f)
    (hf2 : MeasureTheory.MemLp f 2 MeasureTheory.volume) :
    MeasureTheory.eLpNorm (FourierTransform.fourier f) 2 MeasureTheory.volume
      = MeasureTheory.eLpNorm f 2 MeasureTheory.volume := by
  calc MeasureTheory.eLpNorm (FourierTransform.fourier f) 2 MeasureTheory.volume
      = MeasureTheory.eLpNorm
          ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ H (MeasureTheory.MemLp.toLp f hf2)
            : Lp (α := ℝ) H 2 MeasureTheory.volume) : ℝ → H) 2 MeasureTheory.volume :=
        MeasureTheory.eLpNorm_congr_ae (ae_fourier_eq_fourier_toLp hf hf2)
    _ = ‖(MeasureTheory.Lp.fourierTransformₗᵢ ℝ H (MeasureTheory.MemLp.toLp f hf2)
            : Lp (α := ℝ) H 2 MeasureTheory.volume)‖ₑ :=
        (MeasureTheory.Lp.enorm_def _).symm
    _ = ‖(MeasureTheory.MemLp.toLp f hf2 : Lp (α := ℝ) H 2 MeasureTheory.volume)‖ₑ :=
        LinearIsometryEquiv.enorm_map _ _
    _ = MeasureTheory.eLpNorm
          ((MeasureTheory.MemLp.toLp f hf2 : Lp (α := ℝ) H 2 MeasureTheory.volume) : ℝ → H)
          2 MeasureTheory.volume :=
        MeasureTheory.Lp.enorm_def _
    _ = MeasureTheory.eLpNorm f 2 MeasureTheory.volume :=
        MeasureTheory.eLpNorm_congr_ae (MeasureTheory.MemLp.coeFn_toLp hf2)

/-- **Multiplication by a bounded function.**  If `‖m‖ ≤ Cm` everywhere and `g ∈ L²`, then
`m • g ∈ L²` with `‖m • g‖₂ ≤ Cm ‖g‖₂`. -/
theorem eLpNorm_smul_le {m : ℝ → ℂ} {g : ℝ → H} {Cm : ℝ} (hCm : 0 ≤ Cm)
    (hm : AEMeasurable m MeasureTheory.volume)
    (hmb : ∀ ξ, ‖m ξ‖ ≤ Cm) (hg : MeasureTheory.MemLp g 2 MeasureTheory.volume) :
    MeasureTheory.MemLp (fun ξ => m ξ • g ξ) 2 MeasureTheory.volume ∧
      MeasureTheory.eLpNorm (fun ξ => m ξ • g ξ) 2 MeasureTheory.volume
        ≤ ENNReal.ofReal Cm * MeasureTheory.eLpNorm g 2 MeasureTheory.volume := by
  have hpt : ∀ ξ : ℝ, ‖m ξ • g ξ‖ ≤ ‖(Cm : ℂ) • g ξ‖ := by
    intro ξ
    rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hCm]
    exact mul_le_mul_of_nonneg_right (hmb ξ) (norm_nonneg _)
  constructor
  · refine MeasureTheory.MemLp.of_le (p := 2) (hg.const_smul (Cm : ℂ)) ?_ ?_
    · exact hm.aestronglyMeasurable.smul hg.aestronglyMeasurable
    · filter_upwards with ξ using hpt ξ
  · calc MeasureTheory.eLpNorm (fun ξ => m ξ • g ξ) 2 MeasureTheory.volume
        ≤ MeasureTheory.eLpNorm (fun ξ => (Cm : ℂ) • g ξ) 2 MeasureTheory.volume :=
          eLpNorm_mono (hf := by pw_aesm) hpt
      _ = ‖(Cm : ℂ)‖ₑ * MeasureTheory.eLpNorm g 2 MeasureTheory.volume :=
          MeasureTheory.eLpNorm_const_smul (Cm : ℂ) g 2 volume
      _ = ENNReal.ofReal Cm * MeasureTheory.eLpNorm g 2 MeasureTheory.volume := by
          rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hCm]

/-! ## The reverse direction of Plancherel for `L¹` functions -/

/-- **The inverse direction of Plancherel.**  If `h ∈ L¹` has `𝓕 h ∈ L²`, then `h ∈ L²` and
`‖h‖₂ = ‖𝓕 h‖₂`.  Equivalently, `h` is a.e. the inverse `L²`-Fourier transform of `𝓕 h`; the
latter is proved by testing the distributional identity `𝓕 (T_h) = T_{𝓕 h}` against smooth
compactly supported functions and applying the fundamental lemma of the calculus of variations. -/
theorem memLp_of_memLp_fourier {h : ℝ → H} (hh : MeasureTheory.Integrable h)
    (hF : MeasureTheory.MemLp (FourierTransform.fourier h) 2 MeasureTheory.volume) :
    MeasureTheory.MemLp h 2 MeasureTheory.volume ∧
      MeasureTheory.eLpNorm h 2 MeasureTheory.volume
        = MeasureTheory.eLpNorm (FourierTransform.fourier h) 2 MeasureTheory.volume := by
  set V : Lp (α := ℝ) H 2 MeasureTheory.volume :=
    MeasureTheory.MemLp.toLp (FourierTransform.fourier h) hF with hV
  set w : Lp (α := ℝ) H 2 MeasureTheory.volume := FourierTransform.fourierInv V with hw
  have hVae : (V : ℝ → H) =ᵐ[MeasureTheory.volume] FourierTransform.fourier h := by
    rw [hV]
    exact MeasureTheory.MemLp.coeFn_toLp hF
  have h1mem : MeasureTheory.MemLp h 1 MeasureTheory.volume :=
    memLp_one_iff_integrable.mpr hh
  -- the two distributional Fourier transforms
  have hTh : FourierTransform.fourier
        (((MeasureTheory.MemLp.toLp h h1mem : Lp (α := ℝ) H 1 MeasureTheory.volume))
          : TemperedDistribution ℝ H)
      = (V : TemperedDistribution ℝ H) := by
    ext G
    rw [TemperedDistribution.fourier_apply, MeasureTheory.Lp.toTemperedDistribution_apply,
      MeasureTheory.Lp.toTemperedDistribution_apply]
    have h6 : ∫ x, (FourierTransform.fourier G) x
          • (MeasureTheory.MemLp.toLp h h1mem : ℝ → H) x
        = ∫ x, FourierTransform.fourier (⇑G) x
          • (MeasureTheory.MemLp.toLp h h1mem : ℝ → H) x := by
      simp only [SchwartzMap.fourier_coe]
    have h7 : ∫ x, FourierTransform.fourier (⇑G) x
          • (MeasureTheory.MemLp.toLp h h1mem : ℝ → H) x
        = ∫ x, FourierTransform.fourier (⇑G) x • h x := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.MemLp.coeFn_toLp h1mem] with x hx
      rw [hx]
    have h8 : ∫ x, G x • (V : ℝ → H) x = ∫ x, G x • FourierTransform.fourier h x := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hVae] with x hx
      rw [hx]
    rw [h6, h7, integral_smul_fourier_eq_of_integrable hh G.integrable, ← h8]
  have hTw : FourierTransform.fourier ((w : Lp (α := ℝ) H 2 MeasureTheory.volume)
        : TemperedDistribution ℝ H) = (V : TemperedDistribution ℝ H) := by
    rw [hw, MeasureTheory.Lp.fourier_toTemperedDistribution_eq,
      FourierTransform.fourier_fourierInv_eq]
  have hpair : ∀ x : TemperedDistribution ℝ H, 𝓕⁻ (𝓕 x) = x := fun x =>
    FourierPair.fourierInv_fourier_eq
      (E := TemperedDistribution ℝ H) (F := TemperedDistribution ℝ H) x
  have hdist : ((MeasureTheory.MemLp.toLp h h1mem : Lp (α := ℝ) H 1 MeasureTheory.volume)
        : TemperedDistribution ℝ H) = (w : TemperedDistribution ℝ H) := by
    rw [← hpair
        (((MeasureTheory.MemLp.toLp h h1mem : Lp (α := ℝ) H 1 MeasureTheory.volume))
          : TemperedDistribution ℝ H)]
    rw [hTh]
    rw [← hpair (w : TemperedDistribution ℝ H)]
    rw [hTw]
  -- the a.e. identity
  have hli1 : LocallyIntegrable h MeasureTheory.volume := hh.locallyIntegrable
  have hli2 : LocallyIntegrable ((w : Lp (α := ℝ) H 2 MeasureTheory.volume) : ℝ → H)
      MeasureTheory.volume :=
    (MeasureTheory.Lp.memLp w).locallyIntegrable (by norm_num)
  have hae : h =ᵐ[MeasureTheory.volume]
      ((w : Lp (α := ℝ) H 2 MeasureTheory.volume) : ℝ → H) := by
    refine ae_eq_of_integral_contDiff_smul_eq hli1 hli2 (fun g hg hgs => ?_)
    have hgc : HasCompactSupport (Complex.ofRealCLM ∘ g) :=
      hgs.comp_left (map_zero Complex.ofRealCLM)
    have hgd : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
    have hG : ∀ x, ((hgc.toSchwartzMap hgd : SchwartzMap ℝ ℂ)) x = (g x : ℂ) := fun x => rfl
    have hkey := congrArg (fun T : TemperedDistribution ℝ H => T (hgc.toSchwartzMap hgd)) hdist
    have h1 : (((MeasureTheory.MemLp.toLp h h1mem : Lp (α := ℝ) H 1 MeasureTheory.volume))
          : TemperedDistribution ℝ H) (hgc.toSchwartzMap hgd)
        = ∫ x, ((hgc.toSchwartzMap hgd : SchwartzMap ℝ ℂ) x) • h x := by
      rw [MeasureTheory.Lp.toTemperedDistribution_apply]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.MemLp.coeFn_toLp h1mem] with x hx
      rw [hx]
    have h2 : ((w : Lp (α := ℝ) H 2 MeasureTheory.volume) : TemperedDistribution ℝ H)
          (hgc.toSchwartzMap hgd)
        = ∫ x, ((hgc.toSchwartzMap hgd : SchwartzMap ℝ ℂ) x)
            • (w : ℝ → H) x :=
      MeasureTheory.Lp.toTemperedDistribution_apply w _
    rw [h1, h2] at hkey
    simp only [hG, Complex.coe_smul] at hkey
    exact hkey
  refine ⟨MeasureTheory.MemLp.ae_eq hae.symm (MeasureTheory.Lp.memLp w), ?_⟩
  calc MeasureTheory.eLpNorm h 2 MeasureTheory.volume
      = MeasureTheory.eLpNorm ((w : Lp (α := ℝ) H 2 MeasureTheory.volume) : ℝ → H)
          2 MeasureTheory.volume :=
        MeasureTheory.eLpNorm_congr_ae hae
    _ = ‖w‖ₑ := (MeasureTheory.Lp.enorm_def w).symm
    _ = ‖V‖ₑ := by
        rw [hw]
        exact LinearIsometryEquiv.enorm_map (MeasureTheory.Lp.fourierTransformₗᵢ ℝ H).symm V
    _ = MeasureTheory.eLpNorm ((V : Lp (α := ℝ) H 2 MeasureTheory.volume) : ℝ → H)
          2 MeasureTheory.volume :=
        MeasureTheory.Lp.enorm_def V
    _ = MeasureTheory.eLpNorm (FourierTransform.fourier h) 2 MeasureTheory.volume :=
        MeasureTheory.eLpNorm_congr_ae hVae

/-! ## The main theorem -/

/-- The `L²` bound for a convolution operator, from a bound on the sup norm of its Fourier
symbol (= the Fourier transform of the summed kernel).  This is the `p = 2` case of Theorem
`cz-shift`, via Plancherel's theorem.

Available in Mathlib: `MeasureTheory.fourier_smul_convolution_eq` (Fourier transform of a
scalar-times-vector convolution) and `MeasureTheory.Lp.norm_fourier_eq` (Plancherel for
Hilbert-space-valued `L²`); `SchwartzMap.denseRange_toLpCLM` for the density of Schwartz
functions in `L²`. -/
theorem l2_bound_of_fourier_symbol {ι : Type*} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (D : Finset ι) (K : ι → ℝ → ℂ) (ε : ι → ℂ)
    (Cm : ℝ) (hCm : 0 ≤ Cm)
    (hKint : ∀ i ∈ D, MeasureTheory.Integrable (K i))
    (hKbdd : ∀ i ∈ D, ∃ C : ℝ, ∀ x, ‖K i x‖ ≤ C)
    (hsym : ∀ ξ : ℝ, ‖∑ i ∈ D, ε i * FourierTransform.fourier (K i) ξ‖ ≤ Cm) :
    ∀ f : ℝ → H, MeasureTheory.Integrable f → MeasureTheory.MemLp f 2 MeasureTheory.volume →
      MeasureTheory.eLpNorm (czOp D K ε f) 2 MeasureTheory.volume
        ≤ ENNReal.ofReal Cm * MeasureTheory.eLpNorm f 2 MeasureTheory.volume := by
  intro f hf hf2
  -- the Fourier symbol of `czOp D K ε`
  set m : ℝ → ℂ := fun ξ => ∑ i ∈ D, ε i * FourierTransform.fourier (K i) ξ with hm
  have hsym' : ∀ ξ : ℝ, ‖m ξ‖ ≤ Cm := fun ξ => by simpa only [hm] using hsym ξ
  have hmae : AEMeasurable m MeasureTheory.volume := by
    have hcont : Continuous m := by
      rw [hm]
      refine continuous_finsetSum _ (fun i hi => ?_)
      have hci : Continuous (FourierTransform.fourier (K i) : ℝ → ℂ) :=
        VectorFourier.fourierIntegral_continuous (𝕜 := ℝ) (e := Real.fourierChar)
          (μ := volume) (L := innerₗ ℝ) (E := ℂ) Real.continuous_fourierChar continuous_inner
          (hKint i hi)
      exact continuous_const.mul hci
    exact hcont.aemeasurable
  -- the Fourier transform of `czOp D K ε f` is the multiplier `m`
  have hFourier : FourierTransform.fourier (czOp D K ε f) = fun ξ => m ξ • 𝓕 f ξ := by
    simpa only [hm] using fourier_czOp D K ε f hKint hf
  -- `czOp D K ε f` is integrable (a finite sum of `L¹ ⋆ L¹` convolutions)
  have hInt : MeasureTheory.Integrable (czOp D K ε f) := by
    have hsplit : czOp D K ε f = ∑ i ∈ D, ε i • czOpOne (K i) f := by
      funext x
      simp only [czOp, czOpOne, Finset.sum_apply, Pi.smul_apply]
    rw [hsplit]
    exact integrable_sum_smul D ε (fun i => czOpOne (K i) f)
      (fun i hi => integrable_czOpOne (K i) f (hKint i hi) hf)
  -- Plancherel for `f` and the multiplication bound
  have hboundF : MeasureTheory.eLpNorm (𝓕 f) 2 MeasureTheory.volume
      = MeasureTheory.eLpNorm f 2 MeasureTheory.volume := eLpNorm_fourier_eq_of_memLp hf hf2
  have hmemF : MeasureTheory.MemLp (𝓕 f) 2 MeasureTheory.volume := memLp_fourier_of_memLp hf hf2
  have hmult := eLpNorm_smul_le hCm hmae hsym' hmemF
  -- the inverse direction of Plancherel for `czOp D K ε f`
  have hmemCz : MeasureTheory.MemLp (𝓕 (czOp D K ε f)) 2 MeasureTheory.volume := by
    rw [hFourier]
    exact hmult.1
  have hrev := memLp_of_memLp_fourier hInt hmemCz
  rw [hrev.2, hFourier, ← hboundF]
  exact hmult.2

end

end Work.Analysis.CzShift
