import Mathlib
import Submission.Work.GM.Affine.ae_eq_of_tendsto_lintegral_enorm_sq
import Submission.Work.GM.Affine.integral_norm_sq_eq_of_eLpNorm_eq
import Submission.Work.GM.Affine.integral_norm_sq_le_of_support_subset

namespace Work.GM.Affine

open MeasureTheory Filter
open scoped FourierTransform Topology

noncomputable section

/-- The space `L²(ℝ, ℂ)` (as an `Lp` space). -/
abbrev L2C := Lp (α := ℝ) ℂ 2 volume

/-! ### Elementary rephrasings of the `L²`-seminorm

`eLpNorm f 2` is `(∫⁻ x, ‖f x‖ₑ ^ 2) ^ (1/2)`; in particular its square is the lintegral of the
square of the norm, and for a function belonging to `L²` it is the `ofReal` of the `L²`-norm of the
associated class. -/

lemma eLpNorm_sq_eq_lintegral (f : ℝ → ℂ) (hf : MeasureTheory.AEStronglyMeasurable f volume) :
    (eLpNorm f 2 volume) ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

lemma eLpNorm_two_eq_ofReal_norm_toLp (f : ℝ → ℂ) (hf : MemLp f 2 volume) :
    eLpNorm f 2 volume = ENNReal.ofReal ‖(hf.toLp : L2C)‖ := by
  rw [← eLpNorm_congr_ae hf.coeFn_toLp, Lp.norm_def, ENNReal.ofReal_toReal]
  exact (Lp.memLp _).eLpNorm_ne_top

lemma eLpNorm_coeFn_toLp (u : L2C) :
    eLpNorm (⇑u) 2 volume = ENNReal.ofReal ‖u‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.memLp u).eLpNorm_ne_top]

/-- For `f, h ∈ L²`, the `L²`-distance of the associated classes is the square root of
`∫ ‖f - h‖²`. -/
lemma norm_toLp_sub_eq (g ψ : ℝ → ℂ) (hψ : MemLp ψ 2 volume) (hg : MemLp g 2 volume) :
    ‖(hψ.toLp : L2C) - (hg.toLp : L2C)‖ = (∫ x, ‖ψ x - g x‖ ^ 2) ^ (1 / 2 : ℝ) := by
  have h1 : eLpNorm (⇑(MemLp.toLp (ψ - g) (hψ.sub hg))) 2 volume = eLpNorm (ψ - g) 2 volume :=
    eLpNorm_congr_ae (MemLp.coeFn_toLp (hψ.sub hg))
  rw [← MemLp.toLp_sub hψ hg, Lp.norm_def, h1,
    MemLp.eLpNorm_eq_integral_rpow_norm (p := 2) two_ne_zero ENNReal.ofNat_ne_top (hψ.sub hg),
    ENNReal.toReal_ofReal (by positivity)]
  simp only [Pi.sub_apply, ENNReal.toReal_ofNat]
  norm_num

/-- The Fourier transform of a difference of integrable functions is the difference of the Fourier
transforms. -/
lemma fourier_sub_eq (f h : ℝ → ℂ) (hf : Integrable f volume) (hh : Integrable h volume) :
    𝓕 (f - h) = 𝓕 f - 𝓕 h := by
  ext w
  simp only [Pi.sub_apply]
  rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq, ← integral_sub]
  · apply integral_congr_ae
    filter_upwards with v
    simp only [Pi.sub_apply, smul_sub]
  · rw [Real.fourierIntegral_convergent_iff]; exact hf
  · rw [Real.fourierIntegral_convergent_iff]; exact hh

/-- If `h` vanishes outside the measurable set `K` of finite measure and `‖h‖ ≤ ε`, then the
integral of `‖h‖` is at most `ε * μ(K)`. -/
lemma integral_norm_le_of_support_subset (h : ℝ → ℂ) (K : Set ℝ) (ε : ℝ)
    (hK : MeasurableSet K) (hKf : volume K < ⊤) (_hε : 0 ≤ ε)
    (hsur : ∀ x ∉ K, h x = 0) (hbd : ∀ x, ‖h x‖ ≤ ε) :
    ∫ x, ‖h x‖ ≤ ε * (volume K).toReal := by
  have hg : Integrable (K.indicator (fun _ => ε)) volume := by
    rw [integrable_indicator_iff hK]
    exact integrableOn_const hKf.ne
  calc ∫ x, ‖h x‖ ≤ ∫ x, K.indicator (fun _ => ε) x := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) hg
        filter_upwards with x
        by_cases hx : x ∈ K
        · simp [Set.indicator_of_mem hx, hbd x]
        · simp [Set.indicator_of_notMem hx, hsur x hx]
    _ = ε * (volume K).toReal := by
        rw [integral_indicator hK, setIntegral_const, Measure.real, smul_eq_mul]
        ring

/-- **Plancherel for `C_c(ℝ,ℂ)`**: for a continuous compactly supported `g : ℝ → ℂ`,
`∫ x, ‖g x‖^2 = ∫ ξ, ‖𝓕 g ξ‖^2` (Mathlib's `𝓕 = FourierTransform.fourier`, i.e.
`𝓕 g ξ = ∫ v, 𝐞(-(v*ξ)) • g v = ∫ v, exp(-2π i v ξ) g v`). -/
theorem plancherel_continuous (g : ℝ → ℂ) (hg : Continuous g) (hcs : HasCompactSupport g) :
    ∫ x, ‖g x‖ ^ 2 = ∫ ξ, ‖FourierTransform.fourier g ξ‖ ^ 2 := by
  have hgLp : MemLp g 2 volume := hg.memLp_of_hasCompactSupport hcs
  have hgint : Integrable g volume := hg.integrable_of_hasCompactSupport hcs
  have hKmeas : MeasurableSet (tsupport g) := (isClosed_tsupport g).measurableSet
  have hKfin : volume (tsupport g) < ⊤ := IsCompact.measure_lt_top hcs
  -- an approximating sequence of smooth compactly supported functions, supported in `tsupport g`,
  -- converging uniformly to `g`
  choose ψ hψcd hψclose hψsupp using fun n : ℕ =>
    hg.exists_contDiff_approx (⊤ : ℕ∞) continuous_const
      (ε := fun _ : ℝ => (1:ℝ)/(n+1)) (fun _ => by positivity)
  have hψclose' : ∀ n x, ‖ψ n x - g x‖ ≤ (1:ℝ)/(n+1) := fun n x => by
    have h := hψclose n x
    rw [dist_eq_norm] at h
    exact h.le
  have hψsuppK : ∀ n, Function.support (ψ n) ⊆ tsupport g :=
    fun n => (hψsupp n).trans (subset_tsupport g)
  have hψcs : ∀ n, HasCompactSupport (ψ n) := fun n => hcs.mono (hψsupp n)
  have hψLp : ∀ n, MemLp (ψ n) 2 volume :=
    fun n => (hψcd n).continuous.memLp_of_hasCompactSupport (hψcs n)
  have hψint : ∀ n, Integrable (ψ n) volume :=
    fun n => (hψcd n).continuous.integrable_of_hasCompactSupport (hψcs n)
  have hψzero : ∀ n x, x ∉ tsupport g → ψ n x - g x = 0 := fun n x hx => by
    have h1 : ψ n x = 0 := by
      by_contra h
      exact hx (hψsuppK n (Function.mem_support.mpr h))
    have h2 : g x = 0 := by
      by_contra h
      exact hx (subset_tsupport g (Function.mem_support.mpr h))
    rw [h1, h2, sub_zero]
  -- the integral estimate
  have hIle : ∀ n, ∫ x, ‖ψ n x - g x‖ ^ 2
      ≤ ((1:ℝ)/(n+1)) ^ 2 * (volume (tsupport g)).toReal :=
    fun n => integral_norm_sq_le_of_support_subset (fun x => ψ n x - g x) (tsupport g) _
      hKmeas hKfin (by positivity) (hψzero n) (hψclose' n)
  have hI : Tendsto (fun n => ∫ x, ‖ψ n x - g x‖ ^ 2) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun n => integral_nonneg fun x => sq_nonneg _) hIle
    have h1 : Tendsto (fun n : ℕ => (1:ℝ)/(n+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h1.pow 2 |>.mul_const ((volume (tsupport g)).toReal)
  -- convergence in `L²`
  have hnorm : Tendsto (fun n => ‖(hψLp n).toLp - (hgLp.toLp : L2C)‖) atTop (𝓝 0) := by
    have h1 : (fun n => ‖(hψLp n).toLp - (hgLp.toLp : L2C)‖)
        = fun n => (∫ x, ‖ψ n x - g x‖ ^ 2) ^ (1/2:ℝ) :=
      funext fun n => norm_toLp_sub_eq g (ψ n) (hψLp n) hgLp
    rw [h1]
    simpa [Real.sqrt_eq_rpow] using hI.sqrt
  -- the Fourier transform of `g` is continuous
  have hFcont : Continuous (FourierTransform.fourier g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hgint
  -- pointwise convergence of the Fourier transforms
  have hfl : ∀ ξ, Tendsto (fun n => FourierTransform.fourier (ψ n) ξ) atTop
      (𝓝 (FourierTransform.fourier g ξ)) := by
    intro ξ
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbd : ∀ n, ‖FourierTransform.fourier (ψ n) ξ - FourierTransform.fourier g ξ‖
        ≤ (1:ℝ)/(n+1) * (volume (tsupport g)).toReal := by
      intro n
      have hsub : FourierTransform.fourier (ψ n) ξ - FourierTransform.fourier g ξ
          = FourierTransform.fourier (ψ n - g) ξ := by
        have h := congr_fun (fourier_sub_eq (ψ n) g (hψint n) hgint) ξ
        simpa only [Pi.sub_apply] using h.symm
      rw [hsub]
      calc ‖FourierTransform.fourier (ψ n - g) ξ‖
          = ‖∫ v, 𝐞 (-(inner ℝ v ξ)) • (ψ n - g) v‖ := by rw [Real.fourier_eq]
        _ ≤ ∫ v, ‖𝐞 (-(inner ℝ v ξ)) • (ψ n - g) v‖ := norm_integral_le_integral_norm _
        _ = ∫ v, ‖ψ n v - g v‖ := by simp
        _ ≤ (1:ℝ)/(n+1) * (volume (tsupport g)).toReal :=
            integral_norm_le_of_support_subset _ _ _ hKmeas hKfin (by positivity)
              (hψzero n) (hψclose' n)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun n => norm_nonneg _) hbd
    have h1 : Tendsto (fun n : ℕ => (1:ℝ)/(n+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h1.mul_const ((volume (tsupport g)).toReal)
  -- the `L²`-Fourier transform of `g`, and its `L²`-convergence along the approximations
  set U : L2C := 𝓕 (hgLp.toLp : L2C) with hUdef
  have hVU : Tendsto (fun n => ‖(𝓕 ((hψLp n).toLp : L2C) : L2C) - U‖) atTop (𝓝 0) := by
    have h1 : (fun n => ‖(𝓕 ((hψLp n).toLp : L2C) : L2C) - U‖)
        = fun n => ‖(hψLp n).toLp - (hgLp.toLp : L2C)‖ := by
      funext n
      rw [hUdef]
      change ‖(Lp.fourierTransformₗᵢ ℝ ℂ) ((hψLp n).toLp) -
          (Lp.fourierTransformₗᵢ ℝ ℂ) (hgLp.toLp)‖ = ‖(hψLp n).toLp - (hgLp.toLp : L2C)‖
      rw [← map_sub, (Lp.fourierTransformₗᵢ ℝ ℂ).norm_map]
    rw [h1]
    exact hnorm
  -- the associated lintegral convergence
  have hkey : ∀ n, (∫⁻ x,
      ‖((𝓕 ((hψLp n).toLp : L2C) : L2C) : ℝ → ℂ) x - (U : ℝ → ℂ) x‖ₑ ^ (2:ℝ) ∂volume)
      = ENNReal.ofReal (‖(𝓕 ((hψLp n).toLp : L2C) : L2C) - U‖ ^ 2) := by
    intro n
    have hcongr : (fun x => ‖((𝓕 ((hψLp n).toLp : L2C) : L2C) : ℝ → ℂ) x
          - (U : ℝ → ℂ) x‖ₑ ^ (2:ℝ))
        =ᵐ[volume] (fun x => ‖(⇑((𝓕 ((hψLp n).toLp : L2C) : L2C) - U) : ℝ → ℂ) x‖ₑ ^ (2:ℝ)) := by
      filter_upwards [Lp.coeFn_sub (𝓕 ((hψLp n).toLp : L2C) : L2C) U] with x hx
      simp only [Pi.sub_apply] at hx
      rw [hx]
    rw [lintegral_congr_ae hcongr,
      ← eLpNorm_sq_eq_lintegral (⇑((𝓕 ((hψLp n).toLp : L2C) : L2C) - U)) (Lp.aestronglyMeasurable _),
      eLpNorm_coeFn_toLp, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have hlin : Tendsto (fun n => ∫⁻ x,
      ‖((𝓕 ((hψLp n).toLp : L2C) : L2C) : ℝ → ℂ) x - (U : ℝ → ℂ) x‖ₑ ^ (2:ℝ) ∂volume)
      atTop (𝓝 0) := by
    rw [funext hkey]
    have h1 : Tendsto (fun n => ‖(𝓕 ((hψLp n).toLp : L2C) : L2C) - U‖ ^ 2) atTop (𝓝 0) := by
      simpa using hVU.pow 2
    have h2 : Tendsto ((ENNReal.ofReal) ∘ fun n =>
        ‖(𝓕 ((hψLp n).toLp : L2C) : L2C) - U‖ ^ 2) atTop (𝓝 0) := by
      have h3 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
      rwa [ENNReal.ofReal_zero] at h3
    exact h2
  -- pointwise a.e. convergence of the representatives to `𝓕 g`
  have hVae : ∀ n, ((𝓕 ((hψLp n).toLp : L2C) : L2C) : ℝ → ℂ)
      =ᵐ[volume] FourierTransform.fourier (ψ n) := by
    intro n
    have h1 : (𝓕 ((hψLp n).toLp : L2C) : L2C)
        = ((𝓕 ((hψcs n).toSchwartzMap (hψcd n)) : SchwartzMap ℝ ℂ)).toLp 2 volume := by
      rw [show (hψLp n).toLp = ((hψcs n).toSchwartzMap (hψcd n)).toLp 2 volume from rfl,
        SchwartzMap.toLp_fourier_eq]
    rw [h1]
    filter_upwards [SchwartzMap.coeFn_toLp (𝓕 ((hψcs n).toSchwartzMap (hψcd n))) 2 volume]
      with ξ hξ
    rw [hξ, SchwartzMap.fourier_coe]
    rfl
  have hae : ∀ᵐ ξ ∂volume, Tendsto (fun n =>
      ((𝓕 ((hψLp n).toLp : L2C) : L2C) : ℝ → ℂ) ξ) atTop (𝓝 (FourierTransform.fourier g ξ)) := by
    have hall : ∀ᵐ ξ ∂volume, ∀ n,
        ((𝓕 ((hψLp n).toLp : L2C) : L2C) : ℝ → ℂ) ξ = FourierTransform.fourier (ψ n) ξ :=
      ae_all_iff.mpr hVae
    filter_upwards [hall] with ξ hξ
    exact (hfl ξ).congr' (Filter.Eventually.of_forall fun n => (hξ n).symm)
  -- the a.e. identification of `𝓕 g` with the `L²`-Fourier transform
  have hae_eq : FourierTransform.fourier g =ᵐ[volume] (fun ξ => (U : ℝ → ℂ) ξ) :=
    ae_eq_of_tendsto_lintegral_enorm_sq
      (fun n => fun ξ => ((𝓕 ((hψLp n).toLp : L2C) : L2C) : ℝ → ℂ) ξ)
      (FourierTransform.fourier g) (fun ξ => (U : ℝ → ℂ) ξ)
      (fun n => (Lp.aestronglyMeasurable _).aemeasurable)
      hFcont.aemeasurable (Lp.aestronglyMeasurable U).aemeasurable hlin hae
  -- equality of `L²`-seminorms
  have hEq : eLpNorm g 2 volume = eLpNorm (FourierTransform.fourier g) 2 volume := by
    have h1 : eLpNorm (FourierTransform.fourier g) 2 volume = ENNReal.ofReal ‖U‖ := by
      rw [eLpNorm_congr_ae hae_eq]
      exact eLpNorm_coeFn_toLp U
    rw [eLpNorm_two_eq_ofReal_norm_toLp g hgLp, h1, hUdef]
    change ENNReal.ofReal ‖(hgLp.toLp : L2C)‖ =
      ENNReal.ofReal ‖(Lp.fourierTransformₗᵢ ℝ ℂ) (hgLp.toLp)‖
    rw [(Lp.fourierTransformₗᵢ ℝ ℂ).norm_map]
  have hFmem : MemLp (FourierTransform.fourier g) 2 volume :=
    (by rw [MeasureTheory.memLp_iff, ← hEq]; exact hgLp.eLpNorm_lt_top)
  exact integral_norm_sq_eq_of_eLpNorm_eq g (FourierTransform.fourier g) hgLp hFmem hEq

end

end Work.GM.Affine
