import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap BesselPotentialSpace ENNReal Real

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.EllipticEst.InteriorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Self-adjointness of the Fourier transform** for merely integrable (rather than Schwartz)
functions: `∫ (𝓕⁻ f) • g = ∫ f • (𝓕⁻ g)`.

This is the general form of `SchwartzMap.integral_fourierInv_smul_eq`; it is deduced from the
Fubini/self-adjointness statement `VectorFourier.integral_bilin_fourierIntegral_eq_flip` for the
Fourier integral. -/
theorem integral_fourierInv_smul_eq_of_integrable {f g : E → ℂ}
    (hf : Integrable f (volume : Measure E)) (hg : Integrable g (volume : Measure E)) :
    ∫ ξ, (𝓕⁻ f) ξ • g ξ = ∫ x, f x • (𝓕⁻ g) x := by
  have hflip : (-innerₗ E : E →ₗ[ℝ] E →ₗ[ℝ] ℝ).flip = -innerₗ E := by
    ext a b
    simp [LinearMap.flip_apply, LinearMap.neg_apply, innerₗ_apply_apply, real_inner_comm b a]
  have hcont : Continuous fun p : E × E => (-innerₗ E) p.1 p.2 := by
    have hc : Continuous fun p : E × E => -inner ℝ p.1 p.2 := continuous_inner.neg
    simpa only [LinearMap.neg_apply, innerₗ_apply_apply, Pi.neg_apply] using hc
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip (𝕜 := ℝ) (V := E) (W := E)
    (e := Real.fourierChar) (μ := volume) (ν := volume) (L := -innerₗ E)
    (ContinuousLinearMap.lsmul ℂ ℂ) Real.continuous_fourierChar hcont hf hg
  simp only [ContinuousLinearMap.lsmul_apply] at h
  have h1 : ∀ x : E, VectorFourier.fourierIntegral 𝐞 volume (-innerₗ E) f x = 𝓕⁻ f x := fun _ => rfl
  have h3 : (VectorFourier.fourierIntegral 𝐞 volume ((-innerₗ E).flip) g) = 𝓕⁻ g := by
    rw [hflip]
    funext x
    rfl
  simpa only [h1, h3] using h

/-- The weight `(1 + ‖x‖^2)^{m/2}` as a complex valued function. -/
def jbC (m : ℕ) (x : E) : ℂ := (((1 + ‖x‖ ^ 2) ^ ((m : ℝ) / 2) : ℝ) : ℂ)

/-- The reciprocal of the weight, as a complex valued function. -/
def jbCinv (m : ℕ) (x : E) : ℂ := ((((1 + ‖x‖ ^ 2) ^ ((m : ℝ) / 2) : ℝ))⁻¹ : ℂ)

theorem jbC_temperate (m : ℕ) : (jbC (E := E) m).HasTemperateGrowth := by
  unfold jbC; fun_prop

/-- The reciprocal weight is the negative power of the japanese bracket. -/
theorem jbCinv_eq (m : ℕ) :
    jbCinv (E := E) m = fun x : E => (((1 + ‖x‖ ^ 2) ^ (-(m : ℝ) / 2) : ℝ) : ℂ) := by
  funext x
  rw [jbCinv, ← Complex.ofReal_inv, ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖x‖ ^ 2)]
  congr 2
  ring

theorem jbCinv_temperate (m : ℕ) : (jbCinv (E := E) m).HasTemperateGrowth := by
  rw [jbCinv_eq m]; fun_prop

theorem jbC_ne_zero (m : ℕ) (x : E) : jbC (E := E) m x ≠ 0 := by
  unfold jbC
  simp only [ne_eq, Complex.ofReal_eq_zero]
  exact (Real.rpow_pos_of_pos (by positivity) _).ne'

theorem jbC_mul_jbCinv (m : ℕ) :
    jbC (E := E) m * jbCinv (E := E) m = fun _ => (1 : ℂ) := by
  funext x
  rw [Pi.mul_apply, jbCinv, jbC, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (Real.rpow_pos_of_pos (by positivity) (↑m / 2)).ne', Complex.ofReal_one]

theorem jbCinv_memLp (m : ℕ) : MemLp (jbCinv (E := E) m) ⊤ (volume : Measure E) := by
  rw [jbCinv_eq m]
  refine memLp_top_of_bound ?_ 1 ?_
  · apply Continuous.aestronglyMeasurable
    exact Complex.continuous_ofReal.comp
      ((continuous_const.add (continuous_norm.pow 2)).rpow_const
        fun x => Or.inl (ne_of_gt (by positivity : (0 : ℝ) < 1 + ‖x‖ ^ 2)))
  · filter_upwards with x
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by simp) ?_
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith

/-- If a `L²`-Fourier representative `f` and the weighted representative `f'` satisfy
`smulLeftCLM g (𝓕 u) = f'` then `f = g⁻¹ • f'`; this is the `Lp` form of the elementary fact that
the two representatives of the same tempered distribution agree a.e. -/
theorem eq_of_smulLeftCLM_eq {m : ℕ} {f f' : Lp ℂ 2 (volume : Measure E)}
    (h : smulLeftCLM ℂ (jbC (E := E) m) (f : 𝓢'(E, ℂ)) = (f' : 𝓢'(E, ℂ))) :
    f = MemLp.toLp (jbCinv (E := E) m) (jbCinv_memLp (E := E) m) • f' := by
  have hgt : (jbC (E := E) m).HasTemperateGrowth := jbC_temperate m
  have hgit : (jbCinv (E := E) m).HasTemperateGrowth := jbCinv_temperate m
  have hstep : smulLeftCLM ℂ (jbCinv (E := E) m) (f' : 𝓢'(E, ℂ)) = (f : 𝓢'(E, ℂ)) := by
    rw [← h, smulLeftCLM_smulLeftCLM_apply hgt hgit, jbC_mul_jbCinv, smulLeftCLM_const, one_smul]
  have hlp : ((MemLp.toLp (jbCinv (E := E) m) (jbCinv_memLp (E := E) m) • f'
      : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ))
      = smulLeftCLM ℂ (jbCinv (E := E) m) (f' : 𝓢'(E, ℂ)) :=
    Lp.toTemperedDistribution_smul_eq hgit (jbCinv_memLp (E := E) m) f'
  have hkey : Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2
        (MemLp.toLp (jbCinv (E := E) m) (jbCinv_memLp (E := E) m) • f')
      = Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2 f := by
    rw [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistributionCLM_apply, hlp, hstep]
  exact ((LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := (volume : Measure E)) (p := 2)))
      hkey).symm

/-- The square of the moment weight is dominated by the reciprocal japanese bracket. -/
theorem sq_moment_le (n m : ℕ) (x : E) :
    (‖x‖ ^ n * (1 + ‖x‖ ^ 2) ^ (-(m : ℝ) / 2)) ^ 2
      ≤ (1 + ‖x‖ ^ 2) ^ (-((m : ℝ) - n)) := by
  have hpos : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  have h1 : (‖x‖ ^ n) ^ 2 = (‖x‖ ^ 2) ^ n := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]
  have h2 : ((1 + ‖x‖ ^ 2) ^ (-(m : ℝ) / 2)) ^ 2 = (1 + ‖x‖ ^ 2) ^ (-(m : ℝ)) := by
    rw [← Real.rpow_natCast ((1 + ‖x‖ ^ 2) ^ (-(m : ℝ) / 2)) 2, ← Real.rpow_mul hpos.le]
    congr 1
    ring
  calc (‖x‖ ^ n * (1 + ‖x‖ ^ 2) ^ (-(m : ℝ) / 2)) ^ 2
      = (‖x‖ ^ 2) ^ n * (1 + ‖x‖ ^ 2) ^ (-(m : ℝ)) := by rw [mul_pow, h1, h2]
    _ ≤ (1 + ‖x‖ ^ 2) ^ n * (1 + ‖x‖ ^ 2) ^ (-(m : ℝ)) := by
        gcongr
        exact le_of_lt (lt_add_of_pos_left _ one_pos)
    _ = (1 + ‖x‖ ^ 2) ^ (-((m : ℝ) - n)) := by
        rw [← Real.rpow_natCast (1 + ‖x‖ ^ 2) n, ← Real.rpow_add hpos]
        congr 1
        ring

/-- The moment weight `ξ ↦ ‖ξ‖^n (1+‖ξ‖²)^{-m/2}` is square integrable. -/
theorem memLp_moment_weight {n m : ℕ} (hm : (Module.finrank ℝ E : ℝ) < 2 * ((m : ℝ) - n)) :
    MemLp (fun x : E => ‖x‖ ^ n * (1 + ‖x‖ ^ 2) ^ (-(m : ℝ) / 2)) 2 (volume : Measure E) := by
  rw [memLp_two_iff_integrable_sq_norm (by fun_prop)]
  refine Integrable.mono' (g := fun x : E => (1 + ‖x‖ ^ 2) ^ (-((m : ℝ) - n))) ?_ (by fun_prop) ?_
  · have h := integrable_rpow_neg_one_add_norm_sq (E := E) (μ := volume)
      (r := 2 * ((m : ℝ) - n)) hm
    simpa only [show -(2 * ((m : ℝ) - n)) / 2 = -((m : ℝ) - n) by ring] using h
  · filter_upwards with x
    have hA : (0 : ℝ) ≤ ‖x‖ ^ n * (1 + ‖x‖ ^ 2) ^ (-(m : ℝ) / 2) :=
      mul_nonneg (pow_nonneg (norm_nonneg x) n) (Real.rpow_nonneg (by positivity) _)
    rw [Real.norm_of_nonneg hA, Real.norm_of_nonneg (sq_nonneg _)]
    exact sq_moment_le n m x

/-- The weighted representative of `𝓕 u` is an `L²` function. -/
theorem weight_memLp {u : 𝓢'(E, ℂ)} {f : Lp ℂ 2 (volume : Measure E)}
    (hf : 𝓕 u = (f : 𝓢'(E, ℂ))) (m : ℕ) (hm : MemSobolev (m : ℝ) 2 u) :
    ∃ f' : Lp ℂ 2 (volume : Measure E),
      (fun ξ : E => jbC (E := E) m ξ * (f : E → ℂ) ξ) =ᵐ[volume] (f' : E → ℂ) := by
  obtain ⟨f', hf'⟩ : ∃ f' : Lp ℂ 2 (volume : Measure E),
      smulLeftCLM ℂ (jbC (E := E) m) (𝓕 u) = (f' : 𝓢'(E, ℂ)) :=
    memSobolev_iff_exists_smulLeftCLM_fourier.mp hm
  refine ⟨f', ?_⟩
  have hfe : f = MemLp.toLp (jbCinv (E := E) m) (jbCinv_memLp (E := E) m) • f' :=
    eq_of_smulLeftCLM_eq (by rw [← hf]; exact hf')
  rw [hfe]
  filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
      (MemLp.toLp (jbCinv (E := E) m) (jbCinv_memLp (E := E) m)) f',
    MemLp.coeFn_toLp (jbCinv_memLp (E := E) m)] with ξ h1 h2
  rw [h1]
  simp only [smul_eq_mul, Pi.mul_apply]
  rw [h2]
  have h3 : jbC (E := E) m ξ * jbCinv (E := E) m ξ = 1 := by
    have h4 := congr_fun (jbC_mul_jbCinv (E := E) m) ξ
    simpa only [Pi.mul_apply, Pi.one_apply] using h4
  rw [← mul_assoc, h3, one_mul]

/-- The moments of the Fourier representable `L²` function are finite. -/
theorem integrable_moment {u : 𝓢'(E, ℂ)} {f : Lp ℂ 2 (volume : Measure E)}
    (hf : 𝓕 u = (f : 𝓢'(E, ℂ))) (h : ∀ m : ℕ, MemSobolev (m : ℝ) 2 u) (n : ℕ) :
    Integrable (fun ξ : E => ‖ξ‖ ^ n * ‖(f : E → ℂ) ξ‖) (volume : Measure E) := by
  set M : ℕ := n + Module.finrank ℝ E + 1 with hM
  obtain ⟨f', hf'⟩ := weight_memLp hf M (h M)
  have hMn : (M : ℝ) - (n : ℝ) = (Module.finrank ℝ E : ℝ) + 1 := by
    rw [hM]; push_cast; ring
  have hC : MemLp (fun ξ : E => (1 + ‖ξ‖ ^ 2) ^ ((M : ℝ) / 2) * ‖(f : E → ℂ) ξ‖)
      2 (volume : Measure E) := by
    have h1 : MemLp (fun ξ : E => ‖jbC (E := E) M ξ * (f : E → ℂ) ξ‖) 2
        (volume : Measure E) := (MemLp.ae_eq hf'.symm (Lp.memLp f')).norm
    refine MemLp.ae_eq ?_ h1
    filter_upwards with ξ
    rw [norm_mul, jbC, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  have hB : MemLp (fun ξ : E => ‖ξ‖ ^ n * (1 + ‖ξ‖ ^ 2) ^ (-(M : ℝ) / 2))
      2 (volume : Measure E) := by
    refine memLp_moment_weight ?_
    rw [hMn]
    have : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    linarith
  have hBC : MemLp ((fun ξ : E => ‖ξ‖ ^ n * (1 + ‖ξ‖ ^ 2) ^ (-(M : ℝ) / 2)) *
      (fun ξ : E => (1 + ‖ξ‖ ^ 2) ^ ((M : ℝ) / 2) * ‖(f : E → ℂ) ξ‖))
      1 (volume : Measure E) := hB.mul hC
  refine (memLp_one_iff_integrable.mp hBC).congr ?_
  filter_upwards with ξ
  have hkey : (1 + ‖ξ‖ ^ 2) ^ (-(M : ℝ) / 2) * (1 + ‖ξ‖ ^ 2) ^ ((M : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2),
      show -(↑M) / 2 + ↑M / 2 = (0 : ℝ) by ring, Real.rpow_zero]
  simp only [Pi.mul_apply]
  rw [show (‖ξ‖ ^ n * (1 + ‖ξ‖ ^ 2) ^ (-(M : ℝ) / 2)) *
        ((1 + ‖ξ‖ ^ 2) ^ ((M : ℝ) / 2) * ‖(f : E → ℂ) ξ‖)
      = ‖ξ‖ ^ n * ((1 + ‖ξ‖ ^ 2) ^ (-(M : ℝ) / 2) * (1 + ‖ξ‖ ^ 2) ^ ((M : ℝ) / 2))
        * ‖(f : E → ℂ) ξ‖ by ring, hkey]
  ring

theorem exists_contDiffOn_of_memSobolev_all {E : Type*} [NormedAddCommGroup E]    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : 𝓢'(E, ℂ)} (h : ∀ m : ℕ, TemperedDistribution.MemSobolev (m : ℝ) 2 u) (x : E) :
    ∃ r : ℝ, 0 < r ∧ ∃ Φ : E → ℂ, (∀ n : ℕ, ContDiffOn ℝ n Φ (Metric.ball x r)) ∧
      (∀ ψ : 𝓢(E, ℂ), (∀ y, ψ y ≠ 0 → y ∈ Metric.ball x r) →
        u ψ = ∫ y, ψ y • Φ y) := by
  have h0 : MemSobolev (0 : ℝ) 2 u := by simpa using h 0
  obtain ⟨f, hf⟩ : ∃ f : Lp ℂ 2 (volume : Measure E), 𝓕 u = (f : 𝓢'(E, ℂ)) :=
    memSobolev_zero_iff_exists_fourier.mp h0
  have hmom : ∀ n : ℕ, Integrable (fun ξ : E => ‖ξ‖ ^ n * ‖(f : E → ℂ) ξ‖)
      (volume : Measure E) := fun n => integrable_moment hf h n
  have hf_int : Integrable (f : E → ℂ) (volume : Measure E) :=
    (hmom 0).mono' (Lp.memLp f).aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => by simp)
  refine ⟨1, one_pos, fun y => 𝓕⁻ (f : E → ℂ) y, ?_, ?_⟩
  · intro n
    have hc : ContDiff ℝ n (𝓕 (f : E → ℂ)) :=
      Real.contDiff_fourier (N := (n : ℕ∞)) (fun k _ => hmom k)
    have hcomp : ContDiff ℝ n (fun y : E => 𝓕 (f : E → ℂ) (-y)) :=
      hc.comp (contDiff_id.neg)
    have heq : (fun y : E => 𝓕⁻ (f : E → ℂ) y) = fun y : E => 𝓕 (f : E → ℂ) (-y) := by
      funext y
      exact Real.fourierInv_eq_fourier_neg (f : E → ℂ) y
    rw [heq]
    exact hcomp.contDiffOn
  · intro ψ _
    have h1 : u ψ = (f : 𝓢'(E, ℂ)) (𝓕⁻ ψ) := by
      calc u ψ = (𝓕⁻ (𝓕 u)) ψ := by rw [fourierInv_fourier_eq]
        _ = (𝓕 u) (𝓕⁻ ψ) := by rw [TemperedDistribution.fourierInv_apply]
        _ = (f : 𝓢'(E, ℂ)) (𝓕⁻ ψ) := by rw [hf]
    rw [h1, Lp.toTemperedDistribution_apply, SchwartzMap.fourierInv_coe]
    exact integral_fourierInv_smul_eq_of_integrable (SchwartzMap.integrable ψ) hf_int

end Work.EllipticEst.InteriorRegularity
