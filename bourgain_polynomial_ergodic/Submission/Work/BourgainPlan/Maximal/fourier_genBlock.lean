import Mathlib
import Submission.Work.BourgainPlan.Maximal.genWindow_defs
import Submission.Work.BourgainPlan.Maximal.genWindow_analytic
import Submission.Commons.Analysis.Fourier.fourier_comp_mul_left

/-!
# The Fourier transform of the general-`P` block `genBlock`

The `k`-th block of the model of Bourgain §7.2 is, by definition,
`genBlock P k q D φ g s z x = q · 𝓕⁻(genAmpF P k q D φ g s z)(q x)`, i.e. the inverse
Fourier transform of the amplitude `genAmpF`, dilated by `q` and multiplied by `q` (the factor
`q` produces the residue `q [q ∣ j + z]` of the `a`-sum).  Dividing by the dilation constant
exactly cancels the factor `q`, so the block is the inverse transform of the amplitude in the
`q`-rescaled frequency variable; consequently its Fourier transform is the amplitude itself in
that variable:

`𝓕(genBlock P k q D φ g s z) ξ = genAmpF P k q D φ g s z (ξ / q)`.

This is the identity that lets the §7.2 model operator be recognised as a Fourier multiplier by
the amplitude `genAmpF` (see `genWindow_eq_genBlock` for the identification of `genWindow` with
`genBlock` on the lattice `{y q + z}`).

The proof has three ingredients.

* `genAmpF = genBetaAmp · conj (polyProfile P 2^k)` is a `C^∞` compactly supported function:
  `genBetaAmp` is `φ(D·)` times a finite sum of characters (support in `[-1/(2D), 1/(2D)]`
  because `φ` vanishes off `[-1/2,1/2]`), while `polyProfile P N` is the characteristic function
  of the pushforward of Lebesgue measure on `(0,1]` under `s ↦ P(Ns)`, hence `C^∞` in the
  frequency variable `β` (all moments of that pushforward are finite since `P` is bounded on
  `[0,N]`); see `contDiff_polyProfile_charFun`.
* Therefore `𝓕(genAmpF)` is integrable (a `C^∞` compactly supported function is a Schwartz
  function), so Fourier inversion applies: `𝓕(𝓕⁻ genAmpF) = genAmpF`.
* The constant `q` is removed by the dilation identity for the Fourier transform,
  `𝓕(f(q·)) ξ = q⁻¹ 𝓕 f (ξ/q)` (`Commons.Analysis.Fourier.fourier_comp_mul_left`).
-/

namespace Work.BourgainPlan.Maximal

open MeasureTheory Set
open scoped ENNReal

/-! ## Smoothness of the polynomial profile `β ↦ polyProfile P N β` -/

/-- The pushforward of Lebesgue measure on `(0,1]` under `s ↦ P(N s)`.  The polynomial profile
is the characteristic function of this finite measure at `2πβ`. -/
private noncomputable def polyMeasure (P : Polynomial ℤ) (N : ℕ) : Measure ℝ :=
  Measure.map (fun s : ℝ => (toRealPoly P).eval ((N : ℝ) * s)) (volume.restrict (Set.Ioc (0 : ℝ) 1))

private instance instIsFiniteMeasureRestrictIocBourgain :
    IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
  isFiniteMeasure_restrict.mpr
    (by rw [Real.volume_Ioc, sub_zero]; exact ENNReal.ofReal_one ▸ ENNReal.one_ne_top)

private instance instIsFiniteMeasurePolyMeasure (P : Polynomial ℤ) (N : ℕ) :
    IsFiniteMeasure (polyMeasure P N) := by
  unfold polyMeasure
  infer_instance

/-- Every moment of `polyMeasure P N` is finite: on `(0,1]` the map `s ↦ P(N s)` is bounded. -/
private lemma memLp_polyMeasure (P : Polynomial ℤ) (N : ℕ) (k : ℕ) :
    MemLp (id : ℝ → ℝ) (k : ℝ≥0∞) (polyMeasure P N) := by
  obtain ⟨M, hM0, hM⟩ := exists_eval_bound_Ioc P N
  have hbdd : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ‖(toRealPoly P).eval ((N : ℝ) * s)‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.norm_eq_abs]
    exact hM s hs
  have hmem : MemLp (fun s : ℝ => (toRealPoly P).eval ((N : ℝ) * s)) (k : ℝ≥0∞)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    MemLp.of_bound (by fun_prop) M hbdd
  unfold polyMeasure
  exact (memLp_map_measure_iff (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
    (f := fun s : ℝ => (toRealPoly P).eval ((N : ℝ) * s)) (g := (id : ℝ → ℝ))
    (p := (k : ℝ≥0∞)) (by fun_prop) (by fun_prop)).mpr (by simpa using hmem)

/-- The profile is the characteristic function of `polyMeasure` at `2πβ`. -/
private lemma polyProfile_eq_charFun (P : Polynomial ℤ) (N : ℕ) (β : ℝ) :
    polyProfile P N β = MeasureTheory.charFun (polyMeasure P N) (2 * Real.pi * β) := by
  rw [MeasureTheory.charFun_apply_real, polyProfile,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [show (∫ y, Complex.exp (↑(2 * Real.pi * β) * ↑y * Complex.I) ∂(polyMeasure P N))
      = ∫ s, Complex.exp (↑(2 * Real.pi * β) *
          ↑((toRealPoly P).eval ((N : ℝ) * s)) * Complex.I)
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) from by
    unfold polyMeasure
    exact integral_map (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
      (φ := fun s : ℝ => (toRealPoly P).eval ((N : ℝ) * s))
      (f := fun y : ℝ => Complex.exp (↑(2 * Real.pi * β) * ↑y * Complex.I))
      (by fun_prop) (by fun_prop)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  push_cast
  ring_nf

/-- The polynomial profile `polyProfile P N β = ∫₀¹ e(β P(N s)) ds` is smooth in `β`. -/
theorem contDiff_polyProfile_charFun (P : Polynomial ℤ) (N : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun β : ℝ => polyProfile P N β) := by
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (MeasureTheory.charFun (polyMeasure P N)) :=
    MeasureTheory.contDiff_charFun' (n := ⊤) (memLp_polyMeasure P N)
  have hcomp := hcd.comp
    (by fun_prop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun β : ℝ => 2 * Real.pi * β))
  rw [show (fun β : ℝ => polyProfile P N β)
      = (fun β : ℝ => MeasureTheory.charFun (polyMeasure P N) (2 * Real.pi * β))
      from funext (polyProfile_eq_charFun P N)]
  exact hcomp

/-! ## The amplitude `genAmpF` is `C^∞` and compactly supported -/

/-- The slice amplitude `genBetaAmp` has compact support, contained in the window
`[-1/(2D), 1/(2D)]`. -/
theorem hasCompactSupport_genBetaAmp (q : ℕ) {D : ℝ} (hD : 0 < D) {φ : ℝ → ℂ}
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) :
    HasCompactSupport (genBetaAmp q D φ g s z) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(1/(2*D))) (1/(2*D)))
    isCompact_Icc (fun β hβ => ?_)
  rw [Function.mem_support] at hβ
  by_contra hcon
  exact hβ (genBetaAmp_eq_zero_of_notMem q hD hφs g s z hcon)

/-- The slice amplitude `β ↦ φ(Dβ) · Σ_{j ≡ -z (q)} g_j e((j+z)β)` is smooth. -/
theorem contDiff_genBetaAmp (q : ℕ) (D : ℝ) {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (genBetaAmp q D φ g s z) := by
  unfold genBetaAmp
  refine ContDiff.mul (hφ.comp ?_) (ContDiff.sum ?_)
  · exact contDiff_const.mul contDiff_id
  · intro j hj
    refine ContDiff.mul contDiff_const ?_
    rw [show (fun β : ℝ => Complex.exp
        (2 * Real.pi * Complex.I * (((j : ℂ) + (z : ℂ)) * (β : ℂ))))
        = fun β : ℝ => Complex.exp
          (2 * Real.pi * Complex.I * ((j : ℂ) + (z : ℂ)) * (β : ℂ)) by
      funext β; ring_nf]
    fun_prop

/-- The amplitude of the `k`-th block is smooth. -/
theorem contDiff_genAmpF (P : Polynomial ℤ) (k : ℕ) (q : ℕ) (D : ℝ) {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (genAmpF P k q D φ g s z) := by
  have hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (genBetaAmp q D φ g s z) :=
    contDiff_genBetaAmp q D hφ g s z
  have hp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun β : ℝ => starRingEnd ℂ (polyProfile P (2^k) β)) :=
    Complex.conjCLE.contDiff.comp (contDiff_polyProfile_charFun P (2^k))
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun β : ℝ =>
    genBetaAmp q D φ g s z β * starRingEnd ℂ (polyProfile P (2^k) β))
  exact hb.mul hp

/-- The amplitude of the `k`-th block has compact support (`φ` vanishes off the window). -/
theorem hasCompactSupport_genAmpF (P : Polynomial ℤ) (k : ℕ) (q : ℕ) {D : ℝ} (hD : 0 < D)
    {φ : ℝ → ℂ} (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) :
    HasCompactSupport (genAmpF P k q D φ g s z) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-(1/(2*D))) (1/(2*D))) isCompact_Icc (fun β hβ => ?_)
  rw [Function.mem_support] at hβ
  by_contra hcon
  exact hβ (by rw [genAmpF, genBetaAmp_eq_zero_of_notMem q hD hφs g s z hcon, zero_mul])

/-- The Fourier transform of the amplitude is integrable: a smooth compactly supported function is
a Schwartz function, whose Fourier transform is again integrable. -/
theorem integrable_fourier_genAmpF (P : Polynomial ℤ) (k : ℕ) (q : ℕ) {D : ℝ} (hD : 0 < D)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) :
    Integrable (FourierTransform.fourier (genAmpF P k q D φ g s z)) :=
  Commons.Analysis.Fourier.integrable_fourier_of_contDiff_hasCompactSupport
    (hasCompactSupport_genAmpF P k q hD hφs g s z) (contDiff_genAmpF P k q D hφ g s z)

/-! ## The main identity -/

/-- Multiplication by a constant commutes with the Fourier transform. -/
theorem fourier_const_mul (c : ℂ) (f : ℝ → ℂ) (ξ : ℝ) :
    FourierTransform.fourier (fun x : ℝ => c * f x) ξ
      = c * FourierTransform.fourier f ξ := by
  rw [Real.fourier_eq, Real.fourier_eq, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [Circle.smul_def]
  ring

/-- **Bourgain §7.2: the block is the inverse transform of its amplitude, in the `q`-rescaled
frequency variable.**  Consequently the amplitude `genAmpF` is the Fourier multiplier symbol of
the block operator:

`𝓕(genBlock P k q D φ g s z) ξ = genAmpF P k q D φ g s z (ξ / q)`.

Indeed `genBlock · x = q · 𝓕⁻(genAmpF) (q x)`, and the dilation identity
`𝓕(f(q·)) ξ = q⁻¹ 𝓕 f (ξ/q)` cancels the factor `q`; then `𝓕(𝓕⁻ genAmpF) = genAmpF` is Fourier
inversion, applicable because `genAmpF` and `𝓕(genAmpF)` are both integrable (the former is
continuous with compact support, the latter is the Fourier transform of a `C^∞` compactly
supported function) and `genAmpF` is continuous. -/
theorem fourier_genBlock (P : Polynomial ℤ) (k q : ℕ) (hq : 0 < q) {D : ℝ} (hD : 0 < D)
    (h1D : 1 ≤ D) {φ : ℝ → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) (ξ : ℝ) :
    FourierTransform.fourier (genBlock P k q D φ g s z) ξ
      = genAmpF P k q D φ g s z (ξ / (q : ℝ)) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : ((q : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hqpos)
  have _h1D := h1D
  -- integrability of the amplitude and of its Fourier transform, and continuity
  have hGint : Integrable (genAmpF P k q D φ g s z) :=
    integrable_genAmpF P k q hD hφ.continuous hφs g s z
  have hFGint : Integrable (FourierTransform.fourier (genAmpF P k q D φ g s z)) :=
    integrable_fourier_genAmpF P k q hD hφ hφs g s z
  have hcont : ContinuousAt (genAmpF P k q D φ g s z) (ξ / (q : ℝ)) :=
    (continuous_genAmpF P k q D hφ.continuous g s z).continuousAt
  -- the block is a dilated inverse transform
  have hblock : genBlock P k q D φ g s z
      = fun x : ℝ => (q : ℂ) * FourierTransformInv.fourierInv
          (genAmpF P k q D φ g s z) ((q : ℝ) * x) := rfl
  rw [hblock, fourier_const_mul]
  -- pull the dilation out of the Fourier transform; the factors `q` and `q⁻¹` cancel
  rw [Commons.Analysis.Fourier.fourier_comp_mul_left
        (FourierTransformInv.fourierInv (genAmpF P k q D φ g s z)) hqpos]
  have hqq : ((q:ℝ):ℂ)⁻¹ * (q:ℂ) = 1 := by
    rw [Complex.ofReal_natCast, inv_mul_cancel₀]
    exact_mod_cast (ne_of_gt hq)
  have hcancel : (q : ℂ) * (((q : ℝ) : ℂ)⁻¹ * FourierTransform.fourier
      (FourierTransformInv.fourierInv (genAmpF P k q D φ g s z)) (ξ / (q : ℝ)))
      = FourierTransform.fourier (FourierTransformInv.fourierInv
          (genAmpF P k q D φ g s z)) (ξ / (q : ℝ)) := by
    rw [show (q : ℂ) * (((q : ℝ) : ℂ)⁻¹ * FourierTransform.fourier
        (FourierTransformInv.fourierInv (genAmpF P k q D φ g s z)) (ξ / (q : ℝ)))
        = ((q : ℂ) * ((q : ℝ) : ℂ)⁻¹) * FourierTransform.fourier
          (FourierTransformInv.fourierInv (genAmpF P k q D φ g s z)) (ξ / (q : ℝ)) by ring]
    rw [mul_comm (q : ℂ) (((q : ℝ) : ℂ)⁻¹), hqq, one_mul]
  rw [hcancel]
  -- Fourier inversion
  exact hGint.fourier_fourierInv_eq hFGint hcont

end Work.BourgainPlan.Maximal
