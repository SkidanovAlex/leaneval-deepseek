import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Defs
import Submission.Work.BourgainPlan.IonescuWainger.tendsto_lp_diffQuot
import Submission.Work.BourgainPlan.IonescuWainger.ae_eq_zero_on_open_of_forall_isCompact_setIntegral_eq_zero

/-!
# Multiplication by a monomial does not spread the frequency support

If the Fourier transform of `g ∈ ℓ²(ℤ)` vanishes a.e. outside `E`, and `n ↦ n^k g(n)` is also in
`ℓ²`, then the Fourier transform of `n ↦ n^k g(n)` vanishes a.e. outside the closure of `E`.

The mathematical content is that multiplication of the coefficient sequence by the *polynomial*
`n ↦ n^k` is a differential operator on the Fourier side, hence local: the `k`-th derivative of a
function is supported in the closure of the support of the function.  Formally the `k = 1` case is
proved by realizing the operator as the limit of the translation difference quotients
`t⁻¹ (τ_t F - F)`: each `τ_t F` vanishes outside the `t`-neighbourhood of the support, so every
compact subset of the complement of the closure of `E` has vanishing integral against every
difference quotient, and the integral is continuous in the `L²` topology.  The general case follows
by induction (`k ↦ k+1` is `k` followed by the linear case applied to `n ↦ n^k g(n)`).
-/

open MeasureTheory Filter
open scoped lp BigOperators ENNReal Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.IonescuWainger

/-- Translation of an `L²` class on the circle: `(shiftLp t F) x = F (x + t)`. -/
noncomputable def shiftLp (t : Circle) (F : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) :=
  Lp.compMeasurePreserving (fun x : Circle => x + t)
    (measurePreserving_add_right (AddCircle.haarAddCircle (T := 1)) t) F

theorem shiftLp_coeFn (t : Circle) (F : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) :
    (shiftLp t F : Circle → ℂ) =ᵐ[AddCircle.haarAddCircle (T := 1)] fun x => F (x + t) :=
  Lp.coeFn_compMeasurePreserving F _

/-- The `i`-th Fourier coefficient of `ftLp h hh` is `h i`. -/
theorem repr_ftLp {h : ℤ → ℂ} (hh : Memℓp h 2) (i : ℤ) :
    fourierBasis.repr (ftLp h hh) i = h i := by
  have h1 : fourierBasis.repr (ftLp h hh) = (⟨h, hh⟩ : lp (fun _ : ℤ => ℂ) 2) := by
    rw [ftLp]
    exact LinearIsometryEquiv.apply_symm_apply _ _
  rw [h1]

private theorem fourier_add_arg (n : ℤ) (x y : Circle) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, _root_.Circle.coe_mul]

private theorem fourier_neg_neg (n : ℤ) (x : Circle) :
    fourier (-n) (-x) = fourier n x := by
  rw [fourier_apply, neg_zsmul, zsmul_neg, neg_neg, ← fourier_apply]

/-- **The Fourier coefficients of a translate**: the `i`-th coefficient of `shiftLp t (ftLp g hg)`
is `e^{2πi i t} · g i`. -/
theorem repr_shiftLp {g : ℤ → ℂ} (hg : Memℓp g 2) (t : Circle) (i : ℤ) :
    fourierBasis.repr (shiftLp t (ftLp g hg)) i = fourier i t * g i := by
  set F := ftLp g hg with hF
  set U : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) := shiftLp t F with hU
  have hcoe : (U : Circle → ℂ) =ᵐ[AddCircle.haarAddCircle (T := 1)]
      fun s => (F : Circle → ℂ) (s + t) := by
    rw [hU, hF]
    exact shiftLp_coeFn t (ftLp g hg)
  rw [show fourierBasis.repr U i = fourierCoeff U i from fourierBasis_repr U i, fourierCoeff]
  have h1 : ∫ s, fourier (-i) s • (U : Circle → ℂ) s ∂AddCircle.haarAddCircle (T := 1)
      = ∫ s, fourier (-i) s • (F : Circle → ℂ) (s + t) ∂AddCircle.haarAddCircle (T := 1) := by
    refine integral_congr_ae ?_
    filter_upwards [hcoe] with s hs
    rw [hs]
  have h2 : ∫ s, fourier (-i) s • (F : Circle → ℂ) (s + t) ∂AddCircle.haarAddCircle (T := 1)
      = ∫ y, fourier (-i) (y - t) • (F : Circle → ℂ) y ∂AddCircle.haarAddCircle (T := 1) := by
    have h := integral_add_right_eq_self (μ := AddCircle.haarAddCircle (T := 1))
      (fun y : Circle => fourier (-i) (y - t) • (F : Circle → ℂ) y) t
    simpa using h
  have h3 : ∫ y, fourier (-i) (y - t) • (F : Circle → ℂ) y ∂AddCircle.haarAddCircle (T := 1)
      = fourier (-i) (-t) * ∫ y, fourier (-i) y • (F : Circle → ℂ) y
          ∂AddCircle.haarAddCircle (T := 1) := by
    have hpt : (fun y : Circle => fourier (-i) (y - t) • (F : Circle → ℂ) y)
        = fun y : Circle => fourier (-i) (-t) * (fourier (-i) y • (F : Circle → ℂ) y) := by
      funext y
      simp only [sub_eq_add_neg, fourier_add_arg, smul_eq_mul]
      ring
    rw [hpt, integral_const_mul]
  have h4 : ∫ y, fourier (-i) y • (F : Circle → ℂ) y ∂AddCircle.haarAddCircle (T := 1) = g i := by
    have h := repr_ftLp (h := g) hg i
    rw [fourierBasis_repr] at h
    simpa only [fourierCoeff] using h
  rw [h1, h2, h3, h4, fourier_neg_neg i t]

/-- The difference quotient sequence `n ↦ ((e^{2πi n t} - 1)/t) g n` is square summable. -/
theorem memℓp_diffQuot {g : ℤ → ℂ} (hg1 : Memℓp (fun n : ℤ => (n : ℂ) * g n) 2) :
    ∀ t : ℝ, Memℓp (fun n : ℤ => ((t : ℂ)⁻¹ * (fourier n (t : Circle) - 1)) * g n) 2 := by
  have htgt : Memℓp (fun n : ℤ => (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℂ) * g n)) 2 :=
    hg1.const_mul (2 * (Real.pi : ℂ) * Complex.I)
  intro t
  refine Memℓp.mono (f := fun n : ℤ => ((t : ℂ)⁻¹ * (fourier n (t : Circle) - 1)) * g n)
    (g := fun n : ℤ => ‖(2 * (Real.pi : ℂ) * Complex.I) * ((n : ℂ) * g n)‖)
    (memℓp_norm_iff.mpr htgt) (fun n => ?_)
  have hb : ‖(t : ℂ)⁻¹ * (fourier n (t : Circle) - 1)‖ ≤ 2 * Real.pi * |(n : ℝ)| := by
    rw [norm_mul]
    rcases eq_or_ne t 0 with ht0 | ht
    · subst ht0
      norm_num
      positivity
    · have hfr : fourier n (t : Circle) =
          Complex.exp (Complex.I * ((2 * Real.pi * n * t : ℝ) : ℂ)) := by
        rw [fourier_coe_apply]; norm_num; congr 1; ring
      have hbnd : ‖fourier n (t : Circle) - 1‖ ≤ 2 * Real.pi * |(n : ℝ)| * |t| := by
        rw [hfr]
        refine (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * n * t)).trans ?_
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
        norm_num
      rw [norm_inv]
      have htn : ‖(t : ℂ)‖ = |t| := by simp
      rw [htn]
      calc |t|⁻¹ * ‖fourier n (t : Circle) - 1‖
          ≤ |t|⁻¹ * (2 * Real.pi * |(n : ℝ)| * |t|) :=
            mul_le_mul_of_nonneg_left hbnd (by positivity)
        _ = 2 * Real.pi * |(n : ℝ)| := by
            rw [← mul_assoc, mul_comm (|t|⁻¹) (2 * Real.pi * |(n : ℝ)|), mul_assoc,
              inv_mul_cancel₀ (abs_ne_zero.mpr ht), mul_one]
  have hnormc : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one]
    simp [abs_of_pos Real.pi_pos]
  calc ‖((t : ℂ)⁻¹ * (fourier n (t : Circle) - 1)) * g n‖
      = ‖(t : ℂ)⁻¹ * (fourier n (t : Circle) - 1)‖ * ‖g n‖ := norm_mul _ _
    _ ≤ (2 * Real.pi * |(n : ℝ)|) * ‖g n‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = ‖(2 * (Real.pi : ℂ) * Complex.I) * ((n : ℂ) * g n)‖ := by
        rw [norm_mul (2 * (Real.pi : ℂ) * Complex.I) ((n : ℂ) * g n),
          norm_mul ((n : ℂ)) (g n), hnormc, Complex.norm_intCast]
        ring

/-- `HasFreqSupport` only depends on the sequence, not on the proof of square summability. -/
theorem mulPow_hasFreqSupport_congr {f g : ℤ → ℂ} {E : Set Circle} (hfg : ∀ n, f n = g n)
    (hf : Memℓp f 2) (hg : Memℓp g 2) :
    HasFreqSupport f hf E ↔ HasFreqSupport g hg E := by
  have hft : ftLp f hf = ftLp g hg := by
    simp only [ftLp]
    rw [show (⟨f, hf⟩ : lp (fun _ : ℤ => ℂ) 2) = ⟨g, hg⟩ from Subtype.ext (funext hfg)]
  simp only [HasFreqSupport]
  rw [hft]

/-- Enlarging the set never destroys a frequency support condition. -/
theorem mulPow_hasFreqSupport_mono {f : ℤ → ℂ} {hf : Memℓp f 2} {E E' : Set Circle}
    (h : HasFreqSupport f hf E) (hEE : E ⊆ E') : HasFreqSupport f hf E' := by
  filter_upwards [h] with θ hθ hθE'
  exact hθ (fun hmem => hθE' (hEE hmem))

/-- Transporting square summability along a pointwise equality. -/
theorem memℓp_congr_aux {f g : ℤ → ℂ} (h : ∀ n, f n = g n) (hf : Memℓp f 2) : Memℓp g 2 := by
  rw [funext h] at hf
  exact hf

/-- **The linear case**: multiplication of the coefficients by `n` does not spread the frequency
support. -/
theorem hasFreqSupport_mul_linear {g : ℤ → ℂ} (hg : Memℓp g 2) {E : Set Circle}
    (hE : HasFreqSupport g hg E) (hg1 : Memℓp (fun n : ℤ => (n : ℂ) * g n) 2) :
    HasFreqSupport (fun n : ℤ => (n : ℂ) * g n) hg1 (closure E) := by
  set μ : Measure Circle := AddCircle.haarAddCircle (T := 1) with hμdef
  set F : Lp ℂ 2 μ := ftLp g hg with hFdef
  set H : Lp ℂ 2 μ := ftLp (fun n : ℤ => (n : ℂ) * g n) hg1 with hHdef
  show ∀ᵐ θ ∂μ, θ ∉ closure E → (H : Circle → ℂ) θ = 0
  have hD2C : ∀ {ν : Measure Circle} {f : Circle → ℂ}, Integrable f ν →
      ∀ {U : Set Circle}, IsOpen U →
      (∀ C : Set Circle, IsCompact C → C ⊆ U → ∫ x in C, f x ∂ν = 0) →
      ∀ᵐ x ∂ν, x ∈ U → f x = 0 :=
    fun {ν} {f} hf {U} hU h => ae_eq_zero_on_open_of_forall_isCompact_setIntegral_eq_zero hf hU h
  refine hD2C ?_ isClosed_closure.isOpen_compl ?_
  · exact (Lp.memLp H).integrable (by norm_num)
  · intro C hC hCU
    have hCmeas : MeasurableSet C := hC.isClosed.measurableSet
    have hFsupp : ∀ᵐ θ ∂μ, θ ∈ (closure E)ᶜ → (F : Circle → ℂ) θ = 0 := by
      filter_upwards [hE] with θ hθ hθU
      exact hθ (fun hmem => hθU (subset_closure hmem))
    have hFC : ∫ x in C, (F : Circle → ℂ) x ∂μ = 0 := by
      refine setIntegral_eq_zero_of_ae_eq_zero ?_
      filter_upwards [hFsupp] with x hx hxC
      exact hx (hCU hxC)
    obtain ⟨δ, hδpos, hδsub⟩ :=
      hC.exists_cthickening_subset_open isClosed_closure.isOpen_compl hCU
    have hμC : μ C ≠ ∞ := measure_ne_top μ C
    set v : Lp ℂ 2 μ := indicatorConstLp 2 hCmeas hμC (1 : ℂ) with hvdef
    have hinner : ∀ ψ : Lp ℂ 2 μ, (∫ x in C, (ψ : Circle → ℂ) x ∂μ) = inner ℂ v ψ := by
      intro ψ
      classical
      rw [MeasureTheory.L2.inner_def]
      have hpt : (fun x => inner ℂ ((v : Circle → ℂ) x) ((ψ : Circle → ℂ) x))
          =ᵐ[μ] fun x => C.indicator (fun x => (ψ : Circle → ℂ) x) x := by
        filter_upwards [indicatorConstLp_coeFn (μ := μ) (p := 2) (hs := hCmeas) (hμs := hμC)
          (c := (1 : ℂ))] with x hx
        rw [hx, Set.indicator_apply]
        by_cases hxC : x ∈ C <;> simp [hxC]
      rw [integral_congr_ae hpt, integral_indicator hCmeas]
    have htgt : Memℓp (fun n : ℤ => (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℂ) * g n)) 2 :=
      hg1.const_mul (2 * (Real.pi : ℂ) * Complex.I)
    have hdq := memℓp_diffQuot hg1
    have hDlin : ∀ t : ℝ,
        (⟨fun n : ℤ => ((t : ℂ)⁻¹ * (fourier n (t : Circle) - 1)) * g n, hdq t⟩ :
            lp (fun _ : ℤ => ℂ) 2)
          = fourierBasis.repr ((t : ℂ)⁻¹ • (shiftLp (t : Circle) F - F)) := by
      intro t
      refine lp.ext ?_
      funext n
      rw [hFdef]
      simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply,
        LinearIsometryEquiv.map_sub, LinearIsometryEquiv.map_smul]
      rw [repr_shiftLp hg (t : Circle) n, repr_ftLp hg n]
      ring
    have hsymm : fourierBasis.repr.symm
        (⟨fun n : ℤ => (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℂ) * g n), htgt⟩ :
          lp (fun _ : ℤ => ℂ) 2)
        = (2 * (Real.pi : ℂ) * Complex.I) • H := by
      have h2 : fourierBasis.repr ((2 * (Real.pi : ℂ) * Complex.I) • H)
          = (⟨fun n : ℤ => (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℂ) * g n), htgt⟩ :
              lp (fun _ : ℤ => ℂ) 2) := by
        refine lp.ext ?_
        funext n
        rw [hHdef]
        simp only [lp.coeFn_smul, Pi.smul_apply, LinearIsometryEquiv.map_smul]
        rw [repr_ftLp hg1 n]
        ring
      rw [← h2, LinearIsometryEquiv.symm_apply_apply]
    have hlimB : Filter.Tendsto (fun t : ℝ => fourierBasis.repr.symm
        (⟨fun n : ℤ => ((t : ℂ)⁻¹ * (fourier n (t : Circle) - 1)) * g n, hdq t⟩ :
          lp (fun _ : ℤ => ℂ) 2))
        (nhdsWithin (0 : ℝ) ({0}ᶜ))
        (nhds (fourierBasis.repr.symm
          (⟨fun n : ℤ => (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℂ) * g n), htgt⟩ :
            lp (fun _ : ℤ => ℂ) 2))) :=
      ((fourierBasis (T := 1)).repr.symm.continuous.tendsto _).comp
        (tendsto_lp_diffQuot hdq htgt)
    have hlim : Filter.Tendsto (fun t : ℝ => (t : ℂ)⁻¹ • (shiftLp (t : Circle) F - F))
        (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds ((2 * (Real.pi : ℂ) * Complex.I) • H)) := by
      have h1 : Filter.Tendsto (fun t : ℝ => (t : ℂ)⁻¹ • (shiftLp (t : Circle) F - F))
          (nhdsWithin (0 : ℝ) ({0}ᶜ))
          (nhds (fourierBasis.repr.symm
            (⟨fun n : ℤ => (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℂ) * g n), htgt⟩ :
              lp (fun _ : ℤ => ℂ) 2))) :=
        hlimB.congr' (Filter.Eventually.of_forall (fun t => by
          show fourierBasis.repr.symm
              (⟨fun n : ℤ => ((t : ℂ)⁻¹ * (fourier n (t : Circle) - 1)) * g n, hdq t⟩ :
                lp (fun _ : ℤ => ℂ) 2)
            = (t : ℂ)⁻¹ • (shiftLp (t : Circle) F - F)
          rw [hDlin t, LinearIsometryEquiv.symm_apply_apply]))
      rwa [hsymm] at h1
    have hcoe0 : (((0 : ℝ)) : Circle) = 0 := AddCircle.coe_zero 1
    have hev : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) ({0}ᶜ), dist (t : Circle) 0 < δ := by
      have hball : Metric.ball (((0 : ℝ)) : Circle) δ ∈ nhds (((0 : ℝ)) : Circle) :=
        Metric.ball_mem_nhds _ hδpos
      have hpre : (fun t : ℝ => (t : Circle)) ⁻¹' (Metric.ball (((0 : ℝ)) : Circle) δ)
          ∈ nhds (0 : ℝ) :=
        (AddCircle.continuous_mk' 1).continuousAt.preimage_mem_nhds hball
      have hmem : (fun t : ℝ => (t : Circle)) ⁻¹' (Metric.ball (((0 : ℝ)) : Circle) δ)
          ∈ nhdsWithin (0 : ℝ) ({0}ᶜ) := nhdsWithin_le_nhds hpre
      exact Filter.mem_of_superset hmem (fun t ht => by
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_ball] at ht ⊢
        rwa [hcoe0] at ht)
    have hzero : ∀ t : ℝ, dist (t : Circle) 0 < δ →
        inner ℂ v ((t : ℂ)⁻¹ • (shiftLp (t : Circle) F - F)) = 0 := by
      intro t ht
      have hdist : ∀ x : Circle, dist (x + (t : Circle)) x = dist (t : Circle) 0 := by
        intro x
        rw [dist_eq_norm, dist_eq_norm, sub_zero]
        congr 1
        abel
      have hshift0 : ∫ x in C, ((shiftLp (t : Circle) F) : Circle → ℂ) x ∂μ = 0 := by
        refine setIntegral_eq_zero_of_ae_eq_zero ?_
        have hpush : ∀ᵐ x ∂μ, (x + (t : Circle)) ∈ (closure E)ᶜ →
            (F : Circle → ℂ) (x + (t : Circle)) = 0 :=
          (measurePreserving_add_right μ (t : Circle)).quasiMeasurePreserving.ae hFsupp
        filter_upwards [hpush, shiftLp_coeFn (t : Circle) F] with x hx1 hx2 hxC
        rw [hx2]
        refine hx1 (hδsub ?_)
        refine Metric.thickening_subset_cthickening δ C ?_
        exact Metric.mem_thickening_iff.mpr ⟨x, hxC, by rw [hdist x]; exact ht⟩
      have hshift0i : inner ℂ v (shiftLp (t : Circle) F) = 0 := by
        rw [← hinner (shiftLp (t : Circle) F)]
        exact hshift0
      have hFCi : inner ℂ v F = 0 := by
        rw [← hinner F]
        exact hFC
      rw [inner_smul_right, inner_sub_right, hshift0i, hFCi, sub_zero, mul_zero]
    have hlimInt : Filter.Tendsto (fun t : ℝ => inner ℂ v ((t : ℂ)⁻¹ • (shiftLp (t : Circle) F - F)))
        (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (inner ℂ v ((2 * (Real.pi : ℂ) * Complex.I) • H))) :=
      tendsto_const_nhds.inner hlim
    have hlimZero : Filter.Tendsto (fun t : ℝ => inner ℂ v ((t : ℂ)⁻¹ • (shiftLp (t : Circle) F - F)))
        (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with t ht
      exact (hzero t ht).symm
    have hkey : inner ℂ v ((2 * (Real.pi : ℂ) * Complex.I) • H) = 0 :=
      tendsto_nhds_unique hlimInt hlimZero
    rw [inner_smul_right] at hkey
    have hHH : inner ℂ v H = 0 :=
      (mul_eq_zero.mp hkey).resolve_left (by simp [Complex.I_ne_zero, Real.pi_ne_zero])
    rw [← hinner H] at hHH
    exact hHH

/-- **Multiplication by a monomial does not spread the frequency support.**  If the Fourier
transform of `g ∈ ℓ²(ℤ)` vanishes a.e. outside `E` and `n ↦ n^k g(n)` is also in `ℓ²`, then the
Fourier transform of `n ↦ n^k g(n)` vanishes a.e. outside the closure of `E`.  (This is the
analytic input of Tao's weighted `ℓ²` argument: with the polynomial weight `w(n) = 1 + ε²n²` the
weighted kernels `w K_α` have the same frequency supports as the kernels `K_α`, hence are pairwise
orthogonal.) -/
theorem hasFreqSupport_mul_pow (k : ℕ) {g : ℤ → ℂ} (hg : Memℓp g 2) {E : Set Circle}
    (hE : HasFreqSupport g hg E) (hg' : Memℓp (fun n : ℤ => (n : ℂ) ^ k * g n) 2) :
    HasFreqSupport (fun n : ℤ => (n : ℂ) ^ k * g n) hg' (closure E) := by
  induction k with
  | zero =>
    have h0 : ∀ n : ℤ, g n = (fun m : ℤ => (m : ℂ) ^ 0 * g m) n := by intro n; simp
    exact (mulPow_hasFreqSupport_congr h0 hg hg').mp (mulPow_hasFreqSupport_mono hE subset_closure)
  | succ k ih =>
    have hmem : Memℓp (fun n : ℤ => (n : ℂ) ^ k * g n) 2 := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk
      · subst hk0
        exact memℓp_congr_aux (f := g) (g := fun n : ℤ => (n : ℂ) ^ 0 * g n)
          (fun n => by simp) hg
      · refine Memℓp.mono (f := fun n : ℤ => (n : ℂ) ^ k * g n)
          (g := fun n : ℤ => ‖(n : ℂ) ^ (k + 1) * g n‖) (memℓp_norm_iff.mpr hg') ?_
        intro n
        rcases eq_or_ne n 0 with h0 | hn0
        · subst h0
          simp [zero_pow (Nat.pos_iff_ne_zero.mp hk)]
        · rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_intCast]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact pow_le_pow_right₀ (by exact_mod_cast Int.one_le_abs hn0) (Nat.le_succ k)
    have ihE : HasFreqSupport (fun n : ℤ => (n : ℂ) ^ k * g n) hmem (closure E) := ih hmem
    have hmem2 : Memℓp (fun n : ℤ => (n : ℂ) * ((n : ℂ) ^ k * g n)) 2 :=
      memℓp_congr_aux (f := fun n : ℤ => (n : ℂ) ^ (k + 1) * g n)
        (g := fun n : ℤ => (n : ℂ) * ((n : ℂ) ^ k * g n)) (fun n => by rw [pow_succ']; ring) hg'
    have hlin := hasFreqSupport_mul_linear hmem ihE hmem2
    rw [closure_closure] at hlin
    exact (mulPow_hasFreqSupport_congr (f := fun n : ℤ => (n : ℂ) * ((n : ℂ) ^ k * g n))
      (g := fun n : ℤ => (n : ℂ) ^ (k + 1) * g n) (fun n => by rw [pow_succ']; ring)
      hmem2 hg').mp hlin
end Work.BourgainPlan.IonescuWainger
