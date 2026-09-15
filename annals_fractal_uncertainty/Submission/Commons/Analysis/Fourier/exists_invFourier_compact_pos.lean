import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.Analysis.Fourier.half_integral_le_re_fourierInv

namespace Commons.Analysis.Fourier

open MeasureTheory FourierTransform
open scoped FourierTransform RealInnerProductSpace Convolution ComplexConjugate ContDiff

set_option autoImplicit false

/-- The Fourier transform of the reflection `x ↦ f (-x)` of a real-valued function `f` is the
complex conjugate of the Fourier transform of `f`. -/
lemma fourier_comp_neg_eq_conj {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    {f : V → ℂ} (hf : ∀ x, (f x).im = 0) (ξ : V) :
    𝓕 (fun x => f (-x)) ξ = conj (𝓕 f ξ) := by
  have hL : 𝓕 (fun x => f (-x)) ξ = ∫ v, Real.fourierChar (inner ℝ v ξ) • f v := by
    rw [← Real.fourierInv_eq_fourier_comp_neg f, Real.fourierInv_eq]
  rw [hL, Real.fourier_eq, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have hchar : ((Real.fourierChar (inner ℝ v ξ) : Circle) : ℂ) * f v
      = conj (((Real.fourierChar (- inner ℝ v ξ) : Circle) : ℂ) * f v) := by
    rw [map_mul, Complex.conj_eq_iff_im.mpr (hf v), ← Circle.coe_inv_eq_conj,
      AddChar.map_neg_eq_inv, inv_inv]
  simpa [Circle.smul_def] using hchar

theorem exists_invFourier_compact_pos (n : ℕ) :
    ∃ φ ψ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
      HasCompactSupport (⇑ψ) ∧
      (∀ x, 0 ≤ (φ x).re) ∧
      (∀ x, ‖x‖ ≤ 1 → 1 ≤ (φ x).re) ∧
      (∀ x, φ x = ∫ ξ, ψ ξ * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((inner ℝ x ξ : ℝ) : ℂ))) := by
  classical
  let bump : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := ⟨1 / 16, 1 / 8, by norm_num, by norm_num⟩
  let ρ : EuclideanSpace ℝ (Fin n) → ℝ := fun x => 2 * bump.normed volume x
  have hbump_diff : ContDiff ℝ ∞ (bump.normed (volume : Measure (EuclideanSpace ℝ (Fin n)))) :=
    bump.contDiff_normed
  have hbump_cs : HasCompactSupport (bump.normed (volume : Measure (EuclideanSpace ℝ (Fin n)))) :=
    bump.hasCompactSupport_normed
  have hρ_diff : ContDiff ℝ ∞ ρ := by
    have h2 : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => (2 : ℝ) * bump.normed volume x) :=
      (contDiff_const (c := (2 : ℝ))).mul hbump_diff
    simpa [ρ] using h2
  have hρ_cs : HasCompactSupport ρ := by
    refine hbump_cs.mono ?_
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h
    exact hx (by simp [ρ, h])
  have hρc_diff : ContDiff ℝ ∞ (fun x => (ρ x : ℂ)) :=
    (Complex.ofRealCLM.contDiff).comp hρ_diff
  have hρc_cs : HasCompactSupport (fun x => (ρ x : ℂ)) := hρ_cs.mono (by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h
    exact hx (by simp [h]))
  have hρnn : ∀ x, 0 ≤ ρ x := by
    intro x
    simp only [ρ]
    exact mul_nonneg (by norm_num) (bump.nonneg_normed x)
  have hρint : Integrable ρ volume :=
    hρ_diff.continuous.integrable_of_hasCompactSupport hρ_cs
  have hρsupp : ∀ w, 1 / 8 < ‖w‖ → ρ w = 0 := by
    intro w hw
    have hdist : bump.rOut ≤ dist w 0 := by
      rw [dist_eq_norm]
      simp only [bump, sub_zero]
      linarith
    have hb : (bump : EuclideanSpace ℝ (Fin n) → ℝ) w = 0 :=
      ContDiffBump.zero_of_le_dist bump hdist
    simp [ρ, ContDiffBump.normed_def, hb]
  have hρintval : ∫ w, ρ w = 2 := by
    have h2 : (∫ w, ρ w) = ∫ w, 2 * bump.normed volume w := rfl
    rw [h2, integral_const_mul, bump.integral_normed]
    norm_num
  let G : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ :=
    HasCompactSupport.toSchwartzMap hρc_cs hρc_diff
  have hG_coe : ⇑G = fun x => (ρ x : ℂ) :=
    funext (fun x => HasCompactSupport.toSchwartzMap_toFun hρc_cs hρc_diff x)
  have hG_re : ∀ x, (⇑G x).im = 0 := by
    intro x
    rw [hG_coe]
    simp
  have hG_cs : HasCompactSupport (⇑G) := by rw [hG_coe]; exact hρc_cs
  let Ginv : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ := 𝓕⁻ G
  let ρneg : EuclideanSpace ℝ (Fin n) → ℂ := fun x => (ρ (-x) : ℂ)
  have hρneg_diff : ContDiff ℝ ∞ ρneg := by
    have h : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => (ρ (-x) : ℂ)) :=
      hρc_diff.comp contDiff_neg
    simpa [ρneg] using h
  have hρneg_cs : HasCompactSupport ρneg := by
    convert (hρc_cs.comp_homeomorph (Homeomorph.neg (EuclideanSpace ℝ (Fin n)))) using 1
    ext x
    rfl
  let H : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ :=
    HasCompactSupport.toSchwartzMap hρneg_cs hρneg_diff
  have hH_coe : ⇑H = fun x => (ρ (-x) : ℂ) :=
    funext (fun x => HasCompactSupport.toSchwartzMap_toFun hρneg_cs hρneg_diff x)
  have hH_G : ⇑H = fun x => ⇑G (-x) := by
    rw [hH_coe, hG_coe]
  have hH_cs : HasCompactSupport (⇑H) := by rw [hH_coe]; exact hρneg_cs
  let B : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ
  let ψ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ := SchwartzMap.convolution B G H
  let φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ := 𝓕⁻ ψ
  have hFH : ∀ ξ, 𝓕 (⇑H) ξ = conj (𝓕 (⇑G) ξ) := by
    intro ξ
    rw [hH_G]
    exact fourier_comp_neg_eq_conj hG_re ξ
  have hψ_coe : ⇑ψ = convolution (⇑G) (⇑H) B volume :=
    funext (fun x => SchwartzMap.convolution_apply B G H x)
  have hψ_cs : HasCompactSupport (⇑ψ) := by
    rw [hψ_coe]
    exact hG_cs.convolution B hH_cs
  have hφ_val : ∀ x, ⇑φ x = ((‖⇑Ginv x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    calc ⇑φ x = 𝓕⁻ (⇑ψ) x := by rw [SchwartzMap.fourierInv_coe]
      _ = 𝓕 (⇑ψ) (-x) := Real.fourierInv_eq_fourier_neg _ _
      _ = 𝓕 (convolution (⇑G) (⇑H) B volume) (-x) := by rw [hψ_coe]
      _ = B (𝓕 (⇑G) (-x)) (𝓕 (⇑H) (-x)) :=
            Real.fourier_bilin_convolution_eq B G.integrable H.integrable _
      _ = 𝓕 (⇑G) (-x) * conj (𝓕 (⇑G) (-x)) := by rw [hFH]; rfl
      _ = ((‖𝓕 (⇑G) (-x)‖ ^ 2 : ℝ) : ℂ) := by
            rw [Complex.mul_conj']
            push_cast
            ring
      _ = ((‖⇑Ginv x‖ ^ 2 : ℝ) : ℂ) := by
            rw [show ⇑Ginv = 𝓕⁻ (⇑G) from SchwartzMap.fourierInv_coe G,
              Real.fourierInv_eq_fourier_neg]
  have hφ_re : ∀ x, (⇑φ x).re = ‖⇑Ginv x‖ ^ 2 := by
    intro x
    rw [hφ_val x]
    exact Complex.ofReal_re _
  have hnonneg : ∀ x, 0 ≤ (φ x).re := by
    intro x
    rw [hφ_re x]
    positivity
  have hge : ∀ x, ‖x‖ ≤ 1 → 1 ≤ (φ x).re := by
    intro x hx
    rw [hφ_re x]
    have hlow : (1 : ℝ) ≤ (⇑Ginv x).re := by
      have hcoe : ⇑Ginv x = 𝓕⁻ (fun w => (ρ w : ℂ)) x := by
        rw [show ⇑Ginv = 𝓕⁻ (⇑G) from SchwartzMap.fourierInv_coe G, hG_coe]
      rw [hcoe]
      have h := half_integral_le_re_fourierInv hρnn hρint hρsupp x hx
      rw [hρintval] at h
      linarith
    have hnorm : (1 : ℝ) ≤ ‖⇑Ginv x‖ := le_trans hlow (Complex.re_le_norm _)
    nlinarith [hnorm, norm_nonneg (⇑Ginv x)]
  have hφ_eq : ∀ x,
      φ x = ∫ ξ, ψ ξ * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((inner ℝ x ξ : ℝ) : ℂ)) := by
    intro x
    rw [show ⇑φ = 𝓕⁻ (⇑ψ) from SchwartzMap.fourierInv_coe ψ, Real.fourierInv_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    rw [real_inner_comm ξ x]
    have hexp : Complex.exp (↑(2 * Real.pi * (inner ℝ ξ x : ℝ)) * Complex.I)
        = Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((inner ℝ ξ x : ℝ) : ℂ)) := by
      congr 1
      push_cast
      ring
    rw [hexp, mul_comm]
  exact ⟨φ, ψ, hψ_cs, hnonneg, hge, hφ_eq⟩

end Commons.Analysis.Fourier