import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

namespace Commons.Analysis.Fourier

open MeasureTheory FourierTransform Metric
open scoped FourierTransform

set_option autoImplicit false

/-!
# A Schwartz function whose Fourier transform is supported in the unit ball

The main result of this file, `exists_schwartzMap_fourier_support_ball`, exhibits a
Schwartz function `φ` on `ℝᵈ` with `φ 0 = 1`, `supp 𝓕φ ⊆ B(0,1)` and the polynomial decay
bound `‖φ x‖ ≤ C (1 + ‖x‖²)^{-d/2}`.  Such a function is a standard "band-limited
beacon" used to build damping functions in the theory of the fractal uncertainty
principle.

The construction is: let `ψ` be a bump function which is normalised so that `∫ ψ = 1`
and whose (topological) support is contained in the unit ball, and set `φ = 𝓕ψ`.  Then
`𝓕φ = ψ(-·)` is supported in the unit ball as well, `φ 0 = ∫ ψ = 1`, and `φ`, being the
Fourier transform of a Schwartz function, is Schwartz, hence obeys the required decay.
-/

/-- Elementary inequality: `(1 + r²)^{d/2} ≤ (1 + r)^d` for `r ≥ 0`. -/
private lemma one_add_sq_rpow_half_le (d : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (1 + r ^ 2) ^ ((d : ℝ) / 2) ≤ (1 + r) ^ d := by
  have h1 : 1 + r ^ 2 ≤ ((1 + r) ^ 2 : ℝ) := by nlinarith
  have h2 : (1 + r ^ 2) ^ ((d : ℝ) / 2) ≤ ((1 + r) ^ 2 : ℝ) ^ ((d : ℝ) / 2) :=
    Real.rpow_le_rpow (by positivity) h1 (by positivity)
  have h3 : ((1 + r) ^ 2 : ℝ) ^ ((d : ℝ) / 2) = (1 + r) ^ d := by
    rw [← Real.rpow_natCast (1 + r) 2]
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + r)]
    rw [show ((2 : ℕ) : ℝ) * ((d : ℝ) / 2) = (d : ℝ) by push_cast; ring]
    exact Real.rpow_natCast (1 + r) d
  exact h2.trans_eq h3

namespace SchwartzBracketDecay

/-- Decay of a complex-valued Schwartz function `f` on `ℝᵈ` against the bracket
`(1 + ‖x‖²)^{-d/2}`.  This is proved from the Schwartz seminorms, using
`(1 + ‖x‖²)^{d/2} ≤ (1 + ‖x‖)^d`. -/
lemma le_bracket_rpow (d : ℕ) (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : EuclideanSpace ℝ (Fin d),
      ‖f x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ (-(d : ℝ) / 2) := by
  set K : ℝ := 2 ^ d * (Finset.Iic ((d, 0) : ℕ × ℕ)).sup
      (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f with hK
  have hbound : ∀ x : EuclideanSpace ℝ (Fin d), (1 + ‖x‖) ^ d * ‖f x‖ ≤ K := by
    intro x
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (d, 0)) le_rfl
      (Nat.zero_le 0) f x
    simpa [hK, norm_iteratedFDeriv_zero] using h
  refine ⟨max K 1, lt_of_lt_of_le zero_lt_one (le_max_right K 1), fun x => ?_⟩
  have hq : 0 < (1 + ‖x‖ ^ 2) ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  have key : ‖f x‖ * (1 + ‖x‖ ^ 2) ^ ((d : ℝ) / 2) ≤ max K 1 := by
    have hle : (1 + ‖x‖ ^ 2) ^ ((d : ℝ) / 2) ≤ (1 + ‖x‖) ^ d :=
      one_add_sq_rpow_half_le d ‖x‖ (norm_nonneg x)
    calc ‖f x‖ * (1 + ‖x‖ ^ 2) ^ ((d : ℝ) / 2)
        ≤ ‖f x‖ * (1 + ‖x‖) ^ d := mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ = (1 + ‖x‖) ^ d * ‖f x‖ := by ring
      _ ≤ K := hbound x
      _ ≤ max K 1 := le_max_left _ _
  have hrpow : (1 + ‖x‖ ^ 2) ^ (-(d : ℝ) / 2) = ((1 + ‖x‖ ^ 2) ^ ((d : ℝ) / 2))⁻¹ := by
    rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring, Real.rpow_neg (by positivity)]
  rw [hrpow]
  have h1 : ‖f x‖ * (1 + ‖x‖ ^ 2) ^ ((d : ℝ) / 2) * ((1 + ‖x‖ ^ 2) ^ ((d : ℝ) / 2))⁻¹
      ≤ max K 1 * ((1 + ‖x‖ ^ 2) ^ ((d : ℝ) / 2))⁻¹ :=
    mul_le_mul_of_nonneg_right key (inv_nonneg.mpr hq.le)
  rwa [mul_assoc, mul_inv_cancel₀ hq.ne', mul_one] at h1

end SchwartzBracketDecay

/-- The Fourier transform is an involution up to reflection: `𝓕 (𝓕 ψ) ξ = ψ (-ξ)`. -/
private lemma fourier_fourier_apply (d : ℕ)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) (ξ : EuclideanSpace ℝ (Fin d)) :
    FourierTransform.fourier (FourierTransform.fourier ψ) ξ = ψ (-ξ) := by
  have hfun : ∀ y, ψ y = FourierTransform.fourier (FourierTransform.fourier ψ) (-y) := by
    intro y
    have h2 : ⇑(FourierTransform.fourierInv (FourierTransform.fourier ψ)) y
        = ⇑(FourierTransform.fourier (FourierTransform.fourier ψ)) (-y) := by
      rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg,
        ← SchwartzMap.fourier_coe]
    have h3 : ⇑(FourierTransform.fourierInv (FourierTransform.fourier ψ)) y = ψ y := by
      rw [FourierTransform.fourierInv_fourier_eq]
    exact h3 ▸ h2
  simpa using (hfun (-ξ)).symm

/-- There is a Schwartz function `φ` on `ℝᵈ` with `φ 0 = 1`, whose Fourier transform is
supported in the closed unit ball, and which decays like `(1 + ‖x‖²)^{-d/2}`. -/
theorem exists_schwartzMap_fourier_support_ball {d : ℕ} (hd : 0 < d) :
    ∃ (φ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) (C : ℝ), 0 < C ∧ φ 0 = 1 ∧
      (∀ ξ, ξ ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 →
        FourierTransform.fourier φ ξ = 0) ∧
      ∀ x : EuclideanSpace ℝ (Fin d),
        ‖(φ : EuclideanSpace ℝ (Fin d) → ℂ) x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ (-(d : ℝ) / 2) := by
  -- a bump function supported in the unit ball and normalised to have integral `1`
  let bump : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := ⟨1/2, 1, by norm_num, by norm_num⟩
  let g : EuclideanSpace ℝ (Fin d) → ℂ := fun x => (bump.normed volume x : ℂ)
  have hg_cont : ContDiff ℝ (↑(⊤ : ℕ∞)) g := by
    have h1 : ContDiff ℝ (↑(⊤ : ℕ∞))
        (bump.normed (volume : Measure (EuclideanSpace ℝ (Fin d)))) :=
      bump.contDiff_normed (n := ⊤)
    exact (Complex.ofRealCLM.contDiff (n := ↑(⊤ : ℕ∞))).comp h1
  have hg_cs : HasCompactSupport g := by
    refine (bump.hasCompactSupport_normed (μ := volume)).mono ?_
    intro x hx
    simpa [g, Function.mem_support] using hx
  let ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ := hg_cs.toSchwartzMap hg_cont
  have hψ_coe : (ψ : EuclideanSpace ℝ (Fin d) → ℂ) = g := by
    funext a
    exact HasCompactSupport.toSchwartzMap_toFun hg_cs hg_cont a
  let φ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ := FourierTransform.fourier ψ
  have hφ_coe : (φ : EuclideanSpace ℝ (Fin d) → ℂ)
      = FourierTransform.fourier (ψ : EuclideanSpace ℝ (Fin d) → ℂ) :=
    SchwartzMap.fourier_coe ψ
  have hψint : ∫ v, (ψ : EuclideanSpace ℝ (Fin d) → ℂ) v = 1 := by
    rw [show (∫ v, (ψ : EuclideanSpace ℝ (Fin d) → ℂ) v) = ∫ v, g v by rw [hψ_coe]]
    rw [show (∫ v, g v) = ((∫ v, bump.normed volume v : ℝ) : ℂ) from integral_complex_ofReal]
    rw [bump.integral_normed]
    norm_num
  have hφ0 : φ 0 = 1 := by
    have h1 : (φ : EuclideanSpace ℝ (Fin d) → ℂ) 0
        = ∫ v, (ψ : EuclideanSpace ℝ (Fin d) → ℂ) v := by
      rw [hφ_coe, Real.fourier_eq]
      simp
    rw [h1, hψint]
  have hsupp : ∀ ξ, ξ ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 →
      FourierTransform.fourier φ ξ = 0 := by
    intro ξ hξ
    have hnorm : (1 : ℝ) < ‖ξ‖ := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hξ
    have hff : FourierTransform.fourier φ ξ = ψ (-ξ) := by
      show FourierTransform.fourier (FourierTransform.fourier ψ) ξ = ψ (-ξ)
      exact fourier_fourier_apply d ψ ξ
    rw [hff, hψ_coe]
    have hb : bump (-ξ) = 0 := by
      apply ContDiffBump.zero_of_le_dist
      show (1 : ℝ) ≤ dist (-ξ) 0
      rw [dist_eq_norm]
      simpa using hnorm.le
    have hzero : bump.normed (volume : Measure (EuclideanSpace ℝ (Fin d))) (-ξ) = 0 := by
      rw [bump.normed_def (-ξ), hb]
      simp
    simp [g, hzero]
  obtain ⟨C, hCpos, hC⟩ := SchwartzBracketDecay.le_bracket_rpow d φ
  exact ⟨φ, C, hCpos, hφ0, hsupp, hC⟩

end Commons.Analysis.Fourier