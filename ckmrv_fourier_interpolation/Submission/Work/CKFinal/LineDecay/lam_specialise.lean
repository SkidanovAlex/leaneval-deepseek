import Mathlib
import Submission.Work.CKFinal.LineDecay.LamDefs

namespace Work.CKFinal.LineDecay

open Work.CKFinal MeasureTheory
open scoped Topology

/-! ## Elementary specialisations at `z = π r²`

These are the pointwise identities turning the complex-`λ` objects of `LamDefs` into the
real-`r` objects of `Defs`/`F2LayerDefs` at `z = λ = π r²`. -/

/-- `sinSqC r = 2 - 2 cos (π r²)` (the elementary `4 sin²(θ/2) = 2 - 2 cos θ`). -/
lemma sinSqC_eq_two_sub_cos (r : ℝ) :
    Work.Asymptotics.sinSqC r = ((2 - 2 * Real.cos (Real.pi * r ^ 2) : ℝ) : ℂ) := by
  rw [Work.Asymptotics.sinSqC]
  have harg : (Real.pi : ℂ) * (r : ℂ) ^ 2 / 2 = ((Real.pi * r ^ 2 / 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [harg, ← Complex.ofReal_sin]
  rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  congr 1
  rw [Real.sin_sq_eq_half_sub]; ring_nf

/-- `lamS z = 2 - e^{iz} - e^{-iz}` at a real argument is `2 - 2 cos x`. -/
lemma lamS_ofReal (x : ℝ) : lamS ((x : ℝ) : ℂ) = ((2 - 2 * Real.cos x : ℝ) : ℂ) := by
  rw [lamS]
  have h1 : Complex.I * (x : ℂ) = (x : ℂ) * Complex.I := by ring
  have h2 : -((x : ℂ) * Complex.I) = (((-x : ℝ)) : ℂ) * Complex.I := by push_cast; ring
  rw [h1, h2, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  rw [Real.cos_neg, Real.sin_neg]; push_cast; ring

/-- `lamS (π r²) = sinSqC r`. -/
lemma lamS_pi_sq (r : ℝ) :
    lamS (((Real.pi * r ^ 2 : ℝ)) : ℂ) = Work.Asymptotics.sinSqC r := by
  rw [lamS_ofReal, sinSqC_eq_two_sub_cos]

/-- The entire extension `psi1C` of `psi1` at a real argument is `psi1`. -/
lemma psi1C_ofReal (x : ℝ) : psi1C ((x : ℝ) : ℂ) = ((Work.Asymptotics.psi1 x : ℝ) : ℂ) := by
  simp only [psi1C, Work.Asymptotics.psi1]
  have h : ∀ s : ℝ, ((1 - s : ℝ) : ℂ) * Complex.cos ((s : ℂ) * (x : ℂ))
      = (((1 - s) * Real.cos (s * x) : ℝ) : ℂ) := by
    intro s
    rw [show (s : ℂ) * (x : ℂ) = ((s * x : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_mul]
  simp only [h]
  rw [intervalIntegral.integral_ofReal]; push_cast; ring

/-- `highPartC` at `z = π r²` is `highPart`. -/
lemma highPartC_specialise (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (r : ℝ) :
    highPartC G τ ((Real.pi * r ^ 2 : ℝ) : ℂ) = Work.Asymptotics.highPart G τ r := by
  simp only [highPartC, Work.Asymptotics.highPart]
  have hsub : ((Real.pi * r ^ 2 : ℝ) : ℂ) - 2 * (Real.pi : ℂ)
      = ((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub]; push_cast; ring
  rw [psi1C_ofReal, hsub, psi1C_ofReal]

/-- The split point is `H = 1`. -/
lemma hsplit_eq_one : hsplit = 1 := rfl

/-- `lowInt` at `z = π r²`, with the `Kaxis` integrand. -/
lemma lowInt_specialise (K : UpperHalfPlane → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (r : ℝ) :
    lowInt K τ ((Real.pi * r ^ 2 : ℝ) : ℂ)
      = ∫ t in (0 : ℝ)..1, Work.Kernels.Kaxis K τ t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
  rw [lowInt]
  apply intervalIntegral.integral_congr
  intro t _; simp only []
  rw [Kax_eq_Kaxis]; congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_pow]

/-- `tailInt` at `z = π r²`, with the `Kaxis` integrand. -/
lemma tailInt_specialise (K : UpperHalfPlane → UpperHalfPlane → ℂ)
    (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (r : ℝ) :
    tailInt K G τ ((Real.pi * r ^ 2 : ℝ) : ℂ)
      = ∫ t in Set.Ici (1 : ℝ), (Work.Kernels.Kaxis K τ t - Work.Asymptotics.Aexp G τ t)
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
  rw [tailInt]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ici
  intro t _; simp only []
  rw [Kax_eq_Kaxis]; congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_pow]

/-- `lowInt` at `z = π r²` as a `gaussWeight` integral (matching `layerLowK`/`P1`). -/
lemma lowInt_specialise_gw (K : UpperHalfPlane → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (r : ℝ) :
    lowInt K τ ((Real.pi * r ^ 2 : ℝ) : ℂ)
      = ∫ t in (0 : ℝ)..1, Kax K τ 0 t * Work.Asymptotics.gaussWeight r t := by
  rw [lowInt]
  apply intervalIntegral.integral_congr
  intro t _; simp only []
  rw [Work.Asymptotics.gaussWeight]; congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_pow]

/-- `tailInt` at `z = π r²` as a `gaussWeight` integral (matching `layerTruncK`). -/
lemma tailInt_specialise_gw (K : UpperHalfPlane → UpperHalfPlane → ℂ)
    (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (r : ℝ) :
    tailInt K G τ ((Real.pi * r ^ 2 : ℝ) : ℂ)
      = ∫ t in Set.Ici (1 : ℝ), (Kax K τ 0 t - Work.Asymptotics.Aexp G τ t)
          * Work.Asymptotics.gaussWeight r t := by
  rw [tailInt]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ici
  intro t _; simp only []
  rw [Work.Asymptotics.gaussWeight]; congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_pow]

/-- `phiInt` at `z = π r²` as a `gaussWeight` integral (matching `P3`). -/
lemma phiInt_specialise_gw (K : UpperHalfPlane → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (r : ℝ) :
    phiInt K τ ((Real.pi * r ^ 2 : ℝ) : ℂ)
      = ∫ t in Set.Ici (1 : ℝ), Phi K τ t * Work.Asymptotics.gaussWeight r t := by
  rw [phiInt]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ici
  intro t _; simp only []
  rw [Work.Asymptotics.gaussWeight]; congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_pow]

/-- The Gaussian term `e^{iπτr²} = gaussTerm τ r`. -/
lemma exp_eq_gaussTerm (τ : UpperHalfPlane) (r : ℝ) :
    Complex.exp (Complex.I * (τ : ℂ) * (((Real.pi * r ^ 2 : ℝ)) : ℂ))
      = Work.Kernels.gaussTerm τ r := by
  rw [Work.Kernels.gaussTerm]
  congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_pow]; ring

/-! ## The specialisations of the `LHSz`/`RHSz` objects -/

/-- `LHSzHat` at `z = π r²` is `paperLayerK`. -/
lemma LHSzHat_specialise (K : UpperHalfPlane → UpperHalfPlane → ℂ)
    (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (r : ℝ) :
    LHSzHat K G τ ((Real.pi * r ^ 2 : ℝ) : ℂ) = Work.CKFinal.paperLayerK K G r τ := by
  rw [LHSzHat, lamS_pi_sq, lowInt_specialise_gw, tailInt_specialise_gw, highPartC_specialise,
      Work.CKFinal.paperLayerK, Work.CKFinal.layerLowK, Work.CKFinal.layerTruncK]
  ring

/-- `LHSz` at `z = π r²` is `gaussTerm + paperLayer`, for `K = Kfun ℓ d`, `G = Gcusp ℓ d`. -/
lemma LHSz_specialise (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (r : ℝ) :
    LHSz (Work.Kernels.Kfun ℓ d) (Work.Asymptotics.Gcusp ℓ d) τ (((Real.pi * r ^ 2 : ℝ)) : ℂ)
      = Work.Kernels.gaussTerm τ r
        + Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r := by
  rw [LHSz, exp_eq_gaussTerm]
  congr 1
  rw [LHSzHat, lamS_pi_sq, lowInt_specialise, tailInt_specialise, highPartC_specialise,
      Work.Asymptotics.paperLayer, Work.Asymptotics.layerLow, Work.Asymptotics.layerTrunc,
      show Work.Asymptotics.sinSq r = Work.Asymptotics.sinSqC r from rfl, sinSqC_eq_two_sub_cos]
  ring

/-- `RHSz` at `z = π r²` is `P₁ + P₂ + P₃`. -/
lemma RHSz_specialise (K : UpperHalfPlane → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (r : ℝ) :
    RHSz K τ (((Real.pi * r ^ 2 : ℝ)) : ℂ) = P1 K r τ + P2 K r τ + P3 K r τ := by
  rw [RHSz, lamS_pi_sq, lowInt_specialise_gw, phiInt_specialise_gw, horInt1, horInt2,
      P1, P2, P3, hsplit_eq_one, sinSqC_eq_two_sub_cos]

/-- **Specialisation of the complex-`λ` objects at `z = π r²`.**  By definition
`LHSz K G τ (π r²)` is `gaussTerm τ r + paperLayer` and `LHSzHat K G τ (π r²)` is `paperLayerK`
(the hatted pair has no Gaussian term: `Res K̂ = 0`), while `RHSz K τ (π r²)` is `P₁ + P₂ + P₃`.
Uses `hsplit = 1`, `Kax K τ 0 t = Kaxis K τ t`, and the elementary
`sinSqC r = 2 - e^{iπr²} - e^{-iπr²}`; then `psi1C` at a real argument is `psi1`. -/
theorem lam_specialise (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) :
    (∀ r : ℝ, Work.CKFinal.LHSz (Work.Kernels.Kfun ℓ d)
        (Work.Asymptotics.Gcusp ℓ d) τ (((Real.pi * r ^ 2 : ℝ)) : ℂ)
      = Work.Kernels.gaussTerm τ r
        + Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r)
    ∧ (∀ r : ℝ, Work.CKFinal.LHSzHat (Work.Kernels.Khat ℓ d) (Work.CKFinal.Ghat ℓ d) τ
        (((Real.pi * r ^ 2 : ℝ)) : ℂ)
      = Work.CKFinal.paperLayerK (Work.Kernels.Khat ℓ d) (Work.CKFinal.Ghat ℓ d) r τ)
    ∧ (∀ r : ℝ, Work.CKFinal.RHSz (Work.Kernels.Kfun ℓ d) τ (((Real.pi * r ^ 2 : ℝ)) : ℂ)
      = Work.CKFinal.P1 (Work.Kernels.Kfun ℓ d) r τ
        + Work.CKFinal.P2 (Work.Kernels.Kfun ℓ d) r τ
        + Work.CKFinal.P3 (Work.Kernels.Kfun ℓ d) r τ)
    ∧ (∀ r : ℝ, Work.CKFinal.RHSz (Work.Kernels.Khat ℓ d) τ (((Real.pi * r ^ 2 : ℝ)) : ℂ)
      = Work.CKFinal.P1 (Work.Kernels.Khat ℓ d) r τ
        + Work.CKFinal.P2 (Work.Kernels.Khat ℓ d) r τ
        + Work.CKFinal.P3 (Work.Kernels.Khat ℓ d) r τ) := by
  exact ⟨fun r => LHSz_specialise ℓ d τ r, fun r => LHSzHat_specialise _ _ τ r,
    fun r => RHSz_specialise _ τ r, fun r => RHSz_specialise _ τ r⟩

end Work.CKFinal.LineDecay
