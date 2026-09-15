import Mathlib
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_sub_id_rh_bound
import Submission.Commons.NumberTheory.DirichletCharacter.completedLFunction_eq
import Submission.Commons.NumberTheory.DirichletCharacter.completedLFunction_ne_zero_of_one_lt_re
import Submission.Commons.NumberTheory.DirichletCharacter.rootNumber_norm_eq_one
import Submission.Commons.NumberTheory.DirichletCharacter.Even_inv
import Submission.Commons.NumberTheory.DirichletCharacter.Odd_inv
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_L_two_norm_le_one
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_completedLFunction_conj
import Submission.Commons.NumberTheory.DirichletCharacter.lFunction_zeroSet_box_finite
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_horizontal_argument_variation_bound
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_le
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le

open Complex DirichletCharacter
open scoped Real Topology BigOperators

namespace Commons.NumberTheory.DirichletCharacter

noncomputable section

/-! ## 1. The contour integral of `logDeriv` over a rectangle

If `f` is entire and does not vanish on the closed rectangle with corners `z`, `w`, then
`∮_{∂R} f'/f = 0`.  This is the contrapositive form of the argument principle that we use
to force zeros of `Λ(·,χ)` inside a rectangle. -/

lemma rectInt_logDeriv_eq_zero_of_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {z w : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hne : ∀ s : ℂ, z.re ≤ s.re → s.re ≤ w.re → z.im ≤ s.im → s.im ≤ w.im → f s ≠ 0) :
    Commons.NumberTheory.Zeta.rectInt z w (logDeriv f) = 0 := by
  rw [Commons.NumberTheory.Zeta.rectInt]
  refine Complex.integral_boundary_rect_eq_zero_of_differentiableOn (logDeriv f) z w ?_
  intro s hs
  rw [Complex.mem_reProdIm] at hs
  obtain ⟨hre, him⟩ := hs
  rw [Set.uIcc_of_le (le_of_lt hzre)] at hre
  rw [Set.uIcc_of_le (le_of_lt hzim)] at him
  have hfs : f s ≠ 0 := hne s hre.1 hre.2 him.1 him.2
  have : logDeriv f = fun u => deriv f u / f u := rfl
  rw [this]
  exact DifferentiableWithinAt.div (hf.deriv.differentiableAt.differentiableWithinAt)
    hf.differentiableAt.differentiableWithinAt hfs

/-! ## 2. Archimedean (digamma) bounds -/

/-- Real-part lower bound for the digamma function: on `1/2 ≤ Re z ≤ 8`,
`Re ψ(z) ≥ log ‖z‖ - 2`. -/
lemma digamma_re_ge_log (z : ℂ) (h1 : (1 : ℝ) / 2 ≤ z.re) (h2 : z.re ≤ 8) :
    Real.log ‖z‖ - 2 ≤ (Complex.digamma z).re := by
  have h := Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_le z.re z.im h1 h2
  rw [Complex.re_add_im z] at h
  set w : ℂ := Complex.digamma z - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹ with hw
  have hwle : ‖w‖ ≤ (1 : ℝ) / 2 := h
  have hre : -(1 / 2 : ℝ) ≤ w.re := by
    have h' := Complex.abs_re_le_norm w
    rw [abs_le] at h'
    linarith [h'.1]
  have hlog : (Complex.log z).re = Real.log ‖z‖ := Complex.log_re z
  have hzre : 0 < z.re := by linarith
  have hinv : (z⁻¹).re ≤ 2 := by
    rw [Complex.inv_re, Complex.normSq_apply]
    have hsq : 0 < z.re * z.re := mul_pos hzre hzre
    have hpos : 0 < z.re * z.re + z.im * z.im := by nlinarith [sq_nonneg z.im]
    rw [div_le_iff₀ hpos]
    nlinarith [hzre]
  have h2inv : (((2 : ℂ)⁻¹) * z⁻¹).re = (1 / 2) * (z⁻¹).re := by
    rw [Complex.mul_re]; norm_num
  have hz : Complex.digamma z = Complex.log z - ((2 : ℂ)⁻¹) * z⁻¹ + w := by
    rw [hw]; ring
  have hmain : (Complex.digamma z).re = (Complex.log z).re - (((2 : ℂ)⁻¹) * z⁻¹).re + w.re := by
    rw [hz]; simp
  rw [hmain, hlog, h2inv]
  linarith

/-- Norm bound for the digamma function on the strip `-1/2 ≤ Re z ≤ 8`, valid for `‖z‖ ≥ 1`:
`‖ψ(z)‖ ≤ log (2 + |Im z|) + 3`. -/
lemma digamma_norm_le (z : ℂ) (hre1 : -(1 : ℝ) / 2 ≤ z.re) (hre2 : z.re ≤ 8)
    (hz : 1 ≤ ‖z‖) :
    ‖Complex.digamma z‖ ≤ Real.log (2 + |z.im|) + 3 := by
  rcases lt_or_ge ((1 : ℝ) / 2) z.re with h | h
  · have hmid := Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le z.re z.im h.le hre2
    rw [Complex.re_add_im z] at hmid
    linarith
  · have hne : ∀ m : ℕ, z ≠ -(m : ℂ) := by
      intro m hm
      have h1 : z.re = -(m : ℝ) := by rw [hm]; simp
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0
        rw [hm] at hz
        simp at hz
        linarith
      · have h2 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hpos
        linarith [hre1]
    have hshift : Complex.digamma z = Complex.digamma (z + 1) - 1 / z := by
      have h₁ := Complex.digamma_apply_add_one z hne
      rw [h₁]; ring
    have hz1re : (1 : ℝ) / 2 ≤ (z + 1).re := by simp; linarith
    have hz1re2 : (z + 1).re ≤ 8 := by simp; linarith
    have hmid := Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le (z + 1).re (z + 1).im
      hz1re hz1re2
    rw [Complex.re_add_im (z + 1)] at hmid
    have him : (z + 1).im = z.im := by simp
    rw [him] at hmid
    have hnorm1 : ‖(1 : ℂ) / z‖ ≤ 1 := by
      rw [norm_div, norm_one, one_div]
      exact inv_le_one_of_one_le₀ hz
    rw [hshift]
    calc ‖Complex.digamma (z + 1) - 1 / z‖ ≤ ‖Complex.digamma (z + 1)‖ + ‖(1 : ℂ) / z‖ :=
          norm_sub_le _ _
      _ ≤ (Real.log (2 + |z.im|) + 2) + 1 := by linarith
      _ = Real.log (2 + |z.im|) + 3 := by ring



lemma logDeriv_mul' (f g : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℂ f z)
    (hg : DifferentiableAt ℂ g z) (hf0 : f z ≠ 0) (hg0 : g z ≠ 0) :
    logDeriv (f * g) z = logDeriv f z + logDeriv g z := by
  have h1 : logDeriv (f * g) z = (deriv f z * g z + f z * deriv g z) / (f z * g z) := by
    rw [logDeriv_apply, deriv_mul hf hg, Pi.mul_apply]
  rw [h1, logDeriv_apply, logDeriv_apply]
  field_simp

lemma logDeriv_GammaR (z : ℂ) (hz : ∀ m : ℕ, z / 2 ≠ -(m : ℂ)) :
    logDeriv Complex.Gammaℝ z =
      -(1 / 2 : ℂ) * Complex.log (π : ℂ) + (1 / 2 : ℂ) * Complex.digamma (z / 2) := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hinner1 : HasDerivAt (fun z : ℂ => -z / 2) ((-1 : ℂ) / 2) z := by
    simpa using ((hasDerivAt_id z).neg.div_const (2 : ℂ))
  have houter1 : HasDerivAt (fun w : ℂ => (π : ℂ) ^ w)
      ((π : ℂ) ^ (-z / 2) * Complex.log (π : ℂ)) (-z / 2) :=
    (Complex.hasStrictDerivAt_const_cpow (Or.inl hpi)).hasDerivAt
  have hcomp1 : HasDerivAt (fun z : ℂ => (π : ℂ) ^ (-z / 2))
      ((π : ℂ) ^ (-z / 2) * Complex.log (π : ℂ) * ((-1 : ℂ) / 2)) z :=
    houter1.comp z hinner1
  have h1 : logDeriv (fun z : ℂ => (π : ℂ) ^ (-z / 2)) z =
      -(1 / 2 : ℂ) * Complex.log (π : ℂ) := by
    rw [logDeriv_apply, hcomp1.deriv]
    have hne : (π : ℂ) ^ (-z / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
    field_simp
  have hderiv : deriv Complex.Gamma (z / 2) = Complex.digamma (z / 2) * Complex.Gamma (z / 2) := by
    have h : logDeriv Complex.Gamma (z / 2) = Complex.digamma (z / 2) := by
      rw [← Complex.digamma_def]
    rw [logDeriv_apply] at h
    have hg : Complex.Gamma (z / 2) ≠ 0 := Complex.Gamma_ne_zero hz
    rw [div_eq_iff hg] at h
    rw [← h]
  have hinner2 : HasDerivAt (fun z : ℂ => z / 2) ((1 : ℂ) / 2) z := by
    simpa using ((hasDerivAt_id z).div_const (2 : ℂ))
  have houter2 : HasDerivAt Complex.Gamma
      (Complex.digamma (z / 2) * Complex.Gamma (z / 2)) (z / 2) := by
    rw [← hderiv]
    exact (Complex.differentiableAt_Gamma (z / 2) hz).hasDerivAt
  have hcomp2 : HasDerivAt (fun z : ℂ => Complex.Gamma (z / 2))
      (Complex.digamma (z / 2) * Complex.Gamma (z / 2) * ((1 : ℂ) / 2)) z :=
    houter2.comp z hinner2
  have h2 : logDeriv (fun z : ℂ => Complex.Gamma (z / 2)) z =
      (1 / 2 : ℂ) * Complex.digamma (z / 2) := by
    rw [logDeriv_apply, hcomp2.deriv]
    have hg : Complex.Gamma (z / 2) ≠ 0 := Complex.Gamma_ne_zero hz
    field_simp
  have hf0 : (π : ℂ) ^ (-z / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  have hg0 : Complex.Gamma (z / 2) ≠ 0 := Complex.Gamma_ne_zero hz
  have hdf : DifferentiableAt ℂ (fun z : ℂ => (π : ℂ) ^ (-z / 2)) z :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl hpi)
  have hdg : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) z :=
    (Complex.differentiableAt_Gamma (z / 2) hz).comp z (by fun_prop)
  rw [show Complex.Gammaℝ = (fun z : ℂ => (π : ℂ) ^ (-z / 2)) * (fun z : ℂ => Complex.Gamma (z / 2)) by
      funext w; rw [Complex.Gammaℝ_def]; rfl,
    logDeriv_mul' _ _ z hdf hdg hf0 hg0, h1, h2]

/-- `logDeriv` of `u ↦ c ^ (1/2 - u)`. -/
lemma logDeriv_cpow_half_sub (c : ℂ) (hc : c ≠ 0) (u : ℂ) :
    logDeriv (fun z : ℂ => c ^ ((1 / 2 : ℂ) - z)) u = -Complex.log c := by
  have hinner : HasDerivAt (fun z : ℂ => (1 / 2 : ℂ) - z) (-1) u := by
    exact (hasDerivAt_id u).const_sub ((1 / 2 : ℂ))
  have houter : HasDerivAt (fun w : ℂ => c ^ w)
      (c ^ ((1 / 2 : ℂ) - u) * Complex.log c) ((1 / 2 : ℂ) - u) :=
    (Complex.hasStrictDerivAt_const_cpow (Or.inl hc)).hasDerivAt
  have hcomp : HasDerivAt (fun z : ℂ => c ^ ((1 / 2 : ℂ) - z))
      (c ^ ((1 / 2 : ℂ) - u) * Complex.log c * (-1)) u :=
    houter.comp u hinner
  rw [logDeriv_apply, hcomp.deriv]
  have hne : c ^ ((1 - 2 * u) / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hc)
  field_simp

/-- The inverse of a non-trivial Dirichlet character is non-trivial. -/
lemma inv_ne_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) : χ⁻¹ ≠ 1 := by
  intro h
  apply hχ
  calc χ = (χ⁻¹)⁻¹ := by rw [inv_inv]
    _ = (1 : DirichletCharacter ℂ N)⁻¹ := by rw [h]
    _ = 1 := by simp

/-- Functional equation for the logarithmic derivative of the completed L-function. -/
lemma logDeriv_completedLFunction_one_sub {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (hχne : χ ≠ 1) {s : ℂ}
    (hs : DirichletCharacter.completedLFunction χ s ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) s =
      - Complex.log (N : ℂ) -
        logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) (1 - s) := by
  set Λ := DirichletCharacter.completedLFunction χ with hΛ
  set Λi := DirichletCharacter.completedLFunction (χ⁻¹) with hΛi
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hc0 : χ.rootNumber ≠ 0 := by
    intro h
    have := rootNumber_norm_eq_one χ hχ
    rw [h] at this
    norm_num at this
  have hFE : ∀ u : ℂ, Λ u = (N : ℂ) ^ ((1 / 2 : ℂ) - u) * χ.rootNumber * Λi (1 - u) := by
    intro u
    simpa [hΛ, hΛi] using completedLFunction_eq χ hχ u
  set F : ℂ → ℂ := fun u => (N : ℂ) ^ ((1 / 2 : ℂ) - u) * χ.rootNumber with hF
  set G : ℂ → ℂ := fun u => Λi (1 - u) with hG
  have hFG : ∀ u, Λ u = F u * G u := by
    intro u; rw [hFE u, hF, hG]
  have hF0 : F s ≠ 0 := by
    rw [hF]
    exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hN)) hc0
  have hG0 : G s ≠ 0 := by
    intro h
    apply hs
    rw [hFG s, h, mul_zero]
  have hFd : DifferentiableAt ℂ F s := by
    rw [hF]
    exact (DifferentiableAt.const_cpow (by fun_prop) (Or.inl hN)).mul_const _
  have hΛid : Differentiable ℂ Λi :=
    differentiable_completedLFunction (χ := χ⁻¹) (inv_ne_one hχne)
  have hGd : DifferentiableAt ℂ G s := by
    rw [hG]
    exact hΛid.differentiableAt.comp s (by fun_prop)
  have hFderiv : logDeriv F s = -Complex.log (N : ℂ) := by
    rw [hF, logDeriv_mul_const (f := fun u : ℂ => (N : ℂ) ^ ((1 / 2 : ℂ) - u)) s
      χ.rootNumber hc0]
    exact logDeriv_cpow_half_sub (N : ℂ) hN s
  have hGderiv : logDeriv G s = - logDeriv Λi (1 - s) := by
    rw [hG]
    have hcomp : (fun u : ℂ => Λi (1 - u)) = Λi ∘ (fun u : ℂ => 1 - u) := rfl
    rw [hcomp, logDeriv_comp _ (by fun_prop)]
    · have hd : deriv (fun u : ℂ => 1 - u) s = -1 := by
        simpa using (hasDerivAt_id s).const_sub (1 : ℂ)
      rw [hd]; ring
    · exact hΛid.differentiableAt
  rw [show Λ = F * G from funext hFG, logDeriv_mul' F G s hFd hGd hF0 hG0, hFderiv, hGderiv]
  ring


/-! ## 4. The archimedean factor: non-vanishing, differentiability, logarithmic derivative -/

/-- `Γℝ` is differentiable at every point where it does not vanish. -/
lemma differentiableAt_Gammaℝ_of_ne_zero {u : ℂ} (hu : Complex.Gammaℝ u ≠ 0) :
    DifferentiableAt ℂ Complex.Gammaℝ u := by
  have h : DifferentiableAt ℂ (fun s => (Complex.Gammaℝ s)⁻¹) u :=
    Complex.differentiable_Gammaℝ_inv.differentiableAt
  have hinv : DifferentiableAt ℂ (fun s => ((Complex.Gammaℝ s)⁻¹)⁻¹) u := h.inv (inv_ne_zero hu)
  have hfun : (fun s : ℂ => ((Complex.Gammaℝ s)⁻¹)⁻¹) = Complex.Gammaℝ := by
    funext s; rw [inv_inv]
  rwa [hfun] at hinv

/-- `Γℝ` does not vanish on the open right half-plane. -/
lemma Gammaℝ_ne_zero_of_re_pos {u : ℂ} (hu : 0 < u.re) : Complex.Gammaℝ u ≠ 0 := by
  intro h0
  rw [Complex.Gammaℝ_eq_zero_iff] at h0
  obtain ⟨n, hn⟩ := h0
  have h1 : u.re = -(2 * n : ℝ) := by rw [hn]; simp
  have h2 : (0 : ℝ) ≤ (2 * n : ℝ) := by positivity
  linarith

/-- The archimedean gamma factor does not vanish on the open right half-plane. -/
lemma gammaFactor_ne_zero_of_pos_re {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) : DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [h.gammaFactor_def]
    refine Gammaℝ_ne_zero_of_re_pos ?_
    simp only [Complex.add_re, Complex.one_re]
    linarith

lemma differentiableAt_gammaFactor_of_re_pos {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) s := by
  rcases χ.even_or_odd with h | h
  · rw [show DirichletCharacter.gammaFactor χ = Complex.Gammaℝ from funext h.gammaFactor_def]
    exact differentiableAt_Gammaℝ_of_ne_zero (Gammaℝ_ne_zero_of_re_pos hs)
  · rw [show DirichletCharacter.gammaFactor χ = fun u => Complex.Gammaℝ (u + 1) from
      funext (fun u => h.gammaFactor_def u)]
    refine (differentiableAt_Gammaℝ_of_ne_zero ?_).comp s (by fun_prop)
    refine Gammaℝ_ne_zero_of_re_pos ?_
    simp only [Complex.add_re, Complex.one_re]
    linarith

/-- Logarithmic derivative of a translate of `Γℝ`. -/
lemma logDeriv_GammaR_shift (a : ℂ) (s : ℂ) (hz : ∀ m : ℕ, (s + a) / 2 ≠ -(m : ℂ)) :
    logDeriv (fun u : ℂ => Complex.Gammaℝ (u + a)) s =
      -(1 / 2 : ℂ) * Complex.log (π : ℂ) + (1 / 2 : ℂ) * Complex.digamma ((s + a) / 2) := by
  have hΓ : DifferentiableAt ℂ Complex.Gammaℝ (s + a) := by
    refine differentiableAt_Gammaℝ_of_ne_zero ?_
    intro h0
    rw [Complex.Gammaℝ_eq_zero_iff] at h0
    obtain ⟨n, hn⟩ := h0
    exact hz n (by rw [hn]; ring)
  have h1 : HasDerivAt (fun u : ℂ => u + a) 1 s := by
    simpa using (hasDerivAt_id s).add_const a
  have h2 : HasDerivAt Complex.Gammaℝ (deriv Complex.Gammaℝ (s + a)) (s + a) := hΓ.hasDerivAt
  have h3 := h2.comp s h1
  rw [logDeriv_apply]
  have hfun : (fun u : ℂ => Complex.Gammaℝ (u + a)) = Complex.Gammaℝ ∘ (fun u : ℂ => u + a) := rfl
  rw [hfun, h3.deriv, mul_one, ← logDeriv_apply]
  exact logDeriv_GammaR (s + a) hz

/-- Logarithmic derivative of the archimedean gamma factor for even characters. -/
lemma logDeriv_gammaFactor_even_formula {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.Even)
    (s : ℂ) (hz : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) :
    logDeriv (DirichletCharacter.gammaFactor χ) s =
      -(1 / 2 : ℂ) * Complex.log (π : ℂ) + (1 / 2 : ℂ) * Complex.digamma (s / 2) := by
  have hg : DirichletCharacter.gammaFactor χ = fun u => Complex.Gammaℝ (u + 0) := by
    funext u; rw [hχ.gammaFactor_def]; simp
  rw [hg]
  simpa using logDeriv_GammaR_shift 0 s (by simpa using hz)

/-- Logarithmic derivative of the archimedean gamma factor for odd characters. -/
lemma logDeriv_gammaFactor_odd_formula {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.Odd)
    (s : ℂ) (hz : ∀ m : ℕ, (s + 1) / 2 ≠ -(m : ℂ)) :
    logDeriv (DirichletCharacter.gammaFactor χ) s =
      -(1 / 2 : ℂ) * Complex.log (π : ℂ) + (1 / 2 : ℂ) * Complex.digamma ((s + 1) / 2) := by
  have hg : DirichletCharacter.gammaFactor χ = fun u => Complex.Gammaℝ (u + 1) := by
    funext u; rw [hχ.gammaFactor_def]
  rw [hg]
  exact logDeriv_GammaR_shift 1 s hz

/-- Splitting `logDeriv Λ` into the archimedean factor and the L-function. -/
lemma logDeriv_completedLFunction_eq_add_archimedean {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {s : ℂ} (hs0 : s ≠ 0) (hsre : 0 < s.re)
    (hs : DirichletCharacter.LFunction χ s ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) s =
      logDeriv (DirichletCharacter.gammaFactor χ) s +
        logDeriv (DirichletCharacter.LFunction χ) s := by
  have hU : {u : ℂ | 0 < u.re} ∈ 𝓝 s :=
    (isOpen_lt continuous_const continuous_re).mem_nhds hsre
  have hev : DirichletCharacter.completedLFunction χ =ᶠ[𝓝 s]
      (fun u => DirichletCharacter.gammaFactor χ u * DirichletCharacter.LFunction χ u) :=
    Filter.eventually_of_mem hU (fun u hu => by
      have hu0 : u ≠ 0 := by intro h; rw [h] at hu; simp at hu
      have hγ : DirichletCharacter.gammaFactor χ u ≠ 0 := gammaFactor_ne_zero_of_pos_re χ hu
      have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ u (Or.inl hu0)
      show DirichletCharacter.completedLFunction χ u =
        DirichletCharacter.gammaFactor χ u * DirichletCharacter.LFunction χ u
      rw [h]
      exact (mul_div_cancel₀ (a := DirichletCharacter.completedLFunction χ u) hγ).symm)
  rw [(logDeriv_congr_nhds hev).eq_of_nhds]
  exact logDeriv_mul' _ _ s (differentiableAt_gammaFactor_of_re_pos χ hsre)
    (DirichletCharacter.differentiableAt_LFunction χ s (Or.inr hχ))
    (gammaFactor_ne_zero_of_pos_re χ hsre) hs

/-! ## 5. The vertical main term -/

lemma norm_two_add_mul_I (t : ℝ) : ‖(2 : ℂ) + (t : ℂ) * Complex.I‖ = Real.sqrt (4 + t ^ 2) := by
  have hsq : ‖(2 : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 = (Real.sqrt (4 + t ^ 2)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Real.sq_sqrt (by positivity)]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_mul]
    norm_num
    ring
  nlinarith [hsq, norm_nonneg ((2 : ℂ) + (t : ℂ) * Complex.I), Real.sqrt_nonneg (4 + t ^ 2)]

lemma norm_three_add_mul_I (t : ℝ) : ‖(3 : ℂ) + (t : ℂ) * Complex.I‖ = Real.sqrt (9 + t ^ 2) := by
  have hsq : ‖(3 : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 = (Real.sqrt (9 + t ^ 2)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Real.sq_sqrt (by positivity)]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_mul]
    norm_num
    ring
  nlinarith [hsq, norm_nonneg ((3 : ℂ) + (t : ℂ) * Complex.I), Real.sqrt_nonneg (9 + t ^ 2)]

lemma norm_two_sub_mul_I (t : ℝ) : ‖(2 : ℂ) - (t : ℂ) * Complex.I‖ = Real.sqrt (4 + t ^ 2) := by
  have hsq : ‖(2 : ℂ) - (t : ℂ) * Complex.I‖ ^ 2 = (Real.sqrt (4 + t ^ 2)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Real.sq_sqrt (by positivity)]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_sub]
    norm_num
    ring
  nlinarith [hsq, norm_nonneg ((2 : ℂ) - (t : ℂ) * Complex.I), Real.sqrt_nonneg (4 + t ^ 2)]

lemma norm_three_sub_mul_I (t : ℝ) : ‖(3 : ℂ) - (t : ℂ) * Complex.I‖ = Real.sqrt (9 + t ^ 2) := by
  have hsq : ‖(3 : ℂ) - (t : ℂ) * Complex.I‖ ^ 2 = (Real.sqrt (9 + t ^ 2)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Real.sq_sqrt (by positivity)]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_sub]
    norm_num
    ring
  nlinarith [hsq, norm_nonneg ((3 : ℂ) - (t : ℂ) * Complex.I), Real.sqrt_nonneg (9 + t ^ 2)]

/-- Real part of `-(1/2) * log π + (1/2) * ψ(w)`. -/
lemma arch_re_eq (w : ℂ) :
    (-(1 / 2 : ℂ) * Complex.log (π : ℂ) + (1 / 2 : ℂ) * Complex.digamma w).re =
      -(1 / 2) * Real.log Real.pi + (1 / 2) * (Complex.digamma w).re := by
  rw [Complex.add_re, Complex.mul_re, Complex.mul_re, Complex.neg_re, Complex.log_ofReal_re]
  norm_num

/-- Real-part lower bound for the archimedean part of `logDeriv Λ` at `s = 2 + it`. -/
lemma arch_re_lower {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {t : ℝ} (ht : 2 ≤ t) :
    -(1 / 2) * Real.log Real.pi + (1 / 2) * Real.log (t / 2) - 1 ≤
      (logDeriv (DirichletCharacter.gammaFactor χ) ((2 : ℂ) + (t : ℂ) * Complex.I)).re := by
  have ht2 : (0 : ℝ) < t := by linarith
  rcases χ.even_or_odd with h | h
  · have hz : ∀ m : ℕ, ((2 : ℂ) + (t : ℂ) * Complex.I) / 2 ≠ -(m : ℂ) := by
      intro m hm
      have hre := congrArg Complex.im hm
      simp at hre
      linarith
    rw [logDeriv_gammaFactor_even_formula h _ hz, arch_re_eq]
    have hd := digamma_re_ge_log (((2 : ℂ) + (t : ℂ) * Complex.I) / 2)
      (by simp only [Complex.div_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, Complex.one_re,
            Complex.normSq_apply]
          norm_num)
      (by simp only [Complex.div_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, Complex.one_re,
            Complex.normSq_apply]
          norm_num)
    have hnorm : ‖((2 : ℂ) + (t : ℂ) * Complex.I) / 2‖ = Real.sqrt (4 + t ^ 2) / 2 := by
      rw [Complex.norm_div, Complex.norm_two, norm_two_add_mul_I]
    have hlog_le : Real.log (t / 2) ≤ Real.log (Real.sqrt (4 + t ^ 2) / 2) := by
      apply Real.log_le_log (show (0 : ℝ) < t / 2 by linarith)
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have ht_eq : t / 2 * 2 = t := by ring
      rw [ht_eq]
      nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 4 + t ^ 2), sq_nonneg t, ht2,
        Real.sqrt_nonneg (4 + t ^ 2)]
    have hd' : Real.log (Real.sqrt (4 + t ^ 2) / 2) - 2 ≤
        (Complex.digamma (((2 : ℂ) + (t : ℂ) * Complex.I) / 2)).re := by
      rwa [← hnorm]
    linarith
  · have hz : ∀ m : ℕ, (((2 : ℂ) + (t : ℂ) * Complex.I) + 1) / 2 ≠ -(m : ℂ) := by
      intro m hm
      have hre := congrArg Complex.im hm
      simp at hre
      linarith
    rw [logDeriv_gammaFactor_odd_formula h _ hz, arch_re_eq]
    have hd := digamma_re_ge_log ((((2 : ℂ) + (t : ℂ) * Complex.I) + 1) / 2)
      (by simp only [Complex.div_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, Complex.one_re,
            Complex.normSq_apply]
          norm_num)
      (by simp only [Complex.div_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, Complex.one_re,
            Complex.normSq_apply]
          norm_num)
    have hnorm : ‖((((2 : ℂ) + (t : ℂ) * Complex.I) + 1) / 2)‖ = Real.sqrt (9 + t ^ 2) / 2 := by
      have hfun : (((2 : ℂ) + (t : ℂ) * Complex.I) + 1) / 2 =
          ((3 : ℂ) + (t : ℂ) * Complex.I) / 2 := by ring
      rw [hfun, Complex.norm_div, Complex.norm_two, norm_three_add_mul_I]
    have hlog_le : Real.log (t / 2) ≤ Real.log (Real.sqrt (9 + t ^ 2) / 2) := by
      apply Real.log_le_log (show (0 : ℝ) < t / 2 by linarith)
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have ht_eq : t / 2 * 2 = t := by ring
      rw [ht_eq]
      nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 9 + t ^ 2), sq_nonneg t, ht2,
        Real.sqrt_nonneg (9 + t ^ 2)]
    have hd' : Real.log (Real.sqrt (9 + t ^ 2) / 2) - 2 ≤
        (Complex.digamma ((((2 : ℂ) + (t : ℂ) * Complex.I) + 1) / 2)).re := by
      rwa [← hnorm]
    linarith

/-- Real-part lower bound for the archimedean part of `logDeriv Λ⁻¹` at `s = 2 - it`. -/
lemma arch_re_lower_inv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {t : ℝ} (ht : 2 ≤ t) :
    -(1 / 2) * Real.log Real.pi + (1 / 2) * Real.log (t / 2) - 1 ≤
      (logDeriv (DirichletCharacter.gammaFactor χ⁻¹) ((2 : ℂ) - (t : ℂ) * Complex.I)).re := by
  have ht2 : (0 : ℝ) < t := by linarith
  rcases χ.even_or_odd with h | h
  · have hev : (χ⁻¹).Even := Even_inv h
    have hz : ∀ m : ℕ, ((2 : ℂ) - (t : ℂ) * Complex.I) / 2 ≠ -(m : ℂ) := by
      intro m hm
      have hre := congrArg Complex.im hm
      simp at hre
      linarith
    rw [logDeriv_gammaFactor_even_formula hev _ hz, arch_re_eq]
    have hd := digamma_re_ge_log (((2 : ℂ) - (t : ℂ) * Complex.I) / 2)
      (by simp only [Complex.div_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, Complex.one_re,
            Complex.normSq_apply]
          norm_num)
      (by simp only [Complex.div_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, Complex.one_re,
            Complex.normSq_apply]
          norm_num)
    have hnorm : ‖((2 : ℂ) - (t : ℂ) * Complex.I) / 2‖ = Real.sqrt (4 + t ^ 2) / 2 := by
      rw [Complex.norm_div, Complex.norm_two, norm_two_sub_mul_I]
    have hlog_le : Real.log (t / 2) ≤ Real.log (Real.sqrt (4 + t ^ 2) / 2) := by
      apply Real.log_le_log (show (0 : ℝ) < t / 2 by linarith)
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have ht_eq : t / 2 * 2 = t := by ring
      rw [ht_eq]
      nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 4 + t ^ 2), sq_nonneg t, ht2,
        Real.sqrt_nonneg (4 + t ^ 2)]
    rw [hnorm] at hd
    linarith
  · have hod : (χ⁻¹).Odd := Odd_inv h
    have hz : ∀ m : ℕ, (((2 : ℂ) - (t : ℂ) * Complex.I) + 1) / 2 ≠ -(m : ℂ) := by
      intro m hm
      have hre := congrArg Complex.im hm
      simp at hre
      linarith
    rw [logDeriv_gammaFactor_odd_formula hod _ hz, arch_re_eq]
    have hd := digamma_re_ge_log ((((2 : ℂ) - (t : ℂ) * Complex.I) + 1) / 2)
      (by simp only [Complex.div_re, Complex.add_re, Complex.sub_re, Complex.mul_re,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
            Complex.one_re, Complex.normSq_apply]
          norm_num)
      (by simp only [Complex.div_re, Complex.add_re, Complex.sub_re, Complex.mul_re,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
            Complex.one_re, Complex.normSq_apply]
          norm_num)
    have hnorm : ‖((((2 : ℂ) - (t : ℂ) * Complex.I) + 1) / 2)‖ = Real.sqrt (9 + t ^ 2) / 2 := by
      have hfun : (((2 : ℂ) - (t : ℂ) * Complex.I) + 1) / 2 =
          ((3 : ℂ) - (t : ℂ) * Complex.I) / 2 := by ring
      rw [hfun, Complex.norm_div, Complex.norm_two, norm_three_sub_mul_I]
    have hlog_le : Real.log (t / 2) ≤ Real.log (Real.sqrt (9 + t ^ 2) / 2) := by
      apply Real.log_le_log (show (0 : ℝ) < t / 2 by linarith)
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have ht_eq : t / 2 * 2 = t := by ring
      rw [ht_eq]
      nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 9 + t ^ 2), sq_nonneg t, ht2,
        Real.sqrt_nonneg (9 + t ^ 2)]
    have hd' : Real.log (Real.sqrt (9 + t ^ 2) / 2) - 2 ≤
        (Complex.digamma ((((2 : ℂ) - (t : ℂ) * Complex.I) + 1) / 2)).re := by
      rwa [← hnorm]
    linarith

/-! ## 6. Combining the archimedean and L-function bounds -/

/-- Lower bound for the real part of the L-function's log-derivative at `s = 2 + iT`. -/
lemma LFunction_logDeriv_re_lower {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) :
    -1 ≤ (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (T : ℂ) * Complex.I)).re := by
  have h := logDeriv_L_two_norm_le_one χ T
  have h1 : |(logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ))).re| ≤ 1 :=
    le_trans (Complex.abs_re_le_norm _) h
  have harg : (2 : ℂ) + (T : ℂ) * Complex.I = (2 : ℂ) + Complex.I * (T : ℂ) := by ring
  rw [harg]
  exact (abs_le.mp h1).1

/-- Pointwise lower bound for the real part of the vertical integrand. -/
lemma vertical_pointwise_lower {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {t : ℝ} (ht : 2 ≤ t) :
    Real.log N - Real.log Real.pi + Real.log (t / 2) - 4 ≤
      Real.log N +
        (logDeriv (DirichletCharacter.completedLFunction χ)
          ((2 : ℂ) + (t : ℂ) * Complex.I)).re +
        (logDeriv (DirichletCharacter.completedLFunction χ⁻¹)
          ((2 : ℂ) - (t : ℂ) * Complex.I)).re := by
  have hχinv : χ⁻¹ ≠ 1 := inv_ne_one hχ
  have hL₁ : DirichletCharacter.LFunction χ ((2 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    refine DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) ?_
    simp
  have hL₂ : DirichletCharacter.LFunction χ⁻¹ ((2 : ℂ) - (t : ℂ) * Complex.I) ≠ 0 := by
    refine DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hχinv) ?_
    simp
  have hs₁ : ((2 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hs₂ : ((2 : ℂ) - (t : ℂ) * Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  rw [logDeriv_completedLFunction_eq_add_archimedean χ hχ hs₁ (by simp) hL₁,
      logDeriv_completedLFunction_eq_add_archimedean χ⁻¹ hχinv hs₂ (by simp) hL₂]
  have h1 := arch_re_lower χ ht
  have h1' := arch_re_lower_inv χ ht
  have h2 := LFunction_logDeriv_re_lower χ t
  have h2' := LFunction_logDeriv_re_lower χ⁻¹ (-t)
  have h3 : (2 : ℂ) - (t : ℂ) * Complex.I = (2 : ℂ) + Complex.I * ((-t : ℝ) : ℂ) := by
    push_cast; ring
  rw [h3] at h1' ⊢
  have h4 : (2 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I = (2 : ℂ) + Complex.I * ((-t : ℝ) : ℂ) := by ring
  rw [h4] at h2'
  simp only [Complex.add_re] at *
  linarith [h1, h1', h2, h2']

/-! ## 7. Reflection of the imaginary part of `logDeriv Λ` -/

/-- The imaginary part of `logDeriv Λ` is symmetric about the critical line:
`Im ψ_Λ(σ+iT, χ) = Im ψ_Λ(1-σ+iT, χ)`. -/
lemma im_logDeriv_completedLFunction_reflect {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {σ T : ℝ}
    (h : DirichletCharacter.completedLFunction χ ((σ : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    (logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im =
      (logDeriv (DirichletCharacter.completedLFunction χ) (((1 - σ : ℝ) : ℂ) + (T : ℂ) * Complex.I)).im := by
  have hFE := logDeriv_completedLFunction_one_sub χ hχprim hχ h
  -- `ψ_Λ(s,χ) = -log N - ψ_Λ(1-s,χ⁻¹)`, with `1 - s = (1-σ) - iT`
  have h1 : (Complex.log (N : ℂ)).im = 0 := by
    rw [Complex.log_im]
    simpa using Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg N)
  have h2 : (1 : ℂ) - ((σ : ℂ) + (T : ℂ) * Complex.I) =
      ((1 - σ : ℝ) : ℂ) - (T : ℂ) * Complex.I := by push_cast; ring
  have hFE' := hFE
  rw [h2] at hFE'
  have him : (logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im =
      -(logDeriv (DirichletCharacter.completedLFunction χ⁻¹)
        (((1 - σ : ℝ) : ℂ) - (T : ℂ) * Complex.I)).im := by
    rw [hFE']
    simp [h1]
  -- conjugation symmetry at `(1-σ) + iT`
  have hconj := logDeriv_completedLFunction_conj χ hχ (((1 - σ : ℝ) : ℂ) + (T : ℂ) * Complex.I)
  have hstar : star (((1 - σ : ℝ) : ℂ) + (T : ℂ) * Complex.I) =
      ((1 - σ : ℝ) : ℂ) - (T : ℂ) * Complex.I := by
    simp [map_add, map_mul, Complex.conj_ofReal]
    ring
  rw [hstar] at hconj
  rw [him, hconj]
  simp

/-! ## 8. Zeros of `L(·, χ)` on a horizontal line are finite -/

/-- A zero of `L(·, χ)` with non-zero imaginary part lies in the critical strip. -/
lemma LFunction_zero_re_mem_strip_of_im_ne_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {s : ℂ} (hs : s.im ≠ 0)
    (hLs : DirichletCharacter.LFunction χ s = 0) : 0 < s.re ∧ s.re < 1 := by
  have hs0 : s ≠ 0 := fun h => hs (by rw [h]; simp)
  have hΛ : DirichletCharacter.completedLFunction χ s = 0 := by
    have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)
    rw [h] at hLs
    rcases div_eq_zero_iff.mp hLs with h' | h'
    · exact h'
    · exfalso
      rcases χ.even_or_odd with hE | hO
      · rw [Even.gammaFactor_def hE] at h'
        rw [Complex.Gammaℝ_eq_zero_iff] at h'
        obtain ⟨n, hn⟩ := h'
        exact hs (by rw [hn]; simp)
      · rw [Odd.gammaFactor_def hO] at h'
        rw [Complex.Gammaℝ_eq_zero_iff] at h'
        obtain ⟨n, hn⟩ := h'
        have him : s.im = 0 := by
          have h2 := congrArg Complex.im hn
          simpa using h2
        exact hs him
  exact zerosInStrip χ hχ hχprim s hΛ

/-- The set of `σ` with `L(σ + iT, χ) = 0` is finite when `T ≠ 0`. -/
lemma LFunction_horizontal_zeroSet_finite {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {T : ℝ} (hT : T ≠ 0) :
    {σ : ℝ | DirichletCharacter.LFunction χ ((σ : ℂ) + (T : ℂ) * Complex.I) = 0}.Finite := by
  have hfin := lFunction_zeroSet_box_finite χ hχ hχprim |T|
  let f : ℝ → ℂ := fun σ => (σ : ℂ) + (T : ℂ) * Complex.I
  have hpre : (f ⁻¹'
      {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ |T|}).Finite :=
    Set.Finite.preimage (by
      intro σ₁ _ σ₂ _ heq
      have hre : (f σ₁).re = (f σ₂).re := by rw [heq]
      simpa [f] using hre) hfin
  refine hpre.subset ?_
  intro σ hσ
  have him : (f σ).im = T := by simp [f]
  have hstrip := LFunction_zero_re_mem_strip_of_im_ne_zero χ hχ hχprim
    (s := f σ) (by rw [him]; exact hT) hσ
  exact ⟨hσ, hstrip.1, hstrip.2, by rw [him]⟩

open MeasureTheory

/-! ## 9. Continuity of the archimedean logarithmic derivative -/

/-- `logDeriv` of the reciprocal: for differentiable `h` with `h s ≠ 0`, one has
`logDeriv (h⁻¹) = - logDeriv h`. -/
lemma logDeriv_inv' (h : ℂ → ℂ) (s : ℂ) (hd : DifferentiableAt ℂ h s) (hne : h s ≠ 0) :
    logDeriv (fun u => (h u)⁻¹) s = - logDeriv h s := by
  have hderiv : deriv (fun u => (h u)⁻¹) s = - deriv h s / (h s) ^ 2 := by
    change deriv h⁻¹ s = - deriv h s / (h s) ^ 2
    exact (hd.hasDerivAt.inv hne).deriv
  rw [logDeriv_apply, logDeriv_apply, hderiv]
  field_simp

/-- `logDeriv Γℝ` in terms of the entire function `z ↦ (Γℝ z)⁻¹`. -/
private lemma logDeriv_GammaR_add (a z : ℂ) (hz : Complex.Gammaℝ (z + a) ≠ 0) :
    logDeriv (fun u : ℂ => Complex.Gammaℝ (u + a)) z =
      - deriv (fun u : ℂ => (Complex.Gammaℝ (u + a))⁻¹) z /
        ((Complex.Gammaℝ (z + a))⁻¹) := by
  have hd : Differentiable ℂ (fun u : ℂ => (Complex.Gammaℝ (u + a))⁻¹) :=
    Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const a)
  have h := logDeriv_inv' (fun u : ℂ => (Complex.Gammaℝ (u + a))⁻¹) z
    hd.differentiableAt (inv_ne_zero hz)
  rw [show (fun u : ℂ => ((fun u : ℂ => (Complex.Gammaℝ (u + a))⁻¹) u)⁻¹) =
      (fun u : ℂ => Complex.Gammaℝ (u + a)) from by funext u; simp] at h
  rw [h, logDeriv_apply]
  ring

/-- Continuity of `logDeriv Γℝ` at points where `Γℝ` does not vanish. -/
private lemma continuousAt_logDeriv_GammaR_add (a : ℂ) {s : ℂ} (hs : Complex.Gammaℝ (s + a) ≠ 0) :
    ContinuousAt (logDeriv (fun u : ℂ => Complex.Gammaℝ (u + a))) s := by
  have hd : Differentiable ℂ (fun u : ℂ => (Complex.Gammaℝ (u + a))⁻¹) :=
    Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const a)
  have hcontG : ContinuousAt (fun u : ℂ => (Complex.Gammaℝ (u + a))⁻¹) s :=
    hd.continuous.continuousAt
  have hcontD : ContinuousAt (fun u : ℂ => deriv (fun v : ℂ => (Complex.Gammaℝ (v + a))⁻¹) u) s :=
    hd.deriv.continuous.continuousAt
  have hcont : ContinuousAt (fun u : ℂ =>
      - deriv (fun v : ℂ => (Complex.Gammaℝ (v + a))⁻¹) u / ((Complex.Gammaℝ (u + a))⁻¹)) s :=
    (hcontD.neg).div hcontG (inv_ne_zero hs)
  refine hcont.congr ?_
  filter_upwards [hcontG.eventually_ne (inv_ne_zero hs)] with z hz
  exact (logDeriv_GammaR_add a z (fun hz0 => hz (by rw [hz0]; simp))).symm

/-- Continuity of `logDeriv` of the archimedean gamma factor on the right half-plane. -/
lemma continuousAt_logDeriv_gammaFactor_rightHalfPlane {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) : ContinuousAt (logDeriv (DirichletCharacter.gammaFactor χ)) s := by
  rcases χ.even_or_odd with hE | hO
  · have h : DirichletCharacter.gammaFactor χ = fun u : ℂ => Complex.Gammaℝ (u + 0) := by
      funext u; rw [Even.gammaFactor_def hE]; simp
    rw [h]
    exact continuousAt_logDeriv_GammaR_add 0
      (Complex.Gammaℝ_ne_zero_of_re_pos (s := s + 0) (by simpa using hs))
  · have h : DirichletCharacter.gammaFactor χ = fun u : ℂ => Complex.Gammaℝ (u + 1) := by
      funext u; exact Odd.gammaFactor_def hO u
    rw [h]
    exact continuousAt_logDeriv_GammaR_add 1
      (Complex.Gammaℝ_ne_zero_of_re_pos (s := s + 1) (by
        rw [Complex.add_re, Complex.one_re]; linarith))

/-! ## 10. Splitting the vertical integrand at height `T` -/

/-- On the segment `Re s ∈ [1/2, 2]` at height `T ≠ 0`, the integral of the imaginary part of
`logDeriv Λ` splits into the archimedean part and the `L`-function part. -/
lemma horizontal_mid_split {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {T : ℝ} (hT : T ≠ 0)
    (hnz : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → σ ≤ 2 →
      DirichletCharacter.completedLFunction χ ((σ : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    (∫ σ : ℝ in (1/2)..2,
        (logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im)
      = (∫ σ : ℝ in (1/2)..2,
          (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im)
        + (∫ σ : ℝ in (1/2)..2,
          (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im) := by
  have hZfin := LFunction_horizontal_zeroSet_finite χ hχ hχprim hT
  have hZfin' : ({σ : ℝ | σ ∈ Set.uIoc (1/2) 2 ∧
      DirichletCharacter.LFunction χ ((σ : ℂ) + (T : ℂ) * Complex.I) = 0}).Finite :=
    hZfin.subset (fun σ hσ => hσ.2)
  have hZnull : (volume : Measure ℝ) {σ : ℝ | σ ∈ Set.uIoc (1/2) 2 ∧
      DirichletCharacter.LFunction χ ((σ : ℂ) + (T : ℂ) * Complex.I) = 0} = 0 :=
    hZfin'.measure_zero (volume : Measure ℝ)
  have hae : ∀ᵐ (σ : ℝ) ∂(volume : Measure ℝ), σ ∈ Set.uIoc (1/2) 2 →
      (logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im
        - (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im
      = (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im := by
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null (μ := (volume : Measure ℝ)) ?_ hZnull
    intro σ hσ
    rw [Set.mem_setOf_eq] at hσ ⊢
    push_neg at hσ
    obtain ⟨hσmem, hσne⟩ := hσ
    have hlt : (1 / 2 : ℝ) < σ := by
      have h := hσmem
      rw [Set.uIoc_of_le (by norm_num : (1/2 : ℝ) ≤ 2)] at h
      exact h.1
    refine ⟨hσmem, ?_⟩
    by_contra hLs
    refine hσne ?_
    have hre : ((σ : ℂ) + (T : ℂ) * Complex.I).re = σ := by simp
    have hs0 : ((σ : ℂ) + (T : ℂ) * Complex.I) ≠ 0 := by
      intro hh; have := congrArg Complex.re hh; rw [hre] at this; simp at this
      linarith
    have hsre : 0 < ((σ : ℂ) + (T : ℂ) * Complex.I).re := by rw [hre]; linarith
    rw [logDeriv_completedLFunction_eq_add_archimedean χ hχ hs0 hsre hLs]
    simp
  have hΛdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    differentiable_completedLFunction hχ
  have hcont_f : ContinuousOn (fun σ : ℝ =>
      (logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im)
      (Set.uIcc (1/2) 2) := by
    intro σ hσ
    rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 2)] at hσ
    have hne := hnz σ hσ.1 hσ.2
    have h1 : ContinuousAt (fun z : ℂ => logDeriv (DirichletCharacter.completedLFunction χ) z)
        ((σ : ℂ) + (T : ℂ) * Complex.I) := by
      rw [show logDeriv (DirichletCharacter.completedLFunction χ) =
          fun z => deriv (DirichletCharacter.completedLFunction χ) z /
            DirichletCharacter.completedLFunction χ z from rfl]
      exact (hΛdiff.deriv.continuous.continuousAt).div hΛdiff.continuous.continuousAt hne
    have h2 : ContinuousAt (fun σ' : ℝ => ((σ' : ℂ) + (T : ℂ) * Complex.I)) σ := by fun_prop
    exact (Complex.continuous_im.continuousAt.comp
      (ContinuousAt.comp (f := fun σ' : ℝ => ((σ' : ℂ) + (T : ℂ) * Complex.I)) (x := σ) h1 h2)
      ).continuousWithinAt
  have hcont_a : ContinuousOn (fun σ : ℝ =>
      (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im)
      (Set.uIcc (1/2) 2) := by
    intro σ hσ
    rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 2)] at hσ
    have hre : ((σ : ℂ) + (T : ℂ) * Complex.I).re = σ := by simp
    have h1 := continuousAt_logDeriv_gammaFactor_rightHalfPlane χ (s := (σ : ℂ) + (T : ℂ) * Complex.I)
      (by rw [hre]; linarith [hσ.1])
    have h2 : ContinuousAt (fun σ' : ℝ => ((σ' : ℂ) + (T : ℂ) * Complex.I)) σ := by fun_prop
    exact (Complex.continuous_im.continuousAt.comp
      (ContinuousAt.comp (f := fun σ' : ℝ => ((σ' : ℂ) + (T : ℂ) * Complex.I)) (x := σ) h1 h2)
      ).continuousWithinAt
  have hInt_f : IntervalIntegrable (fun σ : ℝ =>
      (logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im)
      volume (1/2) 2 := hcont_f.intervalIntegrable
  have hInt_a : IntervalIntegrable (fun σ : ℝ =>
      (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im)
      volume (1/2) 2 := hcont_a.intervalIntegrable
  have hsub := intervalIntegral.integral_sub hInt_f hInt_a
  have hcongr : (∫ σ : ℝ in (1/2)..2, ((logDeriv (DirichletCharacter.completedLFunction χ)
        ((σ : ℂ) + (T : ℂ) * Complex.I)).im
        - (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im))
      = ∫ σ : ℝ in (1/2)..2, (logDeriv (DirichletCharacter.LFunction χ)
        ((σ : ℂ) + (T : ℂ) * Complex.I)).im :=
    intervalIntegral.integral_congr_ae hae
  calc (∫ σ : ℝ in (1/2)..2,
        (logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im)
      = (∫ σ : ℝ in (1/2)..2,
          (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im)
        + ((∫ σ : ℝ in (1/2)..2,
          (logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im)
          - (∫ σ : ℝ in (1/2)..2,
          (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im)) := by ring
    _ = (∫ σ : ℝ in (1/2)..2,
          (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im)
        + (∫ σ : ℝ in (1/2)..2,
          (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im) := by
        rw [← hsub, hcongr]


/-! ## 12. Archimedean and horizontal bounds -/

lemma arch_im_eq (w : ℂ) :
    (-(1/2 : ℂ) * Complex.log (π : ℂ) + (1/2 : ℂ) * Complex.digamma w).im
      = (1/2) * (Complex.digamma w).im := by
  have h1 : (Complex.log (π : ℂ)).im = 0 := by
    rw [Complex.log_im]
    simpa using Complex.arg_ofReal_of_nonneg (le_of_lt Real.pi_pos)
  have hy : (-(1/2 : ℂ) * Complex.log (π : ℂ)).im = 0 := by
    rw [Complex.mul_im]
    norm_num [h1]
  have hz : ((1/2 : ℂ) * Complex.digamma w).im = (1/2) * (Complex.digamma w).im := by
    rw [Complex.mul_im]
    norm_num
  rw [Complex.add_im, hy, hz, zero_add]



lemma arch_pointwise_im_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {T σ : ℝ}
    (hT : 2 ≤ T) (h1 : 1/2 ≤ σ) (h2 : σ ≤ 2) :
    |(logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im|
      ≤ Real.log (2 + T/2) + 3 := by
  set s : ℂ := (σ : ℂ) + (T : ℂ) * Complex.I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = T := by simp [hs]
  have hhalf : (1 : ℝ) ≤ T / 2 := by linarith
  have hbnd : (1/2 : ℝ) * (Real.log (2 + T / 2) + 3) ≤ Real.log (2 + T/2) + 3 := by
    have h0 : (0:ℝ) ≤ Real.log (2 + T/2) := Real.log_nonneg (by linarith)
    linarith
  rcases χ.even_or_odd with hE | hO
  · have hw : s / 2 = ((σ / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * Complex.I := by
      rw [hs]; push_cast; ring
    have hne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
      intro m hm
      have h := congrArg Complex.re hm
      rw [hw] at h
      simp at h
      have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      linarith
    have him : (s / 2).im = T / 2 := by rw [hw]; simp
    rw [logDeriv_gammaFactor_even_formula hE s hne, arch_im_eq]
    have hψ : ‖Complex.digamma (s / 2)‖ ≤ Real.log (2 + T / 2) + 3 := by
      have h := digamma_norm_le (s / 2) ?_ ?_ ?_
      · rwa [him, abs_of_nonneg (by linarith : (0:ℝ) ≤ T/2)] at h
      · rw [hw]; simp; linarith
      · rw [hw]; simp; linarith
      · calc (1:ℝ) ≤ |(s / 2).im| := by
              rw [him, abs_of_nonneg (by linarith : (0:ℝ) ≤ T/2)]; linarith
          _ ≤ ‖s / 2‖ := Complex.abs_im_le_norm (s / 2)
    have hcast : |(1/2 : ℝ)| = (1/2 : ℝ) := by norm_num
    rw [abs_mul, hcast]
    calc (1/2) * |(Complex.digamma (s / 2)).im|
        ≤ (1/2) * ‖Complex.digamma (s / 2)‖ := by
          have := Complex.abs_im_le_norm (Complex.digamma (s / 2))
          linarith
      _ ≤ (1/2) * (Real.log (2 + T / 2) + 3) := by linarith
      _ ≤ Real.log (2 + T/2) + 3 := hbnd
  · have hw : (s + 1) / 2 = (((σ + 1) / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * Complex.I := by
      rw [hs]; push_cast; ring
    have hne : ∀ m : ℕ, (s + 1) / 2 ≠ -(m : ℂ) := by
      intro m hm
      have h := congrArg Complex.re hm
      rw [hw] at h
      simp at h
      have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      linarith
    have him : ((s + 1) / 2).im = T / 2 := by rw [hw]; simp
    rw [logDeriv_gammaFactor_odd_formula hO s hne, arch_im_eq]
    have hψ : ‖Complex.digamma ((s + 1) / 2)‖ ≤ Real.log (2 + T / 2) + 3 := by
      have h := digamma_norm_le ((s + 1) / 2) ?_ ?_ ?_
      · rwa [him, abs_of_nonneg (by linarith : (0:ℝ) ≤ T/2)] at h
      · rw [hw]; simp; linarith
      · rw [hw]; simp; linarith
      · calc (1:ℝ) ≤ |((s + 1) / 2).im| := by
              rw [him, abs_of_nonneg (by linarith : (0:ℝ) ≤ T/2)]; linarith
          _ ≤ ‖(s + 1) / 2‖ := Complex.abs_im_le_norm ((s + 1) / 2)
    have hcast : |(1/2 : ℝ)| = (1/2 : ℝ) := by norm_num
    rw [abs_mul, hcast]
    calc (1/2) * |(Complex.digamma ((s + 1) / 2)).im|
        ≤ (1/2) * ‖Complex.digamma ((s + 1) / 2)‖ := by
          have := Complex.abs_im_le_norm (Complex.digamma ((s + 1) / 2))
          linarith
      _ ≤ (1/2) * (Real.log (2 + T / 2) + 3) := by linarith
      _ ≤ Real.log (2 + T/2) + 3 := hbnd



lemma arch_im_integral_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {T : ℝ}
    (hT : 2 ≤ T) :
    |∫ σ : ℝ in (1/2)..2,
      (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im|
      ≤ 2 * (Real.log (2 + T/2) + 3) := by
  have hcont : ContinuousOn (fun σ : ℝ =>
      (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im)
      (Set.uIcc (1/2) 2) := by
    intro σ hσ
    rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 2)] at hσ
    have h1 : ContinuousAt (fun z : ℂ => logDeriv (DirichletCharacter.gammaFactor χ) z)
        ((σ : ℂ) + (T : ℂ) * Complex.I) :=
      continuousAt_logDeriv_gammaFactor_rightHalfPlane χ (s := (σ : ℂ) + (T : ℂ) * Complex.I)
        (by simp; linarith [hσ.1])
    have h2 : ContinuousAt (fun σ' : ℝ => ((σ' : ℂ) + (T : ℂ) * Complex.I)) σ := by fun_prop
    exact (Complex.continuous_im.continuousAt.comp
      (ContinuousAt.comp (f := fun σ' : ℝ => ((σ' : ℂ) + (T : ℂ) * Complex.I)) (x := σ) h1 h2)
      ).continuousWithinAt
  have hInt : IntervalIntegrable (fun σ : ℝ =>
      |(logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im|)
      volume (1/2) 2 := hcont.abs.intervalIntegrable
  have h1 := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
    (f := fun σ : ℝ =>
      (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im)
    (a := (1/2 : ℝ)) (b := 2) (by norm_num)
  have h2 : (∫ σ : ℝ in (1/2)..2,
      |(logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im|)
      ≤ ∫ σ : ℝ in (1/2)..2, (Real.log (2 + T/2) + 3) := by
    apply intervalIntegral.integral_mono_on (by norm_num : (1/2 : ℝ) ≤ 2) hInt
      intervalIntegrable_const
    intro σ hσ
    exact arch_pointwise_im_bound χ hT hσ.1 hσ.2
  have h3 : (∫ σ : ℝ in (1/2)..2, (Real.log (2 + T/2) + 3))
      = (2 - 1/2) * (Real.log (2 + T/2) + 3) := by
    rw [intervalIntegral.integral_const]
    simp
  have hnn : (0:ℝ) ≤ Real.log (2 + T/2) + 3 := by
    have := Real.log_nonneg (by linarith : (1:ℝ) ≤ 2 + T/2)
    linarith
  linarith [h1, h2, h3, hnn]

lemma horizontal_line_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ T : ℝ, 2 ≤ T →
      (∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
        DirichletCharacter.completedLFunction χ ((σ : ℂ) + (T : ℂ) * Complex.I) ≠ 0) →
      |∫ σ : ℝ in (-1)..2,
        (logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im|
        ≤ 2 * (2 * (Real.log (2 + T/2) + 3) + C1 * Real.log (N * (T + 3))) := by
  obtain ⟨C, hCpos, hCb⟩ := LFunction_horizontal_argument_variation_bound χ hχ hχprim
  refine ⟨C, hCpos, ?_⟩
  intro T hT hnz
  have hTne : T ≠ 0 := by linarith
  set g : ℝ → ℝ := fun σ =>
    (logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im
    with hgdef
  have hgcont : ContinuousOn g (Set.uIcc (-1) 2) := by
    intro σ hσ
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] at hσ
    have hne := hnz σ hσ.1 hσ.2
    have h1 : ContinuousAt (fun z : ℂ => logDeriv (DirichletCharacter.completedLFunction χ) z)
        ((σ : ℂ) + (T : ℂ) * Complex.I) := by
      rw [show logDeriv (DirichletCharacter.completedLFunction χ) =
          fun z => deriv (DirichletCharacter.completedLFunction χ) z /
            DirichletCharacter.completedLFunction χ z from rfl]
      exact (((differentiable_completedLFunction hχ).deriv).continuous.continuousAt).div
        (differentiable_completedLFunction hχ).continuous.continuousAt hne
    have h2 : ContinuousAt (fun σ' : ℝ => ((σ' : ℂ) + (T : ℂ) * Complex.I)) σ := by fun_prop
    rw [hgdef]
    exact (Complex.continuous_im.continuousAt.comp
      (ContinuousAt.comp (f := fun σ' : ℝ => ((σ' : ℂ) + (T : ℂ) * Complex.I)) (x := σ) h1 h2)
      ).continuousWithinAt
  have hcont1 : ContinuousOn g (Set.uIcc (-1) (1/2)) :=
    hgcont.mono (by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1/2)] at hx
      rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 2)]
      exact ⟨hx.1, by linarith [hx.2]⟩)
  have hcont2 : ContinuousOn g (Set.uIcc (1/2) 2) :=
    hgcont.mono (by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)] at hx
      rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 2)]
      exact ⟨by linarith [hx.1], hx.2⟩)
  have hint1 : IntervalIntegrable g volume (-1) (1/2) := hcont1.intervalIntegrable
  have hint2 : IntervalIntegrable g volume (1/2) 2 := hcont2.intervalIntegrable
  have hrefl : (∫ σ : ℝ in (-1)..(1/2), g σ) = ∫ σ : ℝ in (1/2)..2, g σ := by
    have h1 : (∫ σ : ℝ in (-1)..(1/2), g σ) = ∫ σ : ℝ in (-1)..(1/2), g (1 - σ) := by
      apply intervalIntegral.integral_congr
      intro σ hσ
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1/2)] at hσ
      rw [hgdef]
      exact im_logDeriv_completedLFunction_reflect χ hχ hχprim (hnz σ hσ.1 (by linarith [hσ.2]))
    have h2 : (∫ σ : ℝ in (-1)..(1/2), g (1 - σ))
        = ∫ σ : ℝ in (1 - 1/2)..(1 - (-1)), g σ :=
      intervalIntegral.integral_comp_sub_left g 1
    rw [h1, h2]
    norm_num
  have htwo : (∫ σ : ℝ in (-1)..2, g σ) = 2 * ∫ σ : ℝ in (1/2)..2, g σ := by
    have hadj := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
    rw [← hadj, hrefl]
    ring
  have hmid := horizontal_mid_split χ hχ hχprim hTne (fun σ h1 h2 => hnz σ (by linarith) h2)
  have harch := arch_im_integral_bound χ hT
  have hLb := hCb T hT
  have hmain : |∫ σ : ℝ in (1/2)..2, g σ|
      ≤ 2 * (Real.log (2 + T/2) + 3) + C * Real.log (N * (T + 3)) := by
    rw [show (∫ σ : ℝ in (1/2)..2, g σ) =
      (∫ σ : ℝ in (1/2)..2,
        (logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im)
      from rfl, hmid]
    calc |(∫ σ : ℝ in (1/2)..2,
          (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im)
        + ∫ σ : ℝ in (1/2)..2,
          (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im|
        ≤ |(∫ σ : ℝ in (1/2)..2,
          (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im)|
          + |∫ σ : ℝ in (1/2)..2,
          (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im| :=
            abs_add_le _ _
      _ ≤ 2 * (Real.log (2 + T/2) + 3) + C * Real.log (N * (T + 3)) := by linarith
  rw [htwo, abs_mul, show |(2:ℝ)| = 2 by norm_num]
  linarith

open MeasureTheory

/-! ## 13. The vertical edges of the rectangle -/

/-- The left edge of the rectangle, using the functional equation and conjugation symmetry. -/
lemma fe_vertical_integral {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {T L : ℝ} (hL : 0 ≤ L)
    (hnz : ∀ y : ℝ, T ≤ y → y ≤ T + L →
      DirichletCharacter.completedLFunction χ ((-1 : ℂ) + (y : ℂ) * Complex.I) ≠ 0) :
    (∫ y : ℝ in T..(T+L), logDeriv (DirichletCharacter.completedLFunction χ)
        ((-1 : ℂ) + (y : ℂ) * Complex.I))
      = - (L : ℂ) * Complex.log (N : ℂ)
        - star (∫ y : ℝ in T..(T+L), logDeriv (DirichletCharacter.completedLFunction χ)
            ((2 : ℂ) + (y : ℂ) * Complex.I)) := by
  set Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ with hΛ
  have hpt : ∀ y : ℝ, T ≤ y → y ≤ T + L →
      logDeriv Λ ((-1 : ℂ) + (y : ℂ) * Complex.I)
        = - Complex.log (N : ℂ) - star (logDeriv Λ ((2 : ℂ) + (y : ℂ) * Complex.I)) := by
    intro y hy1 hy2
    have hFE := logDeriv_completedLFunction_one_sub χ hχprim hχ (hnz y hy1 hy2)
    have h1s : (1 : ℂ) - ((-1 : ℂ) + (y : ℂ) * Complex.I) = (2 : ℂ) - (y : ℂ) * Complex.I := by
      push_cast; ring
    rw [h1s] at hFE
    have hconj := logDeriv_completedLFunction_conj χ hχ ((2 : ℂ) + (y : ℂ) * Complex.I)
    have hstar : star ((2 : ℂ) + (y : ℂ) * Complex.I) = (2 : ℂ) - (y : ℂ) * Complex.I := by
      simp [map_add, Complex.conj_ofReal]
      ring
    rw [hstar] at hconj
    rw [hFE, hconj]
  have hcongr : (∫ y : ℝ in T..(T+L), logDeriv Λ ((-1 : ℂ) + (y : ℂ) * Complex.I))
      = ∫ y : ℝ in T..(T+L),
          (- Complex.log (N : ℂ) - star (logDeriv Λ ((2 : ℂ) + (y : ℂ) * Complex.I))) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le (by linarith : T ≤ T + L)] at hy
    exact hpt y hy.1 hy.2
  have hcont2 : Continuous (fun y : ℝ => logDeriv Λ ((2 : ℂ) + (y : ℂ) * Complex.I)) := by
    have h1 : Continuous (fun y : ℝ => ((2 : ℂ) + (y : ℂ) * Complex.I)) := by fun_prop
    apply Continuous.div ?_ ?_ ?_
    · have : Continuous (fun z : ℂ => deriv Λ z) :=
          ((differentiable_completedLFunction hχ).deriv).continuous
      exact this.comp (h1)
    · exact (differentiable_completedLFunction hχ).continuous.comp h1
    · intro y
      refine completedLFunction_ne_zero_of_one_lt_re χ ?_
      simp
  have hint2 : IntervalIntegrable (fun y : ℝ => logDeriv Λ ((2 : ℂ) + (y : ℂ) * Complex.I))
      volume T (T + L) := hcont2.intervalIntegrable T (T+L)
  have hint1 : IntervalIntegrable (fun y : ℝ => - Complex.log (N : ℂ)) volume T (T + L) :=
    intervalIntegrable_const
  have hintstar : IntervalIntegrable
      (fun y : ℝ => star (logDeriv Λ ((2 : ℂ) + (y : ℂ) * Complex.I))) volume T (T + L) :=
    (hcont2.star).intervalIntegrable T (T+L)
  rw [hcongr, intervalIntegral.integral_sub hint1 hintstar, intervalIntegral.integral_const]
  have hconjint : (∫ y : ℝ in T..(T+L), star (logDeriv Λ ((2 : ℂ) + (y : ℂ) * Complex.I)))
      = star (∫ y : ℝ in T..(T+L), logDeriv Λ ((2 : ℂ) + (y : ℂ) * Complex.I)) := by
    have h := Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hint2
    simpa [Complex.conjCLE_apply, star_def] using h
  rw [hconjint]
  have : (T + L - T) • (-Complex.log (N : ℂ)) = - (L : ℂ) * Complex.log (N : ℂ) := by
    rw [Complex.real_smul]
    push_cast
    ring
  rw [this]



lemma vertical_lower {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {T L : ℝ} (hT : 2 ≤ T) (hL : 0 < L) :
    L * (max (Real.log T) (Real.log L) + Real.log N - 8)
      ≤ 2 * (∫ y : ℝ in T..(T+L),
            (logDeriv (DirichletCharacter.completedLFunction χ) ((2:ℂ)+(y:ℂ)*Complex.I)).re)
        + L * Real.log N := by
  have hTL : T ≤ T + L := by linarith
  have hcontC : Continuous (fun y : ℝ =>
      logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + (y : ℂ) * Complex.I)) := by
    have h1 : Continuous (fun y : ℝ => ((2 : ℂ) + (y : ℂ) * Complex.I)) := by fun_prop
    apply Continuous.div ?_ ?_ ?_
    · exact ((differentiable_completedLFunction hχ).deriv).continuous.comp h1
    · exact (differentiable_completedLFunction hχ).continuous.comp h1
    · intro y
      refine completedLFunction_ne_zero_of_one_lt_re χ ?_
      simp
  have hcontRe : Continuous (fun y : ℝ =>
      (logDeriv (DirichletCharacter.completedLFunction χ)
        ((2 : ℂ) + (y : ℂ) * Complex.I)).re) :=
    Complex.continuous_re.comp hcontC
  have hInt2 : IntervalIntegrable (fun y : ℝ =>
      2 * (logDeriv (DirichletCharacter.completedLFunction χ)
        ((2 : ℂ) + (y : ℂ) * Complex.I)).re) volume T (T + L) :=
    (continuous_const.mul hcontRe).intervalIntegrable T (T+L)
  have hptineq : ∀ y : ℝ, T ≤ y → y ≤ T + L →
      Real.log (y/2) - Real.log Real.pi - 4
        ≤ 2 * (logDeriv (DirichletCharacter.completedLFunction χ)
            ((2 : ℂ) + (y : ℂ) * Complex.I)).re := by
    intro y hy1 hy2
    have hy2' : 2 ≤ y := le_trans hT hy1
    have hv := vertical_pointwise_lower χ hχ (t := y) hy2'
    have hconj := logDeriv_completedLFunction_conj χ hχ ((2 : ℂ) + (y : ℂ) * Complex.I)
    have hstar : star ((2 : ℂ) + (y : ℂ) * Complex.I) = (2 : ℂ) - (y : ℂ) * Complex.I := by
      simp [map_add, Complex.conj_ofReal]; ring
    rw [hstar] at hconj
    have hre : (logDeriv (DirichletCharacter.completedLFunction χ⁻¹)
        ((2 : ℂ) - (y : ℂ) * Complex.I)).re
        = (logDeriv (DirichletCharacter.completedLFunction χ)
            ((2 : ℂ) + (y : ℂ) * Complex.I)).re := by
      rw [hconj]; simp
    rw [hre] at hv
    linarith [hv]
  have hpt2 : ∀ y ∈ Set.uIcc T (T + L), Real.log (y/2) = Real.log y - Real.log 2 := by
    intro y hy
    rw [Set.uIcc_of_le hTL] at hy
    rw [Real.log_div (by linarith [hT, hy.1]) (by norm_num)]
  have hintlog : IntervalIntegrable (fun y : ℝ => Real.log y) volume T (T + L) := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    rw [Set.uIcc_of_le hTL] at hy
    exact (Real.continuousAt_log (by linarith [hT, hy.1])).continuousWithinAt
  have hint41 : IntervalIntegrable (fun y : ℝ => Real.log (y/2)) volume T (T + L) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hTL]
    refine ContinuousOn.log (continuousOn_id.div_const 2) ?_
    intro y hy
    linarith [hT, hy.1]
  have hint43 : IntervalIntegrable (fun y : ℝ => Real.log (y/2) - Real.log Real.pi - 4)
      volume T (T + L) := (hint41.sub intervalIntegrable_const).sub intervalIntegrable_const
  have hlogInt : (∫ y : ℝ in T..(T+L), Real.log (y/2))
      = (∫ y : ℝ in T..(T+L), Real.log y) - L * Real.log 2 := by
    rw [intervalIntegral.integral_congr hpt2,
      intervalIntegral.integral_sub hintlog intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hderiv : ∀ y ∈ Set.uIcc T (T+L),
      HasDerivAt (fun z : ℝ => z * Real.log z - z) (Real.log y) y := by
    intro y hy
    rw [Set.uIcc_of_le hTL] at hy
    have hy0 : y ≠ 0 := by linarith [hT, hy.1]
    have hm : HasDerivAt (fun z : ℝ => z * Real.log z) (1 * Real.log y + y * y⁻¹) y :=
      (hasDerivAt_id (x := y)).mul (Real.hasDerivAt_log hy0)
    have h2 : HasDerivAt (fun z : ℝ => z * Real.log z - z)
        ((1 * Real.log y + y * y⁻¹) - 1) y :=
      hm.sub (hasDerivAt_id (x := y))
    have hval : (1 * Real.log y + y * y⁻¹) - 1 = Real.log y := by
      rw [one_mul, mul_inv_cancel₀ hy0]; ring
    rw [hval] at h2
    exact h2
  have hIntlog : (∫ y : ℝ in T..(T+L), Real.log y)
      = ((T+L) * Real.log (T+L) - (T+L)) - (T * Real.log T - T) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintlog
  have hlogbound : L * max (Real.log T) (Real.log L) - L
      ≤ ∫ y : ℝ in T..(T+L), Real.log y := by
    rw [hIntlog]
    have hmax : max (Real.log T) (Real.log L) ≤ Real.log (T+L) :=
      max_le (Real.log_le_log (by linarith) (by linarith))
        (Real.log_le_log hL (by linarith))
    have h3 : 0 ≤ T * (Real.log (T+L) - Real.log T) :=
      mul_nonneg (by linarith) (by
        have h := Real.log_le_log (by linarith : (0:ℝ) < T) (by linarith : T ≤ T + L)
        linarith)
    have h4 : L * max (Real.log T) (Real.log L) ≤ L * Real.log (T+L) :=
      mul_le_mul_of_nonneg_left hmax hL.le
    have hident : ((T+L) * Real.log (T+L) - (T+L)) - (T * Real.log T - T)
        = T * (Real.log (T+L) - Real.log T) + L * Real.log (T+L) - L := by ring
    linarith [hident, h3, h4]
  have hmono : (∫ y : ℝ in T..(T+L), (Real.log (y/2) - Real.log Real.pi - 4))
      ≤ ∫ y : ℝ in T..(T+L), 2 * (logDeriv (DirichletCharacter.completedLFunction χ)
          ((2 : ℂ) + (y : ℂ) * Complex.I)).re :=
    intervalIntegral.integral_mono_on hTL hint43 hInt2
      (fun y hy => hptineq y hy.1 hy.2)
  have hconst : (∫ y : ℝ in T..(T+L), (Real.log (y/2) - Real.log Real.pi - 4))
      = (∫ y : ℝ in T..(T+L), Real.log (y/2)) - (Real.log Real.pi + 4) * L := by
    have e1 : (∫ y : ℝ in T..(T+L), (Real.log (y/2) - Real.log Real.pi - 4))
        = (∫ y : ℝ in T..(T+L), (Real.log (y/2) - (Real.log Real.pi + 4))) := by
      apply intervalIntegral.integral_congr
      intro y _
      ring
    have hsub : (∫ y : ℝ in T..(T+L), (Real.log (y/2) - (Real.log Real.pi + 4)))
        = (∫ y : ℝ in T..(T+L), Real.log (y/2))
          - ∫ y : ℝ in T..(T+L), (Real.log Real.pi + 4) :=
      intervalIntegral.integral_sub hint41 intervalIntegrable_const
    rw [e1, hsub, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_log (by norm_num : (0:ℝ) < 2) (by
      have h := Real.add_one_le_exp (1:ℝ); linarith)
    rwa [Real.log_exp] at this
  have hpile : Real.log Real.pi ≤ 2 := by
    have h4 : Real.pi ≤ Real.exp 2 := by
      have h1 : (2:ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1:ℝ); linarith
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
      rw [h2]; nlinarith [Real.pi_lt_four]
    have := Real.log_le_log Real.pi_pos h4
    rwa [Real.log_exp] at this
  have hmain : 2 * (∫ y : ℝ in T..(T+L),
      (logDeriv (DirichletCharacter.completedLFunction χ)
        ((2 : ℂ) + (y : ℂ) * Complex.I)).re)
      = ∫ y : ℝ in T..(T+L), 2 * (logDeriv (DirichletCharacter.completedLFunction χ)
        ((2 : ℂ) + (y : ℂ) * Complex.I)).re :=
    (intervalIntegral.integral_const_mul 2 _).symm
  rw [hmain]
  have h2' : L * Real.log 2 ≤ L * 1 := mul_le_mul_of_nonneg_left hlog2le hL.le
  have hpi' : L * Real.log Real.pi ≤ L * 2 := mul_le_mul_of_nonneg_left hpile hL.le
  linarith [hmono, hconst, hlogInt, hlogbound, h2', hpi']

open MeasureTheory

/-! ## 14. Assembling the zero-in-window theorem -/

/-- The left-edge integral, in real form, via the functional equation. -/
lemma fe_vertical_re {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {T L : ℝ} (hL : 0 ≤ L)
    (hnz : ∀ y : ℝ, T ≤ y → y ≤ T + L →
      DirichletCharacter.completedLFunction χ ((-1 : ℂ) + (y : ℂ) * Complex.I) ≠ 0) :
    (∫ y : ℝ in T..(T+L),
        (logDeriv (DirichletCharacter.completedLFunction χ)
          ((-1 : ℂ) + (y : ℂ) * Complex.I)).re)
      = - (L * Real.log N)
        - ∫ y : ℝ in T..(T+L),
            (logDeriv (DirichletCharacter.completedLFunction χ)
              ((2 : ℂ) + (y : ℂ) * Complex.I)).re := by
  have hlogN : ((Real.log N : ℝ) : ℂ) = Complex.log (N : ℂ) :=
    Complex.ofReal_log (Nat.cast_nonneg N)
  have hpt : ∀ y : ℝ, T ≤ y → y ≤ T + L →
      (logDeriv (DirichletCharacter.completedLFunction χ) ((-1 : ℂ) + (y : ℂ) * Complex.I)).re
        = - Real.log N
          - (logDeriv (DirichletCharacter.completedLFunction χ)
              ((2 : ℂ) + (y : ℂ) * Complex.I)).re := by
    intro y hy1 hy2
    have hFE := logDeriv_completedLFunction_one_sub χ hχprim hχ (hnz y hy1 hy2)
    have h1s : (1 : ℂ) - ((-1 : ℂ) + (y : ℂ) * Complex.I) = (2 : ℂ) - (y : ℂ) * Complex.I := by
      push_cast; ring
    rw [h1s] at hFE
    have hconj := logDeriv_completedLFunction_conj χ hχ ((2 : ℂ) + (y : ℂ) * Complex.I)
    have hstar : star ((2 : ℂ) + (y : ℂ) * Complex.I) = (2 : ℂ) - (y : ℂ) * Complex.I := by
      simp [map_add, Complex.conj_ofReal]; ring
    rw [hstar] at hconj
    rw [hFE, hconj]
    simp only [Complex.sub_re, Complex.neg_re, ← hlogN, Complex.ofReal_re, Complex.star_def,
      Complex.conj_re]
  have hcont2 : IntervalIntegrable (fun y : ℝ =>
      (logDeriv (DirichletCharacter.completedLFunction χ)
        ((2 : ℂ) + (y : ℂ) * Complex.I)).re) volume T (T + L) := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    rw [Set.uIcc_of_le (by linarith : T ≤ T + L)] at hy
    have h1 : ContinuousAt (fun z : ℂ => logDeriv (DirichletCharacter.completedLFunction χ) z)
        ((2 : ℂ) + (y : ℂ) * Complex.I) := by
      rw [show logDeriv (DirichletCharacter.completedLFunction χ) =
          fun z => deriv (DirichletCharacter.completedLFunction χ) z /
            DirichletCharacter.completedLFunction χ z from rfl]
      exact (((differentiable_completedLFunction hχ).deriv).continuous.continuousAt).div
        (differentiable_completedLFunction hχ).continuous.continuousAt
        (completedLFunction_ne_zero_of_one_lt_re χ (by simp))
    have h2 : ContinuousAt (fun y' : ℝ => ((2 : ℂ) + (y' : ℂ) * Complex.I)) y := by fun_prop
    exact (Complex.continuous_re.continuousAt.comp
      (ContinuousAt.comp (f := fun y' : ℝ => ((2 : ℂ) + (y' : ℂ) * Complex.I)) (x := y) h1 h2)
      ).continuousWithinAt
  have hcongr : (∫ y : ℝ in T..(T+L),
        (logDeriv (DirichletCharacter.completedLFunction χ)
          ((-1 : ℂ) + (y : ℂ) * Complex.I)).re)
      = ∫ y : ℝ in T..(T+L), (- Real.log N
          - (logDeriv (DirichletCharacter.completedLFunction χ)
              ((2 : ℂ) + (y : ℂ) * Complex.I)).re) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le (by linarith : T ≤ T + L)] at hy
    exact hpt y hy.1 hy.2
  rw [hcongr, intervalIntegral.integral_sub intervalIntegrable_const hcont2,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- The sum of the two horizontal edge bounds. -/
lemma horizontal_edges_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ T L : ℝ, 2 ≤ T → 0 < L →
      (∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
        DirichletCharacter.completedLFunction χ ((σ : ℂ) + (T : ℂ) * Complex.I) ≠ 0) →
      (∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
        DirichletCharacter.completedLFunction χ
          ((σ : ℂ) + ((T + L : ℝ) : ℂ) * Complex.I) ≠ 0) →
      |∫ σ : ℝ in (-1)..2,
          (logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im|
        + |∫ σ : ℝ in (-1)..2,
          (logDeriv (DirichletCharacter.completedLFunction χ)
            ((σ : ℂ) + ((T + L : ℝ) : ℂ) * Complex.I)).im|
        ≤ (8 + 4 * C) * (max (Real.log T) (Real.log L) + Real.log 4) + 24
          + 4 * C * Real.log N := by
  obtain ⟨C, hCpos, hCb⟩ := horizontal_line_bound χ hχ hχprim
  refine ⟨C, hCpos, ?_⟩
  intro T L hT hL hnz1 hnz2
  have hCnn : 0 ≤ C := le_of_lt hCpos
  have h1 := hCb T hT hnz1
  have h2 := hCb (T + L) (by linarith) hnz2
  have hlogs : Real.log (T + L + 3) ≤ max (Real.log T) (Real.log L) + Real.log 4 := by
    have h3 : T + L + 3 ≤ 4 * max T L := by
      rcases le_total T L with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    have hpos : 0 < T + L + 3 := by linarith
    have hmaxpos : 0 < max T L := lt_of_lt_of_le (by linarith : (0:ℝ) < T) (le_max_left _ _)
    have := Real.log_le_log hpos h3
    rw [Real.log_mul (by norm_num) hmaxpos.ne'] at this
    have hmlog : Real.log (max T L) = max (Real.log T) (Real.log L) := by
      rcases le_total T L with h | h
      · rw [max_eq_right h, max_eq_right (Real.log_le_log (by linarith : (0:ℝ) < T) h)]
      · rw [max_eq_left h, max_eq_left (Real.log_le_log hL h)]
    linarith [this, hmlog]
  have hU1 : 2 * (2 * (Real.log (2 + T/2) + 3) + C * Real.log ((N:ℝ) * (T + 3)))
      ≤ (4 + 2*C) * Real.log (T+L+3) + 12 + 2*C*Real.log N := by
    have hlog1 : Real.log (2 + T/2) ≤ Real.log (T + L + 3) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlogN : Real.log ((N:ℝ) * (T + 3)) ≤ Real.log N + Real.log (T+L+3) := by
      rw [Real.log_mul (by exact_mod_cast (NeZero.ne N)) (by linarith : (T:ℝ) + 3 ≠ 0)]
      have : Real.log (T + 3) ≤ Real.log (T + L + 3) :=
        Real.log_le_log (by linarith) (by linarith)
      linarith
    have hm1 := mul_le_mul_of_nonneg_left hlog1 (by norm_num : (0:ℝ) ≤ 4)
    have hm2 := mul_le_mul_of_nonneg_left hlogN (by linarith : (0:ℝ) ≤ 2*C)
    nlinarith [hm1, hm2]
  have hU2 : 2 * (2 * (Real.log (2 + (T+L)/2) + 3) + C * Real.log ((N:ℝ) * (T + L + 3)))
      ≤ (4 + 2*C) * Real.log (T+L+3) + 12 + 2*C*Real.log N := by
    have hlog1 : Real.log (2 + (T+L)/2) ≤ Real.log (T + L + 3) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlogN : Real.log ((N:ℝ) * (T + L + 3)) ≤ Real.log N + Real.log (T+L+3) := by
      rw [Real.log_mul (by exact_mod_cast (NeZero.ne N)) (by linarith : (T:ℝ) + L + 3 ≠ 0)]
    have hm1 := mul_le_mul_of_nonneg_left hlog1 (by norm_num : (0:ℝ) ≤ 4)
    have hm2 := mul_le_mul_of_nonneg_left hlogN (by linarith : (0:ℝ) ≤ 2*C)
    nlinarith [hm1, hm2]
  have hU := add_le_add h1 h2
  nlinarith [hU, hU1, hU2, hlogs, hCnn]

lemma intervalIntegrable_logDeriv_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {a b c : ℝ} (hab : a ≤ b)
    (h : ∀ x : ℝ, a ≤ x → x ≤ b →
      DirichletCharacter.completedLFunction χ ((x : ℂ) + (c : ℂ) * Complex.I) ≠ 0) :
    IntervalIntegrable (fun x : ℝ => logDeriv (DirichletCharacter.completedLFunction χ)
      ((x : ℂ) + (c : ℂ) * Complex.I)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  have h1 : ContinuousAt (fun z : ℂ => logDeriv (DirichletCharacter.completedLFunction χ) z)
      ((x : ℂ) + (c : ℂ) * Complex.I) := by
    rw [show logDeriv (DirichletCharacter.completedLFunction χ) =
        fun z => deriv (DirichletCharacter.completedLFunction χ) z /
          DirichletCharacter.completedLFunction χ z from rfl]
    exact (((differentiable_completedLFunction hχ).deriv).continuous.continuousAt).div
      (differentiable_completedLFunction hχ).continuous.continuousAt (h x hx.1 hx.2)
  have h2 : ContinuousAt (fun x' : ℝ => ((x' : ℂ) + (c : ℂ) * Complex.I)) x := by fun_prop
  exact (ContinuousAt.comp (f := fun x' : ℝ => ((x' : ℂ) + (c : ℂ) * Complex.I)) (x := x) h1 h2)
    |>.continuousWithinAt

/-- Integrability along a vertical segment. -/
lemma intervalIntegrable_logDeriv_vert {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {a b c : ℝ} (hab : a ≤ b)
    (h : ∀ y : ℝ, a ≤ y → y ≤ b →
      DirichletCharacter.completedLFunction χ ((c : ℂ) + (y : ℂ) * Complex.I) ≠ 0) :
    IntervalIntegrable (fun y : ℝ => logDeriv (DirichletCharacter.completedLFunction χ)
      ((c : ℂ) + (y : ℂ) * Complex.I)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro y hy
  rw [Set.uIcc_of_le hab] at hy
  have h1 : ContinuousAt (fun z : ℂ => logDeriv (DirichletCharacter.completedLFunction χ) z)
      ((c : ℂ) + (y : ℂ) * Complex.I) := by
    rw [show logDeriv (DirichletCharacter.completedLFunction χ) =
        fun z => deriv (DirichletCharacter.completedLFunction χ) z /
          DirichletCharacter.completedLFunction χ z from rfl]
    exact (((differentiable_completedLFunction hχ).deriv).continuous.continuousAt).div
      (differentiable_completedLFunction hχ).continuous.continuousAt (h y hy.1 hy.2)
  have h2 : ContinuousAt (fun y' : ℝ => ((c : ℂ) + (y' : ℂ) * Complex.I)) y := by fun_prop
  exact (ContinuousAt.comp (f := fun y' : ℝ => ((c : ℂ) + (y' : ℂ) * Complex.I)) (x := y) h1 h2)
    |>.continuousWithinAt



/-- Arithmetic lemma: with `L` large relative to `C` and `log L ≥ 26`, the window `[T, T+L]`
dominates the horizontal edge bounds. -/
lemma window_domination {C L m n : ℝ} (hC : 0 ≤ C) (hn : 0 ≤ n)
    (hL1 : 2 * (8 + 4 * C) ≤ L) (hL2 : 4 * C ≤ L) (hL3 : 26 ≤ Real.log L)
    (hm : Real.log L ≤ m) :
    (8 + 4 * C) * (m + Real.log 4) + 24 + 4 * C * n < L * (m + n - 8) := by
  have hLpos : 0 < L := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hlog4 : Real.log 4 ≤ 2 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
      norm_num
    have hlog2le : Real.log 2 ≤ 1 := by
      have := Real.log_le_log (by norm_num : (0:ℝ) < 2) (by
        have h := Real.add_one_le_exp (1:ℝ); linarith)
      rwa [Real.log_exp] at this
    rw [h4]; linarith
  have key1 : (L/2) * Real.log L ≤ (L - 8 - 4*C) * m := by
    have h1 : (L/2) * Real.log L ≤ (L/2) * m := mul_le_mul_of_nonneg_left hm (by linarith)
    have h2 : (L/2) ≤ (L - 8 - 4*C) := by linarith
    have h3 : (L/2) * m ≤ (L - 8 - 4*C) * m := mul_le_mul_of_nonneg_right h2 hm0
    linarith
  have key2 : 0 ≤ (L - 4*C) * n := mul_nonneg (by linarith) hn
  have key3 : 13 * L ≤ (L/2) * Real.log L := by
    have := mul_le_mul_of_nonneg_left hL3 (by linarith : (0:ℝ) ≤ L/2)
    linarith
  have key4 : (8+4*C) * Real.log 4 ≤ 16 + 8*C := by
    have h : (8+4*C) * Real.log 4 ≤ (8+4*C) * 2 :=
      mul_le_mul_of_nonneg_left hlog4 (by linarith)
    linarith
  have key5 : 8*C + 40 < 5*L := by linarith
  have hrewrite : L * (m + n - 8) - ((8 + 4 * C) * (m + Real.log 4) + 24 + 4 * C * n)
      = (L - 8 - 4*C) * m + (L - 4*C) * n - 8*L - (8+4*C) * Real.log 4 - 24 := by ring
  rw [← sub_pos, hrewrite]
  linarith [key1, key2, key3, key4, key5]

set_option maxHeartbeats 4000000 in
theorem zeroNearHeight_aux {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ T : ℝ, 2 ≤ T →
      ∃ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 ∧ |ρ.im - T| ≤ Δ := by
  obtain ⟨C, hCpos, hCb⟩ := horizontal_edges_bound χ hχ hχprim
  have hCnn : 0 ≤ C := le_of_lt hCpos
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hlogNnn : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlog10 : (2 : ℝ) ≤ Real.log 10 := by
    have h : Real.exp 2 ≤ 10 := by
      have h1 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ); linarith
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      rw [h2]; nlinarith [Real.exp_one_lt_three]
    have h3 := Real.log_le_log (Real.exp_pos 2) h
    rwa [Real.log_exp] at h3
  set L : ℝ := 10^14 * (C + 1) * (Real.log N + 10) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]; positivity
  have hL10 : (10 : ℝ) ≤ Real.log N + 10 := by linarith
  have hbase2 : (10 : ℝ)^15 * (C + 1) ≤ L := by
    rw [hLdef]
    calc (10:ℝ)^15 * (C + 1) = 10^14 * (C + 1) * 10 := by ring
      _ ≤ 10^14 * (C + 1) * (Real.log N + 10) :=
          mul_le_mul_of_nonneg_left hL10 (by positivity)
  have hLge : (10 : ℝ)^15 ≤ L := by
    have h1 : (10:ℝ)^15 ≤ 10^15 * (C + 1) := by
      have := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ C + 1 by linarith)
        (by positivity : (0:ℝ) ≤ 10^15)
      simpa using this
    linarith [hbase2]
  have hL1 : 2 * (8 + 4 * C) ≤ L := by nlinarith [hbase2, hCnn]
  have hL2 : 4 * C ≤ L := by nlinarith [hbase2, hCnn]
  have hL3 : 26 ≤ Real.log L := by
    have hlog : Real.log ((10:ℝ)^15) ≤ Real.log L := Real.log_le_log (by positivity) hLge
    rw [Real.log_pow] at hlog
    have h30 : (30:ℝ) ≤ (15:ℝ) * Real.log 10 := by
      have := mul_le_mul_of_nonneg_left hlog10 (by norm_num : (0:ℝ) ≤ 15)
      linarith
    have hlog' : (15:ℝ) * Real.log 10 ≤ Real.log L := by simpa using hlog
    linarith [hlog', h30]
  refine ⟨L, hLpos, ?_⟩
  intro T hT
  by_contra hcon
  push_neg at hcon
  have hnozero : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 →
      ¬ (T ≤ ρ.im ∧ ρ.im ≤ T + L) := by
    intro ρ hρ h
    have hlt := hcon ρ hρ
    have habs : |ρ.im - T| ≤ L := by
      rw [abs_le]
      exact ⟨by linarith [h.1, hLpos], by linarith [h.2]⟩
    linarith
  have hnz_low : ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
      DirichletCharacter.completedLFunction χ ((σ : ℂ) + (T : ℂ) * Complex.I) ≠ 0 := by
    intro σ h1 h2 h
    have him : (((σ : ℂ) + (T : ℂ) * Complex.I)).im = T := by simp
    refine hnozero _ h ⟨?_, ?_⟩
    · rw [him]
    · rw [him]; linarith
  have hnz_high : ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
      DirichletCharacter.completedLFunction χ ((σ : ℂ) + ((T + L : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro σ h1 h2 h
    have him : (((σ : ℂ) + ((T + L : ℝ) : ℂ) * Complex.I)).im = T + L := by simp
    refine hnozero _ h ⟨?_, ?_⟩
    · rw [him]; linarith
    · rw [him]
  have hnz_left : ∀ y : ℝ, T ≤ y → y ≤ T + L →
      DirichletCharacter.completedLFunction χ ((-1 : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
    intro y hy1 hy2 h
    have him : (((-1 : ℂ) + (y : ℂ) * Complex.I)).im = y := by simp
    refine hnozero _ h ⟨?_, ?_⟩
    · rw [him]; exact hy1
    · rw [him]; exact hy2
  set z : ℂ := (-1 : ℂ) + (T : ℂ) * Complex.I with hz
  set w : ℂ := (2 : ℂ) + ((T + L : ℝ) : ℂ) * Complex.I with hw
  have hzre : z.re = -1 := by rw [hz]; simp
  have hzim : z.im = T := by rw [hz]; simp
  have hwre : w.re = 2 := by rw [hw]; simp
  have hwim : w.im = T + L := by rw [hw]; simp
  have hrect : Commons.NumberTheory.Zeta.rectInt z w
      (logDeriv (DirichletCharacter.completedLFunction χ)) = 0 := by
    refine rectInt_logDeriv_eq_zero_of_ne_zero (differentiable_completedLFunction hχ) ?_ ?_ ?_
    · rw [hzre, hwre]; norm_num
    · rw [hzim, hwim]; linarith
    · intro s h1 h2 h3 h4
      rw [hzim] at h3
      rw [hwim] at h4
      intro hs
      exact hnozero s hs ⟨h3, h4⟩
  -- integrability for `rectB_im_eq`
  have hb := intervalIntegrable_logDeriv_line (a := -1) (b := 2) (c := T) χ hχ (by norm_num)
      (fun x h1 h2 => hnz_low x h1 h2)
  have ht := intervalIntegrable_logDeriv_line (a := -1) (b := 2) (c := T + L) χ hχ (by norm_num)
      (fun x h1 h2 => hnz_high x h1 h2)
  have hr := intervalIntegrable_logDeriv_vert (a := T) (b := T + L) (c := 2) χ hχ (by linarith)
      (fun y h1 h2 => completedLFunction_ne_zero_of_one_lt_re χ (by simp))
  have hl := intervalIntegrable_logDeriv_vert (a := T) (b := T + L) (c := -1) χ hχ (by linarith)
      (fun y h1 h2 => by simpa using hnz_left y h1 h2)
  have himH : (∫ σ : ℝ in (-1)..2, logDeriv (DirichletCharacter.completedLFunction χ)
        ((σ : ℂ) + (T : ℂ) * Complex.I)).im
      = ∫ σ : ℝ in (-1)..2, (logDeriv (DirichletCharacter.completedLFunction χ)
        ((σ : ℂ) + (T : ℂ) * Complex.I)).im := by
    have := Complex.imCLM.intervalIntegral_comp_comm hb
    simpa [Complex.imCLM_apply] using this.symm
  have himH' : (∫ σ : ℝ in (-1)..2, logDeriv (DirichletCharacter.completedLFunction χ)
        ((σ : ℂ) + ((T + L : ℝ) : ℂ) * Complex.I)).im
      = ∫ σ : ℝ in (-1)..2, (logDeriv (DirichletCharacter.completedLFunction χ)
        ((σ : ℂ) + ((T + L : ℝ) : ℂ) * Complex.I)).im := by
    have := Complex.imCLM.intervalIntegral_comp_comm ht
    simpa [Complex.imCLM_apply] using this.symm
  have hreVr : (∫ y : ℝ in T..(T+L), logDeriv (DirichletCharacter.completedLFunction χ)
        ((2 : ℂ) + (y : ℂ) * Complex.I)).re
      = ∫ y : ℝ in T..(T+L), (logDeriv (DirichletCharacter.completedLFunction χ)
        ((2 : ℂ) + (y : ℂ) * Complex.I)).re := by
    have := Complex.reCLM.intervalIntegral_comp_comm hr
    simpa [Complex.reCLM_apply] using this.symm
  have hreVl : (∫ y : ℝ in T..(T+L), logDeriv (DirichletCharacter.completedLFunction χ)
        ((-1 : ℂ) + (y : ℂ) * Complex.I)).re
      = ∫ y : ℝ in T..(T+L), (logDeriv (DirichletCharacter.completedLFunction χ)
        ((-1 : ℂ) + (y : ℂ) * Complex.I)).re := by
    have := Complex.reCLM.intervalIntegral_comp_comm hl
    simpa [Complex.reCLM_apply] using this.symm
  have him : (Commons.NumberTheory.Zeta.rectInt z w
        (logDeriv (DirichletCharacter.completedLFunction χ))).im
      = (∫ σ : ℝ in (-1)..2, (logDeriv (DirichletCharacter.completedLFunction χ)
            ((σ : ℂ) + (T : ℂ) * Complex.I)).im)
        - (∫ σ : ℝ in (-1)..2, (logDeriv (DirichletCharacter.completedLFunction χ)
            ((σ : ℂ) + ((T + L : ℝ) : ℂ) * Complex.I)).im)
        + (∫ y : ℝ in T..(T+L), (logDeriv (DirichletCharacter.completedLFunction χ)
            ((2 : ℂ) + (y : ℂ) * Complex.I)).re)
        - (∫ y : ℝ in T..(T+L), (logDeriv (DirichletCharacter.completedLFunction χ)
            ((-1 : ℂ) + (y : ℂ) * Complex.I)).re) := by
    rw [Commons.NumberTheory.Zeta.rectInt, hzre, hzim, hwre, hwim]
    simp only [smul_eq_mul]
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_add]
    simp only [Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_one]
    rw [himH, himH', hreVr, hreVl]
  have hrect_im : (Commons.NumberTheory.Zeta.rectInt z w
      (logDeriv (DirichletCharacter.completedLFunction χ))).im = 0 := by rw [hrect]; rfl
  rw [him] at hrect_im
  -- the three bounds
  have hU := hCb T L hT hLpos hnz_low hnz_high
  have hvert := vertical_lower χ hχ hT hLpos
  have hRV := fe_vertical_re χ hχ hχprim hLpos.le hnz_left
  have harith := window_domination (m := max (Real.log T) (Real.log L))
    hCnn hlogNnn hL1 hL2 hL3 (le_max_right _ _)
  have h1 : (-(∫ σ : ℝ in (-1)..2, (logDeriv (DirichletCharacter.completedLFunction χ)
      ((σ : ℂ) + (T : ℂ) * Complex.I)).im))
      ≤ |∫ σ : ℝ in (-1)..2, (logDeriv (DirichletCharacter.completedLFunction χ)
      ((σ : ℂ) + (T : ℂ) * Complex.I)).im| := neg_le_abs _
  have h2 : (∫ σ : ℝ in (-1)..2, (logDeriv (DirichletCharacter.completedLFunction χ)
      ((σ : ℂ) + ((T + L : ℝ) : ℂ) * Complex.I)).im)
      ≤ |∫ σ : ℝ in (-1)..2, (logDeriv (DirichletCharacter.completedLFunction χ)
      ((σ : ℂ) + ((T + L : ℝ) : ℂ) * Complex.I)).im| := le_abs_self _
  set Y : ℝ := L * (max (Real.log T) (Real.log L) + Real.log N - 8) with hYdef
  set Z : ℝ := L * Real.log N with hZdef
  set W : ℝ := (8 + 4 * C) * (max (Real.log T) (Real.log L) + Real.log 4) + 24
    + 4 * C * Real.log N with hWdef
  have hs : Y ≤ W := by linarith [hrect_im, hRV, hvert, hU, h1, h2]
  exact absurd harith (not_lt.mpr hs)

/-! ## The target theorem -/

theorem completedLFunction_zeroNearHeight {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ T : ℝ, 2 ≤ T →
      ∃ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 ∧ |ρ.im - T| ≤ Δ :=
  zeroNearHeight_aux χ hχ hχprim

end

end Commons.NumberTheory.DirichletCharacter
