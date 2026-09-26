import Mathlib
import Submission.Work.Asymptotics.CuspDecay.PsiBounds

/-!
# The Lipschitz bound for `Ψ = q j` on the region `Im ≥ 2`

`Ψ` is holomorphic on `ℍ` and `D Ψ = E₄²(q/Δ)(E₄ - E₆) = O(q)` (`normalizedDeriv_Psi`,
`norm_normalizedDeriv_Psi_le`).  On the convex region `{Im ≥ 2}` the `q`-parameter obeys
`‖q‖ ≤ 10^{-5}`, so the mean value theorem gives

`‖Ψ a - Ψ b‖ ≤ 2π · 800 · 10^{-5} · ‖a - b‖ ≤ (1/8) ‖a - b‖`

for all `a, b` with `Im ≥ 2`.  This is the Lipschitz input to `j_sub_lower_lattice`.
-/

noncomputable section

open UpperHalfPlane
open scoped Manifold Topology

namespace Work.Asymptotics.CuspDecay

open Work.Kernels

/-- The region `{Im ≥ 2}` of `ℂ` is convex. -/
lemma convex_im_ge_two : Convex ℝ {u : ℂ | 2 ≤ u.im} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  rw [Complex.add_im, Complex.smul_im, Complex.smul_im, smul_eq_mul, smul_eq_mul]
  nlinarith

/-- **Lipschitz bound for `Ψ` on `Im ≥ 2`.** -/
theorem Psi_lipschitz_eighth (a b : UpperHalfPlane) (ha : 2 ≤ a.im) (hb : 2 ≤ b.im) :
    ‖Psi a - Psi b‖ ≤ (1 / 8) * ‖(a : ℂ) - (b : ℂ)‖ := by
  set f : ℂ → ℂ := fun u => Psi (UpperHalfPlane.ofComplex u) with hf
  set C : ℝ := 2 * Real.pi * (800 * (1 / 100000)) with hC
  have hCpos : 0 ≤ C := by rw [hC]; positivity
  have hdiff : ∀ u ∈ {u : ℂ | 2 ≤ u.im}, DifferentiableAt ℂ f u := by
    intro u hu
    simp only [Set.mem_setOf_eq] at hu
    have hu0 : 0 < u.im := by linarith
    have := UpperHalfPlane.mdifferentiableAt_iff.mp (mdifferentiable_Psi ⟨u, hu0⟩)
    simpa [hf, Function.comp_def] using this
  have hbd : ∀ u ∈ {u : ℂ | 2 ≤ u.im}, ‖deriv f u‖ ≤ C := by
    intro u hu
    simp only [Set.mem_setOf_eq] at hu
    have hu0 : 0 < u.im := by linarith
    have hderiv : deriv f u
        = 2 * (Real.pi : ℂ) * Complex.I
          * Derivative.normalizedDerivOfComplex Psi ⟨u, hu0⟩ := by
      have h : Derivative.normalizedDerivOfComplex Psi ⟨u, hu0⟩
          = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * deriv f u := rfl
      rw [h]
      field_simp
    rw [hderiv, norm_mul, norm_mul]
    have hI : ‖(Complex.I : ℂ)‖ = 1 := Complex.norm_I
    have hpi : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [hI, hpi, mul_one]
    have hq := norm_qParamFun_le_1e5 ⟨u, hu0⟩ hu
    have hD := norm_normalizedDeriv_Psi_le ⟨u, hu0⟩ hu
    have hval : ‖Derivative.normalizedDerivOfComplex Psi ⟨u, hu0⟩‖ ≤ 800 * (1 / 100000) := by
      refine le_trans hD ?_
      exact mul_le_mul_of_nonneg_left hq (by norm_num)
    have h := mul_le_mul_of_nonneg_left hval (by positivity : (0:ℝ) ≤ 2 * Real.pi)
    simpa [hC, mul_assoc] using h
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbd convex_im_ge_two
    (x := (a : ℂ)) (y := (b : ℂ)) ha hb
  have hfa : f (a : ℂ) = Psi a := by
    simp only [hf, Function.comp_apply]
    rw [UpperHalfPlane.ofComplex_apply]
  have hfb : f (b : ℂ) = Psi b := by
    simp only [hf, Function.comp_apply]
    rw [UpperHalfPlane.ofComplex_apply]
  rw [hfa, hfb] at hmain
  have hrev : ‖Psi b - Psi a‖ = ‖Psi a - Psi b‖ := norm_sub_rev _ _
  rw [hrev] at hmain
  refine le_trans hmain ?_
  have hCsmall : C ≤ 1 / 8 := by
    rw [hC]; nlinarith [Real.pi_lt_four]
  calc C * ‖(b : ℂ) - (a : ℂ)‖ ≤ (1 / 8) * ‖(b : ℂ) - (a : ℂ)‖ :=
        mul_le_mul_of_nonneg_right hCsmall (norm_nonneg _)
    _ = (1 / 8) * ‖(a : ℂ) - (b : ℂ)‖ := by rw [norm_sub_rev]

end Work.Asymptotics.CuspDecay
