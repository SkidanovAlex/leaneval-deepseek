/-
# The quantitative reduction to the standard fundamental domain, and growth of `scale`

Auxiliary lemmas for `Work.Asymptotics.bound_of_propagates`:

* `Work.Asymptotics.Frob_inv` : inversion invariance of the Frobenius norm;
* `Work.Asymptotics.MpFrob_le` : the six reduction elements `Mp i` have bounded Frobenius norm;
* `Work.Asymptotics.scale_smul_le_poly` : `scale (γ•τ) ≤ 7 (1+‖γ‖)⁴ (1+scale τ)⁴`;
* `Work.Asymptotics.exists_reduction` : every `τ` is `γ • w` with `w ∈ closure 𝓕` and polynomial
  bounds on `Frob γ` and `scale w`.
-/
import Mathlib
import Submission.Work.Asymptotics.PropagateBounds.Estimate
import Submission.Work.Asymptotics.DomainTiling
import Submission.Work.Asymptotics.Mp_smul_mem_closure_DomainD
import Submission.Work.Asymptotics.closure_DomainD_subset_iUnion_Mp
import Submission.Work.Asymptotics.fd_subset_DomainD
import Submission.Work.Asymptotics.reduction_bound
import Submission.Work.Asymptotics.CarryDefs

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

/-- The Frobenius norm is invariant under inversion. -/
lemma Frob_inv (γ : SL(2, ℤ)) : Frob γ⁻¹ = Frob γ := by
  unfold Frob
  rw [Matrix.SpecialLinearGroup.coe_inv]
  have hadj : (Matrix.adjugate (γ : Matrix (Fin 2) (Fin 2) ℤ)) =
      !![γ 1 1, -(γ 0 1); -(γ 1 0), γ 0 0] := by
    rw [Matrix.adjugate_fin_two]
  rw [hadj]
  congr 1
  simp
  ring

/-- The six reduction elements have bounded Frobenius norm. -/
lemma MpFrob_le (i : Fin 6) : Frob (Mp i) ≤ 2 := by
  have hsq : frobSq (Mp i) ≤ 4 := by fin_cases i <;> decide
  rw [Frob_eq_sqrt_frobSq]
  have hreal : ((frobSq (Mp i) : ℕ) : ℝ) ≤ 4 := by exact_mod_cast hsq
  have h3 : Real.sqrt ((frobSq (Mp i) : ℕ) : ℝ) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hreal
  have h4 : Real.sqrt 4 = 2 := by
    have h : (Real.sqrt 4) ^ 2 = 4 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 4]
  linarith [h3, h4.le, h4.ge]

/-- **Growth of `scale` under a Möbius transformation.** -/
lemma scale_smul_le_poly (γ : SL(2,ℤ)) (τ : ℍ) :
    scale (γ • τ) ≤ 7 * (1 + Frob γ) ^ (4:ℝ) * (1 + scale τ) ^ (4:ℝ) := by
  set F := Frob γ with hF
  set s := scale τ with hs
  have hF0 : 0 ≤ F := Frob_nonneg γ
  have hs0 : 0 ≤ s := le_of_lt (scale_pos τ)
  have hs1 : 1 ≤ s := one_le_scale τ
  have hJ0 : (0:ℝ) < ‖jFun γ (τ : ℂ)‖ := norm_pos_iff.mpr (jFun_ne_zero γ τ)
  have hnormτ : ‖(τ : ℂ)‖ ≤ s := coe_norm_le_scale τ
  have hJle : ‖jFun γ (τ : ℂ)‖ ≤ 2 * F * (1 + s) := by
    refine le_trans (jFun_norm_le γ τ) ?_
    nlinarith
  have hnle : ‖nFun γ (τ : ℂ)‖ ≤ 2 * F * (1 + s) := by
    refine le_trans (nFun_norm_le γ τ) ?_
    nlinarith
  have hJinv : ‖jFun γ (τ : ℂ)‖⁻¹ ≤ s := by
    refine le_trans (SlashBounds.jFun_bound_inv γ τ) ?_
    have h2 : 1 + (τ.im)⁻¹ ≤ 1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖ := by linarith [norm_nonneg ((τ : ℂ))]
    simpa [hs, scale] using h2
  have him : ((γ • τ).im)⁻¹ ≤ 4 * F^2 * (1 + s)^2 * s := by
    rw [im_smul_eq γ τ, inv_div]
    have h1 : ‖jFun γ (τ : ℂ)‖ ^ 2 ≤ 4 * F^2 * (1 + s)^2 := by
      have h1' : ‖jFun γ (τ : ℂ)‖ ^ 2 ≤ (2 * F * (1 + s)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hJle 2
      have h1'' : (2 * F * (1 + s)) ^ 2 = 4 * F^2 * (1 + s)^2 := by ring
      linarith [h1', h1''.le, h1''.ge]
    have h2 : (τ.im)⁻¹ ≤ s := inv_im_le_scale τ
    have h3 : ‖jFun γ (τ : ℂ)‖ ^ 2 / τ.im = ‖jFun γ (τ : ℂ)‖ ^ 2 * (τ.im)⁻¹ := by ring
    rw [h3]
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hcoe : ‖((γ • τ : ℍ) : ℂ)‖ ≤ 2 * F * (1 + s) * s := by
    rw [coe_smul_eq γ τ, norm_div]
    have h1 : ‖nFun γ (τ : ℂ)‖ / ‖jFun γ (τ : ℂ)‖ = ‖nFun γ (τ : ℂ)‖ * ‖jFun γ (τ : ℂ)‖⁻¹ := by
      rw [div_eq_mul_inv]
    rw [h1]
    exact mul_le_mul hnle hJinv (by positivity) (by positivity)
  have hmain : scale (γ • τ) ≤ 1 + 4 * F^2 * (1 + s)^2 * s + 2 * F * (1 + s) * s := by
    rw [scale]
    linarith
  have ha1 : F^2 ≤ (1 + F)^4 := by
    have h1 : F ≤ (1 + F)^2 := by nlinarith
    calc F^2 ≤ ((1 + F)^2)^2 := pow_le_pow_left₀ hF0 h1 2
      _ = (1 + F)^4 := by ring
  have ha2 : (1 + s)^2 * s ≤ (1 + s)^4 := by
    have h1 : s ≤ (1 + s)^2 := by nlinarith
    calc (1 + s)^2 * s ≤ (1 + s)^2 * (1 + s)^2 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (1 + s)^4 := by ring
  have ha : F^2 * (1 + s)^2 * s ≤ (1 + F)^4 * (1 + s)^4 := by
    have h := mul_le_mul ha1 ha2 (by positivity) (by positivity)
    calc F^2 * (1 + s)^2 * s = F^2 * ((1 + s)^2 * s) := by ring
      _ ≤ (1 + F)^4 * (1 + s)^4 := h
  have hb : F * (1 + s) * s ≤ (1 + F)^4 * (1 + s)^4 := by
    have hF1 : F ≤ (1 + F)^4 := by
      calc F ≤ 1 + F := by linarith
        _ = (1 + F)^1 := by ring
        _ ≤ (1 + F)^4 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have hs2 : (1 + s) * s ≤ (1 + s)^4 := by
      have h1 : s ≤ 1 + s := by linarith
      have h2 : (1 + s) * (1 + s) = (1 + s)^2 := by ring
      calc (1 + s) * s ≤ (1 + s) * (1 + s) := mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = (1 + s)^2 := h2
        _ ≤ (1 + s)^4 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h := mul_le_mul hF1 hs2 (by positivity) (by positivity)
    calc F * (1 + s) * s = F * ((1 + s) * s) := by ring
      _ ≤ (1 + F)^4 * (1 + s)^4 := h
  have hc : (1:ℝ) ≤ (1 + F)^4 * (1 + s)^4 := by
    have h1 : (1:ℝ) ≤ (1 + F)^4 := one_le_pow₀ (by linarith)
    have h2 : (1:ℝ) ≤ (1 + s)^4 := one_le_pow₀ (by linarith)
    nlinarith
  have ha' : 4 * (F^2 * (1 + s)^2 * s) ≤ 4 * ((1 + F)^4 * (1 + s)^4) := by linarith
  have hb' : 2 * (F * (1 + s) * s) ≤ 2 * ((1 + F)^4 * (1 + s)^4) := by linarith
  have hrw4 : ((1 + F) ^ (4:ℝ)) = (1 + F)^4 := by
    rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hsw4 : ((1 + s) ^ (4:ℝ)) = (1 + s)^4 := by
    rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  rw [hrw4, hsw4]
  nlinarith [hmain, ha', hb', hc]

/-- **Quantitative reduction to `closure 𝓕`.**  Every `τ` is `γ • w` for some `w` in the closure
of the standard fundamental domain `𝓕` and some `γ ∈ SL(2,ℤ)` whose Frobenius norm, together
with `scale w`, is bounded polynomially in `scale τ`. -/
theorem exists_reduction : ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ τ : ℍ,
    ∃ (γ : SL(2,ℤ)) (w : ℍ), w ∈ closure DomainF ∧ γ • w = τ ∧
      Frob γ ≤ C * (1 + scale τ) ^ N ∧ scale w ≤ C * (1 + scale τ) ^ N := by
  obtain ⟨C_r, N_r, hC_r, hN_r, hred⟩ := reduction_bound
  refine ⟨max (2 * C_r) (7 * 81 * (1 + C_r) ^ 4), 4 * N_r, by positivity, by linarith, fun τ => ?_⟩
  set s := scale τ with hs
  have hs0 : 0 ≤ s := le_of_lt (scale_pos τ)
  have hs1 : (0:ℝ) < 1 + s := by linarith
  have hs1' : (1:ℝ) ≤ 1 + s := by linarith
  have hCr0 : 0 ≤ C_r := le_of_lt hC_r
  have hN4 : 0 ≤ 4 * N_r := by linarith
  have hpow0 : (0:ℝ) < (1 + s) ^ (4 * N_r) := Real.rpow_pos_of_pos hs1 _
  have hC0 : (0:ℝ) ≤ max (2 * C_r) (7 * 81 * (1 + C_r) ^ 4) := by positivity
  obtain ⟨g, hgfd, hgF, hgS⟩ := hred τ
  have hgD : g⁻¹ • τ ∈ closure DomainD :=
    subset_closure (fd_subset_DomainD (by simpa [slSmul] using hgfd))
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (closure_DomainD_subset_iUnion_Mp hgD)
  obtain ⟨x, hx, hxeq⟩ := hi
  have hFg : Frob g ≤ C_r * (1 + s) ^ N_r := by simpa [slSmul, hs] using hgF
  have hSg : scale (g⁻¹ • τ) ≤ C_r * (1 + s) ^ N_r := by simpa [slSmul, hs] using hgS
  have hFg0 : (0:ℝ) ≤ C_r * (1 + s) ^ N_r :=
    mul_nonneg hCr0 (Real.rpow_nonneg (by linarith) N_r)
  refine ⟨g * Mp i, x, hx, ?_, ?_, ?_⟩
  · rw [show (g * Mp i) • x = g • (Mp i • x) by rw [mul_smul]]
    rw [show Mp i • x = g⁻¹ • τ from hxeq, smul_inv_smul]
  · have h2 : Frob (Mp i) ≤ 2 := MpFrob_le i
    have h4 : C_r * (1 + s) ^ N_r * 2 = (2 * C_r) * (1 + s) ^ N_r := by ring
    have hpow : (1 + s) ^ N_r ≤ (1 + s) ^ (4 * N_r) :=
      one_add_rpow_le_rpow (by linarith) hs0
    calc Frob (g * Mp i) ≤ Frob g * Frob (Mp i) := Frob_mul_le g (Mp i)
      _ ≤ (C_r * (1 + s) ^ N_r) * 2 := mul_le_mul hFg h2 (Frob_nonneg _) hFg0
      _ = (2 * C_r) * (1 + s) ^ N_r := h4
      _ ≤ max (2 * C_r) (7 * 81 * (1 + C_r) ^ 4) * (1 + s) ^ (4 * N_r) :=
          mul_le_mul (le_max_left _ _) hpow
            (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 1 + s) N_r) hC0
  · have hx' : x = (Mp i)⁻¹ • (g⁻¹ • τ) := by rw [← hxeq, inv_smul_smul]
    have hFi : 1 + Frob ((Mp i)⁻¹) ≤ 3 := by
      have := MpFrob_le i
      rw [Frob_inv]
      linarith
    have hSi : 1 + scale (g⁻¹ • τ) ≤ (1 + C_r) * (1 + s) ^ N_r := by
      have h1 : (1:ℝ) ≤ (1 + s) ^ N_r := Real.one_le_rpow (by linarith) hN_r
      nlinarith [hSg, hC_r]
    have hFi0 : (0:ℝ) < 1 + Frob ((Mp i)⁻¹) := by
      have := Frob_nonneg ((Mp i)⁻¹); linarith
    have hSi0 : (0:ℝ) < 1 + scale (g⁻¹ • τ) := by
      have := scale_pos (g⁻¹ • τ); linarith
    have hK0 : (0:ℝ) < (1 + C_r) * (1 + s) ^ N_r := by
      have h1 : (0:ℝ) < (1 + s) ^ N_r := Real.rpow_pos_of_pos hs1 N_r
      nlinarith [hC_r]
    rw [hx']
    calc scale ((Mp i)⁻¹ • (g⁻¹ • τ))
        ≤ 7 * (1 + Frob ((Mp i)⁻¹)) ^ (4:ℝ) * (1 + scale (g⁻¹ • τ)) ^ (4:ℝ) :=
          scale_smul_le_poly _ _
      _ = 7 * (1 + Frob ((Mp i)⁻¹)) ^ 4 * (1 + scale (g⁻¹ • τ)) ^ 4 := by
          rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
      _ ≤ 7 * 3 ^ 4 * ((1 + C_r) * (1 + s) ^ N_r) ^ 4 := by
          have hA : (1 + Frob ((Mp i)⁻¹)) ^ 4 ≤ (3:ℝ) ^ 4 :=
            pow_le_pow_left₀ (le_of_lt hFi0) hFi 4
          have hB : (1 + scale (g⁻¹ • τ)) ^ 4 ≤ ((1 + C_r) * (1 + s) ^ N_r) ^ 4 :=
            pow_le_pow_left₀ (le_of_lt hSi0) hSi 4
          have hB0 : (0:ℝ) ≤ ((1 + C_r) * (1 + s) ^ N_r) ^ 4 := pow_nonneg (le_of_lt hK0) 4
          have hA0 : (0:ℝ) ≤ (3:ℝ) ^ 4 := by norm_num
          have h7 : (0:ℝ) ≤ 7 := by norm_num
          have hS0 : (0:ℝ) ≤ (1 + scale (g⁻¹ • τ)) ^ 4 := pow_nonneg (le_of_lt hSi0) 4
          exact mul_le_mul (mul_le_mul_of_nonneg_left hA h7) hB hS0 (by positivity)
      _ = 7 * 81 * (1 + C_r) ^ 4 * (1 + s) ^ (4 * N_r) := by
          have hpow : (1 + s) ^ (4 * N_r) = ((1 + s) ^ N_r) ^ 4 := by
            rw [show 4 * N_r = N_r * ((4:ℕ):ℝ) by ring,
              Real.rpow_mul (le_of_lt hs1) N_r ((4:ℕ):ℝ)]
            exact Real.rpow_natCast _ 4
          rw [mul_pow, ← hpow]
          ring_nf
      _ ≤ max (2 * C_r) (7 * 81 * (1 + C_r) ^ 4) * (1 + s) ^ (4 * N_r) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt hpow0)

end Work.Asymptotics
