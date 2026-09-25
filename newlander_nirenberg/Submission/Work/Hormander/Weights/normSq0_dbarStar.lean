/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# `‖∂̄*_φ f‖²_{L²_φ}` expanded as a double sum of pairings

This file proves `Work.Hormander.Weights.normSq0_dbarStar`, the first, purely
algebraic step in the weighted `L²` theory of `∂̄` on `ℂⁿ`: writing
`∂̄*_φ f = - Σ_j g_j` with `g_j z = ∂_j f_j(z) - f_j(z) ∂_j φ(z)`, the square of
the `L²_φ` norm of `∂̄*_φ f` is the real part of the (finite) double sum
`Σ_{j,k} ⟪g_j, g_k⟫_{L²_φ}`.

The proof is a pointwise identity for complex numbers,
`‖Σ_j a_j‖² = Re (Σ_{j,k} a_j conj a_k)`, integrated term by term; the
compact-support hypotheses make every integrand continuous with compact support,
hence Bochner integrable, which is what licenses exchanging the finite sums with
the integral and taking the real part outside the integral.
-/
import Mathlib
import Submission.Work.Hormander.Weights.Basic

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.Hormander.Weights

variable {n : ℕ}

/-! ### Pointwise algebra -/

/-- The pointwise identity `‖Σ_j a_j‖² = Re (Σ_{j,k} a_j conj a_k)`. -/
lemma norm_sq_sum_eq_re_sum_mul_conj (a : Fin n → ℂ) :
    ‖∑ j, a j‖ ^ 2 = (∑ j, ∑ k, a j * star (a k)).re := by
  have h1 : ‖∑ j, a j‖ ^ 2 = ((∑ j, a j) * star (∑ j, a j)).re := by
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
  rw [h1]
  congr 1
  rw [star_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]

/-- The same identity with a real weight pulled out:
`Re (Σ_{j,k} a_j conj a_k · w) = ‖Σ_j a_j‖² · w` for `w : ℝ`. -/
lemma re_double_sum_mul_conj (w : ℝ) (g : Fin n → ℂ) :
    (∑ j, ∑ k, g j * star (g k) * (w : ℂ)).re = ‖∑ j, g j‖ ^ 2 * w := by
  have inner : ∀ j, (∑ k, g j * star (g k) * (w : ℂ)).re
      = (∑ k, g j * star (g k)).re * w := by
    intro j
    have h : (∑ k, g j * star (g k)) * (w : ℂ)
        = ∑ k, g j * star (g k) * (w : ℂ) := by rw [Finset.sum_mul]
    rw [← h, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [Complex.re_sum]
  simp only [inner]
  have h2 : (∑ x, (∑ k, g x * star (g k)).re) * w
      = ∑ x, (∑ k, g x * star (g k)).re * w := by rw [Finset.sum_mul]
  rw [← h2, ← Complex.re_sum, norm_sq_sum_eq_re_sum_mul_conj]

/-! ### The general integral identity -/

/-- The `L²_φ` norm of `-Σ_j g_j` is the real part of the double sum of the
`L²_φ` pairings of the `g_j`.  Integrability of the products `g_j conj g_k · e^{-φ}`
is the only hypothesis needed; it is supplied below by compact support. -/
lemma normSq0_neg_sum (φ : Cn n → ℝ) (g : Fin n → Cn n → ℂ)
    (hint : ∀ j k, Integrable (fun z => g j z * star (g k z) * (wn n φ z : ℂ))) :
    normSq0 φ (fun z => -∑ j, g j z)
      = (∑ j, ∑ k, pairing0 φ (g j) (g k)).re := by
  have hF : Integrable (fun z => ∑ j, ∑ k, g j z * star (g k z) * (wn n φ z : ℂ)) :=
    integrable_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun k _ => hint j k))
  have hsum : (∑ j, ∑ k, pairing0 φ (g j) (g k))
      = ∫ z, ∑ j, ∑ k, g j z * star (g k z) * (wn n φ z : ℂ) := by
    simp only [pairing0]
    rw [integral_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun k _ => hint j k))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_finsetSum Finset.univ (fun k _ => hint j k)]
  have hre : (∫ z, ∑ j, ∑ k, g j z * star (g k z) * (wn n φ z : ℂ)).re
      = ∫ z, (∑ j, ∑ k, g j z * star (g k z) * (wn n φ z : ℂ)).re := by
    simpa only [Complex.reCLM_apply] using
      (ContinuousLinearMap.integral_comp_comm Complex.reCLM hF).symm
  rw [hsum, hre]
  simp only [normSq0]
  congr 1
  funext z
  rw [re_double_sum_mul_conj, norm_neg]

/-! ### Continuity, compact support and integrability of the pieces -/

/-- The complexification of a real `C¹` weight is `C¹`. -/
lemma contDiff_ofReal_comp {φ : Cn n → ℝ} (hφ : ContDiff ℝ 1 φ) :
    ContDiff ℝ 1 (fun z => (φ z : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hφ

/-- `∂_j u` is continuous for `C¹` functions `u`. -/
lemma continuous_dCoord {u : Cn n → ℂ} (hu : ContDiff ℝ 1 u) (j : Fin n) :
    Continuous (fun z => dCoord n j u z) := by
  have hd : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by simp)
  have h1 : Continuous (fun z => fderiv ℝ u z (evec n j)) := hd.clm_apply continuous_const
  have h2 : Continuous (fun z => fderiv ℝ u z (ivec n j)) := hd.clm_apply continuous_const
  unfold dCoord
  exact continuous_const.mul (h1.sub (continuous_const.mul h2))

/-- `∂_j u` has compact support when `u` does. -/
lemma hasCompactSupport_dCoord {u : Cn n → ℂ} (hu : HasCompactSupport u) (j : Fin n) :
    HasCompactSupport (fun z => dCoord n j u z) := by
  unfold dCoord
  exact (hu.fderiv ℝ).comp_left
    (g := fun L : Cn n →L[ℝ] ℂ =>
      (1 / 2 : ℂ) * (L (evec n j) - Complex.I * L (ivec n j))) (by simp)

/-- A continuous compactly supported function times the weight `e^{-φ}` (for a
continuous real weight `φ`) is Bochner integrable. -/
lemma integrable_mul_wn {ψ : Cn n → ℝ} (hψ : ContDiff ℝ 1 ψ) {u : Cn n → ℂ}
    (hu : Continuous u) (huc : HasCompactSupport u) :
    Integrable (fun z => u z * (wn n ψ z : ℂ)) := by
  have hwn : Continuous (fun z => (wn n ψ z : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_neg.comp hψ.continuous))
  exact (hu.mul hwn).integrable_of_hasCompactSupport (huc.mul_right)

/-! ### The main identity -/

/-- **The `L²_φ` norm of `∂̄*_φ f` as a double sum of pairings.**  For a real `C¹`
weight `φ` and a compactly supported `C¹` `(0,1)`-form `f`,
`‖∂̄*_φ f‖²_{L²_φ} = Re Σ_{j,k} ⟪∂_j f_j - f_j ∂_j φ, ∂_k f_k - f_k ∂_k φ⟫_{L²_φ}`. -/
theorem normSq0_dbarStar {n : ℕ} (φ : Cn n → ℝ) (f : Form1 n) (hφ : ContDiff ℝ 1 φ)
    (hf : ∀ j, ContDiff ℝ 1 (f j)) (hfs : ∀ j, HasCompactSupport (f j)) :
    normSq0 φ (dbarStar φ f) = (∑ j, ∑ k, pairing0 φ
      (fun z => dCoord n j (f j) z - f j z * dPhi n j φ z)
      (fun z => dCoord n k (f k) z - f k z * dPhi n k φ z)).re := by
  have hcont : ∀ j, Continuous (fun z => dCoord n j (f j) z - f j z * dPhi n j φ z) := by
    intro j
    exact (continuous_dCoord (hf j) j).sub
      (((hf j).continuous).mul (continuous_dCoord (contDiff_ofReal_comp hφ) j))
  have hcs : ∀ j, HasCompactSupport (fun z => dCoord n j (f j) z - f j z * dPhi n j φ z) := by
    intro j
    exact (hasCompactSupport_dCoord (hfs j) j).sub
      ((hfs j).mul_right (f' := fun z => dPhi n j φ z))
  have hint : ∀ j k, Integrable (fun z => (dCoord n j (f j) z - f j z * dPhi n j φ z)
      * star (dCoord n k (f k) z - f k z * dPhi n k φ z) * (wn n φ z : ℂ)) := by
    intro j k
    exact integrable_mul_wn hφ ((hcont j).mul (continuous_star.comp (hcont k)))
      ((hcs j).mul_right)
  exact normSq0_neg_sum φ
    (fun j z => dCoord n j (f j) z - f j z * dPhi n j φ z) hint

end Work.Hormander.Weights
