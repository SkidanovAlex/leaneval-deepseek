/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# `‖∂̄f‖²_{L²_φ}` expanded as a double sum of pairings

This file proves `Work.Hormander.Weights.normSq2_dbarForm`, the `(0,2)`-analogue
of `Work.Hormander.Weights.normSq0_dbarStar`: for a real `C¹` weight `φ` and a
compactly supported `C¹` `(0,1)`-form `f`,

  `‖∂̄f‖²_{L²_φ} = (1/2) · Re Σ_{j,k} ⟪(∂̄f)_{jk}, (∂̄f)_{jk}⟫_{L²_φ}`.

Everything is a Bochner integral.  The weight `normSq2` is defined with the
antisymmetric (orthonormal basis) convention
`Σ_{j<k} ‖F j k‖² = (1/2) Σ_{j,k} ‖F j k‖²`; accordingly the factor `1/2` sits
on the `(0,2)` side and each diagonal pairing `⟪g,g⟫_{L²_φ}` contributes
`∫ ‖g z‖² e^{-φ z}`, the `1/2` in front of the double sum being precisely the
one appearing in `normSq2`.

The proof is a pointwise identity for complex numbers,
`g z · conj (g z) · e^{-φ z} = ‖g z‖² · e^{-φ z}`, integrated term by term; the
compact-support hypotheses make every integrand continuous with compact support,
hence Bochner integrable, which is what licenses exchanging the two finite sums
with the integral.
-/
import Mathlib
import Submission.Work.Hormander.Weights.Basic

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.Hormander.Weights

variable {n : ℕ}

/-! ### The diagonal pairing as a real integral -/

/-- `⟪g,g⟫_{L²_φ} = ∫ ‖g z‖² e^{-φ z}`, i.e. the diagonal `L²_φ` pairing of a
compactly supported function is the coercion of a genuine real integral. -/
lemma pairing0_self (φ : Cn n → ℝ) (g : Cn n → ℂ) :
    pairing0 φ g g = (((∫ z, ‖g z‖ ^ 2 * wn n φ z : ℝ)) : ℂ) := by
  show (∫ z, g z * star (g z) * ↑(wn n φ z))
    = (((∫ z, ‖g z‖ ^ 2 * wn n φ z : ℝ)) : ℂ)
  have h : (fun z => g z * star (g z) * ↑(wn n φ z))
      = fun z => (((‖g z‖ ^ 2 * wn n φ z : ℝ)) : ℂ) := by
    funext z
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [← Complex.ofReal_mul]
  rw [h]
  exact integral_ofReal (𝕜 := ℂ) (μ := volume)

/-! ### Continuity, compact support and integrability of the pieces -/

/-- `∂̄_j u` is continuous for `C¹` functions `u`. -/
lemma continuous_dbarCoord {u : Cn n → ℂ} (hu : ContDiff ℝ 1 u) (j : Fin n) :
    Continuous (fun z => dbarCoord n j u z) := by
  have hd : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by simp)
  have h1 : Continuous (fun z => fderiv ℝ u z (evec n j)) := hd.clm_apply continuous_const
  have h2 : Continuous (fun z => fderiv ℝ u z (ivec n j)) := hd.clm_apply continuous_const
  unfold dbarCoord
  exact continuous_const.mul (h1.add (continuous_const.mul h2))

/-- `∂̄_j u` has compact support when `u` does. -/
lemma hasCompactSupport_dbarCoord {u : Cn n → ℂ} (hu : HasCompactSupport u) (j : Fin n) :
    HasCompactSupport (fun z => dbarCoord n j u z) :=
  (hu.fderiv ℝ).mono (fun z hz h0 => hz (by simp [dbarCoord, h0]))

/-- The squared norm of a continuous compactly supported function, weighted by
`e^{-φ}` for a `C¹` weight `φ`, is Bochner integrable. -/
lemma integrable_normSq_mul_wn {u : Cn n → ℂ} (hu : Continuous u)
    (huc : HasCompactSupport u) {φ : Cn n → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Integrable (fun z => ‖u z‖ ^ 2 * wn n φ z) := by
  have hwn : Continuous (fun z => wn n φ z) :=
    Real.continuous_exp.comp (continuous_neg.comp hφ.continuous)
  have hcont : Continuous (fun z => ‖u z‖ ^ 2 * wn n φ z) := (hu.norm.pow 2).mul hwn
  refine hcont.integrable_of_hasCompactSupport ?_
  exact huc.mono (fun z hz h0 => hz (by simp [h0]))

/-! ### The main identity -/

/-- **The `L²_φ` norm of `∂̄f` as a double sum of pairings.**  For a real `C¹`
weight `φ` and a compactly supported `C¹` `(0,1)`-form `f`, the square of the
`L²_φ` norm of `∂̄f` is `1/2` times the real part of the finite double sum of the
`L²_φ` pairings of its coefficients with themselves. -/
theorem normSq2_dbarForm {n : ℕ} (φ : Cn n → ℝ) (f : Form1 n) (hφ : ContDiff ℝ 1 φ)
    (hf : ∀ j, ContDiff ℝ 1 (f j)) (hfs : ∀ j, HasCompactSupport (f j)) :
    normSq2 φ (dbarForm f)
      = ((1 / 2) * ∑ j, ∑ k, pairing0 φ (fun z => dbarForm f j k z) (fun z => dbarForm f j k z)).re
    := by
  -- integrability of every weighted coefficient squared norm
  have hint : ∀ j k, Integrable (fun z => ‖dbarForm f j k z‖ ^ 2 * wn n φ z) := by
    intro j k
    have hcont : Continuous (fun z => dbarForm f j k z) :=
      (continuous_dbarCoord (hf j) k).sub (continuous_dbarCoord (hf k) j)
    have hcs : HasCompactSupport (fun z => dbarForm f j k z) :=
      (hasCompactSupport_dbarCoord (hfs j) k).sub (hasCompactSupport_dbarCoord (hfs k) j)
    exact integrable_normSq_mul_wn hcont hcs hφ
  -- the left hand side, with the finite sums pulled out of the integral
  have hL : normSq2 φ (dbarForm f)
      = (1 / 2) * ∑ j, ∑ k, ∫ z, ‖dbarForm f j k z‖ ^ 2 * wn n φ z := by
    rw [normSq2]
    rw [show (fun z => ((1 / 2 : ℝ) * ∑ j, ∑ k, ‖dbarForm f j k z‖ ^ 2) * wn n φ z)
        = fun z => (1 / 2) * ((∑ j, ∑ k, ‖dbarForm f j k z‖ ^ 2) * wn n φ z) from by
          funext z; ring]
    rw [integral_const_mul]
    congr 1
    rw [show (fun z => (∑ j, ∑ k, ‖dbarForm f j k z‖ ^ 2) * wn n φ z)
        = fun z => ∑ j, ∑ k, ‖dbarForm f j k z‖ ^ 2 * wn n φ z from by
          funext z
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.sum_mul]]
    rw [MeasureTheory.integral_finsetSum Finset.univ
        (f := fun j z => ∑ k, ‖dbarForm f j k z‖ ^ 2 * wn n φ z)
        (fun j _ => MeasureTheory.integrable_finsetSum Finset.univ (fun k _ => hint j k))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [MeasureTheory.integral_finsetSum Finset.univ
        (f := fun k z => ‖dbarForm f j k z‖ ^ 2 * wn n φ z)
        (fun k _ => hint j k)]
  -- the right hand side, via the diagonal pairing identity
  have hR : ((1 / 2) * ∑ j, ∑ k, pairing0 φ (fun z => dbarForm f j k z)
        (fun z => dbarForm f j k z)).re
      = (1 / 2) * ∑ j, ∑ k, ∫ z, ‖dbarForm f j k z‖ ^ 2 * wn n φ z := by
    have hre : (∑ j, ∑ k, pairing0 φ (fun z => dbarForm f j k z)
          (fun z => dbarForm f j k z)).re
        = ∑ j, ∑ k, ∫ z, ‖dbarForm f j k z‖ ^ 2 * wn n φ z := by
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [pairing0_self, Complex.ofReal_re]
    rw [Complex.mul_re, hre]
    norm_num
  exact hL.trans hR.symm

end Work.Hormander.Weights
