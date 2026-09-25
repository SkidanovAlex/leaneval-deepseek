/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Auxiliary calculus for the divergence of the regularised Bochner–Martinelli kernel

This file collects the real calculus needed by
`Submission/Work/CR/Flat/Cauchy/bmKerEpsDivergence.lean`:

* the real Fréchet derivative of `nrmSq x = Σ_j ‖x_j‖²` evaluated on an arbitrary
  vector (`fderiv_nrmSq_apply`), together with its two coordinate specialisations
  `fderiv_nrmSq_single_one` and `fderiv_nrmSq_single_I` and differentiability;
* the radial chain rule `dbarCoord_comp_nrmSq`: for `Φ : ℝ → ℝ` differentiable at
  `nrmSq z` with derivative `Φ'`, `∂̄_k (x ↦ Φ(nrmSq x)) z = Φ' · z_k`;
* the pointwise expansion of the regularised kernel, `bmKerEps_eq_zpow`;
* the elementary sums `Σ_k \bar z_k z_k = nrmSq z` and the final algebraic identity
  `bmKerEps_algebra`.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Polydisc

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

/-! ### The derivative of `nrmSq` -/

/-- The real Fréchet derivative of `nrmSq x = Σ_j ‖x_j‖²` in the direction `v`:
`d nrmSq(z)(v) = Σ_j 2 Re(v_j \overline{z_j})`. -/
lemma fderiv_nrmSq_apply {n : ℕ} (z v : Fin n → ℂ) :
    fderiv ℝ nrmSq z v = ∑ j, 2 * ((v j) * star (z j)).re := by
  rw [show nrmSq = fun x : Fin n → ℂ => ∑ j, ‖x j‖ ^ 2 from rfl]
  rw [show (fun x : Fin n → ℂ => ∑ j, ‖x j‖ ^ 2)
        = (∑ j : Fin n, fun x : Fin n → ℂ => ‖x j‖ ^ 2) from by funext x; simp]
  rw [fderiv_sum]
  swap
  · intro j _
    exact ((ContinuousLinearMap.hasFDerivAt
      ((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ)).norm_sq).differentiableAt
  rw [sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcomp : fderiv ℝ (fun x : Fin n → ℂ => ‖x j‖ ^ 2) z
      = (fderiv ℝ (fun y : ℂ => ‖y‖ ^ 2) (z j)) ∘L (fderiv ℝ (fun x : Fin n → ℂ => x j) z) := by
    rw [show (fun x : Fin n → ℂ => ‖x j‖ ^ 2)
          = (fun y : ℂ => ‖y‖ ^ 2) ∘ (fun x : Fin n → ℂ => x j) from rfl]
    rw [fderiv_comp z ?_ ?_]
    · exact (hasStrictFDerivAt_norm_sq (z j)).differentiableAt
    · exact ((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).differentiableAt
  rw [hcomp]
  simp only [ContinuousLinearMap.comp_apply]
  rw [fderiv_norm_sq_apply]
  rw [show fderiv ℝ (fun x : Fin n → ℂ => x j) z
      = ((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ)).restrictScalars ℝ from
      ((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt.fderiv]
  show (2 • innerSL ℝ (z j)) ((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ) v)
      = 2 * (v j * star (z j)).re
  rw [ContinuousLinearMap.proj_apply]
  simp [Complex.inner]
  ring

/-- `nrmSq` is real-differentiable everywhere. -/
lemma differentiableAt_nrmSq {n : ℕ} (z : Fin n → ℂ) : DifferentiableAt ℝ nrmSq z := by
  rw [show nrmSq = fun x : Fin n → ℂ => ∑ j, ‖x j‖ ^ 2 from rfl]
  rw [show (fun x : Fin n → ℂ => ∑ j, ‖x j‖ ^ 2)
        = (∑ j : Fin n, fun x : Fin n → ℂ => ‖x j‖ ^ 2) from by funext x; simp]
  apply DifferentiableAt.sum
  intro j _
  exact (hasStrictFDerivAt_norm_sq (z j)).differentiableAt.comp z
    ((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).differentiableAt

/-- The derivative of `nrmSq` in the direction `Pi.single k 1` is `2 Re z_k`. -/
lemma fderiv_nrmSq_single_one {n : ℕ} (k : Fin n) (z : Fin n → ℂ) :
    fderiv ℝ nrmSq z (Pi.single k (1 : ℂ)) = 2 * (z k).re := by
  rw [fderiv_nrmSq_apply, Finset.sum_eq_single k]
  · rw [Pi.single_eq_same]
    simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj]
    simp
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- The derivative of `nrmSq` in the direction `Pi.single k I` is `2 Im z_k`. -/
lemma fderiv_nrmSq_single_I {n : ℕ} (k : Fin n) (z : Fin n → ℂ) :
    fderiv ℝ nrmSq z (Pi.single k Complex.I) = 2 * (z k).im := by
  rw [fderiv_nrmSq_apply, Finset.sum_eq_single k]
  · rw [Pi.single_eq_same]
    simp [Complex.mul_re]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj]
    simp
  · intro h
    exact absurd (Finset.mem_univ k) h

/-! ### The radial chain rule for `∂̄` -/

/-- **The radial chain rule.**  If `Φ : ℝ → ℝ` has derivative `Φ'` at `nrmSq z`, then the
`k`-th flat `∂̄`-derivative of the complexified radial function `x ↦ Φ(nrmSq x)` at `z` is
`Φ' · z_k`.  This is the `∂̄`-counterpart of the chain rule: the `(0,1)`-derivative of
`x ↦ nrmSq x` is the holomorphic function `z ↦ z_k`. -/
lemma dbarCoord_comp_nrmSq {n : ℕ} (k : Fin n) {Φ : ℝ → ℝ} {Φ' : ℝ} {z : Fin n → ℂ}
    (hΦ : HasDerivAt Φ Φ' (nrmSq z)) :
    dbarCoord k (fun x : Fin n → ℂ => ((Φ (nrmSq x) : ℝ) : ℂ)) z = (Φ' : ℂ) * z k := by
  have hns : DifferentiableAt ℝ nrmSq z := differentiableAt_nrmSq z
  have hg : DifferentiableAt ℝ (fun x : Fin n → ℂ => Φ (nrmSq x)) z :=
    hΦ.differentiableAt.comp z hns
  have hfd : fderiv ℝ (fun x : Fin n → ℂ => ((Φ (nrmSq x) : ℝ) : ℂ)) z
      = Complex.ofRealCLM ∘L (ContinuousLinearMap.toSpanSingleton ℝ Φ' ∘L fderiv ℝ nrmSq z) := by
    have h1 : fderiv ℝ (fun x : Fin n → ℂ => Φ (nrmSq x)) z
        = ContinuousLinearMap.toSpanSingleton ℝ Φ' ∘L fderiv ℝ nrmSq z := by
      rw [show (fun x : Fin n → ℂ => Φ (nrmSq x)) = Φ ∘ nrmSq from rfl,
        fderiv_comp z hΦ.differentiableAt hns, hΦ.hasFDerivAt.fderiv]
    rw [show (fun x : Fin n → ℂ => ((Φ (nrmSq x) : ℝ) : ℂ))
          = (⇑Complex.ofRealCLM) ∘ (fun x : Fin n → ℂ => Φ (nrmSq x)) from rfl,
      fderiv_comp z Complex.ofRealCLM.differentiableAt hg, h1, ContinuousLinearMap.fderiv]
  rw [dbarCoord, hfd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, Complex.ofRealCLM_apply]
  rw [fderiv_nrmSq_single_one k z, fderiv_nrmSq_single_I k z]
  conv_rhs => rw [← Complex.re_add_im (z k)]
  push_cast
  ring

/-! ### The regularised kernel as a product -/

/-- The regularised Bochner–Martinelli kernel written as `\bar x_k` times the complexified
radial weight `(nrmSq x + ε²)^{-n}` (in `zpow` form). -/
lemma bmKerEps_eq_zpow {n : ℕ} (k : Fin n) (ε : ℝ) (x : Fin n → ℂ) :
    bmKerEps k ε x = star (x k) * (((nrmSq x + ε ^ 2) ^ (-(n : ℤ)) : ℝ) : ℂ) := by
  rw [bmKerEps_apply, div_eq_mul_inv, Complex.ofReal_zpow, ← zpow_natCast, ← zpow_neg]
  simp only [starRingEnd_apply]

/-! ### Two elementary identities -/

/-- `Σ_k \bar z_k z_k = nrmSq z`. -/
lemma sum_conj_mul_self {n : ℕ} (z : Fin n → ℂ) :
    ∑ k, star (z k) * z k = (((nrmSq z : ℝ)) : ℂ) := by
  rw [nrmSq, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simpa only [starRingEnd_apply, ← Complex.ofReal_pow] using Complex.conj_mul' (z k)

/-- **The algebraic identity behind the divergence.**  For `ε > 0` and `r ≥ 0`,
`n (r+ε²)^{-n} - n r (r+ε²)^{-n-1} = n ε² (r+ε²)^{-(n+1)}`. -/
lemma bmKerEps_algebra {n : ℕ} {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) :
    (n : ℂ) * (((r + ε ^ 2 : ℝ) : ℂ) ^ (-(n : ℤ)))
      + ((-(n : ℤ) : ℂ) * (((r + ε ^ 2 : ℝ) : ℂ) ^ (-(n : ℤ) - 1))) * ((r : ℝ) : ℂ)
      = (n : ℂ) * (ε : ℂ) ^ 2 / (((r + ε ^ 2 : ℝ) : ℂ) ^ (n + 1)) := by
  have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  have hCpos : (0 : ℝ) < r + ε ^ 2 := add_pos_of_nonneg_of_pos hr hε2
  have hreal : (n : ℝ) * (r + ε ^ 2) ^ (-(n : ℤ))
      + ((-(n : ℤ) : ℝ) * (r + ε ^ 2) ^ (-(n : ℤ) - 1)) * r
      = (n : ℝ) * ε ^ 2 / (r + ε ^ 2) ^ (n + 1) := by
    push_cast
    have h1 : (r + ε ^ 2) ^ (-(n : ℤ)) = ((r + ε ^ 2) ^ n)⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    have h2 : (r + ε ^ 2) ^ (-(n : ℤ) - 1) = ((r + ε ^ 2) ^ (n + 1))⁻¹ := by
      have he : (-(n : ℤ) - 1 : ℤ) = -(((n + 1 : ℕ)) : ℤ) := by push_cast; ring
      rw [he, zpow_neg, zpow_natCast]
    rw [h1, h2, pow_succ]
    generalize hX : (r + ε ^ 2) ^ n = X
    have hC0 : (r + ε ^ 2) ≠ 0 := hCpos.ne'
    have hX0 : X ≠ 0 := by rw [← hX]; exact pow_ne_zero _ hC0
    have hXC : X * (r + ε ^ 2) ≠ 0 := mul_ne_zero hX0 hC0
    field_simp
    ring
  have hcast : (((n : ℝ) * (r + ε ^ 2) ^ (-(n : ℤ))
      + ((-(n : ℤ) : ℝ) * (r + ε ^ 2) ^ (-(n : ℤ) - 1)) * r : ℝ) : ℂ)
      = (((n : ℝ) * ε ^ 2 / (r + ε ^ 2) ^ (n + 1) : ℝ) : ℂ) := by
    rw [hreal]
  have hbridge : (n : ℂ) * (((r + ε ^ 2 : ℝ) : ℂ) ^ (-(n : ℤ)))
      + ((-(n : ℤ) : ℂ) * (((r + ε ^ 2 : ℝ) : ℂ) ^ (-(n : ℤ) - 1))) * ((r : ℝ) : ℂ)
      = (((n : ℝ) * (r + ε ^ 2) ^ (-(n : ℤ))
          + ((-(n : ℤ) : ℝ) * (r + ε ^ 2) ^ (-(n : ℤ) - 1)) * r : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hbridge, hcast]
  push_cast
  ring

end Work.CR.Flat.Cauchy
