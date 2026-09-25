import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmKerEpsAux
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dCoord
import Submission.Work.CR.Flat.Cauchy.bmKernel_divergence_aux

namespace Work.NN.Core

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

open Work.CR.Flat.Cauchy

/-! ## Auxiliary calculus for radial weights

These are the analogues of `Work.CR.Flat.Cauchy.bmCz.dCoord_radial` (which handles the exponent
`-n`) for the exponent `-(n+1)`, which is the weight appearing in the regularised radial
`∂`-integration by parts. -/

/-- `nrmSq` is `C¹`. -/
lemma contDiff_one_nrmSq {n : ℕ} : ContDiff ℝ 1 (fun x : Fin n → ℂ => nrmSq x) := by
  have h : (fun x : Fin n → ℂ => nrmSq x) = fun x => ∑ i : Fin n, ‖x i‖ ^ 2 := rfl
  rw [h]
  refine ContDiff.sum (s := Finset.univ) (fun i _ => ?_)
  have h2 : (fun x : Fin n → ℂ => ‖x i‖ ^ 2)
      = (fun y : ℂ => ‖y‖ ^ 2) ∘
          ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ) := rfl
  rw [h2]
  exact (contDiff_norm_sq ℂ (E := ℂ) (n := 1)).comp
    (((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).contDiff (𝕜 := ℝ))

/-- The complexified radial weight `x ↦ (nrmSq x + ε²)^{-(k+1)}` is `C¹` when `ε > 0`. -/
lemma contDiff_one_radial_neg {n : ℕ} (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 1 (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2) ^ (-(k : ℤ) - 1) : ℝ)) : ℂ)) := by
  have hbase : ContDiff ℝ 1 (fun x : Fin n → ℂ => (((nrmSq x + ε ^ 2) ^ (k + 1) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_one_nrmSq.add contDiff_const).pow (k + 1))
  have hne : ∀ x : Fin n → ℂ, (((nrmSq x + ε ^ 2) ^ (k + 1) : ℝ) : ℂ) ≠ 0 := by
    intro x
    rw [Complex.ofReal_ne_zero]
    exact pow_ne_zero _ (ne_of_gt (by have := nrmSq_nonneg x; positivity))
  have hfun : (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2) ^ (-(k : ℤ) - 1) : ℝ)) : ℂ))
      = fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2) ^ (k + 1) : ℝ)) : ℂ)⁻¹ := by
    funext x
    have hreal : (nrmSq x + ε ^ 2) ^ (-(k : ℤ) - 1) = ((nrmSq x + ε ^ 2) ^ (k + 1))⁻¹ := by
      rw [show (-(k : ℤ) - 1) = -(((k + 1 : ℕ)) : ℤ) by push_cast; ring, zpow_neg,
        zpow_natCast]
    rw [hreal, Complex.ofReal_inv]
  rw [hfun]
  exact ContDiff.inv hbase hne

/-- The profile `t ↦ (t + ε²)^{-(k+1)}` has derivative `(-(k+1)) (t + ε²)^{-(k+2)}`. -/
lemma hasDerivAt_radial_neg {k : ℕ} {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => (s + ε ^ 2) ^ (-(k : ℤ) - 1))
      ((((-(k : ℤ) - 1 : ℤ)) : ℝ) * (t + ε ^ 2) ^ (-(k : ℤ) - 2)) t := by
  have hpos : (0 : ℝ) < t + ε ^ 2 := by have := pow_pos hε 2; linarith
  have h1 : HasDerivAt (fun s : ℝ => s + ε ^ 2) (1 : ℝ) t := by
    simpa using (hasDerivAt_id t).add_const (ε ^ 2)
  have h0 : HasDerivAt (fun x : ℝ => x ^ (-(k : ℤ) - 1))
      ((((-(k : ℤ) - 1 : ℤ)) : ℝ) * (t + ε ^ 2) ^ (-(k : ℤ) - 2)) (t + ε ^ 2) := by
    have := hasDerivAt_zpow (-(k : ℤ) - 1) (t + ε ^ 2) (Or.inl hpos.ne')
    rwa [show ((-(k : ℤ) - 1) - 1 : ℤ) = -(k : ℤ) - 2 by ring] at this
  simpa only [Function.comp_def, mul_one] using h0.comp t h1

/-- The `(1,0)`-derivative of the radial weight `(nrmSq · + ε²)^{-(k+1)}`. -/
lemma dCoord_radial_neg {n : ℕ} (k : ℕ) {ε : ℝ} (hε : 0 < ε) (j : Fin n) (z : Fin n → ℂ) :
    Work.CR.Flat.dCoord j (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2) ^ (-(k : ℤ) - 1) : ℝ)) : ℂ)) z
      = -((k : ℂ) + 1) * ((((nrmSq z + ε ^ 2) ^ (-(k : ℤ) - 2) : ℝ)) : ℂ) * star (z j) := by
  have h := Work.CR.Flat.Cauchy.bmCz.dCoord_comp_nrmSq (n := n) j
    (Φ := fun t : ℝ => (t + ε ^ 2) ^ (-(k : ℤ) - 1))
    (Φ' := (((-(k : ℤ) - 1 : ℤ)) : ℝ) * (nrmSq z + ε ^ 2) ^ (-(k : ℤ) - 2))
    (hasDerivAt_radial_neg (k := k) hε (nrmSq_nonneg z))
  rw [h, Complex.ofReal_mul,
    show ((((-(k : ℤ) - 1 : ℤ)) : ℝ) : ℂ) = -((k : ℂ) + 1) by push_cast; ring]

/-- A continuous function times a compactly supported continuous function is integrable. -/
lemma integrable_mul_of_hasCompactSupport' {n : ℕ} {a b : (Fin n → ℂ) → ℂ}
    (ha : Continuous a) (hb : Continuous b) (hbc : HasCompactSupport b) :
    Integrable (fun x => a x * b x) volume :=
  (ha.mul hb).integrable_of_hasCompactSupport (hbc.mul_left (f := a))

/-- **Bilinear integration by parts for the flat `∂`-operator against a radial weight.**
For `ψ ∈ C¹_c` and `ε > 0`,
`∫ x, (nrmSq x + ε²)^{-(k+1)} ∂_j ψ x = (k+1) ∫ x, (nrmSq x + ε²)^{-(k+2)} \bar x_j ψ x`. -/
theorem czbL2_integral_radial_dCoord {n : ℕ} {ε : ℝ} (hε : 0 < ε) (j : Fin n)
    {ψ : (Fin n → ℂ) → ℂ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, ((((Work.CR.Flat.Cauchy.nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ)) : ℂ)
        * Work.CR.Flat.dCoord j ψ x
      = ((n : ℂ) + 1) * ∫ x, ((((Work.CR.Flat.Cauchy.nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 2) : ℝ)) : ℂ)
          * star (x j) * ψ x := by
  have hu : ContDiff ℝ 1
      (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ)) : ℂ)) :=
    contDiff_one_radial_neg n hε
  have hUc : Continuous (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ)) : ℂ)) :=
    hu.continuous
  have hfdU : Continuous (fun x : Fin n → ℂ =>
      fderiv ℝ (fun y : Fin n → ℂ => ((((nrmSq y + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ)) : ℂ)) x
        (Pi.single j 1)) :=
    (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hfdUI : Continuous (fun x : Fin n → ℂ =>
      fderiv ℝ (fun y : Fin n → ℂ => ((((nrmSq y + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ)) : ℂ)) x
        (Pi.single j Complex.I)) :=
    (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hfdψ : Continuous (fun x : Fin n → ℂ => fderiv ℝ ψ x (Pi.single j 1)) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hfdψI : Continuous (fun x : Fin n → ℂ => fderiv ℝ ψ x (Pi.single j Complex.I)) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcsψ1 : HasCompactSupport (fun x : Fin n → ℂ => fderiv ℝ ψ x (Pi.single j 1)) :=
    (hψc.fderiv ℝ).comp_left (g := fun L : (Fin n → ℂ) →L[ℝ] ℂ => L (Pi.single j 1)) (by simp)
  have hcsψI : HasCompactSupport (fun x : Fin n → ℂ => fderiv ℝ ψ x (Pi.single j Complex.I)) :=
    (hψc.fderiv ℝ).comp_left (g := fun L : (Fin n → ℂ) →L[ℝ] ℂ => L (Pi.single j Complex.I)) (by simp)
  have h1u : Integrable (fun x => fderiv ℝ
      (fun y : Fin n → ℂ => ((((nrmSq y + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ)) : ℂ)) x (Pi.single j 1)
        * ψ x) volume :=
    integrable_mul_of_hasCompactSupport' hfdU hψ.continuous hψc
  have hIu : Integrable (fun x => fderiv ℝ
      (fun y : Fin n → ℂ => ((((nrmSq y + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ)) : ℂ)) x (Pi.single j Complex.I)
        * ψ x) volume :=
    integrable_mul_of_hasCompactSupport' hfdUI hψ.continuous hψc
  have h1v : Integrable (fun x => ((((nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ)) : ℂ)
      * fderiv ℝ ψ x (Pi.single j 1)) volume :=
    integrable_mul_of_hasCompactSupport' hUc hfdψ hcsψ1
  have hIv : Integrable (fun x => ((((nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ)) : ℂ)
      * fderiv ℝ ψ x (Pi.single j Complex.I)) volume :=
    integrable_mul_of_hasCompactSupport' hUc hfdψI hcsψI
  have huv : Integrable (fun x => ((((nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ)) : ℂ) * ψ x) volume :=
    integrable_mul_of_hasCompactSupport' hUc hψ.continuous hψc
  have hIBP := Work.CR.Flat.Cauchy.bmCz.integral_mul_dCoord_eq_neg (n := n) j hu hψ
    h1u hIu h1v hIv huv
  rw [hIBP]
  have hpoint : (fun x : Fin n → ℂ => Work.CR.Flat.dCoord j
        (fun y : Fin n → ℂ => ((((nrmSq y + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ)) : ℂ)) x * ψ x)
      = fun x : Fin n → ℂ => (-((n : ℂ) + 1))
          * (((((nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 2) : ℝ)) : ℂ) * star (x j) * ψ x) := by
    funext x
    rw [dCoord_radial_neg n hε j x]
    ring
  rw [hpoint, MeasureTheory.integral_const_mul]
  ring

end

end Work.NN.Core
