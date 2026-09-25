import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Polydisc.dbarCoord_mul
import Submission.Work.NN.Core.integral_normSq_dCoord_eq_dbarCoord
import Submission.Work.CR.Flat.integral_mul_dbarCoord_eq_neg

/-!
# The weighted energy estimate of the Newlander–Nirenberg argument

For `C¹` functions `η`, `H : ℂⁿ → ℂ` with compact support, if the `(0,1)`-part of `dH`
is small on the support of `η`,
  `∑_j ‖∂̄_j H‖² ≤ ε² ∑_j (‖∂_j H‖² + ‖∂̄_j H‖²)`  with `ε² ≤ 1/10`,
then
  `∫ ‖η‖² ∑_j (‖∂_j H‖² + ‖∂̄_j H‖²) ≤ 12 ∫ ‖H‖² ∑_j (‖∂_j η‖² + ‖∂̄_j η‖²)`.

The proof is the classical one: with `u = ηH`, the identity `∫∑‖∂_j u‖² = ∫∑‖∂̄_j u‖²`
(`integral_normSq_dCoord_eq_dbarCoord`) turns the `L²`-norm of `∂u` into the (small) `L²`-norm of
`∂̄u` and the error terms involving `∂η`; the smallness `ε² ≤ 1/10` makes the coefficient of the
left hand side comparable to `1`, giving constants `54/5` for `∫‖η‖²∑‖∂_j H‖²` and `12` for the
full energy.

## Main results

* `Work.NN.Core.weighted_energy_le`
-/

noncomputable section

open scoped NNReal ENNReal ContDiff
open MeasureTheory Set

namespace Work.NN.Core

/-- Leibniz rule for the `j`-th flat `∂`-operator on `ℂⁿ`
(`dCoord j u z = (1/2)(∂_{x_j} - i ∂_{y_j})u(z)`, see `Submission/Work/CR/Flat/Polydisc.lean`),
the `(1,0)`-counterpart of `Work.CR.Flat.Polydisc.dbarCoord_mul`. -/
lemma dCoord_mul {n : ℕ} (j : Fin n) (u v : Cn n → ℂ) (z : Cn n)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    Work.CR.Flat.dCoord j (fun w => u w * v w) z
      = Work.CR.Flat.dCoord j u z * v z + u z * Work.CR.Flat.dCoord j v z := by
  have hmul : (fun w => u w * v w) = u * v := by funext w; rw [Pi.mul_apply]
  rw [hmul]
  have hfg : fderiv ℝ (u * v) z = u z • fderiv ℝ v z + v z • fderiv ℝ u z := by
    have h := (hu.hasFDerivAt.mul hv.hasFDerivAt).fderiv
    simpa using h
  rw [Work.CR.Flat.dCoord, hfg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [Work.CR.Flat.dCoord, Work.CR.Flat.dCoord]
  ring

/-- Integrability of `z ↦ ‖w z‖² X z` when `w` is continuous with compact support and `X` is
continuous. -/
lemma integrable_normSq_mul {n : ℕ} {w : Cn n → ℂ} {X : Cn n → ℝ}
    (hw : Continuous w) (hX : Continuous X) (hwcs : HasCompactSupport w) :
    Integrable (fun z => ‖w z‖ ^ 2 * X z) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (hw.norm.pow 2).mul hX
  · refine hwcs.mono' (fun z hz => subset_closure ?_)
    simp only [Function.mem_support] at hz ⊢
    intro hz0
    exact hz (by simp [hz0])

/-- Integrability of `z ↦ ∑_j ‖∂_j f z‖²` for `f` of class `C¹` with compact support. -/
lemma integrable_sum_sq_dCoord {n : ℕ} {f : Cn n → ℂ} (hf : ContDiff ℝ 1 f)
    (hcs : HasCompactSupport f) :
    Integrable (fun z => ∑ j : Fin n, ‖Work.CR.Flat.dCoord j f z‖ ^ 2) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact continuous_finsetSum _ (fun j _ => (continuous_dCoord j hf).norm.pow 2)
  · refine (hcs.fderiv ℝ).mono' (fun z hz => subset_closure ?_)
    simp only [Function.mem_support] at hz ⊢
    intro hzero
    exact hz (by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [Work.CR.Flat.dCoord, hzero]
      simp)

/-- Integrability of `z ↦ ∑_j ‖∂̄_j f z‖²` for `f` of class `C¹` with compact support. -/
lemma integrable_sum_sq_dbarCoord {n : ℕ} {f : Cn n → ℂ} (hf : ContDiff ℝ 1 f)
    (hcs : HasCompactSupport f) :
    Integrable (fun z => ∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j f z‖ ^ 2) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact continuous_finsetSum _ (fun j _ => (continuous_dbarCoord j hf).norm.pow 2)
  · refine (hcs.fderiv ℝ).mono' (fun z hz => subset_closure ?_)
    simp only [Function.mem_support] at hz ⊢
    intro hzero
    exact hz (by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [Work.CR.Flat.dbarCoord, hzero]
      simp)

/-- `(b + c)² ≤ 2b² + 2c²` for `a ≤ b + c` and `a, b, c ≥ 0`. -/
lemma sq_le_two_sq_add_two_sq {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a ≤ b + c) : a ^ 2 ≤ 2 * b ^ 2 + 2 * c ^ 2 := by
  nlinarith [sq_nonneg (b - c)]

theorem weighted_energy_le {n : ℕ} {η H : Work.NN.Core.Cn n → ℂ}
    (hη : ContDiff ℝ 1 η) (hH : ContDiff ℝ 1 H)
    (hηcs : HasCompactSupport η) (hHcs : HasCompactSupport H)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ^ 2 ≤ 1 / 10)
    (hsmall : ∀ z ∈ tsupport η,
      (∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2)
        ≤ ε ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j H z‖ ^ 2
            + ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2))) :
    ∫ z, ‖η z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j H z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2))
      ≤ 12 * ∫ z, ‖H z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j η z‖ ^ 2
          + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2)) := by
  classical
  set fA : Cn n → ℝ := fun z => ∑ j : Fin n, ‖Work.CR.Flat.dCoord j H z‖ ^ 2 with hfA
  set fB : Cn n → ℝ := fun z => ∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2 with hfB
  set gA : Cn n → ℝ := fun z => ∑ j : Fin n, ‖Work.CR.Flat.dCoord j η z‖ ^ 2 with hgA
  set gB : Cn n → ℝ := fun z => ∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2 with hgB
  set u : Cn n → ℂ := fun w => η w * H w with hu
  set Phi1 : Cn n → ℝ := fun z => ∑ j : Fin n, ‖Work.CR.Flat.dCoord j u z‖ ^ 2 with hPhi1
  set Phi2 : Cn n → ℝ := fun z => ∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j u z‖ ^ 2 with hPhi2
  have hfAc : Continuous fA := by
    rw [hfA]; exact continuous_finsetSum _ (fun j _ => (continuous_dCoord j hH).norm.pow 2)
  have hfBc : Continuous fB := by
    rw [hfB]; exact continuous_finsetSum _ (fun j _ => (continuous_dbarCoord j hH).norm.pow 2)
  have hgAc : Continuous gA := by
    rw [hgA]; exact continuous_finsetSum _ (fun j _ => (continuous_dCoord j hη).norm.pow 2)
  have hgBc : Continuous gB := by
    rw [hgB]; exact continuous_finsetSum _ (fun j _ => (continuous_dbarCoord j hη).norm.pow 2)
  have hu_ct : ContDiff ℝ 1 u := by rw [hu]; exact hη.mul hH
  have hu_cs : HasCompactSupport u := by rw [hu]; exact HasCompactSupport.mul_right hηcs
  have hInt_L : Integrable (fun z => ‖η z‖ ^ 2 * fA z) :=
    integrable_normSq_mul hη.continuous hfAc hηcs
  have hInt_LB : Integrable (fun z => ‖η z‖ ^ 2 * fB z) :=
    integrable_normSq_mul hη.continuous hfBc hηcs
  have hInt_Ma : Integrable (fun z => ‖H z‖ ^ 2 * gA z) :=
    integrable_normSq_mul hH.continuous hgAc hHcs
  have hInt_Mb : Integrable (fun z => ‖H z‖ ^ 2 * gB z) :=
    integrable_normSq_mul hH.continuous hgBc hHcs
  have hInt_M : Integrable (fun z => ‖H z‖ ^ 2 * (gA z + gB z)) :=
    integrable_normSq_mul hH.continuous (hgAc.add hgBc) hHcs
  have hInt_P1 : Integrable Phi1 := by rw [hPhi1]; exact integrable_sum_sq_dCoord hu_ct hu_cs
  have hInt_P2 : Integrable Phi2 := by rw [hPhi2]; exact integrable_sum_sq_dbarCoord hu_ct hu_cs
  -- Pointwise smallness of the `(0,1)`-energy on the support of `η`.
  have hBsmall : ∀ z : Cn n, ‖η z‖ ^ 2 * fB z ≤ (1 / 9) * (‖η z‖ ^ 2 * fA z) := by
    intro z
    by_cases hz : z ∈ Function.support η
    · have hzts : z ∈ tsupport η := subset_closure hz
      have h1 : fB z ≤ ε ^ 2 * (fA z + fB z) := by
        have h := hsmall z hzts
        simp only [hfA, hfB, Finset.sum_add_distrib] at h ⊢
        exact h
      have h2 : fB z ≤ (1 / 9) * fA z := by
        have h10 : ε ^ 2 * (fA z + fB z) ≤ (1 / 10) * (fA z + fB z) :=
          mul_le_mul_of_nonneg_right hε1 (by
            have h3 : 0 ≤ fA z := by rw [hfA]; exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
            have h4 : 0 ≤ fB z := by rw [hfB]; exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
            linarith)
        have h3 : fB z ≤ (1 / 10) * (fA z + fB z) := le_trans h1 h10
        linarith
      calc ‖η z‖ ^ 2 * fB z ≤ ‖η z‖ ^ 2 * ((1 / 9) * fA z) :=
            mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
        _ = (1 / 9) * (‖η z‖ ^ 2 * fA z) := by ring
    · simp only [Function.mem_support, not_not] at hz
      simp [hz]
  -- Pointwise bound of `‖η‖² ‖∂_j H‖²` by `‖∂_j u‖²` and the error term `‖H‖²‖∂_j η‖²`.
  have hperD : ∀ z j, ‖η z‖ ^ 2 * ‖Work.CR.Flat.dCoord j H z‖ ^ 2
      ≤ 2 * ‖Work.CR.Flat.dCoord j u z‖ ^ 2
        + 2 * (‖H z‖ ^ 2 * ‖Work.CR.Flat.dCoord j η z‖ ^ 2) := by
    intro z j
    have hηd : DifferentiableAt ℝ η z := hη.differentiable_one z
    have hHd : DifferentiableAt ℝ H z := hH.differentiable_one z
    have hpr : Work.CR.Flat.dCoord j u z
        = Work.CR.Flat.dCoord j η z * H z + η z * Work.CR.Flat.dCoord j H z := by
      rw [hu]; exact dCoord_mul j η H z hηd hHd
    have heq : η z * Work.CR.Flat.dCoord j H z
        = Work.CR.Flat.dCoord j u z - H z * Work.CR.Flat.dCoord j η z := by
      rw [hpr]; ring
    have hnorm : ‖η z‖ * ‖Work.CR.Flat.dCoord j H z‖
        = ‖Work.CR.Flat.dCoord j u z - H z * Work.CR.Flat.dCoord j η z‖ := by
      rw [← norm_mul, heq]
    have hle : ‖η z‖ * ‖Work.CR.Flat.dCoord j H z‖
        ≤ ‖Work.CR.Flat.dCoord j u z‖ + ‖H z‖ * ‖Work.CR.Flat.dCoord j η z‖ := by
      rw [hnorm]
      calc ‖Work.CR.Flat.dCoord j u z - H z * Work.CR.Flat.dCoord j η z‖
          ≤ ‖Work.CR.Flat.dCoord j u z‖ + ‖H z * Work.CR.Flat.dCoord j η z‖ := norm_sub_le _ _
        _ = ‖Work.CR.Flat.dCoord j u z‖ + ‖H z‖ * ‖Work.CR.Flat.dCoord j η z‖ := by rw [norm_mul]
    have hsq := sq_le_two_sq_add_two_sq (a := ‖η z‖ * ‖Work.CR.Flat.dCoord j H z‖)
      (b := ‖Work.CR.Flat.dCoord j u z‖) (c := ‖H z‖ * ‖Work.CR.Flat.dCoord j η z‖)
      (by positivity) (norm_nonneg _) (by positivity) hle
    rw [mul_pow, mul_pow] at hsq
    exact hsq
  -- Pointwise bound of `‖∂̄_j u‖²` by the small `(0,1)`-energy of `H` and the error term.
  have hperB : ∀ z j, ‖Work.CR.Flat.dbarCoord j u z‖ ^ 2
      ≤ 2 * (‖η z‖ ^ 2 * ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2)
        + 2 * (‖H z‖ ^ 2 * ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2) := by
    intro z j
    have hηd : DifferentiableAt ℝ η z := hη.differentiable_one z
    have hHd : DifferentiableAt ℝ H z := hH.differentiable_one z
    have hpr : Work.CR.Flat.dbarCoord j u z
        = Work.CR.Flat.dbarCoord j η z * H z + η z * Work.CR.Flat.dbarCoord j H z := by
      rw [hu]; exact Work.CR.Flat.Polydisc.dbarCoord_mul j η H z hηd hHd
    have hnorm : ‖Work.CR.Flat.dbarCoord j u z‖
        ≤ ‖η z‖ * ‖Work.CR.Flat.dbarCoord j H z‖ + ‖H z‖ * ‖Work.CR.Flat.dbarCoord j η z‖ := by
      rw [hpr]
      calc ‖Work.CR.Flat.dbarCoord j η z * H z + η z * Work.CR.Flat.dbarCoord j H z‖
          ≤ ‖Work.CR.Flat.dbarCoord j η z * H z‖ + ‖η z * Work.CR.Flat.dbarCoord j H z‖ :=
            norm_add_le _ _
        _ = ‖η z‖ * ‖Work.CR.Flat.dbarCoord j H z‖ + ‖H z‖ * ‖Work.CR.Flat.dbarCoord j η z‖ := by
            rw [norm_mul, norm_mul]; ring
    have hsq := sq_le_two_sq_add_two_sq (norm_nonneg _) (by positivity) (by positivity) hnorm
    rw [mul_pow, mul_pow] at hsq
    exact hsq
  -- Summing the per-coordinate bounds.
  have hpt1 : ∀ z : Cn n, ‖η z‖ ^ 2 * fA z ≤ 2 * Phi1 z + 2 * (‖H z‖ ^ 2 * gA z) := by
    intro z
    have hsum : ∑ j : Fin n, ‖η z‖ ^ 2 * ‖Work.CR.Flat.dCoord j H z‖ ^ 2
        ≤ ∑ j : Fin n, (2 * ‖Work.CR.Flat.dCoord j u z‖ ^ 2
            + 2 * (‖H z‖ ^ 2 * ‖Work.CR.Flat.dCoord j η z‖ ^ 2)) :=
      Finset.sum_le_sum (fun j _ => hperD z j)
    have e1 : ‖η z‖ ^ 2 * fA z = ∑ j : Fin n, ‖η z‖ ^ 2 * ‖Work.CR.Flat.dCoord j H z‖ ^ 2 := by
      rw [hfA, Finset.mul_sum]
    have e2 : (∑ j : Fin n, (2 * ‖Work.CR.Flat.dCoord j u z‖ ^ 2
            + 2 * (‖H z‖ ^ 2 * ‖Work.CR.Flat.dCoord j η z‖ ^ 2)))
        = 2 * Phi1 z + 2 * (‖H z‖ ^ 2 * gA z) := by
      simp only [hPhi1, hgA, Finset.sum_add_distrib, Finset.mul_sum]
    rw [e1]
    exact le_trans hsum (le_of_eq e2)
  have hpt2 : ∀ z : Cn n, Phi2 z ≤ (2 / 9) * (‖η z‖ ^ 2 * fA z) + 2 * (‖H z‖ ^ 2 * gB z) := by
    intro z
    have hsum : ∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j u z‖ ^ 2
        ≤ ∑ j : Fin n, (2 * (‖η z‖ ^ 2 * ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2)
            + 2 * (‖H z‖ ^ 2 * ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2)) :=
      Finset.sum_le_sum (fun j _ => hperB z j)
    have e1 : Phi2 z = ∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j u z‖ ^ 2 := by rw [hPhi2]
    have e2 : (∑ j : Fin n, (2 * (‖η z‖ ^ 2 * ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2)
            + 2 * (‖H z‖ ^ 2 * ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2)))
        = 2 * (‖η z‖ ^ 2 * fB z) + 2 * (‖H z‖ ^ 2 * gB z) := by
      simp only [hfB, hgB, Finset.sum_add_distrib, Finset.mul_sum]
    have h2 : Phi2 z ≤ 2 * (‖η z‖ ^ 2 * fB z) + 2 * (‖H z‖ ^ 2 * gB z) := by
      rw [e1]; exact le_trans hsum (le_of_eq e2)
    have h4 : 2 * (‖η z‖ ^ 2 * fB z) ≤ 2 * ((1 / 9) * (‖η z‖ ^ 2 * fA z)) :=
      mul_le_mul_of_nonneg_left (hBsmall z) (by norm_num)
    linarith
  -- The integral chain.
  have hLHS_split : ∫ z, ‖η z‖ ^ 2 * (fA z + fB z)
      = (∫ z, ‖η z‖ ^ 2 * fA z) + ∫ z, ‖η z‖ ^ 2 * fB z := by
    rw [← integral_add hInt_L hInt_LB]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    ring
  have hb_le : ∫ z, ‖η z‖ ^ 2 * fB z ≤ (1 / 9) * ∫ z, ‖η z‖ ^ 2 * fA z := by
    have h := integral_mono hInt_LB (hInt_L.const_mul (1 / 9)) hBsmall
    rw [integral_const_mul] at h
    exact h
  have hLHS_le : ∫ z, ‖η z‖ ^ 2 * (fA z + fB z) ≤ (10 / 9) * ∫ z, ‖η z‖ ^ 2 * fA z := by
    rw [hLHS_split]; linarith
  have hL_le : ∫ z, ‖η z‖ ^ 2 * fA z
      ≤ 2 * (∫ z, Phi1 z) + 2 * (∫ z, ‖H z‖ ^ 2 * gA z) := by
    have h := integral_mono hInt_L ((hInt_P1.const_mul 2).add (hInt_Ma.const_mul 2)) hpt1
    simp only [Pi.add_apply] at h
    rw [integral_add (hInt_P1.const_mul 2) (hInt_Ma.const_mul 2),
        integral_const_mul, integral_const_mul] at h
    exact h
  have hP_le : ∫ z, Phi2 z
      ≤ (2 / 9) * (∫ z, ‖η z‖ ^ 2 * fA z) + 2 * (∫ z, ‖H z‖ ^ 2 * gB z) := by
    have h := integral_mono hInt_P2 ((hInt_L.const_mul (2 / 9)).add (hInt_Mb.const_mul 2)) hpt2
    simp only [Pi.add_apply] at h
    rw [integral_add (hInt_L.const_mul (2 / 9)) (hInt_Mb.const_mul 2),
        integral_const_mul, integral_const_mul] at h
    exact h
  have hP_eq : (∫ z, Phi1 z) = (∫ z, Phi2 z) := by
    have h := integral_normSq_dCoord_eq_dbarCoord hu_ct hu_cs
    simpa only [hPhi1, hPhi2] using h
  have hMa_le : ∫ z, ‖H z‖ ^ 2 * gA z ≤ ∫ z, ‖H z‖ ^ 2 * (gA z + gB z) := by
    refine integral_mono hInt_Ma hInt_M (fun z => ?_)
    have hgb : 0 ≤ gB z := by rw [hgB]; exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hHH : 0 ≤ ‖H z‖ ^ 2 := sq_nonneg _
    nlinarith
  have hMb_le : ∫ z, ‖H z‖ ^ 2 * gB z ≤ ∫ z, ‖H z‖ ^ 2 * (gA z + gB z) := by
    refine integral_mono hInt_Mb hInt_M (fun z => ?_)
    have hga : 0 ≤ gA z := by rw [hgA]; exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hHH : 0 ≤ ‖H z‖ ^ 2 := sq_nonneg _
    nlinarith
  have hkey : ∫ z, ‖η z‖ ^ 2 * fA z ≤ (54 / 5) * ∫ z, ‖H z‖ ^ 2 * (gA z + gB z) := by
    linarith [hL_le, hP_le, hP_eq, hMa_le, hMb_le]
  have hfin : ∫ z, ‖η z‖ ^ 2 * (fA z + fB z)
      ≤ 12 * ∫ z, ‖H z‖ ^ 2 * (gA z + gB z) := by
    have h1 := mul_le_mul_of_nonneg_left hkey (by norm_num : (0:ℝ) ≤ 10 / 9)
    linarith [hLHS_le, h1]
  -- Rewriting back to the displayed form.
  have hLHS_eq : (∫ z, ‖η z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j H z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2)))
      = ∫ z, ‖η z‖ ^ 2 * (fA z + fB z) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [hfA, hfB, Finset.sum_add_distrib]
  have hRHS_eq : (∫ z, ‖H z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j η z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2)))
      = ∫ z, ‖H z‖ ^ 2 * (gA z + gB z) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [hgA, hgB, Finset.sum_add_distrib]
  rw [hLHS_eq, hRHS_eq]
  exact hfin

end Work.NN.Core
