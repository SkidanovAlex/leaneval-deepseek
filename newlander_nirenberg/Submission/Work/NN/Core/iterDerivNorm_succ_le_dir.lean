/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# One-step estimate for `iterDerivNorm`

For an open `Ω ⊆ ℂⁿ` and `f : ℂⁿ → ℂ` of class `C^{k+1}` on `Ω`, the `(k+1)`-st
iterated-derivative norm of `f` on `Ω` is bounded by the sum, over the `2n` real
coordinate directions `e_j` and `i e_j`, of the `k`-th iterated-derivative norm of
the corresponding directional derivative:

`iterDerivNorm (k+1) f Ω ≤ ∑ p : Fin n × Bool, iterDerivNorm k (∂_p f) Ω`,

where `∂_{(j,false)} f = ∂f/∂x_j` and `∂_{(j,true)} f = ∂f/∂y_j` (i.e. the derivative
of `f` in direction `1` resp. `I` in the `j`-th coordinate).

The mathematical content is the identification of the `(k+1)`-st iterated
derivative with the `k`-th iterated derivative of the directional derivative
(`iteratedFDeriv_succ_apply_right` + commutation of iterated derivatives with
evaluation of a continuous linear map at a constant), together with the elementary
fact that every `v ∈ ℂⁿ` is a real linear combination `∑_p c_p • dirOf p` of the
`2n` directions with `|c_p| ≤ ‖v‖` (sup norm).
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc

open scoped NNReal ENNReal
open Set

noncomputable section

namespace Work.NN.Core

/-- The `2n` real coordinate directions in `ℂⁿ = Fin n → ℂ`: for `p = (j, false)` the
vector `1` in the `j`-th coordinate, for `p = (j, true)` the vector `I` in the `j`-th
coordinate. -/
def dirOf {n : ℕ} (p : Fin n × Bool) : Fin n → ℂ :=
  if p.2 then Pi.single p.1 Complex.I else Pi.single p.1 (1 : ℂ)

/-- Every `v : ℂⁿ` is a real linear combination of the `2n` directions `dirOf p`, with
coefficients the real and imaginary parts of the coordinates. -/
lemma sum_smul_dirOf {n : ℕ} (v : Fin n → ℂ) :
    v = ∑ p : Fin n × Bool, (if p.2 then (v p.1).im else (v p.1).re) • dirOf p := by
  funext i
  rw [Finset.sum_apply, ← Finset.univ_product_univ, Finset.sum_product]
  simp only [Pi.smul_apply, dirOf]
  simp only [Fintype.sum_bool, ite_true, ite_false, Bool.false_eq_true]
  rw [Finset.sum_eq_single i]
  · simp [Pi.single_eq_same, Complex.re_add_im, add_comm]
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- For any continuous linear map out of `ℂⁿ = Fin n → ℂ` (with the sup norm), the
operator norm is bounded by the sum of the norms of the images of the `2n` coordinate
directions `dirOf p`. -/
lemma norm_le_sum_norm_dirOf {n : ℕ} {W : Type*} [SeminormedAddCommGroup W] [NormedSpace ℝ W]
    (B : (Fin n → ℂ) →L[ℝ] W) :
    ‖B‖ ≤ ∑ p : Fin n × Bool, ‖B (dirOf p)‖ := by
  refine (ContinuousLinearMap.opNorm_le_iff (by positivity)).mpr fun v => ?_
  have hcoef : ∀ p : Fin n × Bool, |(if p.2 then (v p.1).im else (v p.1).re : ℝ)| ≤ ‖v‖ := by
    rintro ⟨j, b⟩
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      exact le_trans (Complex.abs_re_le_norm (v j)) (norm_le_pi_norm v j)
    · simp only [ite_true]
      exact le_trans (Complex.abs_im_le_norm (v j)) (norm_le_pi_norm v j)
  have hstep1 : B v = ∑ p : Fin n × Bool,
      (if p.2 then (v p.1).im else (v p.1).re) • B (dirOf p) := by
    conv_lhs => rw [sum_smul_dirOf v]
    rw [map_sum]
    exact Finset.sum_congr rfl fun p _ => by rw [map_smul]
  calc ‖B v‖
      = ‖∑ p : Fin n × Bool, (if p.2 then (v p.1).im else (v p.1).re) • B (dirOf p)‖ := by
        rw [hstep1]
    _ ≤ ∑ p : Fin n × Bool, ‖(if p.2 then (v p.1).im else (v p.1).re) • B (dirOf p)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ p : Fin n × Bool, ‖v‖ * ‖B (dirOf p)‖ := by
        apply Finset.sum_le_sum; intro p _
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hcoef p) (norm_nonneg _)
    _ = (∑ p : Fin n × Bool, ‖B (dirOf p)‖) * ‖v‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ => mul_comm _ _

/-- Multilinear version of `norm_le_sum_norm_dirOf`: for a `k`-multilinear map `C` into
`(ℂⁿ →L[ℝ] ℂ)`, the operator norm is bounded by the sum, over the `2n` directions, of
the norms of the `k`-multilinear maps `w ↦ C w (dirOf p)`. -/
lemma norm_multilinear_le_sum_dirOf {n k : ℕ}
    (C : (Fin n → ℂ) [×k]→L[ℝ] ((Fin n → ℂ) →L[ℝ] ℂ)) :
    ‖C‖ ≤ ∑ p : Fin n × Bool,
      ‖(ContinuousLinearMap.apply ℝ ℂ (dirOf p)).compContinuousMultilinearMap C‖ := by
  refine (ContinuousMultilinearMap.opNorm_le_iff (by positivity)).mpr fun m => ?_
  calc ‖C m‖
      ≤ ∑ p : Fin n × Bool, ‖C m (dirOf p)‖ := norm_le_sum_norm_dirOf (C m)
    _ = ∑ p : Fin n × Bool,
          ‖((ContinuousLinearMap.apply ℝ ℂ (dirOf p)).compContinuousMultilinearMap C) m‖ := by
        apply Finset.sum_congr rfl; intro p _
        simp [ContinuousLinearMap.compContinuousMultilinearMap_coe]
    _ ≤ ∑ p : Fin n × Bool,
          ‖(ContinuousLinearMap.apply ℝ ℂ (dirOf p)).compContinuousMultilinearMap C‖
            * ∏ i, ‖m i‖ := by
        apply Finset.sum_le_sum; intro p _
        exact ContinuousMultilinearMap.le_opNorm _ m
    _ = (∑ p : Fin n × Bool,
          ‖(ContinuousLinearMap.apply ℝ ℂ (dirOf p)).compContinuousMultilinearMap C‖)
            * ∏ i, ‖m i‖ := by
        rw [Finset.sum_mul]

theorem iterDerivNorm_succ_le_dir {n k : ℕ} {Ω : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → ℂ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ (((k+1 : ℕ)) : WithTop ENat) f Ω) :
    Work.CR.Flat.iterDerivNorm (k+1) f Ω
      ≤ ∑ p : Fin n × Bool, Work.CR.Flat.iterDerivNorm k
          (fun z => fderiv ℝ f z
            (if p.2 then Pi.single p.1 Complex.I else Pi.single p.1 (1 : ℂ))) Ω := by
  have hmn : ((k : ℕ) : WithTop ENat) + 1 ≤ (((k+1 : ℕ)) : WithTop ENat) := by
    rw [show (((k+1 : ℕ)) : WithTop ENat) = ((k : ℕ) : WithTop ENat) + 1 from by
      push_cast; ring]
  have hc : ContDiffOn ℝ ((k : ℕ) : WithTop ENat) (fun z => fderiv ℝ f z) Ω :=
    hf.fderiv_of_isOpen hΩ hmn
  rw [Work.CR.Flat.iterDerivNorm]
  refine iSup₂_le fun x hx => ?_
  have hreal : ‖iteratedFDerivWithin ℝ (k+1) f Ω x‖ ≤
      ∑ p : Fin n × Bool,
        ‖iteratedFDerivWithin ℝ k (fun z => fderiv ℝ f z (dirOf p)) Ω x‖ := by
    rw [iteratedFDerivWithin_of_isOpen (k+1) hΩ hx]
    have hcur : (continuousMultilinearCurryRightEquiv' ℝ k (Fin n → ℂ) ℂ)
        (iteratedFDeriv ℝ (k+1) f x) = iteratedFDeriv ℝ k (fun z => fderiv ℝ f z) x := by
      rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
        LinearIsometryEquiv.apply_symm_apply]
    calc ‖iteratedFDeriv ℝ (k+1) f x‖
        = ‖(continuousMultilinearCurryRightEquiv' ℝ k (Fin n → ℂ) ℂ)
            (iteratedFDeriv ℝ (k+1) f x)‖ :=
          ((continuousMultilinearCurryRightEquiv' ℝ k (Fin n → ℂ) ℂ).norm_map _).symm
      _ = ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ f z) x‖ := by rw [hcur]
      _ ≤ ∑ p : Fin n × Bool,
            ‖(ContinuousLinearMap.apply ℝ ℂ (dirOf p)).compContinuousMultilinearMap
              (iteratedFDeriv ℝ k (fun z => fderiv ℝ f z) x)‖ :=
          norm_multilinear_le_sum_dirOf _
      _ = ∑ p : Fin n × Bool,
            ‖iteratedFDerivWithin ℝ k (fun z => fderiv ℝ f z (dirOf p)) Ω x‖ := by
          apply Finset.sum_congr rfl; intro p _
          congr 1
          ext w
          rw [ContinuousLinearMap.compContinuousMultilinearMap_coe]
          rw [show iteratedFDeriv ℝ k (fun z => fderiv ℝ f z) x
                = iteratedFDerivWithin ℝ k (fun z => fderiv ℝ f z) Ω x from
              (iteratedFDerivWithin_of_isOpen k hΩ hx).symm]
          exact (iteratedFDerivWithin_clm_apply_const_apply hΩ.uniqueDiffOn hc le_rfl hx).symm
  calc ENNReal.ofReal ‖iteratedFDerivWithin ℝ (k+1) f Ω x‖
      ≤ ENNReal.ofReal (∑ p : Fin n × Bool,
          ‖iteratedFDerivWithin ℝ k (fun z => fderiv ℝ f z (dirOf p)) Ω x‖) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ∑ p : Fin n × Bool,
          ENNReal.ofReal ‖iteratedFDerivWithin ℝ k (fun z => fderiv ℝ f z (dirOf p)) Ω x‖ := by
        rw [ENNReal.ofReal_sum_of_nonneg]; intro i _; positivity
    _ ≤ ∑ p : Fin n × Bool,
          Work.CR.Flat.iterDerivNorm k (fun z => fderiv ℝ f z (dirOf p)) Ω := by
        apply Finset.sum_le_sum; intro p _
        exact Work.CR.Flat.le_iterDerivNorm k _ Ω hx

end Work.NN.Core
