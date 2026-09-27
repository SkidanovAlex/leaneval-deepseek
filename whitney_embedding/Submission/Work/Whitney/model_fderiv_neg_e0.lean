import Mathlib
import Submission.Work.Whitney.LocalModel
import Submission.Work.Whitney.TransverseAux

/-!
# The derivative of Whitney's local model at `-e₀`

This file computes the Fréchet derivative of Whitney's model
`model n : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)` (see
`Submission/Work/Whitney/LocalModel.lean`) at the second preimage of its self-intersection,
the point `-e₀`:

`fderiv ℝ (model n) (-(e0 n)) v = (v, sheetNegE0 n v)`,

where `sheetNegE0 n` is the linear map `v ↦ (fun i => if i = 0 then (1/2) * v 0 else -(1/2) * v i)`
from `Submission/Work/Whitney/TransverseAux.lean`.  Equivalently, `model n` is *approximately the
linear inclusion* `x ↦ (x, 0)` near `-e₀`, with second block the (linear) "second sheet"
`sheetNegE0`.

Since `uu n x = ∏ i, (1 + x i ^ 2)` evaluates to `2` at `±e₀` (and only the `0`-th coordinate of
`±e₀` is nonzero), the computation is a finite, explicit one: the first block of the model is
`y ↦ y - (2 * y 0 / uu n y) • e₀` (its correction term has derivative zero at `-e₀`), while the
second block is `y ↦ (uu n y)⁻¹ • (e₀ + (y 0) • (y - (y 0) • e₀))`, whose derivative turns out
to be `sheetNegE0 n`.

Everything needed is proved here from `LocalModel` and `TransverseAux` only.
-/

namespace Work.Whitney

open scoped BigOperators

noncomputable section

/-- The `i`-th coordinate functional on `ℝⁿ`, as a continuous linear map. -/
abbrev mfneCoord (n : ℕ) (i : Fin n) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i

/-! ## The denominator `uu` and its derivative -/

lemma mfne_uu_pos (n : ℕ) (x : Fin n → ℝ) : 0 < uu n x := by
  unfold uu
  exact Finset.prod_pos fun i _ => by positivity

lemma mfne_uu_ne_zero (n : ℕ) (x : Fin n → ℝ) : uu n x ≠ 0 := (mfne_uu_pos n x).ne'

/-- `uu n = ∏ i, (1 + x i ^ 2)` is differentiable, with the product rule derivative. -/
lemma mfne_hasFDerivAt_uu (n : ℕ) (x : Fin n → ℝ) :
    HasFDerivAt (uu n)
      (∑ i, (∏ j ∈ Finset.univ.erase i, (1 + x j ^ 2)) • ((2 * x i) • mfneCoord n i)) x := by
  have h : HasFDerivAt (fun y : Fin n → ℝ => ∏ i, (1 + y i ^ 2))
      (∑ i, (∏ j ∈ Finset.univ.erase i, (1 + x j ^ 2)) • ((2 * x i) • mfneCoord n i)) x := by
    refine HasFDerivAt.finsetProd (u := Finset.univ) ?_
    intro i _
    have h0 : HasFDerivAt (fun y : Fin n → ℝ => y i) (mfneCoord n i) x :=
      (mfneCoord n i).hasFDerivAt
    refine ((h0.pow 2).const_add 1).congr_fderiv ?_
    ext v
    simp only [smul_apply, ContinuousLinearMap.proj_apply]
    ring
  exact h

lemma mfne_differentiableAt_uu (n : ℕ) (x : Fin n → ℝ) : DifferentiableAt ℝ (uu n) x :=
  (mfne_hasFDerivAt_uu n x).differentiableAt

lemma mfne_fderiv_uu_apply (n : ℕ) (x v : Fin n → ℝ) :
    fderiv ℝ (uu n) x v = ∑ i, (∏ j ∈ Finset.univ.erase i, (1 + x j ^ 2)) * (2 * x i * v i) := by
  rw [(mfne_hasFDerivAt_uu n x).fderiv]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, mul_assoc]

/-- Derivative of the inverse of a differentiable scalar function on `ℝⁿ`. -/
lemma mfne_hasFDerivAt_inv_comp (n : ℕ) {d : (Fin n → ℝ) → ℝ} {d' : (Fin n → ℝ) →L[ℝ] ℝ}
    {x : Fin n → ℝ} (hd : HasFDerivAt d d' x) (hx : d x ≠ 0) :
    HasFDerivAt (fun y => (d y)⁻¹) (-(d x ^ 2)⁻¹ • d') x := by
  have h : HasFDerivAt (Inv.inv ∘ d)
      (((-ContinuousLinearMap.mulLeftRight ℝ ℝ (d x)⁻¹) (d x)⁻¹).comp d') x :=
    (hasFDerivAt_inv' (𝕜 := ℝ) (R := ℝ) hx).comp x hd
  have hfun : (Inv.inv ∘ d) = fun y => (d y)⁻¹ := rfl
  rw [hfun] at h
  refine h.congr_fderiv ?_
  ext w
  simp only [ContinuousLinearMap.comp_apply, neg_apply, smul_apply,
    ContinuousLinearMap.mulLeftRight_apply]
  rw [sq, mul_inv]
  ring

/-! ## The value of `uu` and of its derivative at `-e₀` -/

lemma mfne_uu_neg_e0 (n : ℕ) [NeZero n] : uu n (-(e0 n)) = 2 := by
  unfold uu
  rw [Finset.prod_eq_single 0]
  · simp [e0]
    norm_num
  · intro b _ hb
    simp [e0, hb]
  · intro h
    exact absurd (Finset.mem_univ 0) h

lemma mfne_fderiv_uu_neg_e0 (n : ℕ) [NeZero n] (v : Fin n → ℝ) :
    fderiv ℝ (uu n) (-(e0 n)) v = -2 * v 0 := by
  rw [mfne_fderiv_uu_apply]
  rw [Finset.sum_eq_single 0]
  · have hprod : (∏ j ∈ Finset.univ.erase 0, (1 + (-(e0 n)) j ^ 2)) = 1 := by
      refine Finset.prod_eq_one ?_
      intro b hb
      rw [Finset.mem_erase] at hb
      simp [e0, hb.1]
    rw [hprod]
    simp [e0]
  · intro b _ hb
    simp [e0, hb]
  · intro h
    exact absurd (Finset.mem_univ 0) h

/-! ## The two components of the model at `-e₀` -/

lemma mfne_hasFDerivAt_model_fst_neg_e0 (n : ℕ) [NeZero n] :
    HasFDerivAt (fun y : Fin n → ℝ => (model n y).1)
      (ContinuousLinearMap.pi (fun i : Fin n => mfneCoord n i)) (-(e0 n)) := by
  refine hasFDerivAt_pi.mpr ?_
  intro i
  show HasFDerivAt (fun y : Fin n → ℝ => (model n y).1 i) (mfneCoord n i) (-(e0 n))
  by_cases hi : i = 0
  · subst hi
    have hfun : (fun y : Fin n → ℝ => (model n y).1 0)
        = fun y => y 0 - 2 * (y 0 * (uu n y)⁻¹) := by
      funext y
      rw [model_fst n y 0]; rw [if_pos rfl]; rw [div_eq_mul_inv]
      ring
    rw [hfun]
    have h0 : HasFDerivAt (fun y : Fin n → ℝ => y 0) (mfneCoord n 0) (-(e0 n)) :=
      (mfneCoord n 0).hasFDerivAt
    have hd : HasFDerivAt (uu n) (fderiv ℝ (uu n) (-(e0 n))) (-(e0 n)) :=
      (mfne_differentiableAt_uu n (-(e0 n))).hasFDerivAt
    have hinv := mfne_hasFDerivAt_inv_comp n hd (mfne_uu_ne_zero n (-(e0 n)))
    have hmul : HasFDerivAt (fun y : Fin n → ℝ => y 0 * (uu n y)⁻¹)
        (((-(e0 n)) 0) • (-((uu n (-(e0 n))) ^ 2)⁻¹ • fderiv ℝ (uu n) (-(e0 n)))
          + (uu n (-(e0 n)))⁻¹ • mfneCoord n 0) (-(e0 n)) := h0.mul hinv
    have hmain : HasFDerivAt (fun y : Fin n → ℝ => y 0 - 2 * (y 0 * (uu n y)⁻¹))
        (mfneCoord n 0 - (2 : ℝ) • (((-(e0 n)) 0) •
            (-((uu n (-(e0 n))) ^ 2)⁻¹ • fderiv ℝ (uu n) (-(e0 n)))
          + (uu n (-(e0 n)))⁻¹ • mfneCoord n 0)) (-(e0 n)) :=
      h0.sub (hmul.const_mul 2)
    refine hmain.congr_fderiv ?_
    ext v
    simp only [sub_apply, add_apply, smul_apply, mfneCoord,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [mfne_fderiv_uu_neg_e0 n v, mfne_uu_neg_e0 n]
    simp [e0]
    ring
  · have hfun : (fun y : Fin n → ℝ => (model n y).1 i) = fun y => y i := by
      funext y
      rw [model_fst n y i]; rw [if_neg hi]; simp
    rw [hfun]
    exact (mfneCoord n i).hasFDerivAt

lemma mfne_hasFDerivAt_model_snd_neg_e0 (n : ℕ) [NeZero n] :
    HasFDerivAt (fun y : Fin n → ℝ => (model n y).2)
      (ContinuousLinearMap.pi (fun i : Fin n =>
        (if i = 0 then (1/2:ℝ) else -(1/2)) • mfneCoord n i)) (-(e0 n)) := by
  refine hasFDerivAt_pi.mpr ?_
  intro i
  show HasFDerivAt (fun y : Fin n → ℝ => (model n y).2 i)
    ((if i = 0 then (1/2:ℝ) else -(1/2)) • mfneCoord n i) (-(e0 n))
  by_cases hi : i = 0
  · subst hi
    have hfun : (fun y : Fin n → ℝ => (model n y).2 0) = fun y => (uu n y)⁻¹ := by
      funext y
      rw [model_snd n y 0]; rw [if_pos rfl]; rw [one_div]
    rw [hfun]
    have hd : HasFDerivAt (uu n) (fderiv ℝ (uu n) (-(e0 n))) (-(e0 n)) :=
      (mfne_differentiableAt_uu n (-(e0 n))).hasFDerivAt
    have hinv := mfne_hasFDerivAt_inv_comp n hd (mfne_uu_ne_zero n (-(e0 n)))
    refine hinv.congr_fderiv ?_
    ext v
    simp only [smul_apply, mfneCoord, ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [mfne_fderiv_uu_neg_e0 n v, mfne_uu_neg_e0 n]
    simp
    ring
  · have hfun : (fun y : Fin n → ℝ => (model n y).2 i)
        = fun y => (y 0 * y i) * (uu n y)⁻¹ := by
      funext y
      rw [model_snd n y i]; rw [if_neg hi]; rw [div_eq_mul_inv]
    rw [hfun]
    have h0 : HasFDerivAt (fun y : Fin n → ℝ => y 0) (mfneCoord n 0) (-(e0 n)) :=
      (mfneCoord n 0).hasFDerivAt
    have hi' : HasFDerivAt (fun y : Fin n → ℝ => y i) (mfneCoord n i) (-(e0 n)) :=
      (mfneCoord n i).hasFDerivAt
    have hc : HasFDerivAt (fun y : Fin n → ℝ => y 0 * y i)
        (((-(e0 n)) 0) • mfneCoord n i + ((-(e0 n)) i) • mfneCoord n 0) (-(e0 n)) :=
      h0.mul hi'
    have hd : HasFDerivAt (uu n) (fderiv ℝ (uu n) (-(e0 n))) (-(e0 n)) :=
      (mfne_differentiableAt_uu n (-(e0 n))).hasFDerivAt
    have hinv := mfne_hasFDerivAt_inv_comp n hd (mfne_uu_ne_zero n (-(e0 n)))
    have hmain : HasFDerivAt (fun y : Fin n → ℝ => (y 0 * y i) * (uu n y)⁻¹)
        ((((-(e0 n)) 0) * ((-(e0 n)) i)) •
            (-((uu n (-(e0 n))) ^ 2)⁻¹ • fderiv ℝ (uu n) (-(e0 n)))
          + (uu n (-(e0 n)))⁻¹ •
            (((-(e0 n)) 0) • mfneCoord n i + ((-(e0 n)) i) • mfneCoord n 0))
        (-(e0 n)) := hc.mul hinv
    refine hmain.congr_fderiv ?_
    ext v
    simp only [add_apply, smul_apply, mfneCoord,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [mfne_fderiv_uu_neg_e0 n v, mfne_uu_neg_e0 n]
    simp [e0, hi]

/-- **The derivative of Whitney's local model at `-e₀`.**  The model
`model n x = (x - (2 * x 0 / uu n x) • e₀, (uu n x)⁻¹ • (e₀ + (x 0) • (x - (x 0) • e₀)))`
(with `uu n x = ∏ i, (1 + x i ^ 2)`) has Fréchet derivative `v ↦ (v, sheetNegE0 n v)` at the
second preimage `-e₀` of its self-intersection: the first block is (to first order) the identity,
and the second block is the linear "second sheet" `sheetNegE0 n`. -/
theorem model_fderiv_neg_e0 (n : ℕ) [NeZero n] :
    ∀ v : Fin n → ℝ,
      fderiv ℝ (Work.Whitney.model n) (-(Work.Whitney.e0 n)) v =
        (v, Work.Whitney.sheetNegE0 n v) := by
  intro v
  have h1 := mfne_hasFDerivAt_model_fst_neg_e0 n
  have h2 := mfne_hasFDerivAt_model_snd_neg_e0 n
  have hm : HasFDerivAt (model n)
      ((ContinuousLinearMap.pi (fun i : Fin n => mfneCoord n i)).prod
        (ContinuousLinearMap.pi (fun i : Fin n =>
          (if i = 0 then (1/2:ℝ) else -(1/2)) • mfneCoord n i))) (-(e0 n)) :=
    h1.prodMk h2
  rw [hm.fderiv, ContinuousLinearMap.prod_apply]
  refine Prod.ext ?_ ?_
  · funext i
    simp only [ContinuousLinearMap.pi_apply, mfneCoord, ContinuousLinearMap.proj_apply]
  · funext i
    simp only [ContinuousLinearMap.pi_apply, smul_apply, mfneCoord,
      ContinuousLinearMap.proj_apply, smul_eq_mul, sheetNegE0, LinearMap.pi_apply,
      LinearMap.smul_apply, LinearMap.proj_apply]

end

end Work.Whitney
