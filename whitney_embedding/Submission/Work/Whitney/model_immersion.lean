import Mathlib
import Submission.Work.Whitney.LocalModel

namespace Work.Whitney

open scoped Manifold ContDiff BigOperators
open Set Filter Topology

/-! ## Facts about the denominator `uu n x = ∏ i, (1 + x i ^ 2)` -/

lemma uu_pos (n : ℕ) (x : Fin n → ℝ) : 0 < uu n x := by
  unfold uu
  exact Finset.prod_pos fun i _ => by positivity

lemma uu_ne_zero (n : ℕ) (x : Fin n → ℝ) : uu n x ≠ 0 := (uu_pos n x).ne'

lemma contDiff_uu (n : ℕ) : ContDiff ℝ ⊤ (uu n) := by
  unfold uu
  fun_prop

/-- The `i`-th coordinate functional on `ℝⁿ`. -/
abbrev coord (n : ℕ) (i : Fin n) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i

@[simp] lemma coord_apply (n : ℕ) (i : Fin n) (w : Fin n → ℝ) : coord n i w = w i := rfl

lemma fderiv_coord (n : ℕ) (i : Fin n) (x w : Fin n → ℝ) :
    fderiv ℝ (fun y : Fin n → ℝ => y i) x w = w i := by
  have h1 : HasFDerivAt (⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i))
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) x :=
    ContinuousLinearMap.hasFDerivAt _
  have h2 : fderiv ℝ (fun y : Fin n → ℝ => y i) x
      = ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i := h1.fderiv
  rw [h2]
  simp

/-- Derivative of the inverse of a differentiable scalar function. -/
lemma hasFDerivAt_inv_comp (n : ℕ) {d : (Fin n → ℝ) → ℝ} {d' : (Fin n → ℝ) →L[ℝ] ℝ}
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

/-! ## Derivatives of `uu` -/

lemma hasFDerivAt_uu (n : ℕ) (x : Fin n → ℝ) :
    HasFDerivAt (uu n)
      (∑ i, (∏ j ∈ Finset.univ.erase i, (1 + x j ^ 2)) •
        ((2 * x i) • coord n i)) x := by
  have h : HasFDerivAt (fun y : Fin n → ℝ => ∏ i, (1 + y i ^ 2))
      (∑ i, (∏ j ∈ Finset.univ.erase i, (1 + x j ^ 2)) • ((2 * x i) • coord n i)) x := by
    refine HasFDerivAt.finsetProd (u := Finset.univ) ?_
    intro i hi
    have h0 : HasFDerivAt (fun y : Fin n → ℝ => y i) (coord n i) x := (coord n i).hasFDerivAt
    refine ((h0.pow 2).const_add 1).congr_fderiv ?_
    ext v
    simp only [smul_apply, ContinuousLinearMap.proj_apply]
    ring
  exact h

lemma differentiableAt_uu (n : ℕ) (x : Fin n → ℝ) : DifferentiableAt ℝ (uu n) x :=
  (hasFDerivAt_uu n x).differentiableAt

lemma fderiv_uu_apply (n : ℕ) (x v : Fin n → ℝ) :
    fderiv ℝ (uu n) x v = ∑ i, (∏ j ∈ Finset.univ.erase i, (1 + x j ^ 2)) * (2 * x i * v i) := by
  rw [(hasFDerivAt_uu n x).fderiv]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, mul_assoc]

lemma fderiv_uu_e0 (n : ℕ) [NeZero n] (x : Fin n → ℝ) :
    fderiv ℝ (uu n) x (e0 n) = 2 * x 0 * ∏ j ∈ Finset.univ.erase 0, (1 + x j ^ 2) := by
  rw [fderiv_uu_apply]
  rw [Finset.sum_eq_single 0]
  · simp [e0]
    ring
  · intro b _ hb
    simp [e0, hb]
  · intro h
    exact absurd (Finset.mem_univ 0) h

/-! ## The coordinate functions of the model -/

lemma fderiv_model_fst_apply_ne (n : ℕ) [NeZero n] {i : Fin n} (hi : i ≠ 0) (x w : Fin n → ℝ) :
    fderiv ℝ (fun y => (model n y).1 i) x w = w i := by
  have hfun : (fun y : Fin n → ℝ => (model n y).1 i) = fun y => y i := by
    funext y; simp [model, hi]
  rw [hfun, fderiv_coord]

lemma fderiv_model_fst_zero_apply (n : ℕ) [NeZero n] (x w : Fin n → ℝ) :
    fderiv ℝ (fun y => (model n y).1 0) x w
      = w 0 - 2 * (uu n x)⁻¹ * w 0
        + 2 * x 0 * (uu n x ^ 2)⁻¹ * (fderiv ℝ (uu n) x w) := by
  have hfun : (fun y : Fin n → ℝ => (model n y).1 0)
      = fun y => y 0 - 2 * (y 0 * (uu n y)⁻¹) := by
    funext y; simp [model, div_eq_mul_inv]; ring
  rw [hfun]
  have h0 : HasFDerivAt (fun y : Fin n → ℝ => y 0) (coord n 0) x := (coord n 0).hasFDerivAt
  have hd : HasFDerivAt (uu n) (fderiv ℝ (uu n) x) x := (differentiableAt_uu n x).hasFDerivAt
  have hinv := hasFDerivAt_inv_comp n hd (uu_ne_zero n x)
  have hm : HasFDerivAt (fun y : Fin n → ℝ => y 0 * (uu n y)⁻¹)
      ((x 0) • (-((uu n x) ^ 2)⁻¹ • fderiv ℝ (uu n) x) + (uu n x)⁻¹ • coord n 0) x :=
    h0.mul hinv
  have hmain : HasFDerivAt (fun y : Fin n → ℝ => y 0 - 2 * (y 0 * (uu n y)⁻¹))
      (coord n 0 - (2 : ℝ) • ((x 0) • (-((uu n x) ^ 2)⁻¹ • fderiv ℝ (uu n) x)
        + (uu n x)⁻¹ • coord n 0)) x :=
    h0.sub (hm.const_mul 2)
  rw [hmain.fderiv]
  simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

lemma fderiv_model_snd_zero_apply (n : ℕ) [NeZero n] (x w : Fin n → ℝ) :
    fderiv ℝ (fun y => (model n y).2 0) x w = -((uu n x) ^ 2)⁻¹ * (fderiv ℝ (uu n) x w) := by
  have hfun : (fun y : Fin n → ℝ => (model n y).2 0) = fun y => (uu n y)⁻¹ := by
    funext y; simp [model]
  rw [hfun]
  have hd : HasFDerivAt (uu n) (fderiv ℝ (uu n) x) x := (differentiableAt_uu n x).hasFDerivAt
  rw [(hasFDerivAt_inv_comp n hd (uu_ne_zero n x)).fderiv]
  simp only [smul_apply, smul_eq_mul]

lemma fderiv_model_snd_apply_ne (n : ℕ) [NeZero n] {i : Fin n} (hi : i ≠ 0) (x w : Fin n → ℝ) :
    fderiv ℝ (fun y => (model n y).2 i) x w
      = (uu n x)⁻¹ * (x i * w 0 + x 0 * w i)
        - x 0 * x i * (uu n x ^ 2)⁻¹ * (fderiv ℝ (uu n) x w) := by
  have hfun : (fun y : Fin n → ℝ => (model n y).2 i)
      = fun y => (y 0 * y i) * (uu n y)⁻¹ := by
    funext y; simp [model, hi, div_eq_mul_inv]
  rw [hfun]
  have h0 : HasFDerivAt (fun y : Fin n → ℝ => y 0) (coord n 0) x := (coord n 0).hasFDerivAt
  have hi' : HasFDerivAt (fun y : Fin n → ℝ => y i) (coord n i) x := (coord n i).hasFDerivAt
  have hc : HasFDerivAt (fun y : Fin n → ℝ => y 0 * y i)
      ((x 0) • coord n i + (x i) • coord n 0) x := h0.mul hi'
  have hd : HasFDerivAt (uu n) (fderiv ℝ (uu n) x) x := (differentiableAt_uu n x).hasFDerivAt
  have hinv := hasFDerivAt_inv_comp n hd (uu_ne_zero n x)
  have hmain : HasFDerivAt (fun y : Fin n → ℝ => (y 0 * y i) * (uu n y)⁻¹)
      ((x 0 * x i) • (-((uu n x) ^ 2)⁻¹ • fderiv ℝ (uu n) x)
        + (uu n x)⁻¹ • ((x 0) • coord n i + (x i) • coord n 0)) x :=
    hc.mul hinv
  rw [hmain.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

/-! ## Smoothness of the model -/

lemma contDiff_model_fst (n : ℕ) [NeZero n] (i : Fin n) :
    ContDiff ℝ ⊤ (fun y : Fin n → ℝ => (model n y).1 i) := by
  by_cases hi : i = 0
  · subst hi
    have hfun : (fun y : Fin n → ℝ => (model n y).1 0)
        = fun y => y 0 - 2 * (y 0 * (uu n y)⁻¹) := by
      funext y; simp [model, div_eq_mul_inv]; ring
    rw [hfun]
    have h1 : ContDiff ℝ ⊤ (fun y : Fin n → ℝ => y 0) := (coord n 0).contDiff
    have h2 : ContDiff ℝ ⊤ (fun y : Fin n → ℝ => (uu n y)⁻¹) :=
      (contDiff_uu n).inv fun y => uu_ne_zero n y
    have h3 : ContDiff ℝ ⊤ (fun y : Fin n → ℝ => y 0 * (uu n y)⁻¹) := h1.mul h2
    have h4 : ContDiff ℝ ⊤ (fun y : Fin n → ℝ => 2 * (y 0 * (uu n y)⁻¹)) :=
      (contDiff_const (c := (2 : ℝ))).mul h3
    exact h1.sub h4
  · have hfun : (fun y : Fin n → ℝ => (model n y).1 i) = fun y => y i := by
      funext y; simp [model, hi]
    rw [hfun]
    exact (coord n i).contDiff

lemma contDiff_model_snd (n : ℕ) [NeZero n] (i : Fin n) :
    ContDiff ℝ ⊤ (fun y : Fin n → ℝ => (model n y).2 i) := by
  by_cases hi : i = 0
  · subst hi
    have hfun : (fun y : Fin n → ℝ => (model n y).2 0) = fun y => (uu n y)⁻¹ := by
      funext y; simp [model]
    rw [hfun]
    exact (contDiff_uu n).inv fun y => uu_ne_zero n y
  · have hfun : (fun y : Fin n → ℝ => (model n y).2 i)
        = fun y => (y 0 * y i) * (uu n y)⁻¹ := by
      funext y; simp [model, hi, div_eq_mul_inv]
    rw [hfun]
    have h1 : ContDiff ℝ ⊤ (fun y : Fin n → ℝ => y 0) := (coord n 0).contDiff
    have h2 : ContDiff ℝ ⊤ (fun y : Fin n → ℝ => y i) := (coord n i).contDiff
    have h3 : ContDiff ℝ ⊤ (fun y : Fin n → ℝ => (uu n y)⁻¹) :=
      (contDiff_uu n).inv fun y => uu_ne_zero n y
    exact (h1.mul h2).mul h3

lemma contDiff_model (n : ℕ) [NeZero n] : ContDiff ℝ ⊤ (model n) := by
  have h1 : ContDiff ℝ ⊤ (fun y : Fin n → ℝ => (model n y).1) :=
    contDiff_pi.mpr fun i => contDiff_model_fst n i
  have h2 : ContDiff ℝ ⊤ (fun y : Fin n → ℝ => (model n y).2) :=
    contDiff_pi.mpr fun i => contDiff_model_snd n i
  exact h1.prodMk h2

lemma differentiableAt_model (n : ℕ) [NeZero n] (x : Fin n → ℝ) :
    DifferentiableAt ℝ (model n) x :=
  ((contDiff_model n).contDiffAt).differentiableAt (by simp)

/-! ## Relating `fderiv (model n) x` to the coordinate functions -/

lemma fderiv_model_fst_apply_eq (n : ℕ) [NeZero n] (x w : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (fun y => (model n y).1 i) x w = ((fderiv ℝ (model n) x) w).1 i := by
  have hm := differentiableAt_model n x
  have h1 : DifferentiableAt ℝ (fun y => (model n y).1) x := hm.fst
  rw [fderiv_apply h1 i, fderiv.fst hm]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

lemma fderiv_model_snd_apply_eq (n : ℕ) [NeZero n] (x w : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (fun y => (model n y).2 i) x w = ((fderiv ℝ (model n) x) w).2 i := by
  have hm := differentiableAt_model n x
  have h1 : DifferentiableAt ℝ (fun y => (model n y).2) x := hm.snd
  rw [fderiv_apply h1 i, fderiv.snd hm]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

/-! ## The kernel of `fderiv (model n) x` is trivial -/

lemma model_fderiv_zero (n : ℕ) [NeZero n] (x w : Fin n → ℝ)
    (h0 : fderiv ℝ (model n) x w = 0) : w = 0 := by
  have hcomp1 : ∀ i, fderiv ℝ (fun y => (model n y).1 i) x w = 0 := by
    intro i
    rw [fderiv_model_fst_apply_eq n x w i, h0]
    simp
  have hcomp2 : ∀ i, fderiv ℝ (fun y => (model n y).2 i) x w = 0 := by
    intro i
    rw [fderiv_model_snd_apply_eq n x w i, h0]
    simp
  have hw_ne : ∀ i, i ≠ 0 → w i = 0 := by
    intro i hi
    have h := hcomp1 i
    rwa [fderiv_model_fst_apply_ne n hi x w] at h
  -- the derivative of `uu` is zero at `w`
  have hD0 : fderiv ℝ (uu n) x w = 0 := by
    have h := hcomp2 0
    rw [fderiv_model_snd_zero_apply n x w] at h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact absurd (neg_eq_zero.mp h1) (inv_ne_zero (pow_ne_zero 2 (uu_ne_zero n x)))
    · exact h2
  have hw_eq : w = w 0 • e0 n := by
    funext i
    by_cases hi : i = 0
    · subst hi; simp [e0]
    · rw [hw_ne i hi]; simp [e0, hi]
  have hfD : fderiv ℝ (uu n) x w
      = w 0 * (2 * x 0 * ∏ j ∈ Finset.univ.erase 0, (1 + x j ^ 2)) := by
    conv_lhs => rw [hw_eq]
    rw [map_smul, fderiv_uu_e0, smul_eq_mul]
  by_cases hw0 : w 0 = 0
  · funext i
    by_cases hi : i = 0
    · subst hi; simpa using hw0
    · simpa [Pi.zero_apply] using hw_ne i hi
  · exfalso
    -- equation from the first block
    have e1 : w 0 * (1 - 2 * (uu n x)⁻¹) = 0 := by
      have h := hcomp1 0
      rw [fderiv_model_fst_zero_apply n x w, hD0] at h
      have h' : w 0 - 2 * (uu n x)⁻¹ * w 0 = 0 := by simpa using h
      rw [← h']
      ring
    -- equation from the second block
    have hPne : (∏ j ∈ Finset.univ.erase 0, (1 + x j ^ 2)) ≠ 0 :=
      (Finset.prod_pos fun j _ => by positivity).ne'
    have hx0 : x 0 = 0 := by
      have h2 : w 0 * (2 * x 0 * (∏ j ∈ Finset.univ.erase 0, (1 + x j ^ 2))) = 0 := by
        rw [← hfD, hD0]
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hw0
      · rcases mul_eq_zero.mp h with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact absurd h'' (by norm_num)
          · exact h''
        · exact absurd h' hPne
    have hxne : ∀ i, i ≠ 0 → x i = 0 := by
      intro i hi
      have h := hcomp2 i
      rw [fderiv_model_snd_apply_ne n hi x w, hD0, hw_ne i hi] at h
      have h' : (uu n x)⁻¹ * (x i * w 0) = 0 := by simpa using h
      have h2 : uu n x * ((uu n x)⁻¹ * (x i * w 0)) = 0 := by rw [h', mul_zero]
      rw [← mul_assoc, mul_inv_cancel₀ (uu_ne_zero n x), one_mul] at h2
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact h3
      · exact absurd h3 hw0
    have hxall : x = 0 := by
      funext i
      by_cases hi : i = 0
      · subst hi; simpa using hx0
      · simpa [Pi.zero_apply] using hxne i hi
    have huu1 : uu n x = 1 := by rw [hxall]; simp [uu]
    have hcoef : 1 - 2 * (uu n x)⁻¹ = 0 := by
      rcases mul_eq_zero.mp e1 with h | h
      · exact absurd h hw0
      · exact h
    have huu2 : uu n x = 2 := by
      have h2 : 2 * (uu n x)⁻¹ = 1 := by linarith
      have h3 : 2 = uu n x := by
        have h4 := congrArg (fun t => t * uu n x) h2
        simp only [one_mul] at h4
        rw [mul_assoc, inv_mul_cancel₀ (uu_ne_zero n x), mul_one] at h4
        exact h4
      exact h3.symm
    linarith [huu1, huu2]

/-- The explicit Whitney model `x ↦ (fun i => x i - (if i = 0 then 2 * x i / uu n x else 0), fun i => if i = 0 then 1 / uu n x else x 0 * x i / uu n x)`, where `uu n x = ∏ i, (1 + x i ^ 2)`, is smooth and is an immersion at every point of `ℝⁿ`.  (Do NOT reword the docstring; the statement is exactly as reviewed.) -/
theorem model_immersion (n : ℕ) [NeZero n] :
    ContDiff ℝ ⊤ (Work.Whitney.model n) ∧
      ∀ x : Fin n → ℝ, Function.Injective (fderiv ℝ (Work.Whitney.model n) x) := by
  refine ⟨contDiff_model n, ?_⟩
  intro x u v huv
  have h0 : fderiv ℝ (model n) x (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have := model_fderiv_zero n x (u - v) h0
  exact sub_eq_zero.mp this

end Work.Whitney
