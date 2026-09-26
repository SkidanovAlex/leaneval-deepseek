import Mathlib
import Submission.Work.Drive.trigFun

namespace Work.Drive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `d/dt (cos (k t) • v) = -(k • (sin (k t) • v))`, for integer frequencies `k`. -/
lemma trigFun_hasDerivAt_cos_int_mul_smul (k : ℤ) (v : E) (t : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cos ((k:ℝ)*y) • v)
      (-((k:ℝ) • (Real.sin ((k:ℝ)*t) • v))) t := by
  have h1 : HasDerivAt (fun y : ℝ => Real.cos ((k:ℝ) * y))
      ((-Real.sin ((k:ℝ)*t)) * (k:ℝ)) t := by
    simpa [Function.comp_def] using (Real.hasDerivAt_cos ((k:ℝ) * t)).comp t
      ((hasDerivAt_const t (k:ℝ)).mul (hasDerivAt_id t))
  have h2 := h1.smul_const v
  have he : ((-Real.sin ((k:ℝ)*t)) * (k:ℝ)) • v
      = -((k:ℝ) • (Real.sin ((k:ℝ)*t) • v)) := by
    rw [neg_mul, neg_smul, smul_smul, mul_comm (Real.sin ((k:ℝ)*t)) (k:ℝ)]
  rw [he] at h2
  exact h2

/-- `d/dt (sin (k t) • w) = k • (cos (k t) • w)`, for integer frequencies `k`. -/
lemma trigFun_hasDerivAt_sin_int_mul_smul (k : ℤ) (w : E) (t : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin ((k:ℝ)*y) • w)
      ((k:ℝ) • (Real.cos ((k:ℝ)*t) • w)) t := by
  have h1 : HasDerivAt (fun y : ℝ => Real.sin ((k:ℝ) * y))
      (Real.cos ((k:ℝ)*t) * (k:ℝ)) t := by
    simpa [Function.comp_def] using (Real.hasDerivAt_sin ((k:ℝ) * t)).comp t
      ((hasDerivAt_const t (k:ℝ)).mul (hasDerivAt_id t))
  have h2 := h1.smul_const w
  have he : (Real.cos ((k:ℝ)*t) * (k:ℝ)) • w
      = (k:ℝ) • (Real.cos ((k:ℝ)*t) • w) := by
    rw [smul_smul, mul_comm (Real.cos ((k:ℝ)*t)) (k:ℝ)]
  rw [he] at h2
  exact h2

/-- The coefficient computation behind `trigFun_hasDerivAt_prim`, for a single frequency `k`:
the derivative of the `k`-th `cos`-term of `prim P` plus the derivative of the `k`-th `sin`-term of
`prim P` equals the `k`-th term of `P.toFun`.  For `k ≠ 0` the coefficients
`(prim P).c k = -(1/k) • P.d k`, `(prim P).d k = (1/k) • P.c k` turn the derivative
`cos (k t) • (k • d'_k) - sin (k t) • (k • c'_k)` into `cos (k t) • P.c k + sin (k t) • P.d k`
via `k * (1/k) = 1`; for `k = 0` both sides vanish (`(prim P).d 0 = 0`, and `P.c 0 = 0`). -/
lemma trigFun_prim_coeff_deriv (P : TrigFun E) (h0 : P.c 0 = 0) (k : ℤ) (t : ℝ) :
    -((k:ℝ) • (Real.sin ((k:ℝ)*t) • (TrigFun.prim P).c k))
        + (k:ℝ) • (Real.cos ((k:ℝ)*t) • (TrigFun.prim P).d k)
      = Real.cos ((k:ℝ)*t) • P.c k + Real.sin ((k:ℝ)*t) • P.d k := by
  by_cases hk : k = 0
  · subst hk
    simp [TrigFun.prim, Finsupp.onFinset_apply, h0]
  · have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast hk
    simp only [TrigFun.prim, Finsupp.onFinset_apply, if_neg hk, smul_neg, smul_smul, neg_neg]
    have h1 : (k:ℝ) * (Real.sin ((k:ℝ)*t) * ((k:ℝ))⁻¹) = Real.sin ((k:ℝ)*t) := by
      calc (k:ℝ) * (Real.sin ((k:ℝ)*t) * ((k:ℝ))⁻¹)
          = Real.sin ((k:ℝ)*t) * ((k:ℝ) * ((k:ℝ))⁻¹) := by ring
        _ = Real.sin ((k:ℝ)*t) := by rw [mul_inv_cancel₀ hkR, mul_one]
    have h2 : (k:ℝ) * (Real.cos ((k:ℝ)*t) * ((k:ℝ))⁻¹) = Real.cos ((k:ℝ)*t) := by
      calc (k:ℝ) * (Real.cos ((k:ℝ)*t) * ((k:ℝ))⁻¹)
          = Real.cos ((k:ℝ)*t) * ((k:ℝ) * ((k:ℝ))⁻¹) := by ring
        _ = Real.cos ((k:ℝ)*t) := by rw [mul_inv_cancel₀ hkR, mul_one]
    rw [h1, h2, add_comm]

/-- If the constant coefficient of `P : TrigFun E` vanishes, then `TrigFun.prim P` (the termwise
antiderivative defined in `Submission/Work/Drive/trigFun.lean`) is a primitive of `P.toFun`.
Termwise: `d/dt (cos (k t) • c'_k + sin (k t) • d'_k) = cos (k t) • (k • d'_k) - sin (k t) • (k • c'_k)`,
and for `k ≠ 0` the definitions `c'_k = -(1/k) • d_k`, `d'_k = (1/k) • c_k` turn this into
`cos (k t) • c_k + sin (k t) • d_k` (using `k * (1/k) = 1`); the `k = 0` term of `prim P` is a
constant (derivative `0`), matching `P.c 0 = 0` on the other side.
Route: `HasDerivAt.sum`, `Real.hasDerivAt_cos`/`Real.hasDerivAt_sin` composed with `t ↦ (k:ℝ)*t`,
`HasDerivAt.smul_const`, then identify the two `Finsupp.sum`s using `Finsupp.onFinset_apply`,
`Finsupp.sum_congr`, `Finset.sum_subset` (coefficients of `P` vanish off its support) and
`inv_mul_cancel₀`/`smul_smul`. -/
theorem trigFun_hasDerivAt_prim {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Work.Drive.TrigFun E) (h0 : P.c 0 = 0) (t : ℝ) :
    HasDerivAt (Work.Drive.TrigFun.prim P).toFun (P.toFun t) t := by
  classical
  set S := insert 0 (P.c.support ∪ P.d.support) with hS
  have hsubc : (TrigFun.prim P).c.support ⊆ S := by
    rw [hS]; exact Finset.filter_subset _ _
  have hsubd : (TrigFun.prim P).d.support ⊆ S := by
    rw [hS]; exact Finset.filter_subset _ _
  have hsubc2 : P.c.support ⊆ S := by
    rw [hS]; exact Finset.Subset.trans Finset.subset_union_left (Finset.subset_insert 0 _)
  have hsubd2 : P.d.support ⊆ S := by
    rw [hS]; exact Finset.Subset.trans Finset.subset_union_right (Finset.subset_insert 0 _)
  -- `(prim P).toFun` as a sum over the finite set `S`
  have hL : ∀ y : ℝ, (TrigFun.prim P).toFun y
      = ∑ k ∈ S, (Real.cos ((k:ℝ)*y) • (TrigFun.prim P).c k
          + Real.sin ((k:ℝ)*y) • (TrigFun.prim P).d k) := by
    intro y
    rw [TrigFun.toFun]
    rw [Finsupp.sum_of_support_subset _ hsubc (fun k v => Real.cos ((k:ℝ)*y) • v)
          (by intro i hi; simp),
        Finsupp.sum_of_support_subset _ hsubd (fun k v => Real.sin ((k:ℝ)*y) • v)
          (by intro i hi; simp)]
    rw [Finset.sum_add_distrib]
  -- term-by-term derivative
  have hder : ∀ k ∈ S, HasDerivAt (fun y : ℝ => Real.cos ((k:ℝ)*y) • (TrigFun.prim P).c k
        + Real.sin ((k:ℝ)*y) • (TrigFun.prim P).d k)
      (Real.cos ((k:ℝ)*t) • P.c k + Real.sin ((k:ℝ)*t) • P.d k) t := by
    intro k _
    have hA := trigFun_hasDerivAt_cos_int_mul_smul (E := E) k ((TrigFun.prim P).c k) t
    have hB := trigFun_hasDerivAt_sin_int_mul_smul (E := E) k ((TrigFun.prim P).d k) t
    have hAB := hA.add hB
    rw [trigFun_prim_coeff_deriv P h0 k t] at hAB
    exact hAB
  -- the summed derivative is `P.toFun t`
  have hEq : (∑ k ∈ S, (Real.cos ((k:ℝ)*t) • P.c k + Real.sin ((k:ℝ)*t) • P.d k))
      = P.toFun t := by
    change (∑ k ∈ S, (Real.cos ((k:ℝ)*t) • P.c k + Real.sin ((k:ℝ)*t) • P.d k))
      = P.c.sum (fun k v => Real.cos ((k:ℝ)*t) • v)
        + P.d.sum (fun k v => Real.sin ((k:ℝ)*t) • v)
    rw [Finset.sum_add_distrib]
    rw [← Finsupp.sum_of_support_subset P.c hsubc2 (fun k v => Real.cos ((k:ℝ)*t) • v)
          (by intro i hi; simp),
        ← Finsupp.sum_of_support_subset P.d hsubd2 (fun k v => Real.sin ((k:ℝ)*t) • v)
          (by intro i hi; simp)]
  have hfinal : HasDerivAt (fun y : ℝ => ∑ k ∈ S, (Real.cos ((k:ℝ)*y) • (TrigFun.prim P).c k
        + Real.sin ((k:ℝ)*y) • (TrigFun.prim P).d k)) (P.toFun t) t := by
    have h := HasDerivAt.sum hder
    rw [hEq] at h
    rw [show (∑ i ∈ S, (fun y : ℝ => Real.cos ((i:ℝ)*y) • (TrigFun.prim P).c i
            + Real.sin ((i:ℝ)*y) • (TrigFun.prim P).d i))
        = fun y : ℝ => ∑ i ∈ S, (Real.cos ((i:ℝ)*y) • (TrigFun.prim P).c i
            + Real.sin ((i:ℝ)*y) • (TrigFun.prim P).d i) from by
      funext y; exact Finset.sum_apply y S _] at h
    exact h
  have hEqF : (fun y : ℝ => ∑ k ∈ S, (Real.cos ((k:ℝ)*y) • (TrigFun.prim P).c k
        + Real.sin ((k:ℝ)*y) • (TrigFun.prim P).d k)) = (TrigFun.prim P).toFun :=
    funext (fun y => (hL y).symm)
  rw [hEqF] at hfinal
  exact hfinal

end Work.Drive
