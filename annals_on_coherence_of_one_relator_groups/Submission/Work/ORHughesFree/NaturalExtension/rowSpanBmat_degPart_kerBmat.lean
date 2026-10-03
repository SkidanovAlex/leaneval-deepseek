import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.DualityDefs
import Submission.Work.ORHughesFree.NaturalExtension.DualityAPI

universe u

namespace Work.ORHughesFree.NaturalExtension

/-! ## Coefficient bookkeeping for `toPoly` and for multiplication by powers of `t`

The two inclusions of `rowSpanBmat_degPart_kerBmat` are proved by comparing coefficient vectors
with the coefficients of the elements `t^i * p` and `toPoly k x * p` of `SkewL R`.  This section
collects the elementary lemmas doing the coefficient computation.

* `coeffElt_single_mul_aux` : the `w`-th coefficient of `single (ofAdd i) c * f`;
* `coeffElt_toPoly_aux` : the `w`-th coefficient of `toPoly k x`;
* `coeffElt_toPoly_mul_aux` : the `w`-th coefficient of `toPoly k x * p`, in a form directly
  comparable with a row of `Bmat p k`;
* `coeffElt_t_pow_mul_aux` : the `w`-th coefficient of `t^i * p`. -/

section Aux

variable {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]

/-- The inverse of `ofAdd v` followed by `ofAdd w` is `ofAdd (w - v)`: rewriting the group
operation of `Multiplicative ℤ` in terms of the additive one. -/
private lemma ofAdd_inv_mul_aux (v w : ℤ) :
    (Multiplicative.ofAdd v)⁻¹ * Multiplicative.ofAdd w = Multiplicative.ofAdd (w - v) := by
  rw [← ofAdd_neg, ← ofAdd_add]
  congr 1
  ring

/-- Convolution formula for the coefficient of a product with a monomial: the `w`-th coefficient
of `single (ofAdd i) c * f` is `c * (t^i • coeffElt f (w - i))`. -/
private lemma coeffElt_single_mul_aux (i : ℤ) (c : R) (f : SkewL R) (w : ℤ) :
    coeffElt (SkewMonoidAlgebra.single (Multiplicative.ofAdd i) c * f) w =
      c * (Multiplicative.ofAdd i • coeffElt f (w - i)) := by
  rw [coeffElt, SkewMonoidAlgebra.coeff_single_mul, ofAdd_inv_mul_aux]
  rfl

/-- Coefficient extraction is additive. -/
private lemma coeffElt_add_aux {U : Type u} [AddMonoid U] (a b : SkewL U) (w : ℤ) :
    coeffElt (a + b) w = coeffElt a w + coeffElt b w := by
  simp [coeffElt, SkewMonoidAlgebra.coeff_add]

/-- Coefficients of a finite sum of elements of `SkewL R`. -/
private lemma coeffElt_finset_sum_aux {ι : Type*} (s : Finset ι) (F : ι → SkewL R) (w : ℤ) :
    coeffElt (∑ i ∈ s, F i) w = ∑ i ∈ s, coeffElt (F i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeffElt]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, coeffElt_add_aux, ih]

/-- Coefficients of a monomial. -/
private lemma coeffElt_single_aux {U : Type u} [AddMonoid U] (i : ℤ) (c : U) (w : ℤ) :
    coeffElt (SkewMonoidAlgebra.single (Multiplicative.ofAdd i) c) w = if i = w then c else 0 := by
  rw [coeffElt, SkewMonoidAlgebra.coeff_single]
  by_cases h : i = w
  · subst h; simp
  · rw [Finsupp.single_eq_of_ne' (fun hh => h (Multiplicative.ofAdd.injective hh)), if_neg h]

/-- Coefficients of `toPoly k x = ∑_i x_i t^i`. -/
private lemma coeffElt_toPoly_aux (k : ℕ) (x : Fin (k+1) → R) (w : ℤ) :
    coeffElt (toPoly k x) w = ∑ i : Fin (k+1), (if ((i:ℕ):ℤ) = w then x i else 0 : R) := by
  rw [toPoly, coeffElt_finset_sum_aux (R := R)]
  exact Finset.sum_congr rfl (fun i _ => coeffElt_single_aux ((i:ℕ):ℤ) (x i) w)

/-- The coefficient vector of `toPoly k x` in degrees `0,…,k` is `x`. -/
private lemma cvec_toPoly_aux (k : ℕ) (x : Fin (k+1) → R) :
    cvec R k (toPoly k x) = x := by
  funext j
  change coeffElt (toPoly k x) ((j:ℕ):ℤ) = x j
  rw [coeffElt_toPoly_aux (R := R)]
  have h1 : ∀ b ∈ (Finset.univ : Finset (Fin (k+1))), b ≠ j →
      (if ((b:ℕ):ℤ) = ((j:ℕ):ℤ) then x b else 0 : R) = 0 := by
    intro b _ hb
    rw [if_neg]
    intro hh
    exact hb (Fin.ext (by omega))
  refine ((Finset.sum_eq_single (s := (Finset.univ : Finset (Fin (k+1))))
    (f := fun i : Fin (k+1) => (if ((i:ℕ):ℤ) = ((j:ℕ):ℤ) then x i else 0 : R)) j h1
    (fun h => absurd (Finset.mem_univ j) h)).trans ?_)
  rw [if_pos rfl]

/-- `toPoly k x` has no coefficients of negative degree. -/
private lemma coeffElt_toPoly_eq_zero_of_lt_aux (k : ℕ) (x : Fin (k+1) → R) {w : ℤ}
    (hw : w < 0) : coeffElt (toPoly k x) w = 0 := by
  rw [coeffElt_toPoly_aux (R := R)]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [if_neg]
  intro h
  have : (0:ℤ) ≤ ((i:ℕ):ℤ) := Int.natCast_nonneg _
  omega

/-- The coefficient of `toPoly k x * p` in degree `w`, in the form in which it is compared with
the rows of `Bmat p k`. -/
private lemma coeffElt_toPoly_mul_aux (k : ℕ) (x : Fin (k+1) → R) (p : SkewL R) (w : ℤ) :
    coeffElt (toPoly k x * p) w =
      ∑ i : Fin (k+1), x i * (Multiplicative.ofAdd ((i:ℕ):ℤ) • coeffElt p (w - ((i:ℕ):ℤ))) := by
  rw [toPoly, Finset.sum_mul, coeffElt_finset_sum_aux (R := R)]
  exact Finset.sum_congr rfl (fun i _ => coeffElt_single_mul_aux ((i:ℕ):ℤ) (x i) p w)

/-- Normal form for the powers of the variable `t` of `R[t^{±1};τ]`: `t ^ k = single (ofAdd k) 1`. -/
private lemma skewLaurentT_pow_eq_single_aux (k : ℕ) :
    (skewLaurentT : SkewL R) ^ k = SkewMonoidAlgebra.single (Multiplicative.ofAdd (k : ℤ)) 1 := by
  rw [skewLaurentT]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, SkewMonoidAlgebra.single_mul_single, ← ofAdd_add]
    simp

/-- Left multiplication by `t ^ N` shifts coefficients up by `N` (and applies the twist `τ`). -/
private lemma coeffElt_t_pow_mul_aux (f : SkewL R) (N : ℕ) (w : ℤ) :
    coeffElt (((skewLaurentT : SkewL R) ^ N) * f) w =
      Multiplicative.ofAdd ((N : ℕ) : ℤ) • coeffElt f (w - ((N : ℕ) : ℤ)) := by
  rw [skewLaurentT_pow_eq_single_aux, coeffElt_single_mul_aux, one_mul]

end Aux

/-- The row span of `Bmat p k` consists of coefficient vectors of `t^i * p` (`i ≤ k`), which
lie in `degPart R (genIdeal p) (k + upDeg p)`; the row kernel of `Bmat p k` consists of the
coefficient vectors `cvec R k f` of the polynomial elements `f = ∑_i x_i t^i` of `annSet p`
with `f * p = 0` (the hypothesis `hp` is needed: for `x ∈ kerBmat`, all coefficients of
`toPoly k x * p` in degrees `0..k+upDeg p` vanish, and `toPoly k x * p` has no other degrees). -/
theorem rowSpanBmat_degPart_kerBmat {R : Type u} [Ring R] [VonNeumannRegularRing R]
    [MulSemiringAction (Multiplicative ℤ) R] (rk : SylvesterRank R)
    (p : SkewL R) (hp : ∀ k : ℤ, k < 0 → coeffElt p k = 0) (k : ℕ) :
    (rowSpanBmat p k ≤ degPart R (genIdeal p) (k + upDeg p)) ∧
      (kerBmat p k ≤ degPart R (annSet p) k) := by
  constructor
  · -- Every row of `Bmat p k` is the coefficient vector of `t^i * p`, a polynomial left
    -- multiple of `p` of degree `≤ k + upDeg p`.
    rw [rowSpanBmat]
    refine Submodule.span_le.mpr ?_
    rintro v ⟨i, rfl⟩
    have hrow : (fun j : Fin (k + upDeg p + 1) => Bmat p k i j) =
        cvec R (k + upDeg p) ((skewLaurentT : SkewL R) ^ (i : ℕ) * p) := by
      funext j
      simp only [cvec, Bmat]
      rw [coeffElt_t_pow_mul_aux (R := R)]
    show (fun j : Fin (k + upDeg p + 1) => Bmat p k i j) ∈ degPart R (genIdeal p) (k + upDeg p)
    rw [hrow]
    refine Submodule.subset_span ⟨(skewLaurentT : SkewL R) ^ (i : ℕ) * p,
      ⟨(skewLaurentT : SkewL R) ^ (i : ℕ), rfl⟩, ?_, rfl⟩
    intro l hl
    rw [coeffElt_t_pow_mul_aux (R := R)]
    rw [hp (l - ((i : ℕ) : ℤ)) (by have hi : (0:ℤ) ≤ ((i:ℕ):ℤ) := Int.natCast_nonneg _; omega),
      smul_zero]
  · -- A vector in the row kernel gives a polynomial `toPoly k x` with `toPoly k x * p = 0`.
    intro x hx
    rw [kerBmat, LinearMap.mem_ker, Matrix.vecMulLinear_apply] at hx
    have hcol : ∀ j : Fin (k + upDeg p + 1), ∑ i : Fin (k+1), x i * Bmat p k i j = 0 := by
      intro j
      have h := congrFun hx j
      rw [Matrix.vecMul_apply, Matrix.col_apply', dotProduct] at h
      exact h
    have hgcoef : ∀ w : ℤ, coeffElt (toPoly k x * p) w = 0 := by
      intro w
      rw [coeffElt_toPoly_mul_aux (R := R)]
      by_cases hw : w < 0
      · -- all products `t^i * p` have no coefficients in negative degrees
        refine Finset.sum_eq_zero (fun i _ => ?_)
        have hi : (0:ℤ) ≤ ((i:ℕ):ℤ) := Int.natCast_nonneg _
        rw [hp _ (by omega), smul_zero, mul_zero]
      · have hw0 : (0:ℤ) ≤ w := le_of_not_gt hw
        by_cases hw2 : w ≤ ((k + upDeg p : ℕ) : ℤ)
        · -- in degrees `0..k+upDeg p` the coefficients are those of the row relation `x ᵥ* Bmat`
          have h1 : w.toNat ≤ k + upDeg p := Int.toNat_le.mpr hw2
          have hval : ((w.toNat : ℕ) : ℤ) = w := Int.toNat_of_nonneg hw0
          have hc := hcol ⟨w.toNat, by omega⟩
          simpa [Bmat, hval] using hc
        · -- beyond degree `k + upDeg p` all coefficients of `p` involved vanish
          refine Finset.sum_eq_zero (fun i _ => ?_)
          have hi : ((i:ℕ):ℤ) ≤ (k:ℤ) := by have := i.isLt; omega
          have hu : ((k + upDeg p : ℕ) : ℤ) < w := lt_of_not_ge hw2
          rw [coeffElt_eq_zero_of_gt_upDeg p (by push_cast at hu; omega), smul_zero, mul_zero]
    have hgp : toPoly k x * p = 0 := by
      apply SkewMonoidAlgebra.ext
      intro m
      have h := hgcoef (Multiplicative.toAdd m)
      simp only [SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
      rw [← h, coeffElt, ofAdd_toAdd]
    exact Submodule.subset_span ⟨toPoly k x, hgp,
      (fun l hl => coeffElt_toPoly_eq_zero_of_lt_aux k x hl), by rw [cvec_toPoly_aux]⟩

end Work.ORHughesFree.NaturalExtension
