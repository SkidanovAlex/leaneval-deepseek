/-
# `Work.FTS.PhiStar.Gegenbauer.gCSpanDefs` — the change-of-basis toolkit for `gC (2k+1)`

This module sets up the linear-algebraic machinery behind

`Work.FTS.PhiStar.Gegenbauer.gC_span_eq`:
the span of the odd Gegenbauer polynomials `C^{(3/2)}_{2k+1}` (`k ≤ N`) equals the span of the
odd monomials `x^{2k+1}` (`k ≤ N`).

Both families are triangular bases of the odd polynomials of degree `≤ 2N+1`: `C_{2k+1}` is an
odd polynomial whose leading term is a *nonzero* multiple of `x^{2k+1}`.  Everything is phrased in
terms of `Submodule.span ℝ` of function spaces `ℝ → ℝ`, so no polynomial machinery is needed.

Contents:

* `X k = x ↦ x^{2k}`, `Y k = x ↦ x^{2k+1}`;
* `evenSpan k = span {x^{2j} | j ≤ k}`, `oddSpan k = span {x^{2j+1} | j ≤ k}`;
* `mulX` — multiplication by the identity function, as an `ℝ`-linear endomorphism of `ℝ → ℝ`,
  with the span calculus `mulX_evenSpan_le` / `mulX_oddSpan_le`;
* `A k = gC (2k)`, `B k = gC (2k+1)` and the two recurrences `A_succ`, `B_succ` (from the
  three-term recurrence `gC_rec` of `Gegenbauer/gC_ode`);
* the coefficients `cfA cfB cfC cfD` (the ratios `(2n+5)/(n+2)`, `(n+3)/(n+2)` at `n = 2k`,
  `n = 2k+1`), `c k` (the leading coefficient of `C_{2k+1}`, so that `B k - c k • Y k` lies in
  `oddSpan (k-1)`) and `a k` (the leading coefficient of `C_{2k}`), with `a_succ`/`c_succ`;
* the two "tail" identities `A_tail`, `B_tail`, which are exactly the algebraic cores of the
  induction steps in `gC_span_eq`.
-/
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.PhiStar.Gegenbauer

set_option autoImplicit false

/-! ## The odd and even monomial families -/

/-- `X k` is the even monomial `x ↦ x ^ (2k)`. -/
def X (k : ℕ) : ℝ → ℝ := fun x => x ^ (2 * k)

/-- `Y k` is the odd monomial `x ↦ x ^ (2k+1)`. -/
def Y (k : ℕ) : ℝ → ℝ := fun x => x ^ (2 * k + 1)

/-- The span of the even monomials `x ^ (2j)`, `j ≤ k`. -/
def evenSpan (k : ℕ) : Submodule ℝ (ℝ → ℝ) := Submodule.span ℝ (X '' Set.Iic k)

/-- The span of the odd monomials `x ^ (2j+1)`, `j ≤ k`. -/
def oddSpan (k : ℕ) : Submodule ℝ (ℝ → ℝ) := Submodule.span ℝ (Y '' Set.Iic k)

/-! ## Multiplication by the identity function -/

/-- Multiplication of a function by the identity function, as an `ℝ`-linear map. -/
def mulX : (ℝ → ℝ) →ₗ[ℝ] (ℝ → ℝ) where
  toFun f := fun x => x * f x
  map_add' f g := by funext x; simp [Pi.add_apply, mul_add]
  map_smul' c f := by funext x; simp [Pi.smul_apply, smul_eq_mul, mul_left_comm]

lemma mulX_apply (f : ℝ → ℝ) (x : ℝ) : mulX f x = x * f x := rfl

/-- `mulX` maps the `k`-th even monomial to the `k`-th odd monomial. -/
lemma mulX_X (k : ℕ) : mulX (X k) = Y k := by
  funext x
  rw [mulX_apply, X, Y, pow_succ']

/-- `mulX` maps the `k`-th odd monomial to the `(k+1)`-st even monomial. -/
lemma mulX_Y (k : ℕ) : mulX (Y k) = X (k + 1) := by
  funext x
  rw [mulX_apply, X, Y, ← pow_succ' x (2 * k + 1),
    show 2 * k + 1 + 1 = 2 * (k + 1) by omega]

/-- `mulX` maps `evenSpan k` into `oddSpan k`. -/
lemma mulX_evenSpan_le (k : ℕ) : Submodule.map mulX (evenSpan k) ≤ oddSpan k := by
  rw [evenSpan, Submodule.map_span, Submodule.span_le]
  rintro g ⟨f, ⟨j, hj, rfl⟩, rfl⟩
  rw [mulX_X]
  exact Submodule.subset_span ⟨j, hj, rfl⟩

/-- `mulX` maps `oddSpan k` into `evenSpan (k+1)`. -/
lemma mulX_oddSpan_le (k : ℕ) : Submodule.map mulX (oddSpan k) ≤ evenSpan (k + 1) := by
  rw [oddSpan, Submodule.map_span, Submodule.span_le]
  rintro g ⟨f, ⟨j, hj, rfl⟩, rfl⟩
  rw [mulX_Y]
  exact Submodule.subset_span
    ⟨j + 1, Set.mem_Iic.mpr (Nat.succ_le_succ (Set.mem_Iic.mp hj)), rfl⟩

lemma mulX_mem_of_mem_evenSpan {k : ℕ} {f : ℝ → ℝ} (hf : f ∈ evenSpan k) :
    mulX f ∈ oddSpan k := mulX_evenSpan_le k ⟨f, hf, rfl⟩

lemma mulX_mem_of_mem_oddSpan {k : ℕ} {f : ℝ → ℝ} (hf : f ∈ oddSpan k) :
    mulX f ∈ evenSpan (k + 1) := mulX_oddSpan_le k ⟨f, hf, rfl⟩

lemma mulX_mulX_mem_of_mem_oddSpan {k : ℕ} {f : ℝ → ℝ} (hf : f ∈ oddSpan k) :
    mulX (mulX f) ∈ oddSpan (k + 1) :=
  mulX_mem_of_mem_evenSpan (mulX_mem_of_mem_oddSpan hf)

/-! ## Monotonicity, generators, and the successor decomposition -/

lemma evenSpan_mono {k m : ℕ} (h : k ≤ m) : evenSpan k ≤ evenSpan m := by
  rw [evenSpan, evenSpan, Submodule.span_le]
  rintro g ⟨j, hj, rfl⟩
  exact Submodule.subset_span ⟨j, le_trans hj h, rfl⟩

lemma oddSpan_mono {k m : ℕ} (h : k ≤ m) : oddSpan k ≤ oddSpan m := by
  rw [oddSpan, oddSpan, Submodule.span_le]
  rintro g ⟨j, hj, rfl⟩
  exact Submodule.subset_span ⟨j, le_trans hj h, rfl⟩

lemma X_mem (k : ℕ) : X k ∈ evenSpan k :=
  Submodule.subset_span ⟨k, Set.mem_Iic.mpr le_rfl, rfl⟩

lemma Y_mem (k : ℕ) : Y k ∈ oddSpan k :=
  Submodule.subset_span ⟨k, Set.mem_Iic.mpr le_rfl, rfl⟩

lemma Iic_succ (k : ℕ) : Set.Iic (k + 1) = insert (k + 1) (Set.Iic k) := by
  ext j; simp only [Set.mem_Iic, Set.mem_insert_iff]; omega

lemma oddSpan_succ (k : ℕ) : oddSpan (k + 1) = ℝ ∙ Y (k + 1) ⊔ oddSpan k := by
  unfold oddSpan
  rw [Iic_succ, Set.image_insert_eq, Submodule.span_insert]

/-! ## The even/odd indexed Gegenbauer polynomials and their recurrences -/

/-- `A k = gC (2k)`, the even-indexed Gegenbauer polynomial. -/
def A (k : ℕ) : ℝ → ℝ := fun x => gC (2 * k) x

/-- `B k = gC (2k+1)`, the odd-indexed Gegenbauer polynomial. -/
def B (k : ℕ) : ℝ → ℝ := fun x => gC (2 * k + 1) x

/-- The coefficient `(2n+5)/(n+2)` of the recurrence at `n = 2k`. -/
def cfA (k : ℕ) : ℝ := (2 * ((2 * k : ℕ) : ℝ) + 5) / (((2 * k : ℕ) : ℝ) + 2)

/-- The coefficient `(n+3)/(n+2)` of the recurrence at `n = 2k`. -/
def cfB (k : ℕ) : ℝ := (((2 * k : ℕ) : ℝ) + 3) / (((2 * k : ℕ) : ℝ) + 2)

/-- The coefficient `(2n+5)/(n+2)` of the recurrence at `n = 2k+1`. -/
def cfC (k : ℕ) : ℝ := (2 * ((2 * k + 1 : ℕ) : ℝ) + 5) / (((2 * k + 1 : ℕ) : ℝ) + 2)

/-- The coefficient `(n+3)/(n+2)` of the recurrence at `n = 2k+1`. -/
def cfD (k : ℕ) : ℝ := (((2 * k + 1 : ℕ) : ℝ) + 3) / (((2 * k + 1 : ℕ) : ℝ) + 2)

lemma cfA_pos (k : ℕ) : 0 < cfA k := by rw [cfA]; positivity
lemma cfB_pos (k : ℕ) : 0 < cfB k := by rw [cfB]; positivity
lemma cfC_pos (k : ℕ) : 0 < cfC k := by rw [cfC]; positivity
lemma cfD_pos (k : ℕ) : 0 < cfD k := by rw [cfD]; positivity

lemma cfA_ne_zero (k : ℕ) : cfA k ≠ 0 := ne_of_gt (cfA_pos k)
lemma cfB_ne_zero (k : ℕ) : cfB k ≠ 0 := ne_of_gt (cfB_pos k)
lemma cfC_ne_zero (k : ℕ) : cfC k ≠ 0 := ne_of_gt (cfC_pos k)
lemma cfD_ne_zero (k : ℕ) : cfD k ≠ 0 := ne_of_gt (cfD_pos k)

/-- The recurrence for the even-indexed family, pointwise. -/
lemma A_succ_pt (k : ℕ) (x : ℝ) : A (k + 1) x = cfA k * (x * B k x) - cfB k * A k x := by
  have hne : (((2 * k : ℕ) : ℝ) + 2) ≠ 0 := by positivity
  have hx : gC (2 * k + 2) x
      = ((2 * ((2 * k : ℕ) : ℝ) + 5) * x * gC (2 * k + 1) x
          - (((2 * k : ℕ) : ℝ) + 3) * gC (2 * k) x) / (((2 * k : ℕ) : ℝ) + 2) :=
    (eq_div_iff hne).mpr (by rw [mul_comm]; exact gC_rec (2 * k) x)
  show gC (2 * k + 2) x = cfA k * (x * gC (2 * k + 1) x) - cfB k * gC (2 * k) x
  rw [hx, cfA, cfB, div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_div]
  congr 1
  ring

/-- The recurrence for the odd-indexed family, pointwise. -/
lemma B_succ_pt (k : ℕ) (x : ℝ) :
    B (k + 1) x = cfC k * (x * A (k + 1) x) - cfD k * B k x := by
  have hne : (((2 * k + 1 : ℕ) : ℝ) + 2) ≠ 0 := by positivity
  have hx : gC ((2 * k + 1) + 2) x
      = ((2 * ((2 * k + 1 : ℕ) : ℝ) + 5) * x * gC ((2 * k + 1) + 1) x
          - (((2 * k + 1 : ℕ) : ℝ) + 3) * gC (2 * k + 1) x) / (((2 * k + 1 : ℕ) : ℝ) + 2) :=
    (eq_div_iff hne).mpr (by rw [mul_comm]; exact gC_rec (2 * k + 1) x)
  show gC ((2 * k + 1) + 2) x
      = cfC k * (x * gC (2 * (k + 1)) x) - cfD k * gC (2 * k + 1) x
  rw [hx, cfC, cfD, div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_div]
  congr 1
  ring

/-- The recurrence for the even-indexed family. -/
lemma A_succ (k : ℕ) : A (k + 1) = cfA k • mulX (B k) - cfB k • A k := by
  funext x
  rw [A_succ_pt k x]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulX_apply]

/-- The recurrence for the odd-indexed family. -/
lemma B_succ (k : ℕ) : B (k + 1) = cfC k • mulX (A (k + 1)) - cfD k • B k := by
  funext x
  rw [B_succ_pt k x]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulX_apply]

/-! ## The leading coefficients `a` and `c` -/

/-- `c k` is the coefficient of `x ^ (2k+1)` in `gC (2k+1)`; it is defined so that
`B k - c k • Y k ∈ oddSpan (k-1)`. -/
def c : ℕ → ℝ := fun k => Nat.rec 3 (fun j cj => cfC j * (cfA j * cj)) k

/-- `a k` is the coefficient of `x ^ (2k)` in `gC (2k)`; it is defined so that
`A k - a k • X k ∈ evenSpan (k-1)`. -/
def a : ℕ → ℝ := fun k => Nat.rec 1 (fun j _ => cfA j * c j) k

lemma c_zero : c 0 = 3 := rfl

lemma c_succ (k : ℕ) : c (k + 1) = cfC k * (cfA k * c k) := rfl

lemma a_zero : a 0 = 1 := rfl

lemma a_succ (k : ℕ) : a (k + 1) = cfA k * c k := rfl

lemma c_pos : ∀ k : ℕ, 0 < c k := by
  intro k
  induction k with
  | zero => rw [c_zero]; norm_num
  | succ k ih => rw [c_succ]; exact mul_pos (cfC_pos k) (mul_pos (cfA_pos k) ih)

lemma c_ne_zero (k : ℕ) : c k ≠ 0 := ne_of_gt (c_pos k)

/-! ## The two tail identities -/

/-- The algebraic core of the first induction step: the tail of `A (k+1)` (its difference from
its leading term) is the `mulX`-image of the tail of `B k`. -/
lemma A_tail (k : ℕ) :
    A (k + 1) - a (k + 1) • X (k + 1)
      = cfA k • mulX (B k - c k • Y k) - cfB k • A k := by
  funext x
  have hXY : x * Y k x = X (k + 1) x := by
    rw [← mulX_apply (Y k) x]; exact congrFun (mulX_Y k) x
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulX_apply]
  rw [A_succ_pt k x, a_succ k, ← hXY]
  ring

/-- The algebraic core of the second induction step: the tail of `B (k+1)` is the `mulX`-image
of the tail of `A (k+1)`. -/
lemma B_tail (k : ℕ) :
    B (k + 1) - c (k + 1) • Y (k + 1)
      = cfC k • mulX (A (k + 1) - a (k + 1) • X (k + 1)) - cfD k • B k := by
  funext x
  have hXY : x * X (k + 1) x = Y (k + 1) x := by
    rw [← mulX_apply (X (k + 1)) x]; exact congrFun (mulX_X (k + 1)) x
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulX_apply]
  rw [B_succ_pt k x, c_succ k, a_succ k, ← hXY]
  ring

end Work.FTS.PhiStar.Gegenbauer
