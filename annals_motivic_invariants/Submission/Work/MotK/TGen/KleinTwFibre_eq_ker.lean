import Mathlib
import Submission.Work.MotK.TwCensus.STClass
import Submission.Work.MotK.CensusFibre.kleinFibre_eq_ker
import Submission.Work.MotK.KleinTwData
import Submission.Work.MotK.TGen.TwBridge
import Submission.Work.MotK.CensusFibre.det_submatrix_kleinMat_eq_sq
import Submission.Work.TwistModel.adjugate_eq_skewPfaffian5
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The T-twisted fibre lemma: the kernel of `kleinTwM` is the line spanned by `kleinTwP`

`Work.MotK.TwCensus.kleinTwM a b h y` is the matrix of the linear system `y ↦ M(y)·c'` whose
kernel over `c'` is the fibre of the *twisted* quadro map `kleinTwP a b h y` over `[c']`
(`Submission/Work/MotK/TwCensus/STClass.lean`, node K5 of the census of the T-twisted
Crauder–Katz link).  This file proves the twisted transport of the *proved* split statement
`Work.MotK.CensusFibre.kleinFibre_eq_ker`:

  `kleinTwM a b h y *ᵥ c' = 0  ↔  kleinTwP a b h y ∝ c'`

for `kleinTwP a b h y ≠ 0` and `c' ≠ 0`.

The two ingredients are the twisted analogues of the split identities:

* `kleinTwM_mulVec_kleinTwP` — `kleinTwM · kleinTwP = 0`;
* `det_submatrix_kleinTwM_eq` — the determinant of the principal `4 × 4` minor of `kleinTwM`
  deleting `k` is `h^{[k≥1]} · (kleinTwP k)²` (note the *weight* `h` for `k ≠ 0`, which is exactly
  what makes the twisted transport work; the naive unweighted and `h^{-⌊(i+j)/5⌋}`-weighted forms
  are false).

Both are polynomial identities with integer coefficients, proved by expanding `kleinTwM` into its
explicit `5 × 5` matrix (`kleinTwM_eq`) and using `ring`; the rest of the argument is the rank
argument of the split case verbatim, so the only field-theoretic input used is `h ≠ 0`.

The explicit matrix is obtained from the weights `twW i j ∈ {0,1}` (which are `1` exactly for
`1 ≤ j` and `i + j ≤ 4`, indices read in `{0,…,4}`) applied to the rows of `kleinM`:

```
kleinTwM a b h y = !![0,          h*a*y1,   h*b*y2,  -h*b*y3, -h*a*y4;
                      -a*y1,      0,        h*a*y3,   h*b*y4, -b*y0;
                      -b*y2,      -h*a*y3,  0,        a*y0,   b*y1;
                       b*y3,      -h*b*y4, -a*y0,    0,      a*y2;
                       a*y4,       b*y0,   -b*y1,  -a*y2,    0]
```
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.MotK.TGen

open Matrix

variable {K : Type} [Field K]

/-- **The T-twisted ruling matrix in explicit coordinates.**  Since `twW i j = 1` exactly for
`1 ≤ j` and `i + j ≤ 4` (indices read in `{0,…,4}`), the matrix `kleinTwM a b h y` is the matrix
`kleinM a b y` with the weight `h` inserted in its strict upper triangle (column `0` excluded);
here it is exhibited entrywise. -/
theorem kleinTwM_eq (a b h : K) (y : Fin 5 → K) :
    Work.MotK.TwCensus.kleinTwM a b h y =
      !![0, h * (a * y 1), h * (b * y 2), h * (-b * y 3), h * (-a * y 4);
         -a * y 1, 0, h * (a * y 3), h * (b * y 4), -b * y 0;
         -b * y 2, -h * a * y 3, 0, a * y 0, b * y 1;
         b * y 3, -h * b * y 4, -a * y 0, 0, a * y 2;
         a * y 4, b * y 0, -b * y 1, -a * y 2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Work.MotK.TwCensus.kleinTwM, Work.MotK.TwCensus.twW, Work.MotK.kleinM,
      Work.MotK.kleinM_zero, Work.MotK.kleinM_one, Work.MotK.kleinM_two, Work.MotK.kleinM_three,
      Work.MotK.kleinM_four, Work.MotK.kleinM0, Work.MotK.kleinM1, Work.MotK.kleinM2,
      Work.MotK.kleinM3, Work.MotK.kleinM4] <;> ring

/-- **`kleinTwM · kleinTwP = 0` in coordinates**: the twisted Pfaffian vector lies in the kernel of
the twisted ruling matrix.  This is the twisted transport of `kleinM_mul_kleinP`. -/
theorem kleinTwM_mul_kleinTwP (a b h : K) (y : Fin 5 → K) (i : Fin 5) :
    ∑ j, Work.MotK.TwCensus.kleinTwM a b h y i j * Work.MotK.kleinTwP a b h y j = 0 := by
  rw [kleinTwM_eq]
  fin_cases i <;>
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five, Pi.zero_apply]
    simp [Work.MotK.kleinTwP, Work.MotK.kleinTwP0, Work.MotK.kleinTwP1, Work.MotK.kleinTwP2,
      Work.MotK.kleinTwP3, Work.MotK.kleinTwP4]
    first | refl_ring1 | ring

/-- **`kleinTwM · kleinTwP = 0`**, in `Matrix.mulVec` form. -/
theorem kleinTwM_mulVec_kleinTwP (a b h : K) (y : Fin 5 → K) :
    Matrix.mulVec (Work.MotK.TwCensus.kleinTwM a b h y) (Work.MotK.kleinTwP a b h y) = 0 :=
  funext (kleinTwM_mul_kleinTwP a b h y)

/-- **The determinant of the principal `4 × 4` minor of `kleinTwM` is the weighted square of the
corresponding twisted Pfaffian.**  Deleting row and column `k`, the determinant is `(kleinTwP k)²`
for `k = 0` and `h · (kleinTwP k)²` for `k ≠ 0`.  It is a polynomial identity of degree `8`,
proved by expanding the minor with `Work.TwistModel.det_fin_four_expand`. -/
theorem det_submatrix_kleinTwM_eq (a b h : K) (y : Fin 5 → K) (k : Fin 5) :
    ((Work.MotK.TwCensus.kleinTwM a b h y).submatrix k.succAbove k.succAbove).det
      = (if k = 0 then 1 else h) * (Work.MotK.kleinTwP a b h y k) ^ 2 := by
  rw [kleinTwM_eq]
  fin_cases k <;>
  · rw [Work.TwistModel.det_fin_four_expand]
    simp [Matrix.submatrix_apply, Fin.succAbove, Work.MotK.kleinTwP, Work.MotK.kleinTwP0,
      Work.MotK.kleinTwP1, Work.MotK.kleinTwP2, Work.MotK.kleinTwP3, Work.MotK.kleinTwP4]
    first | refl_ring1 | ring

/-- **The fibres of the twisted Pfaffian (quadro) map are the linear spaces `{c' : M·c' = 0}`.**

For `c' ≠ 0` and `y` with `kleinTwP a b h y ≠ 0` (i.e. `y` not on the twisted Klein curve), the
following are equivalent:

* `kleinTwP a b h y` is proportional to `c'`;
* `c'` lies in the kernel of the linear map `v ↦ kleinTwM a b h y *ᵥ v`.

The proof is the rank argument of `Work.MotK.CensusFibre.kleinFibre_eq_ker`: `kleinTwP ≠ 0` means
that some coordinate `kleinTwP k` is nonzero, hence — by `det_submatrix_kleinTwM_eq` — that the
`k`-th principal `4 × 4` minor of `kleinTwM` is invertible (`h ≠ 0`), so `rank kleinTwM ≥ 4`; and
`kleinTwM · kleinTwP = 0` with `kleinTwP ≠ 0` rules out `rank = 5`.  Hence `rank kleinTwM = 4` and
its kernel is one-dimensional, containing both `kleinTwP ≠ 0` and `c' ≠ 0`, so the two are
proportional. -/
theorem KleinTwFibre_eq_ker {K : Type} [Field K] (a b h : K) (hh : h ≠ 0) (y c' : Fin 5 → K)
    (hy : Work.MotK.kleinTwP a b h y ≠ 0) (hc' : c' ≠ 0) :
    Matrix.mulVec (Work.MotK.TwCensus.kleinTwM a b h y) c' = 0 ↔
      ∃ l : K, l ≠ 0 ∧ ∀ k : Fin 5, Work.MotK.kleinTwP a b h y k = l * c' k := by
  constructor
  · -- **Necessity of the linear condition.**  `kleinTwP ≠ 0` gives a coordinate `k` with
    -- `kleinTwP k ≠ 0`; the corresponding principal minor of `kleinTwM` has determinant
    -- `h^{[k≥1]} (kleinTwP k)² ≠ 0`, so the kernel of `kleinTwM` is one-dimensional.  Both
    -- `kleinTwP` and `c'` lie in it, and `c' ≠ 0`, so they are proportional.
    intro hM
    have hkex : ∃ k, Work.MotK.kleinTwP a b h y k ≠ 0 := by
      by_contra h'
      simp only [not_exists, not_not] at h'
      exact hy (funext h')
    obtain ⟨k, hk⟩ := hkex
    have hdet : ((Work.MotK.TwCensus.kleinTwM a b h y).submatrix k.succAbove
        k.succAbove).det ≠ 0 := by
      rw [det_submatrix_kleinTwM_eq]
      have hcoeff : (if k = 0 then (1 : K) else h) ≠ 0 := by
        by_cases hk0 : k = 0
        · subst hk0; simp
        · simp [hk0, hh]
      exact mul_ne_zero hcoeff (pow_ne_zero 2 hk)
    have hw : Matrix.mulVec (Work.MotK.TwCensus.kleinTwM a b h y)
        (Work.MotK.kleinTwP a b h y) = 0 := kleinTwM_mulVec_kleinTwP a b h y
    have hprop : Work.MotK.kleinTwP a b h y k • c' = c' k • (Work.MotK.kleinTwP a b h y) :=
      Work.MotK.CensusFibre.smul_eq_smul_of_mulVec_eq_zero hw hM hdet
    have hck : c' k ≠ 0 := by
      intro h0
      have h1 : Work.MotK.kleinTwP a b h y k • c' = 0 := by rw [hprop, h0, zero_smul]
      exact hc' ((smul_eq_zero.mp h1).resolve_left hk)
    refine ⟨(c' k)⁻¹ * Work.MotK.kleinTwP a b h y k, mul_ne_zero (inv_ne_zero hck) hk,
      fun i => ?_⟩
    have hp : Work.MotK.kleinTwP a b h y =
        ((c' k)⁻¹ * Work.MotK.kleinTwP a b h y k) • c' := by
      have h2 := congrArg (fun w : Fin 5 → K => (c' k)⁻¹ • w) hprop.symm
      simpa [smul_smul, inv_smul_smul₀ hck] using h2
    simpa using congrFun hp i
  · -- **Sufficiency.**  If `kleinTwP = l · c'` with `l ≠ 0`, then
    -- `kleinTwM·c' = l⁻¹ · kleinTwM·kleinTwP = 0`.
    rintro ⟨l, hl, hl'⟩
    funext i
    show ∑ j, Work.MotK.TwCensus.kleinTwM a b h y i j * c' j = 0
    have h1 : (∑ j, Work.MotK.TwCensus.kleinTwM a b h y i j * (l * c' j)) = 0 := by
      have hgen : (∑ j, Work.MotK.TwCensus.kleinTwM a b h y i j * (l * c' j)) =
          ∑ j, Work.MotK.TwCensus.kleinTwM a b h y i j * Work.MotK.kleinTwP a b h y j :=
        Finset.sum_congr rfl fun j _ => by rw [hl' j]
      rw [hgen, kleinTwM_mul_kleinTwP a b h y i]
    have h2 : l * (∑ j, Work.MotK.TwCensus.kleinTwM a b h y i j * c' j) = 0 := by
      rw [Finset.mul_sum]
      exact (Finset.sum_congr rfl fun j _ => by ring).trans h1
    exact (mul_eq_zero.mp h2).resolve_left hl

end Work.MotK.TGen
