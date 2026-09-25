import Mathlib
import Submission.Work.LT.relT_defs
import Submission.Work.LT.l2norm_triangle

/-!
# Elementary `ℓ²` analysis on a finite type

`l2sq h = ∑ x, Complex.normSq (h x)` is (the square of) the `ℓ²`-norm of a complex-valued
function `h` on a finite type `X`, and `l2norm h = √(l2sq h)`.  This file collects the
elementary facts about them used by the relative-property-(T) column lemma
(`Submission/Work/LT/sl3_relT_column.lean`).  Minkowski's inequality is proved separately in
`Submission/Work/LT/l2norm_triangle.lean` (by transporting to `EuclideanSpace ℂ X`); the
reverse triangle inequality below is derived from it the same way.
-/

namespace Work.LT

lemma l2sq_nonneg {X : Type*} [Fintype X] (h : X → ℂ) : 0 ≤ l2sq h := by
  unfold l2sq
  exact Finset.sum_nonneg fun x _ => Complex.normSq_nonneg (h x)

lemma l2sq_eq_zero_iff {X : Type*} [Fintype X] (h : X → ℂ) : l2sq h = 0 ↔ h = 0 := by
  unfold l2sq
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Complex.normSq_nonneg (h x))]
  constructor
  · intro hh
    funext x
    exact Complex.normSq_eq_zero.mp (hh x (Finset.mem_univ x))
  · rintro rfl x -
    simp

lemma l2sq_smul {X : Type*} [Fintype X] (c : ℂ) (h : X → ℂ) :
    l2sq (c • h) = Complex.normSq c * l2sq h := by
  unfold l2sq
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]
  rw [Finset.mul_sum]

lemma l2sq_neg {X : Type*} [Fintype X] (h : X → ℂ) : l2sq (-h) = l2sq h := by
  unfold l2sq
  simp only [Pi.neg_apply, Complex.normSq_neg]

lemma l2norm_neg {X : Type*} [Fintype X] (h : X → ℂ) : l2norm (-h) = l2norm h := by
  rw [l2norm, l2norm, l2sq_neg]

/-- Reverse triangle inequality for `l2norm`, obtained from `l2norm_eq_norm` and the reverse
triangle inequality for a norm. -/
lemma l2norm_sub_rev {X : Type*} [Fintype X] (a b : X → ℂ) :
    |l2norm a - l2norm b| ≤ l2norm (a - b) := by
  rw [l2norm_eq_norm a, l2norm_eq_norm b, l2norm_eq_norm (a - b), WithLp.toLp_sub]
  exact abs_norm_sub_norm_le _ _

/-- Elementary `ℓ²` analysis on a finite type: `l2sq h = ∑ x, Complex.normSq (h x)` is
nonnegative and vanishes only for `h = 0`, `l2norm h = √(l2sq h)` satisfies
`l2norm h ^ 2 = l2sq h`, is subadditive (Minkowski), and `l2norm` inherits the reverse triangle
inequality `|l2norm a − l2norm b| ≤ l2norm (a − b)`; also `l2sq` scales as `l2sq (c • h) =
Complex.normSq c * l2sq h`. -/
theorem relT_l2 :
    (∀ {X : Type*} [Fintype X] (h : X → ℂ), 0 ≤ l2sq h)
  ∧ (∀ {X : Type*} [Fintype X] (h : X → ℂ), 0 ≤ l2norm h)
  ∧ (∀ {X : Type*} [Fintype X] (h : X → ℂ), l2norm h ^ 2 = l2sq h)
  ∧ (∀ {X : Type*} [Fintype X] (h : X → ℂ), l2sq h = 0 ↔ h = 0)
  ∧ (∀ {X : Type*} [Fintype X] (c : ℂ) (h : X → ℂ), l2sq (c • h) = Complex.normSq c * l2sq h)
  ∧ (∀ {X : Type*} [Fintype X] (a b : X → ℂ), l2norm (a + b) ≤ l2norm a + l2norm b)
  ∧ (∀ {X : Type*} [Fintype X] (a b : X → ℂ), |l2norm a - l2norm b| ≤ l2norm (a - b)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X _ h
    exact l2sq_nonneg h
  · intro X _ h
    exact Real.sqrt_nonneg _
  · intro X _ h
    exact Real.sq_sqrt (l2sq_nonneg h)
  · intro X _ h
    exact l2sq_eq_zero_iff h
  · intro X _ c h
    exact l2sq_smul c h
  · intro X _ a b
    exact l2norm_triangle a b
  · intro X _ a b
    exact l2norm_sub_rev a b

end Work.LT
