import Mathlib
import Submission.Work.RPV.Defs

/-!
# Two rectangles with proportional side lengths are similar (`Work.RPV.similar_R_of_dims`)

The rectangle `R z w θ` (see `ChallengeDeps`) has the four vertices
`z·c, (w.re + z.im·I)·c, w·c, (z.re + w.im·I)·c`, where `c = θ.toCircle` is a unit complex
number.  Writing `pt x y = x + y·I` for the point with coordinates `(x, y)`, the four vertices are
`c` times the four points

`pt z.re z.im, pt w.re z.im, pt w.re w.im, pt z.re w.im`,

i.e. each vertex uses one of the two real coordinates `z.re`, `w.re` for its real part and one of
`z.im`, `w.im` for its imaginary part.  Consequently every pairwise distance of the rectangle is
`√(δ₁² + δ₂²)` where `δ₁ ∈ {0, ±(z.re - w.re)}` and `δ₂ ∈ {0, ±(z.im - w.im)}`.  The hypotheses
`|z.re - w.re| = κ·|z'.re - w'.re|` and `|z.im - w.im| = κ·|z'.im - w'.im|` therefore scale *all*
pairwise distances by `κ`, which is exactly `Similar` (proportional `edist`), and multiplication by
the unit complex numbers `θ.toCircle`, `θ'.toCircle` is an isometry, so the angles drop out.
-/

open RectangularPegProblem Complex

namespace Work.RPV

namespace RectSim

/-- The complex number with coordinates `(x, y)`. -/
def pt (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * I

/-- Pick `a` on `0` and `b` on `1`. -/
def pick (k : Fin 2) (a b : ℝ) : ℝ := if k = 0 then a else b

/-- Which of `z.re`, `w.re` is the real part of the `i`-th vertex. -/
def bChoice : Fin 4 → Fin 2 := ![0, 1, 1, 0]

/-- Which of `z.im`, `w.im` is the imaginary part of the `i`-th vertex. -/
def cChoice : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- The four vertices of the (unrotated) rectangle with real coordinate pair `(X, Y)` for `z` and
`(X', Y')` for `w`. -/
def rect (X Y X' Y' : ℝ) : Fin 4 → ℂ :=
  fun i => pt (pick (bChoice i) X X') (pick (cChoice i) Y Y')

/-- The norm of a difference of two points given by coordinates. -/
lemma norm_pt_sub (a b c d : ℝ) : ‖pt a b - pt c d‖ = Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := by
  have hn : ‖pt a b - pt c d‖ = Real.sqrt (Complex.normSq (pt a b - pt c d)) := by
    rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have h : Complex.normSq (pt a b - pt c d) = (a - c) ^ 2 + (b - d) ^ 2 := by
    simp [Complex.normSq_apply, pt]; ring
  rw [hn, h]

/-- `√(δ₁² + δ₂²)` scales by `κ` when `δ₁`, `δ₂` do. -/
lemma sqrt_scale (κ : ℝ) (hκ : 0 < κ) (δ₁ δ₂ δ₁' δ₂' : ℝ)
    (h₁ : |δ₁| = κ * |δ₁'|) (h₂ : |δ₂| = κ * |δ₂'|) :
    Real.sqrt (δ₁ ^ 2 + δ₂ ^ 2) = κ * Real.sqrt (δ₁' ^ 2 + δ₂' ^ 2) := by
  have e₁ : δ₁ ^ 2 = κ ^ 2 * δ₁' ^ 2 := by rw [← sq_abs δ₁, h₁, mul_pow, sq_abs δ₁']
  have e₂ : δ₂ ^ 2 = κ ^ 2 * δ₂' ^ 2 := by rw [← sq_abs δ₂, h₂, mul_pow, sq_abs δ₂']
  have e : δ₁ ^ 2 + δ₂ ^ 2 = κ ^ 2 * (δ₁' ^ 2 + δ₂' ^ 2) := by rw [e₁, e₂]; ring
  rw [e, Real.sqrt_mul (sq_nonneg κ), Real.sqrt_sq_eq_abs, abs_of_pos hκ]

/-- `pick`ing two of `a, b` scales by `κ`, in every combination. -/
lemma abs_pick_scale (a b a' b' κ : ℝ) (h : |a - b| = κ * |a' - b'|) (r s : Fin 2) :
    |pick r a b - pick s a b| = κ * |pick r a' b' - pick s a' b'| := by
  fin_cases r <;> fin_cases s <;> simp [pick, abs_sub_comm, h]

/-- All pairwise distances of `rect X Y X' Y'` scale by `κ`. -/
lemma norm_rect_sub (κ : ℝ) (hκ : 0 < κ) (X Y X' Y' X₂ Y₂ X₂' Y₂' : ℝ)
    (hx : |X - X'| = κ * |X₂ - X₂'|) (hy : |Y - Y'| = κ * |Y₂ - Y₂'|) (i j : Fin 4) :
    ‖rect X Y X' Y' i - rect X Y X' Y' j‖ =
      κ * ‖rect X₂ Y₂ X₂' Y₂' i - rect X₂ Y₂ X₂' Y₂' j‖ := by
  unfold rect
  rw [norm_pt_sub, norm_pt_sub]
  exact sqrt_scale κ hκ _ _ _ _ (abs_pick_scale _ _ _ _ κ hx _ _) (abs_pick_scale _ _ _ _ κ hy _ _)

/-- Multiplication by a unit complex number preserves distances. -/
lemma norm_mul_unit (c : ℂ) (hc : ‖c‖ = 1) (x y : ℂ) : ‖x * c - y * c‖ = ‖x - y‖ := by
  have h : x * c - y * c = (x - y) * c := by ring
  rw [h, norm_mul, hc, mul_one]

/-- `R z w θ` is the unrotated rectangle attached to `(z, w)`, rotated by `θ.toCircle`. -/
lemma R_eq_rect (z w : ℂ) (θ : Real.Angle) :
    RectangularPegProblem.R z w θ =
      fun i => rect z.re z.im w.re w.im i * (θ.toCircle : ℂ) := by
  ext i
  fin_cases i <;>
    simp [rect, RectangularPegProblem.R, pt, pick, bChoice, cChoice, Complex.re_add_im]

end RectSim

open RectSim

theorem similar_R_of_dims (z w z' w' : ℂ) (θ θ' : Real.Angle) (κ : ℝ) (hκ : 0 < κ)
    (hx : |z.re - w.re| = κ * |z'.re - w'.re|)
    (hy : |z.im - w.im| = κ * |z'.im - w'.im|) :
    Similar (RectangularPegProblem.R z w θ) (RectangularPegProblem.R z' w' θ') := by
  rw [R_eq_rect z w θ, R_eq_rect z' w' θ']
  refine Similar.of_exists_edist_eq ⟨Real.toNNReal κ, (Real.toNNReal_pos.mpr hκ).ne', ?_⟩
  intro i j
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
  rw [norm_mul_unit _ (Circle.norm_coe _), norm_mul_unit _ (Circle.norm_coe _)]
  rw [show (Real.toNNReal κ : ENNReal) = ENNReal.ofReal κ from by
    rw [← ENNReal.ofReal_coe_nnreal]; congr 1; simp [Real.coe_toNNReal', hκ.le]]
  rw [← ENNReal.ofReal_mul hκ.le]
  rw [norm_rect_sub κ hκ z.re z.im w.re w.im z'.re z'.im w'.re w'.im hx hy i j]

end Work.RPV
