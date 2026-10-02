import Submission.Work.ThomBordism.Grassmann.Smooth.Chart.Frame

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The two orientations of a graph

For a graph datum `d : Amb k →L[ℝ] Amb m` there are two oriented points of `OG k m` over the plane
`graph(d)`.  This file constructs both of them explicitly, as `posPoint S d` and `negPoint S d`:

* `posPoint S d` is the point whose `S`-determinant is *positive*; it is obtained from the graph
  point by the sign gauge `signMat S d` (the diagonal matrix whose first entry is the sign of the
  determinant of the Gram–Schmidt frame);
* `negPoint S d` is obtained from `posPoint` by the matrix `flipMat k` of determinant `-1` (for
  `0 < k`).

Both have `chartData S · = d`, and their `frameSign` is `1` respectively `-1`.
-/

namespace Work.ThomBordism.Grassmann.Smooth

open scoped Topology
open Set

noncomputable section

variable {k m : ℕ}

/-! ## The span of a frame under the action -/

theorem span_soActFun_le (A : Matrix (Fin k) (Fin k) ℝ) (f : Fin k → Amb (k + m)) :
    Submodule.span ℝ (Set.range (soActFun A f)) ≤ Submodule.span ℝ (Set.range f) := by
  refine Submodule.span_le.mpr ?_
  rintro x ⟨i, rfl⟩
  rw [soActFun]
  exact Submodule.sum_mem _ fun l _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

theorem span_soActFun_eq {A : Matrix (Fin k) (Fin k) ℝ} (hA : A * A.transpose = 1)
    (f : Fin k → Amb (k + m)) :
    Submodule.span ℝ (Set.range (soActFun A f)) = Submodule.span ℝ (Set.range f) := by
  refine le_antisymm (span_soActFun_le A f) ?_
  have hcomp : soActFun A.transpose (soActFun A f) = f := by
    rw [soActFun_comp, hA, soActFun_one]
  calc Submodule.span ℝ (Set.range f)
      = Submodule.span ℝ (Set.range (soActFun A.transpose (soActFun A f))) := by rw [hcomp]
    _ ≤ Submodule.span ℝ (Set.range (soActFun A f)) :=
        span_soActFun_le A.transpose (soActFun A f)

/-! ## The sign gauge of a graph -/

/-- The sign gauge of a graph: the diagonal matrix whose first entry is the sign of
`det (frameMatrix S (graphFrame S d))` and whose other entries are `1`. -/
def signMat (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.diagonal fun i : Fin k =>
    if (i : ℕ) = 0 then (frameMatrix S (graphFrame S d)).det
      / |(frameMatrix S (graphFrame S d)).det| else 1

/-- The sign of a nonzero real number. -/
theorem signFun_mul_self {t : ℝ} (ht : t ≠ 0) : t / |t| * (t / |t|) = 1 := by
  rw [div_mul_div_comm, ← sq, ← sq, sq_abs]
  exact div_self (pow_ne_zero 2 ht)

/-- The sign of a nonzero real number times the number is its absolute value. -/
theorem mul_signFun {t : ℝ} (ht : t ≠ 0) : t * (t / |t|) = |t| := by
  have h1 : t * (t / |t|) = t ^ 2 / |t| := by ring
  rw [h1, ← sq_abs, sq, mul_div_assoc, div_self (abs_ne_zero.mpr ht), mul_one]

theorem signMat_transpose (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    (signMat S d).transpose = signMat S d := Matrix.diagonal_transpose _

theorem signMat_mul_self (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    signMat S d * signMat S d = 1 := by
  rw [signMat, Matrix.diagonal_mul_diagonal]
  refine (Matrix.diagonal_eq_diagonal_iff).mpr fun i => ?_
  by_cases h : (i : ℕ) = 0
  · rw [if_pos h]; exact signFun_mul_self (graphFrame_det_ne_zero S d)
  · rw [if_neg h]; norm_num

theorem signMat_transpose_mul_self (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    (signMat S d).transpose * signMat S d = 1 := by
  rw [signMat_transpose]; exact signMat_mul_self S d

theorem signMat_mul_transpose (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    signMat S d * (signMat S d).transpose = 1 := by
  rw [signMat_transpose]; exact signMat_mul_self S d

theorem signMat_det_ne_zero (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    (signMat S d).det ≠ 0 := by
  by_cases hk : k = 0
  · subst hk
    have h : signMat S d = 1 := Subsingleton.elim _ _
    rw [h, Matrix.det_one]; exact one_ne_zero
  · rw [signMat, Matrix.det_diagonal,
      Finset.prod_eq_single (⟨0, Nat.pos_of_ne_zero hk⟩ : Fin k)
        (fun b _ hb => by rw [if_neg (fun h => hb (Fin.ext h))])
        (fun hmem => absurd (Finset.mem_univ _) hmem), if_pos rfl]
    exact div_ne_zero (graphFrame_det_ne_zero S d) (abs_ne_zero.mpr (graphFrame_det_ne_zero S d))

/-- The determinant of the sign gauge, for `0 < k`. -/
theorem signMat_det_of_pos {k : ℕ} (hk : 0 < k) (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    (signMat S d).det = (frameMatrix S (graphFrame S d)).det
      / |(frameMatrix S (graphFrame S d)).det| := by
  rw [signMat, Matrix.det_diagonal,
    Finset.prod_eq_single (⟨0, hk⟩ : Fin k)
      (fun b _ hb => by rw [if_neg (fun h => hb (Fin.ext h))])
      (fun hmem => absurd (Finset.mem_univ _) hmem), if_pos rfl]

theorem flipMat_signMat_transpose_mul_self (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    (flipMat k * signMat S d).transpose * (flipMat k * signMat S d) = 1 := by
  rw [Matrix.transpose_mul, signMat_transpose, flipMat_transpose]
  calc (signMat S d * flipMat k) * (flipMat k * signMat S d)
      = signMat S d * (flipMat k * flipMat k) * signMat S d := by noncomm_ring
    _ = 1 := by rw [flipMat_mul_self, mul_one, signMat_mul_self]

theorem flipMat_signMat_mul_transpose (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    (flipMat k * signMat S d) * (flipMat k * signMat S d).transpose = 1 := by
  rw [Matrix.transpose_mul, signMat_transpose, flipMat_transpose]
  calc (flipMat k * signMat S d) * (signMat S d * flipMat k)
      = flipMat k * (signMat S d * signMat S d) * flipMat k := by noncomm_ring
    _ = 1 := by rw [signMat_mul_self, mul_one, flipMat_mul_self]

/-! ## The two points over a graph -/

/-- The Gram–Schmidt frame of a graph, corrected by the sign gauge, so that its `S`-matrix has
positive determinant. -/
def posFrame (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) : Fin k → Amb (k + m) :=
  soActFun (signMat S d) (graphFrame S d)

/-- The frame of the graph with `S`-determinant of the *opposite* sign. -/
def negFrame (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) : Fin k → Amb (k + m) :=
  soActFun (flipMat k * signMat S d) (graphFrame S d)

/-- **The positively oriented point over the graph of `d`** in the chart `S`. -/
def posPoint (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) : OG k m :=
  Quotient.mk'' ⟨posFrame S d,
    orthonormal_soActFun (signMat_transpose_mul_self S d) (orthonormal_graphFrame S d)⟩

/-- **The negatively oriented point over the graph of `d`** in the chart `S`. -/
def negPoint (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) : OG k m :=
  Quotient.mk'' ⟨negFrame S d,
    orthonormal_soActFun (flipMat_signMat_transpose_mul_self S d)
      (orthonormal_graphFrame S d)⟩

theorem posPoint_mk (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    posPoint S d = Quotient.mk'' ⟨posFrame S d,
      orthonormal_soActFun (signMat_transpose_mul_self S d) (orthonormal_graphFrame S d)⟩ := rfl

theorem negPoint_mk (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    negPoint S d = Quotient.mk'' ⟨negFrame S d,
      orthonormal_soActFun (flipMat_signMat_transpose_mul_self S d)
        (orthonormal_graphFrame S d)⟩ := rfl

theorem posFrame_mem_chartSet (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    (⟨posFrame S d,
      orthonormal_soActFun (signMat_transpose_mul_self S d) (orthonormal_graphFrame S d)⟩ :
        Stiefel k m) ∈ chartSet S := by
  show (frameMatrix S (posFrame S d)).det ≠ 0
  rw [posFrame, frameMatrix_soActFun, Matrix.det_mul]
  exact mul_ne_zero (graphFrame_det_ne_zero S d) (signMat_det_ne_zero S d)

theorem negFrame_det_ne_zero (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    (frameMatrix S (negFrame S d)).det ≠ 0 := by
  by_cases hk : k = 0
  · subst hk
    have h1 : negFrame S d = graphFrame S d := funext fun i => isEmptyElim i
    rw [h1]; exact graphFrame_det_ne_zero S d
  · rw [negFrame, frameMatrix_soActFun, Matrix.det_mul, Matrix.det_mul,
      flipMat_det_of_pos (Nat.pos_of_ne_zero hk)]
    exact mul_ne_zero (graphFrame_det_ne_zero S d)
      (mul_ne_zero (by norm_num) (signMat_det_ne_zero S d))

theorem negFrame_mem_chartSet (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    (⟨negFrame S d,
      orthonormal_soActFun (flipMat_signMat_transpose_mul_self S d)
        (orthonormal_graphFrame S d)⟩ : Stiefel k m) ∈ chartSet S :=
  negFrame_det_ne_zero S d

/-- The determinant of the `S`-matrix of the corrected frame is positive: it is the absolute value
of the determinant of the original frame matrix. -/
theorem frameMatrix_det_posFrame (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    (frameMatrix S (posFrame S d)).det = |(frameMatrix S (graphFrame S d)).det| := by
  rw [posFrame, frameMatrix_soActFun, Matrix.det_mul]
  by_cases hk : k = 0
  · subst hk
    have h1 : signMat S d = 1 := Subsingleton.elim _ _
    have h2 : frameMatrix S (graphFrame S d) = 1 := Subsingleton.elim _ _
    rw [h1, h2, Matrix.det_one]
    norm_num
  · rw [signMat_det_of_pos (Nat.pos_of_ne_zero hk)]
    exact mul_signFun (graphFrame_det_ne_zero S d)

/-- The determinant of the `S`-matrix of the negatively corrected frame (for `0 < k`). -/
theorem frameMatrix_det_negFrame {k m : ℕ} (hk : 0 < k) (S : ChartIdx k m)
    (d : Amb k →L[ℝ] Amb m) :
    (frameMatrix S (negFrame S d)).det = -|(frameMatrix S (graphFrame S d)).det| := by
  rw [negFrame, frameMatrix_soActFun, Matrix.det_mul, Matrix.det_mul,
    signMat_det_of_pos hk, flipMat_det_of_pos hk]
  have ht := graphFrame_det_ne_zero S d
  have h : (frameMatrix S (graphFrame S d)).det * (-1
      * ((frameMatrix S (graphFrame S d)).det / |(frameMatrix S (graphFrame S d)).det|))
      = -((frameMatrix S (graphFrame S d)).det
        * ((frameMatrix S (graphFrame S d)).det / |(frameMatrix S (graphFrame S d)).det|)) := by
    ring
  rw [h, mul_signFun ht]

/-! ## The chart data and the sign of the two points -/

theorem chartData_posPoint (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    chartData S (posPoint S d) = d := by
  rw [posPoint_mk,
    chartData_eq_of_span_eq (posFrame_mem_chartSet S d) (graphFrame_mem_chartSet S d)
      (span_soActFun_eq (signMat_mul_transpose S d) (graphFrame S d)),
    show (Quotient.mk'' (⟨graphFrame S d, orthonormal_graphFrame S d⟩ : Stiefel k m) : OG k m)
      = graphPoint S d from rfl,
    chartData_graphPoint]

theorem chartData_negPoint (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    chartData S (negPoint S d) = d := by
  rw [negPoint_mk,
    chartData_eq_of_span_eq (negFrame_mem_chartSet S d) (graphFrame_mem_chartSet S d)
      (span_soActFun_eq (flipMat_signMat_mul_transpose S d) (graphFrame S d)),
    show (Quotient.mk'' (⟨graphFrame S d, orthonormal_graphFrame S d⟩ : Stiefel k m) : OG k m)
      = graphPoint S d from rfl,
    chartData_graphPoint]

theorem frameSign_posPoint (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    frameSign S (posPoint S d) = 1 := by
  rw [posPoint_mk, frameSign_mk, frameSignFun, frameMatrix_det_posFrame, abs_abs]
  exact div_self (abs_ne_zero.mpr (graphFrame_det_ne_zero S d))

theorem frameSign_negPoint {k m : ℕ} (hk : 0 < k) (S : ChartIdx k m)
    (d : Amb k →L[ℝ] Amb m) : frameSign S (negPoint S d) = -1 := by
  rw [negPoint_mk, frameSign_mk, frameSignFun, frameMatrix_det_negFrame hk]
  rw [abs_neg, neg_div, abs_abs, div_self (abs_ne_zero.mpr (graphFrame_det_ne_zero S d))]

end

end Work.ThomBordism.Grassmann.Smooth
