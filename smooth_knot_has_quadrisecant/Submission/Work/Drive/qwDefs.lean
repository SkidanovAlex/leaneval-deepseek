import Mathlib
import Submission.Work.Drive.genericFullDefs
import Submission.Work.Drive.genericFullDense
import Submission.Work.Drive.Prelude

/-!
# The quadrisecant-isolation vocabulary

This module fixes the objects of the quadrisecant-isolation bad-set argument
(`Work.Drive.genericFullDenseK`).  See the docstrings below.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-! ## The four-parameter window -/

/-- The parameter space `(a, z, w, b)` of one quadrisecant window. -/
abbrev QP := EuclideanSpace ℝ (Fin 4)

/-- The first parameter. -/
def qA (τ : QP) : ℝ := τ.ofLp 0
/-- The second parameter. -/
def qZ (τ : QP) : ℝ := τ.ofLp 1
/-- The third parameter. -/
def qW (τ : QP) : ℝ := τ.ofLp 2
/-- The fourth parameter. -/
def qB (τ : QP) : ℝ := τ.ofLp 3

/-- The `i`-th coordinate, as a continuous linear map. -/
def qC (i : Fin 4) : QP →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).toContinuousLinearMap)

lemma qA_eq : qA = ⇑(qC 0) := by funext τ; rfl
lemma qZ_eq : qZ = ⇑(qC 1) := by funext τ; rfl
lemma qW_eq : qW = ⇑(qC 2) := by funext τ; rfl
lemma qB_eq : qB = ⇑(qC 3) := by funext τ; rfl

theorem contDiff_qA : ContDiff ℝ ⊤ qA := qA_eq ▸ (qC 0).contDiff
theorem contDiff_qZ : ContDiff ℝ ⊤ qZ := qZ_eq ▸ (qC 1).contDiff
theorem contDiff_qW : ContDiff ℝ ⊤ qW := qW_eq ▸ (qC 2).contDiff
theorem contDiff_qB : ContDiff ℝ ⊤ qB := qB_eq ▸ (qC 3).contDiff

/-- The window with coordinates `(a, z, w, b)`. -/
def qPar (a z w b : ℝ) : QP := WithLp.toLp 2 ![a, z, w, b]

@[simp] lemma qA_qPar (a z w b : ℝ) : qA (qPar a z w b) = a := by
  simp [qA, qPar]
@[simp] lemma qZ_qPar (a z w b : ℝ) : qZ (qPar a z w b) = z := by
  simp [qZ, qPar]
@[simp] lemma qW_qPar (a z w b : ℝ) : qW (qPar a z w b) = w := by
  simp [qW, qPar]
@[simp] lemma qB_qPar (a z w b : ℝ) : qB (qPar a z w b) = b := by
  simp [qB, qPar]

/-! ## The geometric data of a window -/

/-- The point at the first parameter. -/
def qPA (r : ℝ → Space) (p : Coeff × QP) : Space := pertV r p.1 (qA p.2)

/-- The point at the second parameter. -/
def qPZ (r : ℝ → Space) (p : Coeff × QP) : Space := pertV r p.1 (qZ p.2)

/-- The point at the third parameter. -/
def qPW (r : ℝ → Space) (p : Coeff × QP) : Space := pertV r p.1 (qW p.2)

/-- The point at the fourth parameter. -/
def qPB (r : ℝ → Space) (p : Coeff × QP) : Space := pertV r p.1 (qB p.2)

/-- The first chord direction `r z - r a`. -/
def qU (r : ℝ → Space) (p : Coeff × QP) : Space := qPZ r p - qPA r p

/-- The second chord direction `r w - r a`. -/
def qV (r : ℝ → Space) (p : Coeff × QP) : Space := qPW r p - qPA r p

/-- The third chord direction `r b - r a`. -/
def qS (r : ℝ → Space) (p : Coeff × QP) : Space := qPB r p - qPA r p

/-- **The triplet of pairwise collinearity conditions.** -/
def triplet (r : ℝ → Space) (p : Coeff × QP) : Space × Space × Space :=
  (cross3 (qU r p) (qV r p), cross3 (qU r p) (qS r p), cross3 (qV r p) (qS r p))

/-- The four partials of the four-point collinearity map at the window. -/
def qPartial (r : ℝ → Space) (p : Coeff × QP) : Fin 4 → Space × Space :=
  quadPartial (pertV r p.1) (qA p.2) (qZ p.2) (qW p.2) (qB p.2)

/-- The partials, transported to the `L²`-inner-product space `WithLp 2 (Space × Space)`. -/
def qPartialW (r : ℝ → Space) (p : Coeff × QP) : Fin 4 → WithLp 2 (Space × Space) :=
  fun i => WithLp.toLp 2 (qPartial r p i)

/-- **The Gram determinant of the four partials.** -/
def qGram (r : ℝ → Space) (p : Coeff × QP) : ℝ :=
  (Matrix.gram ℝ (qPartialW r p)).det

/-- **The chord–tangent defect at `a`.** -/
def qXa (r : ℝ → Space) (p : Coeff × QP) : Space :=
  cross3 (pertVelV r p.1 (qA p.2)) (qU r p)

/-! ## The compact window box and the bad set -/

/-- The compact box of windows with gaps at least `1/(k+1)` and total length at most `2π`. -/
def qBox (k : ℕ) : Set QP :=
  {τ | qA τ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧
    (1 : ℝ) / (k + 1) ≤ qZ τ - qA τ ∧
    (1 : ℝ) / (k + 1) ≤ qW τ - qZ τ ∧
    (1 : ℝ) / (k + 1) ≤ qB τ - qW τ ∧
    qB τ - qA τ ≤ 2 * Real.pi - (1 : ℝ) / (k + 1)}

/-- **The quadrisecant-isolation bad set.** -/
def qBad (r : ℝ → Space) (ρ : ℝ) (k : ℕ) : Set Coeff :=
  {c | c ∈ Kv ρ ∧ ∃ τ ∈ qBox k, triplet r (c, τ) = 0 ∧ qGram r (c, τ) = 0}

/-! ## The dependence criterion -/

/-- The four partials are linearly dependent exactly when the Gram determinant vanishes. -/
theorem qGram_eq_zero_iff (r : ℝ → Space) (p : Coeff × QP) :
    qGram r p = 0 ↔ ¬ LinearIndependent ℝ (qPartialW r p) := by
  have h := Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ) (v := qPartialW r p)
  rw [qGram]
  constructor
  · intro h0 hli
    exact (h.mpr hli) h0
  · intro h0
    by_contra hne
    exact h0 (h.mp hne)

/-! ## The parameters as a `Fin 4`-family, and the encoded data maps -/

/-- The four window parameters as a family indexed by `Fin 4`. -/
def qtp (τ : QP) : Fin 4 → ℝ := ![qA τ, qZ τ, qW τ, qB τ]

@[simp] lemma qtp_zero (τ : QP) : qtp τ 0 = qA τ := rfl
@[simp] lemma qtp_one (τ : QP) : qtp τ 1 = qZ τ := rfl
@[simp] lemma qtp_two (τ : QP) : qtp τ 2 = qW τ := rfl
@[simp] lemma qtp_three (τ : QP) : qtp τ 3 = qB τ := rfl

/-- A linear identification of `Space × Space × Space` with `ℝ⁹`. -/
def eTrip : (Space × Space × Space) ≃L[ℝ] EuclideanSpace ℝ (Fin 9) :=
  (LinearEquiv.ofFinrankEq (Space × Space × Space) (EuclideanSpace ℝ (Fin 9))
    (by simp [Module.finrank_prod, finrank_euclideanSpace_fin])).toContinuousLinearEquiv

/-- **The augmented map of the main application**: the triplet, together with the Gram
determinant of the partials.  Its zero set is the bad locus. -/
def qPsiF (r : ℝ → Space) : Coeff × QP → WithLp 2 (EuclideanSpace ℝ (Fin 9) × ℝ) :=
  fun p => WithLp.toLp 2 (eTrip (triplet r p), qGram r p)

/-- **The map of the exceptional-locus application**: the triplet, together with the
chord–tangent defect `qXa`. -/
def qPsi2 (r : ℝ → Space) : Coeff × QP → (Space × Space × Space) × Space :=
  fun p => (triplet r p, qXa r p)

/-! ## The `m`-minors of the partial matrix and the level-`m` augmented map -/

/-- The `m`-minor of the partial matrix: the determinant of the submatrix whose columns are given
by `z.1` and whose coordinate rows are given by `z.2`. -/
def qMinor (r : ℝ → Space) (p : Coeff × QP) (m : ℕ)
    (z : (Fin m → Fin 4) × (Fin m → Fin 6)) : ℝ :=
  (Matrix.of (fun i j : Fin m => (eTgt (qPartial r p (z.1 i))).ofLp (z.2 j))).det

/-- **The level-`m` augmented map**: the triplet together with all `m`-minors of the partial
matrix.  Its zero set is `{triplet = 0} ∩ {the four partials have rank < m}`. -/
def qPsiM (r : ℝ → Space) (m : ℕ) : Coeff × QP →
    (Space × Space × Space) × ((Fin m → Fin 4) → (Fin m → Fin 6) → ℝ) :=
  fun p => (triplet r p, fun a b => qMinor r p m (a, b))

/-- The span of the four partials (as a submodule of `WithLp 2 (Space × Space)`). -/
def qSpan (r : ℝ → Space) (p : Coeff × QP) : Submodule ℝ (WithLp 2 (Space × Space)) :=
  Submodule.span ℝ (Set.range (qPartialW r p))

end

end Work.Drive
