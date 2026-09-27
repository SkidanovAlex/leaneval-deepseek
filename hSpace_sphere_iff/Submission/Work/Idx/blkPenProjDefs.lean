import Mathlib
import Submission.Work.Idx.WPenBlk
import Submission.Work.Idx.matPenProj_eval

/-!
# `Work.Idx.blkPenProjDefs` — shared vocabulary for `Work.Idx.blkPenProj_preSeq_blocks`

* `wIncl n d` is the index map `Fin (d+1) × Fin n → Fin (d+2) × Fin n`, `(k,i) ↦ (k.castSucc, i)`;
  the "sandwich" `(wInc n d)ᵀ * M * wInc n d` is the restriction of `M` to these indices.

* `wCorr n d b z` is the correction term of the prepend comparison: the `(d+1)`-block matrix whose
  block `(k,i)` is `z^{k-1} • (Ring.inverse (wQ n d b z) * b i)`.

* `Work.Idx.BlkPen.matEntryCLM` / `Work.Idx.BlkPen.circleIntegral_apply` — the circle integral of a
  matrix-valued function over `C(X, ℂ)` (in the `L∞` operator norm `Matrix.linftyOpNormedRing`,
  which is the structure used by `blkPenProj`) is entrywise.  Also `blkPenProj_eq`, recording that
  `blkPenProj X A B = (2πi)⁻¹ • ∮ z, (zA+B)⁻¹ A dz`.

Throughout this file the matrix norms on `Matrix ι ι C(X, ℂ)` are the `L∞` operator norms
(`open scoped Matrix.Norms.Operator`), matching the `letI` instances installed inside `blkPenProj`,
`wPsi` and `Work.KT.Idx.penProj`.
-/

namespace Work.Idx

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval Matrix.Norms.Operator

noncomputable section

variable {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The inclusion of the first `d+1` block indices into the first `d+2`. -/
def wIncl (n d : ℕ) : Fin (d + 1) × Fin n → Fin (d + 2) × Fin n :=
  fun p => (Fin.castSucc p.1, p.2)

@[simp] lemma wIncl_apply (n d : ℕ) (p : Fin (d + 1) × Fin n) :
    wIncl n d p = (Fin.castSucc p.1, p.2) := rfl

/-- `blkPenProj` is `(2πi)⁻¹` times the circle integral of the integrand `(zA+B)⁻¹A`. -/
theorem blkPenProj_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι C(X, ℂ)) :
    blkPenProj X A B = (2 * Real.pi * Complex.I)⁻¹ •
      ∮ z in C(0, 1), Work.KT.Idx.pResA A B z := rfl

/-- The correction term of the prepend comparison: the `(d+1)`-block matrix whose block `(k,i)` is
`z^{k-1} • (Ring.inverse (wQ n d b z) * b i)`. -/
def wCorr {A : Type*} [CommRing A] [Algebra ℂ A] (n d : ℕ)
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) A) (z : ℂ) :
    Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) A :=
  fun p q => (z ^ ((p.1 : ℤ) - 1) • (Ring.inverse (wQ n d b z) * b q.1)) p.2 q.2

@[simp] lemma wCorr_apply {A : Type*} [CommRing A] [Algebra ℂ A] (n d : ℕ)
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) A) (z : ℂ)
    (p q : Fin (d + 1) × Fin n) :
    wCorr n d b z p q = (z ^ ((p.1 : ℤ) - 1) • (Ring.inverse (wQ n d b z) * b q.1)) p.2 q.2 :=
  rfl

namespace BlkPen

/-- The `(i,j)` entry of a matrix, as a continuous linear functional for the `L∞-L¹` operator
norm (`Matrix.linftyOpNormedRing`). -/
def matEntryCLM {ι : Type*} [Fintype ι] (i j : ι) :
    Matrix ι ι C(X, ℂ) →L[ℂ] C(X, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun M => by
      rw [one_mul]
      have h1 : ‖M i j‖₊ ≤ ∑ l : ι, ‖M i l‖₊ :=
        Finset.single_le_sum (f := fun l => ‖M i l‖₊) (fun _ _ => zero_le) (Finset.mem_univ j)
      have h2 : (∑ l : ι, ‖M i l‖₊) ≤ (Finset.univ.sup fun k : ι => ∑ l : ι, ‖M k l‖₊) :=
        Finset.le_sup (f := fun k => ∑ l, ‖M k l‖₊) (Finset.mem_univ i)
      have h3 : ‖M i j‖₊ ≤ ‖M‖₊ := by
        rw [Matrix.linfty_opNNNorm_def]
        exact h1.trans h2
      exact NNReal.coe_le_coe.mp (by simpa using h3))

@[simp] theorem matEntryCLM_apply {ι : Type*} [Fintype ι] (i j : ι) (M : Matrix ι ι C(X, ℂ)) :
    matEntryCLM (X := X) i j M = M i j := rfl

/-- **Entrywise circle integration.** For a circle-integrable matrix-valued function, the `(i,j)`
entry of the circle integral is the circle integral of the `(i,j)` entries. -/
theorem circleIntegral_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ℂ → Matrix ι ι C(X, ℂ)) (c : ℂ) (R : ℝ) (i j : ι) (hf : CircleIntegrable f c R) :
    (∮ z in C(c, R), f z) i j = ∮ z in C(c, R), f z i j := by
  have hcomp : CompleteSpace (Matrix ι ι C(X, ℂ)) := Matrix.instCompleteSpace _ _ _
  have h := @circleIntegral_map_clm (Matrix ι ι C(X, ℂ)) _ _ (C(X, ℂ)) _ _ hcomp _
    (matEntryCLM (X := X) i j) f c R hf
  exact h

end BlkPen

end

end Work.Idx
