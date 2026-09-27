import Mathlib
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.FP.pencil_proj_data
import Submission.Work.KT.FP.pCirc_eq_of_annulus
import Submission.Work.KT.FP.prepend_admissible
import Submission.Work.KT.FP.coeffSeq_appSeq_preSeq
import Submission.Work.Idx.wPen_append
import Submission.Work.Idx.wPen_prepend

/-!
# `Work.KT.FP.lindAt_pad_step` — the degree-padding step for `lindAt`

`lindAt X n m P ρ = cls (matPProj X _ (linAf X n m) (linBf X n m P) ρ) - m • cls (one n)` is the
candidate index of a Laurent matrix `P` of degree bound `m`.

Increasing the degree bound `m ↦ m + 1` replaces the coefficient sequence
`b = coeffSeq X n m P = ((P)_{-m}, …, (P)_m)` (length `2m+1`, carried by the pencil
`z • wPenAf X n (2m) + wPenBf X n (2m) b`) by the padded sequence
`(0, b_0, …, b_{2m}, 0) = appSeq (preSeq b)` (length `2m+3`, carried by the pencil
`z • wPenAf X n (2m+2) + wPenBf X n (2m+2) ·`).  By Hatcher's formulas (1) and (2)
(`Work.Idx.wPen_append`, `Work.Idx.wPen_prepend`):

* *append* (`b ↦ (b, 0)`) does not change the class of the Riesz projection;
* *prepend* (`b ↦ (0, b)`) increases it by the trivial class `cls (one n)`.

The two steps are applied at the radii `1` (allowed by the invertibility of the pencils on the
annuli `ρ ≤ ‖z‖ ≤ 1` and `ρ' ≤ ‖z‖ ≤ 1`, through the radius independence `matPProj_radius_eq_one`),
and the `- m • cls (one n)` bookkeeping cancels the extra summand.
-/

namespace Work.KT.FP

open Matrix

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-! ### Radius independence of the matrix pencil projection -/

/-- If the pencil `z ↦ z • A + B` is invertible on the closed annulus `ρ ≤ ‖z‖ ≤ 1`
(`0 < ρ ≤ 1`), then the matrix pencil projection `matPProj X N A B` takes the same value at the
radii `ρ` and `1`.

This is the second component of `pencil_proj_data`, transported to `matPProj`; the case `ρ = 1` is
trivial.  The instances are supplied explicitly because `matPProj` installs the `L∞` operator
norm by a `letI`, which a tactic-mode `letI`/`haveI` cannot reproduce definitionally. -/
lemma matPProj_radius_eq_one (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {N : ℕ} (A B : Matrix (Fin N) (Fin N) C(X, ℂ)) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • A + B)) :
    matPProj X N A B ρ = matPProj X N A B 1 := by
  rcases lt_or_eq_of_le hρ1 with hlt | heq
  · have h := @pencil_proj_data (Matrix (Fin N) (Fin N) C(X, ℂ)) Matrix.linftyOpNormedRing
      Matrix.linftyOpNormedAlgebra (Matrix.instCompleteSpace (Fin N) (Fin N) C(X, ℂ)) A B
    exact h.2 hρ0 hlt le_rfl hunit
  · rw [heq]

/-! ### Block versus flat form of the W pencil -/

/-- The block form `z • wPenA + wPenB` and the flat form `wPenPencil` of the W pencil of a
coefficient sequence are simultaneously units: the flat form is the `finProdFinEquiv`-reindexing
of the block form, and `Matrix.reindex` preserves units. -/
lemma isUnit_wPenPencil_iff (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {n d : ℕ} (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) (z : ℂ) :
    IsUnit (z • Work.KT.Idx.wPenA X n d + Work.KT.Idx.wPenB X n d b)
      ↔ IsUnit (Work.KT.Idx.wPenPencil X n d b z) := by
  rw [Work.KT.Idx.wPenPencil, Work.KT.Idx.wPenAf, Work.KT.Idx.wPenBf]
  rw [← Work.Idx.reindex_smul_app finProdFinEquiv z (Work.KT.Idx.wPenA X n d)]
  rw [← Work.Idx.reindex_add_app finProdFinEquiv
        (z • Work.KT.Idx.wPenA X n d) (Work.KT.Idx.wPenB X n d b)]
  exact (Work.Idx.isUnit_reindex_iff_app finProdFinEquiv _).symm

end

/-- **The degree-padding step.**  If the pencils of the coefficient sequences of the degree bounds
`m` and `m + 1` of a Laurent matrix `P` (whose coefficients vanish outside `[-m, m]`) are
invertible on the annuli `ρ ≤ ‖z‖ ≤ 1` and `ρ' ≤ ‖z‖ ≤ 1` respectively, then the candidate index
computed at degree bound `m + 1` and radius `ρ'` agrees with the one computed at degree bound `m`
and radius `ρ`. -/
theorem lindAt_pad_step (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n m : ℕ) (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
    (hb : ∀ (i j : Fin n) (k : ℤ), (m : ℤ) < k ∨ k < -(m : ℤ) → (P i j).coeff k = 0)
    {ρ ρ' : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hρ'0 : 0 < ρ') (hρ'1 : ρ' ≤ 1)
    (hadm : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • Work.KT.FP.linAf X n m + Work.KT.FP.linBf X n m P))
    (hadm' : ∀ z : ℂ, ρ' ≤ ‖z‖ → ‖z‖ ≤ 1 →
      IsUnit (z • Work.KT.FP.linAf X n (m + 1) + Work.KT.FP.linBf X n (m + 1) P)) :
    Work.KT.FP.lindAt X n (m + 1) P ρ' = Work.KT.FP.lindAt X n m P ρ := by
  -- the sequence identity: the padded sequence is `appSeq (preSeq c)`
  have hseq := coeffSeq_appSeq_preSeq X n m P hb
  -- the W pencil of `coeffSeq X n m P` is a unit on the unit circle
  have hC1 : ∀ z : ℂ, ‖z‖ = 1 →
      IsUnit (Work.KT.Idx.wPenPencil X n (2 * m) (coeffSeq X n m P) z) := by
    intro z hz
    show IsUnit (z • Work.KT.Idx.wPenAf X n (2 * m)
      + Work.KT.Idx.wPenBf X n (2 * m) (coeffSeq X n m P))
    exact hadm z (by rw [hz]; exact hρ1) (le_of_eq hz)
  -- the W pencil of the padded sequence `appSeq (preSeq c) = coeffSeq X n (m+1) P` is a unit too
  have hC3 : ∀ z : ℂ, ‖z‖ = 1 →
      IsUnit (Work.KT.Idx.wPenPencil X n (2 * m + 2)
        (Work.KT.Idx.appSeq X (Work.KT.Idx.preSeq X (coeffSeq X n m P))) z) := by
    intro z hz
    rw [← hseq]
    show IsUnit (z • Work.KT.Idx.wPenAf X n (2 * (m + 1))
      + Work.KT.Idx.wPenBf X n (2 * (m + 1)) (coeffSeq X n (m + 1) P))
    exact hadm' z (by rw [hz]; exact hρ'1) (le_of_eq hz)
  -- the prepended pencil (block form) is a unit on the unit circle
  have hPreBlock : ∀ z : ℂ, ‖z‖ = 1 →
      IsUnit (z • Work.KT.Idx.wPenA X n (2 * m + 1) + Work.KT.Idx.wPenB X n (2 * m + 1)
        (Work.KT.Idx.preSeq X (coeffSeq X n m P))) := by
    intro z hz
    have h := prepend_admissible X n (2 * m) (coeffSeq X n m P) (ρ := 1) (by norm_num) le_rfl
      (fun w hw1 hw2 => (isUnit_wPenPencil_iff X (coeffSeq X n m P) w).mpr
        (hC1 w (le_antisymm hw2 hw1)))
    exact h z (le_of_eq hz.symm) (le_of_eq hz)
  have hC2 : ∀ z : ℂ, ‖z‖ = 1 →
      IsUnit (Work.KT.Idx.wPenPencil X n (2 * m + 1)
        (Work.KT.Idx.preSeq X (coeffSeq X n m P)) z) :=
    fun z hz => (isUnit_wPenPencil_iff X (Work.KT.Idx.preSeq X (coeffSeq X n m P)) z).mp
      (hPreBlock z hz)
  -- Hatcher's formulas (1) (append) and (2) (prepend)
  have happ := Work.Idx.wPen_append X n (2 * m + 1) (Work.KT.Idx.preSeq X (coeffSeq X n m P))
    hC2 hC3
  have hpres := Work.Idx.wPen_prepend X n (2 * m) (coeffSeq X n m P) hC1 hC2
  -- the class identity at radius `1`
  have hcls : Work.KT.cls (⟨(2 * (m + 1) + 1) * n,
        matPProj X ((2 * (m + 1) + 1) * n) (linAf X n (m + 1)) (linBf X n (m + 1) P) 1⟩
        : Mat C(X, ℂ))
      = Work.KT.cls (⟨(2 * m + 1) * n,
          matPProj X ((2 * m + 1) * n) (linAf X n m) (linBf X n m P) 1⟩ : Mat C(X, ℂ))
        + Work.KT.cls (Mat.one C(X, ℂ) n) := by
    simp only [linAf, linBf]
    rw [hseq]
    exact happ.trans hpres
  -- radius independence of the two projections
  have hrad := matPProj_radius_eq_one X (linAf X n m) (linBf X n m P) hρ0 hρ1 hadm
  have hrad' := matPProj_radius_eq_one X (linAf X n (m + 1)) (linBf X n (m + 1) P) hρ'0 hρ'1 hadm'
  unfold lindAt
  rw [hrad', hrad, hcls, add_nsmul, one_nsmul]
  abel

end Work.KT.FP
