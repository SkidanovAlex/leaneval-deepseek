import Mathlib.Tactic.Abel
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Submission.Work.BoseRowQ2.ArithRow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.GchiReduction` — the Fock ⇄ one-body reduction for the `RowGchi` row

FS l.3253 compares the localised `Σ_j Q_{L,j}χ_Λ²Q_{L,j}` (the corpus's `Gop`) with the
total χ-mode number `Σ_k a_k†a_k` (`allNumOp`) plus a multiple of `n₊^H`.  Both operators
are *second quantisations of one-body operators*, and the corpus's model represents them
as

    `Gop      = besselOpMat A ,   allNumOp = besselOpMat F ,   NH = besselOpMat ((1/32) T)`

for the `Fin m × Fin m` matrices

    `A l l'  = Σ_{s,s'} fL s fL s' χ̂²(s'−s) · g s' l · g s l'`   (the D M D form),
    `F l l'  = Σ_k f k l · f k l'`                                (the χ-frame),
    `T l l'  = Σ_k η_H k · f k l · f k l'`                        (the high χ-frame).

This module proves the two *general* facts that turn the row into finite-dimensional
linear algebra:

* `besselOpMat_form_nonneg` — a symmetric positive semidefinite matrix `M` gives a
  form-positive operator `besselOpMat m M` (via the Gram factorisation
  `Work.BoseB4.Exists_gram_iff` and the positivity `a†(w)a(w) = a(w)*a(w) ≥ 0`);
* `besselOpMat_le_of_mat` — consequently, if the *matrix* inequality
  `A ⪯ B + C` holds (as a quadratic form on `Fin m → ℝ`), then the corresponding
  Fock-level quadratic-form inequality holds: the one-body estimate implies the row.

These are the tools that let a proof of `RowGchi` be carried out at the level of the
one-body matrices; the analytic content (the "smooth mask" estimate on `A ⪯ (1+ε)F +
γT`) is *not* here.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseRowQ2

open Work.BoseB4

/-! ## 1. Positive semidefinite matrices give form-positive operators -/

/-- **The Gram factorisation of a PSD matrix, in `besselOpMat` form.**  If `M` is a
symmetric positive semidefinite `Fin m × Fin m` matrix, then `besselOpMat m M` is the sum
of the positive rank-one operators `a†(w_l) a(w_l)`: the Gram vectors are read off from
`Work.BoseB4.Exists_gram_iff`. -/
theorem besselOpMat_form_nonneg {m : ℕ} (M : Fin m → Fin m → ℝ)
    (hsym : ∀ i j, M i j = M j i)
    (hquad : ∀ v : Fin m → ℝ, 0 ≤ ∑ i, ∑ j, v i * M i j * v j)
    (Φ : RealFock m) :
    0 ≤ bomb m (besselOpMat m M Φ) Φ := by
  classical
  -- the Gram factorisation
  obtain ⟨mm, w, hw⟩ := (Exists_gram_iff M).mpr ⟨hsym, hquad⟩
  -- `M i j = Σ_l w i l * w j l`
  have hM : M = fun i j => ∑ l : Fin mm, w i l * w j l := by
    funext i j
    rw [← hw i j, gram]
  -- `besselOpMat M` as a sum of rank-one pieces
  have hkey : (∑ l : Fin mm, (creOf m (fun i => w i l)).comp (annOf m (fun j => w j l)))
      = besselOpMat m M := by
    rw [finset_sum_creOf_comp_annOf (m := m) (W := fun p i => w i p) (S := Finset.univ), hM]
    rfl
  rw [← hkey]
  have houter : bomb m ((∑ l : Fin mm,
      (creOf m (fun i => w i l)).comp (annOf m (fun j => w j l))) Φ) Φ
      = ∑ l : Fin mm,
          bomb m (((creOf m (fun i => w i l)).comp (annOf m (fun j => w j l))) Φ) Φ := by
    simp only [LinearMap.sum_apply, map_sum]
  rw [houter]
  have hterm : ∀ l : Fin mm,
      bomb m ((creOf m (fun i => w i l)).comp (annOf m (fun j => w j l)) Φ) Φ
        = bomb m (annOf m (fun j => w j l) Φ) (annOf m (fun j => w j l) Φ) := by
    intro l
    rw [LinearMap.comp_apply, CreOf_annOf_adjoint]
  exact Finset.sum_nonneg fun l _ => by rw [hterm l]; exact Bomb_self_nonneg _

/-- **The Fock-level inequality from a matrix inequality.**  If the matrix difference
`B + C - A` is symmetric and positive semidefinite, then for every Fock state `Φ`

    `⟪besselOpMat A Φ, Φ⟫ ≤ ⟪besselOpMat B Φ, Φ⟫ + ⟪besselOpMat C Φ, Φ⟫`.

This is the exact form in which the `RowGchi` row reduces to one-body linear algebra:
take `A` the localised `Gop` matrix, `B = (1+ε)F` and `C = γ·T`. -/
theorem besselOpMat_le_of_mat {m : ℕ} (A B C : Fin m → Fin m → ℝ)
    (hsym : ∀ i j, B i j + C i j - A i j = B j i + C j i - A j i)
    (hquad : ∀ v : Fin m → ℝ, 0 ≤ ∑ i, ∑ j, v i * (B i j + C i j - A i j) * v j)
    (Φ : RealFock m) :
    bomb m (besselOpMat m A Φ) Φ
      ≤ bomb m (besselOpMat m B Φ) Φ + bomb m (besselOpMat m C Φ) Φ := by
  have hnn := besselOpMat_form_nonneg (fun i j => B i j + C i j - A i j) hsym hquad Φ
  -- rewrite `besselOpMat (B + C - A)` as `besselOpMat B + besselOpMat C - besselOpMat A`
  have hrew : besselOpMat m (fun i j => B i j + C i j - A i j)
      = besselOpMat m B + (besselOpMat m C - besselOpMat m A) := by
    have h1 : (fun i j => B i j + C i j - A i j)
        = (fun i j => B i j + C i j) - A := rfl
    rw [h1, besselOpMat_sub]
    have h2 : (fun i j => B i j + C i j) = B + C := rfl
    rw [h2, besselOpMat_add]
    abel
  rw [hrew] at hnn
  -- expand the form
  have hlin : bomb m ((besselOpMat m B + (besselOpMat m C - besselOpMat m A)) Φ) Φ
      = bomb m (besselOpMat m B Φ) Φ
        + (bomb m (besselOpMat m C Φ) Φ - bomb m (besselOpMat m A Φ) Φ) := by
    rw [LinearMap.add_apply, map_add, LinearMap.sub_apply, map_sub,
      LinearMap.add_apply, LinearMap.sub_apply]
  rw [hlin] at hnn
  linarith

end Work.BoseRowQ2
