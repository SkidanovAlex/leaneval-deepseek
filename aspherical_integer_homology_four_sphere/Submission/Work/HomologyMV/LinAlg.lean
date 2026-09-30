import Mathlib
import Submission.Work.HomologyMV.Model

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `HomologyMV/`: integer linear algebra certificates

The certificates produced by `Data.lean` are *integer matrix identities*: a right or left inverse
of a matrix, or a change of basis bringing a matrix to normal form.  This file turns such
identities into the linear-algebraic facts the Mayer–Vietoris computation needs
(`range = ⊤`, `ker = ⊥`), and records the two normal-form matrices

* `projMat m = [1_m | 0] : ℤ^{m+1} → ℤ^m`,
* `inclMat m = [1_m ; 0] : ℤ^m → ℤ^{m+1}`.

## Main results

* `range_toLin'_eq_top_of_mul_eq_one` — a matrix with a right inverse is surjective;
* `ker_toLin'_eq_bot_of_mul_eq_one` — a matrix with a left inverse is injective;
* `range_eq_top_of_subsingleton_target` — every map into a trivial module is surjective.

The two *normal form* lemmas (`ker_toLin'_iso_int_of_normalForm`,
`coker_toLin'_iso_int_of_normalForm`) are proved in the files named after them.
-/

namespace Work.HomologyMV

open CategoryTheory

noncomputable section

/-- The matrix `[1_m | 0] : ℤ^{m+1} → ℤ^m`. -/
def projMat (m : ℕ) : Matrix (Fin m) (Fin (m + 1)) ℤ :=
  fun i j => if (j : ℕ) = (i : ℕ) then 1 else 0

/-- The matrix `[1_m ; 0] : ℤ^m → ℤ^{m+1}`. -/
def inclMat (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) ℤ :=
  fun i j => if (i : ℕ) = (j : ℕ) then 1 else 0

@[simp] theorem projMat_apply_val (m : ℕ) (i : Fin m) (j : Fin (m + 1)) :
    projMat m i j = if (j : ℕ) = (i : ℕ) then 1 else 0 := rfl

@[simp] theorem inclMat_apply_val (m : ℕ) (i : Fin (m + 1)) (j : Fin m) :
    inclMat m i j = if (i : ℕ) = (j : ℕ) then 1 else 0 := rfl

/-- `Matrix.toLin'` of a matrix with a *right* inverse is surjective. -/
theorem range_toLin'_eq_top_of_mul_eq_one {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (B : Matrix (Fin n) (Fin m) ℤ) (h : A * B = 1) : (Matrix.toLin' A).range = ⊤ := by
  rw [LinearMap.range_eq_top]
  have h1 : (Matrix.toLin' A).comp (Matrix.toLin' B) = LinearMap.id := by
    rw [← Matrix.toLin'_mul, h, Matrix.toLin'_one]
  intro y
  exact ⟨Matrix.toLin' B y, by simpa using LinearMap.congr_fun h1 y⟩

/-- `Matrix.toLin'` of a matrix with a *left* inverse is injective. -/
theorem ker_toLin'_eq_bot_of_mul_eq_one {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (C : Matrix (Fin n) (Fin m) ℤ) (h : C * A = 1) : (Matrix.toLin' A).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  have h1 : (Matrix.toLin' C).comp (Matrix.toLin' A) = LinearMap.id := by
    rw [← Matrix.toLin'_mul, h, Matrix.toLin'_one]
  intro x y hxy
  have hx : Matrix.toLin' A (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have h2 := LinearMap.congr_fun h1 (x - y)
  simp only [LinearMap.comp_apply, hx, map_zero, LinearMap.id_coe, id_eq] at h2
  exact sub_eq_zero.mp h2.symm

/-- Every linear map into a trivial module has range `⊤`. -/
theorem range_eq_top_of_subsingleton_target {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] [Subsingleton N] (f : M →ₗ[ℤ] N) : f.range = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro y
  exact ⟨0, Subsingleton.elim _ _⟩

/-- The zero module is a subsingleton. -/
theorem subsingleton_freeMod_zero : Subsingleton (freeMod 0) := by
  rw [freeMod]
  infer_instance

end

end Work.HomologyMV
