/-
Shared definitions for the proof of `Work.DSTR.M110.torusConjPow`.
-/
import Mathlib
import Submission.Work.DSTR.M110.nonsplitAux
import Submission.Work.DSTR.M110.SplitCase.GaloisPart
import Submission.Work.DSTR.M110.SplitCase.Helpers

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint Polynomial Matrix

namespace Work.DSTR.M110

variable {F : Type*} [Field F]

/-- `c` is not a square in a field only if it is non-zero. -/
lemma ne_zero_of_not_isSquare {c : F} (hc : ¬ IsSquare c) : c ≠ 0 :=
  fun h => hc (h ▸ ⟨0, by ring⟩)

/-- The companion matrix `!![0, c; 1, 0]`. -/
def companionMat (c : F) : Matrix (Fin 2) (Fin 2) F := !![0, c; 1, 0]

@[simp] lemma companionMat_apply_zero_zero (c : F) :
    companionMat c 0 0 = 0 := rfl
@[simp] lemma companionMat_apply_zero_one (c : F) :
    companionMat c 0 1 = c := rfl
@[simp] lemma companionMat_apply_one_zero (c : F) :
    companionMat c 1 0 = 1 := rfl
@[simp] lemma companionMat_apply_one_one (c : F) :
    companionMat c 1 1 = 0 := rfl

lemma companionMat_det {c : F} (hc0 : c ≠ 0) : (companionMat c).det ≠ 0 := by
  have hdet : (companionMat c).det = -c := by
    simp [companionMat, Matrix.det_fin_two]
  rw [hdet]; exact neg_ne_zero.mpr hc0

/-- The companion matrix of `X ^ 2 - c` as an element of `GL(2,F)`. -/
noncomputable def companion (c : F) (hc0 : c ≠ 0) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (companionMat c) (companionMat_det hc0)

@[simp] lemma companion_coe (c : F) (hc0 : c ≠ 0) :
    (companion c hc0 : Matrix (Fin 2) (Fin 2) F) = companionMat c :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

lemma companion_hB (c : F) (hc0 : c ≠ 0) :
    (companion c hc0 : Matrix (Fin 2) (Fin 2) F) * companion c hc0 = c • 1 := by
  rw [companion_coe]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, companionMat]

/-- The companion matrix attached to a non-square `c`. -/
noncomputable def B0 {F : Type*} [Field F] (c : F) (hc : ¬ IsSquare c) : GL (Fin 2) F :=
  companion c (ne_zero_of_not_isSquare hc)

@[simp] lemma B0_coe {F : Type*} [Field F] (c : F) (hc : ¬ IsSquare c) :
    (B0 c hc : Matrix (Fin 2) (Fin 2) F) = companionMat c := companion_coe _ _

lemma B0_hB {F : Type*} [Field F] (c : F) (hc : ¬ IsSquare c) :
    (B0 c hc : Matrix (Fin 2) (Fin 2) F) * B0 c hc = c • 1 :=
  companion_hB c (ne_zero_of_not_isSquare hc)


end Work.DSTR.M110

namespace Work.DSTR.M110

variable (p k : ℕ) [Fact p.Prime]

/-- The Frobenius ring automorphism `a ↦ a ^ p` of `GF(p^k)`. -/
noncomputable def frobEquiv : GaloisField p k ≃+* GaloisField p k :=
  (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) (GaloisField p k)).toRingEquiv

@[simp] lemma frobEquiv_apply (a : GaloisField p k) : frobEquiv p k a = a ^ p := by
  rw [show frobEquiv p k a =
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) (GaloisField p k)) a from rfl]
  rw [FiniteField.frobeniusAlgEquivOfAlgebraic_apply]
  norm_num [ZMod.card]

/-- The Frobenius automorphism is `a ↦ a ^ (p ^ n)` on its `n`-th power. -/
lemma frobEquiv_pow_apply (n : ℕ) (a : GaloisField p k) :
    (frobEquiv p k ^ n) a = a ^ (p ^ n) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      change (frobEquiv p k ^ n) (frobEquiv p k a) = a ^ p ^ (n + 1)
      rw [ih, frobEquiv_apply, ← pow_mul]
      congr 1
      rw [pow_succ']

end Work.DSTR.M110

namespace Work.DSTR.M110

variable (p k : ℕ) [Fact p.Prime]

/-- The "correcting" diagonal matrix `!![1, 0; 0, c ^ ((p-1)/2)]`. -/
noncomputable def deltaMat (c : GaloisField p k) : Matrix (Fin 2) (Fin 2) (GaloisField p k) :=
  !![1, 0; 0, c ^ ((p - 1) / 2)]

lemma deltaMat_det {c : GaloisField p k} (hc0 : c ≠ 0) : (deltaMat p k c).det ≠ 0 := by
  have hdet : (deltaMat p k c).det = c ^ ((p - 1) / 2) := by
    simp [deltaMat, Matrix.det_fin_two]
  rw [hdet]; exact pow_ne_zero _ hc0

noncomputable def deltaGL (c : GaloisField p k) (hc0 : c ≠ 0) : GL (Fin 2) (GaloisField p k) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (deltaMat p k c) (deltaMat_det p k hc0)

@[simp] lemma deltaGL_coe (c : GaloisField p k) (hc0 : c ≠ 0) :
    (deltaGL p k c hc0 : Matrix (Fin 2) (Fin 2) (GaloisField p k)) = deltaMat p k c :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

/-- The non-split torus representation attached to the companion matrix `B0 c`. -/
noncomputable def torusPermB0 [DecidableEq (GaloisField p k)] (c : GaloisField p k) (hc : ¬ IsSquare c) :
    Work.DSTR.M110.TorUnits (GaloisField p k) c →* Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)) :=
  Work.DSTR.M110.torusPerm (B0 c hc) c (B0_hB c hc)

@[simp] lemma torusPermB0_apply [DecidableEq (GaloisField p k)] (c : GaloisField p k) (hc : ¬ IsSquare c)
    (u : Work.DSTR.M110.TorUnits (GaloisField p k) c) :
    torusPermB0 p k c hc u = Work.DSTR.M110.torusPerm (B0 c hc) c (B0_hB c hc) u := rfl

/-- The involutive element `t = pglHom (mk (B0 c))`. -/
noncomputable def tB0 [DecidableEq (GaloisField p k)] (c : GaloisField p k) (hc : ¬ IsSquare c) :
    Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)) :=
  Work.AUTL2.pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk (B0 c hc))

/-- The determinant-free abbreviation of `torusAlgHom` for the companion matrix `B0`. -/
noncomputable def torusAlgHomB0 (c : GaloisField p k) (hc : ¬ IsSquare c) :
    AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C c : (GaloisField p k)[X]) →+*
      Matrix (Fin 2) (Fin 2) (GaloisField p k) :=
  torusAlgHom (B0 c hc) c (B0_hB c hc)

@[simp] lemma torusAlgHomB0_apply (c : GaloisField p k) (hc : ¬ IsSquare c)
    (μ : AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C c : (GaloisField p k)[X])) :
    torusAlgHomB0 p k c hc μ = torusAlgHom (B0 c hc) c (B0_hB c hc) μ := rfl

/-- `¬ IsSquare c` forces `p` odd. -/
lemma odd_of_not_isSquare (hk : k ≠ 0) {c : GaloisField p k} (hc : ¬ IsSquare c) : Odd p := by
  refine (Fact.out : p.Prime).odd_of_ne_two ?_
  intro hp
  subst hp
  haveI : Fintype (GaloisField 2 k) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 k) = 2 ^ k := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 k hk]
  apply hc
  rw [isSquare_iff_exists_sq]
  refine ⟨c ^ (2 ^ (k - 1)), ?_⟩
  rw [← pow_mul, show 2 ^ (k - 1) * 2 = 2 ^ k by rw [← pow_succ]; congr 1; omega,
    ← hcard, FiniteField.pow_card]

/-- For odd `p`, `((p-1)/2) * 2 = p-1`. -/
lemma half_mul_two (hodd : Odd p) : (p - 1) / 2 * 2 = p - 1 := by
  obtain ⟨m, rfl⟩ := hodd
  rw [show 2 * m + 1 - 1 = 2 * m by omega, Nat.mul_div_cancel_left _ (by norm_num)]
  omega

/-- `a ^ p = (a ^ ((p-1)/2)) ^ 2 * a` for odd `p`. -/
lemma pow_eq_half_sq_mul (hodd : Odd p) (a : GaloisField p k) :
    a ^ p = a ^ ((p - 1) / 2) * a ^ ((p - 1) / 2) * a := by
  have h : (p - 1) / 2 + (p - 1) / 2 = p - 1 := by
    have := half_mul_two p hodd; omega
  rw [← pow_add, h, ← pow_succ]
  rw [Nat.sub_add_cancel (Fact.out : p.Prime).one_le]

/-- The matrix group element of the companion torus. -/
noncomputable def torusGLB0 [DecidableEq (GaloisField p k)] (c : GaloisField p k) (hc : ¬ IsSquare c) :
    Work.DSTR.M110.TorUnits (GaloisField p k) c →* GL (Fin 2) (GaloisField p k) :=
  Work.DSTR.M110.torusGL (B0 c hc) c (B0_hB c hc)

@[simp] lemma torusGLB0_apply_coe [DecidableEq (GaloisField p k)] (c : GaloisField p k) (hc : ¬ IsSquare c)
    (u : Work.DSTR.M110.TorUnits (GaloisField p k) c) :
    ((torusGLB0 p k c hc u : GL (Fin 2) (GaloisField p k)) :
        Matrix (Fin 2) (Fin 2) (GaloisField p k)) = torusAlgHomB0 p k c hc (u : AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C c : (GaloisField p k)[X])) := rfl

@[simp] lemma torusPermB0_eq [DecidableEq (GaloisField p k)] (c : GaloisField p k) (hc : ¬ IsSquare c)
    (u : Work.DSTR.M110.TorUnits (GaloisField p k) c) :
    torusPermB0 p k c hc u =
      Work.AUTL2.pglHom (GaloisField p k)
        (Matrix.ProjGenLinGroup.mk (torusGLB0 p k c hc u)) := rfl


end Work.DSTR.M110
