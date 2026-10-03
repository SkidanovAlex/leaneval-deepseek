/-
# The ping-pong geometry in the upper half plane

Entries of the powers of the matrices `Amat p`, `Bmat p`, `gmat p j` of `SL(2, ℤ)`, and the action
of `gmat p j ^ k` on the upper half plane.
-/
import Mathlib
import Submission.Work.ORLocInd.FKS.SL2Defs

namespace Work.ORLocInd.FKS

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups

/-! ## Entries of the powers of `Amat` and `Bmat` -/

private lemma matA_pow (p m : ℕ) :
    (!![1, (p : ℤ); 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) ^ m = !![1, (p : ℤ) * m; 0, 1] := by
  induction m with
  | zero => ext i l; fin_cases i <;> fin_cases l <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private lemma matB_pow (p m : ℕ) :
    (!![1, 0; (p : ℤ), 1] : Matrix (Fin 2) (Fin 2) ℤ) ^ m = !![1, 0; (p : ℤ) * m, 1] := by
  induction m with
  | zero => ext i l; fin_cases i <;> fin_cases l <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma Amat_pow_coe (p m : ℕ) :
    coeMonoidHom (Amat p ^ m) = !![1, (p : ℤ) * m; 0, 1] := by
  rw [map_pow,
    show coeMonoidHom (Amat p) = (!![1, (p : ℤ); 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) from rfl]
  exact matA_pow p m

lemma Bmat_pow_coe (p m : ℕ) :
    coeMonoidHom (Bmat p ^ m) = !![1, 0; (p : ℤ) * m, 1] := by
  rw [map_pow,
    show coeMonoidHom (Bmat p) = (!![1, 0; (p : ℤ), 1] : Matrix (Fin 2) (Fin 2) ℤ) from rfl]
  exact matB_pow p m

private lemma invA_coe (p m : ℕ) :
    coeMonoidHom ((Amat p ^ m)⁻¹) = !![1, -((p : ℤ) * m); 0, 1] := by
  have hmul : coeMonoidHom (Amat p ^ m) * coeMonoidHom ((Amat p ^ m)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hM : coeMonoidHom ((Amat p ^ m)⁻¹) = (coeMonoidHom (Amat p ^ m))⁻¹ := by
    rw [← Matrix.inv_eq_right_inv hmul]
  rw [hM, Amat_pow_coe, Matrix.inv_eq_right_inv]
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private lemma invB_coe (p m : ℕ) :
    coeMonoidHom ((Bmat p ^ m)⁻¹) = !![1, 0; -((p : ℤ) * m), 1] := by
  have hmul : coeMonoidHom (Bmat p ^ m) * coeMonoidHom ((Bmat p ^ m)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hM : coeMonoidHom ((Bmat p ^ m)⁻¹) = (coeMonoidHom (Bmat p ^ m))⁻¹ := by
    rw [← Matrix.inv_eq_right_inv hmul]
  rw [hM, Bmat_pow_coe, Matrix.inv_eq_right_inv]
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma Amat_zpow_coe (p : ℕ) (k : ℤ) :
    coeMonoidHom (Amat p ^ k) = !![1, (p : ℤ) * k; 0, 1] := by
  rcases Int.eq_nat_or_neg k with ⟨m, hm | hm⟩
  · subst hm; rw [zpow_natCast]; exact Amat_pow_coe p m
  · subst hm
    rw [_root_.zpow_neg, zpow_natCast]
    simpa [mul_neg] using invA_coe p m

lemma Bmat_zpow_coe (p : ℕ) (k : ℤ) :
    coeMonoidHom (Bmat p ^ k) = !![1, 0; (p : ℤ) * k, 1] := by
  rcases Int.eq_nat_or_neg k with ⟨m, hm | hm⟩
  · subst hm; rw [zpow_natCast]; exact Bmat_pow_coe p m
  · subst hm
    rw [_root_.zpow_neg, zpow_natCast]
    simpa [mul_neg] using invB_coe p m


/-! ## The entries of `gmat` -/

lemma gmat_coe (p j : ℕ) :
    coeMonoidHom (gmat p j) =
      !![1 + (p : ℤ)^2 * (j : ℤ), -((p : ℤ)^3 * (j : ℤ)^2); (p : ℤ), 1 - (p : ℤ)^2 * (j : ℤ)] := by
  have hB : coeMonoidHom (Bmat p) = (!![1, 0; (p : ℤ) * 1, 1] : Matrix (Fin 2) (Fin 2) ℤ) := by
    simpa using Bmat_zpow_coe p 1
  have hAinv : coeMonoidHom ((Amat p ^ (j : ℤ))⁻¹) =
      (!![1, -((p : ℤ) * (j : ℤ)); 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [zpow_natCast]; exact invA_coe p j
  show coeMonoidHom (Amat p ^ (j : ℤ) * Bmat p * (Amat p ^ (j : ℤ))⁻¹) = _
  rw [map_mul, map_mul, Amat_zpow_coe, hB, hAinv]
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma gmat_apply (p j : ℕ) (i l : Fin 2) :
    (gmat p j) i l =
      (!![1 + (p : ℤ)^2 * (j : ℤ), -((p : ℤ)^3 * (j : ℤ)^2); (p : ℤ), 1 - (p : ℤ)^2 * (j : ℤ)] :
        Matrix (Fin 2) (Fin 2) ℤ) i l := by
  rw [show (gmat p j : SL(2, ℤ)) i l = (coeMonoidHom (gmat p j)) i l from rfl, gmat_coe]

/-! ## Compatibility of `SpecialLinearGroup.map` with entry extraction -/

lemma sl_map_apply {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A : SL(2, R)) (i l : Fin 2) : (SpecialLinearGroup.map f A) i l = f (A i l) := rfl

lemma sl_map_map {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : S →+* T) (g : R →+* S) (A : SL(2, R)) :
    SpecialLinearGroup.map f (SpecialLinearGroup.map g A) =
      SpecialLinearGroup.map (f.comp g) A := by
  apply Matrix.SpecialLinearGroup.ext
  intro i l
  rw [sl_map_apply, sl_map_apply, sl_map_apply, RingHom.comp_apply]

lemma gmat_apply_00 (p j : ℕ) : (gmat p j) 0 0 = 1 + (p : ℤ)^2 * (j : ℤ) := by
  have h := gmat_apply p j 0 0
  simpa using h

lemma gmat_apply_01 (p j : ℕ) : (gmat p j) 0 1 = -((p : ℤ)^3 * (j : ℤ)^2) := by
  have h := gmat_apply p j 0 1
  simpa using h

lemma gmat_apply_10 (p j : ℕ) : (gmat p j) 1 0 = (p : ℤ) := by
  have h := gmat_apply p j 1 0
  simpa using h

lemma gmat_apply_11 (p j : ℕ) : (gmat p j) 1 1 = 1 - (p : ℤ)^2 * (j : ℤ) := by
  have h := gmat_apply p j 1 1
  simpa using h

/-! ## The action of the powers -/

lemma Amat_zpow_smul (p : ℕ) (k : ℤ) (z : UpperHalfPlane) :
    ↑((Amat p ^ k) • z) = ↑z + (p : ℂ) * k := by
  rw [coe_specialLinearGroup_apply,
    show (↑(Amat p ^ k) : Matrix (Fin 2) (Fin 2) ℤ) = coeMonoidHom (Amat p ^ k) from rfl,
    Amat_zpow_coe]
  simp

lemma Bmat_zpow_smul (p : ℕ) (k : ℤ) (z : UpperHalfPlane) :
    ↑((Bmat p ^ k) • z) = ↑z / ((p : ℂ) * k * ↑z + 1) := by
  rw [coe_specialLinearGroup_apply,
    show (↑(Bmat p ^ k) : Matrix (Fin 2) (Fin 2) ℤ) = coeMonoidHom (Bmat p ^ k) from rfl,
    Bmat_zpow_coe]
  simp

/-! ## The action of `gmat p j ^ k` -/

lemma gmat_zpow_eq (p j : ℕ) (k : ℤ) :
    gmat p j ^ k = Amat p ^ (j : ℤ) * Bmat p ^ k * (Amat p ^ (j : ℤ))⁻¹ := by
  conv_lhs => rw [gmat, ← MulAut.conj_apply (Amat p ^ (j : ℤ)) (Bmat p)]
  rw [← map_zpow, MulAut.conj_apply]

theorem coe_gmat_pow_smul (p j : ℕ) (k : ℤ) (z : UpperHalfPlane) :
    ↑((gmat p j ^ k) • z) =
      (↑z - (p * j : ℂ)) / (((p : ℤ) * k : ℂ) * (↑z - (p * j : ℂ)) + 1) + (p * j : ℂ) := by
  have hA : (Amat p ^ (j : ℤ))⁻¹ = Amat p ^ (-(j : ℤ)) := by rw [_root_.zpow_neg]
  rw [gmat_zpow_eq, hA, mul_smul, mul_smul, Amat_zpow_smul, Bmat_zpow_smul, Amat_zpow_smul]
  push_cast
  ring

end Work.ORLocInd.FKS
