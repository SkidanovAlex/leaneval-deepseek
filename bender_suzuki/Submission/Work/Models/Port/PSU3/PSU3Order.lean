/-
The order of `PSU(3, 2^n)`:  `|SU(3,q)| / gcd(3, q+1)` with `q = 2^n`.

`PSU(3,2^n)` is the image of `SU(3,2^n)` in `PGL(3,2^(2n)) = GL(3,2^(2n))/Z`, so
`|PSU(3,q)| = |SU(3,q)| / |Z(SU(3,q))|`.  The scalar matrices of `SU(3,q)` are the
`λ·1` with `λ^(q+1) = 1` (the form is preserved) and `λ^3 = 1` (unit determinant),
and the number of such `λ ∈ GF(q²)^×` is `gcd(3, q+1)`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSU3.Order
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.card_map_mul_card_inf_ker
import Submission.Work.Models.Port.Commons.FieldTheory.Finite.fixed_card_pow_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs

namespace Submission.PSU3

/-! ## Scalar matrices in `SU(3,2^n)` -/

lemma herm_scalar (n : ℕ) (a : F n) :
    herm (Matrix.scalar (Fin 3) a) = Matrix.scalar (Fin 3) (a ^ (2 ^ n)) := by
  rw [Matrix.scalar_apply, herm_diagonal, ← Matrix.scalar_apply]

/-- `scalar a * J3 * scalar b = (a*b) • J3`. -/
lemma scalar_mul_J3_mul_scalar (n : ℕ) (a b : F n) :
    Matrix.scalar (Fin 3) a * (J3 : Matrix (Fin 3) (Fin 3) (F n)) * Matrix.scalar (Fin 3) b =
      (a * b) • (J3 : Matrix (Fin 3) (Fin 3) (F n)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J3, Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_three]

lemma det_scalar_three (n : ℕ) (u : (F n)ˣ) :
    GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) u) = u ^ 3 := by
  rw [Matrix.GeneralLinearGroup.det_scalar]
  norm_num

/-- The scalar matrices of `SU(3,2^n)`: `λ·1` with `λ^(q+1) = 1` and `λ^3 = 1`. -/
theorem isSU3_scalar_iff (n : ℕ) (u : (F n)ˣ) :
    IsSU3 (Matrix.GeneralLinearGroup.scalar (Fin 3) u) ↔ u ^ (2 ^ n + 1) = 1 ∧ u ^ 3 = 1 := by
  have hcoe := Matrix.GeneralLinearGroup.coe_scalar (n := Fin 3) u
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩
  · have h1 := h.1
    rw [hcoe, herm_scalar, scalar_mul_J3_mul_scalar, ← pow_succ] at h1
    have h2 := congrFun (congrFun h1 0) 2
    refine Units.ext ?_
    simpa [J3] using h2
  · rw [← det_scalar_three n u]
    exact h.2
  · have h1 : (↑u : F n) ^ (2 ^ n + 1) = 1 := by
      have := congrArg (fun x : (F n)ˣ => (x : F n)) h.1
      simpa using this
    rw [hcoe, herm_scalar, scalar_mul_J3_mul_scalar, ← pow_succ, h1, one_smul]
  · rw [det_scalar_three, h.2]

lemma scalar_eq_scalar_iff (n : ℕ) {u v : (F n)ˣ}
    (h : Matrix.GeneralLinearGroup.scalar (Fin 3) u = Matrix.GeneralLinearGroup.scalar (Fin 3) v) :
    u = v := by
  apply Units.ext
  have h' := congrArg (fun x : GL (Fin 3) (F n) =>
    ((x : Matrix (Fin 3) (Fin 3) (F n)) 0 0)) h
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h'

/-- The unit behind a scalar matrix in `SU(3,2^n)`. -/
noncomputable def su3CenterUnit (n : ℕ)
    (A : ↥(SU3 n ⊓ (Matrix.GeneralLinearGroup.scalar (Fin 3)).range)) : (F n)ˣ :=
  Classical.choose (MonoidHom.mem_range.mp A.2.2)

lemma su3CenterUnit_spec (n : ℕ)
    (A : ↥(SU3 n ⊓ (Matrix.GeneralLinearGroup.scalar (Fin 3)).range)) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) (su3CenterUnit n A) = A.1 :=
  Classical.choose_spec (MonoidHom.mem_range.mp A.2.2)

noncomputable def su3CenterToFun (n : ℕ)
    (A : ↥(SU3 n ⊓ (Matrix.GeneralLinearGroup.scalar (Fin 3)).range)) :
    {u : (F n)ˣ // u ^ (2 ^ n + 1) = 1 ∧ u ^ 3 = 1} :=
  ⟨su3CenterUnit n A, (isSU3_scalar_iff n (su3CenterUnit n A)).mp (by
    rw [su3CenterUnit_spec n A]; exact A.2.1)⟩

noncomputable def su3CenterInv (n : ℕ)
    (u : {u : (F n)ˣ // u ^ (2 ^ n + 1) = 1 ∧ u ^ 3 = 1}) :
    ↥(SU3 n ⊓ (Matrix.GeneralLinearGroup.scalar (Fin 3)).range) :=
  ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) u.1,
    ⟨(isSU3_scalar_iff n u.1).mpr u.2, MonoidHom.mem_range.mpr ⟨u.1, rfl⟩⟩⟩

/-- The scalar matrices in `SU(3,2^n)` are the units `λ` with `λ^(q+1) = λ^3 = 1`. -/
noncomputable def su3CenterEquiv (n : ℕ) :
    ↥(SU3 n ⊓ (Matrix.GeneralLinearGroup.scalar (Fin 3)).range) ≃
      {u : (F n)ˣ // u ^ (2 ^ n + 1) = 1 ∧ u ^ 3 = 1} where
  toFun := su3CenterToFun n
  invFun := su3CenterInv n
  left_inv A := by
    apply Subtype.ext
    show Matrix.GeneralLinearGroup.scalar (Fin 3) (su3CenterUnit n A) = A.1
    exact su3CenterUnit_spec n A
  right_inv u := by
    apply Subtype.ext
    show su3CenterUnit n (su3CenterInv n u) = u.1
    exact scalar_eq_scalar_iff n (su3CenterUnit_spec n (su3CenterInv n u))

/-- `|Z(SU(3,2^n))| = gcd(3, q+1)`. -/
theorem card_su3_center (n : ℕ) (hn : 1 ≤ n) :
    Nat.card ↥(SU3 n ⊓ Subgroup.center (GL (Fin 3) (F n))) = Nat.gcd 3 (2 ^ n + 1) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  rw [Nat.card_congr (su3CenterEquiv n)]
  rw [Nat.card_congr (Equiv.subtypeEquivRight
    (fun u : (F n)ˣ => (pow_gcd_eq_one (a := u) (m := 2 ^ n + 1) (n := 3)).symm))]
  rw [Commons.FieldTheory.Finite.fixedPowTwo.card_units_pow_eq_one_gcd, Nat.card_units,
    GaloisField.card 2 (2 * n) (by omega)]
  have hdvd : Nat.gcd (2 ^ n + 1) 3 ∣ 2 ^ (2 * n) - 1 :=
    (Nat.gcd_dvd_left _ _).trans
      ⟨2 ^ n - 1, by rw [← two_pow_sub_one_mul_add_one, mul_comm]⟩
  rw [Nat.gcd_comm (2 ^ (2 * n) - 1), Nat.gcd_eq_left_iff_dvd.mpr hdvd,
    Nat.gcd_comm 3 (2 ^ n + 1)]

/-- The order of `PSU(3,2^n)`: `q^3 (q^2-1) (q^3+1) / gcd(3, q+1)`. -/
theorem card_PSU3Model (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (PSU3Model n) * Nat.gcd 3 (2 ^ n + 1) =
      2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1) := by
  rw [PSU3Model_eq_map_SU3]
  have h := Commons.GroupTheory.Subgroup.card_map_mul_card_inf_ker
    (ProjGenLinGroup.mk : GL (Fin 3) (F n) →* ProjGenLinGroup (Fin 3) (F n))
    ProjGenLinGroup.mk_surjective (SU3 n)
  rw [ProjGenLinGroup.ker_mk, card_su3_center n hn] at h
  rw [h, card_SU3 n hn]

end Submission.PSU3
