/-
The order of `SU(3, 2^n)`:  `|SU(3,q)| = q^3 (q^2 - 1) (q^3 + 1)` with `q = 2^n`.

Strategy.  The group `SU(3,q)` acts on the set `X` of non-zero isotropic vectors of the
Hermitian space `(F^3, J)`.  We prove by an explicit computation that this action is
**transitive**: every non-zero isotropic vector is the first column of a suitable matrix in
`SU(3,q)` (using the maximal torus, the "opposite" root elements `S·u(b,c)·S` and the Weyl
element `S = J`).  The stabiliser of the first basis vector `e_0` is the unipotent radical
`U` of order `q^3`.  Hence `|SU(3,q)| = |U| · |X|`, and `|X| = (q^3+1)(q^2-1)`, which is
obtained by a direct count of the solutions of `x^q z + y^(q+1) + z^q x = 0`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSU3.Borel
import Submission.Work.Models.Port.Commons.FieldTheory.FiniteField.trace_surjective_galoisField_even
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

/-! ## The Weyl element `S = J3` -/

lemma J3_det (n : ℕ) : (J3 : Matrix (Fin 3) (Fin 3) (F n)).det = 1 := by
  have hmul : (J3 : Matrix (Fin 3) (Fin 3) (F n)).det *
      (J3 : Matrix (Fin 3) (Fin 3) (F n)).det = 1 := by
    rw [← Matrix.det_mul, J3_mul_self, Matrix.det_one]
  rcases mul_self_eq_one_iff.mp hmul with h | h
  · exact h
  · rw [h, CharTwo.neg_eq]

/-- The Weyl element of `SU(3,2^n)`: it is the Gram matrix `J3` itself. -/
noncomputable def suSg (n : ℕ) : GL (Fin 3) (F n) :=
  Matrix.GeneralLinearGroup.mk'' (J3) (by rw [J3_det]; exact isUnit_one)

@[simp] lemma suSg_coe (n : ℕ) :
    ((suSg n : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) = J3 :=
  Matrix.GeneralLinearGroup.val_mk'' _ _

lemma suSg_isSU3 (n : ℕ) : IsSU3 (suSg n) := by
  refine ⟨?_, ?_⟩
  · rw [suSg_coe, herm_J3, J3_mul_self, one_mul]
  · show GeneralLinearGroup.det (suSg n) = 1
    apply Units.ext
    show ((suSg n : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)).det = 1
    rw [suSg_coe, J3_det]

lemma suSg_mem_SU3 (n : ℕ) : suSg n ∈ SU3 n := suSg_isSU3 n

lemma suSg_mul_self (n : ℕ) : suSg n * suSg n = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, suSg_coe, J3_mul_self,
    Matrix.GeneralLinearGroup.coe_one]

/-- The "opposite" root element `S·u(b,c)·S`, whose first column is `(1, b^q, c)`. -/
noncomputable def suUinvg (n : ℕ) (b c : F n) : GL (Fin 3) (F n) :=
  suSg n * suUg n b c * suSg n

/-- The matrix `S·u(b,c)·S = !![1,0,0; b^q,1,0; c,b,1]`. -/
lemma suUinvg_coe (n : ℕ) (b c : F n) :
    ((suUinvg n b c : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) =
      !![1, 0, 0; b ^ (2 ^ n), 1, 0; c, b, 1] := by
  rw [suUinvg, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    suSg_coe, suUg_coe, J3, suUmat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

lemma suUinvg_mem_SU3 (n : ℕ) (b c : F n) (hc : c + c ^ (2 ^ n) = b ^ (2 ^ n + 1)) :
    suUinvg n b c ∈ SU3 n := by
  have h1 := suSg_mem_SU3 n
  have h2 : suUg n b c ∈ SU3 n := suUg_isSU3 n b c hc
  exact (SU3 n).mul_mem ((SU3 n).mul_mem h1 h2) h1

/-- The first column of `S·u(b,c)·S`. -/
lemma suUinvg_first (n : ℕ) (b c : F n) (i : Fin 3) :
    (((suUinvg n b c : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) i 0) =
      ![(1 : F n), b ^ (2 ^ n), c] i := by
  rw [suUinvg_coe]
  fin_cases i <;> simp

/-! ## First columns of the standard elements -/

/-- The first basis vector `e_0 = (1,0,0)`. -/
noncomputable def suE0 (n : ℕ) : Fin 3 → F n := ![1, 0, 0]

lemma suTg_first (n : ℕ) (a : (F n)ˣ) (i : Fin 3) :
    (((suTg n a : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) i 0) =
      ![(↑a : F n), 0, 0] i := by
  rw [suTg_coe, suTmat]
  fin_cases i <;> simp [Matrix.diagonal_apply]

lemma suUg_first (n : ℕ) (b c : F n) (i : Fin 3) :
    (((suUg n b c : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) i 0) =
      ![(1 : F n), 0, 0] i := by
  rw [suUg_coe]
  fin_cases i <;> simp [suUmat]

/-- Applying a matrix whose first column is `v` to `e_0` gives `v`. -/
lemma mulVec_suE0 (n : ℕ) (M : Matrix (Fin 3) (Fin 3) (F n)) (i : Fin 3) :
    (M *ᵥ suE0 n) i = M i 0 := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  simp [suE0]

/-! ## Isotropic vectors and transitivity of the action -/

/-- A vector is isotropic for the Hermitian form `J`:  `v_0^q v_2 + v_1^(q+1) + v_2^q v_0 = 0`. -/
def IsIsoVec (n : ℕ) (v : Fin 3 → F n) : Prop :=
  v 0 ^ (2 ^ n) * v 2 + v 1 ^ (2 ^ n + 1) + v 2 ^ (2 ^ n) * v 0 = 0

/-- The relation `c + c^q = (v_1/v_0)^(q+1)` for `c = v_2/v_0` when `v` is isotropic. -/
lemma iso_div (n : ℕ) (v : Fin 3 → F n) (hv : IsIsoVec n v) (h0 : v 0 ≠ 0) :
    (v 2 / v 0) + (v 2 / v 0) ^ (2 ^ n) = (v 1 / v 0) ^ (2 ^ n + 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv0ne : (v 0 : F n) ≠ 0 := h0
  have hmain : v 2 * v 0 ^ (2 ^ n) + v 2 ^ (2 ^ n) * v 0 = v 1 ^ (2 ^ n + 1) := by
    have h := hv
    rw [IsIsoVec] at h
    refine CharTwo.add_eq_zero.mp ?_
    rw [show v 2 * v 0 ^ (2 ^ n) + v 2 ^ (2 ^ n) * v 0 + v 1 ^ (2 ^ n + 1)
        = v 0 ^ (2 ^ n) * v 2 + v 1 ^ (2 ^ n + 1) + v 2 ^ (2 ^ n) * v 0 by ring]
    exact h
  simp only [div_pow]
  rw [div_add_div _ _ hv0ne (pow_ne_zero _ hv0ne)]
  rw [← pow_succ' (v 0) (2 ^ n)]
  rw [mul_comm (v 0) (v 2 ^ (2 ^ n))]
  rw [hmain]

lemma suTg_mulVec_suE0 (n : ℕ) (a : (F n)ˣ) :
    ((suTg n a : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n =
      ![(↑a : F n), 0, 0] := by
  rw [suTg_coe, suTmat]
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, suE0, Matrix.diagonal_apply]

lemma suUinvg_mulVec_suE0 (n : ℕ) (b c : F n) :
    ((suUinvg n b c : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n =
      ![(1 : F n), b ^ (2 ^ n), c] := by
  rw [suUinvg_coe]
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, suE0]

lemma vec3_eq_smul_suE0 (n : ℕ) (a : F n) : ![a, 0, 0] = a • suE0 n := by
  ext i
  fin_cases i <;> simp [suE0, Pi.smul_apply]

lemma suSg_mulVec (n : ℕ) (w : Fin 3 → F n) :
    ((suSg n : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ w =
      ![w 2, w 1, w 0] := by
  rw [suSg_coe, J3]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- Every non-zero isotropic vector is the image of `e_0` under some element of `SU(3,2^n)`. -/
theorem su3_exists_mulVec_suE0_eq (n : ℕ) (v : Fin 3 → F n)
    (hv : IsIsoVec n v) (hv0 : v ≠ 0) :
    ∃ A ∈ SU3 n,
      ((A : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n = v := by
  rcases eq_or_ne (v 0) 0 with h0 | h0
  · -- `v_0 = 0`: then `v = (0,0,v_2)` with `v_2 ≠ 0`
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : v 1 = 0 := by
      have h := hv
      rw [IsIsoVec, h0] at h
      simpa using h
    have h2 : v 2 ≠ 0 := by
      intro hz
      exact hv0 (funext fun i => by fin_cases i <;> simp [h0, h1, hz])
    refine ⟨suSg n * suTg n (Units.mk0 (v 2) h2), ?_, ?_⟩
    · exact (SU3 n).mul_mem (suSg_mem_SU3 n) (suTg_isSU3 n _)
    · rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, suTg_mulVec_suE0,
        suSg_mulVec]
      ext i
      fin_cases i <;> simp [suE0, h0, h1]
  · -- `v_0 ≠ 0`
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set b : F n := (v 1 / v 0) ^ (2 ^ n) with hb
    set c : F n := v 2 / v 0 with hc
    have hbq : b ^ (2 ^ n) = v 1 / v 0 := by
      rw [hb, ← pow_mul, show 2 ^ n * 2 ^ n = 2 ^ (2 * n) by rw [← pow_add]; ring, pow_card_sq]
    have hb2 : (v 1 / v 0) ^ (2 ^ n) = b := by
      rw [← hbq, ← pow_mul, show 2 ^ n * 2 ^ n = 2 ^ (2 * n) by rw [← pow_add]; ring,
        pow_card_sq]
    have hb3 : b ^ (2 ^ n + 1) = (v 1 / v 0) ^ (2 ^ n + 1) := by
      simp only [pow_succ']
      rw [hbq, hb2, mul_comm b (v 1 / v 0)]
    have hbc : c + c ^ (2 ^ n) = b ^ (2 ^ n + 1) := by
      rw [hc, iso_div n v hv h0]
      exact hb3.symm
    have hcancel : ∀ x : F n, v 0 * (x / v 0) = x := by
      intro x
      rw [div_eq_mul_inv, ← mul_assoc, mul_comm (v 0) x, mul_assoc, mul_inv_cancel₀ h0,
        mul_one]
    refine ⟨suUinvg n b c * suTg n (Units.mk0 (v 0) h0), ?_, ?_⟩
    · exact (SU3 n).mul_mem (suUinvg_mem_SU3 n b c hbc) (suTg_isSU3 n _)
    · rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, suTg_mulVec_suE0,
        vec3_eq_smul_suE0, Matrix.mulVec_smul, suUinvg_mulVec_suE0]
      ext i
      fin_cases i <;> simp [suE0, Pi.smul_apply, hbq, hc, hcancel]

/-! ## The stabiliser of `e_0` is the unipotent radical `U` -/

/-- The `(i,j)` entry of the condition `Aᴴ J A = J`. -/
lemma isSU3_entry (n : ℕ) {A : GL (Fin 3) (F n)} (hA : IsSU3 A) (i j : Fin 3) :
    (A : Matrix (Fin 3) (Fin 3) (F n)) 2 i ^ (2 ^ n) *
        (A : Matrix (Fin 3) (Fin 3) (F n)) 0 j +
      (A : Matrix (Fin 3) (Fin 3) (F n)) 1 i ^ (2 ^ n) *
        (A : Matrix (Fin 3) (Fin 3) (F n)) 1 j +
      (A : Matrix (Fin 3) (Fin 3) (F n)) 0 i ^ (2 ^ n) *
        (A : Matrix (Fin 3) (Fin 3) (F n)) 2 j = J3 i j := by
  have h := congrFun (congrFun hA.1 i) j
  simpa [herm, J3, Matrix.mul_apply, Fin.sum_univ_three] using h

lemma suUmat_mulVec_suE0 (n : ℕ) (b c : F n) : suUmat n b c *ᵥ suE0 n = suE0 n := by
  rw [suUmat]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, suE0]

/-- `x ^ (2^n) = 0` implies `x = 0`. -/
lemma pow_two_pow_eq_zero {n : ℕ} {x : F n} (h : x ^ (2 ^ n) = 0) : x = 0 := by
  by_contra hx
  exact absurd h (pow_ne_zero _ hx)

/-- `x ^ (2^n) = 1` implies `x = 1`. -/
lemma pow_two_pow_eq_one {n : ℕ} {x : F n} (h : x ^ (2 ^ n) = 1) : x = 1 := by
  have hx : x = (x ^ (2 ^ n)) ^ (2 ^ n) := by
    rw [← pow_mul, show 2 ^ n * 2 ^ n = 2 ^ (2 * n) by rw [← pow_add]; ring, pow_card_sq]
  rw [hx, h, one_pow]

/-- A matrix of `SU(3,2^n)` fixing `e_0` has first column `(1,0,0)`, hence lies in `U`. -/
lemma mem_suU_of_isSU3_mulVec_suE0 (n : ℕ) (A : GL (Fin 3) (F n))
    (hA : IsSU3 A) (h : (A : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n = suE0 n) :
    A ∈ suU n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzp : (0 : F n) ^ (2 ^ n) = 0 := zero_pow (pow_ne_zero _ (by norm_num))
  have hop : (1 : F n) ^ (2 ^ n) = 1 := one_pow _
  have hcol : ∀ i, (A : Matrix (Fin 3) (Fin 3) (F n)) i 0 = suE0 n i := by
    intro i
    rw [← mulVec_suE0 n A i]
    exact congrFun h i
  have h00 : (A : Matrix (Fin 3) (Fin 3) (F n)) 0 0 = 1 := by simpa [suE0] using hcol 0
  have h10 : (A : Matrix (Fin 3) (Fin 3) (F n)) 1 0 = 0 := by simpa [suE0] using hcol 1
  have h20 : (A : Matrix (Fin 3) (Fin 3) (F n)) 2 0 = 0 := by simpa [suE0] using hcol 2
  have h21 : (A : Matrix (Fin 3) (Fin 3) (F n)) 2 1 = 0 := by
    have e := isSU3_entry n hA 1 0
    rw [J3] at e
    simp only [h00, h10, h20, hzp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply, mul_one, one_mul, mul_zero, zero_mul,
      add_zero, zero_add] at e
    exact pow_two_pow_eq_zero e
  have h22 : (A : Matrix (Fin 3) (Fin 3) (F n)) 2 2 = 1 := by
    have e := isSU3_entry n hA 0 2
    rw [J3] at e
    simp only [h00, h10, h20, hzp, hop, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply, mul_one, one_mul,
      mul_zero, zero_mul, add_zero, zero_add] at e
    exact e
  have h11 : (A : Matrix (Fin 3) (Fin 3) (F n)) 1 1 = 1 := by
    have hdet : (A : Matrix (Fin 3) (Fin 3) (F n)).det = 1 := by
      have hh := congrArg (fun u : (F n)ˣ => (u : F n)) hA.2
      simpa using hh
    rw [Matrix.det_fin_three] at hdet
    rw [h00, h10, h20, h21, h22] at hdet
    simpa using hdet
  have h12 : (A : Matrix (Fin 3) (Fin 3) (F n)) 1 2 =
      (A : Matrix (Fin 3) (Fin 3) (F n)) 0 1 ^ (2 ^ n) := by
    have e := isSU3_entry n hA 1 2
    rw [J3] at e
    simp only [h11, h21, h22, hzp, hop, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply, mul_one, one_mul,
      mul_zero, zero_mul, add_zero, zero_add] at e
    exact CharTwo.add_eq_zero.mp e
  have hcond : (A : Matrix (Fin 3) (Fin 3) (F n)) 0 2 +
      (A : Matrix (Fin 3) (Fin 3) (F n)) 0 2 ^ (2 ^ n) =
      (A : Matrix (Fin 3) (Fin 3) (F n)) 0 1 ^ (2 ^ n + 1) := by
    have e := isSU3_entry n hA 2 2
    rw [J3] at e
    simp only [h12, h21, h22, hzp, hop, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply, mul_one, one_mul,
      mul_zero, zero_mul, add_zero, zero_add] at e
    rw [← pow_mul, show 2 ^ n * 2 ^ n = 2 ^ (2 * n) by rw [← pow_add]; ring,
      pow_card_sq, ← pow_succ'] at e
    refine CharTwo.add_eq_zero.mp ?_
    rw [show (A : Matrix (Fin 3) (Fin 3) (F n)) 0 2 +
        (A : Matrix (Fin 3) (Fin 3) (F n)) 0 2 ^ (2 ^ n) +
        (A : Matrix (Fin 3) (Fin 3) (F n)) 0 1 ^ (2 ^ n + 1) =
        (A : Matrix (Fin 3) (Fin 3) (F n)) 0 2 +
        (A : Matrix (Fin 3) (Fin 3) (F n)) 0 1 ^ (2 ^ n + 1) +
        (A : Matrix (Fin 3) (Fin 3) (F n)) 0 2 ^ (2 ^ n) by ring]
    exact e
  have hmat : (A : Matrix (Fin 3) (Fin 3) (F n)) =
      suUmat n ((A : Matrix (Fin 3) (Fin 3) (F n)) 0 1)
        ((A : Matrix (Fin 3) (Fin 3) (F n)) 0 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [suUmat, h00, h10, h20, h21, h22, h11, h12]
  exact ⟨(A : Matrix (Fin 3) (Fin 3) (F n)) 0 1, (A : Matrix (Fin 3) (Fin 3) (F n)) 0 2,
    hcond, by apply Units.ext; rw [suUg_coe]; exact hmat⟩

/-- The stabiliser of `e_0` in `SU(3,2^n)` is exactly the unipotent radical `U`. -/
lemma mulVec_suE0_iff_mem_suU (n : ℕ) (A : GL (Fin 3) (F n)) (hA : A ∈ SU3 n) :
    (A : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n = suE0 n ↔ A ∈ suU n := by
  refine ⟨fun h => mem_suU_of_isSU3_mulVec_suE0 n A hA h, fun h => ?_⟩
  obtain ⟨b, c, hc, rfl⟩ := h
  rw [suUg_coe]
  exact suUmat_mulVec_suE0 n b c

/-! ## Counting the non-zero isotropic vectors -/

/-- Scaling a vector by `a` multiplies `J(v,v)` by `a^(q+1)`. -/
lemma isIsoVec_smul (n : ℕ) (v : Fin 3 → F n) (a : F n) (hv : IsIsoVec n v) :
    IsIsoVec n (a • v) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv' : v 0 ^ (2 ^ n) * v 2 + v 1 ^ (2 ^ n) * v 1 + v 2 ^ (2 ^ n) * v 0 = 0 := by
    rw [← pow_succ (v 1) (2 ^ n)]
    exact hv
  simp only [IsIsoVec, Pi.smul_apply, smul_eq_mul, mul_pow, pow_succ]
  rw [show a ^ (2 ^ n) * v 0 ^ (2 ^ n) * (a * v 2) +
        a ^ (2 ^ n) * v 1 ^ (2 ^ n) * (a * v 1) +
        a ^ (2 ^ n) * v 2 ^ (2 ^ n) * (a * v 0) =
      (a ^ (2 ^ n) * a) *
        (v 0 ^ (2 ^ n) * v 2 + v 1 ^ (2 ^ n) * v 1 + v 2 ^ (2 ^ n) * v 0) by ring]
  rw [hv', mul_zero]

lemma isIsoVec_smul_iff (n : ℕ) (v : Fin 3 → F n) {a : F n} (ha : a ≠ 0) :
    IsIsoVec n (a • v) ↔ IsIsoVec n v := by
  refine ⟨fun h => ?_, isIsoVec_smul n v a⟩
  have h' := isIsoVec_smul n (a • v) a⁻¹ h
  rwa [inv_smul_smul₀ ha v] at h'

lemma zero_pow_two (n : ℕ) : (0 : F n) ^ (2 ^ n) = 0 :=
  zero_pow (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))

lemma zero_pow_two_add_one (n : ℕ) : (0 : F n) ^ (2 ^ n + 1) = 0 :=
  zero_pow (by positivity)

lemma isIsoVec_apply_zero_left (n : ℕ) (v : Fin 3 → F n) (hv : IsIsoVec n v)
    (h0 : v 0 = 0) : v 1 = 0 := by
  have h2 : v 1 ^ (2 ^ n + 1) = 0 := by
    have h := hv
    rw [IsIsoVec, h0] at h
    simpa [zero_pow_two, zero_mul, add_zero] using h
  by_contra h1
  exact absurd h2 (pow_ne_zero _ h1)

/-- Non-zero isotropic vectors. -/
abbrev suIsoX (n : ℕ) : Type := {v : Fin 3 → F n // IsIsoVec n v ∧ v ≠ 0}

/-- Non-zero isotropic vectors with `v 0 = 0`. -/
abbrev suIsoX0 (n : ℕ) : Type := {v : Fin 3 → F n // IsIsoVec n v ∧ v ≠ 0 ∧ v 0 = 0}

/-- Non-zero isotropic vectors with `v 0 ≠ 0`. -/
abbrev suIsoX1 (n : ℕ) : Type := {v : Fin 3 → F n // IsIsoVec n v ∧ v ≠ 0 ∧ v 0 ≠ 0}

/-- Isotropic vectors with `w 0 = 1`. -/
abbrev suIsoB (n : ℕ) : Type := {w : Fin 3 → F n // w 0 = 1 ∧ IsIsoVec n w}

/-- The bijection `X_0 ≃ (F^×)`, `v ↦ v_2`. -/
noncomputable def suIsoX0Equiv (n : ℕ) : suIsoX0 n ≃ (F n)ˣ where
  toFun v := Units.mk0 (v.1 2) (by
    have h1 : v.1 1 = 0 := isIsoVec_apply_zero_left n v.1 v.2.1 v.2.2.2
    intro h2
    exact v.2.2.1 (funext fun i => by fin_cases i <;> simp [v.2.2.2, h1, h2]))
  invFun u := ⟨fun i => ![0, 0, (u : F n)] i, by
    refine ⟨?_, ?_, ?_⟩
    · rw [IsIsoVec]
      simp [zero_pow_two, zero_mul, add_zero]
    · intro h
      have hh := congrFun h 2
      simp only [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply]
        at hh
      exact Units.ne_zero u hh
    · simp⟩
  left_inv v := by
    have h1 : v.1 1 = 0 := isIsoVec_apply_zero_left n v.1 v.2.1 v.2.2.2
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [h1, v.2.2.2]
  right_inv u := by
    apply Units.ext
    simp

/-- The bijection `B ≃ F × GF(q)`, `w ↦ (w_1, w_2 + c(w_1))`. -/
noncomputable def suIsoBEquiv (n : ℕ) (hn : 1 ≤ n) :
    suIsoB n ≃ F n × {k : F n // k ^ (2 ^ n) = k} where
  toFun w := (w.1 1, ⟨w.1 2 + suCb n hn (w.1 1), by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hw : w.1 2 + w.1 2 ^ (2 ^ n) = w.1 1 ^ (2 ^ n + 1) := by
      have h := w.2.2
      rw [IsIsoVec, w.2.1] at h
      simp only [one_pow, one_mul, mul_one] at h
      refine CharTwo.add_eq_zero.mp ?_
      rw [show (w.1 2 + w.1 2 ^ (2 ^ n)) + w.1 1 ^ (2 ^ n + 1)
          = w.1 2 + w.1 1 ^ (2 ^ n + 1) + w.1 2 ^ (2 ^ n) by ring]
      exact h
    have e1 : w.1 2 ^ (2 ^ n) = w.1 2 + w.1 1 ^ (2 ^ n + 1) := by
      rw [← hw]
      rw [show w.1 2 + (w.1 2 + w.1 2 ^ (2 ^ n)) =
        (w.1 2 + w.1 2) + w.1 2 ^ (2 ^ n) by ring, CharTwo.add_self_eq_zero, zero_add]
    have e2 : suCb n hn (w.1 1) ^ (2 ^ n) = suCb n hn (w.1 1) + w.1 1 ^ (2 ^ n + 1) := by
      rw [← suCb_spec n hn (w.1 1)]
      rw [show suCb n hn (w.1 1) + (suCb n hn (w.1 1) + suCb n hn (w.1 1) ^ (2 ^ n)) =
        (suCb n hn (w.1 1) + suCb n hn (w.1 1)) + suCb n hn (w.1 1) ^ (2 ^ n) by ring,
        CharTwo.add_self_eq_zero, zero_add]
    rw [add_pow_char_pow, e1, e2]
    rw [show (w.1 2 + w.1 1 ^ (2 ^ n + 1)) + (suCb n hn (w.1 1) + w.1 1 ^ (2 ^ n + 1)) =
        (w.1 2 + suCb n hn (w.1 1)) + (w.1 1 ^ (2 ^ n + 1) + w.1 1 ^ (2 ^ n + 1)) by ring,
      CharTwo.add_self_eq_zero, add_zero]⟩)
  invFun p := ⟨fun i => ![1, p.1, suCb n hn p.1 + p.2.1] i, by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨?_, ?_⟩
    · simp
    · rw [IsIsoVec]
      have h1 : (1 : F n) ^ (2 ^ n) = 1 := one_pow _
      have h2 : (suCb n hn p.1 + p.2.1) + (suCb n hn p.1 + p.2.1) ^ (2 ^ n)
          = p.1 ^ (2 ^ n + 1) := by
        rw [add_pow_char_pow]
        rw [show suCb n hn p.1 + ↑p.2 + (suCb n hn p.1 ^ (2 ^ n) + ↑p.2 ^ (2 ^ n)) =
            (suCb n hn p.1 + suCb n hn p.1 ^ (2 ^ n)) + (↑p.2 + ↑p.2 ^ (2 ^ n)) by ring]
        rw [suCb_spec n hn p.1, p.2.2, CharTwo.add_self_eq_zero, add_zero]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons, h1, one_mul, mul_one]
      rw [show (suCb n hn p.1 + ↑p.2) + p.1 ^ (2 ^ n + 1) +
          (suCb n hn p.1 + ↑p.2) ^ (2 ^ n) =
        ((suCb n hn p.1 + ↑p.2) + (suCb n hn p.1 + ↑p.2) ^ (2 ^ n)) +
          p.1 ^ (2 ^ n + 1) by ring]
      rw [h2, CharTwo.add_self_eq_zero]⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp
    · exact w.2.1.symm
    · rw [show suCb n hn (w.1 1) + (w.1 2 + suCb n hn (w.1 1)) =
          (suCb n hn (w.1 1) + suCb n hn (w.1 1)) + w.1 2 by ring,
        CharTwo.add_self_eq_zero, zero_add]
  right_inv p := by
    refine Prod.ext rfl (Subtype.ext ?_)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    rw [show suCb n hn p.1 + ↑p.2 + suCb n hn p.1 =
        (suCb n hn p.1 + suCb n hn p.1) + ↑p.2 by ring,
      CharTwo.add_self_eq_zero, zero_add]

/-- The bijection `X_1 ≃ F^× × B`, `v ↦ (v_0, v/v_0)`. -/
noncomputable def suIsoX1Equiv (n : ℕ) : suIsoX1 n ≃ (F n)ˣ × suIsoB n where
  toFun v := (Units.mk0 (v.1 0) v.2.2.2, ⟨(v.1 0)⁻¹ • v.1, by
    refine ⟨?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact inv_mul_cancel₀ v.2.2.2
    · exact (isIsoVec_smul_iff n v.1 (inv_ne_zero v.2.2.2)).mpr v.2.1⟩)
  invFun p := ⟨(p.1 : F n) • p.2.1, by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨isIsoVec_smul n p.2.1 (p.1 : F n) p.2.2.2, ?_, ?_⟩
    · intro h
      have hh := congrFun h 0
      simp only [Pi.smul_apply, p.2.2.1, smul_eq_mul, mul_one, Pi.zero_apply] at hh
      exact Units.ne_zero p.1 hh
    · simp only [Pi.smul_apply, p.2.2.1, smul_eq_mul, mul_one]
      exact Units.ne_zero p.1⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    simp only [Pi.smul_apply, Units.val_mk0, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ v.2.2.2, one_mul]
  right_inv p := by
    refine Prod.ext (Units.ext ?_) (Subtype.ext ?_)
    · simp only [Pi.smul_apply, p.2.2.1, smul_eq_mul, mul_one, Units.val_mk0,
        mul_inv_cancel₀ (Units.ne_zero p.1)]
    · funext i
      simp only [Pi.smul_apply, Units.val_mk0, p.2.2.1, smul_eq_mul, mul_one]
      rw [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero p.1), one_mul]

/-- The sum decomposition `X_0 ⊕ X_1 ≃ X`. -/
noncomputable def suIsoSplit (n : ℕ) : suIsoX0 n ⊕ suIsoX1 n ≃ suIsoX n where
  toFun v := Sum.elim (fun w => ⟨w.1, w.2.1, w.2.2.1⟩) (fun w => ⟨w.1, w.2.1, w.2.2.1⟩) v
  invFun v := by
    classical
    exact if h : v.1 0 = 0 then Sum.inl ⟨v.1, v.2.1, v.2.2, h⟩
      else Sum.inr ⟨v.1, v.2.1, v.2.2, h⟩
  left_inv v := by
    rcases v with (w | w)
    · exact dif_pos w.2.2.2
    · exact dif_neg w.2.2.2
  right_inv v := by
    dsimp only
    split <;> rfl

/-- `|X| = (q^3+1)(q^2-1)`. -/
theorem card_suIsoX (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (suIsoX n) = (2 ^ (3 * n) + 1) * (2 ^ (2 * n) - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Nat.card (F n) = 2 ^ (2 * n) := GaloisField.card 2 (2 * n) (by omega)
  have hcardU : Nat.card (F n)ˣ = 2 ^ (2 * n) - 1 := by rw [Nat.card_units, hq]
  have hcardFix : Nat.card {k : F n // k ^ (2 ^ n) = k} = 2 ^ n :=
    Commons.FieldTheory.Finite.fixed_card_pow_two n (by omega)
  have hsplit : Nat.card (suIsoX n) = Nat.card (suIsoX0 n) + Nat.card (suIsoX1 n) := by
    rw [← Nat.card_congr (suIsoSplit n), Nat.card_sum]
  have h0 : Nat.card (suIsoX0 n) = 2 ^ (2 * n) - 1 := by
    rw [Nat.card_congr (suIsoX0Equiv n), hcardU]
  have hB : Nat.card (suIsoB n) = 2 ^ (3 * n) := by
    rw [Nat.card_congr (suIsoBEquiv n hn), Nat.card_prod, hq, hcardFix, ← pow_add]
    congr 1
    ring
  have h1 : Nat.card (suIsoX1 n) = (2 ^ (2 * n) - 1) * 2 ^ (3 * n) := by
    rw [Nat.card_congr (suIsoX1Equiv n), Nat.card_prod, hcardU, hB]
  set A : ℕ := 2 ^ (2 * n) - 1 with hA
  rw [hsplit, h0, h1]
  show A + A * 2 ^ (3 * n) = (2 ^ (3 * n) + 1) * A
  ring

/-! ## The order of `SU(3,2^n)` -/

/-- `A·e_0` is isotropic for `A ∈ SU(3,2^n)`. -/
lemma isIsoVec_mulVec_suE0 (n : ℕ) (A : GL (Fin 3) (F n)) (hA : IsSU3 A) :
    IsIsoVec n ((A : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show (A : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n =
      fun i => (A : Matrix (Fin 3) (Fin 3) (F n)) i 0 from funext (mulVec_suE0 n A)]
  have h := isSU3_entry n hA 0 0
  rw [J3] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.of_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one] at h
  rw [IsIsoVec, pow_succ]
  rw [show (A : Matrix (Fin 3) (Fin 3) (F n)) 0 0 ^ (2 ^ n) *
        (A : Matrix (Fin 3) (Fin 3) (F n)) 2 0 +
        (A : Matrix (Fin 3) (Fin 3) (F n)) 1 0 ^ (2 ^ n) *
          (A : Matrix (Fin 3) (Fin 3) (F n)) 1 0 +
        (A : Matrix (Fin 3) (Fin 3) (F n)) 2 0 ^ (2 ^ n) *
          (A : Matrix (Fin 3) (Fin 3) (F n)) 0 0 =
      (A : Matrix (Fin 3) (Fin 3) (F n)) 2 0 ^ (2 ^ n) *
          (A : Matrix (Fin 3) (Fin 3) (F n)) 0 0 +
        (A : Matrix (Fin 3) (Fin 3) (F n)) 1 0 ^ (2 ^ n) *
          (A : Matrix (Fin 3) (Fin 3) (F n)) 1 0 +
        (A : Matrix (Fin 3) (Fin 3) (F n)) 0 0 ^ (2 ^ n) *
          (A : Matrix (Fin 3) (Fin 3) (F n)) 2 0 by ring]
  exact h

/-- `A·e_0 ≠ 0` for `A ∈ SU(3,2^n)` and `n ≥ 1`. -/
lemma ne_zero_mulVec_suE0 (n : ℕ) (_hn : 1 ≤ n) (A : GL (Fin 3) (F n)) (_hA : IsSU3 A) :
    (A : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n ≠ 0 := by
  intro h
  have h2 : (A⁻¹ : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ
      ((A : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n) = suE0 n := by
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_inv,
      ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one,
      Matrix.one_mulVec]
  rw [h, Matrix.mulVec_zero] at h2
  have h3 : (0 : F n) = 1 := by simpa [suE0] using congrFun h2 0
  exact one_ne_zero h3.symm

/-- An element of `SU(3,2^n)` whose first column is the isotropic vector `v`. -/
noncomputable def su3Pre (n : ℕ) (v : suIsoX n) : ↥(SU3 n) :=
  ⟨Classical.choose (su3_exists_mulVec_suE0_eq n v.1 v.2.1 v.2.2),
    (Classical.choose_spec (su3_exists_mulVec_suE0_eq n v.1 v.2.1 v.2.2)).1⟩

lemma su3Pre_spec (n : ℕ) (v : suIsoX n) :
    (((su3Pre n v).1 : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n = v.1 :=
  (Classical.choose_spec (su3_exists_mulVec_suE0_eq n v.1 v.2.1 v.2.2)).2

lemma suU_mulVec_suE0 (n : ℕ) (u : ↥(suU n)) :
    ((u.1 : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n = suE0 n := by
  obtain ⟨b, c, hc, hu⟩ := u.2
  rw [hu, suUg_coe]
  exact suUmat_mulVec_suE0 n b c

/-- The value of the bijection `X × U ≃ SU(3,2^n)`. -/
noncomputable def su3Mul (n : ℕ) (v : suIsoX n) (u : ↥(suU n)) : ↥(SU3 n) :=
  ⟨(su3Pre n v).1 * u.1, (SU3 n).mul_mem (su3Pre n v).2 ((suU_le_SU3 n) u.2)⟩

/-- `SU(3,2^n)` is in bijection with `X × U`. -/
noncomputable def su3Equiv (n : ℕ) (hn : 1 ≤ n) : suIsoX n × ↥(suU n) ≃ ↥(SU3 n) :=
  Equiv.ofBijective (fun p : suIsoX n × ↥(suU n) => su3Mul n p.1 p.2) ⟨by
    rintro ⟨v, u⟩ ⟨w, u'⟩ h
    have h' : (su3Mul n v u).1 = (su3Mul n w u').1 := congrArg Subtype.val h
    have hcol : (((su3Pre n v).1 : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ
        suE0 n = ((su3Pre n w).1 : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n := by
      have h2 := congrArg (fun x : GL (Fin 3) (F n) =>
        ((x : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n)) h'
      simp only [su3Mul] at h2
      rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, suU_mulVec_suE0 n u,
        Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, suU_mulVec_suE0 n u'] at h2
      exact h2
    rw [su3Pre_spec n v, su3Pre_spec n w] at hcol
    have hvw : v = w := Subtype.ext hcol
    subst hvw
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel h'))
  , by
    intro A
    set v : suIsoX n := ⟨(A.1 : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n,
      isIsoVec_mulVec_suE0 n A.1 A.2, ne_zero_mulVec_suE0 n hn A.1 A.2⟩ with hv
    have hsU : (su3Pre n v).1⁻¹ * A.1 ∈ suU n := by
      rw [← mulVec_suE0_iff_mem_suU n _
        ((SU3 n).mul_mem ((SU3 n).inv_mem (su3Pre n v).2) A.2)]
      rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
        show (A.1 : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n =
          v.1 from rfl, ← su3Pre_spec n v, Matrix.mulVec_mulVec]
      show (((su3Pre n v).1⁻¹ * (su3Pre n v).1 : GL (Fin 3) (F n)) :
        Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n = suE0 n
      rw [inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    refine ⟨(v, ⟨(su3Pre n v).1⁻¹ * A.1, hsU⟩), ?_⟩
    apply Subtype.ext
    show (su3Pre n v).1 * ((su3Pre n v).1⁻¹ * A.1) = A.1
    rw [← mul_assoc, mul_inv_cancel, one_mul]⟩

/-- The order of `SU(3,2^n)`: `q^3 (q^2-1) (q^3+1)` with `q = 2^n`. -/
theorem card_SU3 (n : ℕ) (hn : 1 ≤ n) :
    Nat.card ↥(SU3 n) = 2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1) := by
  set A : ℕ := 2 ^ (2 * n) - 1 with hAdef
  set B : ℕ := 2 ^ (3 * n) with hBdef
  rw [← Nat.card_congr (su3Equiv n hn), Nat.card_prod, card_suIsoX n hn, card_suU n hn]
  show (B + 1) * A * B = B * A * (B + 1)
  ring

/-- The index of the Borel subgroup in `SU(3,2^n)` is `q^3 + 1`, the number of isotropic
points of the Hermitian curve -- the coset space `SU(3,2^n)/B` is the Hermitian curve. -/
theorem card_suB_mul_index (n : ℕ) (hn : 1 ≤ n) :
    Nat.card ↥(suB n) * (2 ^ (3 * n) + 1) = Nat.card ↥(SU3 n) := by
  rw [card_suB n hn, card_SU3 n hn]

end Submission.PSU3
