/-
# Directness of `(T-I)²R + S(T-I)²R` on the odd part, transported along `psiM`

This file proves `Work.Asymptotics.oddDirect_of_psiM`: given the *shifted* directness statement
`hRR` in the free-product algebra `RR = ℂ[ℤ/2 ∗ ℤ/3]`, together with injectivity and
surjectivity (onto the odd part) of the odd component `psiM : RR → R = ℂ[SL(2,ℤ)]` of the
algebra homomorphism `psi : RR → R` of `Submission/Work/Asymptotics/psiOdd.lean`, the
directness statement

  `A z = -A → B z = -B → (T-1)²A + S(T-1)²B = 0 → A = 0 ∧ B = 0`   (`z = -I ∈ SL(2,ℤ)`)

holds in the odd part `R e₋` of `R`.

## The transport

`psiM` is additive, multiplicative and `ℂ`-linear, and it carries the two elements of `RR`
that generate the shifted theory to the two operators of the statement:

* `psiM (Tnu i) = i • ((R_T - 1) e₋)`,  so  `psiM ((Tnu i)² · x) = (-1) • ((R_T-1)² e₋ · psiM x)`
  (here `Tnu i = i`-shifted generator of the CKMRV Proposition 3.1 statement, `Tnu ν = T - ν`);
* `psiM X = i • (R_S e₋)`,  so  `psiM (X · (Tnu i)² · y) = (-i) • ((R_S (R_T-1)²) e₋ · psiM y)`.

Since `e₋` is central and idempotent and fixes the odd part pointwise, applying `psiM` to
`(Tnu i)² · (i • a) + X · (Tnu i)² · b` (where `a`, `b` are preimages of `A`, `B` under `psiM`)
produces `(-i) • ((T-1)²A + S(T-1)²B) = 0`.  Injectivity of `psiM` turns this into the
hypothesis of `hRR` at `ν = i`, which gives `i • a = 0` and `b = 0`, hence `a = b = 0` and
finally `A = B = 0`.

The extra factor `i` on `a` (rather than using `a` itself) is exactly what converts the
coefficient `1` of the `S(T-1)²` term into the coefficient `psiM X = i • (R_S e₋)`:
`i • (Tnu i)²` is the preimage of `(-i) • (T-1)²`, and `(-i)·i = 1` restores the operator
`S(T-1)²` on the second summand.
-/
import Mathlib
import Submission.Work.Asymptotics.psiOdd

namespace Work.Asymptotics

open Work.Kernels
open Work.FreeProduct (RR X Y Y2 TT Tnu x y y2)
open scoped MonoidAlgebra MatrixGroups

noncomputable section

/-! ## `psiM` and the shifted difference operator -/

/-- `psiM` is additive. -/
lemma psiM_sub (a b : RR) : psiM (a - b) = psiM a - psiM b := by
  rw [psiM, psiM, psiM, map_sub, sub_mul]

/-- `psiM 0 = 0`. -/
lemma psiM_zero : psiM (0 : RR) = 0 := by simp [psiM]

/-- `psiM (T - ν) = i • (R_T e₋) - ν • e₋`. -/
lemma psiM_Tnu (ν : ℂ) : psiM (Tnu ν) = Complex.I • (R_T * eMinus) - ν • eMinus := by
  rw [show Tnu ν = TT - ν • 1 from rfl, psiM_sub, psiM_TT, psiM_smul, psiM_one]

/-- At `ν = i` the shifted difference operator descends to `i • ((R_T - 1) e₋)`. -/
lemma psiM_Tnu_I : psiM (Tnu Complex.I) = Complex.I • ((R_T - 1) * eMinus) := by
  rw [psiM_Tnu, ← smul_sub, sub_mul, one_mul]

/-- The square `psiM ((Tnu i)²) = -((R_T - 1)² e₋)`. -/
lemma psiM_TnuI_sq : psiM (Tnu Complex.I ^ 2) = (-1 : ℂ) • ((R_T - 1) ^ 2 * eMinus) := by
  have h2 : Tnu Complex.I ^ 2 = Tnu Complex.I * Tnu Complex.I := pow_two _
  rw [h2, psiM_mul, psiM_Tnu_I, smul_mul_smul, mul_eMinus_mul,
      show (R_T - 1) * (R_T - 1) = (R_T - 1) ^ 2 from (pow_two _).symm, Complex.I_mul_I]

/-- `psiM (X · (Tnu i)²) = -i • ((R_S (R_T - 1)²) e₋)`. -/
lemma psiM_XTnuI_sq :
    psiM (X * Tnu Complex.I ^ 2) = -Complex.I • ((R_S * (R_T - 1) ^ 2) * eMinus) := by
  rw [psiM_mul, psiM_X, psiM_TnuI_sq, smul_mul_smul, mul_eMinus_mul,
      show Complex.I * -1 = -Complex.I by ring]

/-! ## The admissibility of `ν = i` for `hRR` -/

lemma I_cube_ne_one : (Complex.I : ℂ) ^ 3 ≠ 1 := by
  have h3 : (Complex.I : ℂ) ^ 3 = -Complex.I := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, Complex.I_sq]; ring
  rw [h3]; intro h; have := congrArg Complex.re h; simp at this

lemma I_cube_ne_neg_one : (Complex.I : ℂ) ^ 3 ≠ -1 := by
  have h3 : (Complex.I : ℂ) ^ 3 = -Complex.I := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, Complex.I_sq]; ring
  rw [h3]; intro h
  have hI : (Complex.I : ℂ) = 1 := by
    have := congrArg Neg.neg h; simpa using this
  have := congrArg Complex.re hI; simp at this

theorem oddDirect_of_psiM
    (hRR : ∀ {ν : ℂ}, ν ≠ 0 → ν ^ 3 ≠ 1 → ν ^ 3 ≠ -1 →
      ∀ a b : Work.FreeProduct.RR,
        Work.FreeProduct.Tnu ν ^ 2 * a + Work.FreeProduct.X * Work.FreeProduct.Tnu ν ^ 2 * b = 0 →
        a = 0 ∧ b = 0)
    (hinj : Function.Injective Work.Asymptotics.psiM)
    (hsurj : ∀ A : Work.Kernels.R, A * Work.Residues.Rneg = -A →
      ∃ a : Work.FreeProduct.RR, Work.Asymptotics.psiM a = A) :
    ∀ A B : Work.Kernels.R, A * Work.Residues.Rneg = -A → B * Work.Residues.Rneg = -B →
      (Work.Kernels.R_T - 1) ^ 2 * A + Work.Kernels.R_S * (Work.Kernels.R_T - 1) ^ 2 * B = 0 →
      A = 0 ∧ B = 0 := by
  intro A B hA hB hrel
  -- preimages of `A` and `B` in the free-product algebra
  obtain ⟨a, ha⟩ := hsurj A hA
  obtain ⟨b, hb⟩ := hsurj B hB
  -- `e₋` fixes the odd part pointwise
  have hAe : eMinus * A = A := by
    have h := (mul_Rneg_eq_neg_iff A).mp hA
    rw [eMinus_comm A]; exact h.symm
  have hBe : eMinus * B = B := by
    have h := (mul_Rneg_eq_neg_iff B).mp hB
    rw [eMinus_comm B]; exact h.symm
  -- the two summands of the transported relation
  have h1 : psiM (Tnu Complex.I ^ 2 * (Complex.I • a))
      = -Complex.I • ((R_T - 1) ^ 2 * A) := by
    rw [psiM_mul, psiM_TnuI_sq, psiM_smul, ha, smul_mul_smul,
      show (-1 : ℂ) * Complex.I = -Complex.I by ring]
    congr 1
    rw [mul_assoc, hAe]
  have h2 : psiM (X * Tnu Complex.I ^ 2 * b)
      = -Complex.I • ((R_S * (R_T - 1) ^ 2) * B) := by
    rw [show X * Tnu Complex.I ^ 2 * b = (X * Tnu Complex.I ^ 2) * b from rfl,
      psiM_mul, psiM_XTnuI_sq, hb, Algebra.smul_mul_assoc]
    congr 1
    rw [mul_assoc, hBe]
  -- hence `psiM` kills the element `(Tnu i)² · (i • a) + X · (Tnu i)² · b`
  have hu : psiM (Tnu Complex.I ^ 2 * (Complex.I • a) + X * Tnu Complex.I ^ 2 * b) = 0 := by
    rw [psiM_add, h1, h2, ← smul_add, hrel, smul_zero]
  have hu0 : Tnu Complex.I ^ 2 * (Complex.I • a) + X * Tnu Complex.I ^ 2 * b = 0 :=
    hinj (hu.trans psiM_zero.symm)
  -- the shifted directness statement at `ν = i`
  obtain ⟨hI0, hb0⟩ := hRR (ν := Complex.I) Complex.I_ne_zero I_cube_ne_one I_cube_ne_neg_one
    (Complex.I • a) b hu0
  have ha0 : a = 0 := (smul_eq_zero.mp hI0).resolve_left Complex.I_ne_zero
  constructor
  · rw [← ha, ha0]; simp [psiM]
  · rw [← hb, hb0]; simp [psiM]

end

end Work.Asymptotics
