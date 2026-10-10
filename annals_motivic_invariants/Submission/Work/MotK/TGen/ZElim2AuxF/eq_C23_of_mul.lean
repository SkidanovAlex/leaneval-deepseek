import Mathlib
import Submission.Work.MotK.TGen.ZElim2Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 2000000

namespace Work.MotK.TGen.ZElim2AuxF

/-!
# The cubic cofactor of a `(2,3)` factorisation of `g0p r` is `C23`

If `Q23 u · S = g0p r` for some `S`, then `S = C23 r u`.  The point is that `Q23` is monic of
`X₀`-degree `2` while `g0p r` has `X₀`-degree `5` (as `r ≠ 0`), so `S` has `X₀`-degree exactly
`3`, and the four top `X₀`-coefficients of `g0p r` pin `S` down completely; those four forced
coefficients are precisely the coefficients of `C23`.

The argument is carried out in `L[X₁][X₀]` via `MvPolynomial.finSuccEquiv L 1`.
-/

/-- `finSuccEquiv L 1` sends the constant `C a` to `C (C a)`. -/
private lemma finSucc_C {L : Type*} [CommSemiring L] (a : L) :
    MvPolynomial.finSuccEquiv L 1 (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := by
  rw [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]
  rfl

/-- `finSuccEquiv L 1` sends `X 0` to `Polynomial.X`. -/
private lemma finSucc_X0 {L : Type*} [CommSemiring L] :
    MvPolynomial.finSuccEquiv L 1 (MvPolynomial.X (0 : Fin 2)) = Polynomial.X :=
  MvPolynomial.finSuccEquiv_X_zero

/-- `finSuccEquiv L 1` sends `X 1` to the constant `C (X 0)`. -/
private lemma finSucc_X1 {L : Type*} [CommSemiring L] :
    MvPolynomial.finSuccEquiv L 1 (MvPolynomial.X (1 : Fin 2)) =
      Polynomial.C (MvPolynomial.X 0) :=
  MvPolynomial.finSuccEquiv_X_succ (n := 1) (j := (0 : Fin 1))

/-- The `(k+2)`-coefficient of `(X² + Pp·X + Qq)·w`. -/
private lemma coeff_quad {R : Type*} [CommSemiring R] (Pp Qq : R) (w : Polynomial R) (k : ℕ) :
    ((Polynomial.X ^ 2 + Polynomial.C Pp * Polynomial.X + Polynomial.C Qq) * w).coeff (k + 2)
      = w.coeff k + Pp * w.coeff (k + 1) + Qq * w.coeff (k + 2) := by
  have h2 : (Polynomial.X ^ 2 * w).coeff (k + 2) = w.coeff k := Polynomial.coeff_X_pow_mul w 2 k
  have h1 : ((Polynomial.C Pp * Polynomial.X) * w).coeff (k + 2) = Pp * w.coeff (k + 1) := by
    rw [mul_assoc, Polynomial.coeff_C_mul]
    have h := Polynomial.coeff_X_mul w (k + 1)
    rw [show k + 1 + 1 = k + 2 from rfl] at h
    rw [h]
  have h0 : (Polynomial.C Qq * w).coeff (k + 2) = Qq * w.coeff (k + 2) :=
    Polynomial.coeff_C_mul w
  rw [add_mul, add_mul, Polynomial.coeff_add, Polynomial.coeff_add, h2, h1, h0]

theorem eq_C23_of_mul {L : Type*} [Field L] (r u1 u0 v2 v1 v0 : L) (hr : r ≠ 0)
    (S : MvPolynomial (Fin 2) L)
    (h : Work.MotK.TGen.Q23 u1 u0 v2 v1 v0 * S = Work.MotK.TGen.g0p r) :
    S = Work.MotK.TGen.C23 r u1 u0 v2 v1 v0 := by
  -- abbreviations for the coefficients in `L[X₁]`
  set Y : MvPolynomial (Fin 1) L := MvPolynomial.X 0 with hY
  set p : MvPolynomial (Fin 1) L := MvPolynomial.C u1 * Y + MvPolynomial.C u0 with hp
  set q : MvPolynomial (Fin 1) L :=
    MvPolynomial.C v2 * Y ^ 2 + MvPolynomial.C v1 * Y + MvPolynomial.C v0 with hq
  set A : MvPolynomial (Fin 1) L := MvPolynomial.C (r ^ 7) with hA
  set B : MvPolynomial (Fin 1) L := MvPolynomial.C (r ^ 3 * (3 + r ^ 5)) with hB
  set D : MvPolynomial (Fin 1) L := MvPolynomial.C (1 + 2 * r ^ 5) with hD
  set E0 : MvPolynomial (Fin 1) L := MvPolynomial.C (r ^ 2) with hE0
  set w : Polynomial (MvPolynomial (Fin 1) L) := MvPolynomial.finSuccEquiv L 1 S with hw
  -- the images of `Q23`, `g0p r` and `C23` under `finSuccEquiv`
  have hQ23 : MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.Q23 u1 u0 v2 v1 v0)
      = Polynomial.X ^ 2 + Polynomial.C p * Polynomial.X + Polynomial.C q := by
    rw [Work.MotK.TGen.Q23, Work.MotK.TGen.q1p, Work.MotK.TGen.q0p, hp, hq, hY]
    simp only [map_add, map_mul, map_pow, finSucc_C, finSucc_X0, finSucc_X1,
      Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow]
  have hG : MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.g0p r)
      = Polynomial.C A * Polynomial.X ^ 5 + Polynomial.C (-(B * Y)) * Polynomial.X ^ 2
        + Polynomial.C (D * Y ^ 3) * Polynomial.X
        + Polynomial.C (E0 - E0 * Y ^ 5) := by
    rw [Work.MotK.TGen.g0p, hA, hB, hD, hE0, hY]
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_one,
      finSucc_C, finSucc_X0, finSucc_X1,
      Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg]
    first | refl_ring1 | ring
  have hC23 : MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.C23 r u1 u0 v2 v1 v0)
      = Polynomial.C A * Polynomial.X ^ 3 + Polynomial.C (-(A * p)) * Polynomial.X ^ 2
        + Polynomial.C (A * (p ^ 2 - q)) * Polynomial.X
        + Polynomial.C (-(B * Y) - A * p * (p ^ 2 - 2 * q)) := by
    rw [Work.MotK.TGen.C23, Work.MotK.TGen.q1p, Work.MotK.TGen.q0p, hA, hB, hp, hq, hY]
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_ofNat,
      finSucc_C, finSucc_X0, finSucc_X1,
      Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg,
      Polynomial.C_ofNat]
    first | refl_ring1 | ring
  -- `A` is nonzero
  have hA_ne : A ≠ 0 := by
    rw [hA]
    intro hh
    refine pow_ne_zero 7 hr ((MvPolynomial.C_injective (Fin 1) L) ?_)
    rw [hh]
    simp
  -- the `X₀`-coefficients of `e (g0p r)`
  have hg5 : (MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.g0p r)).coeff 5 = A := by
    rw [hG]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X]
    norm_num
  have hg4 : (MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.g0p r)).coeff 4 = 0 := by
    rw [hG]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X]
    norm_num
  have hg3 : (MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.g0p r)).coeff 3 = 0 := by
    rw [hG]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X]
    norm_num
  have hg2 : (MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.g0p r)).coeff 2 = -(B * Y) := by
    rw [hG]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X]
    norm_num
  -- the `X₀`-coefficients of `e (C23)`
  have hW3 : (MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.C23 r u1 u0 v2 v1 v0)).coeff 3
      = A := by
    rw [hC23]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X]
    norm_num
  have hW2 : (MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.C23 r u1 u0 v2 v1 v0)).coeff 2
      = -(A * p) := by
    rw [hC23]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X]
    norm_num
  have hW1 : (MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.C23 r u1 u0 v2 v1 v0)).coeff 1
      = A * (p ^ 2 - q) := by
    rw [hC23]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X]
    norm_num
  have hW0 : (MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.C23 r u1 u0 v2 v1 v0)).coeff 0
      = -(B * Y) - A * p * (p ^ 2 - 2 * q) := by
    rw [hC23]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X]
    norm_num
  -- the main equation in the split ring
  have hmain : MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.Q23 u1 u0 v2 v1 v0) * w
      = MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.g0p r) := by
    rw [hw, ← map_mul, h]
  have hmainX : (Polynomial.X ^ 2 + Polynomial.C p * Polynomial.X + Polynomial.C q) * w
      = MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.g0p r) := by
    rw [← hQ23]
    exact hmain
  -- degree bounds
  have hdegG_le : (MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.g0p r)).natDegree ≤ 5 := by
    rw [hG]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
        · exact Polynomial.natDegree_C_mul_X_pow_le A 5
        · exact (Polynomial.natDegree_C_mul_X_pow_le (-(B * Y)) 2).trans
            (by norm_num : (2 : ℕ) ≤ 5)
      · exact ((Polynomial.natDegree_C_mul_le (D * Y ^ 3) Polynomial.X).trans
          (le_of_eq Polynomial.natDegree_X)).trans (by norm_num : (1 : ℕ) ≤ 5)
    · rw [Polynomial.natDegree_C]; norm_num
  have hdegG : (MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.g0p r)).natDegree = 5 :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdegG_le (by rw [hg5]; exact hA_ne)
  have hG_ne : MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.g0p r) ≠ 0 := by
    intro h0
    have h1 : (MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.g0p r)).natDegree = 0 := by
      rw [h0, Polynomial.natDegree_zero]
    omega
  have hdegQ_le : (Polynomial.X ^ 2 + Polynomial.C p * Polynomial.X + Polynomial.C q).natDegree
      ≤ 2 := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact le_of_eq (Polynomial.natDegree_X_pow 2)
      · exact ((Polynomial.natDegree_C_mul_le p Polynomial.X).trans
          (le_of_eq Polynomial.natDegree_X)).trans (by norm_num : (1 : ℕ) ≤ 2)
    · rw [Polynomial.natDegree_C]; norm_num
  have hQ2 : (Polynomial.X ^ 2 + Polynomial.C p * Polynomial.X + Polynomial.C q).coeff 2 = 1 := by
    rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  have hdegQ : (MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.Q23 u1 u0 v2 v1 v0)).natDegree
      = 2 := by
    rw [hQ23]
    exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdegQ_le (by rw [hQ2]; norm_num)
  have hQ_ne : MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.Q23 u1 u0 v2 v1 v0) ≠ 0 := by
    intro h0
    have h1 : (MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.Q23 u1 u0 v2 v1 v0)).natDegree
        = 0 := by rw [h0, Polynomial.natDegree_zero]
    omega
  have hw_ne : w ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmain
    exact hG_ne hmain.symm
  have hdegw : w.natDegree = 3 := by
    have hh := Polynomial.natDegree_mul hQ_ne hw_ne
    rw [hmain, hdegG, hdegQ] at hh
    omega
  have hw4 : w.coeff 4 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdegw]; norm_num)
  have hw5 : w.coeff 5 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdegw]; norm_num)
  -- the four forced coefficients of `w`
  have hc3 : w.coeff 3 = A := by
    have hh : ((Polynomial.X ^ 2 + Polynomial.C p * Polynomial.X + Polynomial.C q) * w).coeff 5
        = (MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.g0p r)).coeff 5 := by rw [hmainX]
    rw [coeff_quad p q w 3, hw4, hw5] at hh
    rw [mul_zero, mul_zero, add_zero, add_zero, hg5] at hh
    exact hh
  have hc2 : w.coeff 2 = -(A * p) := by
    have hh : w.coeff 2 + p * A = 0 := by
      have hh' : ((Polynomial.X ^ 2 + Polynomial.C p * Polynomial.X + Polynomial.C q) * w).coeff 4
          = (MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.g0p r)).coeff 4 := by rw [hmainX]
      rw [coeff_quad p q w 2, hw4, hc3, hg4] at hh'
      rw [mul_zero, add_zero] at hh'
      exact hh'
    have hh'' : w.coeff 2 = -(p * A) := eq_neg_of_add_eq_zero_left hh
    rw [← mul_comm A p] at hh''
    exact hh''
  have hc1 : w.coeff 1 = A * (p ^ 2 - q) := by
    have hh : w.coeff 1 + p * (-(A * p)) + q * A = 0 := by
      have hh' : ((Polynomial.X ^ 2 + Polynomial.C p * Polynomial.X + Polynomial.C q) * w).coeff 3
          = (MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.g0p r)).coeff 3 := by rw [hmainX]
      rw [coeff_quad p q w 1, hc2, hc3, hg3] at hh'
      exact hh'
    linear_combination (norm := first | refl_ring1 | ring1) hh
  have hc0 : w.coeff 0 = -(B * Y) - A * p * (p ^ 2 - 2 * q) := by
    have hh : w.coeff 0 + p * (A * (p ^ 2 - q)) + q * (-(A * p)) = -(B * Y) := by
      have hh' : ((Polynomial.X ^ 2 + Polynomial.C p * Polynomial.X + Polynomial.C q) * w).coeff 2
          = (MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.g0p r)).coeff 2 := by rw [hmainX]
      rw [coeff_quad p q w 0, hc1, hc2, hg2] at hh'
      exact hh'
    linear_combination (norm := first | refl_ring1 | ring1) hh
  -- conclude
  have hdegW : (MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.C23 r u1 u0 v2 v1 v0)).natDegree
      ≤ 3 := by
    rw [hC23]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
        · exact Polynomial.natDegree_C_mul_X_pow_le A 3
        · exact (Polynomial.natDegree_C_mul_X_pow_le (-(A * p)) 2).trans
            (by norm_num : (2 : ℕ) ≤ 3)
      · exact ((Polynomial.natDegree_C_mul_le (A * (p ^ 2 - q)) Polynomial.X).trans
          (le_of_eq Polynomial.natDegree_X)).trans (by norm_num : (1 : ℕ) ≤ 3)
    · rw [Polynomial.natDegree_C]; norm_num
  have hWeq : w = MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.C23 r u1 u0 v2 v1 v0) := by
    apply Polynomial.ext
    intro n
    by_cases hn : n < 4
    · interval_cases n
      · rw [hc0, hW0]
      · rw [hc1, hW1]
      · rw [hc2, hW2]
      · rw [hc3, hW3]
    · push_neg at hn
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdegw]; omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegW (by omega))]
  have : MvPolynomial.finSuccEquiv L 1 S
      = MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.C23 r u1 u0 v2 v1 v0) := by
    rw [← hw, hWeq]
  exact (MvPolynomial.finSuccEquiv L 1).injective this

end Work.MotK.TGen.ZElim2AuxF
