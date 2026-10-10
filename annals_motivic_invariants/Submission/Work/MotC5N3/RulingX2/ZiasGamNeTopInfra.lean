import Submission.Work.MotC5N3.RulingX2.SlicePhi
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace Work.MotC5N3.RulingX2

open MvPolynomial

variable {K : Type} [Field K] [CharP K 5]

/-- The collapse `X 0 ↦ 0`, `X 1 ↦ X`: extracts the `K[X 1]`-part of a polynomial that does not
involve `X 0`. -/
noncomputable def toK : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval (fun i => if i = 0 then 0 else Polynomial.X)

/-- The chart isomorphism `X 0 ↦ X`, `X 1 ↦ C X` from `K[X 0, X 1]` onto `(K[X])[X]`. -/
noncomputable def ev : MvPolynomial (Fin 2) K →ₐ[K] Polynomial (Polynomial K) :=
  MvPolynomial.aeval (fun i => if i = 0 then Polynomial.X else Polynomial.C Polynomial.X)

lemma ev_X0 : ev (X 0 : MvPolynomial (Fin 2) K) = Polynomial.X := by
  simp [ev, MvPolynomial.aeval_X]

lemma ev_X1 : ev (X 1 : MvPolynomial (Fin 2) K) = Polynomial.C Polynomial.X := by
  simp [ev, MvPolynomial.aeval_X]

lemma toK_X1 : toK (X 1 : MvPolynomial (Fin 2) K) = Polynomial.X := by
  simp [toK, MvPolynomial.aeval_X]

lemma ev_C (c : K) : ev (C c) = Polynomial.C (Polynomial.C c) := by
  simp only [ev, MvPolynomial.aeval_C]
  exact (IsScalarTower.algebraMap_apply K (Polynomial K) (Polynomial (Polynomial K)) c).symm

lemma toK_C (c : K) : toK (C c) = Polynomial.C c := by
  simp only [toK, MvPolynomial.aeval_C, Polynomial.C_eq_algebraMap]

/-- `Dhat` as a one-variable polynomial. -/
noncomputable def Dr (a b g : K) : Polynomial K := toK (Slice.Dhat a b g)
/-- `Rhat` as a one-variable polynomial. -/
noncomputable def Rr (a b g : K) : Polynomial K := toK (Slice.Rhat a b g)
/-- `PhatPoly` as a one-variable polynomial. -/
noncomputable def Pr (a b g : K) : Polynomial K := toK (Slice.PhatPoly a b g)
/-- `PhiAlpha` as a one-variable polynomial. -/
noncomputable def Al (a b g : K) : Polynomial K := toK (Slice.PhiAlpha a b g)
/-- `PhiBeta` as a one-variable polynomial. -/
noncomputable def Be (a b g : K) : Polynomial K := toK (Slice.PhiBeta a b g)

/-- The norm `Rr ^ 2 - Al * Rr * Dr + Be * Dr ^ 2` of `Gam` in `K[X]`. -/
noncomputable def nrm (a b g : K) : Polynomial K :=
  Rr a b g ^ 2 - Al a b g * Rr a b g * Dr a b g + Be a b g * Dr a b g ^ 2

/-- The `K[X 0, X 1]`-version of the same norm. -/
noncomputable def nrmMv (a b g : K) : MvPolynomial (Fin 2) K :=
  Slice.Rhat a b g ^ 2 - Slice.PhiAlpha a b g * Slice.Rhat a b g * Slice.Dhat a b g
    + Slice.PhiBeta a b g * Slice.Dhat a b g ^ 2

lemma ev_PhiAlpha (a b g : K) :
    ev (Slice.PhiAlpha a b g) = Polynomial.C (Al a b g) := by
  simp only [Slice.PhiAlpha, Al, map_add, map_mul, map_pow, ev_C, ev_X1, toK_C, toK_X1,
    Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow]

lemma ev_PhiBeta (a b g : K) :
    ev (Slice.PhiBeta a b g) = Polynomial.C (Be a b g) := by
  simp only [Slice.PhiBeta, Be, map_add, map_mul, map_pow, ev_C, ev_X1, toK_C, toK_X1,
    Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow]

lemma ev_Dhat (a b g : K) : ev (Slice.Dhat a b g) = Polynomial.C (Dr a b g) := by
  simp only [Slice.Dhat, Dr, map_add, map_mul, map_pow, ev_C, ev_X1, toK_C, toK_X1,
    Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow]

lemma ev_Rhat (a b g : K) : ev (Slice.Rhat a b g) = Polynomial.C (Rr a b g) := by
  simp only [Slice.Rhat, Rr, map_add, map_mul, map_pow, ev_C, ev_X1, toK_C, toK_X1,
    Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow]

lemma ev_Phat (a b g : K) : ev (Slice.PhatPoly a b g) = Polynomial.C (Pr a b g) := by
  simp only [Slice.PhatPoly, Slice.Phat, Slice.Phat_p0, Slice.Phat_p1, Pr, map_add, map_mul,
    map_pow, ev_C, ev_X1, toK_C, toK_X1, Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow]

lemma ev_Phisq (a b g : K) :
    ev (Slice.Phisq a b g) = Polynomial.X ^ 2 + Polynomial.C (Al a b g) * Polynomial.X
      + Polynomial.C (Be a b g) := by
  simp only [Slice.Phisq, map_add, map_mul, map_pow, ev_X0, ev_PhiAlpha, ev_PhiBeta]

lemma ev_Gam (a b g : K) :
    ev (Slice.Gam a b g) = Polynomial.C (Dr a b g) * Polynomial.X + Polynomial.C (Rr a b g) := by
  simp only [Slice.Gam, map_add, map_mul, ev_X0, ev_Dhat, ev_Rhat]

lemma ev_nrmMv (a b g : K) : ev (nrmMv a b g) = Polynomial.C (nrm a b g) := by
  simp only [nrmMv, nrm, map_add, map_sub, map_mul, map_pow, ev_PhiAlpha, ev_PhiBeta, ev_Dhat,
    ev_Rhat, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow]

/-! ## Numeral reduction in characteristic `5` -/

/-- `n` and `n % 5` agree in any field of characteristic `5`. -/
lemma hmodK (n : ℕ) : (n : K) = ((n % 5 : ℕ) : K) := by
  conv_lhs => rw [← Nat.mod_add_div n 5]
  push_cast
  rw [show (5 : K) = 0 from CharP.cast_eq_zero K 5, zero_mul, add_zero]

/-- `n` and `n % 5` agree in `K[X 0, X 1]` when `char K = 5`. -/
lemma hmodMv (n : ℕ) : (n : MvPolynomial (Fin 2) K) = ((n % 5 : ℕ) : MvPolynomial (Fin 2) K) := by
  conv_lhs => rw [← Nat.mod_add_div n 5]
  push_cast
  rw [show (5 : MvPolynomial (Fin 2) K) = 0 from CharP.cast_eq_zero _ 5, zero_mul, add_zero]

lemma hmodMv' (n : ℕ) : (n : MvPolynomial (Fin 2) K) = ((n % 5 : ℕ) : MvPolynomial (Fin 2) K) :=
  hmodMv n

/-- The freshman's dream for the factor `2 (a - 3b)^5` appearing in `Phi`. -/
lemma denden (a b : K) : (2 : K) * (a - 3 * b) ^ 5 = 2 * a ^ 5 + 4 * b ^ 5 := by
  refl_ring1 (mod := 5)

end Work.MotC5N3.RulingX2
