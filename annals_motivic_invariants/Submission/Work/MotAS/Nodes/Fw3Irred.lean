import Mathlib
import Submission.Work.MotAS.Nodes.Fw3Aux
import Submission.Work.MotAS.FdivASGen3
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.Nodes.Fw3.asH_irreducible`

`asH a b g = α·X 0 + β` is linear in `X 0`, with
`α = 2A·(X 1 - X 2²) + (a² + b²)` and
`β = -A·X 1²X 2 - 3(a²+b²)·X 1X 2 + 2(a²+b²)·X 2³ - (4a²+ab-4b²)·X 2 + A·g`, `A = a² - ab - b²`.
The polynomial is irreducible for `A ≠ 0`, `g ≠ 0`: `α` is irreducible (it is linear in `X 1` with
the unit leading coefficient `2A`), `α ∤ β` (at the point `(X 0, X 1) = (-(a²+b²)/(2A), 0)` the
first factor vanishes while `β` takes the value `A·g ≠ 0`), and a linear polynomial with coprime
coefficients over a domain is irreducible.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Work.MotAS.Nodes.Fw3

open Polynomial MvPolynomial

/-! ## General lemmas -/

theorem coeff_one_C_mul_X_add_C {R : Type*} [Semiring R] (c d : R) :
    (Polynomial.C c * Polynomial.X + Polynomial.C d : Polynomial R).coeff 1 = c := by
  simp

theorem coeff_zero_C_mul_X_add_C {R : Type*} [Semiring R] (c d : R) :
    (Polynomial.C c * Polynomial.X + Polynomial.C d : Polynomial R).coeff 0 = d := by
  simp

theorem coeff_mul_C_fw {R : Type*} [CommSemiring R] (p : Polynomial R) (a : R) (n : ℕ) :
    (p * Polynomial.C a).coeff n = a * p.coeff n := by
  rw [show p * Polynomial.C a = Polynomial.C a * p from mul_comm p _,
    Polynomial.coeff_C_mul]

/-- `u * p` is irreducible when `u` is a unit and `p` is irreducible. -/
theorem irreducible_mul_unit {M : Type*} [Monoid M] {u p : M} (hu : IsUnit u)
    (hp : Irreducible p) : Irreducible (u * p) := by
  obtain ⟨v, hv⟩ := hu
  subst hv
  have hinv : (↑v⁻¹ : M) * ↑v = 1 := Units.inv_mul v
  have hmul : (↑v : M) * ↑v⁻¹ = 1 := Units.mul_inv v
  refine ⟨fun h => hp.not_isUnit ?_, fun a b hab => ?_⟩
  · have h1 : p = ↑v⁻¹ * (↑v * p) := by rw [← mul_assoc, hinv, one_mul]
    rw [h1]
    exact (Units.isUnit _).mul h
  · have h1 : p = (↑v⁻¹ * a) * b := by
      rw [show p = ↑v⁻¹ * (↑v * p) from by rw [← mul_assoc, hinv, one_mul], hab, mul_assoc]
    rcases hp.isUnit_or_isUnit h1 with h | h
    · left
      have h2 : a = ↑v * (↑v⁻¹ * a) := by rw [← mul_assoc, hmul, one_mul]
      rw [h2]
      exact (Units.isUnit _).mul h
    · exact Or.inr h

/-- A degree-one polynomial over a domain whose leading coefficient is a unit is irreducible. -/
theorem irreducible_C_mul_X_add_C_of_isUnit {R : Type*} [CommRing R] [IsDomain R] {c d : R}
    (hc : IsUnit c) : Irreducible (Polynomial.C c * Polynomial.X + Polynomial.C d) := by
  obtain ⟨v, hv⟩ := hc
  subst hv
  have h1 : (Polynomial.C (v : R) * Polynomial.X + Polynomial.C d : Polynomial R)
      = Polynomial.C (v : R) * (Polynomial.X - Polynomial.C (-(((v⁻¹ : Rˣ) : R)) * d)) := by
    rw [mul_sub, ← Polynomial.C_mul]
    rw [show (v : R) * (-(((v⁻¹ : Rˣ) : R)) * d) = -d from by
      rw [neg_mul, mul_neg, neg_inj, ← mul_assoc, Units.mul_inv, one_mul]]
    rw [map_neg]
    first | refl_ring1 | ring
  rw [h1]
  exact irreducible_mul_unit (IsUnit.map (Polynomial.C : R →+* Polynomial R) (Units.isUnit v))
    (Polynomial.irreducible_X_sub_C _)

/-- **Irreducibility of a linear polynomial with coprime coefficients** over a domain. -/
theorem irreducible_C_mul_X_add_C {R : Type*} [CommRing R] [IsDomain R] {c d : R}
    (hc : c ≠ 0) (hrel : IsRelPrime c d) :
    Irreducible (Polynomial.C c * Polynomial.X + Polynomial.C d) := by
  have hne : (Polynomial.C c * Polynomial.X + Polynomial.C d : Polynomial R) ≠ 0 := by
    intro h
    have h1 := congrArg (fun z : Polynomial R => z.coeff 1) h
    rw [coeff_one_C_mul_X_add_C, Polynomial.coeff_zero] at h1
    exact hc h1
  have hdeg : (Polynomial.C c * Polynomial.X + Polynomial.C d : Polynomial R).natDegree = 1 := by
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine Polynomial.natDegree_mul_le.trans ?_
        rw [Polynomial.natDegree_C, Polynomial.natDegree_X, zero_add]
      · rw [Polynomial.natDegree_C]; norm_num
    · rw [coeff_one_C_mul_X_add_C]; exact hc
  refine ⟨fun hu => ?_, fun p q hpq => ?_⟩
  · have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [hdeg] at h0
    exact absurd h0 (by norm_num)
  · have hp0 : p ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hpq
      exact hne hpq
    have hq0 : q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hpq
      exact hne hpq
    have hdegmul : p.natDegree + q.natDegree = 1 := by
      rw [← Polynomial.natDegree_mul hp0 hq0, ← hpq, hdeg]
    rcases Nat.eq_zero_or_pos q.natDegree with hqd | hqd
    · right
      have hqC : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero (by omega)
      have hrα : q.coeff 0 ∣ c := by
        refine ⟨p.coeff 1, ?_⟩
        have h := congrArg (fun z : Polynomial R => z.coeff 1) hpq
        rw [hqC, coeff_mul_C_fw, coeff_one_C_mul_X_add_C] at h
        exact h
      have hrβ : q.coeff 0 ∣ d := by
        refine ⟨p.coeff 0, ?_⟩
        have h := congrArg (fun z : Polynomial R => z.coeff 0) hpq
        rw [hqC, coeff_mul_C_fw, coeff_zero_C_mul_X_add_C] at h
        exact h
      rw [hqC]
      exact IsUnit.map Polynomial.C (hrel hrα hrβ)
    · left
      have hpC : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero (by omega)
      have hrα : p.coeff 0 ∣ c := by
        refine ⟨q.coeff 1, ?_⟩
        have h := congrArg (fun z : Polynomial R => z.coeff 1) hpq
        rw [hpC, Polynomial.coeff_C_mul, coeff_one_C_mul_X_add_C] at h
        exact h
      have hrβ : p.coeff 0 ∣ d := by
        refine ⟨q.coeff 0, ?_⟩
        have h := congrArg (fun z : Polynomial R => z.coeff 0) hpq
        rw [hpC, Polynomial.coeff_C_mul, coeff_zero_C_mul_X_add_C] at h
        exact h
      rw [hpC]
      exact IsUnit.map Polynomial.C (hrel hrα hrβ)

/-! ## The specific data -/

variable {K : Type*} [Field K] [CharP K 5]

/-- The image of `MvPolynomial.C r` under `finSuccEquiv`. -/
theorem finSuccEquiv_C {n : ℕ} (r : K) :
    MvPolynomial.finSuccEquiv K n (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := by
  have h := (MvPolynomial.finSuccEquiv K n).commutes r
  rw [MvPolynomial.algebraMap_eq K (Fin (n + 1))] at h
  rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K)
    (Polynomial (MvPolynomial (Fin n) K))] at h
  rw [Polynomial.algebraMap_eq, MvPolynomial.algebraMap_eq K (Fin n)] at h
  exact h

theorem finSuccEquiv_X_zero_fw :
    MvPolynomial.finSuccEquiv K 2 (MvPolynomial.X 0) = Polynomial.X :=
  MvPolynomial.finSuccEquiv_X_zero

theorem finSuccEquiv_X_one_fw :
    MvPolynomial.finSuccEquiv K 2 (MvPolynomial.X 1) = Polynomial.C (MvPolynomial.X 0) := by
  rw [show (1 : Fin 3) = Fin.succ (0 : Fin 2) from rfl, MvPolynomial.finSuccEquiv_X_succ]

theorem finSuccEquiv_X_two_fw :
    MvPolynomial.finSuccEquiv K 2 (MvPolynomial.X 2) = Polynomial.C (MvPolynomial.X 1) := by
  rw [show (2 : Fin 3) = Fin.succ (1 : Fin 2) from rfl, MvPolynomial.finSuccEquiv_X_succ]

theorem finSuccEquiv1_X_zero_fw :
    MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X 0) = Polynomial.X :=
  MvPolynomial.finSuccEquiv_X_zero

theorem finSuccEquiv1_X_one_fw :
    MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X 1) = Polynomial.C (MvPolynomial.X 0) := by
  rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl, MvPolynomial.finSuccEquiv_X_succ]

/-- `2 ≠ 0` in characteristic `5`. -/
theorem two_ne_zero_fw : (2 : K) ≠ 0 := by
  intro h
  have hd : (5 : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff K 5 2).mp h
  norm_num at hd

/-- The `X 0`-coefficient of `asH` after `finSuccEquiv K 2`. -/
noncomputable def alphaF (a b : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C (2 * asA a b) * (MvPolynomial.X 0 - MvPolynomial.X 1 ^ 2)
    + MvPolynomial.C (asB a b)

/-- The constant term of `asH` after `finSuccEquiv K 2`. -/
noncomputable def betaF (a b g : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C (-(asA a b)) * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1
    + MvPolynomial.C (-(3 * asB a b)) * MvPolynomial.X 0 * MvPolynomial.X 1
    + MvPolynomial.C (2 * asB a b) * MvPolynomial.X 1 ^ 3
    + MvPolynomial.C (-(4 * a ^ 2 + a * b - 4 * b ^ 2)) * MvPolynomial.X 1
    + MvPolynomial.C (asA a b * g)

theorem finSuccEquiv_asH (a b g : K) :
    MvPolynomial.finSuccEquiv K 2 (asH a b g)
      = Polynomial.C (alphaF a b) * Polynomial.X + Polynomial.C (betaF a b g) := by
  simp only [asH, asHlo, asH3, asQ, asA, asB, alphaF, betaF,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat,
    finSuccEquiv_X_zero_fw, finSuccEquiv_X_one_fw, finSuccEquiv_X_two_fw, finSuccEquiv_C,
    Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg]
  first | refl_ring1 | ring

theorem finSuccEquiv_alphaF (a b : K) :
    MvPolynomial.finSuccEquiv K 1 (alphaF a b)
      = Polynomial.C (MvPolynomial.C (2 * asA a b)) * Polynomial.X
        + Polynomial.C (MvPolynomial.C (asB a b)
            - MvPolynomial.C (2 * asA a b) * MvPolynomial.X 0 ^ 2) := by
  simp only [alphaF, asA, asB, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat,
    finSuccEquiv1_X_zero_fw, finSuccEquiv1_X_one_fw, finSuccEquiv_C,
    Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg]
  first | refl_ring1 | ring

theorem alphaF_ne_zero (a b : K) (hA : asA a b ≠ 0) : alphaF a b ≠ 0 := by
  have h2A : (2 : K) * asA a b ≠ 0 := mul_ne_zero two_ne_zero_fw hA
  intro h
  have h1 : MvPolynomial.finSuccEquiv K 1 (alphaF a b) = 0 := by rw [h, map_zero]
  rw [finSuccEquiv_alphaF] at h1
  have h2 := congrArg (fun p : Polynomial (MvPolynomial (Fin 1) K) => p.coeff 1) h1
  rw [coeff_one_C_mul_X_add_C, Polynomial.coeff_zero] at h2
  exact (MvPolynomial.C_ne_zero.mpr h2A) h2

theorem alphaF_irreducible (a b : K) (hA : asA a b ≠ 0) : Irreducible (alphaF a b) := by
  have h2A : (2 : K) * asA a b ≠ 0 := mul_ne_zero two_ne_zero_fw hA
  have hψirr : Irreducible (MvPolynomial.finSuccEquiv K 1 (alphaF a b)) := by
    rw [finSuccEquiv_alphaF]
    exact irreducible_C_mul_X_add_C_of_isUnit
      (IsUnit.map (MvPolynomial.C : K →+* MvPolynomial (Fin 1) K)
        (isUnit_iff_ne_zero.mpr h2A))
  exact (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv K 1)).mp hψirr

theorem alphaF_not_dvd_betaF (a b g : K) (hA : asA a b ≠ 0) (hg : g ≠ 0) :
    ¬ (alphaF a b ∣ betaF a b g) := by
  have h2A : (2 : K) * asA a b ≠ 0 := mul_ne_zero two_ne_zero_fw hA
  have hkey : (2 * asA a b) * (-(asB a b) * (2 * asA a b)⁻¹) = -asB a b := by
    calc (2 * asA a b) * (-(asB a b) * (2 * asA a b)⁻¹)
        = -((asB a b) * ((2 * asA a b) * (2 * asA a b)⁻¹)) := by ring
      _ = -(asB a b) := by rw [mul_inv_cancel₀ h2A, mul_one]
  have hv : MvPolynomial.eval (![-(asB a b) * (2 * asA a b)⁻¹, 0] : Fin 2 → K) (alphaF a b) = 0 := by
    simp only [alphaF, map_add, map_sub, map_mul, map_pow, MvPolynomial.eval_X,
      MvPolynomial.eval_C, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons]
    rw [show (0 : K) ^ 2 = 0 from by norm_num, sub_zero, hkey]
    first | refl_ring1 | ring
  have hw : MvPolynomial.eval (![-(asB a b) * (2 * asA a b)⁻¹, 0] : Fin 2 → K) (betaF a b g)
      = asA a b * g := by
    simp only [betaF, map_add, map_mul, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_C,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
    first | refl_ring1 | ring
  intro hdvd
  obtain ⟨e, he⟩ := hdvd
  have h := congrArg (MvPolynomial.eval (![-(asB a b) * (2 * asA a b)⁻¹, 0] : Fin 2 → K)) he
  rw [map_mul] at h
  rw [hv, hw, zero_mul] at h
  exact (mul_ne_zero hA hg) h

/-- **`asH a b g` is irreducible** for `A ≠ 0` and `g ≠ 0`. -/
theorem asH_irreducible (a b g : K) (hA : asA a b ≠ 0) (hg : g ≠ 0) :
    Irreducible (asH a b g) := by
  have hα : alphaF a b ≠ 0 := alphaF_ne_zero a b hA
  have hαirr : Irreducible (alphaF a b) := alphaF_irreducible a b hA
  have hαβ : ¬ (alphaF a b ∣ betaF a b g) := alphaF_not_dvd_betaF a b g hA hg
  have hrel : IsRelPrime (alphaF a b) (betaF a b g) := by
    intro d hda hdb
    obtain ⟨e, hea⟩ := hda
    rcases hαirr.isUnit_or_isUnit hea with hu | hu
    · exact hu
    · exfalso
      obtain ⟨v, hv⟩ := hu
      subst hv
      have hαd : alphaF a b ∣ d := by
        refine ⟨↑v⁻¹, ?_⟩
        rw [hea, mul_assoc, Units.mul_inv, mul_one]
      exact hαβ (dvd_trans hαd hdb)
  have hmain : Irreducible (Polynomial.C (alphaF a b) * Polynomial.X + Polynomial.C (betaF a b g)) :=
    irreducible_C_mul_X_add_C hα hrel
  exact (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv K 2)).mp (by
    rw [finSuccEquiv_asH a b g]
    exact hmain)

end Work.MotAS.Nodes.Fw3
