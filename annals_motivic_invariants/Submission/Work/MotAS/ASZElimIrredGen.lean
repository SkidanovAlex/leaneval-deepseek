import Mathlib
import Submission.Work.MotAS.ASZElimData
import Submission.Work.ClassBCD.RatFunc.irreducible_X_pow_sub_X_sub_C
import Submission.Work.MotAS.ASZGen.CertDefs
import Submission.Work.MotAS.ASZGen.CertQData
import Submission.Work.MotAS.ASZGen.CertSData
import Submission.Work.MotAS.ASZGen.restrict_irreducible
import Submission.Work.MotAS.ASZGen.irreducible_of_root_finrank_five
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Irreducibility of the AS eliminant `P a b g` in characteristic `5`

`P = P a b g ∈ K[X₀,X₁]` is the eliminant of the residual chart of the Crauder–Katz link
(`Work.MotAS.ASZElim.P`).  Its restriction to `X₁ = 0` is the quintic

`P₀ = c5 X^5 + c4 X^4 + c3 X^3 + c2 X^2 + c0`

with `c5 = a^5g^2 - a^3b^2 + 2a^2b^3 + 2b^5g^2`, `c4 = 2a^4b + 2a^3b^2 - a^2b^3 + ab^4`,
`c3 = -a^5 - a^4b + 2a^3b^2 + a^2b^3 - 2ab^4 + 2b^5`, `c2 = 2a^5 - b^5`, `c0 = -a^5 - 2b^5`.

The proof goes as follows.  In `L = K[θ]/(θ^5 - θ - g)` (a field, `hg`), the element
`W = cf(θ)` of the Artin–Schreier extension satisfies the quintic relation

`W^5 + c4 W^4 + c5 c3 W^3 + c5^2 c2 W^2 + c5^4 c0 = 0`

(`cert_dvd_aux`, from the explicit cofactors `Qd`/`Sd` of `CertQData`/`CertSData`).  Since `cf` has
degree `4` and leading coefficient `c4 ≠ 0`, `W ∉ K`; this also forces `c5 ≠ 0` (`c5 = 0` would give
`W^4 (W + c4) = 0`, i.e. `W ∈ K`).  Hence `T = W / c5` satisfies `P₀(T) = 0`, and since `[L : K] = 5`
is prime and `T ∉ K`, `P₀` is irreducible.  The two-variable elimination argument
`restrict_irreducible` upgrades this to `P`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.MotAS

open Polynomial

/-! ### The divisibility certificate for `cf` -/

/-- The polynomial identity behind the certificate: over `ℤ[a,b,g]`,

`cf^5 + c4 cf^4 + (c5 c3) cf^3 + (c5^2 c2) cf^2 + (c5^4 c0) = (X^5 - X - g) * Qd + 5 * Sd`.

In characteristic `5` the `5 * Sd` term vanishes, so `X^5 - X - g` divides the left hand side. -/
theorem cert_dvd_aux {K : Type*} [Field K] [CharP K 5] (a b g : K) :
    (X ^(5:ℕ) - X - C g) ∣
      (Work.MotAS.ASZGen.cf a b g ^(5:ℕ)
        + C (2*a^(4:ℕ)*b+2*a^(3:ℕ)*b^(2:ℕ)-a^(2:ℕ)*b^(3:ℕ)+a*b^(4:ℕ)) * Work.MotAS.ASZGen.cf a b g ^(4:ℕ)
        + C ((a^(5:ℕ)*g^(2:ℕ)-a^(3:ℕ)*b^(2:ℕ)+2*a^(2:ℕ)*b^(3:ℕ)+2*b^(5:ℕ)*g^(2:ℕ))
            *(-a^(5:ℕ)-a^(4:ℕ)*b+2*a^(3:ℕ)*b^(2:ℕ)+a^(2:ℕ)*b^(3:ℕ)-2*a*b^(4:ℕ)+2*b^(5:ℕ))) * Work.MotAS.ASZGen.cf a b g ^(3:ℕ)
        + C ((a^(5:ℕ)*g^(2:ℕ)-a^(3:ℕ)*b^(2:ℕ)+2*a^(2:ℕ)*b^(3:ℕ)+2*b^(5:ℕ)*g^(2:ℕ))^(2:ℕ)*(2*a^(5:ℕ)-b^(5:ℕ)))
            * Work.MotAS.ASZGen.cf a b g ^(2:ℕ)
        + C ((a^(5:ℕ)*g^(2:ℕ)-a^(3:ℕ)*b^(2:ℕ)+2*a^(2:ℕ)*b^(3:ℕ)+2*b^(5:ℕ)*g^(2:ℕ))^(4:ℕ)*(-a^(5:ℕ)-2*b^(5:ℕ)))) := by
  have hcf : Work.MotAS.ASZGen.cf a b g =
      (C (2*a^(4:ℕ)*b+2*a^(3:ℕ)*b^(2:ℕ)-a^(2:ℕ)*b^(3:ℕ)+a*b^(4:ℕ)) * X ^(4:ℕ)
        + C (g * (a+2*b)^(5:ℕ)) * X ^(3:ℕ)
        + C (a*b*(3*a+b)*(a^(2:ℕ)+b^(2:ℕ))) * X ^(2:ℕ)
        + C (g * (-a^(5:ℕ)-a^(4:ℕ)*b+2*a^(3:ℕ)*b^(2:ℕ)+a^(2:ℕ)*b^(3:ℕ)-2*a*b^(4:ℕ)+2*b^(5:ℕ))) * X
        + C (-(a+2*b)*a^(2:ℕ)*b^(2:ℕ))) := rfl
  have hQ : Work.MotAS.CertData.Qd a b g =
      (C (Work.MotAS.CertData.Qd15 a b g) * X ^(15:ℕ)
        + C (Work.MotAS.CertData.Qd14 a b g) * X ^(14:ℕ)
        + C (Work.MotAS.CertData.Qd13 a b g) * X ^(13:ℕ)
        + C (Work.MotAS.CertData.Qd12 a b g) * X ^(12:ℕ)
        + C (Work.MotAS.CertData.Qd11 a b g) * X ^(11:ℕ)
        + C (Work.MotAS.CertData.Qd10 a b g) * X ^(10:ℕ)
        + C (Work.MotAS.CertData.Qd9 a b g) * X ^(9:ℕ)
        + C (Work.MotAS.CertData.Qd8 a b g) * X ^(8:ℕ)
        + C (Work.MotAS.CertData.Qd7 a b g) * X ^(7:ℕ)
        + C (Work.MotAS.CertData.Qd6 a b g) * X ^(6:ℕ)
        + C (Work.MotAS.CertData.Qd5 a b g) * X ^(5:ℕ)
        + C (Work.MotAS.CertData.Qd4 a b g) * X ^(4:ℕ)
        + C (Work.MotAS.CertData.Qd3 a b g) * X ^(3:ℕ)
        + C (Work.MotAS.CertData.Qd2 a b g) * X ^(2:ℕ)
        + C (Work.MotAS.CertData.Qd1 a b g) * X ^(1:ℕ)
        + C (Work.MotAS.CertData.Qd0 a b g)) := rfl
  have hS : Work.MotAS.CertData.Sd a b g =
      (C (Work.MotAS.CertData.Sd4 a b g) * X ^(4:ℕ)
        + C (Work.MotAS.CertData.Sd3 a b g) * X ^(3:ℕ)
        + C (Work.MotAS.CertData.Sd2 a b g) * X ^(2:ℕ)
        + C (Work.MotAS.CertData.Sd1 a b g) * X ^(1:ℕ)
        + C (Work.MotAS.CertData.Sd0 a b g)) := rfl
  have hkey : (Work.MotAS.ASZGen.cf a b g ^(5:ℕ)
        + C (2*a^(4:ℕ)*b+2*a^(3:ℕ)*b^(2:ℕ)-a^(2:ℕ)*b^(3:ℕ)+a*b^(4:ℕ)) * Work.MotAS.ASZGen.cf a b g ^(4:ℕ)
        + C ((a^(5:ℕ)*g^(2:ℕ)-a^(3:ℕ)*b^(2:ℕ)+2*a^(2:ℕ)*b^(3:ℕ)+2*b^(5:ℕ)*g^(2:ℕ))
            *(-a^(5:ℕ)-a^(4:ℕ)*b+2*a^(3:ℕ)*b^(2:ℕ)+a^(2:ℕ)*b^(3:ℕ)-2*a*b^(4:ℕ)+2*b^(5:ℕ))) * Work.MotAS.ASZGen.cf a b g ^(3:ℕ)
        + C ((a^(5:ℕ)*g^(2:ℕ)-a^(3:ℕ)*b^(2:ℕ)+2*a^(2:ℕ)*b^(3:ℕ)+2*b^(5:ℕ)*g^(2:ℕ))^(2:ℕ)*(2*a^(5:ℕ)-b^(5:ℕ)))
            * Work.MotAS.ASZGen.cf a b g ^(2:ℕ)
        + C ((a^(5:ℕ)*g^(2:ℕ)-a^(3:ℕ)*b^(2:ℕ)+2*a^(2:ℕ)*b^(3:ℕ)+2*b^(5:ℕ)*g^(2:ℕ))^(4:ℕ)*(-a^(5:ℕ)-2*b^(5:ℕ))))
      = (X ^(5:ℕ) - X - C g) * Work.MotAS.CertData.Qd a b g
        + C (5 : K) * Work.MotAS.CertData.Sd a b g := by
    rw [hcf, hQ, hS]
    first
      | (simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_zero, map_ofNat]; refl_ring1)
      | polynomial
      | (simp only [Polynomial.C_eq_algebraMap]; polynomial)
      | ring_nf
  have hC5 : (C (5 : K) : Polynomial K) = 0 := by
    rw [show (5 : K) = 0 from CharP.cast_eq_zero K 5]
    simp
  refine ⟨Work.MotAS.CertData.Qd a b g, ?_⟩
  rw [hkey, hC5]
  simp

/-! ### Degree of the eliminant -/

/-- A monomial shaped term `C c * X 0^m * X 1^n` with `m + n ≤ 5` has total degree at most `5`. -/
private lemma totalDegree_term_le {K : Type*} [Field K] (c : K) (m n : ℕ) (h : m + n ≤ 5) :
    (MvPolynomial.C c * (MvPolynomial.X (0 : Fin 2)) ^ m
      * (MvPolynomial.X (1 : Fin 2)) ^ n : MvPolynomial (Fin 2) K).totalDegree ≤ 5 := by
  have h1 : (MvPolynomial.C c * (MvPolynomial.X (0 : Fin 2)) ^ m :
      MvPolynomial (Fin 2) K).totalDegree ≤ m := by
    calc (MvPolynomial.C c * (MvPolynomial.X (0 : Fin 2)) ^ m).totalDegree
        ≤ (MvPolynomial.C c).totalDegree + ((MvPolynomial.X (0 : Fin 2)) ^ m).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ = m := by simp
  calc (MvPolynomial.C c * (MvPolynomial.X (0 : Fin 2)) ^ m
          * (MvPolynomial.X (1 : Fin 2)) ^ n).totalDegree
      ≤ (MvPolynomial.C c * (MvPolynomial.X (0 : Fin 2)) ^ m).totalDegree
        + ((MvPolynomial.X (1 : Fin 2)) ^ n).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ ≤ m + n := add_le_add h1 (le_of_eq (MvPolynomial.totalDegree_X_pow _ _))
    _ ≤ 5 := h

/-- The eliminant `P a b g` has total degree at most `5`. -/
theorem P_totalDegree_le_aux {K : Type*} [Field K] (a b g : K) :
    (Work.MotAS.ASZElim.P a b g).totalDegree ≤ 5 := by
  have hP : Work.MotAS.ASZElim.P a b g =
      MvPolynomial.C (a^(5:ℕ)*g^(2:ℕ) + -1*a^(3:ℕ)*b^(2:ℕ) + 2*a^(2:ℕ)*b^(3:ℕ) + 2*b^(5:ℕ)*g^(2:ℕ))
          * (MvPolynomial.X (0:Fin 2))^(5:ℕ) * (MvPolynomial.X (1:Fin 2))^(0:ℕ)
      + MvPolynomial.C (2*a^(4:ℕ)*b + 2*a^(3:ℕ)*b^(2:ℕ) + -1*a^(2:ℕ)*b^(3:ℕ) + a*b^(4:ℕ))
          * (MvPolynomial.X (0:Fin 2))^(4:ℕ) * (MvPolynomial.X (1:Fin 2))^(0:ℕ)
      + MvPolynomial.C (a^(3:ℕ)*b^(2:ℕ) + 2*a^(2:ℕ)*b^(3:ℕ))
          * (MvPolynomial.X (0:Fin 2))^(3:ℕ) * (MvPolynomial.X (1:Fin 2))^(2:ℕ)
      + MvPolynomial.C (-2*a^(5:ℕ)*g + b^(5:ℕ)*g)
          * (MvPolynomial.X (0:Fin 2))^(3:ℕ) * (MvPolynomial.X (1:Fin 2))^(1:ℕ)
      + MvPolynomial.C (-1*a^(5:ℕ) + -1*a^(4:ℕ)*b + 2*a^(3:ℕ)*b^(2:ℕ) + a^(2:ℕ)*b^(3:ℕ) + -2*a*b^(4:ℕ) + 2*b^(5:ℕ))
          * (MvPolynomial.X (0:Fin 2))^(3:ℕ) * (MvPolynomial.X (1:Fin 2))^(0:ℕ)
      + MvPolynomial.C (a^(4:ℕ)*b*g + a^(3:ℕ)*b^(2:ℕ)*g + 2*a^(2:ℕ)*b^(3:ℕ)*g + -2*a*b^(4:ℕ)*g)
          * (MvPolynomial.X (0:Fin 2))^(2:ℕ) * (MvPolynomial.X (1:Fin 2))^(3:ℕ)
      + MvPolynomial.C (a^(4:ℕ)*b + 2*a^(3:ℕ)*b^(2:ℕ) + a^(2:ℕ)*b^(3:ℕ) + 2*a*b^(4:ℕ))
          * (MvPolynomial.X (0:Fin 2))^(2:ℕ) * (MvPolynomial.X (1:Fin 2))^(2:ℕ)
      + MvPolynomial.C (2*a^(5:ℕ) + -1*b^(5:ℕ))
          * (MvPolynomial.X (0:Fin 2))^(2:ℕ) * (MvPolynomial.X (1:Fin 2))^(0:ℕ)
      + MvPolynomial.C (-1*a^(5:ℕ)*g^(2:ℕ) + -2*b^(5:ℕ)*g^(2:ℕ))
          * (MvPolynomial.X (0:Fin 2))^(1:ℕ) * (MvPolynomial.X (1:Fin 2))^(4:ℕ)
      + MvPolynomial.C (-2*a^(5:ℕ)*g + -2*a^(4:ℕ)*b*g + -1*a^(3:ℕ)*b^(2:ℕ)*g + 2*a^(2:ℕ)*b^(3:ℕ)*g + a*b^(4:ℕ)*g
            + -1*b^(5:ℕ)*g)
          * (MvPolynomial.X (0:Fin 2))^(1:ℕ) * (MvPolynomial.X (1:Fin 2))^(3:ℕ)
      + MvPolynomial.C (-1*a^(5:ℕ) + -1*a^(4:ℕ)*b + -1*a^(3:ℕ)*b^(2:ℕ) + -2*a^(2:ℕ)*b^(3:ℕ) + 2*a*b^(4:ℕ) + -2*b^(5:ℕ))
          * (MvPolynomial.X (0:Fin 2))^(1:ℕ) * (MvPolynomial.X (1:Fin 2))^(2:ℕ)
      + MvPolynomial.C (2*a^(5:ℕ)*g^(3:ℕ) + -1*b^(5:ℕ)*g^(3:ℕ))
          * (MvPolynomial.X (0:Fin 2))^(0:ℕ) * (MvPolynomial.X (1:Fin 2))^(5:ℕ)
      + MvPolynomial.C (-1*a^(5:ℕ)*g + -2*b^(5:ℕ)*g)
          * (MvPolynomial.X (0:Fin 2))^(0:ℕ) * (MvPolynomial.X (1:Fin 2))^(3:ℕ)
      + MvPolynomial.C (a^(5:ℕ) + a^(4:ℕ)*b + -2*a^(3:ℕ)*b^(2:ℕ) + -1*a^(2:ℕ)*b^(3:ℕ) + 2*a*b^(4:ℕ) + -2*b^(5:ℕ))
          * (MvPolynomial.X (0:Fin 2))^(0:ℕ) * (MvPolynomial.X (1:Fin 2))^(2:ℕ)
      + MvPolynomial.C (-1*a^(5:ℕ) + -2*b^(5:ℕ))
          * (MvPolynomial.X (0:Fin 2))^(0:ℕ) * (MvPolynomial.X (1:Fin 2))^(0:ℕ) := by
    unfold Work.MotAS.ASZElim.P
    refl_ring1
  rw [hP]
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
        · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
          · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
            · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
              · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
                · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
                  · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
                    · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
                      · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
                        · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
                          · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
                            · exact totalDegree_term_le _ 5 0 (by decide)
                            · exact totalDegree_term_le _ 4 0 (by decide)
                          · exact totalDegree_term_le _ 3 2 (by decide)
                        · exact totalDegree_term_le _ 3 1 (by decide)
                      · exact totalDegree_term_le _ 3 0 (by decide)
                    · exact totalDegree_term_le _ 2 3 (by decide)
                  · exact totalDegree_term_le _ 2 2 (by decide)
                · exact totalDegree_term_le _ 2 0 (by decide)
              · exact totalDegree_term_le _ 1 4 (by decide)
            · exact totalDegree_term_le _ 1 3 (by decide)
          · exact totalDegree_term_le _ 1 2 (by decide)
        · exact totalDegree_term_le _ 0 5 (by decide)
      · exact totalDegree_term_le _ 0 3 (by decide)
    · exact totalDegree_term_le _ 0 2 (by decide)
  · exact totalDegree_term_le _ 0 0 (by decide)

/-! ### The `X₁ = 0` specialisation of the eliminant -/

/-- Substituting `X₀ ↦ X`, `X₁ ↦ 0` in the eliminant. -/
theorem aeval_restrict_P_aux {K : Type*} [Field K] (a b g : K) :
    MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then (Polynomial.X : Polynomial K) else 0)
        (Work.MotAS.ASZElim.P a b g)
      = Polynomial.C (a^(5:ℕ)*g^(2:ℕ) - a^(3:ℕ)*b^(2:ℕ) + 2*a^(2:ℕ)*b^(3:ℕ) + 2*b^(5:ℕ)*g^(2:ℕ)) * Polynomial.X^(5:ℕ)
        + Polynomial.C (2*a^(4:ℕ)*b + 2*a^(3:ℕ)*b^(2:ℕ) - a^(2:ℕ)*b^(3:ℕ) + a*b^(4:ℕ)) * Polynomial.X^(4:ℕ)
        + Polynomial.C (-a^(5:ℕ) - a^(4:ℕ)*b + 2*a^(3:ℕ)*b^(2:ℕ) + a^(2:ℕ)*b^(3:ℕ) - 2*a*b^(4:ℕ) + 2*b^(5:ℕ)) * Polynomial.X^(3:ℕ)
        + Polynomial.C (2*a^(5:ℕ) - b^(5:ℕ)) * Polynomial.X^(2:ℕ)
        + Polynomial.C (-a^(5:ℕ) - 2*b^(5:ℕ)) := by
  simp [Work.MotAS.ASZElim.P]
  first
    | (simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_zero, map_ofNat]; refl_ring1)
    | ring
    | ring_nf
    | polynomial
    | (simp only [Polynomial.C_eq_algebraMap]; polynomial)
    | (simp only [Polynomial.C_eq_algebraMap]; ring_nf)

/-! ### The main theorem -/

theorem ASZElimIrredGen (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^(2:ℕ) - a * b - b ^(2:ℕ) ≠ 0) (hab : a ≠ 0) (hbb : b ≠ 0)
    (hg : ¬ ∃ c : K, c ^(5:ℕ) - c = g) :
    Irreducible (Work.MotAS.ASZElim.P a b g) := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  -- ## the coefficients of the eliminant, restricted to `X₁ = 0`
  set c5 : K := a^(5:ℕ)*g^(2:ℕ) - a^(3:ℕ)*b^(2:ℕ) + 2*a^(2:ℕ)*b^(3:ℕ) + 2*b^(5:ℕ)*g^(2:ℕ) with hc5
  set c4 : K := 2*a^(4:ℕ)*b + 2*a^(3:ℕ)*b^(2:ℕ) - a^(2:ℕ)*b^(3:ℕ) + a*b^(4:ℕ) with hc4
  set c3 : K := -a^(5:ℕ) - a^(4:ℕ)*b + 2*a^(3:ℕ)*b^(2:ℕ) + a^(2:ℕ)*b^(3:ℕ) - 2*a*b^(4:ℕ) + 2*b^(5:ℕ) with hc3
  set c2 : K := 2*a^(5:ℕ) - b^(5:ℕ) with hc2
  set c0 : K := -a^(5:ℕ) - 2*b^(5:ℕ) with hc0
  -- ## `c4 ≠ 0`
  have hm2b : 2*a - b ≠ 0 := by
    intro h
    apply ha
    have h1 : a^(2:ℕ) - a*b - b^(2:ℕ) = (2*a-b)*(3*a+b) - 5*a^(2:ℕ) := by ring
    rw [h1, h, h5]
    refl_ring1
  have hc4ne : c4 ≠ 0 := by
    rw [hc4]
    have h1 : 2*a^(4:ℕ)*b + 2*a^(3:ℕ)*b^(2:ℕ) - a^(2:ℕ)*b^(3:ℕ) + a*b^(4:ℕ)
        = a*b*(a^(2:ℕ)-a*b-b^(2:ℕ))*(2*a-b) + 5*(a^(3:ℕ)*b^(2:ℕ)) := by ring
    rw [h1, h5]
    simp only [zero_mul, add_zero]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hab hbb) ha) hm2b
  -- ## the Artin-Schreier field `L = K[θ]/(θ^5-θ-g)`
  have hg' : ∀ c : K, c ^(5:ℕ) - c ≠ g := fun c h => hg ⟨c, h⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set F : Polynomial K := X ^(5:ℕ) - X - C g with hF
  have hFirr : Irreducible F := by
    rw [hF]
    exact Work.ClassBCD.RatFunc.irreducible_X_pow_sub_X_sub_C K 5 g hg'
  haveI : Fact (Irreducible F) := ⟨hFirr⟩
  have hFnatDeg : F.natDegree = 5 := by
    rw [hF, show (X ^(5:ℕ) - X - C g : Polynomial K) = X ^(5:ℕ) - (X + C g) by ring]
    have hsub : (X ^(5:ℕ) - (X + C g) : Polynomial K).natDegree =
        (X ^(5:ℕ) : Polynomial K).natDegree :=
      Polynomial.natDegree_sub_eq_left_of_natDegree_lt (p := X ^(5:ℕ)) (q := X + C g) (by
        have h : (X + C g : Polynomial K).natDegree ≤ 1 := by
          refine (Polynomial.natDegree_add_le _ _).trans ?_
          rw [Polynomial.natDegree_X, Polynomial.natDegree_C]
          norm_num
        rw [Polynomial.natDegree_X_pow]
        omega)
    rw [hsub, Polynomial.natDegree_X_pow]
  have hFne : F ≠ 0 := by
    intro h
    have h2 := hFnatDeg
    rw [h] at h2
    simp at h2
  -- ## the element `W = cf(θ)`
  set W : AdjoinRoot F := AdjoinRoot.mk F (Work.MotAS.ASZGen.cf a b g) with hW
  have hdiv : F ∣ (Work.MotAS.ASZGen.cf a b g ^(5:ℕ) + C c4 * Work.MotAS.ASZGen.cf a b g ^(4:ℕ)
      + C (c5 * c3) * Work.MotAS.ASZGen.cf a b g ^(3:ℕ)
      + C (c5 ^(2:ℕ) * c2) * Work.MotAS.ASZGen.cf a b g ^(2:ℕ)
      + C (c5 ^(4:ℕ) * c0)) := by
    rw [hF, hc4, hc5, hc3, hc2, hc0]
    exact cert_dvd_aux (K := K) a b g
  set C5 : AdjoinRoot F := algebraMap K (AdjoinRoot F) c5 with hC5
  set C4 : AdjoinRoot F := algebraMap K (AdjoinRoot F) c4 with hC4
  set C3 : AdjoinRoot F := algebraMap K (AdjoinRoot F) c3 with hC3
  set C2 : AdjoinRoot F := algebraMap K (AdjoinRoot F) c2 with hC2
  set C0 : AdjoinRoot F := algebraMap K (AdjoinRoot F) c0 with hC0
  -- ## the quintic relation satisfied by `W`
  have hrel : W ^(5:ℕ) + C4 * W ^(4:ℕ) + (C5 * C3) * W ^(3:ℕ) + (C5 ^(2:ℕ) * C2) * W ^(2:ℕ)
      + C5 ^(4:ℕ) * C0 = 0 := by
    have h0 : AdjoinRoot.mk F (Work.MotAS.ASZGen.cf a b g ^(5:ℕ)
        + C c4 * Work.MotAS.ASZGen.cf a b g ^(4:ℕ)
        + C (c5 * c3) * Work.MotAS.ASZGen.cf a b g ^(3:ℕ)
        + C (c5 ^(2:ℕ) * c2) * Work.MotAS.ASZGen.cf a b g ^(2:ℕ)
        + C (c5 ^(4:ℕ) * c0)) = 0 :=
      AdjoinRoot.mk_eq_zero.mpr hdiv
    simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_C, ← hW, ← hC5, ← hC4, ← hC3,
      ← hC2, ← hC0] at h0
    exact h0
  -- ## `W ∉ K`
  have hWnotK : W ∉ Set.range (algebraMap K (AdjoinRoot F)) := by
    rintro ⟨k, hk⟩
    have h1 : AdjoinRoot.mk F (Work.MotAS.ASZGen.cf a b g - C k) = 0 := by
      rw [map_sub, hW.symm, AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq, ← hk, sub_self]
    have hdiv' : F ∣ (Work.MotAS.ASZGen.cf a b g - C k) := AdjoinRoot.mk_eq_zero.mp h1
    have hne : Work.MotAS.ASZGen.cf a b g - C k ≠ 0 := by
      intro h0
      have hcoeff : (Work.MotAS.ASZGen.cf a b g).coeff 4 = c4 := by
        rw [hc4]; exact Work.MotAS.ASZGen.cf_coeff_four a b g
      have hz : (Work.MotAS.ASZGen.cf a b g - C k).coeff 4 = 0 := by
        rw [h0, Polynomial.coeff_zero]
      have hCk : (C k : Polynomial K).coeff 4 = 0 := by
        rw [Polynomial.coeff_C]
        norm_num
      rw [Polynomial.coeff_sub, hcoeff, hCk, sub_zero] at hz
      exact hc4ne hz
    have hle := Polynomial.natDegree_le_of_dvd hdiv' hne
    rw [hFnatDeg] at hle
    have h4 : (Work.MotAS.ASZGen.cf a b g - C k).natDegree ≤ 4 :=
      (Polynomial.natDegree_sub_le _ _).trans
        (max_le (Work.MotAS.ASZGen.cf_natDegree_le a b g)
          ((le_of_eq (Polynomial.natDegree_C k)).trans (by decide)))
    omega
  -- ## `c5 ≠ 0`
  have hc5ne : c5 ≠ 0 := by
    intro hc5zero
    have hC5z : C5 = 0 := by rw [hC5, hc5zero, map_zero]
    have hW4 : W ^(4:ℕ) * (W + C4) = 0 := by
      have h1 : W ^(5:ℕ) + C4 * W ^(4:ℕ) = 0 := by
        have h := hrel
        rw [hC5z] at h
        simpa using h
      rw [← h1]
      refl_ring1
    rcases mul_eq_zero.mp hW4 with h | h
    · apply hWnotK
      have hW0 : W = 0 := (pow_eq_zero_iff (by norm_num : (4:ℕ) ≠ 0)).mp h
      exact ⟨0, by rw [map_zero, hW0]⟩
    · apply hWnotK
      have hWc : W = -C4 := (add_eq_zero_iff_eq_neg).mp h
      refine ⟨-c4, ?_⟩
      rw [map_neg, ← hC4, hWc]
  have hC5ne : C5 ≠ 0 := by
    rw [hC5]
    intro h
    exact hc5ne (FaithfulSMul.algebraMap_injective K (AdjoinRoot F) (by rw [h, map_zero]))
  -- ## the element `T = W / c5`
  set T : AdjoinRoot F := C5⁻¹ * W with hT
  have hT' : C5 * T = W := by
    rw [hT, ← mul_assoc, mul_inv_cancel₀ hC5ne, one_mul]
  have hTnotK : T ∉ Set.range (algebraMap K (AdjoinRoot F)) := by
    rintro ⟨k, hk⟩
    apply hWnotK
    refine ⟨c5 * k, ?_⟩
    rw [map_mul, hk, ← hC5]
    exact hT'
  -- ## `P₀` and `P₀(T) = 0`
  set P0 : Polynomial K := C c5 * X ^(5:ℕ) + C c4 * X ^(4:ℕ) + C c3 * X ^(3:ℕ) + C c2 * X ^(2:ℕ) + C c0
    with hP0
  have hP0nat : P0.natDegree = 5 := by
    rw [hP0]
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (n := 5) ?_ ?_
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
        · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
          · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
            · exact (Polynomial.natDegree_C_mul_X_pow_le _ 5).trans (by decide)
            · exact (Polynomial.natDegree_C_mul_X_pow_le _ 4).trans (by decide)
          · exact (Polynomial.natDegree_C_mul_X_pow_le _ 3).trans (by decide)
        · exact (Polynomial.natDegree_C_mul_X_pow_le _ 2).trans (by decide)
      · exact (le_of_eq (Polynomial.natDegree_C _)).trans (by decide)
    · have hc : (C c5 * X ^(5:ℕ) + C c4 * X ^(4:ℕ) + C c3 * X ^(3:ℕ) + C c2 * X ^(2:ℕ)
          + C c0 : Polynomial K).coeff 5 = c5 := by
        simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
          Polynomial.coeff_C]
        norm_num
      rw [hc]
      exact hc5ne
  have hP0ne : P0 ≠ 0 := by
    intro h
    have h2 := hP0nat
    rw [h] at h2
    simp at h2
  have hP0eval : Polynomial.aeval T P0 = 0 := by
    have key : C5 ^(4:ℕ) * Polynomial.aeval T P0 = 0 := by
      rw [hP0]
      simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
        ← hC5, ← hC4, ← hC3, ← hC2, ← hC0]
      have he : C5 ^(4:ℕ) * (C5 * T ^(5:ℕ) + C4 * T ^(4:ℕ) + C3 * T ^(3:ℕ) + C2 * T ^(2:ℕ) + C0)
          = W ^(5:ℕ) + C4 * W ^(4:ℕ) + (C5 * C3) * W ^(3:ℕ) + (C5 ^(2:ℕ) * C2) * W ^(2:ℕ)
            + C5 ^(4:ℕ) * C0 := by
        rw [← hT']
        refl_ring1
      rw [he, hrel]
    exact (mul_eq_zero.mp key).resolve_left (pow_ne_zero 4 hC5ne)
  -- ## `finrank K L = 5`
  have hfin : Module.finrank K (AdjoinRoot F) = 5 := by
    have h1 : Module.finrank K (AdjoinRoot F) = (AdjoinRoot.powerBasis hFne).dim :=
      PowerBasis.finrank (AdjoinRoot.powerBasis hFne)
    rw [h1, AdjoinRoot.powerBasis_dim hFne, hFnatDeg]
  -- ## `P₀` is irreducible
  have hP0irr : Irreducible P0 :=
    Work.MotAS.ASZGen.irreducible_of_root_finrank_five hfin T hTnotK P0 hP0ne hP0eval
      (le_of_eq hP0nat)
  -- ## assemble: restrict `P` to `X₁ = 0` and apply the line criterion
  refine Work.MotAS.ASZGen.restrict_irreducible (Work.MotAS.ASZElim.P a b g)
    (P_totalDegree_le_aux (K := K) a b g) ?_ ?_
  · rw [aeval_restrict_P_aux (K := K) a b g,
      ← hc5, ← hc4, ← hc3, ← hc2, ← hc0, ← hP0]
    exact hP0irr
  · rw [aeval_restrict_P_aux (K := K) a b g,
      ← hc5, ← hc4, ← hc3, ← hc2, ← hc0, ← hP0]
    exact hP0nat

end Work.MotAS
