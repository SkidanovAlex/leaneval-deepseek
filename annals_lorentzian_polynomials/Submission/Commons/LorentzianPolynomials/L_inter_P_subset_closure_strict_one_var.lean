import Mathlib
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.strict_subset_L

namespace Commons.LorentzianPolynomials

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

/-!
# The one-variable case of Theorem 2.25

For `n = 1` the strictly Lorentzian polynomials are exactly the degree-`d` homogeneous
polynomials with positive coefficients:

`Ŀ 1 d = P 1 d` for every `d`.

Consequently `L 1 d ∩ P 1 d ⊆ P 1 d = Ŀ 1 d ⊆ closure (Ŀ 1 d)`.
-/

/-- In one variable, a monomial of weight `m` is necessarily `single 0 m`. -/
private lemma one_var_weight_eq_single {m : ℕ} {m' : Fin 1 →₀ ℕ}
    (hm : Finsupp.weight (1 : Fin 1 → ℕ) m' = m) : m' = Finsupp.single (0 : Fin 1) m := by
  apply Finsupp.ext
  intro i
  fin_cases i
  have hw : m' (0 : Fin 1) = m := by
    rw [← hm]
    rw [Finsupp.weight_eq_sum]
    simp
  simp [hw]

/-- The coefficient of the (unique) degree-`d` monomial of a member of `P 1 d` is positive. -/
private lemma one_var_coeff_of_mem_P {d : ℕ} {f : H 1 d} (hf : f ∈ P 1 d) :
    0 < f.1.coeff (Finsupp.single (0 : Fin 1) d) := by
  exact hf (Finsupp.single (0 : Fin 1) d) (by simp [Finsupp.weight_single])

/-- Membership in `P 1 m` is equivalent to positivity of the single coefficient. -/
private lemma one_var_mem_P_iff_coeff_pos (m : ℕ) (f : H 1 m) :
    f ∈ P 1 m ↔ 0 < f.1.coeff (Finsupp.single (0 : Fin 1) m) := by
  constructor
  · intro hf
    exact one_var_coeff_of_mem_P hf
  · intro hpos m' hm
    have hm' : m' = Finsupp.single (0 : Fin 1) m := one_var_weight_eq_single hm
    simpa [hm'] using hpos

/-- The coefficient of the partial derivative at the expected monomial. -/
private lemma one_var_coeff_pderiv (k : ℕ) (f : H 1 (k + 1)) :
    (pderiv (0 : Fin 1) f.1).coeff (Finsupp.single (0 : Fin 1) k) =
      (k + 1 : ℝ) * f.1.coeff (Finsupp.single (0 : Fin 1) (k + 1)) := by
  have hc := MvPolynomial.coeff_pderiv (p := f.1) (i := (0 : Fin 1)) (m := Finsupp.single (0 : Fin 1) k)
  have hsum : (Finsupp.single (0 : Fin 1) k + Finsupp.single (0 : Fin 1) 1 : Fin 1 →₀ ℕ) =
      Finsupp.single (0 : Fin 1) (k + 1) := by
    apply Finsupp.ext
    intro i
    fin_cases i
    simp
  rw [hc]
  rw [hsum]
  have hk : (Finsupp.single (0 : Fin 1) k) (0 : Fin 1) = k := Finsupp.single_eq_same
  rw [hk]
  ring

/-- The derivative of a positive one-variable polynomial of degree `k+1` is positive of
degree `k`. -/
private lemma one_var_pderiv_mem_P (k : ℕ) (f : H 1 (k + 1)) (hf : f ∈ P 1 (k + 1)) :
    (⟨f.1.pderiv (0 : Fin 1), f.2.pderiv⟩ : H 1 k) ∈ P 1 k := by
  exact (one_var_mem_P_iff_coeff_pos k (⟨f.1.pderiv (0 : Fin 1), f.2.pderiv⟩ : H 1 k)).mpr (by
    change 0 < (f.1.pderiv (0 : Fin 1)).coeff (Finsupp.single (0 : Fin 1) k)
    rw [one_var_coeff_pderiv k f]
    have hc : 0 < f.1.coeff (Finsupp.single (0 : Fin 1) (k + 1)) := one_var_coeff_of_mem_P hf
    positivity)

/-- The Hessian of a homogeneous quadratic in one variable is the diagonal `2c`. -/
private lemma hessian_one (f : H 1 2) :
    f.hessian = Matrix.diagonal (fun _ : Fin 1 => 2 * f.1.coeff (Finsupp.single (0 : Fin 1) 2)) := by
  ext i j
  fin_cases i
  fin_cases j
  unfold H.hessian
  simp

/-- In degree two and one variable `Ŀ 1 2 = P 1 2`. -/
private lemma Ŀ1_eq_P1_of_degree_two : Ŀ 1 2 = P 1 2 := by
  apply le_antisymm
  · intro f hf
    exact hf.1
  · intro f hf
    have hpos : 0 < f.1.coeff (Finsupp.single (0 : Fin 1) 2) := one_var_coeff_of_mem_P hf
    change f ∈ {f : H 1 2 | f ∈ P 1 2 ∧ IsUnit f.hessian ∧
      (f.hessian.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 1}
    constructor
    · exact hf
    · constructor
      · -- IsUnit hessian: the single entry `2 * coeff` is non-zero since `coeff > 0`
        have hhess : f.hessian = Matrix.diagonal (fun _ : Fin 1 => 2 * f.1.coeff (Finsupp.single (0 : Fin 1) 2)) :=
          hessian_one f
        rw [Matrix.isUnit_iff_isUnit_det]
        rw [hhess, Matrix.det_diagonal]
        simp
        exact ne_of_gt (by positivity)
      · -- exactly one positive root: the characteristic polynomial is `X - C (2 * coeff)`
        have hhess : f.hessian = Matrix.diagonal (fun _ : Fin 1 => 2 * f.1.coeff (Finsupp.single (0 : Fin 1) 2)) :=
          hessian_one f
        rw [hhess, Matrix.charpoly_diagonal]
        rw [Fin.prod_univ_one]
        have hroots : (Polynomial.X - Polynomial.C (2 * f.1.coeff (Finsupp.single (0 : Fin 1) 2))).roots =
            ({2 * f.1.coeff (Finsupp.single (0 : Fin 1) 2)} : Multiset ℝ) :=
          Polynomial.roots_X_sub_C _
        rw [hroots]
        have hgt : 0 < (2 * f.1.coeff (Finsupp.single (0 : Fin 1) 2) : ℝ) := by positivity
        rw [Multiset.filter_singleton]
        rw [if_pos hgt]
        simp

/-- In one variable, `Ŀ 1 d = P 1 d` for all `d`. -/
private lemma Ŀ1_eq_P1 (d : ℕ) : Ŀ 1 d = P 1 d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      cases d with
      | zero => rfl
      | succ d1 =>
          cases d1 with
          | zero => rfl
          | succ d2 =>
              cases d2 with
              | zero => exact Ŀ1_eq_P1_of_degree_two
              | succ k =>
                  apply le_antisymm
                  · intro f hf
                    exact hf.1
                  · intro f hf
                    change f ∈ {f : H 1 (k + 3) | f ∈ P 1 (k + 3) ∧
                      ∀ i : Fin 1, (⟨f.1.pderiv i, f.2.pderiv⟩ : H 1 (k + 2)) ∈ Ŀ 1 (k + 2)}
                    constructor
                    · exact hf
                    · intro i
                      fin_cases i
                      have hderP : (⟨f.1.pderiv (0 : Fin 1), f.2.pderiv⟩ : H 1 (k + 2)) ∈ P 1 (k + 2) :=
                        one_var_pderiv_mem_P (k + 2) f hf
                      have hi := ih (k + 2) (by omega)
                      rw [hi]
                      exact hderP

/-- In one variable, the intersection `L 1 d ∩ P 1 d` is contained in the closure of the
strictly Lorentzian polynomials. -/
theorem L_inter_P_subset_closure_strict_one_var (d : ℕ) :
    (Commons.LorentzianPolynomials.L 1 d ∩ Commons.LorentzianPolynomials.P 1 d) ⊆
      closure (Commons.LorentzianPolynomials.Ŀ 1 d) := by
  intro f hf
  have hĿ : f ∈ Ŀ 1 d := by
    rw [Ŀ1_eq_P1 d]
    exact hf.2
  exact subset_closure hĿ

end

end Commons.LorentzianPolynomials
