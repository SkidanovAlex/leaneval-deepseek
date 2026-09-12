import Mathlib
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.LorentzianPolynomials.closure_strict_eq_L_of_degree_le_two
import Submission.Commons.LorentzianPolynomials.closure_P_eq_S_of_degree_le_one
import Submission.Commons.LorentzianPolynomials.L_inter_P_subset_closure_strict_one_var
import Submission.Commons.LorentzianPolynomials.L_inter_P_subset_closure_strict_high

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set

set_option autoImplicit false

namespace Commons.LorentzianPolynomials

noncomputable section

-- Degree <= 2 base cases (any n)

private lemma deg0 (n : ℕ) : (L n 0 ∩ P n 0) ⊆ closure (Ŀ n 0) := by
  intro x hx
  have hxL : x ∈ L n 0 := hx.1
  have hS : x ∈ S n 0 := by simpa [L] using hxL
  have hcl : S n 0 = closure (Ŀ n 0) := by
    rw [show Ŀ n 0 = P n 0 by rfl]
    rw [closure_P_eq_S_of_degree_le_one n 0 (by norm_num)]
  rwa [← hcl]

private lemma deg1 (n : ℕ) : (L n 1 ∩ P n 1) ⊆ closure (Ŀ n 1) := by
  intro x hx
  have hxL : x ∈ L n 1 := hx.1
  have hS : x ∈ S n 1 := by simpa [L] using hxL
  have hcl : S n 1 = closure (Ŀ n 1) := by
    rw [show Ŀ n 1 = P n 1 by rfl]
    rw [closure_P_eq_S_of_degree_le_one n 1 (by norm_num)]
  rwa [← hcl]

private lemma deg2 (n : ℕ) (hn : 0 < n) : (L n 2 ∩ P n 2) ⊆ closure (Ŀ n 2) := by
  intro x hx
  have hxL : x ∈ L n 2 := hx.1
  have hS : x ∈ S n 2 := by simpa [L] using hxL
  have hcl : S n 2 = closure (Ŀ n 2) := by
    rw [closure_strict_eq_L_of_degree_le_two n hn]
    rfl
  rwa [← hcl]

theorem L_inter_P_subset_closure_strict (n d : ℕ) (hn : 0 < n) :
    (Commons.LorentzianPolynomials.L n d ∩ Commons.LorentzianPolynomials.P n d) ⊆
      closure (Commons.LorentzianPolynomials.Ŀ n d) := by
  by_cases hn1 : n = 1
  · subst n
    exact L_inter_P_subset_closure_strict_one_var d
  · have hn2 : 2 ≤ n := by omega
    intro x hx
    cases d with
    | zero => exact deg0 n hx
    | succ d0 =>
        cases d0 with
        | zero => exact deg1 n hx
        | succ d1 =>
            cases d1 with
            | zero => exact deg2 n hn hx
            | succ k =>
                exact L_inter_P_subset_closure_strict_high n (Nat.succ (Nat.succ (Nat.succ k))) hn2 (by norm_num) hx

end

end Commons.LorentzianPolynomials
