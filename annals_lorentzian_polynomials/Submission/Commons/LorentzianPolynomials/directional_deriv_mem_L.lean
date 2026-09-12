import Mathlib
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.LorentzianPolynomials.rayleigh_of_hessian_roots_le_one
import Submission.Commons.Analysis.MvPolynomial.isStable_of_degree_le_one
import Submission.Commons.Combinatorics.MvPolynomial.support_directionalDeriv_MConvex
import Submission.Commons.LorentzianPolynomials.directional_deriv_three_mem_L

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Commons.LorentzianPolynomials

noncomputable section

/-- The nonnegative directional derivative of a polynomial, as a polynomial. -/
def dd (n : ℕ) (u : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ j : Fin n, MvPolynomial.C (u j) * MvPolynomial.pderiv j p

lemma dd_isHomogeneous (n d : ℕ) (u : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous d) : (dd n u p).IsHomogeneous (d - 1) := by
  unfold dd
  refine MvPolynomial.IsHomogeneous.sum (s := Finset.univ)
    (fun j : Fin n => MvPolynomial.C (u j) * MvPolynomial.pderiv j p) (d - 1) ?_
  intro j hj
  have hpd : (MvPolynomial.pderiv j p).IsHomogeneous (d - 1) := hp.pderiv
  have hC : (MvPolynomial.C (u j) : MvPolynomial (Fin n) ℝ).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C (σ := Fin n) (R := ℝ) (u j)
  simpa using hC.mul hpd

lemma dd_coeff (n : ℕ) (u : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) (m : Fin n →₀ ℕ) :
    (dd n u p).coeff m =
      ∑ j : Fin n, u j * ((m j : ℝ) + 1) * p.coeff (m + Finsupp.single j 1) := by
  unfold dd
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [MvPolynomial.coeff_C_mul]
  rw [MvPolynomial.coeff_pderiv]
  ring_nf

lemma dd_coeff_nonneg (n : ℕ) (u : Fin n → ℝ) (hu : ∀ j : Fin n, 0 ≤ u j)
    (p : MvPolynomial (Fin n) ℝ) (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m) (m : Fin n →₀ ℕ) :
    0 ≤ (dd n u p).coeff m := by
  rw [dd_coeff]
  exact Finset.sum_nonneg (fun j hj => by
    have h1 : 0 ≤ u j := hu j
    have h2 : 0 ≤ (m j : ℝ) + 1 := by
      have h2n : 0 ≤ (m j : ℝ) := by exact_mod_cast (Nat.zero_le (m j))
      linarith
    have h3 : 0 ≤ p.coeff (m + Finsupp.single j 1) := hp _
    exact mul_nonneg (mul_nonneg h1 h2) h3)

lemma dd_pderiv (n : ℕ) (u : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    MvPolynomial.pderiv i (dd n u p) = dd n u (MvPolynomial.pderiv i p) := by
  unfold dd
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    MvPolynomial.pderiv i (MvPolynomial.C (u j) * MvPolynomial.pderiv j p)
        = MvPolynomial.pderiv i (u j • MvPolynomial.pderiv j p) := by rw [← MvPolynomial.smul_eq_C_mul]
    _ = u j • MvPolynomial.pderiv i (MvPolynomial.pderiv j p) := by
        exact (MvPolynomial.pderiv (R := ℝ) i : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ).map_smul (u j) _
    _ = MvPolynomial.C (u j) * MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
        rw [MvPolynomial.smul_eq_C_mul]
        rw [rayleigh_pre.pderiv_comm i j p]

/-- The nonnegative directional derivative as an element of `H n (d - 1)`. -/
noncomputable def ddH (n d : ℕ) (hd : 1 ≤ d) (u : Fin n → ℝ) (f : H n d) : H n (d - 1) :=
  ⟨dd n u f.1, (MvPolynomial.mem_homogeneousSubmodule (d - 1) (dd n u f.1)).mpr (dd_isHomogeneous n d u f.1 f.2)⟩

theorem directional_deriv_mem_L (n d : ℕ) (hn : 0 < n) (hd : 1 ≤ d)
    (f : Commons.LorentzianPolynomials.H n d) (hf : f ∈ Commons.LorentzianPolynomials.L n d)
    (u : Fin n → ℝ) (hu : ∀ j : Fin n, 0 ≤ u j) :
    ∃ g : Commons.LorentzianPolynomials.H n (d - 1),
      g ∈ Commons.LorentzianPolynomials.L n (d - 1) ∧
        g.1 = ∑ j : Fin n, MvPolynomial.C (u j) * MvPolynomial.pderiv j f.1 := by
  classical
  -- strong induction on the degree
  have main : ∀ (m : ℕ), 1 ≤ m → ∀ (f : H n m), f ∈ L n m → ∀ (u : Fin n → ℝ),
      (∀ j : Fin n, 0 ≤ u j) → ∃ g : H n (m - 1), g ∈ L n (m - 1) ∧ g.1 = dd n u f.1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro hm f hf u hu
        cases m with
        | zero => omega
        | succ m0 =>
            cases m0 with
            | zero =>
                -- m = 1
                refine ⟨ddH n 1 hm u f, ?_, rfl⟩
                have hfS : f ∈ S n 1 := by simpa [L] using hf
                have hnnf : ∀ a : Fin n →₀ ℕ, 0 ≤ f.1.coeff a := hfS.2
                have hnn : ∀ a : Fin n →₀ ℕ, 0 ≤ (ddH n 1 hm u f).1.coeff a := by
                  intro a
                  exact dd_coeff_nonneg n u hu f.1 hnnf a
                have hstable : IsStable (ddH n 1 hm u f).1 := by
                  unfold IsStable
                  exact Commons.Analysis.MvPolynomial.isStable_of_degree_le_one n 0 (by norm_num) (ddH n 1 hm u f) hnn
                change ddH n 1 hm u f ∈ S n 0
                exact ⟨hstable, hnn⟩
            | succ m1 =>
                cases m1 with
                | zero =>
                    -- m = 2
                    refine ⟨ddH n 2 hm u f, ?_, rfl⟩
                    have hfS : f ∈ S n 2 := by simpa [L] using hf
                    have hnnf : ∀ a : Fin n →₀ ℕ, 0 ≤ f.1.coeff a := hfS.2
                    have hnn : ∀ a : Fin n →₀ ℕ, 0 ≤ (ddH n 2 hm u f).1.coeff a := by
                      intro a
                      exact dd_coeff_nonneg n u hu f.1 hnnf a
                    have hstable : IsStable (ddH n 2 hm u f).1 := by
                      unfold IsStable
                      exact Commons.Analysis.MvPolynomial.isStable_of_degree_le_one n 1 (by norm_num) (ddH n 2 hm u f) hnn
                    change ddH n 2 hm u f ∈ S n 1
                    exact ⟨hstable, hnn⟩
                | succ k =>
                    -- m = k + 3
                    have hfM : f ∈ M n (Nat.succ (Nat.succ (Nat.succ k))) := by
                      simpa [L] using hf.1
                    have hfderiv : ∀ i : Fin n, ⟨f.1.pderiv i, f.2.pderiv⟩ ∈ L n (Nat.succ (Nat.succ k)) := by
                      simpa [L] using hf.2
                    cases k with
                    | zero =>
                        -- m = 3
                        rcases directional_deriv_three_mem_L n hn f hf u hu with ⟨g, hgL, hg⟩
                        refine ⟨g, ?_, ?_⟩
                        · simpa using hgL
                        · simpa [dd] using hg
                    | succ k0 =>
                        -- m = k0 + 4
                        let m' : ℕ := Nat.succ (Nat.succ (Nat.succ k0))
                        let g : H n m' := ddH n (Nat.succ (Nat.succ (Nat.succ (Nat.succ k0)))) (by omega) u f
                        refine ⟨g, ?_, ?_⟩
                        · -- g ∈ L n m'
                          change g ∈ L n (Nat.succ (Nat.succ (Nat.succ k0)))
                          rw [L]
                          change g ∈ {x : H n (Nat.succ (Nat.succ (Nat.succ k0))) |
                            x ∈ M n (Nat.succ (Nat.succ (Nat.succ k0))) ∧
                              ∀ i : Fin n, ⟨x.1.pderiv i, x.2.pderiv⟩ ∈ L n (Nat.succ (Nat.succ k0))}
                          constructor
                          · -- g ∈ M n m'
                            change g ∈ M n (Nat.succ (Nat.succ (Nat.succ k0)))
                            rw [M]
                            change IsMConvex (g.1.support : Set (Fin n →₀ ℕ)) ∧
                              ∀ m : Fin n →₀ ℕ, 0 ≤ g.1.coeff m
                            constructor
                            · have hfhom : f.1.IsHomogeneous (Nat.succ (Nat.succ (Nat.succ (Nat.succ k0)))) := by
                                exact (MvPolynomial.mem_homogeneousSubmodule (Nat.succ (Nat.succ (Nat.succ (Nat.succ k0)))) f.1).mp f.2
                              have hnnf : ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m := by
                                change f ∈ M n (Nat.succ (Nat.succ (Nat.succ (Nat.succ k0)))) at hfM
                                exact hfM.2
                              have hMf : IsMConvex (f.1.support : Set (Fin n →₀ ℕ)) := by
                                change f ∈ M n (Nat.succ (Nat.succ (Nat.succ (Nat.succ k0)))) at hfM
                                exact hfM.1
                              change IsMConvex ((dd n u f.1).support : Set (Fin n →₀ ℕ))
                              simpa [dd] using Commons.Combinatorics.MvPolynomial.support_directionalDeriv_MConvex
                                n (Nat.succ (Nat.succ (Nat.succ (Nat.succ k0))))
                                (by omega) f.1 hfhom hnnf hMf u hu
                            · change ∀ a : Fin n →₀ ℕ, 0 ≤ (dd n u f.1).coeff a
                              intro a
                              have hnnf : ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m := by
                                change f ∈ M n (Nat.succ (Nat.succ (Nat.succ (Nat.succ k0)))) at hfM
                                exact hfM.2
                              exact dd_coeff_nonneg n u hu f.1 hnnf a
                          · -- partial derivatives of g are in L n (k0+2)
                            intro i
                            let fi : H n (Nat.succ (Nat.succ (Nat.succ k0))) :=
                              ⟨f.1.pderiv i, f.2.pderiv⟩
                            have hfiL : fi ∈ L n (Nat.succ (Nat.succ (Nat.succ k0))) := by
                              simpa [fi] using hfderiv i
                            have hih := ih (Nat.succ (Nat.succ (Nat.succ k0))) (by omega) (by omega) fi hfiL u hu
                            rcases hih with ⟨gi, hgiL, hgi⟩
                            -- ⟨pderiv i g.1, g.2.pderiv⟩ equals gi as an H-element
                            have hpd : MvPolynomial.pderiv i (dd n u f.1) = dd n u (MvPolynomial.pderiv i f.1) :=
                              dd_pderiv n u f.1 i
                            have heq : (⟨g.1.pderiv i, g.2.pderiv⟩ : H n (Nat.succ (Nat.succ k0))) = gi := by
                              apply Subtype.ext
                              change (dd n u f.1).pderiv i = gi.1
                              rw [hpd]
                              simpa [fi] using hgi.symm
                            simpa [g, heq] using hgiL
                        · -- g.1 = dd n u f.1
                          change (ddH n (Nat.succ (Nat.succ (Nat.succ (Nat.succ k0)))) (by omega) u f).1 = dd n u f.1
                          rfl
  rcases main d hd f hf u hu with ⟨g, hgL, hg⟩
  refine ⟨g, hgL, ?_⟩
  simpa [dd] using hg

end

end Commons.LorentzianPolynomials
