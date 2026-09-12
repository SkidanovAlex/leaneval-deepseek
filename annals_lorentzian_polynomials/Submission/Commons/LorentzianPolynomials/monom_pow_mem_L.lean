import Mathlib
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.LorentzianPolynomials.closure_strict_eq_L_of_degree_le_two

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Commons.LorentzianPolynomials

noncomputable section

private def mp_sumX (n : ℕ) : MvPolynomial (Fin n) ℝ := ∑ i : Fin n, MvPolynomial.X i

private lemma mp_sumX_isHomogeneous (n d : ℕ) : MvPolynomial.IsHomogeneous ((mp_sumX n) ^ d) d := by
  classical
  have hw : MvPolynomial.IsWeightedHomogeneous (1 : Fin n → ℕ) (mp_sumX n) 1 := by
    unfold mp_sumX
    refine MvPolynomial.IsWeightedHomogeneous.sum Finset.univ (fun i : Fin n => MvPolynomial.X i) 1 ?_
    intro i hi
    simpa using (MvPolynomial.isWeightedHomogeneous_X (R := ℝ) (1 : Fin n → ℕ) i)
  simpa [MvPolynomial.IsHomogeneous] using (hw.pow (n := d))

/-- `mp_sumXpow n d = (X₁ + ⋯ + Xₙ)^d` as an element of `H n d`. -/
private def mp_sumXpow (n d : ℕ) : H n d := ⟨(mp_sumX n) ^ d, by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact mp_sumX_isHomogeneous n d⟩

private lemma mp_sumXpow_apply (n d : ℕ) : (mp_sumXpow n d).1 = (mp_sumX n) ^ d := rfl

private lemma mp_sum_eq_weight_one (n : ℕ) (m : Fin n →₀ ℕ) :
    m.sum (fun _ x => x) = Finsupp.weight (1 : Fin n → ℕ) m := by
  rw [Finsupp.weight_eq_sum]
  rw [Finsupp.sum]
  simp
  exact Finset.sum_subset (Finset.subset_univ m.support) (by
    intro x hx hxnot
    exact Finsupp.notMem_support_iff.mp hxnot)

private lemma mp_multinomial_pos_real (n : ℕ) (m : Fin n →₀ ℕ) : 0 < (m.multinomial : ℝ) := by
  have hpos : 0 < m.multinomial := by
    rw [Finsupp.multinomial_eq]
    exact Nat.multinomial_pos (s := m.support) (f := m)
  exact_mod_cast hpos

/-- All coefficients of `(Σ Xᵢ)^d` at monomials of weight `d` are positive. -/
private lemma mp_sumXpow_mem_P (n d : ℕ) : mp_sumXpow n d ∈ P n d := by
  intro m hm
  have hcoeff := MvPolynomial.coeff_sum_X_pow_of_fintype (R := ℝ) (σ := Fin n) m d
  have hsum : m.sum (fun _ x => x) = Finsupp.weight (1 : Fin n → ℕ) m := mp_sum_eq_weight_one n m
  change 0 < (mp_sumXpow n d).1.coeff m
  rw [mp_sumXpow_apply, mp_sumX, hcoeff]
  rw [if_pos]
  · exact mp_multinomial_pos_real n m
  · rw [hsum]
    exact hm

private lemma mp_pderiv_sumX (n : ℕ) (i : Fin n) : pderiv i (mp_sumX n) = 1 := by
  classical
  unfold mp_sumX
  rw [map_sum]
  simp

private lemma mp_pderiv_sumX_pow (n d : ℕ) (i : Fin n) :
    pderiv i ((mp_sumX n) ^ d) = (d : ℝ) • (mp_sumX n) ^ (d - 1) := by
  rw [pderiv_pow, mp_pderiv_sumX, mul_one]
  rw [← (C_eq_coe_nat (σ := Fin n) (R := ℝ) d), smul_eq_C_mul]

private lemma mp_aeval_sumX (n : ℕ) (z : Fin n → ℍ) :
    MvPolynomial.aeval (((↑) : ℍ → ℂ) ∘ z) (mp_sumX n) = ∑ i : Fin n, (z i : ℂ) := by
  unfold mp_sumX
  simp [map_sum, Function.comp_def]

private lemma mp_aeval_sumX_pow (n d : ℕ) (z : Fin n → ℍ) :
    MvPolynomial.aeval (((↑) : ℍ → ℂ) ∘ z) ((mp_sumX n) ^ d) = (∑ i : Fin n, (z i : ℂ)) ^ d := by
  rw [map_pow]
  rw [mp_aeval_sumX n z]

private lemma mp_sum_eval_ne_zero_of_pos (n : ℕ) (hn : 0 < n) (z : Fin n → ℍ) :
    (∑ i : Fin n, (z i : ℂ)) ≠ 0 := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have him : 0 < (∑ i : Fin n, (z i : ℂ)).im := by
    rw [Complex.im_sum Finset.univ (fun i : Fin n => (z i : ℂ))]
    exact Finset.sum_pos (s := Finset.univ) (f := fun i : Fin n => (z i : ℂ).im)
      (fun i hi => by simpa using UpperHalfPlane.im_pos (z i)) Finset.univ_nonempty
  intro hzero
  rw [hzero] at him
  norm_num at him

/-- `(Σ Xᵢ)^d` is stable whenever `0 < n`. -/
private lemma mp_sumX_pow_stable (n d : ℕ) (hn : 0 < n) :
    IsStable ((mp_sumX n) ^ d) := by
  right
  intro z
  rw [mp_aeval_sumX_pow n d z]
  have hsum : (∑ i : Fin n, (z i : ℂ)) ≠ 0 := mp_sum_eval_ne_zero_of_pos n hn z
  by_cases hd : d = 0
  · subst hd
    simp
  · exact pow_ne_zero d hsum

/-! ## `IsStable`, `M`, `L` are closed under positive scalar multiplication -/

private lemma mp_IsStable_smul {n : ℕ} (c : ℝ) (hc : c ≠ 0) (p : MvPolynomial (Fin n) ℝ)
    (hp : IsStable p) : IsStable (c • p) := by
  rcases hp with h0 | hz
  · left
    rw [h0]
    simp
  · right
    intro z
    rw [map_smul]
    exact smul_ne_zero (r := c) (m := MvPolynomial.aeval (((↑) : ℍ → ℂ) ∘ z) p) hc (hz z)

private lemma mp_support_smul {n : ℕ} (c : ℝ) (hc : c ≠ 0) (p : MvPolynomial (Fin n) ℝ) :
    (c • p).support = p.support := by
  ext m
  simp [MvPolynomial.mem_support_iff, hc]

private lemma mp_IsMConvex_smul {n : ℕ} (c : ℝ) (hc : c ≠ 0) (p : MvPolynomial (Fin n) ℝ)
    (hJ : IsMConvex (p.support : Set (Fin n →₀ ℕ))) :
    IsMConvex ((c • p).support : Set (Fin n →₀ ℕ)) := by
  rw [mp_support_smul c hc p]
  exact hJ

/-- positive scalar multiples of Lorentzian polynomials are Lorentzian -/
private lemma mp_smul_mem_L (n d : ℕ) (c : ℝ) (hc : 0 < c) (f : H n d) (hf : f ∈ L n d) :
    c • f ∈ L n d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      cases d with
      | zero =>
          rcases hf with ⟨hstab, hnn⟩
          constructor
          · change IsStable (c • f.1)
            exact mp_IsStable_smul c (ne_of_gt hc) f.1 hstab
          · intro m
            change 0 ≤ (c • f.1).coeff m
            rw [MvPolynomial.coeff_smul]
            exact mul_nonneg (le_of_lt hc) (hnn m)
      | succ d1 =>
          cases d1 with
          | zero =>
              rcases hf with ⟨hstab, hnn⟩
              constructor
              · change IsStable (c • f.1)
                exact mp_IsStable_smul c (ne_of_gt hc) f.1 hstab
              · intro m
                change 0 ≤ (c • f.1).coeff m
                rw [MvPolynomial.coeff_smul]
                exact mul_nonneg (le_of_lt hc) (hnn m)
          | succ d2 =>
              cases d2 with
              | zero =>
                  rcases hf with ⟨hstab, hnn⟩
                  constructor
                  · change IsStable (c • f.1)
                    exact mp_IsStable_smul c (ne_of_gt hc) f.1 hstab
                  · intro m
                    change 0 ≤ (c • f.1).coeff m
                    rw [MvPolynomial.coeff_smul]
                    exact mul_nonneg (le_of_lt hc) (hnn m)
              | succ k =>
                  rcases hf with ⟨hM, hder⟩
                  rcases hM with ⟨hMcvx, hnn⟩
                  constructor
                  · constructor
                    · change IsMConvex (((c • f).1).support : Set (Fin n →₀ ℕ))
                      change IsMConvex (f.1.support : Set (Fin n →₀ ℕ)) at hMcvx
                      exact mp_IsMConvex_smul c (ne_of_gt hc) f.1 hMcvx
                    · intro m
                      change 0 ≤ (c • f.1).coeff m
                      rw [MvPolynomial.coeff_smul]
                      exact mul_nonneg (le_of_lt hc) (hnn m)
                  · intro i
                    have hdi : (⟨(c • f).1.pderiv i, (c • f).2.pderiv⟩ : H n (k + 2)) =
                        c • (⟨f.1.pderiv i, f.2.pderiv⟩ : H n (k + 2)) := by
                      apply Subtype.ext
                      change pderiv i (c • f.1) = c • (pderiv i f.1)
                      exact (MvPolynomial.pderiv (R := ℝ) i : MvPolynomial (Fin n) ℝ →ₗ[ℝ]
                        MvPolynomial (Fin n) ℝ).map_smul c f.1
                    rw [hdi]
                    exact ih (k + 2) (by omega) (⟨f.1.pderiv i, f.2.pderiv⟩ : H n (k + 2)) (hder i)

/-- `(Σ Xᵢ)^d ∈ L n d` for every degree `d` (whenever `0 < n`). -/
private lemma mp_sumXpow_mem_L (n : ℕ) (hn : 0 < n) :
    ∀ d : ℕ, (mp_sumXpow n d : H n d) ∈ L n d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      cases d with
      | zero =>
          constructor
          · exact mp_sumX_pow_stable n 0 hn
          · exact (P_subset_M n 0 (mp_sumXpow_mem_P n 0)).2
      | succ d1 =>
          cases d1 with
          | zero =>
              constructor
              · exact mp_sumX_pow_stable n 1 hn
              · exact (P_subset_M n 1 (mp_sumXpow_mem_P n 1)).2
          | succ d2 =>
              cases d2 with
              | zero =>
                  constructor
                  · exact mp_sumX_pow_stable n 2 hn
                  · exact (P_subset_M n 2 (mp_sumXpow_mem_P n 2)).2
              | succ k =>
                  constructor
                  · exact P_subset_M n (k + 3) (mp_sumXpow_mem_P n (k + 3))
                  · intro i
                    change (⟨(mp_sumXpow n (k + 3)).1.pderiv i,
                        (mp_sumXpow n (k + 3)).2.pderiv⟩ : H n (k + 2)) ∈ L n (k + 2)
                    have hder : (⟨(mp_sumXpow n (k + 3)).1.pderiv i,
                          (mp_sumXpow n (k + 3)).2.pderiv⟩ : H n (k + 2)) =
                        ((k + 3 : ℝ)) • mp_sumXpow n (k + 2) := by
                      apply Subtype.ext
                      change pderiv i ((mp_sumX n) ^ (k + 3)) =
                        ((k + 3 : ℝ)) • (mp_sumX n) ^ (k + 2)
                      have h := mp_pderiv_sumX_pow n (k + 3) i
                      simpa [mp_sumXpow, show k + 3 - 1 = k + 2 by omega] using h
                    rw [hder]
                    exact mp_smul_mem_L n (k + 2) (k + 3 : ℝ) (by positivity)
                      (mp_sumXpow n (k + 2)) (ih (k + 2) (by omega))


/-- A polynomial with all degree-`d` coefficients positive is not the zero polynomial,
provided there is at least one monomial of degree `d` (i.e. `0 < n`). -/
private lemma mp_P_mem_ne_zero {n d : ℕ} (hn : 0 < n) (f : H n d) (hf : f ∈ P n d) :
    f ≠ 0 := by
  intro hzero
  have hz : f.1 = (0 : MvPolynomial (Fin n) ℝ) := by
    rw [hzero]
    rfl
  let i : Fin n := ⟨0, hn⟩
  let m : Fin n →₀ ℕ := Finsupp.single i d
  have hw : Finsupp.weight (1 : Fin n → ℕ) m = d := by
    rw [Finsupp.weight_single]
    simp
  have hpos : 0 < f.1.coeff m := hf m hw
  have hzero_coeff : f.1.coeff m = 0 := by
    rw [hz]
    simp
  simp [hzero_coeff] at hpos

theorem monom_pow_mem_L (n d : ℕ) (hn : 0 < n) :
    ∃ f : Commons.LorentzianPolynomials.H n d,
      f ∈ Commons.LorentzianPolynomials.L n d ∧ f ≠ 0 := by
  exact ⟨mp_sumXpow n d, mp_sumXpow_mem_L n hn d,
    mp_P_mem_ne_zero hn (mp_sumXpow n d) (mp_sumXpow_mem_P n d)⟩

end

end Commons.LorentzianPolynomials
