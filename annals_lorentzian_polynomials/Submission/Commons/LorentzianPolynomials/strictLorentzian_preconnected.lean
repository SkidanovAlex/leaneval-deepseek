import Mathlib
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.closure_strict_eq_L_of_degree_le_two
import Submission.Commons.LorentzianPolynomials.smul_mem_strict
import Submission.Commons.LorentzianPolynomials.substS_mem_P
import Submission.Commons.LorentzianPolynomials.substS_at_zero
import Submission.Commons.LorentzianPolynomials.substS_at_one
import Submission.Commons.LorentzianPolynomials.L_mem_nonneg
import Submission.Commons.LorentzianPolynomials.P_subset_M
import Submission.Commons.LorentzianPolynomials.pderiv_stable_mem_S
import Submission.Commons.LorentzianPolynomials.subst_coeff_continuous
import Submission.Commons.LorentzianPolynomials.nuij_smoothing
import Submission.Commons.LorentzianPolynomials.flow_substS_mem_L
import Submission.Commons.LinearAlgebra.Matrix.strictQuad_preconnected
import Submission.Commons.Algebra.MvPolynomial.homogeneous_coeff_equiv

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Commons.LorentzianPolynomials

noncomputable section

/-! ## Membership depends only on the underlying polynomial -/

private lemma mem_P_of_val_eq {n d : ℕ} {f g : H n d} (hfg : f.1 = g.1) : g ∈ P n d → f ∈ P n d := by
  intro hg m hm
  change 0 < f.1.coeff m
  rw [hfg]
  exact hg m hm

private lemma mem_S_of_val_eq {n d : ℕ} {f g : H n d} (hfg : f.1 = g.1) : g ∈ S n d → f ∈ S n d := by
  intro hg
  rcases hg with ⟨hstab, hnon⟩
  constructor
  · change IsStable f.1
    simpa [hfg] using hstab
  · intro m
    change 0 ≤ f.1.coeff m
    rw [hfg]
    exact hnon m

private lemma mem_M_of_val_eq {n d : ℕ} {f g : H n d} (hfg : f.1 = g.1) : g ∈ M n d → f ∈ M n d := by
  intro hg
  rcases hg with ⟨hconv, hnon⟩
  constructor
  · change IsMConvex (f.1.support : Set (Fin n →₀ ℕ))
    change IsMConvex (g.1.support : Set (Fin n →₀ ℕ)) at hconv
    simpa [hfg] using hconv
  · intro m
    change 0 ≤ f.1.coeff m
    rw [hfg]
    exact hnon m

private lemma mem_Ŀ_of_val_eq {n d : ℕ} {f g : H n d} (hfg : f.1 = g.1) : g ∈ Ŀ n d → f ∈ Ŀ n d := by
  intro hg
  induction d using Nat.strong_induction_on with
  | h d ih =>
      cases d with
      | zero =>
          change f ∈ P n 0
          change g ∈ P n 0 at hg
          exact mem_P_of_val_eq hfg hg
      | succ d1 =>
          cases d1 with
          | zero =>
              change f ∈ P n 1
              change g ∈ P n 1 at hg
              exact mem_P_of_val_eq hfg hg
          | succ d2 =>
              cases d2 with
              | zero =>
                  -- Ŀ n 2 : use the explicit shape
                  rcases hg with ⟨hgP, hunit, hcard⟩
                  change f ∈ {f : H n 2 | f ∈ P n 2 ∧ IsUnit f.hessian ∧
                    (f.hessian.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 1}
                  constructor
                  · exact mem_P_of_val_eq hfg hgP
                  · have hhes : g.hessian = f.hessian := by
                      classical
                      unfold H.hessian
                      funext i j
                      by_cases hij : i = j
                      · subst j
                        simp [hfg.symm]
                      · simp [hfg.symm, hij]
                    constructor
                    · simpa [hhes] using hunit
                    · simpa [hhes] using hcard
              | succ k =>
                  change f ∈ {f : H n (k + 3) | f ∈ P n (k + 3) ∧
                    ∀ i : Fin n, (⟨f.1.pderiv i, f.2.pderiv⟩ : H n (k + 2)) ∈ Ŀ n (k + 2)}
                  change g ∈ {g : H n (k + 3) | g ∈ P n (k + 3) ∧
                    ∀ i : Fin n, (⟨g.1.pderiv i, g.2.pderiv⟩ : H n (k + 2)) ∈ Ŀ n (k + 2)} at hg
                  rcases hg with ⟨hgP, hder⟩
                  constructor
                  · exact mem_P_of_val_eq hfg hgP
                  · intro i
                    exact ih (k + 2) (by omega) (by simp [hfg]) (hder i)

private lemma mem_L_of_val_eq {n d : ℕ} {f g : H n d} (hfg : f.1 = g.1) : g ∈ L n d → f ∈ L n d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro hg
      cases d with
      | zero =>
          have : S n 0 = L n 0 := by rfl
          rw [← this] at hg ⊢
          exact mem_S_of_val_eq hfg hg
      | succ d0 =>
          cases d0 with
          | zero =>
              have : S n 1 = L n 1 := by rfl
              rw [← this] at hg ⊢
              exact mem_S_of_val_eq hfg hg
          | succ d1 =>
              cases d1 with
              | zero =>
                  have : S n 2 = L n 2 := by rfl
                  rw [← this] at hg ⊢
                  exact mem_S_of_val_eq hfg hg
              | succ k =>
                  -- d = k+3 ≥ 3
                  change g ∈ {g : H n (k + 3) | g ∈ M n (k + 3) ∧
                    ∀ i : Fin n, (⟨g.1.pderiv i, g.2.pderiv⟩ : H n (k + 2)) ∈ L n (k + 2)} at hg
                  rcases hg with ⟨hgM, hder⟩
                  change f ∈ {f : H n (k + 3) | f ∈ M n (k + 3) ∧
                    ∀ i : Fin n, (⟨f.1.pderiv i, f.2.pderiv⟩ : H n (k + 2)) ∈ L n (k + 2)}
                  constructor
                  · exact mem_M_of_val_eq hfg hgM
                  · intro i
                    exact ih (k + 2) (by omega) (f := ⟨f.1.pderiv i, f.2.pderiv⟩)
                      (g := ⟨g.1.pderiv i, g.2.pderiv⟩) (by simp [hfg]) (hder i)
/-! ## The model element `(Σ Xᵢ)^d` and its memberships -/

/-- `sumX n = X₁ + ⋯ + Xₙ`. -/
private def sumX (n : ℕ) : MvPolynomial (Fin n) ℝ := ∑ i : Fin n, MvPolynomial.X i

private lemma sumX_isHomogeneous (n d : ℕ) : MvPolynomial.IsHomogeneous ((sumX n) ^ d) d := by
  classical
  have hw : MvPolynomial.IsWeightedHomogeneous (1 : Fin n → ℕ) (sumX n) 1 := by
    unfold sumX
    refine MvPolynomial.IsWeightedHomogeneous.sum Finset.univ (fun i : Fin n => MvPolynomial.X i) 1 ?_
    intro i hi
    simpa using (MvPolynomial.isWeightedHomogeneous_X (R := ℝ) (1 : Fin n → ℕ) i)
  simpa [MvPolynomial.IsHomogeneous] using (hw.pow (n := d))

/-- `sumXpow n d = (X₁ + ⋯ + Xₙ)^d` as an element of `H n d`. -/
private noncomputable def sumXpow (n d : ℕ) : H n d := ⟨(sumX n) ^ d, by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact sumX_isHomogeneous n d⟩

private lemma sumXpow_apply (n d : ℕ) : (sumXpow n d).1 = (sumX n) ^ d := rfl

private lemma sumX_weight (n : ℕ) (m : Fin n →₀ ℕ) :
    m.sum (fun _ x => x) = Finsupp.weight (1 : Fin n → ℕ) m := by
  rw [Finsupp.weight_eq_sum]
  rw [Finsupp.sum]
  simp
  exact Finset.sum_subset (Finset.subset_univ m.support) (by
    intro x hx hxnot
    exact Finsupp.notMem_support_iff.mp hxnot)

private lemma multinomial_pos_real (n : ℕ) (m : Fin n →₀ ℕ) : 0 < (m.multinomial : ℝ) := by
  have hpos : 0 < m.multinomial := by
    rw [Finsupp.multinomial_eq]
    exact Nat.multinomial_pos (s := m.support) (f := m)
  exact_mod_cast hpos

private lemma sumXpow_coeff_pos (n d : ℕ) (m : Fin n →₀ ℕ) (hm : Finsupp.weight (1 : Fin n → ℕ) m = d) :
    0 < (sumXpow n d).1.coeff m := by
  have hcoeff := MvPolynomial.coeff_sum_X_pow_of_fintype (R := ℝ) (σ := Fin n) m d
  have hsum : m.sum (fun _ x => x) = Finsupp.weight (1 : Fin n → ℕ) m := sumX_weight n m
  rw [sumXpow_apply, sumX, hcoeff]
  rw [if_pos]
  · exact multinomial_pos_real n m
  · rw [hsum]
    exact hm

private lemma sumXpow_coeff_nonneg (n d : ℕ) (m : Fin n →₀ ℕ) : 0 ≤ (sumXpow n d).1.coeff m := by
  by_cases hm : Finsupp.weight (1 : Fin n → ℕ) m = d
  · exact le_of_lt (sumXpow_coeff_pos n d m hm)
  · have hhom : (sumXpow n d).1.IsHomogeneous d := (sumXpow n d).2
    have hwh : (sumXpow n d).1.IsWeightedHomogeneous (1 : Fin n → ℕ) d := by
      simpa [MvPolynomial.IsHomogeneous] using hhom
    have hc : (sumXpow n d).1.coeff m = 0 :=
      MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero (w := (1 : Fin n → ℕ))
        (φ := (sumXpow n d).1) (n := d) hwh m hm
    rw [hc]

private lemma pderiv_sumX (n : ℕ) (i : Fin n) : pderiv i (sumX n) = 1 := by
  classical
  unfold sumX
  rw [map_sum]
  simp

private lemma pderiv_sumX_pow (n d : ℕ) (i : Fin n) :
    pderiv i ((sumX n) ^ d) = (d : ℝ) • (sumX n) ^ (d - 1) := by
  rw [pderiv_pow, pderiv_sumX, mul_one]
  rw [← (C_eq_coe_nat (σ := Fin n) (R := ℝ) d), smul_eq_C_mul]

private lemma aeval_sumX (n : ℕ) (z : Fin n → ℍ) :
    MvPolynomial.aeval (((↑) : ℍ → ℂ) ∘ z) (sumX n) = ∑ i : Fin n, (z i : ℂ) := by
  unfold sumX
  simp [map_sum, Function.comp_def]

private lemma aeval_sumX_pow (n d : ℕ) (z : Fin n → ℍ) :
    MvPolynomial.aeval (((↑) : ℍ → ℂ) ∘ z) ((sumX n) ^ d) = (∑ i : Fin n, (z i : ℂ)) ^ d := by
  rw [map_pow]
  rw [aeval_sumX n z]

private lemma spc_sum_eval_ne_zero_of_pos (n : ℕ) (hn : 0 < n) (z : Fin n → ℍ) :
    (∑ i : Fin n, (z i : ℂ)) ≠ 0 := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have him : 0 < (∑ i : Fin n, (z i : ℂ)).im := by
    rw [Complex.im_sum Finset.univ (fun i : Fin n => (z i : ℂ))]
    exact Finset.sum_pos (s := Finset.univ) (f := fun i : Fin n => (z i : ℂ).im)
      (fun i hi => by simpa using UpperHalfPlane.im_pos (z i)) Finset.univ_nonempty
  intro hzero
  rw [hzero] at him
  norm_num at him

private lemma sumX_pow_stable (n d : ℕ) (hn : 0 < n) : IsStable ((sumX n) ^ d) := by
  right
  intro z
  rw [aeval_sumX_pow n d z]
  have hsum : (∑ i : Fin n, (z i : ℂ)) ≠ 0 := spc_sum_eval_ne_zero_of_pos n hn z
  by_cases hd : d = 0
  · subst hd
    simp
  · exact pow_ne_zero d hsum

private lemma IsStable_smul {n : ℕ} (c : ℝ) (hc : c ≠ 0) (p : MvPolynomial (Fin n) ℝ)
    (hp : IsStable p) : IsStable (c • p) := by
  rcases hp with h0 | hz
  · left
    rw [h0]
    simp
  · right
    intro z
    rw [map_smul]
    exact smul_ne_zero (r := c) (m := MvPolynomial.aeval (((↑) : ℍ → ℂ) ∘ z) p) hc (hz z)

private lemma support_smul {n : ℕ} (c : ℝ) (hc : c ≠ 0) (p : MvPolynomial (Fin n) ℝ) :
    (c • p).support = p.support := by
  ext m
  simp [MvPolynomial.mem_support_iff, hc]

private lemma IsMConvex_smul {n : ℕ} (c : ℝ) (hc : c ≠ 0) (p : MvPolynomial (Fin n) ℝ)
    (hJ : IsMConvex (p.support : Set (Fin n →₀ ℕ))) :
    IsMConvex ((c • p).support : Set (Fin n →₀ ℕ)) := by
  rw [support_smul c hc p]
  exact hJ

/-- positive scalar multiples of Lorentzian polynomials are Lorentzian -/
private lemma spc_smul_mem_L (n d : ℕ) (c : ℝ) (hc : 0 < c) (f : H n d) (hf : f ∈ L n d) :
    c • f ∈ L n d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      cases d with
      | zero =>
          rcases hf with ⟨hstab, hnn⟩
          constructor
          · change IsStable (c • f.1)
            exact IsStable_smul c (ne_of_gt hc) f.1 hstab
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
                exact IsStable_smul c (ne_of_gt hc) f.1 hstab
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
                    exact IsStable_smul c (ne_of_gt hc) f.1 hstab
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
                      exact IsMConvex_smul c (ne_of_gt hc) f.1 hMcvx
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
private lemma sumXpow_mem_L (n : ℕ) (hn : 0 < n) :
    ∀ d : ℕ, (sumXpow n d : H n d) ∈ L n d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      cases d with
      | zero =>
          have hS : (sumXpow n 0 : H n 0) ∈ S n 0 := by
            constructor
            · exact sumX_pow_stable n 0 hn
            · intro m
              exact sumXpow_coeff_nonneg n 0 m
          have : S n 0 = L n 0 := by rfl
          simpa [this] using hS
      | succ d1 =>
          cases d1 with
          | zero =>
              have hS : (sumXpow n 1 : H n 1) ∈ S n 1 := by
                constructor
                · exact sumX_pow_stable n 1 hn
                · intro m
                  exact sumXpow_coeff_nonneg n 1 m
              have : S n 1 = L n 1 := by rfl
              simpa [this] using hS
          | succ d2 =>
              cases d2 with
              | zero =>
                  have hS : (sumXpow n 2 : H n 2) ∈ S n 2 := by
                    constructor
                    · exact sumX_pow_stable n 2 hn
                    · intro m
                      exact sumXpow_coeff_nonneg n 2 m
                  have : S n 2 = L n 2 := by rfl
                  simpa [this] using hS
              | succ k =>
                  constructor
                  · exact P_subset_M n (k + 3) (by
                      intro m hm
                      exact sumXpow_coeff_pos n (k + 3) m hm)
                  · intro i
                    change (⟨(sumXpow n (k + 3)).1.pderiv i,
                        (sumXpow n (k + 3)).2.pderiv⟩ : H n (k + 2)) ∈ L n (k + 2)
                    have hder : (⟨(sumXpow n (k + 3)).1.pderiv i,
                          (sumXpow n (k + 3)).2.pderiv⟩ : H n (k + 2)) =
                        ((k + 3 : ℝ)) • sumXpow n (k + 2) := by
                      apply Subtype.ext
                      change pderiv i ((sumX n) ^ (k + 3)) =
                        ((k + 3 : ℝ)) • (sumX n) ^ (k + 2)
                      have h := pderiv_sumX_pow n (k + 3) i
                      simpa [sumXpow, show k + 3 - 1 = k + 2 by omega] using h
                    rw [hder]
                    exact spc_smul_mem_L n (k + 2) (k + 3 : ℝ) (by positivity)
                      (sumXpow n (k + 2)) (ih (k + 2) (by omega))
/-! ## `P n d` is convex -/

private lemma P_convex (n d : ℕ) : Convex ℝ (P n d) := by
  classical
  intro f hf g hg a b ha hb hab
  intro m hm
  rw [show (a • f + b • g).1 = a • f.1 + b • g.1 by rfl]
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
    smul_eq_mul, smul_eq_mul]
  have hfm : 0 < f.1.coeff m := hf m hm
  have hgm : 0 < g.1.coeff m := hg m hm
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simp [ha0, hb1]
    exact hgm
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have h1 : 0 < a * f.1.coeff m := mul_pos hapos hfm
    have h2 : 0 ≤ b * g.1.coeff m := mul_nonneg hb (le_of_lt hgm)
    linarith

private lemma Ŀ_eq_P_of_le_one (n d : ℕ) (hd : d ≤ 1) : Ŀ n d = P n d := by
  rcases d with _ | d
  · rfl
  · rcases d with _ | d
    · rfl
    · exfalso
      omega

/-- Degrees 0 and 1 are preconnected. -/
private lemma preconnected_of_degree_le_one (n d : ℕ) (hd : d ≤ 1) :
    IsPreconnected (Ŀ n d) := by
  rw [Ŀ_eq_P_of_le_one n d hd]
  exact (P_convex n d).isPreconnected
/-! ## Degree 2: transfer from the strictly Lorentzian quadratic matrices -/

private lemma hessian_mem_strictQuad {n : ℕ} {f : H n 2} (hf : f ∈ Ŀ n 2) :
    f.hessian ∈ Commons.LinearAlgebra.Matrix.strictQuadSet n := by
  classical
  have hf2 : f ∈ {f : H n 2 | f ∈ P n 2 ∧ IsUnit f.hessian ∧
      (f.hessian.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 1} := by
    simpa [Ŀ] using hf
  rcases hf2 with ⟨hP, hunit, hcard⟩
  unfold Commons.LinearAlgebra.Matrix.strictQuadSet
  constructor
  · exact hessian_symm n f
  · constructor
    · exact (mem_P_iff_hessian_pos n f).mp hP
    · exact ⟨hunit, hcard⟩

private lemma quadricOfMatrix_mem_Ŀ_of_strictQuad {n : ℕ} (hn : 0 < n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ Commons.LinearAlgebra.Matrix.strictQuadSet n) :
    quadricOfMatrix n A ∈ Ŀ n 2 := by
  classical
  rcases hA with ⟨hAsymm, hApos, hAunit, hAcard⟩
  have hP : quadricOfMatrix n A ∈ P n 2 := by
    rw [mem_P_iff_hessian_pos]
    rw [hessian_quadricOfMatrix_symm n A hAsymm]
    exact hApos
  have hq : IsUnit (quadricOfMatrix n A).hessian ∧
      ((quadricOfMatrix n A).hessian.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 1 := by
    rw [hessian_quadricOfMatrix_symm n A hAsymm]
    exact ⟨hAunit, hAcard⟩
  change quadricOfMatrix n A ∈ {f : H n 2 | f ∈ P n 2 ∧ IsUnit f.hessian ∧
      (f.hessian.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 1}
  simpa [Ŀ, hP, hq]

private lemma joinedIn_Ŀ2 (n : ℕ) (hn : 0 < n) :
    ∀ f ∈ Ŀ n 2, ∀ g ∈ Ŀ n 2, JoinedIn (Ŀ n 2) f g := by
  classical
  intro f hf g hg
  let Hf : Matrix (Fin n) (Fin n) ℝ := f.hessian
  let Hg : Matrix (Fin n) (Fin n) ℝ := g.hessian
  have hHf : Hf ∈ Commons.LinearAlgebra.Matrix.strictQuadSet n := by
    simpa [Hf] using hessian_mem_strictQuad hf
  have hHg : Hg ∈ Commons.LinearAlgebra.Matrix.strictQuadSet n := by
    simpa [Hg] using hessian_mem_strictQuad hg
  have hJoined : JoinedIn (Commons.LinearAlgebra.Matrix.strictQuadSet n) Hf Hg := by
    have hpc := Commons.LinearAlgebra.Matrix.strictQuad_preconnected_set n hn
    rw [isPathConnected_iff] at hpc
    exact hpc.2 Hf hHf Hg hHg
  let φ : Matrix (Fin n) (Fin n) ℝ → H n 2 := quadricOfMatrix n
  have hφ : Continuous φ := continuous_quadricOfMatrix n
  have hmap : JoinedIn (φ '' Commons.LinearAlgebra.Matrix.strictQuadSet n) (φ Hf) (φ Hg) :=
    hJoined.map hφ
  have hφHf : φ Hf = f := by
    simp [φ, Hf, quadricOfMatrix_hessian n f]
  have hφHg : φ Hg = g := by
    simp [φ, Hg, quadricOfMatrix_hessian n g]
  have himg_Ŀ : φ '' Commons.LinearAlgebra.Matrix.strictQuadSet n ⊆ Ŀ n 2 := by
    rintro p ⟨A, hA, rfl⟩
    exact quadricOfMatrix_mem_Ŀ_of_strictQuad hn hA
  have hmono : JoinedIn (Ŀ n 2) (φ Hf) (φ Hg) := hmap.mono himg_Ŀ
  simpa [hφHf, hφHg] using hmono

/-- The degree-two strictly Lorentzian set is path connected. -/
private lemma Ŀ2_nonempty (n : ℕ) (hn : 0 < n) : (Ŀ n 2).Nonempty := by
  classical
  let hub : Matrix (Fin n) (Fin n) ℝ := fun i j => if i = j then (1 / 2 : ℝ) else 1
  refine ⟨quadricOfMatrix n hub, ?_⟩
  have hhub : hub ∈ Commons.LinearAlgebra.Matrix.strictQuadSet n :=
    Commons.LinearAlgebra.Matrix.hub_end_mem hn
  simpa [hub] using quadricOfMatrix_mem_Ŀ_of_strictQuad hn hhub

private lemma pathConnected_degreeTwo (n : ℕ) (hn : 0 < n) : IsPathConnected (Ŀ n 2) := by
  rw [isPathConnected_iff]
  constructor
  · exact Ŀ2_nonempty n hn
  · exact joinedIn_Ŀ2 n hn

private lemma preconnected_degreeTwo (n : ℕ) (hn : 0 < n) : IsPreconnected (Ŀ n 2) :=
  (IsPathConnected.isConnected (pathConnected_degreeTwo n hn)).isPreconnected
private lemma spc_one_var_weight_eq_single {m : ℕ} {m' : Fin 1 →₀ ℕ}
    (hm : Finsupp.weight (1 : Fin 1 → ℕ) m' = m) : m' = Finsupp.single (0 : Fin 1) m := by
  apply Finsupp.ext
  intro i
  have hi : i = 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)
  subst i
  simp
  have hw : (∑ x : Fin 1, m' x) = m := by
    rw [Finsupp.weight_eq_sum] at hm
    simpa using hm
  have hsum0 : (∑ x : Fin 1, m' x) = m' 0 := by
    rw [Finset.sum_eq_single (0 : Fin 1)]
    · intro b hb hb0
      have hb0' : b = 0 := Fin.ext (Nat.lt_one_iff.mp b.isLt)
      exact (hb0 hb0').elim
    · intro h0
      exact False.elim (h0 (Finset.mem_univ (0 : Fin 1)))
  simpa [hsum0] using hw

private lemma spc_one_var_coeff_of_mem_P {d : ℕ} {f : H 1 d} (hf : f ∈ P 1 d) :
    0 < f.1.coeff (Finsupp.single (0 : Fin 1) d) := by
  exact hf (Finsupp.single (0 : Fin 1) d) (by simp [Finsupp.weight_single])

private lemma spc_one_var_mem_P_iff_coeff_pos (m : ℕ) (f : H 1 m) :
    f ∈ P 1 m ↔ 0 < f.1.coeff (Finsupp.single (0 : Fin 1) m) := by
  constructor
  · intro hf
    exact spc_one_var_coeff_of_mem_P (d := m) hf
  · intro hpos m' hm
    have hm' : m' = Finsupp.single (0 : Fin 1) m := spc_one_var_weight_eq_single (m := m) (m' := m') hm
    simpa [hm'] using hpos

private lemma spc_one_var_coeff_pderiv (k : ℕ) (f : H 1 (k + 1)) :
    (pderiv (0 : Fin 1) f.1).coeff (Finsupp.single (0 : Fin 1) k) =
      (k + 1 : ℝ) * f.1.coeff (Finsupp.single (0 : Fin 1) (k + 1)) := by
  have hsum : Finsupp.single (0 : Fin 1) k + Finsupp.single (0 : Fin 1) 1 = Finsupp.single (0 : Fin 1) (k + 1) := by
    apply Finsupp.ext
    intro i
    fin_cases i
    simp
  calc
    (pderiv (0 : Fin 1) f.1).coeff (Finsupp.single (0 : Fin 1) k)
        = coeff (Finsupp.single (0 : Fin 1) k + Finsupp.single (0 : Fin 1) 1) f.1 *
            ((Finsupp.single (0 : Fin 1) k) (0 : Fin 1) + 1) := by
            exact MvPolynomial.coeff_pderiv (p := f.1) (i := (0 : Fin 1)) (m := Finsupp.single (0 : Fin 1) k)
    _ = coeff (Finsupp.single (0 : Fin 1) (k + 1)) f.1 * (k + 1) := by
            congr 1
            · exact congrArg (fun m : Fin 1 →₀ ℕ => coeff m f.1) hsum
            · simp
    _ = (k + 1 : ℝ) * coeff (Finsupp.single (0 : Fin 1) (k + 1)) f.1 := by ring

private lemma spc_one_var_pderiv_mem_P (k : ℕ) (f : H 1 (k + 1)) (hf : f ∈ P 1 (k + 1)) :
    (⟨f.1.pderiv (0 : Fin 1), f.2.pderiv⟩ : H 1 k) ∈ P 1 k := by
  apply (spc_one_var_mem_P_iff_coeff_pos k (⟨f.1.pderiv (0 : Fin 1), f.2.pderiv⟩ : H 1 k)).2
  change 0 < (pderiv (0 : Fin 1) f.1).coeff (Finsupp.single (0 : Fin 1) k)
  rw [spc_one_var_coeff_pderiv k f]
  have hc : 0 < f.1.coeff (Finsupp.single (0 : Fin 1) (k + 1)) :=
    spc_one_var_coeff_of_mem_P (d := k + 1) hf
  positivity

private lemma spc_hessian_one (f : H 1 2) :
    f.hessian = Matrix.diagonal (fun _ : Fin 1 => 2 * f.1.coeff (Finsupp.single (0 : Fin 1) 2)) := by
  ext i j
  fin_cases i <;> fin_cases j
  change (if (0 : Fin 1) = 0 then 2 * f.1.coeff (Finsupp.single (0 : Fin 1) 2)
      else f.1.coeff (Finsupp.single (0 : Fin 1) 1 + Finsupp.single (0 : Fin 1) 1)) =
    (2 * f.1.coeff (Finsupp.single (0 : Fin 1) 2))
  simp

private lemma spc_prod_fin1 (c : ℝ) : (∏ i : Fin 1, c) = c := by
  rw [Fin.prod_univ_one]

private lemma spc_det_one_diag (c : ℝ) :
    (Matrix.diagonal (fun _ : Fin 1 => c) : Matrix (Fin 1) (Fin 1) ℝ).det = c := by
  rw [Matrix.det_diagonal]
  exact spc_prod_fin1 c

private lemma spc_charpoly_one_diag (c : ℝ) :
    (Matrix.diagonal (fun _ : Fin 1 => c) : Matrix (Fin 1) (Fin 1) ℝ).charpoly =
      Polynomial.X - Polynomial.C c := by
  rw [Matrix.charpoly_diagonal]
  rw [Fin.prod_univ_one]

private lemma spc_roots_pos_card_one (c : ℝ) (hc : 0 < c) :
    ((Polynomial.X - Polynomial.C c : Polynomial ℝ).roots.filter (fun r : ℝ => 0 < r)).card = 1 := by
  rw [Polynomial.roots_X_sub_C]
  rw [Multiset.filter_singleton]
  simp [hc]

private lemma spc_Ŀ1_eq_P1_of_degree_two : Ŀ 1 2 = P 1 2 := by
  apply le_antisymm
  · intro f hf
    exact hf.1
  · intro f hf
    have hpos : 0 < f.1.coeff (Finsupp.single (0 : Fin 1) 2) := spc_one_var_coeff_of_mem_P (d := 2) hf
    have h2pos : 0 < 2 * f.1.coeff (Finsupp.single (0 : Fin 1) 2) := by positivity
    change f ∈ {f : H 1 2 | f ∈ P 1 2 ∧ IsUnit f.hessian ∧
      (f.hessian.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 1}
    constructor
    · exact hf
    · constructor
      · have hhess : f.hessian = Matrix.diagonal (fun _ : Fin 1 => 2 * f.1.coeff (Finsupp.single (0 : Fin 1) 2)) :=
          spc_hessian_one f
        rw [Matrix.isUnit_iff_isUnit_det]
        rw [hhess, Matrix.det_diagonal]
        rw [Fin.prod_univ_one]
        exact isUnit_iff_ne_zero.mpr (ne_of_gt h2pos)
      · have hhess : f.hessian = Matrix.diagonal (fun _ : Fin 1 => 2 * f.1.coeff (Finsupp.single (0 : Fin 1) 2)) :=
          spc_hessian_one f
        rw [hhess]
        rw [spc_charpoly_one_diag]
        exact spc_roots_pos_card_one (2 * f.1.coeff (Finsupp.single (0 : Fin 1) 2)) h2pos

private lemma spc_Ŀ1_eq_P1 (d : ℕ) : Ŀ 1 d = P 1 d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      cases d with
      | zero => rfl
      | succ d1 =>
          cases d1 with
          | zero => rfl
          | succ d2 =>
              cases d2 with
              | zero => exact spc_Ŀ1_eq_P1_of_degree_two
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
                        spc_one_var_pderiv_mem_P (k + 2) f hf
                      have hi := ih (k + 2) (by omega)
                      rw [hi]
                      exact hderP


/-! ## The S-flow substitution `S(θ,f) = f((1−θ)X + θ·(ΣX))` -/

/-- The substituted variable `(1−θ)·X j + θ·(Σᵢ Xᵢ)`. -/
private def flowSVar (n : ℕ) (θ : ℝ) (j : Fin n) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C (1 - θ) * MvPolynomial.X j +
    MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i)

private lemma flowSVar_isHomogeneous_one (n : ℕ) (θ : ℝ) (j : Fin n) :
    (flowSVar n θ j).IsHomogeneous 1 := by
  have hXj : (MvPolynomial.X j : MvPolynomial (Fin n) ℝ).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X (σ := Fin n) (R := ℝ) j
  have hC1 : (MvPolynomial.C (1 - θ) : MvPolynomial (Fin n) ℝ).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C (σ := Fin n) (R := ℝ) (1 - θ)
  have hsum : ((∑ i : Fin n, MvPolynomial.X i) : MvPolynomial (Fin n) ℝ).IsHomogeneous 1 := by
    exact MvPolynomial.IsHomogeneous.sum Finset.univ (fun i : Fin n => MvPolynomial.X i) 1
      (fun i hi => MvPolynomial.isHomogeneous_X (σ := Fin n) (R := ℝ) i)
  have hC2 : (MvPolynomial.C θ : MvPolynomial (Fin n) ℝ).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C (σ := Fin n) (R := ℝ) θ
  unfold flowSVar
  exact (MvPolynomial.IsHomogeneous.mul (φ := MvPolynomial.C (1 - θ)) hC1 (ψ := MvPolynomial.X j) hXj).add
    (MvPolynomial.IsHomogeneous.mul (φ := MvPolynomial.C θ) hC2 (ψ := ∑ i : Fin n, MvPolynomial.X i) hsum)

/-- `S(θ,f) = f((1−θ)·X + θ·(Σᵢ Xᵢ))` as an element of `H n d`. -/
private noncomputable def flowS {n d : ℕ} (θ : ℝ) (f : H n d) : H n d :=
  ⟨MvPolynomial.aeval (fun j : Fin n => flowSVar n θ j) f.1, by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    have hhom := MvPolynomial.IsHomogeneous.aeval (hφ := f.2)
      (g := fun j : Fin n => flowSVar n θ j) (flowSVar_isHomogeneous_one n θ)
    simpa [mul_comm] using hhom⟩

private lemma flowS_apply (n d : ℕ) (θ : ℝ) (f : H n d) :
    (flowS (n := n) (d := d) θ f).1 = MvPolynomial.aeval (fun j : Fin n => flowSVar n θ j) f.1 := rfl

private lemma flowSVar_at_one (n : ℕ) (j : Fin n) :
    flowSVar n 1 j = ∑ i : Fin n, MvPolynomial.X i := by
  unfold flowSVar
  simp

private lemma flowSVar_at_zero (n : ℕ) (j : Fin n) : flowSVar n 0 j = MvPolynomial.X j := by
  unfold flowSVar
  simp

/-- `S(0,f) = f`. -/
private lemma flowS_zero (n d : ℕ) (f : H n d) : flowS (n := n) (d := d) 0 f = f := by
  apply Subtype.ext
  rw [flowS_apply]
  have hfun : (fun j : Fin n => flowSVar n 0 j) = (fun j : Fin n => MvPolynomial.X j) := by
    funext j
    exact flowSVar_at_zero n j
  rw [hfun]
  exact MvPolynomial.aeval_X_left_apply f.1

/-- `S(θ,f)` stays in `P` for `0 ≤ θ ≤ 1`. -/
private lemma flowS_mem_P (n d : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (f : H n d) (hf : f ∈ P n d) : flowS (n := n) (d := d) θ f ∈ P n d := by
  rcases substS_mem_P n d θ hθ0 hθ1 f hf with ⟨g, hgP, hgval⟩
  exact mem_P_of_val_eq (by
    rw [flowS_apply]
    simpa [flowSVar] using hgval.symm) hgP

/-- `S(θ,f)` stays in `L` for `0 ≤ θ ≤ 1` (flow). -/
private lemma flowS_mem_L (n d : ℕ) (hn : 0 < n) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (f : H n d) (hf : f ∈ L n d) : flowS (n := n) (d := d) θ f ∈ L n d := by
  rcases flow_substS_mem_L n d hn f hf θ hθ0 hθ1 with ⟨g, hgL, hgval⟩
  exact mem_L_of_val_eq (by
    rw [flowS_apply]
    simpa [flowSVar] using hgval.symm) hgL

/-- `S(1,f) = f(1,…,1) · (Σ Xᵢ)^d`. -/
private lemma flowS_one (n d : ℕ) (f : H n d) :
    flowS (n := n) (d := d) 1 f = (MvPolynomial.eval (fun _ : Fin n => (1 : ℝ)) f.1) • sumXpow n d := by
  apply Subtype.ext
  rw [flowS_apply]
  rw [show (fun j : Fin n => flowSVar n 1 j) =
      (fun _ : Fin n => ∑ i : Fin n, MvPolynomial.X i) by
    funext j
    exact flowSVar_at_one n j]
  simpa [sumXpow_apply, sumX, H_smul_val] using (substS_at_one n d f)

/-- Evaluation at the all-ones vector of a positive-coefficient homogeneous polynomial
of degree `d ≥ 1` is positive. -/
private lemma eval_one_pos_of_mem_P {n d : ℕ} (hn : 0 < n) (hd : 1 ≤ d)
    (f : H n d) (hf : f ∈ P n d) : 0 < MvPolynomial.eval (fun _ : Fin n => (1 : ℝ)) f.1 := by
  classical
  let e : Fin n := ⟨0, hn⟩
  have hw : Finsupp.weight (1 : Fin n → ℕ) (Finsupp.single e d) = d := by
    rw [Finsupp.weight_single]
    simp
  have hpos : 0 < f.1.coeff (Finsupp.single e d) := hf (Finsupp.single e d) hw
  have hfne : f.1 ≠ 0 := by
    intro hz
    have hc : f.1.coeff (Finsupp.single e d) = 0 := by simp [hz]
    linarith
  have hdeg : f.1.IsHomogeneous d := f.2
  have hwh : f.1.IsWeightedHomogeneous (1 : Fin n → ℕ) d := by
    simpa [MvPolynomial.IsHomogeneous] using hdeg
  have hcpos : ∀ m ∈ f.1.support, 0 < f.1.coeff m := by
    intro m hm
    have hc : f.1.coeff m ≠ 0 := (MvPolynomial.mem_support_iff).mp hm
    have hw2 : Finsupp.weight (1 : Fin n → ℕ) m = d := by
      by_contra h2
      exact hc (MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero (w := (1 : Fin n → ℕ))
        (φ := f.1) (n := d) hwh m h2)
    exact hf m hw2
  have hsupp : f.1.support.Nonempty := by
    by_contra hne
    apply hfne
    rw [← MvPolynomial.support_eq_empty]
    exact (Finset.not_nonempty_iff_eq_empty).mp hne
  rw [MvPolynomial.eval_eq]
  have hprod : ∀ m ∈ f.1.support, (∏ i ∈ m.support, (1 : ℝ) ^ m i) = 1 := by
    intro m hm
    apply Finset.prod_eq_one
    intro i hi
    simpa using (one_pow (m i))
  have hsum : (∑ m ∈ f.1.support, f.1.coeff m * ∏ i ∈ m.support, (1 : ℝ) ^ m i) =
      ∑ m ∈ f.1.support, f.1.coeff m := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [hprod m hm]
    ring
  rw [hsum]
  exact Finset.sum_pos hcpos hsupp

/-! ## Basic algebraic facts about `nuij_T` -/

/-- each `nuij_power` is linear -/
private lemma nuij_power_smul {n d : ℕ} (i s : Fin n) (θ : ℝ) (c : ℝ) (f : H n d) :
    (nuij_power i s d θ) (c • f) = c • ((nuij_power i s d θ) f) := by
  exact (nuij_power i s d θ).map_smul c f

/-- folding `nuij_power` over a list is linear in the polynomial -/
private lemma nuij_fold_smul {n d : ℕ} (l : List (Fin n)) (s : Fin n) (θ : ℝ) (c : ℝ) :
    ∀ f : H n d,
      l.foldl (fun acc i => (nuij_power i s d θ) acc) (c • f) =
        c • l.foldl (fun acc i => (nuij_power i s d θ) acc) f := by
  induction l with
  | nil => intro f; simp
  | cons a l' ih =>
      intro f
      calc
        (a :: l').foldl (fun acc i => (nuij_power i s d θ) acc) (c • f)
            = l'.foldl (fun acc i => (nuij_power i s d θ) acc)
                ((nuij_power a s d θ) (c • f)) := by simp [List.foldl]
        _ = l'.foldl (fun acc i => (nuij_power i s d θ) acc)
                (c • ((nuij_power a s d θ) f)) := by rw [nuij_power_smul]
        _ = c • l'.foldl (fun acc i => (nuij_power i s d θ) acc)
                ((nuij_power a s d θ) f) := ih _
        _ = c • (a :: l').foldl (fun acc i => (nuij_power i s d θ) acc) f := by
              simp [List.foldl]

/-- `nuij_T` is linear in the polynomial -/
private lemma nuij_T_smul {n d : ℕ} (hn2 : 2 ≤ n) (θ : ℝ) (c : ℝ) (f : H n d) :
    nuij_T (n := n) (d := d) hn2 θ (c • f) = c • nuij_T (n := n) (d := d) hn2 θ f := by
  rw [nuij_T_eq_fold, nuij_T_eq_fold]
  exact nuij_fold_smul (nuij_idx hn2) (nuij_s hn2) θ c f

/-- `nuij_deformEnd` at `θ = 0` is the identity -/
private lemma nuij_deformEnd_zero (n k : ℕ) (i s : Fin n) :
    nuij_deformEnd (n := n) (k := k) i s 0 = 1 := by
  ext f
  unfold nuij_deformEnd
  simp

/-- each `nuij_power` at `θ = 0` is the identity -/
private lemma nuij_power_zero (n d : ℕ) (i s : Fin n) :
    nuij_power i s d 0 = (1 : Module.End ℝ (H n d)) := by
  cases d with
  | zero => rfl
  | succ k =>
      change (nuij_deformEnd (n := n) (k := k) i s 0) ^ (k + 1) = 1
      rw [nuij_deformEnd_zero]
      simp

/-- `nuij_T(0,f) = f`. -/
private lemma nuij_fold_zero {n d : ℕ} (l : List (Fin n)) (s : Fin n) (f : H n d) :
    l.foldl (fun acc i => (nuij_power i s d 0) acc) f = f := by
  induction l with
  | nil => simp [List.foldl]
  | cons a l' ih =>
      have hstep : (nuij_power a s d 0) f = f := by
        simpa [nuij_power_zero]
      rw [List.foldl, hstep]
      exact ih

private lemma nuij_T_zero (n d : ℕ) (hn2 : 2 ≤ n) (f : H n d) :
    nuij_T (n := n) (d := d) hn2 0 f = f := by
  rw [nuij_T_eq_fold]
  exact nuij_fold_zero (nuij_idx hn2) (nuij_s hn2) f

/-! ## The smoothing path stays in `Ŀ` -/

/-- path membership: for `0 < θ ≤ 1`, `T(θ, S(θ,f))` is strictly Lorentzian -/
private lemma path_mem_Ŀ (n d : ℕ) (hn2 : 2 ≤ n) (hd : 3 ≤ d) (θ : ℝ) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (f : H n d) (hfĿ : f ∈ Ŀ n d) :
    nuij_T (n := n) (d := d) hn2 θ (flowS (n := n) (d := d) θ f) ∈ Ŀ n d := by
  have hfL : f ∈ L n d := strict_subset_L n d (by omega) hfĿ
  have hfP : f ∈ P n d := by
    cases d with
    | zero => simpa [Ŀ] using hfĿ
    | succ d1 =>
        cases d1 with
        | zero => simpa [Ŀ] using hfĿ
        | succ d2 =>
            cases d2 with
            | zero => exact hfĿ.1
            | succ k => exact hfĿ.1
  have hθ0 : 0 ≤ θ := le_of_lt hθ
  have hSL : flowS (n := n) (d := d) θ f ∈ L n d := flowS_mem_L n d (by omega) θ hθ0 hθ1 f hfL
  have hSP : flowS (n := n) (d := d) θ f ∈ P n d := flowS_mem_P n d θ hθ0 hθ1 f hfP
  exact nuij_smoothing n d hn2 hd θ hθ (flowS (n := n) (d := d) θ f) ⟨hSL, hSP⟩

/-! ## Continuity of the smoothing path -/

/-- the weight-`d` exponent vectors -/
private abbrev spc_WeightExps (n d : ℕ) := {m : Fin n →₀ ℕ // Finsupp.weight (1 : Fin n → ℕ) m = d}

private noncomputable instance spc_weightExps_fintype (n d : ℕ) : Fintype (spc_WeightExps n d) := by
  dsimp [spc_WeightExps]
  exact (Finsupp.finite_of_nat_weight_eq (w := (1 : Fin n → ℕ)) (σ := Fin n) (by intro x; simp) d).fintype

private noncomputable instance spc_weightExps_isModuleTopology (n d : ℕ) :
    IsModuleTopology ℝ (spc_WeightExps n d → ℝ) := by
  dsimp [spc_WeightExps]
  infer_instance

/-- the coordinate linear equivalence `H n d ≃ₗ[ℝ] (exponents of weight d → ℝ)` -/
private noncomputable def spc_coordEquiv (n d : ℕ) : H n d ≃ₗ[ℝ] (spc_WeightExps n d → ℝ) := by
  classical
  change homogeneousSubmodule (Fin n) ℝ d ≃ₗ[ℝ] (spc_WeightExps n d → ℝ)
  exact Classical.choose (Commons.Algebra.MvPolynomial.homogeneous_coeff_equiv n d)

private lemma spc_coordEquiv_apply (n d : ℕ) (f : H n d) (m : spc_WeightExps n d) :
    spc_coordEquiv n d f m = MvPolynomial.coeff m.1 f.1 := by
  classical
  have h := Classical.choose_spec (Commons.Algebra.MvPolynomial.homogeneous_coeff_equiv n d)
  change ((Classical.choose (Commons.Algebra.MvPolynomial.homogeneous_coeff_equiv n d)) f m) =
    MvPolynomial.coeff m.1 f.1
  exact h f m

/-- continuous coordinate functions imply continuity into `H n d` -/
private lemma spc_continuous_of_coeff_continuous {n d : ℕ} {X : Type*} [TopologicalSpace X]
    (g : X → H n d)
    (h : ∀ m : spc_WeightExps n d, Continuous (fun x : X => MvPolynomial.coeff m.1 (g x).1)) :
    Continuous g := by
  classical
  let e := spc_coordEquiv n d
  have hecont : Continuous e := by
    exact IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hecont' : Continuous e.symm := by
    exact IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  have hcoords : ∀ m : spc_WeightExps n d, Continuous (fun x : X => e (g x) m) := by
    intro m
    have : (fun x : X => e (g x) m) = fun x : X => MvPolynomial.coeff m.1 (g x).1 := by
      funext x
      exact spc_coordEquiv_apply n d (g x) m
    rw [this]
    exact h m
  have hege : Continuous (fun x : X => e (g x)) := by
    exact continuous_pi (fun m => hcoords m)
  have hg : g = fun x => e.symm (e (g x)) := by
    funext x
    simp
  rw [hg]
  exact hecont'.comp hege

/-- `θ ↦ S(θ,f)` is continuous. -/
private lemma flowS_continuous (n d : ℕ) (f : H n d) :
    Continuous (fun θ : ℝ => flowS (n := n) (d := d) θ f) := by
  apply spc_continuous_of_coeff_continuous
  intro m
  -- coefficient of the substituted polynomial is continuous in θ (commons lemma)
  have h := subst_coeff_continuous n d f m.1
  simpa [flowS_apply, flowSVar] using h

/-- every linear map between module-topology spaces is continuous -/
private lemma spc_linear_cont {n d1 d2 : ℕ} (L : H n d1 →ₗ[ℝ] H n d2) : Continuous L := by
  exact IsModuleTopology.continuous_of_linearMap L

@[fun_prop]
private lemma spc_pderivH_cont (n k : ℕ) (i : Fin n) : Continuous (nuij_pderivH (n := n) (k := k) i) :=
  spc_linear_cont (nuij_pderivH (n := n) (k := k) i)

@[fun_prop]
private lemma spc_mulXH_cont (n k : ℕ) (i : Fin n) : Continuous (nuij_mulXH (n := n) (k := k) i) :=
  spc_linear_cont (nuij_mulXH (n := n) (k := k) i)

private lemma nuij_deformEnd_cont_apply (n k : ℕ) (i s : Fin n) :
    Continuous (fun p : ℝ × H n (k + 1) => nuij_deformEnd (n := n) (k := k) i s p.1 p.2) := by
  unfold nuij_deformEnd
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.comp_apply]
  refine Continuous.add ?_ ?_
  · exact continuous_snd
  · have hL : Continuous (fun p : ℝ × H n (k + 1) => (nuij_mulXH (n := n) (k := k) i)
        ((nuij_pderivH (n := n) (k := k) s) p.2)) := by
      exact ((spc_mulXH_cont n k i).comp (spc_pderivH_cont n k s)).comp continuous_snd
    exact Continuous.smul continuous_fst hL

private lemma nuij_deformEnd_pow_cont (n k m : ℕ) (i s : Fin n) :
    Continuous (fun p : ℝ × H n (k + 1) => ((nuij_deformEnd (n := n) (k := k) i s p.1) ^ m) p.2) := by
  induction m with
  | zero => simpa using (continuous_snd (X := ℝ) (Y := H n (k + 1)))
  | succ m ih =>
      have h1 : (fun p : ℝ × H n (k + 1) =>
          ((nuij_deformEnd (n := n) (k := k) i s p.1) ^ (m + 1)) p.2) =
          fun p => ((nuij_deformEnd (n := n) (k := k) i s p.1) ^ m)
            ((nuij_deformEnd (n := n) (k := k) i s p.1) p.2) := by
        funext p
        rw [pow_succ]
        rfl
      rw [h1]
      exact ih.comp (Continuous.prodMk continuous_fst (nuij_deformEnd_cont_apply (n := n) (k := k) i s))

private lemma nuij_power_cont_apply (n d : ℕ) (i s : Fin n) :
    Continuous (fun p : ℝ × H n d => (nuij_power (n := n) i s d p.1) p.2) := by
  cases d with
  | zero => simpa [nuij_power] using (continuous_snd (X := ℝ) (Y := H n 0))
  | succ k =>
      change Continuous (fun p : ℝ × H n (k + 1) =>
        ((nuij_deformEnd (n := n) (k := k) i s p.1) ^ (k + 1)) p.2)
      exact nuij_deformEnd_pow_cont n k (k + 1) i s

private lemma nuij_foldl_power_cont {n d : ℕ} (l : List (Fin n)) (s : Fin n) :
    Continuous (fun p : ℝ × H n d =>
      l.foldl (fun acc i => (nuij_power (n := n) i s d p.1) acc) p.2) := by
  induction l with
  | nil => simpa using (continuous_snd (X := ℝ) (Y := H n d))
  | cons a l' ih =>
      have hstep : Continuous (fun p : ℝ × H n d =>
          l'.foldl (fun acc i => (nuij_power (n := n) i s d p.1) acc)
            ((nuij_power (n := n) a s d p.1) p.2)) := by
        exact ih.comp (Continuous.prodMk continuous_fst (nuij_power_cont_apply (n := n) (d := d) a s))
      have hmain : (fun p : ℝ × H n d =>
          (a :: l').foldl (fun acc i => (nuij_power (n := n) i s d p.1) acc) p.2) =
          fun p => l'.foldl (fun acc i => (nuij_power (n := n) i s d p.1) acc)
            ((nuij_power (n := n) a s d p.1) p.2) := by
        funext p
        simp [List.foldl]
      rw [hmain]
      exact hstep

/-- `(θ,g) ↦ T_n(θ,g)` is continuous. -/
private lemma nuij_T_cont (n d : ℕ) (hn2 : 2 ≤ n) :
    Continuous (fun p : ℝ × H n d => nuij_T (n := n) (d := d) hn2 p.1 p.2) := by
  have hfold : Continuous (fun p : ℝ × H n d =>
      (nuij_idx hn2).foldl (fun acc i => (nuij_power (n := n) i (nuij_s hn2) d p.1) acc) p.2) :=
    nuij_foldl_power_cont (nuij_idx hn2) (nuij_s hn2)
  have hfun : (fun p : ℝ × H n d => nuij_T (n := n) (d := d) hn2 p.1 p.2) =
      fun p : ℝ × H n d =>
        (nuij_idx hn2).foldl (fun acc i => (nuij_power (n := n) i (nuij_s hn2) d p.1) acc) p.2 := by
    funext p
    rw [nuij_T_eq_fold]
  rw [hfun]
  exact hfold

/-- the whole homotopy `θ ↦ T_n(θ, S(θ,f))` is continuous in `θ`. -/
private lemma path_cont (n d : ℕ) (hn2 : 2 ≤ n) (f : H n d) :
    Continuous (fun θ : ℝ => nuij_T (n := n) (d := d) hn2 θ (flowS (n := n) (d := d) θ f)) := by
  have hsub : Continuous (fun θ : ℝ => flowS (n := n) (d := d) θ f) := flowS_continuous n d f
  change Continuous ((fun p : ℝ × H n d => nuij_T (n := n) (d := d) hn2 p.1 p.2) ∘
    (fun θ : ℝ => (θ, flowS (n := n) (d := d) θ f)))
  exact (nuij_T_cont n d hn2).comp (Continuous.prodMk continuous_id hsub)

/-! ## Paths inside `Ŀ n d` and the high-degree path connectedness -/

/-- the common endpoint `e = T_n(1, (Σ Xᵢ)^d)` -/
private noncomputable def spc_e (n d : ℕ) (hn2 : 2 ≤ n) : H n d :=
  nuij_T (n := n) (d := d) hn2 1 (sumXpow n d)

/-- `e ∈ Ŀ n d` for `3 ≤ d`. -/
private lemma spc_e_mem_Ŀ (n d : ℕ) (hn2 : 2 ≤ n) (hd : 3 ≤ d) : spc_e n d hn2 ∈ Ŀ n d := by
  have hL : (sumXpow n d : H n d) ∈ L n d := sumXpow_mem_L n (by omega) d
  have hP : (sumXpow n d : H n d) ∈ P n d := by
    intro m hm
    exact sumXpow_coeff_pos n d m hm
  dsimp [spc_e]
  exact nuij_smoothing n d hn2 hd 1 (by norm_num) (sumXpow n d) ⟨hL, hP⟩

/-- the map `θ ↦ T(θ, S(θ,f))` sends the unit interval into `Ŀ n d` -/
private lemma path_image_mem_Ŀ {n d : ℕ} (hn2 : 2 ≤ n) (hd : 3 ≤ d) (f : H n d)
    (hfĿ : f ∈ Ŀ n d) :
    ∀ t ∈ unitInterval,
      nuij_T (n := n) (d := d) hn2 t (flowS (n := n) (d := d) t f) ∈ Ŀ n d := by
  intro t ht
  rw [unitInterval, Set.mem_Icc] at ht
  rcases ht with ⟨ht0, ht1⟩
  by_cases htpos : t = 0
  · subst t
    rw [flowS_zero, nuij_T_zero]
    exact hfĿ
  · have ht0' : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htpos)
    exact path_mem_Ŀ n d hn2 hd t ht0' ht1 f hfĿ

/-- positive scalar multiples of `e` are joined along the positive ray -/
private lemma ray_joinedIn {n d : ℕ} (hn2 : 2 ≤ n) (hd : 3 ≤ d) (c1 c2 : ℝ)
    (hc1 : 0 < c1) (hc2 : 0 < c2) :
    JoinedIn (Ŀ n d) (c1 • spc_e n d hn2) (c2 • spc_e n d hn2) := by
  classical
  let e : H n d := spc_e n d hn2
  have heĿ : e ∈ Ŀ n d := by simpa [e] using (spc_e_mem_Ŀ n d hn2 hd)
  let γ : ℝ → H n d := fun t : ℝ => ((1 - t) * c1 + t * c2) • e
  have hγ : Continuous γ := by
    dsimp [γ]
    fun_prop
  have hγ0 : γ 0 = c1 • e := by
    dsimp [γ]
    simp
  have hγ1 : γ 1 = c2 • e := by
    dsimp [γ]
    simp
  have himg : γ '' unitInterval ⊆ Ŀ n d := by
    rintro p ⟨t, ht, rfl⟩
    rw [unitInterval, Set.mem_Icc] at ht
    rcases ht with ⟨ht0, ht1⟩
    have hpos : 0 < (1 - t) * c1 + t * c2 := by
      by_cases ht1' : t = 1
      · subst t
        simpa using hc2
      · have htlt : t < 1 := lt_of_le_of_ne ht1 ht1'
        have h1 : 0 < 1 - t := sub_pos.mpr htlt
        have h2 : 0 < (1 - t) * c1 := mul_pos h1 hc1
        have h3 : 0 ≤ t * c2 := mul_nonneg ht0 (le_of_lt hc2)
        linarith
    exact smul_mem_strict n d (by omega) hpos e heĿ
  exact JoinedIn.ofLine hγ.continuousOn hγ0 hγ1 himg

/-- every element of `Ŀ n d` is joined to a positive multiple of `e` -/
private lemma joined_to_e {n d : ℕ} (hn2 : 2 ≤ n) (hd : 3 ≤ d) (f : H n d)
    (hfĿ : f ∈ Ŀ n d) :
    JoinedIn (Ŀ n d) f (((MvPolynomial.eval (fun _ : Fin n => (1 : ℝ)) f.1)) • spc_e n d hn2) := by
  classical
  let γ : ℝ → H n d :=
    fun t : ℝ => nuij_T (n := n) (d := d) hn2 t (flowS (n := n) (d := d) t f)
  have hγc : Continuous γ := path_cont n d hn2 f
  have hγ0 : γ 0 = f := by
    dsimp [γ]
    rw [flowS_zero, nuij_T_zero]
  have hevalpos : 0 < MvPolynomial.eval (fun _ : Fin n => (1 : ℝ)) f.1 :=
    eval_one_pos_of_mem_P (by omega) (by omega : 1 ≤ d) f (by
      -- f ∈ P
      cases d with
      | zero => simpa [Ŀ] using hfĿ
      | succ d1 =>
          cases d1 with
          | zero => simpa [Ŀ] using hfĿ
          | succ d2 =>
              cases d2 with
              | zero => exact hfĿ.1
              | succ k => exact hfĿ.1)
  have hγ1 : γ 1 = (MvPolynomial.eval (fun _ : Fin n => (1 : ℝ)) f.1) • spc_e n d hn2 := by
    dsimp [γ, spc_e]
    calc
      nuij_T (n := n) (d := d) hn2 1 (flowS (n := n) (d := d) 1 f)
          = nuij_T (n := n) (d := d) hn2 1
              ((MvPolynomial.eval (fun _ : Fin n => (1 : ℝ)) f.1) • sumXpow n d) := by
              rw [flowS_one]
      _ = (MvPolynomial.eval (fun _ : Fin n => (1 : ℝ)) f.1) •
            nuij_T (n := n) (d := d) hn2 1 (sumXpow n d) := by
              rw [nuij_T_smul]
  have himg : γ '' unitInterval ⊆ Ŀ n d := by
    rintro p ⟨t, ht, rfl⟩
    exact path_image_mem_Ŀ hn2 hd f hfĿ t ht
  exact JoinedIn.ofLine hγc.continuousOn hγ0 hγ1 himg

/-- high-degree strictly Lorentzian sets are path connected -/
private lemma pathConnected_highDegree (n d : ℕ) (hn2 : 2 ≤ n) (hd : 3 ≤ d) :
    IsPathConnected (Ŀ n d) := by
  rw [isPathConnected_iff]
  constructor
  · exact ⟨spc_e n d hn2, spc_e_mem_Ŀ n d hn2 hd⟩
  · intro f hf g hg
    let cf : ℝ := MvPolynomial.eval (fun _ : Fin n => (1 : ℝ)) f.1
    let cg : ℝ := MvPolynomial.eval (fun _ : Fin n => (1 : ℝ)) g.1
    have hcf : 0 < cf := by
      dsimp [cf]
      exact eval_one_pos_of_mem_P (by omega) (by omega : 1 ≤ d) f (by
        cases d with
        | zero => simpa [Ŀ] using hf
        | succ d1 =>
            cases d1 with
            | zero => simpa [Ŀ] using hf
            | succ d2 =>
                cases d2 with
                | zero => exact hf.1
                | succ k => exact hf.1)
    have hcg : 0 < cg := by
      dsimp [cg]
      exact eval_one_pos_of_mem_P (by omega) (by omega : 1 ≤ d) g (by
        cases d with
        | zero => simpa [Ŀ] using hg
        | succ d1 =>
            cases d1 with
            | zero => simpa [Ŀ] using hg
            | succ d2 =>
                cases d2 with
                | zero => exact hg.1
                | succ k => exact hg.1)
    have h1 : JoinedIn (Ŀ n d) f (cf • spc_e n d hn2) := by
      dsimp [cf]
      exact joined_to_e hn2 hd f hf
    have h2 : JoinedIn (Ŀ n d) (cf • spc_e n d hn2) (cg • spc_e n d hn2) := by
      dsimp [cf, cg]
      exact ray_joinedIn hn2 hd cf cg hcf hcg
    have h3 : JoinedIn (Ŀ n d) (cg • spc_e n d hn2) g := by
      have h3' : JoinedIn (Ŀ n d) g (cg • spc_e n d hn2) := by
        dsimp [cg]
        exact joined_to_e hn2 hd g hg
      exact h3'.symm
    exact h1.trans (h2.trans h3)

/-- high-degree strictly Lorentzian sets are preconnected -/
private lemma preconnected_highDegree (n d : ℕ) (hn2 : 2 ≤ n) (hd : 3 ≤ d) :
    IsPreconnected (Ŀ n d) :=
  (IsPathConnected.isConnected (pathConnected_highDegree n d hn2 hd)).isPreconnected
/-! ## The main statement -/

theorem strictLorentzian_preconnected (n d : ℕ) (hn : 0 < n) :
    IsPreconnected (Commons.LorentzianPolynomials.Ŀ n d) := by
  by_cases hd : d ≤ 1
  · exact preconnected_of_degree_le_one n d hd
  · by_cases hn1 : n = 1
    · subst n
      rw [spc_Ŀ1_eq_P1 d]
      exact (P_convex 1 d).isPreconnected
    · have hn2 : 2 ≤ n := by omega
      by_cases hd2' : d = 2
      · subst d
        exact preconnected_degreeTwo n (by omega)
      · have hd3 : 3 ≤ d := by omega
        exact preconnected_highDegree n d hn2 hd3
end
end Commons.LorentzianPolynomials
