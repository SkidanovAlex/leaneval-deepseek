import Mathlib
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.LorentzianPolynomials.closure_strict_eq_L_of_degree_le_two
import Submission.Commons.LorentzianPolynomials.P_subset_M
import Submission.Commons.LorentzianPolynomials.subst_coeff_continuous
import Submission.Commons.LorentzianPolynomials.L_mem_nonneg
import Submission.Commons.LorentzianPolynomials.substS_at_zero
import Submission.Commons.Algebra.MvPolynomial.subst_coeff_pos
import Submission.Commons.LorentzianPolynomials.directional_deriv_mem_L

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Commons.LorentzianPolynomials

noncomputable section

/-! ## The substitution operator `S_θ` and its algebraic properties -/

/-- The substituted variable: `(1−θ)·X j + θ·(Σ i, X i)`. -/
private noncomputable def flowVar (n : ℕ) (θ : ℝ) (j : Fin n) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C (1 - θ) * MvPolynomial.X j +
    MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i)

/-- The linear form `flowVar n θ j` is homogeneous of degree `1`. -/
private lemma flowVar_isHomogeneous_one (n : ℕ) (θ : ℝ) (j : Fin n) :
    (flowVar n θ j).IsHomogeneous 1 := by
  have hXj : (MvPolynomial.X j : MvPolynomial (Fin n) ℝ).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X (σ := Fin n) (R := ℝ) j
  have hC1 : (MvPolynomial.C (1 - θ) : MvPolynomial (Fin n) ℝ).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C (σ := Fin n) (R := ℝ) (1 - θ)
  have hsum : ((∑ i : Fin n, MvPolynomial.X i) : MvPolynomial (Fin n) ℝ).IsHomogeneous 1 := by
    exact MvPolynomial.IsHomogeneous.sum Finset.univ (fun i : Fin n => MvPolynomial.X i) 1
      (fun i hi => MvPolynomial.isHomogeneous_X (σ := Fin n) (R := ℝ) i)
  have hC2 : (MvPolynomial.C θ : MvPolynomial (Fin n) ℝ).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C (σ := Fin n) (R := ℝ) θ
  unfold flowVar
  exact (MvPolynomial.IsHomogeneous.mul (φ := MvPolynomial.C (1 - θ)) hC1 (ψ := MvPolynomial.X j) hXj).add
    (MvPolynomial.IsHomogeneous.mul (φ := MvPolynomial.C θ) hC2 (ψ := ∑ i : Fin n, MvPolynomial.X i) hsum)

/-- `S_θ f := f((1−θ)·X + θ·(ΣᵢXᵢ))` as an element of `H n d`. -/
private noncomputable def flowSubst {n d : ℕ} (θ : ℝ) (f : H n d) : H n d :=
  ⟨MvPolynomial.aeval (fun j : Fin n => flowVar n θ j) f.1, by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    have h := MvPolynomial.IsHomogeneous.aeval (hφ := f.2)
      (g := fun j : Fin n => flowVar n θ j) (flowVar_isHomogeneous_one n θ)
    simpa [Nat.one_mul, mul_comm, mul_left_comm, mul_assoc] using h⟩

private lemma flowSubst_val (n d : ℕ) (θ : ℝ) (f : H n d) :
    (flowSubst (n := n) (d := d) θ f).1 =
      MvPolynomial.aeval (fun j : Fin n => flowVar n θ j) f.1 := rfl

private lemma aeval_flowVar (n : ℕ) (θ : ℝ) (z : Fin n → ℂ) (j : Fin n) :
    MvPolynomial.aeval (fun i : Fin n => (z i : ℂ)) (flowVar n θ j) =
      ((1 - θ : ℝ) : ℂ) * (z j : ℂ) + ((θ : ℝ) : ℂ) * (∑ i : Fin n, (z i : ℂ)) := by
  unfold flowVar
  simp [MvPolynomial.aeval_X, map_sum]

/-- evaluation identity: substituting into `p` and then evaluating at `z` equals
evaluating `p` at the substituted points. -/
private lemma aeval_flowSubst_aeval {n : ℕ} (θ : ℝ) (z : Fin n → ℂ) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.aeval (fun j : Fin n => (z j : ℂ)) (MvPolynomial.aeval (fun j : Fin n => flowVar n θ j) p) =
      MvPolynomial.aeval (fun j : Fin n =>
        ((1 - θ : ℝ) : ℂ) * (z j : ℂ) +
          ((θ : ℝ) : ℂ) * (∑ i : Fin n, (z i : ℂ))) p := by
  classical
  have h := MvPolynomial.aeval_bind₁ (R := ℝ) (S := ℂ)
    (f := fun j : Fin n => (z j : ℂ)) (g := fun j : Fin n => flowVar n θ j) (φ := p)
  -- h : aeval z (bind₁ g p) = aeval (fun i => aeval z (g i)) p
  rw [← MvPolynomial.aeval_eq_bind₁ (f := fun j : Fin n => flowVar n θ j)] at h
  -- now h : aeval z (aeval g p) = aeval (fun i => aeval z (g i)) p ; but binder order changed:
  -- aeval_eq_bind₁ : aeval f = bind₁ f (equal alg homs). So aeval (flowVar) p = bind₁ (flowVar) p.
  change MvPolynomial.aeval (fun j : Fin n => (z j : ℂ)) (MvPolynomial.aeval (fun j : Fin n => flowVar n θ j) p) =
    MvPolynomial.aeval (fun j : Fin n =>
      ((1 - θ : ℝ) : ℂ) * (z j : ℂ) + ((θ : ℝ) : ℂ) * (∑ i : Fin n, (z i : ℂ))) p
  have hfun : (fun i : Fin n => MvPolynomial.aeval (fun j : Fin n => (z j : ℂ)) (flowVar n θ i)) =
      (fun j : Fin n => ((1 - θ : ℝ) : ℂ) * (z j : ℂ) +
        ((θ : ℝ) : ℂ) * (∑ i : Fin n, (z i : ℂ))) := by
    funext j
    exact aeval_flowVar n θ z j
  rw [h, hfun]

/-! ## The upper-half-plane image of the flow -/

/-- For `z ∈ ℍⁿ` and `θ ∈ [0,1]`, the point `(1−θ)·z_j + θ·(Σᵢzᵢ)` again has positive
imaginary part (uses `0 < n`). -/
private lemma flow_map_im_pos (n : ℕ) (hn : 0 < n) (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (z : Fin n → ℍ) (j : Fin n) :
    0 < (((1 - θ : ℝ) : ℂ) * (z j : ℂ) + ((θ : ℝ) : ℂ) * (∑ i : Fin n, (z i : ℂ))).im := by
  rw [Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul]
  have hsum : ((∑ i : Fin n, (z i : ℂ)).im) = ∑ i : Fin n, (z i : ℂ).im := by
    exact map_sum Complex.imAddGroupHom (fun i : Fin n => (z i : ℂ)) Finset.univ
  rw [hsum]
  by_cases hθ0' : θ = 0
  · subst θ
    simp
    exact UpperHalfPlane.im_pos (z j)
  · have hθpos : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθ0')
    have hzpos : 0 < (z j : ℂ).im := UpperHalfPlane.im_pos (z j)
    have hnonneg1 : 0 ≤ (1 - θ) * (z j : ℂ).im :=
      mul_nonneg (sub_nonneg.mpr hθ1) (le_of_lt hzpos)
    haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    have hSpos : 0 < (∑ i : Fin n, (z i : ℂ).im) :=
      Finset.sum_pos (s := Finset.univ) (f := fun i : Fin n => (z i : ℂ).im)
        (fun i hi => UpperHalfPlane.im_pos (z i)) Finset.univ_nonempty
    have hpos2 : 0 < θ * (∑ i : Fin n, (z i : ℂ).im) := mul_pos hθpos hSpos
    linarith

/-- The flow map sends the upper half plane into itself. -/
private def flowMap {n : ℕ} (hn : 0 < n) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (z : Fin n → ℍ) : Fin n → ℍ :=
  fun j => ⟨((1 - θ : ℝ) : ℂ) * (z j : ℂ) + ((θ : ℝ) : ℂ) * (∑ i : Fin n, (z i : ℂ)),
    flow_map_im_pos n hn θ hθ0 hθ1 z j⟩

/-- stability is preserved under the flow substitution: if `p` is stable and `0 ≤ θ ≤ 1`,
then `S_θ p` is stable. -/
private lemma flowSubst_IsStable (n : ℕ) (hn : 0 < n) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (p : MvPolynomial (Fin n) ℝ) (hp : IsStable p) :
    IsStable (MvPolynomial.aeval (fun j : Fin n => flowVar n θ j) p) := by
  rcases hp with hp0 | hpz
  · left
    simp [hp0]
  · right
    intro z
    let w : Fin n → ℍ := flowMap (n := n) hn θ hθ0 hθ1 z
    have hne : MvPolynomial.aeval (fun j : Fin n => ((w j : ℂ))) p ≠ 0 := by
      simpa [Function.comp_def] using hpz w
    have hwz : (fun j : Fin n => ((w j : ℂ))) =
        (fun j : Fin n => ((1 - θ : ℝ) : ℂ) * (z j : ℂ) +
          ((θ : ℝ) : ℂ) * (∑ i : Fin n, (z i : ℂ))) := by
      funext j
      rfl
    change MvPolynomial.aeval (fun j : Fin n => ((z j : ℂ)))
        (MvPolynomial.aeval (fun j : Fin n => flowVar n θ j) p) ≠ 0
    have hmain := aeval_flowSubst_aeval (n := n) θ (fun i : Fin n => (z i : ℂ)) p
    rw [hmain]
    rw [← hwz]
    exact hne

/-! ## nonnegativity of coefficients is preserved by the flow -/

private lemma coeff_mul_nonneg_of_coeff_nonneg {n : ℕ} {p q : MvPolynomial (Fin n) ℝ}
    (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m p) (hq : ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m q) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m (p * q) := by
  classical
  intro m
  rw [MvPolynomial.coeff_mul]
  exact Finset.sum_nonneg (fun x hx => mul_nonneg (hp x.1) (hq x.2))


private lemma coeff_add_nonneg {n : ℕ} {p q : MvPolynomial (Fin n) ℝ}
    (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m p) (hq : ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m q) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m (p + q) := by
  intro m
  rw [coeff_add]
  exact add_nonneg (hp m) (hq m)

private lemma coeff_smul_nonneg {n : ℕ} (a : ℝ) (ha : 0 ≤ a) {p : MvPolynomial (Fin n) ℝ}
    (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m p) : ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m (a • p) := by
  intro m
  rw [coeff_smul, smul_eq_mul]
  exact mul_nonneg ha (hp m)

private lemma coeff_C_mul_nonneg {n : ℕ} {c : ℝ} (hc : 0 ≤ c) {p : MvPolynomial (Fin n) ℝ}
    (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m p) : ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m (C c * p) := by
  intro m
  rw [coeff_C_mul]
  exact mul_nonneg hc (hp m)

private lemma coeff_one_nonneg {n : ℕ} : ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m (1 : MvPolynomial (Fin n) ℝ) := by
  classical
  intro m
  by_cases hm : m = 0
  · subst m
    simp
  · have hzero : coeff m (1 : MvPolynomial (Fin n) ℝ) = 0 := by
      rw [← MvPolynomial.C_1, MvPolynomial.coeff_C]
      rw [if_neg]
      exact fun h => hm h.symm
    rw [hzero]

private lemma coeff_pow_nonneg {n : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m p) (k : ℕ) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m (p ^ k) := by
  induction k with
  | zero => intro m; simpa using (coeff_one_nonneg (n := n) m)
  | succ k ih =>
      intro m
      rw [pow_succ]
      exact coeff_mul_nonneg_of_coeff_nonneg ih hp m

private lemma coeff_prod_nonneg {n : ℕ} {ι : Type*} (s : Finset ι)
    (p : ι → MvPolynomial (Fin n) ℝ) (hp : ∀ i : ι, ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m (p i)) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m (s.prod p) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro m; simpa using (coeff_one_nonneg (n := n) m)
  | insert i s' his ih =>
      intro m
      rw [Finset.prod_insert his]
      exact coeff_mul_nonneg_of_coeff_nonneg (hp i) ih m

private lemma coeff_X_nonneg {n : ℕ} (j : Fin n) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m (X j : MvPolynomial (Fin n) ℝ) := by
  classical
  intro m
  by_cases hm : m = Finsupp.single j 1
  · subst m
    rw [MvPolynomial.coeff_X j (Finsupp.single j 1)]
    norm_num
  · rw [MvPolynomial.coeff_X j m, if_neg]
    exact fun h => hm h.symm

private lemma coeff_sumX_nonneg (n : ℕ) : ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m (∑ i : Fin n, (X i : MvPolynomial (Fin n) ℝ)) := by
  classical
  intro m
  rw [coeff_sum]
  exact Finset.sum_nonneg (fun i hi => coeff_X_nonneg i m)

/-- `flowVar n θ j` has nonnegative coefficients when `0 ≤ θ ≤ 1`. -/
private lemma flowVar_coeff_nonneg (n : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (j : Fin n) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m (flowVar n θ j) := by
  intro m
  unfold flowVar
  rw [coeff_add]
  have h1 : ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m (MvPolynomial.C (1 - θ) * (X j : MvPolynomial (Fin n) ℝ)) := by
    intro m'
    exact coeff_C_mul_nonneg (sub_nonneg.mpr hθ1) (coeff_X_nonneg j) m'
  have h2 : ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m (MvPolynomial.C θ * (∑ i : Fin n, (X i : MvPolynomial (Fin n) ℝ))) := by
    intro m'
    exact coeff_C_mul_nonneg hθ0 (coeff_sumX_nonneg n) m'
  exact add_nonneg (h1 m) (h2 m)

/-- Substituting into a polynomial with nonnegative coefficients yields nonnegative
coefficients, provided every substituted variable also has nonnegative coefficients. -/
private lemma aeval_coeff_nonneg {n : ℕ} {g : Fin n → MvPolynomial (Fin n) ℝ}
    (hg : ∀ j : Fin n, ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m (g j)) :
    ∀ p : MvPolynomial (Fin n) ℝ, (∀ m : Fin n →₀ ℕ, 0 ≤ coeff m p) →
      ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m (MvPolynomial.aeval (fun j : Fin n => g j) p) := by
  classical
  intro p hp m
  rw [MvPolynomial.as_sum p, map_sum]
  rw [coeff_sum]
  refine Finset.sum_nonneg (fun v hv => ?_)
  have hc : 0 ≤ coeff v p := hp v
  have hae := MvPolynomial.aeval_monomial (R := ℝ) (S₁ := MvPolynomial (Fin n) ℝ)
    (g := fun j : Fin n => g j) (d := v) (r := coeff v p)
  have hae' : MvPolynomial.aeval (fun j : Fin n => g j) (MvPolynomial.monomial v (coeff v p)) =
      MvPolynomial.C (coeff v p) * v.prod (fun i k => g i ^ k) := by
    simpa using hae
  rw [hae']
  rw [coeff_C_mul]
  change 0 ≤ coeff v p * coeff m (v.support.prod (fun i : Fin n => (g i) ^ (v i)))
  exact mul_nonneg hc (coeff_prod_nonneg v.support (fun i : Fin n => (g i) ^ (v i))
    (fun i m' => coeff_pow_nonneg (hg i) (v i) m') m)

/-- The flow substitution preserves nonnegativity of all coefficients (`0 ≤ θ ≤ 1`). -/
private lemma flowSubst_coeff_nonneg (n : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (p : MvPolynomial (Fin n) ℝ) (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m p) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ coeff m (MvPolynomial.aeval (fun j : Fin n => flowVar n θ j) p) :=
  aeval_coeff_nonneg (n := n) (g := fun j : Fin n => flowVar n θ j)
    (flowVar_coeff_nonneg n θ hθ0 hθ1) p hp




private lemma pderiv_aeval {n : ℕ} (i : Fin n) (g : Fin n → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.pderiv i (MvPolynomial.aeval (fun j : Fin n => g j) p) =
      ∑ j : Fin n, MvPolynomial.aeval (fun j : Fin n => g j) (MvPolynomial.pderiv j p) *
        MvPolynomial.pderiv i (g j) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q ihp ihq =>
      calc
        MvPolynomial.pderiv i (MvPolynomial.aeval (fun j : Fin n => g j) (p + q))
            = MvPolynomial.pderiv i (MvPolynomial.aeval (fun j : Fin n => g j) p) +
                MvPolynomial.pderiv i (MvPolynomial.aeval (fun j : Fin n => g j) q) := by
                rw [map_add]
                exact (MvPolynomial.pderiv i).map_add _ _
        _ = (∑ j : Fin n, MvPolynomial.aeval (fun j : Fin n => g j) (MvPolynomial.pderiv j p) *
                MvPolynomial.pderiv i (g j)) +
              (∑ j : Fin n, MvPolynomial.aeval (fun j : Fin n => g j) (MvPolynomial.pderiv j q) *
                MvPolynomial.pderiv i (g j)) := by rw [ihp, ihq]
        _ = ∑ j : Fin n, MvPolynomial.aeval (fun j : Fin n => g j)
                (MvPolynomial.pderiv j p + MvPolynomial.pderiv j q) *
              MvPolynomial.pderiv i (g j) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro j hj
              rw [map_add]
              ring
        _ = ∑ j : Fin n, MvPolynomial.aeval (fun j : Fin n => g j) (MvPolynomial.pderiv j (p + q)) *
              MvPolynomial.pderiv i (g j) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hA : (MvPolynomial.pderiv j) p + (MvPolynomial.pderiv j) q =
                  (MvPolynomial.pderiv j) (p + q) := ((MvPolynomial.pderiv j).map_add p q).symm
              rw [hA]
  | mul_X p k ih =>
      calc
        MvPolynomial.pderiv i (MvPolynomial.aeval (fun j : Fin n => g j) (p * (X k : MvPolynomial (Fin n) ℝ)))
            = MvPolynomial.pderiv i (MvPolynomial.aeval (fun j : Fin n => g j) p * g k) := by
                rw [map_mul, aeval_X]
        _ = MvPolynomial.pderiv i (MvPolynomial.aeval (fun j : Fin n => g j) p) * g k +
              MvPolynomial.aeval (fun j : Fin n => g j) p * MvPolynomial.pderiv i (g k) := by
                rw [pderiv_mul]
        _ = (∑ j : Fin n, MvPolynomial.aeval (fun j : Fin n => g j) (MvPolynomial.pderiv j p) *
                MvPolynomial.pderiv i (g j)) * g k +
              MvPolynomial.aeval (fun j : Fin n => g j) p * MvPolynomial.pderiv i (g k) := by
                rw [ih]
        _ = ∑ j : Fin n, MvPolynomial.aeval (fun j : Fin n => g j)
                (MvPolynomial.pderiv j (p * (X k : MvPolynomial (Fin n) ℝ))) *
              MvPolynomial.pderiv i (g j) := by
              let A : Fin n → MvPolynomial (Fin n) ℝ := fun j => MvPolynomial.aeval (fun j => g j) (MvPolynomial.pderiv j p)
              let B : MvPolynomial (Fin n) ℝ := g k
              let D : MvPolynomial (Fin n) ℝ := MvPolynomial.aeval (fun j => g j) p
              let C : Fin n → MvPolynomial (Fin n) ℝ := fun j => MvPolynomial.pderiv i (g j)
              have hterm : ∀ j : Fin n,
                  MvPolynomial.aeval (fun j : Fin n => g j) (MvPolynomial.pderiv j (p * (X k : MvPolynomial (Fin n) ℝ))) =
                    A j * B + (if j = k then D else 0) := by
                intro j
                dsimp [A, B, D]
                rw [pderiv_mul, pderiv_X]
                by_cases hjk : j = k
                · subst k
                  simp [map_add, map_mul, aeval_X]
                · simp [hjk, map_add, map_mul, aeval_X]
              have hY : (∑ j : Fin n, (if j = k then D else (0 : MvPolynomial (Fin n) ℝ)) * C j) =
                  D * C k := by
                rw [Finset.sum_eq_single k]
                · simp
                · intro j hj hjk
                  simp [hjk]
                · intro hk
                  exact False.elim (hk (Finset.mem_univ k))
              calc
                (∑ j, A j * C j) * B + D * C k
                    = ∑ j, (A j * B + (if j = k then D else 0)) * C j := by
                        -- RHS: split and pull B
                        calc
                          (∑ j, A j * C j) * B + D * C k
                              = B * (∑ j, A j * C j) + D * C k := by ring
                          _ = (∑ j, B * (A j * C j)) + D * C k := by rw [Finset.mul_sum]
                          _ = (∑ j, A j * B * C j) + D * C k := by
                                  apply congrArg (fun x : MvPolynomial (Fin n) ℝ => x + D * C k)
                                  apply Finset.sum_congr rfl
                                  intro j hj
                                  ring
                          _ = (∑ j, A j * B * C j) + (∑ j, (if j = k then D else 0) * C j) := by
                                  rw [← hY]
                          _ = ∑ j, (A j * B * C j + (if j = k then D else 0) * C j) := by
                                  rw [Finset.sum_add_distrib]
                          _ = ∑ j, (A j * B + (if j = k then D else 0)) * C j := by
                                  apply Finset.sum_congr rfl
                                  intro j hj
                                  ring
                _ = ∑ j, (MvPolynomial.aeval (fun j : Fin n => g j)
                        (MvPolynomial.pderiv j (p * (X k : MvPolynomial (Fin n) ℝ)))) * C j := by
                        apply Finset.sum_congr rfl
                        intro j hj
                        rw [hterm j]
                _ = ∑ j, (MvPolynomial.aeval (fun j : Fin n => g j)
                        (MvPolynomial.pderiv j (p * (X k : MvPolynomial (Fin n) ℝ)))) *
                      MvPolynomial.pderiv i (g j) := by rfl


/-- `∂_i (flowVar n θ j) = C ((1−θ)·δ_{ij} + θ)`. -/
private lemma pderiv_flowVar (n : ℕ) (θ : ℝ) (i j : Fin n) :
    MvPolynomial.pderiv i (flowVar n θ j) =
      MvPolynomial.C ((1 - θ) * (if i = j then 1 else 0) + θ) := by
  classical
  unfold flowVar
  rw [map_add, pderiv_C_mul, pderiv_C_mul]
  rw [pderiv_X]
  have hsum : MvPolynomial.pderiv i (∑ k : Fin n, (X k : MvPolynomial (Fin n) ℝ)) = 1 := by
    rw [map_sum]
    rw [Finset.sum_eq_single i]
    · simp
    · intro k hk hki
      rw [pderiv_X]
      simp [hki]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  rw [hsum]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij]

private noncomputable def flowDeriv (n : ℕ) (θ : ℝ) (i : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ j : Fin n, MvPolynomial.C ((1 - θ) * (if j = i then 1 else 0) + θ) * MvPolynomial.pderiv j p

private lemma flow_pderiv (n : ℕ) (θ : ℝ) (i : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.pderiv i (MvPolynomial.aeval (fun j : Fin n => flowVar n θ j) p) =
      MvPolynomial.aeval (fun j : Fin n => flowVar n θ j) (flowDeriv n θ i p) := by
  classical
  rw [pderiv_aeval]
  simp_rw [pderiv_flowVar]
  have hif : ∀ j : Fin n, ((1 - θ) * (if i = j then 1 else 0) + θ) =
      ((1 - θ) * (if j = i then 1 else 0) + θ) := by
    intro j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij, Ne.symm hij]
  -- now goal: Σ_j aeval g (∂_j p) * C (b j) = aeval g (Σ_j C (b' j) * ∂_j p) where b j = (1-θ)(if i=j...)+θ and b' j = (1-θ)(if j=i...)+θ
  -- show each summand equals aeval g (C (b' j) * ∂_j p), then pull the sum inside.
  have hsummand : ∀ j : Fin n,
      MvPolynomial.aeval (fun j : Fin n => flowVar n θ j) (MvPolynomial.pderiv j p) *
          MvPolynomial.C ((1 - θ) * (if i = j then 1 else 0) + θ) =
        MvPolynomial.aeval (fun j : Fin n => flowVar n θ j)
          (MvPolynomial.C ((1 - θ) * (if j = i then 1 else 0) + θ) * MvPolynomial.pderiv j p) := by
    intro j
    let c : ℝ := (1 - θ) * (if j = i then 1 else 0) + θ
    have hC : MvPolynomial.aeval (fun j : Fin n => flowVar n θ j) (MvPolynomial.C c) =
        MvPolynomial.C c := by
      simp
    calc
      MvPolynomial.aeval (fun j : Fin n => flowVar n θ j) (MvPolynomial.pderiv j p) *
            MvPolynomial.C ((1 - θ) * (if i = j then 1 else 0) + θ)
          = MvPolynomial.aeval (fun j : Fin n => flowVar n θ j) (MvPolynomial.pderiv j p) *
              MvPolynomial.C c := by
              rw [hif j]
      _ = MvPolynomial.C c * MvPolynomial.aeval (fun j : Fin n => flowVar n θ j) (MvPolynomial.pderiv j p) := by
              ring
      _ = MvPolynomial.aeval (fun j : Fin n => flowVar n θ j) (MvPolynomial.C c) *
            MvPolynomial.aeval (fun j : Fin n => flowVar n θ j) (MvPolynomial.pderiv j p) := by
              rw [hC]
      _ = MvPolynomial.aeval (fun j : Fin n => flowVar n θ j)
            (MvPolynomial.C c * MvPolynomial.pderiv j p) := by
              rw [map_mul]
      _ = MvPolynomial.aeval (fun j : Fin n => flowVar n θ j)
            (MvPolynomial.C ((1 - θ) * (if j = i then 1 else 0) + θ) * MvPolynomial.pderiv j p) := by
              rfl
  rw [show (∑ j : Fin n, MvPolynomial.aeval (fun j : Fin n => flowVar n θ j) (MvPolynomial.pderiv j p) *
        MvPolynomial.C ((1 - θ) * (if i = j then 1 else 0) + θ)) =
      (∑ j : Fin n, MvPolynomial.aeval (fun j : Fin n => flowVar n θ j)
        (MvPolynomial.C ((1 - θ) * (if j = i then 1 else 0) + θ) * MvPolynomial.pderiv j p)) by
    exact Finset.sum_congr rfl (fun j hj => hsummand j)]
  rw [show flowDeriv n θ i p = (∑ j : Fin n,
        MvPolynomial.C ((1 - θ) * (if j = i then 1 else 0) + θ) * MvPolynomial.pderiv j p) by rfl]
  rw [map_sum]

/-! ## The flow preserves `L n d` in degrees ≤ 2 (base of the induction) -/

/-- The flow maps `S n d` into itself (`0 ≤ θ ≤ 1`). -/
private lemma flowSubst_mem_S (n d : ℕ) (hn : 0 < n) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (f : H n d) (hf : f ∈ S n d) : flowSubst (n := n) (d := d) θ f ∈ S n d := by
  constructor
  · exact flowSubst_IsStable n hn θ hθ0 hθ1 f.1 hf.1
  · intro m
    exact flowSubst_coeff_nonneg n θ hθ0 hθ1 f.1 hf.2 m

/-- If two polynomials agree, membership in `S`, `M` and `L` transfers. -/
private lemma L_mem_of_val_eq {n d : ℕ} {f g : H n d} (hfg : f.1 = g.1) : g ∈ L n d → f ∈ L n d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro hg
      cases d with
      | zero =>
          have : S n 0 = L n 0 := by rfl
          rw [← this] at hg ⊢
          rcases hg with ⟨hstab, hnon⟩
          constructor
          · simpa [hfg] using hstab
          · intro m
            rw [hfg]
            exact hnon m
      | succ d0 =>
          cases d0 with
          | zero =>
              have : S n 1 = L n 1 := by rfl
              rw [← this] at hg ⊢
              rcases hg with ⟨hstab, hnon⟩
              constructor
              · simpa [hfg] using hstab
              · intro m
                rw [hfg]
                exact hnon m
          | succ d1 =>
              cases d1 with
              | zero =>
                  have : S n 2 = L n 2 := by rfl
                  rw [← this] at hg ⊢
                  rcases hg with ⟨hstab, hnon⟩
                  constructor
                  · simpa [hfg] using hstab
                  · intro m
                    rw [hfg]
                    exact hnon m
              | succ k =>
                  -- d = k+3 ≥ 3
                  rcases hg with ⟨hM, hder⟩
                  constructor
                  · -- M n (k+3) membership: M-convex support + nonneg coeffs, both on f.1
                    rcases hM with ⟨hconv, hnon⟩
                    constructor
                    · simpa [hfg] using hconv
                    · intro m
                      rw [hfg]
                      exact hnon m
                  · intro i
                    exact ih (k + 2) (by omega) (f := ⟨f.1.pderiv i, f.2.pderiv⟩)
                      (g := ⟨g.1.pderiv i, g.2.pderiv⟩) (by simp [hfg]) (hder i)

/-- The flow preserves `L n d` for `d ≤ 2`. -/
private lemma flowSubst_mem_L_low (n d : ℕ) (hn : 0 < n) (hd : d ≤ 2)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (f : H n d) (hf : f ∈ L n d) :
    flowSubst (n := n) (d := d) θ f ∈ L n d := by
  have hfS : f ∈ S n d := by
    have : L n d = S n d := by
      rcases d with _ | d
      · rfl
      · rcases d with _ | d
        · rfl
        · rcases d with _ | d
          · rfl
          · exfalso
            omega
    rwa [this] at hf
  have hgS := flowSubst_mem_S n d hn θ hθ0 hθ1 f hfS
  have : L n d = S n d := by
    rcases d with _ | d
    · rfl
    · rcases d with _ | d
      · rfl
      · rcases d with _ | d
        · rfl
        · exfalso
          omega
  rw [this]
  exact hgS

/-! ## auxiliary facts for the inductive assembly -/

/-- the zero polynomial as an element of `H n d`. -/
private noncomputable def zeroH (n d : ℕ) : H n d := ⟨0, by simp⟩

private lemma zeroH_val (n d : ℕ) : (zeroH n d).1 = 0 := rfl

/-- the zero polynomial is in `S n d`. -/
private lemma zeroH_mem_S (n d : ℕ) : zeroH n d ∈ S n d := by
  unfold S
  constructor
  · left
    rfl
  · intro m
    rw [zeroH_val]
    simp

/-- the zero polynomial is in `M n d`. -/
private lemma zeroH_mem_M (n d : ℕ) : zeroH n d ∈ M n d := by
  unfold M
  constructor
  · have hsupp : ((zeroH n d).1.support : Set (Fin n →₀ ℕ)) = ∅ := by
      rw [zeroH_val]
      simp
    rw [hsupp]
    intro α hα β hβ i hi
    exact False.elim hα
  · intro m
    rw [zeroH_val]
    simp

/-- the zero polynomial is Lorentzian. -/
private lemma zeroH_mem_L (n d : ℕ) : zeroH n d ∈ L n d := by
  classical
  induction d using Nat.strong_induction_on with
  | h d ih =>
      cases d with
      | zero =>
          have : L n 0 = S n 0 := by rfl
          rw [this]
          exact zeroH_mem_S n 0
      | succ d0 =>
          cases d0 with
          | zero =>
              have : L n 1 = S n 1 := by rfl
              rw [this]
              exact zeroH_mem_S n 1
          | succ d1 =>
              cases d1 with
              | zero =>
                  have : L n 2 = S n 2 := by rfl
                  rw [this]
                  exact zeroH_mem_S n 2
              | succ k =>
                  change zeroH n (k + 3) ∈ {x : H n (k + 3) | x ∈ M n (k + 3) ∧
                    ∀ i : Fin n, ⟨x.1.pderiv i, x.2.pderiv⟩ ∈ L n (k + 2)}
                  constructor
                  · exact zeroH_mem_M n (k + 3)
                  · intro i
                    let z : H n (k + 3) := zeroH n (k + 3)
                    have hp : (⟨z.1.pderiv i, z.2.pderiv⟩ : H n (k + 2)).1 = (zeroH n (k + 2)).1 := by
                      change z.1.pderiv i = (zeroH n (k + 2)).1
                      have hz : z.1 = (0 : MvPolynomial (Fin n) ℝ) := rfl
                      have hz2 : (zeroH n (k + 2)).1 = (0 : MvPolynomial (Fin n) ℝ) := rfl
                      rw [hz, hz2]
                      simp
                    exact L_mem_of_val_eq (n := n) (d := k + 2)
                      (f := ⟨z.1.pderiv i, z.2.pderiv⟩) (g := zeroH n (k + 2)) hp
                      (ih (k + 2) (by omega))

/-- `S_θ 0 = 0`. -/
private lemma flowSubst_zero (n d : ℕ) (θ : ℝ) :
    flowSubst (n := n) (d := d) θ (zeroH n d) = zeroH n d := by
  apply Subtype.ext
  change MvPolynomial.aeval (fun j : Fin n => flowVar n θ j) (0 : MvPolynomial (Fin n) ℝ) = 0
  simp

/-- `S_0 f = f`. -/
private lemma flowSubst_eq_self_of_theta_zero (n d : ℕ) (f : H n d) :
    flowSubst (n := n) (d := d) (0 : ℝ) f = f := by
  apply Subtype.ext
  change MvPolynomial.aeval (fun j : Fin n =>
      MvPolynomial.C (1 - (0 : ℝ)) * MvPolynomial.X j +
        MvPolynomial.C (0 : ℝ) * (∑ i : Fin n, MvPolynomial.X i)) f.1 = f.1
  exact substS_at_zero n d f

/-- every member of `L` has nonnegative coefficients. -/
private lemma L_coeff_nonneg (n d : ℕ) (f : H n d) (hf : f ∈ L n d) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m :=
  L_mem_nonneg n d f hf

/-! ## The flow theorem for `L`: main induction -/

/-- The flow substitution keeps `L n d` inside `L n d` for `0 ≤ θ ≤ 1`. -/
private theorem flowSubst_mem_L_all (n : ℕ) (hn : 0 < n) :
    ∀ (d : ℕ) (θ : ℝ), 0 ≤ θ → θ ≤ 1 → ∀ f : H n d, f ∈ L n d →
      flowSubst (n := n) (d := d) θ f ∈ L n d := by
  classical
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro θ hθ0 hθ1 f hf
      by_cases hd3 : 3 ≤ d
      · obtain ⟨k, rfl⟩ : ∃ k : ℕ, d = k + 3 := ⟨d - 3, by omega⟩
        by_cases hf0 : f = zeroH n (k + 3)
        · have hz : flowSubst (n := n) (d := k + 3) θ f = zeroH n (k + 3) := by
            rw [hf0]
            exact flowSubst_zero n (k + 3) θ
          rw [hz]
          exact zeroH_mem_L n (k + 3)
        · by_cases hθ0' : θ = 0
          · have hid : flowSubst (n := n) (d := k + 3) θ f = f := by
              rw [hθ0']
              exact flowSubst_eq_self_of_theta_zero n (k + 3) f
            rw [hid]
            exact hf
          · have hθpos : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθ0')
            change flowSubst (n := n) (d := k + 3) θ f ∈ {x : H n (k + 3) | x ∈ M n (k + 3) ∧
              ∀ i : Fin n, ⟨x.1.pderiv i, x.2.pderiv⟩ ∈ L n (k + 2)}
            constructor
            · have hP : flowSubst (n := n) (d := k + 3) θ f ∈ P n (k + 3) := by
                intro m hm
                change 0 < (MvPolynomial.aeval (fun j : Fin n => flowVar n θ j) f.1).coeff m
                exact Commons.Algebra.MvPolynomial.subst_coeff_pos n (k + 3) f.1 (L_coeff_nonneg n (k + 3) f hf)
                  (by
                    intro hzero
                    apply hf0
                    apply Subtype.ext
                    change f.1 = (zeroH n (k + 3)).1
                    rw [hzero]
                    rfl)
                  ((MvPolynomial.mem_homogeneousSubmodule (σ := Fin n) (R := ℝ) (k + 3) f.1).mp f.2)
                  hθpos hθ1 m hm
              exact P_subset_M n (k + 3) hP
            · intro i
              let u : Fin n → ℝ := fun j => (1 - θ) * (if i = j then 1 else 0) + θ
              have hu : ∀ j : Fin n, 0 ≤ u j := by
                intro j
                dsimp [u]
                by_cases hij : i = j
                · subst j
                  have h1 : (1 - θ) * (1 : ℝ) + θ = 1 := by ring
                  rw [if_pos rfl, h1]
                  norm_num
                · rw [if_neg hij]
                  simpa using hθ0
              rcases directional_deriv_mem_L n (k + 3) hn (by omega : 1 ≤ k + 3) f hf u hu
                with ⟨h, hhL, hval⟩
              have hstep := ih (k + 2) (by omega) θ hθ0 hθ1 h hhL
              have hderEq : flowDeriv n θ i f.1 = h.1 := by
                rw [hval]
                apply Finset.sum_congr rfl
                intro j hj
                congr 1
                dsimp [u]
                by_cases hij : i = j
                · subst j
                  simp
                · simp [hij, Ne.symm hij]
              have hchain : (flowSubst (n := n) (d := k + 2) θ h).1 =
                  (flowSubst (n := n) (d := k + 3) θ f).1.pderiv i := by
                calc
                  (flowSubst (n := n) (d := k + 2) θ h).1
                      = MvPolynomial.aeval (fun j : Fin n => flowVar n θ j) h.1 := rfl
                  _ = MvPolynomial.aeval (fun j : Fin n => flowVar n θ j) (flowDeriv n θ i f.1) := by
                        rw [hderEq]
                  _ = MvPolynomial.pderiv i (MvPolynomial.aeval (fun j : Fin n => flowVar n θ j) f.1) := by
                        exact (flow_pderiv n θ i f.1).symm
                  _ = (flowSubst (n := n) (d := k + 3) θ f).1.pderiv i := by
                        rfl
              let part : H n (k + 2) := ⟨(flowSubst (n := n) (d := k + 3) θ f).1.pderiv i,
                (flowSubst (n := n) (d := k + 3) θ f).2.pderiv⟩
              exact L_mem_of_val_eq (n := n) (d := k + 2) (f := part)
                (g := flowSubst (n := n) (d := k + 2) θ h) (by
                  change part.1 = (flowSubst (n := n) (d := k + 2) θ h).1
                  exact hchain.symm) hstep
      · exact flowSubst_mem_L_low n d hn (by omega) θ hθ0 hθ1 f hf

/-- The main statement: for `f ∈ L n d` and `0 ≤ θ ≤ 1`, the substituted polynomial
`f((1−θ)·X + θ·(Σᵢ Xᵢ))` is again Lorentzian. -/
theorem flow_substS_mem_L (n d : ℕ) (hn : 0 < n) (f : H n d) (hf : f ∈ L n d) :
    ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ∃ g : H n d, g ∈ L n d ∧
        g.1 = MvPolynomial.aeval (fun j : Fin n =>
          MvPolynomial.C (1 - θ) * MvPolynomial.X j +
            MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i)) f.1 := by
  intro θ hθ0 hθ1
  refine ⟨flowSubst (n := n) (d := d) θ f, ?_, ?_⟩
  · exact flowSubst_mem_L_all n hn d θ hθ0 hθ1 f hf
  · rfl
