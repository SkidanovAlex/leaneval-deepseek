import Mathlib
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.LorentzianPolynomials.closure_strict_eq_L_of_degree_le_two
import Submission.Commons.LorentzianPolynomials.P_subset_M
import Submission.Commons.LorentzianPolynomials.quad_deform_stable
import Submission.Commons.Data.List.erase_append_perm
import Submission.Commons.LorentzianPolynomials.deform_mem_L
import Submission.Commons.LorentzianPolynomials.rayleigh_of_hessian_roots_le_one
import Submission.Commons.Combinatorics.MvPolynomial.interval_convex_of_rayleigh
import Submission.Commons.LinearAlgebra.Matrix.quadratic_stable_iff_roots_card_le_one
import Submission.Commons.Data.Real.sq_gt_of_two_roots_quad
import Submission.Commons.LinearAlgebra.Matrix.negDef_ker_pos_implies_strict
import Submission.Commons.LinearAlgebra.Matrix.perron_vector_of_nonneg_symm_card_pos_le_one_pos

namespace Commons.LorentzianPolynomials

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set
open scoped BigOperators
open Commons.LinearAlgebra.Matrix

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

noncomputable section

/-- partial derivative `H(n,k+1) → H(n,k)` -/
def nuij_pderivH {n : ℕ} (k : ℕ) (i : Fin n) : H n (k + 1) →ₗ[ℝ] H n k where
  toFun f := ⟨pderiv i f.1, f.2.pderiv⟩
  map_add' f g := by
    apply Subtype.ext
    exact Derivation.map_add (pderiv i) f.1 g.1
  map_smul' a f := by
    apply Subtype.ext
    exact Derivation.map_smul (pderiv i) a f.1

/-- multiplication by `X i`: `H(n,k) → H(n,k+1)` -/
def nuij_mulXH {n : ℕ} (k : ℕ) (i : Fin n) : H n k →ₗ[ℝ] H n (k + 1) where
  toFun f := ⟨X i * f.1, by
    have hf : f.1.IsHomogeneous k := f.2
    have hX : (X i : MvPolynomial (Fin n) ℝ).IsHomogeneous 1 := MvPolynomial.isHomogeneous_X ℝ i
    have hdeg : 1 + k = k + 1 := by omega
    simpa [hdeg] using hX.mul hf⟩
  map_add' f g := by
    apply Subtype.ext
    change X i * (f.1 + g.1) = X i * f.1 + X i * g.1
    rw [mul_add]
  map_smul' a f := by
    apply Subtype.ext
    change X i * (a • f.1) = a • (X i * f.1)
    rw [Algebra.smul_def, Algebra.smul_def]
    ring

/-- the deformation endomorphism on `H n (k+1)`: `f ↦ (1 + θ·X_i·∂_s) f` -/
def nuij_deformEnd {n : ℕ} (k : ℕ) (i s : Fin n) (θ : ℝ) : Module.End ℝ (H n (k + 1)) :=
  LinearMap.id + (θ • ((nuij_mulXH k i).comp (nuij_pderivH k s)))

/-- power `(1 + θ·X_i·∂_s)^d` acting on `H n d` -/
def nuij_power {n : ℕ} (i s : Fin n) (d : ℕ) (θ : ℝ) : Module.End ℝ (H n d) :=
  match d with
  | 0 => 1
  | k + 1 => (nuij_deformEnd (n := n) (k := k) i s θ) ^ (k + 1)

/-- `T_n(θ,f) = ∏_{i ∈ [0,n-2]} (1 + θ·X_i·∂_s)^d f`, with `s = n-1`. -/
def nuij_T {n d : ℕ} (hn2 : 2 ≤ n) (θ : ℝ) (f : H n d) : H n d :=
  let s : Fin n := ⟨n - 1, by omega⟩
  let idx : List (Fin n) := (List.finRange (n - 1)).map (fun i : Fin (n - 1) => ⟨i.1, by omega⟩)
  idx.foldl (fun acc i => (nuij_power i s d θ) acc) f

-- basic value lemmas for subtype H
lemma H_add_val {n d : ℕ} (f g : H n d) : (f + g).1 = f.1 + g.1 := by
  dsimp [H]
  exact Submodule.coe_add f g

lemma H_smul_val {n d : ℕ} (a : ℝ) (f : H n d) : (a • f).1 = a • f.1 := by
  dsimp [H]
  exact Submodule.coe_smul a f

lemma nuij_pderivH_apply {n : ℕ} (k : ℕ) (i : Fin n) (f : H n (k + 1)) :
    (nuij_pderivH k i f).1 = pderiv i f.1 := rfl

lemma nuij_mulXH_apply {n : ℕ} (k : ℕ) (i : Fin n) (f : H n k) :
    (nuij_mulXH k i f).1 = X i * f.1 := rfl

/-- the deformed polynomial `(1 + θ·X_i·∂_s)f` is homogeneous of the same degree -/
lemma nuij_deformH_homogeneous {n : ℕ} (k : ℕ) (i s : Fin n) (θ : ℝ) (f : H n (k + 1)) :
    (f.1 + (C θ) * X i * pderiv s f.1).IsHomogeneous (k + 1) := by
  have hf : f.1.IsHomogeneous (k + 1) := f.2
  have hpd : (pderiv s f.1).IsHomogeneous k := hf.pderiv
  have hX : (X i : MvPolynomial (Fin n) ℝ).IsHomogeneous 1 := MvPolynomial.isHomogeneous_X ℝ i
  have hC : ((C θ) : MvPolynomial (Fin n) ℝ).IsHomogeneous 0 := MvPolynomial.isHomogeneous_C (Fin n) θ
  have hCX : ((C θ) * X i : MvPolynomial (Fin n) ℝ).IsHomogeneous 1 := by
    have hdeg : 0 + 1 = 1 := by omega
    simpa [hdeg] using hC.mul hX
  have hprod : ((C θ) * X i * pderiv s f.1).IsHomogeneous (k + 1) := by
    have hdeg : 1 + k = k + 1 := by omega
    simpa [hdeg] using hCX.mul hpd
  exact hf.add hprod

/-- the H-element version of the deformed polynomial -/
def nuij_deformH {n : ℕ} (k : ℕ) (i s : Fin n) (θ : ℝ) (f : H n (k + 1)) : H n (k + 1) :=
  ⟨f.1 + (C θ) * X i * pderiv s f.1, nuij_deformH_homogeneous k i s θ f⟩

lemma nuij_deformEnd_eq_deformH {n : ℕ} (k : ℕ) (i s : Fin n) (θ : ℝ) (f : H n (k + 1)) :
    (nuij_deformEnd (n := n) (k := k) i s θ) f = nuij_deformH k i s θ f := by
  apply Subtype.ext
  change ((nuij_deformEnd (n := n) (k := k) i s θ) f).1 =
    f.1 + (C θ) * X i * pderiv s f.1
  simp [H_add_val, H_smul_val, nuij_pderivH_apply, nuij_mulXH_apply, nuij_deformEnd,
    Algebra.smul_def, mul_assoc, add_assoc, add_comm, add_left_comm]

lemma nuij_deformEnd_apply_val {n : ℕ} (k : ℕ) (i s : Fin n) (θ : ℝ) (f : H n (k + 1)) :
    ((nuij_deformEnd (n := n) (k := k) i s θ) f).1 = f.1 + (C θ) * X i * pderiv s f.1 := by
  simp [H_add_val, H_smul_val, nuij_pderivH_apply, nuij_mulXH_apply, nuij_deformEnd,
    Algebra.smul_def, mul_assoc, add_assoc, add_comm, add_left_comm]

/-- the polynomial deformation `f ↦ f + θ·w_i·∂_s f` -/
def nuij_deformPoly {n : ℕ} (i s : Fin n) (θ : ℝ) (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  p + (C θ) * X i * pderiv s p

-- =====================================================================
-- monomial / coefficient helpers
-- =====================================================================

/-- unit vector exponent -/
abbrev ne (n : ℕ) (i : Fin n) : Fin n →₀ ℕ := Finsupp.single i 1

/-- A member of `P n d` has all coefficients nonnegative (positive in degree `d`). -/
lemma P_coeff_nonneg {n d : ℕ} (f : H n d) (hf : f ∈ P n d) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m := by
  intro m
  by_cases hm : Finsupp.weight (1 : Fin n → ℕ) m = d
  · exact le_of_lt (hf m hm)
  · have hh : f.1.IsWeightedHomogeneous (1 : Fin n → ℕ) d := by
      simpa [MvPolynomial.IsHomogeneous] using f.2
    have hz := MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero hh m hm
    rw [hz]

lemma ne_add_sub_cancel {n : ℕ} (i : Fin n) (m : Fin n →₀ ℕ) (hi : 0 < m i) :
    ne n i + (m - ne n i) = m := by
  ext a
  by_cases hai : a = i
  · subst a
    simp [ne]
    omega
  · simp [ne, hai]

lemma coeff_X_mul_of_pos {n : ℕ} (i : Fin n) (m : Fin n →₀ ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hi : 0 < m i) : MvPolynomial.coeff m (X i * p) = MvPolynomial.coeff (m - ne n i) p := by
  classical
  have h := MvPolynomial.coeff_X_mul (m - ne n i) i p
  have h' : coeff (ne n i + (m - ne n i)) (X i * p) = coeff (m - ne n i) p := by simpa [ne] using h
  simpa [ne_add_sub_cancel i m hi] using h'

lemma coeff_X_mul_nonneg {n : ℕ} (i : Fin n) (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ (X i * p).coeff m := by
  classical
  intro m
  by_cases hm : 0 < m i
  · rw [coeff_X_mul_of_pos i m p hm]
    exact hp (m - ne n i)
  · have hm0 : m i = 0 := by omega
    rw [← MvPolynomial.support_sum_monomial_coeff p]
    rw [Finset.mul_sum]
    rw [MvPolynomial.coeff_sum]
    have hsum0 : (∑ x ∈ p.support, coeff m (X i * (monomial x) (coeff x p))) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      have hia : (ne n i + a) i ≠ m i := by simp [ne, hm0]
      have hne : ne n i + a ≠ m := by
        intro h
        have hc := congrArg (fun q : Fin n →₀ ℕ => q i) h
        exact hia hc
      rw [show (X i : MvPolynomial (Fin n) ℝ) = monomial (ne n i) (1 : ℝ) by simp [X, ne]]
      rw [MvPolynomial.monomial_mul]
      rw [MvPolynomial.coeff_monomial]
      simp [hne]
    rw [hsum0]

lemma coeff_pderiv_nonneg' {n : ℕ} (i : Fin n) (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ (pderiv i p).coeff m := by
  intro m
  rw [MvPolynomial.coeff_pderiv]
  exact mul_nonneg (hp (m + ne n i)) (by positivity)

/-- `(1 + θ·X_i·∂_s)` maps polynomials with nonnegative coefficients to polynomials with
nonnegative coefficients when `θ ≥ 0`. -/
lemma nuij_deformPoly_coeff_nonneg {n : ℕ} (i s : Fin n) (θ : ℝ) (hθ : 0 ≤ θ)
    (p : MvPolynomial (Fin n) ℝ) (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ (nuij_deformPoly i s θ p).coeff m := by
  classical
  intro m
  unfold nuij_deformPoly
  rw [MvPolynomial.coeff_add]
  rw [mul_assoc, MvPolynomial.coeff_C_mul]
  have h1 : 0 ≤ p.coeff m := hp m
  have h2 : 0 ≤ (X i * pderiv s p).coeff m :=
    coeff_X_mul_nonneg i (pderiv s p) (coeff_pderiv_nonneg' s p hp) m
  nlinarith [mul_nonneg hθ h2]

/-- `(1 + θ·X_i·∂_s)` preserves strict coefficient positivity of every degree-`k+1`
monomial (`P n (k+1)`), for `θ ≥ 0`. -/
lemma nuij_deformH_mem_P {n : ℕ} (k : ℕ) (i s : Fin n) (θ : ℝ) (hθ : 0 ≤ θ)
    (f : H n (k + 1)) (hf : f ∈ P n (k + 1)) : nuij_deformH k i s θ f ∈ P n (k + 1) := by
  intro m hm
  change 0 < (f.1 + (C θ) * X i * pderiv s f.1).coeff m
  rw [MvPolynomial.coeff_add]
  rw [mul_assoc, MvPolynomial.coeff_C_mul]
  have h1 : 0 < f.1.coeff m := hf m hm
  have hnn : ∀ a : Fin n →₀ ℕ, 0 ≤ (pderiv s f.1).coeff a :=
    coeff_pderiv_nonneg' s f.1 (P_coeff_nonneg f hf)
  have h2 : 0 ≤ (X i * pderiv s f.1).coeff m := coeff_X_mul_nonneg i (pderiv s f.1) hnn m
  nlinarith [mul_nonneg hθ h2]



-- =====================================================================
-- P is preserved by powers and by T
-- =====================================================================

/-- iterates of the single deformation preserve `P`. -/
lemma nuij_deformEnd_iter_mem_P {n : ℕ} (k : ℕ) (i s : Fin n) (θ : ℝ) (hθ : 0 ≤ θ)
    (m : ℕ) (f : H n (k + 1)) (hf : f ∈ P n (k + 1)) :
    ((nuij_deformEnd (n := n) (k := k) i s θ) ^ m) f ∈ P n (k + 1) := by
  revert f
  induction m with
  | zero => intro f hf; simpa using hf
  | succ m ih =>
      intro f hf
      rw [pow_succ']
      change nuij_deformEnd (n := n) (k := k) i s θ
        (((nuij_deformEnd (n := n) (k := k) i s θ) ^ m) f) ∈ P n (k + 1)
      rw [nuij_deformEnd_eq_deformH]
      exact nuij_deformH_mem_P k i s θ hθ
        (((nuij_deformEnd (n := n) (k := k) i s θ) ^ m) f) (ih f hf)

/-- power `(1+θ·X_i·∂_s)^d` acting on `H n d` preserves `P n d`. -/
lemma nuij_power_mem_P {n : ℕ} (i s : Fin n) (d : ℕ) (θ : ℝ) (hθ : 0 ≤ θ)
    (f : H n d) (hf : f ∈ P n d) : (nuij_power i s d θ) f ∈ P n d := by
  cases d with
  | zero => simpa [nuij_power] using hf
  | succ k =>
      change ((nuij_deformEnd (n := n) (k := k) i s θ) ^ (k + 1)) f ∈ P n (k + 1)
      exact nuij_deformEnd_iter_mem_P k i s θ hθ (k + 1) f hf

/-- the Nuij smoothing `T_n(θ,f)` preserves `P n d` for `θ ≥ 0`. -/
lemma nuij_T_mem_P {n d : ℕ} (hn2 : 2 ≤ n) (θ : ℝ) (hθ : 0 ≤ θ)
    (f : H n d) (hf : f ∈ P n d) : nuij_T (n := n) (d := d) hn2 θ f ∈ P n d := by
  unfold nuij_T
  let s : Fin n := ⟨n - 1, by omega⟩
  let idx : List (Fin n) := (List.finRange (n - 1)).map (fun i : Fin (n - 1) => ⟨i.1, by omega⟩)
  have hfold : ∀ (l : List (Fin n)) (acc : H n d), acc ∈ P n d →
      l.foldl (fun a i => (nuij_power i s d θ) a) acc ∈ P n d := by
    intro l
    induction l with
    | nil => intro acc hacc; simpa using hacc
    | cons a l ih =>
        intro acc hacc
        simp only [List.foldl_cons]
        exact ih ((nuij_power a s d θ) acc) (nuij_power_mem_P a s d θ hθ acc hacc)
  exact hfold idx f hf


-- =====================================================================
-- iterated partial derivatives along lists; Ŀ membership criterion
-- =====================================================================

/-- iterated partial derivative along a list of indices -/
def nuij_pderivL {n : ℕ} (l : List (Fin n)) (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  l.foldl (fun q i => pderiv i q) p

lemma nuij_pderivL_isHomogeneous {n : ℕ} (l : List (Fin n)) (p : MvPolynomial (Fin n) ℝ) (d : ℕ)
    (hp : p.IsHomogeneous d) : (nuij_pderivL l p).IsHomogeneous (d - l.length) := by
  revert p d
  induction l using List.recOn with
  | nil => intro p d hp; simpa [nuij_pderivL] using hp
  | cons i l ih =>
      intro p d hp
      change (nuij_pderivL l (pderiv i p)).IsHomogeneous (d - (i :: l).length)
      have hpd : (pderiv i p).IsHomogeneous (d - 1) := hp.pderiv
      have hstep : (nuij_pderivL l (pderiv i p)).IsHomogeneous ((d - 1) - l.length) :=
        ih (pderiv i p) (d - 1) hpd
      have hl : (i :: l).length = l.length + 1 := by simp
      have h : (d - 1) - l.length = d - (i :: l).length := by
        rw [hl]
        omega
      simpa [nuij_pderivL, h] using hstep

lemma nuij_pderivL_nil {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : nuij_pderivL [] p = p := by
  simp [nuij_pderivL]

lemma nuij_pderivL_cons {n : ℕ} (i : Fin n) (l : List (Fin n)) (p : MvPolynomial (Fin n) ℝ) :
    nuij_pderivL (i :: l) p = nuij_pderivL l (pderiv i p) := by
  rfl

lemma nuij_pderivL_append {n : ℕ} (l₁ l₂ : List (Fin n)) (p : MvPolynomial (Fin n) ℝ) :
    nuij_pderivL (l₁ ++ l₂) p = nuij_pderivL l₂ (nuij_pderivL l₁ p) := by
  induction l₁ generalizing p with
  | nil => simp [nuij_pderivL]
  | cons i l₁ ih =>
      change nuij_pderivL (i :: l₁ ++ l₂) p = nuij_pderivL l₂ (nuij_pderivL (i :: l₁) p)
      rw [show nuij_pderivL (i :: l₁ ++ l₂) p = nuij_pderivL (l₁ ++ l₂) (pderiv i p) by rfl]
      rw [ih (pderiv i p)]
      rfl

/-- partial derivative of a `P`-element (degree `k+1`) along one variable stays in `P` of
degree `k`. -/
lemma pderivH_mem_P {n : ℕ} (k : ℕ) (i : Fin n) (f : H n (k + 1)) (hf : f ∈ P n (k + 1)) :
    (⟨pderiv i f.1, f.2.pderiv⟩ : H n k) ∈ P n k := by
  intro m hm
  change 0 < (pderiv i f.1).coeff m
  rw [MvPolynomial.coeff_pderiv]
  have hmw : Finsupp.weight (1 : Fin n → ℕ) (m + ne n i) = k + 1 := by
    rw [map_add, Finsupp.weight_single, hm]
    simp [ne]
  have hpos : 0 < f.1.coeff (m + ne n i) := hf (m + ne n i) hmw
  positivity

/-- the `(d-2)`-fold iterated partial, presented as a quadratic element of `H n 2`
(given `l.length = d - 2`). -/
def pderivL2 {n d : ℕ} (hd : 2 ≤ d) (l : List (Fin n)) (h : l.length = d - 2) (f : H n d) : H n 2 :=
  ⟨nuij_pderivL l f.1, by
    have hdeg : d - l.length = 2 := by omega
    have hh := nuij_pderivL_isHomogeneous l f.1 d f.2
    simpa [hdeg] using hh⟩

lemma pderivL2_val {n d : ℕ} (hd : 2 ≤ d) (l : List (Fin n)) (h : l.length = d - 2) (f : H n d) :
    (pderivL2 hd l h f).1 = nuij_pderivL l f.1 := rfl

/-- `Ŀ`-membership criterion for degree `d ≥ 2`: positive coefficients and all
`(d-2)`-fold partial derivatives in `Ŀ n 2` forces membership in `Ŀ n d`. -/
lemma strict_mem_of_pderivs {n d : ℕ} (hd : 2 ≤ d) (f : H n d) (hP : f ∈ P n d)
    (hder : ∀ (l : List (Fin n)) (h : l.length = d - 2),
      pderivL2 hd l h f ∈ Ŀ n 2) :
    f ∈ Ŀ n d := by
  revert hd f hP hder
  induction d with
  | zero => intro hd; omega
  | succ d ih =>
      cases d with
      | zero => intro hd; omega
      | succ d2 =>
          cases d2 with
          | zero =>
              -- degree 2
              intro hd f hP hder
              change f ∈ Ŀ n 2
              have hlen : ([] : List (Fin n)).length = 2 - 2 := by simp
              have hmem := hder [] hlen
              have heq : pderivL2 hd ([] : List (Fin n)) hlen f = f := by
                apply Subtype.ext
                change nuij_pderivL [] f.1 = f.1
                simp [nuij_pderivL]
              simpa [heq] using hmem
          | succ k =>
              -- degree k + 3
              intro hd f hP hder
              change f ∈ {f : H n (k + 3) | f ∈ P n (k + 3) ∧
                ∀ i : Fin n, (⟨f.1.pderiv i, f.2.pderiv⟩ : H n (k + 2)) ∈ Ŀ n (k + 2)}
              constructor
              · exact hP
              · intro i
                let g : H n (k + 2) := ⟨f.1.pderiv i, f.2.pderiv⟩
                have hgP : g ∈ P n (k + 2) := by
                  change (⟨f.1.pderiv i, f.2.pderiv⟩ : H n (k + 2)) ∈ P n (k + 2)
                  exact pderivH_mem_P (k + 2) i f hP
                have hk2 : 2 ≤ k + 2 := by omega
                refine ih hk2 g hgP ?_
                intro l hl
                have hlen : (i :: l).length = (k + 3) - 2 := by
                  have hlk : l.length = k := by omega
                  simp [hlk]
                have hmain := hder (i :: l) hlen
                have hval : (pderivL2 hk2 l hl g).1 = (pderivL2 hd (i :: l) hlen f).1 := by
                  change nuij_pderivL l (pderiv i f.1) = nuij_pderivL (i :: l) f.1
                  rw [nuij_pderivL_cons]
                have heq : pderivL2 hk2 l hl g = pderivL2 hd (i :: l) hlen f := by
                  apply Subtype.ext
                  exact hval
                simpa [heq] using hmain

-- =====================================================================
-- quadratic restriction analysis on lines (direction `s`)
-- =====================================================================

open Commons.LinearAlgebra.Matrix
open rayleigh_pre

lemma aeval_ofReal_eval (n : ℕ) (w : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.aeval (fun j : Fin n => (w j : ℂ)) p = (MvPolynomial.eval w p : ℂ) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
      rw [map_add, map_add]
      simp [hp, hq]
  | mul_X p i hp =>
      rw [map_mul, map_mul]
      rw [MvPolynomial.aeval_X]
      simp [hp]

/-- For homogeneous quadratics: `2 * eval w f = quadReal f.hessian w w`. -/
lemma eval_two_quadReal (n : ℕ) (f : H n 2) (w : Fin n → ℝ) :
    (2 : ℝ) * MvPolynomial.eval w f.1 = quadReal f.hessian w w := by
  classical
  have h := hessian_aeval_eq n f (fun j : Fin n => (w j : ℂ))
  have hℂ : ((2 : ℝ) * MvPolynomial.eval w f.1 : ℂ) = (quadReal f.hessian w w : ℂ) := by
    calc
      ((2 : ℝ) * MvPolynomial.eval w f.1 : ℂ) = 2 * (MvPolynomial.eval w f.1 : ℂ) := by norm_num
      _ = 2 * MvPolynomial.aeval (fun j : Fin n => (w j : ℂ)) f.1 := by rw [aeval_ofReal_eval]
      _ = (∑ i : Fin n, ∑ j : Fin n, f.hessian i j * (w i : ℂ) * (w j : ℂ)) := h
      _ = (quadReal f.hessian w w : ℂ) := by
        simp [quadReal]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hre := congrArg Complex.re hℂ
  simpa using hre

/-- line-restriction value: `quadReal H (y • e_s − v) = Qee y² − 2 Qev y + Qvv`. -/
lemma quadReal_line_expand {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (s : Fin n) (v : Fin n → ℝ) (y : ℝ) :
    quadReal H (fun k : Fin n => y * (if k = s then 1 else 0) - v k)
      (fun k : Fin n => y * (if k = s then 1 else 0) - v k) =
      y ^ 2 * quadReal H (evec s) (evec s) - 2 * y * quadReal H (evec s) v + quadReal H v v := by
  have hveq : (fun k : Fin n => y * (if k = s then 1 else 0) - v k) =
      y • evec s + (-1 : ℝ) • v := by
    funext k
    by_cases hk : k = s
    · subst k
      simp [evec]
      ring
    · simp [evec, hk]
  rw [hveq]
  rw [quadReal_expand H hH (evec s) v y (-1)]
  ring

/-- LINE CRITERION (strict stability): a positive quadratic whose restriction to every
affine line `x · e_s − v` (with `v` not parallel to `e_s`) has two distinct real roots is
strictly Lorentzian. -/
theorem strict_of_line_roots (n : ℕ) (s : Fin n) (f : H n 2) (hf : f ∈ P n 2)
    (hrestrict : ∀ v : Fin n → ℝ, (∃ j : Fin n, j ≠ s ∧ v j ≠ 0) →
      ∃ a b : ℝ, a ≠ b ∧
        MvPolynomial.eval (fun k : Fin n => a * (if k = s then 1 else 0) - v k) f.1 = 0 ∧
        MvPolynomial.eval (fun k : Fin n => b * (if k = s then 1 else 0) - v k) f.1 = 0) :
    f ∈ Ŀ n 2 := by
  classical
  let H := f.hessian
  have hsymm : H.IsSymm := by simpa [H] using hessian_symm n f
  have hposEntries : ∀ i j : Fin n, 0 < H i j := by
    simpa [H] using (mem_P_iff_hessian_pos n f).mp hf
  have hQee_pos : 0 < quadReal H (evec s) (evec s) := by
    have : quadReal H (evec s) (evec s) = H s s := by
      simp [quadReal, evec]
    rw [this]
    exact hposEntries s s
  have hker : ∀ v : Fin n → ℝ, quadReal H (evec s) v = 0 → v = 0 ∨ quadReal H v v < 0 := by
    intro v hvQ
    by_cases hv0 : v = 0
    · left
      exact hv0
    · right
      have hnotpar : ∃ j : Fin n, j ≠ s ∧ v j ≠ 0 := by
        by_contra hn
        have hzero : ∀ j : Fin n, j ≠ s → v j = 0 := by
          intro j hj
          by_contra hz
          exact hn ⟨j, hj, hz⟩
        have hv_eq : v = (v s) • evec s := by
          funext k
          by_cases hk : k = s
          · subst k
            simp [evec]
          · have := hzero k hk
            simp [evec, hk, this]
        let c : ℝ := v s
        have hQQ : quadReal H (evec s) v = c * quadReal H (evec s) (evec s) := by
          rw [hv_eq]
          exact quadReal_smul_right H c (evec s) (evec s)
        have hQ0 : c * quadReal H (evec s) (evec s) = 0 := by
          rw [← hQQ]
          exact hvQ
        have hvs0 : c = 0 := (mul_eq_zero.mp hQ0).resolve_right (ne_of_gt hQee_pos)
        have hv_eq0 : v = 0 := by
          rw [hv_eq]
          simp [hvs0, c]
        exact hv0 hv_eq0
      rcases hrestrict v hnotpar with ⟨a, b, hab, ha0, hb0⟩
      let Qee := quadReal H (evec s) (evec s)
      let Qev := quadReal H (evec s) v
      let Qvv := quadReal H v v
      have hqa : quadReal H (fun k : Fin n => a * (if k = s then 1 else 0) - v k)
          (fun k : Fin n => a * (if k = s then 1 else 0) - v k) = 0 := by
        rw [← eval_two_quadReal n f (fun k : Fin n => a * (if k = s then 1 else 0) - v k)]
        rw [ha0]
        norm_num
      have hqb : quadReal H (fun k : Fin n => b * (if k = s then 1 else 0) - v k)
          (fun k : Fin n => b * (if k = s then 1 else 0) - v k) = 0 := by
        rw [← eval_two_quadReal n f (fun k : Fin n => b * (if k = s then 1 else 0) - v k)]
        rw [hb0]
        norm_num
      have hqa0 : a ^ 2 * Qee - 2 * a * Qev + Qvv = 0 := by
        dsimp [Qee, Qev, Qvv]
        rw [← quadReal_line_expand H hsymm s v a]
        exact hqa
      have hqb0 : b ^ 2 * Qee - 2 * b * Qev + Qvv = 0 := by
        dsimp [Qee, Qev, Qvv]
        rw [← quadReal_line_expand H hsymm s v b]
        exact hqb
      have ha' : Qee * a ^ 2 - 2 * Qev * a + Qvv = 0 := by
        nlinarith [hqa0]
      have hb' : Qee * b ^ 2 - 2 * Qev * b + Qvv = 0 := by
        nlinarith [hqb0]
      have hgt := Commons.Data.Real.sq_gt_of_two_roots_quad Qee Qev Qvv hQee_pos ⟨a, b, hab, ha', hb'⟩
      have hQvv_neg : Qvv < 0 := by
        have hpos : 0 < Qee := by simpa [Qee] using hQee_pos
        have hmul : Qee * Qvv < 0 := by
          have : Qev ^ 2 > Qee * Qvv := hgt
          have hQev0 : Qev = 0 := by simpa [Qev] using hvQ
          nlinarith
        nlinarith
      exact hQvv_neg
  rcases negDef_ker_pos_implies_strict n H hsymm (evec s) hQee_pos hker with ⟨hunit, hcard⟩
  have hquad : quadricOfMatrix n H = f := by simpa [H] using (quadricOfMatrix_hessian n f)
  have hmem : quadricOfMatrix n H ∈ Ŀ n 2 := quadricOfMatrix_mem_Ŀ_of_strict n hsymm hposEntries hunit hcard
  simpa [hquad] using hmem


-- =====================================================================
-- real quadratic toolkit
-- =====================================================================

/-- two distinct real roots from a strictly positive discriminant. -/
lemma two_roots_of_discr_gt (a b c : ℝ) (ha : 0 < a) (hd : b ^ 2 > 4 * a * c) :
    ∃ x y : ℝ, x ≠ y ∧ a * x ^ 2 + b * x + c = 0 ∧ a * y ^ 2 + b * y + c = 0 := by
  let d : ℝ := Real.sqrt (b ^ 2 - 4 * a * c)
  have hdisc : 0 ≤ b ^ 2 - 4 * a * c := by linarith
  have hdsq : d ^ 2 = b ^ 2 - 4 * a * c := by
    dsimp [d]
    exact Real.sq_sqrt hdisc
  have hdpos : 0 < d := by
    dsimp [d]
    exact Real.sqrt_pos.mpr (by linarith)
  refine ⟨(-b + d) / (2 * a), (-b - d) / (2 * a), ?_, ?_, ?_⟩
  · -- distinct
    have h2a : (2 * a : ℝ) ≠ 0 := by positivity
    have hdiff : ((-b + d) / (2 * a)) - ((-b - d) / (2 * a)) = (2 * d) / (2 * a) := by
      field_simp [h2a]
      ring
    intro h
    have hz : (2 * d) / (2 * a) = 0 := by
      rw [← hdiff]
      rw [h]
      ring
    have hd0 : d = 0 := by
      field_simp [h2a] at hz
      nlinarith
    nlinarith
  · have h2a : (2 * a : ℝ) ≠ 0 := by positivity
    field_simp [h2a]
    nlinarith [hdsq]
  · have h2a : (2 * a : ℝ) ≠ 0 := by positivity
    field_simp [h2a]
    nlinarith [hdsq]

/-- a quadratic with positive leading coefficient that attains a strictly negative value
has two distinct real zeros. -/
lemma two_roots_of_neg_value (a b c : ℝ) (ha : 0 < a) {x₀ : ℝ}
    (hx : a * x₀ ^ 2 + b * x₀ + c < 0) :
    ∃ x y : ℝ, x ≠ y ∧ a * x ^ 2 + b * x + c = 0 ∧ a * y ^ 2 + b * y + c = 0 := by
  have hdisc : b ^ 2 > 4 * a * c := by
    have hmain : 0 ≤ (2 * a * x₀ + b) ^ 2 := sq_nonneg (2 * a * x₀ + b)
    have hrel : (2 * a * x₀ + b) ^ 2 = 4 * a * (a * x₀ ^ 2 + b * x₀ + c) + (b ^ 2 - 4 * a * c) := by ring
    nlinarith
  exact two_roots_of_discr_gt a b c ha hdisc

/-- the (double) root when the discriminant vanishes. -/
lemma root_of_discr_zero (a b c : ℝ) (ha : 0 < a) (hd : b ^ 2 = 4 * a * c) :
    a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c = 0 := by
  have h2a : (2 * a : ℝ) ≠ 0 := by positivity
  field_simp [h2a]
  nlinarith


-- =====================================================================
-- restrictions of stable positive quadratics are real-rooted
-- =====================================================================

/-- a stable, nonnegative quadratic (nonzero) has a Hessian with at most one positive
eigenvalue. -/
lemma stable_quad_hessian_card_le_one {n : ℕ} (q : H n 2) (hq : q ∈ S n 2) (hq0 : q.1 ≠ 0) :
    (q.hessian.charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1 := by
  classical
  let A := q.hessian
  have hsymm : A.IsSymm := by simpa [A] using hessian_symm n q
  have hnn : ∀ i j : Fin n, 0 ≤ A i j := by
    intro i j
    have hc : ∀ m : Fin n →₀ ℕ, 0 ≤ q.1.coeff m := hq.2
    -- hessian entries are (up to 2) coefficients of q
    by_cases hij : i = j
    · subst j
      have : A i i = 2 * q.1.coeff (Finsupp.single i 2) := by simp [A, H.hessian]
      rw [this]
      exact mul_nonneg (by norm_num) (hc (Finsupp.single i 2))
    · have : A i j = q.1.coeff (Finsupp.single i 1 + Finsupp.single j 1) := by
        simp [A, H.hessian, hij]
      rw [this]
      exact hc (Finsupp.single i 1 + Finsupp.single j 1)
  -- stability of q means: q = 0 or for all z in the upper half plane, aeval z q ≠ 0
  have hstab : q.1 = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
      MvPolynomial.aeval (((↑) : UpperHalfPlane → ℂ) ∘ z) q.1 ≠ 0 := hq.1
  rcases hstab with hzero | hpos
  · exfalso
    exact hq0 hzero
  · have hsum : ∀ z : Fin n → UpperHalfPlane,
        (∑ i : Fin n, ∑ j : Fin n, A i j * (z i : ℂ) * (z j : ℂ)) ≠ 0 := by
      intro z
      have hz := hpos z
      have hae := hessian_aeval_eq n q (fun j : Fin n => (z j : ℂ))
      -- 2 * aeval z q ≠ 0
      intro hz0
      have hae0 : MvPolynomial.aeval (fun j : Fin n => (z j : ℂ)) q.1 = 0 := by
        have : 2 * MvPolynomial.aeval (fun j : Fin n => (z j : ℂ)) q.1 = 0 := by
          rw [hae]
          exact hz0
        exact (mul_eq_zero.mp this).resolve_left (by norm_num)
      exact hz hae0
    exact (quadratic_stable_iff_roots_card_le_one A hsymm hnn).mp (Or.inr hsum)

/-- pointwise identity: the value of a quadratic on the line `x·e_s − v` is
`½(Qss x² − 2·Qsv·x + Qvv)` (hessian-normalized). -/
lemma quad_line_value_eq {n : ℕ} (q : H n 2) (s : Fin n) (v : Fin n → ℝ) (x : ℝ) :
    MvPolynomial.eval (fun k : Fin n => x * (if k = s then 1 else 0) - v k) q.1 =
      (1 / 2 : ℝ) * (quadReal q.hessian (evec s) (evec s) * x ^ 2 -
        2 * quadReal q.hessian (evec s) v * x + quadReal q.hessian v v) := by
  have h := eval_two_quadReal n q (fun k : Fin n => x * (if k = s then 1 else 0) - v k)
  -- 2 * eval = quadReal H (line point) (line point)
  have hsymm : (q.hessian).IsSymm := hessian_symm n q
  have hline := quadReal_line_expand q.hessian hsymm s v x
  have h2 : 2 * MvPolynomial.eval (fun k : Fin n => x * (if k = s then 1 else 0) - v k) q.1 =
      quadReal q.hessian (fun k : Fin n => x * (if k = s then 1 else 0) - v k)
        (fun k : Fin n => x * (if k = s then 1 else 0) - v k) := h
  rw [hline] at h2
  nlinarith

/-- DISCRIMINANT INEQUALITY on every line: for a positive quadratic whose Hessian has at
most one positive eigenvalue, the restriction to `x·e_s − v` is real-rooted. -/
lemma quad_line_discr_nonneg {n : ℕ} (q : H n 2) (s : Fin n) (hP : q ∈ P n 2)
    (hcard : (q.hessian.charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1) :
    ∀ v : Fin n → ℝ,
      (quadReal q.hessian (evec s) v) ^ 2 ≥
        quadReal q.hessian (evec s) (evec s) * quadReal q.hessian v v := by
  classical
  intro v
  have hsymm : (q.hessian).IsSymm := hessian_symm n q
  have hQss : 0 < quadReal q.hessian (evec s) (evec s) := by
    have hpos : ∀ i j : Fin n, 0 < q.hessian i j := (mem_P_iff_hessian_pos n q).mp hP
    have : quadReal q.hessian (evec s) (evec s) = q.hessian s s := by
      simp [quadReal, evec]
    rw [this]
    exact hpos s s
  exact quadReal_sq_ge_self_mul q.hessian hsymm hcard (evec s) v hQss

/-- real-rooted dichotomy: a positive quadratic with Hessian of index ≤ 1 restricted to
any line has either two distinct real zeros or (at least) a real zero. -/
lemma quad_line_root_or_two {n : ℕ} (q : H n 2) (s : Fin n) (hP : q ∈ P n 2)
    (hcard : (q.hessian.charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1) :
    ∀ v : Fin n → ℝ,
      (∃ a b : ℝ, a ≠ b ∧
        MvPolynomial.eval (fun k : Fin n => a * (if k = s then 1 else 0) - v k) q.1 = 0 ∧
        MvPolynomial.eval (fun k : Fin n => b * (if k = s then 1 else 0) - v k) q.1 = 0) ∨
      ∃ c : ℝ, MvPolynomial.eval (fun k : Fin n => c * (if k = s then 1 else 0) - v k) q.1 = 0 := by
  classical
  intro v
  have hsymm : (q.hessian).IsSymm := hessian_symm n q
  have hQss : 0 < quadReal q.hessian (evec s) (evec s) := by
    have hpos : ∀ i j : Fin n, 0 < q.hessian i j := (mem_P_iff_hessian_pos n q).mp hP
    have : quadReal q.hessian (evec s) (evec s) = q.hessian s s := by simp [quadReal, evec]
    rw [this]
    exact hpos s s
  have hQss0 : quadReal q.hessian (evec s) (evec s) ≠ 0 := ne_of_gt hQss
  have hdisc := quad_line_discr_nonneg q s hP hcard v
  by_cases hgt : (quadReal q.hessian (evec s) v) ^ 2 > quadReal q.hessian (evec s) (evec s) *
      quadReal q.hessian v v
  · left
    rcases two_roots_of_discr_gt (quadReal q.hessian (evec s) (evec s))
        (-2 * quadReal q.hessian (evec s) v) (quadReal q.hessian v v) hQss (by nlinarith)
      with ⟨a, b, hab, ha, hb⟩
    refine ⟨a, b, hab, ?_, ?_⟩
    · have hline := quad_line_value_eq q s v a
      rw [hline]
      nlinarith
    · have hline := quad_line_value_eq q s v b
      rw [hline]
      nlinarith
  · right
    have hle : (quadReal q.hessian (evec s) v) ^ 2 ≤ quadReal q.hessian (evec s) (evec s) *
        quadReal q.hessian v v := le_of_not_gt hgt
    have heq : (quadReal q.hessian (evec s) v) ^ 2 = quadReal q.hessian (evec s) (evec s) *
        quadReal q.hessian v v := le_antisymm hle hdisc
    refine ⟨quadReal q.hessian (evec s) v / quadReal q.hessian (evec s) (evec s), ?_⟩
    have hline := quad_line_value_eq q s v (quadReal q.hessian (evec s) v /
      quadReal q.hessian (evec s) (evec s))
    rw [hline]
    field_simp [hQss0]
    nlinarith


/-- a positive, stable quadratic is nonzero (when `0 < n`). -/
lemma stable_pos_quad_ne_zero {n : ℕ} (hn : 0 < n) (q : H n 2) (hP : q ∈ P n 2) :
    q.1 ≠ 0 := by
  classical
  let i : Fin n := ⟨0, hn⟩
  have hw : Finsupp.weight (1 : Fin n → ℕ) (Finsupp.single i 2) = 2 := by
    rw [Finsupp.weight_single]
    simp
  have hc : 0 < q.1.coeff (Finsupp.single i 2) := hP (Finsupp.single i 2) hw
  intro h0
  have : q.1.coeff (Finsupp.single i 2) = 0 := by
    rw [h0]
    simp
  linarith

/-- the real-rooted dichotomy for positive stable quadratics: restriction to any line
`x·e_s − v` has two distinct real zeros or a real zero. -/
lemma stable_pos_quad_line_root_or_two {n : ℕ} (hn : 0 < n) (s : Fin n) (q : H n 2)
    (hq : q ∈ S n 2 ∩ P n 2) :
    ∀ v : Fin n → ℝ,
      (∃ a b : ℝ, a ≠ b ∧
        MvPolynomial.eval (fun k : Fin n => a * (if k = s then 1 else 0) - v k) q.1 = 0 ∧
        MvPolynomial.eval (fun k : Fin n => b * (if k = s then 1 else 0) - v k) q.1 = 0) ∨
      ∃ c : ℝ, MvPolynomial.eval (fun k : Fin n => c * (if k = s then 1 else 0) - v k) q.1 = 0 := by
  have hS : q ∈ S n 2 := hq.1
  have hP : q ∈ P n 2 := hq.2
  have hq0 : q.1 ≠ 0 := stable_pos_quad_ne_zero hn q hP
  have hcard := stable_quad_hessian_card_le_one q hS hq0
  exact quad_line_root_or_two q s hP hcard


-- =====================================================================
-- deform_preserves_L : base degrees 0, 1, 2
-- =====================================================================

/-- `(1 + θ·X_i·∂_j)` preserves `L n 2` for `θ ≥ 0`. -/
lemma deformH_mem_L_degree_two {n : ℕ} (i j : Fin n) (θ : ℝ) (hθ : 0 ≤ θ)
    (f : H n 2) (hf : f ∈ L n 2) :
    nuij_deformH (k := 1) i j θ f ∈ L n 2 := by
  have hfS : f ∈ S n 2 := by simpa [L] using hf
  change nuij_deformH (k := 1) i j θ f ∈ S n 2
  change IsStable (nuij_deformH (k := 1) i j θ f).1 ∧
    ∀ m : Fin n →₀ ℕ, 0 ≤ (nuij_deformH (k := 1) i j θ f).1.coeff m
  constructor
  · change IsStable (f.1 + (C θ) * X i * pderiv j f.1)
    exact quad_deform_stable i j θ f.1 f.2 hfS.1 hfS.2 hθ
  · have hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ (f.1 + (C θ) * X i * pderiv j f.1).coeff m :=
      nuij_deformPoly_coeff_nonneg i j θ hθ f.1 hfS.2
    exact hnn

/-- `(1 + θ·X_i·∂_j)` preserves `L n 1` for `θ ≥ 0`. -/
lemma deformH_mem_L_degree_one {n : ℕ} (i j : Fin n) (θ : ℝ) (hθ : 0 ≤ θ)
    (f : H n 1) (hf : f ∈ L n 1) :
    nuij_deformH (k := 0) i j θ f ∈ L n 1 := by
  have hfS : f ∈ S n 1 := by simpa [L] using hf
  change nuij_deformH (k := 0) i j θ f ∈ S n 1
  change IsStable (nuij_deformH (k := 0) i j θ f).1 ∧
    ∀ m : Fin n →₀ ℕ, 0 ≤ (nuij_deformH (k := 0) i j θ f).1.coeff m
  constructor
  · -- deformed polynomial is linear homogeneous with nonnegative coefficients; use
    -- isStable_of_degree_le_one
    change f.1 + (C θ) * X i * pderiv j f.1 = 0 ∨
      ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (((↑) : UpperHalfPlane → ℂ) ∘ z) (f.1 + (C θ) * X i * pderiv j f.1) ≠ 0
    have hlin : (f.1 + (C θ) * X i * pderiv j f.1).IsHomogeneous 1 :=
      nuij_deformH_homogeneous (k := 0) i j θ f
    have hnn : ∀ m : Fin n →₀ ℕ,
        0 ≤ (f.1 + (C θ) * X i * pderiv j f.1).coeff m :=
      nuij_deformPoly_coeff_nonneg i j θ hθ f.1 hfS.2
    let F : homogeneousSubmodule (Fin n) ℝ 1 :=
      ⟨f.1 + (C θ) * X i * pderiv j f.1, hlin⟩
    exact (Commons.Analysis.MvPolynomial.isStable_of_degree_le_one n 1 (by norm_num) F hnn)
  · exact nuij_deformPoly_coeff_nonneg i j θ hθ f.1 hfS.2


/-- partial derivative of a degree-0 homogeneous polynomial is zero. -/
lemma pderiv_of_homogeneous_zero {n : ℕ} (i : Fin n) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous 0) : pderiv i p = 0 := by
  classical
  ext m
  rw [MvPolynomial.coeff_pderiv]
  have hw : Finsupp.weight (1 : Fin n → ℕ) (m + ne n i) ≠ 0 := by
    rw [map_add, Finsupp.weight_single]
    simp [ne]
  have hh : p.IsWeightedHomogeneous (1 : Fin n → ℕ) 0 := by
    simpa [MvPolynomial.IsHomogeneous] using hp
  have hz := MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero hh (m + ne n i) hw
  rw [hz]
  simp

/-- `(1 + θ·X_i·∂_j)` preserves `L n 0` for `θ ≥ 0` (it is the identity in degree 0). -/
lemma deform_mem_L_degree_zero {n : ℕ} (i j : Fin n) (θ : ℝ) (hθ : 0 ≤ θ)
    (f : H n 0) (hf : f ∈ L n 0) :
    (⟨f.1 + (C θ) * X i * pderiv j f.1, by
        have hz : pderiv j f.1 = 0 := pderiv_of_homogeneous_zero j f.1 f.2
        simpa [hz] using f.2⟩ : H n 0) ∈ L n 0 := by
  have hfS : f ∈ S n 0 := by simpa [L] using hf
  change IsStable (f.1 + (C θ) * X i * pderiv j f.1) ∧
    ∀ m : Fin n →₀ ℕ, 0 ≤ (f.1 + (C θ) * X i * pderiv j f.1).coeff m
  have hz : pderiv j f.1 = 0 := pderiv_of_homogeneous_zero j f.1 f.2
  constructor
  · simpa [hz] using hfS.1
  · simpa [hz] using hfS.2

/-- canonical deformation element at any degree. -/
def deformElem {n d : ℕ} (i j : Fin n) (θ : ℝ) (f : H n d) : H n d :=
  ⟨f.1 + (C θ) * X i * pderiv j f.1, by
    by_cases h0 : d = 0
    · subst d
      have hz : pderiv j f.1 = 0 := pderiv_of_homogeneous_zero j f.1 f.2
      simpa [hz] using f.2
    · have hf' : f.1.IsHomogeneous d := f.2
      have hpd : (pderiv j f.1).IsHomogeneous (d - 1) := hf'.pderiv
      have hX : (X i : MvPolynomial (Fin n) ℝ).IsHomogeneous 1 := MvPolynomial.isHomogeneous_X ℝ i
      have hC : ((C θ) : MvPolynomial (Fin n) ℝ).IsHomogeneous 0 := MvPolynomial.isHomogeneous_C (Fin n) θ
      have hCX : ((C θ) * X i : MvPolynomial (Fin n) ℝ).IsHomogeneous 1 := by
        have hdeg : 0 + 1 = 1 := by omega
        simpa [hdeg] using hC.mul hX
      have hprod : ((C θ) * X i * pderiv j f.1).IsHomogeneous d := by
        have hdeg : 1 + (d - 1) = d := by omega
        simpa [hdeg] using hCX.mul hpd
      exact hf'.add hprod⟩

lemma deformElem_val {n d : ℕ} (i j : Fin n) (θ : ℝ) (f : H n d) :
    (deformElem (n := n) (d := d) i j θ f).1 = f.1 + (C θ) * X i * pderiv j f.1 := rfl

/-- in positive degree the canonical element is `nuij_deformH`. -/
lemma deformElem_eq_deformH {n k : ℕ} (i j : Fin n) (θ : ℝ) (f : H n (k + 1)) :
    deformElem (n := n) (d := k + 1) i j θ f = nuij_deformH k i j θ f := by
  apply Subtype.ext
  change f.1 + (C θ) * X i * pderiv j f.1 = f.1 + (C θ) * X i * pderiv j f.1
  rfl

/-- `(1 + θ·X_i·∂_j)` preserves `L n d` for `d ≤ 2` and `θ ≥ 0`. -/
lemma deform_mem_L_of_degree_le_two {n d : ℕ} (i j : Fin n) (θ : ℝ) (hθ : 0 ≤ θ)
    (f : H n d) (hf : f ∈ L n d) (hd : d ≤ 2) :
    deformElem (n := n) (d := d) i j θ f ∈ L n d := by
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hcases with hd0 | hd1 | hd2
  · subst d
    -- deformElem in degree 0 equals f
    have heq : deformElem (n := n) (d := 0) i j θ f = f := by
      apply Subtype.ext
      change f.1 + (C θ) * X i * pderiv j f.1 = f.1
      have hz : pderiv j f.1 = 0 := pderiv_of_homogeneous_zero j f.1 f.2
      rw [hz]
      ring
    rw [heq]
    exact hf
  · subst d
    rw [deformElem_eq_deformH]
    exact deformH_mem_L_degree_one i j θ hθ f hf
  · subst d
    rw [deformElem_eq_deformH]
    exact deformH_mem_L_degree_two i j θ hθ f hf

-- =====================================================================
-- stability under variable renaming; the ≺ (precedes) relation
-- =====================================================================

/-- stability is preserved by renaming variables (forward direction). -/
lemma IsStable_rename {n m : ℕ} (e : Fin n → Fin m) (p : MvPolynomial (Fin n) ℝ)
    (h : IsStable p) : IsStable (MvPolynomial.rename e p) := by
  rcases h with hz | hf
  · left
    rw [hz]
    simp
  · right
    intro z
    have hsub := MvPolynomial.aeval_rename e (fun j : Fin m => ((z j : UpperHalfPlane) : ℂ)) p
    have hf' := hf (fun i : Fin n => z (e i))
    change (MvPolynomial.aeval (fun j : Fin m => ((z j : UpperHalfPlane) : ℂ))
      (MvPolynomial.rename e p)) ≠ 0
    rw [MvPolynomial.aeval_rename]
    simpa [Function.comp_def] using hf (fun i : Fin n => z (e i))

/-- stability is preserved by dropping an unused last variable (backward direction of
`Fin.castSucc` renaming). -/
lemma IsStable_rename_castSucc {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (h : IsStable (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) p)) :
    IsStable p := by
  classical
  let H0 : UpperHalfPlane := UpperHalfPlane.mk Complex.I (by simp)
  have hcs_inj : Function.Injective (Fin.castSucc : Fin n → Fin (n + 1)) := by
    intro a b hab
    apply Fin.ext
    simpa using congrArg Fin.val hab
  rcases h with hz | hf
  · left
    exact MvPolynomial.rename_injective (Fin.castSucc : Fin n → Fin (n + 1)) hcs_inj hz
  · right
    intro z
    let g : Fin (n + 1) → UpperHalfPlane := fun j =>
      if hj : j.1 < n then z ⟨j.1, hj⟩ else H0
    have hge : ∀ i : Fin n, g (Fin.castSucc i) = z i := by
      intro i
      dsimp [g]
      simp [i.isLt]
    have hfun : ((fun j : Fin (n + 1) => ((g j : UpperHalfPlane) : ℂ)) ∘
          (Fin.castSucc : Fin n → Fin (n + 1))) =
        (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) := by
      funext i
      simp [hge i]
    have heq : MvPolynomial.aeval (fun i : Fin n => (z i : ℂ)) p =
        MvPolynomial.aeval (fun j : Fin (n + 1) => ((g j : UpperHalfPlane) : ℂ))
          (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) p) := by
      rw [MvPolynomial.aeval_rename]
      rw [hfun]
    change (MvPolynomial.aeval (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) p) ≠ 0
    rw [heq]
    exact hf g

/-- stability is unaffected by embedding into one more variable (with `castSucc`). -/
lemma IsStable_rename_castSucc_iff {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    IsStable (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) p) ↔ IsStable p := by
  constructor
  · exact IsStable_rename_castSucc p
  · intro hp
    exact IsStable_rename (Fin.castSucc : Fin n → Fin (n + 1)) p hp

/-- the relation `f ≺ g` for stable polynomials: `g + w_{n+1}·f` is stable. -/
def Precedes {n : ℕ} (f g : MvPolynomial (Fin n) ℝ) : Prop :=
  IsStable (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) g +
    MvPolynomial.X (Fin.last n) *
      MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f)

/-- `0 ≺ g` iff `g` is stable. -/
lemma precedes_zero_left {n : ℕ} (g : MvPolynomial (Fin n) ℝ) :
    Precedes 0 g ↔ IsStable g := by
  unfold Precedes
  simp
  exact IsStable_rename_castSucc_iff g


-- =====================================================================
-- derivative of a stable quadratic is a stable linear form
-- (the quadratic case of Lemma closure (1), used throughout the
-- deformation analysis; the linear form has nonnegative coefficients)
-- =====================================================================

/-- derivative (along `i`) of a stable quadratic with nonnegative coefficients is stable
(as a linear form), i.e. lies in `S n 1`. -/
lemma pderiv_quad_mem_S {n : ℕ} (i : Fin n) (q : H n 2) (hq : q ∈ S n 2) :
    (⟨pderiv i q.1, by simpa using q.2.pderiv⟩ : H n 1) ∈ S n 1 := by
  have hnnq : ∀ m : Fin n →₀ ℕ, 0 ≤ q.1.coeff m := hq.2
  change IsStable (pderiv i q.1) ∧ ∀ m : Fin n →₀ ℕ, 0 ≤ (pderiv i q.1).coeff m
  constructor
  · change pderiv i q.1 = 0 ∨
      ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (((↑) : UpperHalfPlane → ℂ) ∘ z) (pderiv i q.1) ≠ 0
    have hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ (pderiv i q.1).coeff m := coeff_pderiv_nonneg' i q.1 hnnq
    let L : homogeneousSubmodule (Fin n) ℝ 1 :=
      ⟨pderiv i q.1, by simpa using q.2.pderiv⟩
    exact Commons.Analysis.MvPolynomial.isStable_of_degree_le_one n 1 (by norm_num) L hnn
  · exact coeff_pderiv_nonneg' i q.1 hnnq


-- =====================================================================
-- first restriction-level closure instance: vertex sign (interlacing)
-- =====================================================================

/-- vertex-sign estimate: a positive quadratic whose Hessian has index ≤ 1 is `≤ 0` at
every point of the line `x·e_s − v` where the linear form `(H·)_i` (the derivative along
`e_i`) vanishes. -/
lemma quad_line_vertex_sign {n : ℕ} (i s : Fin n) (C : H n 2) (hP : C ∈ P n 2)
    (hcard : (C.hessian.charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1) :
    ∀ v : Fin n → ℝ, ∀ ξ : ℝ,
      quadReal C.hessian (evec i) (fun k : Fin n => ξ * (if k = s then 1 else 0) - v k) = 0 →
        MvPolynomial.eval (fun k : Fin n => ξ * (if k = s then 1 else 0) - v k) C.1 ≤ 0 := by
  classical
  intro v ξ hx
  let H := C.hessian
  let y : Fin n → ℝ := fun k => ξ * (if k = s then 1 else 0) - v k
  have hsymm : H.IsSymm := by simpa [H] using hessian_symm n C
  have hQii : 0 < quadReal H (evec i) (evec i) := by
    have hpos : ∀ a b : Fin n, 0 < H a b := by simpa [H] using (mem_P_iff_hessian_pos n C).mp hP
    have : quadReal H (evec i) (evec i) = H i i := by simp [quadReal, evec]
    rw [this]
    exact hpos i i
  have hineq := quadReal_sq_ge_self_mul H hsymm hcard (evec i) y hQii
  have hx' : quadReal H (evec i) y = 0 := by simpa [H, y] using hx
  have hQyy : quadReal H y y ≤ 0 := by
    have hmul : quadReal H (evec i) (evec i) * quadReal H y y ≤ 0 := by
      nlinarith
    nlinarith
  have hval := quad_line_value_eq C s v ξ
  have hline := quadReal_line_expand H hsymm s v ξ
  have hle : MvPolynomial.eval (fun k : Fin n => ξ * (if k = s then 1 else 0) - v k) C.1 ≤ 0 := by
    rw [hval]
    nlinarith [hQyy, hline]
  simpa [y] using hle


/-- the vertex-sign estimate for stable positive quadratics: if the linear form `∂ᵢ C`
vanishes at a point of the line, `C` is nonpositive there. -/
lemma stable_pos_quad_line_vertex_sign {n : ℕ} (hn : 0 < n) (i s : Fin n) (C : H n 2)
    (hC : C ∈ S n 2 ∩ P n 2) :
    ∀ v : Fin n → ℝ, ∀ ξ : ℝ,
      quadReal C.hessian (evec i) (fun k : Fin n => ξ * (if k = s then 1 else 0) - v k) = 0 →
        MvPolynomial.eval (fun k : Fin n => ξ * (if k = s then 1 else 0) - v k) C.1 ≤ 0 := by
  have hS : C ∈ S n 2 := hC.1
  have hP : C ∈ P n 2 := hC.2
  have hC0 : C.1 ≠ 0 := stable_pos_quad_ne_zero hn C hP
  have hcard := stable_quad_hessian_card_le_one C hS hC0
  exact quad_line_vertex_sign i s C hP hcard


-- =====================================================================
-- claim (I) ingredients: vertex negativity + deformed two distinct roots
-- =====================================================================

/-- value of the `e_s`-directional derivative along a line: `Q(e_s, x·e_s − v) =
x·Q(e_s,e_s) − Q(e_s,v)`. -/
lemma quadReal_evec_line {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (s : Fin n) (v : Fin n → ℝ) (x : ℝ) :
    quadReal A (evec s) (fun k : Fin n => x * (if k = s then 1 else 0) - v k) =
      x * quadReal A (evec s) (evec s) - quadReal A (evec s) v := by
  have hveq : (fun k : Fin n => x * (if k = s then 1 else 0) - v k) =
      x • evec s + (-1 : ℝ) • v := by
    funext k
    by_cases hk : k = s
    · subst k
      simp [evec]
      ring
    · simp [evec, hk]
  rw [hveq]
  rw [quadReal_add_right A (evec s) (x • evec s) ((-1) • v)]
  rw [quadReal_smul_right A x (evec s) (evec s)]
  rw [quadReal_smul_right A (-1) (evec s) v]
  ring

/-- a positive quadratic whose restriction to the line `x·e_s − v` has two distinct real
zeros is strictly negative at the point where the directional derivative along `e_s`
vanishes (its vertex). -/
lemma quad_line_vertex_neg {n : ℕ} (s : Fin n) (A : H n 2) (hA : A ∈ P n 2)
    (v : Fin n → ℝ)
    (htwo : ∃ a b : ℝ, a ≠ b ∧
      MvPolynomial.eval (fun k : Fin n => a * (if k = s then 1 else 0) - v k) A.1 = 0 ∧
      MvPolynomial.eval (fun k : Fin n => b * (if k = s then 1 else 0) - v k) A.1 = 0) :
    ∀ ξ : ℝ,
      quadReal A.hessian (evec s) (fun k : Fin n => ξ * (if k = s then 1 else 0) - v k) = 0 →
        MvPolynomial.eval (fun k : Fin n => ξ * (if k = s then 1 else 0) - v k) A.1 < 0 := by
  classical
  intro ξ hx
  let H := A.hessian
  have hsymm : H.IsSymm := by simpa [H] using hessian_symm n A
  have hQss : 0 < quadReal H (evec s) (evec s) := by
    have hpos : ∀ a b : Fin n, 0 < H a b := by simpa [H] using (mem_P_iff_hessian_pos n A).mp hA
    have : quadReal H (evec s) (evec s) = H s s := by simp [quadReal, evec]
    rw [this]
    exact hpos s s
  rcases htwo with ⟨a, b, hab, ha, hb⟩
  have ha' : quadReal H (evec s) (evec s) * a ^ 2 - 2 * quadReal H (evec s) v * a +
      quadReal H v v = 0 := by
    have hq := quad_line_value_eq A s v a
    have hz : (1 / 2 : ℝ) *
        (quadReal H (evec s) (evec s) * a ^ 2 - 2 * quadReal H (evec s) v * a + quadReal H v v) = 0 := by
      rw [← hq]
      exact ha
    nlinarith
  have hb' : quadReal H (evec s) (evec s) * b ^ 2 - 2 * quadReal H (evec s) v * b +
      quadReal H v v = 0 := by
    have hq := quad_line_value_eq A s v b
    have hz : (1 / 2 : ℝ) *
        (quadReal H (evec s) (evec s) * b ^ 2 - 2 * quadReal H (evec s) v * b + quadReal H v v) = 0 := by
      rw [← hq]
      exact hb
    nlinarith
  have hgt := Commons.Data.Real.sq_gt_of_two_roots_quad
    (quadReal H (evec s) (evec s)) (quadReal H (evec s) v) (quadReal H v v) hQss
    ⟨a, b, hab, ha', hb'⟩
  have hroot : ξ * quadReal H (evec s) (evec s) - quadReal H (evec s) v = 0 := by
    rw [quadReal_evec_line H hsymm s v ξ] at hx
    exact hx
  have hval := quad_line_value_eq A s v ξ
  have hneg : MvPolynomial.eval (fun k : Fin n => ξ * (if k = s then 1 else 0) - v k) A.1 < 0 := by
    rw [hval]
    -- inside: Qss ξ² − 2Qsv ξ + Qvv ; use hroot (Qsv = ξ Qss) and hgt
    have hrel : (quadReal H (evec s) (evec s) * ξ ^ 2 - 2 * quadReal H (evec s) v * ξ +
        quadReal H v v) < 0 := by
      have hQsv : quadReal H (evec s) v = ξ * quadReal H (evec s) (evec s) := by
        linarith
      have hgt' : (ξ * quadReal H (evec s) (evec s)) ^ 2 > quadReal H (evec s) (evec s) *
          quadReal H v v := by
        rw [← hQsv]
        exact hgt
      have hmain : quadReal H v v < quadReal H (evec s) (evec s) * ξ ^ 2 := by
        nlinarith
      nlinarith
    nlinarith
  exact hneg


-- =====================================================================
-- CLAIM (I) AT LINE LEVEL: deformed restriction has two distinct zeros
-- =====================================================================
/-- a positive quadratic whose restriction has two distinct real zeros stays with two
distinct real zeros after the deformation `A + μ·(∂ₛA)| + λ·C`, provided the interlacing
datum (`C`'s `e_i`-derivative equals `A`'s `e_s`-derivative along the line) holds. -/
lemma deform_line_two_roots {n : ℕ} (i s : Fin n) (A C : H n 2)
    (hA : A ∈ P n 2) (hC : C ∈ P n 2)
    (hcardC : (C.hessian.charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1)
    (v : Fin n → ℝ)
    (hB : ∀ x : ℝ,
      quadReal A.hessian (evec s) (fun k : Fin n => x * (if k = s then 1 else 0) - v k) =
        quadReal C.hessian (evec i) (fun k : Fin n => x * (if k = s then 1 else 0) - v k))
    (htwo : ∃ a b : ℝ, a ≠ b ∧
      MvPolynomial.eval (fun k : Fin n => a * (if k = s then 1 else 0) - v k) A.1 = 0 ∧
      MvPolynomial.eval (fun k : Fin n => b * (if k = s then 1 else 0) - v k) A.1 = 0) :
    ∀ (θ : ℝ) (hθ : 0 < θ) (αi : ℕ),
      ∃ r₁ r₂ : ℝ, r₁ ≠ r₂ ∧
        MvPolynomial.eval (fun k : Fin n => r₁ * (if k = s then 1 else 0) - v k) A.1 +
          (-(θ * (v i : ℝ))) * quadReal A.hessian (evec s)
            (fun k : Fin n => r₁ * (if k = s then 1 else 0) - v k) +
          (θ * (αi : ℝ)) * MvPolynomial.eval (fun k : Fin n => r₁ * (if k = s then 1 else 0) - v k) C.1 = 0 ∧
        MvPolynomial.eval (fun k : Fin n => r₂ * (if k = s then 1 else 0) - v k) A.1 +
          (-(θ * (v i : ℝ))) * quadReal A.hessian (evec s)
            (fun k : Fin n => r₂ * (if k = s then 1 else 0) - v k) +
          (θ * (αi : ℝ)) * MvPolynomial.eval (fun k : Fin n => r₂ * (if k = s then 1 else 0) - v k) C.1 = 0 := by
  classical
  intro θ hθ αi
  let H := A.hessian
  let K := C.hessian
  have hsymmA : H.IsSymm := by simpa [H] using hessian_symm n A
  have hsymmC : K.IsSymm := by simpa [K] using hessian_symm n C
  let QssA : ℝ := quadReal H (evec s) (evec s)
  let QsvA : ℝ := quadReal H (evec s) v
  let QvvA : ℝ := quadReal H v v
  let QssC : ℝ := quadReal K (evec s) (evec s)
  let QsvC : ℝ := quadReal K (evec s) v
  let QvvC : ℝ := quadReal K v v
  have hQssA : 0 < QssA := by
    have hpos : ∀ a b : Fin n, 0 < H a b := by simpa [H] using (mem_P_iff_hessian_pos n A).mp hA
    have : quadReal H (evec s) (evec s) = H s s := by simp [quadReal, evec]
    dsimp [QssA]
    rw [this]
    exact hpos s s
  have hQssA0 : QssA ≠ 0 := ne_of_gt hQssA
  have hQssC : 0 < QssC := by
    have hpos : ∀ a b : Fin n, 0 < K a b := by simpa [K] using (mem_P_iff_hessian_pos n C).mp hC
    have : quadReal K (evec s) (evec s) = K s s := by simp [quadReal, evec]
    dsimp [QssC]
    rw [this]
    exact hpos s s
  let ξ : ℝ := QsvA / QssA
  have hrootA : quadReal H (evec s) (fun k : Fin n => ξ * (if k = s then 1 else 0) - v k) = 0 := by
    rw [quadReal_evec_line H hsymmA s v ξ]
    have hQssA0' : quadReal H (evec s) (evec s) ≠ 0 := by simpa [QssA] using hQssA0
    dsimp [ξ, QsvA, QssA]
    field_simp [hQssA0']
    ring
  have hnegA : MvPolynomial.eval (fun k : Fin n => ξ * (if k = s then 1 else 0) - v k) A.1 < 0 := by
    exact quad_line_vertex_neg s A hA v htwo ξ hrootA
  have hBξ : quadReal K (evec i) (fun k : Fin n => ξ * (if k = s then 1 else 0) - v k) = 0 := by
    rw [← hB ξ]
    exact hrootA
  have hleC : MvPolynomial.eval (fun k : Fin n => ξ * (if k = s then 1 else 0) - v k) C.1 ≤ 0 := by
    exact quad_line_vertex_sign i s C hC hcardC v ξ hBξ
  have hα0 : 0 ≤ (αi : ℝ) := by exact_mod_cast (Nat.zero_le αi)
  have hθα : 0 ≤ θ * (αi : ℝ) := by positivity
  have hpξ : MvPolynomial.eval (fun k : Fin n => ξ * (if k = s then 1 else 0) - v k) A.1 +
      (-(θ * (v i : ℝ))) * quadReal H (evec s)
        (fun k : Fin n => ξ * (if k = s then 1 else 0) - v k) +
      (θ * (αi : ℝ)) * MvPolynomial.eval (fun k : Fin n => ξ * (if k = s then 1 else 0) - v k) C.1 < 0 := by
    have hmid0 : (-(θ * (v i : ℝ))) * quadReal H (evec s)
        (fun k : Fin n => ξ * (if k = s then 1 else 0) - v k) = 0 := by
      rw [hrootA]
      ring
    have hCterm : (θ * (αi : ℝ)) * MvPolynomial.eval (fun k : Fin n =>
        ξ * (if k = s then 1 else 0) - v k) C.1 ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos hθα hleC
    nlinarith
  let a : ℝ := (1 / 2 : ℝ) * QssA + (θ * (αi : ℝ)) * ((1 / 2 : ℝ) * QssC)
  let b : ℝ := -QsvA + (-(θ * (v i : ℝ))) * QssA - (θ * (αi : ℝ)) * QsvC
  let c : ℝ := (1 / 2 : ℝ) * QvvA + (-(θ * (v i : ℝ))) * (-QsvA) + (θ * (αi : ℝ)) * ((1 / 2 : ℝ) * QvvC)
  have ha : 0 < a := by
    dsimp [a]
    have hα : 0 ≤ (αi : ℝ) := by exact_mod_cast (Nat.zero_le αi)
    positivity
  have hpoly : ∀ x : ℝ,
      MvPolynomial.eval (fun k : Fin n => x * (if k = s then 1 else 0) - v k) A.1 +
        (-(θ * (v i : ℝ))) * quadReal H (evec s)
          (fun k : Fin n => x * (if k = s then 1 else 0) - v k) +
        (θ * (αi : ℝ)) * MvPolynomial.eval (fun k : Fin n => x * (if k = s then 1 else 0) - v k) C.1 =
      a * x ^ 2 + b * x + c := by
    intro x
    have hvalA := quad_line_value_eq A s v x
    have hvalC := quad_line_value_eq C s v x
    have hBx := quadReal_evec_line H hsymmA s v x
    dsimp [a, b, c, QssA, QsvA, QvvA, QssC, QsvC, QvvC]
    rw [hvalA, hvalC, hBx]
    ring
  have hroots := two_roots_of_neg_value a b c ha (by
    have hvalξ : a * ξ ^ 2 + b * ξ + c < 0 := by
      rw [← hpoly ξ]
      simpa [H] using hpξ
    exact hvalξ)
  rcases hroots with ⟨r₁, r₂, hne, hr₁, hr₂⟩
  refine ⟨r₁, r₂, hne, ?_, ?_⟩
  · have hp₁ : MvPolynomial.eval (fun k : Fin n => r₁ * (if k = s then 1 else 0) - v k) A.1 +
        (-(θ * (v i : ℝ))) * quadReal H (evec s)
          (fun k : Fin n => r₁ * (if k = s then 1 else 0) - v k) +
        (θ * (αi : ℝ)) * MvPolynomial.eval (fun k : Fin n => r₁ * (if k = s then 1 else 0) - v k) C.1 = 0 := by
      rw [hpoly r₁]
      exact hr₁
    simpa [H] using hp₁
  · have hp₂ : MvPolynomial.eval (fun k : Fin n => r₂ * (if k = s then 1 else 0) - v k) A.1 +
        (-(θ * (v i : ℝ))) * quadReal H (evec s)
          (fun k : Fin n => r₂ * (if k = s then 1 else 0) - v k) +
        (θ * (αi : ℝ)) * MvPolynomial.eval (fun k : Fin n => r₂ * (if k = s then 1 else 0) - v k) C.1 = 0 := by
      rw [hpoly r₂]
      exact hr₂
    simpa [H] using hp₂


-- =====================================================================
-- claim (II) ingredient: degree-0 homogeneous polynomials are constants
-- =====================================================================

/-- a degree-`0` homogeneous polynomial is the constant polynomial equal to its
constant coefficient. -/
lemma hom0_eq_const {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) (hp : p.IsHomogeneous 0) :
    p = MvPolynomial.C (p.coeff 0) := by
  classical
  ext m
  by_cases hm : m = 0
  · subst m
    rw [MvPolynomial.coeff_C]
    simp
  · have hw : Finsupp.weight (1 : σ → ℕ) m ≠ 0 := by
      intro hw0
      apply hm
      ext i
      have hsum := Finsupp.weight_eq_sum (w := (1 : σ → ℕ)) (f := m)
      rw [hw0] at hsum
      have hz : ∀ x : σ, x ∈ Finset.univ → m x • (1 : ℕ) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
          (f := fun x : σ => m x • (1 : ℕ))
          (by intro x hx; exact Nat.zero_le _)).mp hsum.symm
      have hxi := hz i (Finset.mem_univ i)
      simpa using hxi
    have hh : p.IsWeightedHomogeneous (1 : σ → ℕ) 0 := by
      simpa [MvPolynomial.IsHomogeneous] using hp
    have hz := MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero hh m hw
    rw [hz]
    symm
    rw [MvPolynomial.coeff_C]
    rw [if_neg (show ¬ (0 : σ →₀ ℕ) = m from fun h => hm h.symm)]


-- =====================================================================
-- exponent-(d) partials of P-elements are positive constants
-- =====================================================================

/-- positivity of an iterated-derivative coefficient: `coeff m (pderivL l p)` is a
positive multiple of `coeff (m + eSum l) p`. -/
lemma coeff_pderivL_pos {n : ℕ} (l : List (Fin n)) (p : MvPolynomial (Fin n) ℝ) (m : Fin n →₀ ℕ)
    (hpnn : ∀ e : Fin n →₀ ℕ, 0 ≤ p.coeff e)
    (hpos : 0 < p.coeff (m + Commons.Combinatorics.MvPolynomial.eSum l)) :
    0 < (nuij_pderivL l p).coeff m := by
  induction l generalizing p m with
  | nil =>
      simpa [nuij_pderivL, Commons.Combinatorics.MvPolynomial.eSum] using hpos
  | cons i l ih =>
      have hpd : 0 < (pderiv i p).coeff (m + Commons.Combinatorics.MvPolynomial.eSum l) := by
        have hc2 := MvPolynomial.coeff_pderiv (p := p) (i := i) (m := m + Commons.Combinatorics.MvPolynomial.eSum l)
        have he : m + Commons.Combinatorics.MvPolynomial.eSum l + ne n i =
            m + Commons.Combinatorics.MvPolynomial.eSum (i :: l) := by
          rw [Commons.Combinatorics.MvPolynomial.eSum_cons]
          simp [ne, add_assoc, add_comm, add_left_comm]
        rw [hc2]
        have hc : 0 < p.coeff (m + Commons.Combinatorics.MvPolynomial.eSum l + ne n i) := by
          rw [he]
          exact hpos
        have hf : 0 < (((m + Commons.Combinatorics.MvPolynomial.eSum l) i : ℕ) + 1 : ℝ) := by
          positivity
        positivity
      exact (by simpa [nuij_pderivL_cons] using
        (ih (pderiv i p) m (coeff_pderiv_nonneg' i p hpnn) hpd))

/-- a length-`d` iterated partial of a positive (`P n d`) element is a positive constant. -/
lemma pderivL_const_pos_of_P {n d : ℕ} (l : List (Fin n)) (f : H n d) (hf : f ∈ P n d)
    (hl : l.length = d) :
    ∃ c : ℝ, 0 < c ∧ nuij_pderivL l f.1 = MvPolynomial.C c := by
  have hdeg0 : d - l.length = 0 := by omega
  have hh : (nuij_pderivL l f.1).IsHomogeneous 0 := by
    simpa [hdeg0] using nuij_pderivL_isHomogeneous l f.1 d f.2
  have heq := hom0_eq_const (nuij_pderivL l f.1) hh
  have hpos : 0 < (nuij_pderivL l f.1).coeff 0 := by
    apply coeff_pderivL_pos l f.1 0 (P_coeff_nonneg f hf)
    have hw' := Commons.Combinatorics.MvPolynomial.degN_eSum (σ := Fin n) (l := l)
    have hw : Finsupp.weight (1 : Fin n → ℕ) (Commons.Combinatorics.MvPolynomial.eSum l) = d := by
      change Finsupp.weight (fun x : Fin n => (1 : ℕ)) (Commons.Combinatorics.MvPolynomial.eSum l) = d
      simpa [Commons.Combinatorics.MvPolynomial.degN, hl] using hw'
    simpa using hf (Commons.Combinatorics.MvPolynomial.eSum l) hw
  refine ⟨(nuij_pderivL l f.1).coeff 0, hpos, ?_⟩
  exact heq


-- =====================================================================
-- over-derivation kills homogeneous polynomials
-- =====================================================================

/-- derivatives of the zero polynomial vanish. -/
lemma nuij_pderivL_zero {n : ℕ} (l : List (Fin n)) :
    nuij_pderivL l (0 : MvPolynomial (Fin n) ℝ) = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      rw [nuij_pderivL_cons]
      have hz : pderiv i (0 : MvPolynomial (Fin n) ℝ) = 0 := by
        ext m
        rw [MvPolynomial.coeff_pderiv]
        simp
      rw [hz]
      exact ih

/-- differentiating a degree-`d` homogeneous polynomial along more than `d` directions
gives the zero polynomial. -/
lemma pderivL_zero_of_length_gt {n : ℕ} (l : List (Fin n)) (p : MvPolynomial (Fin n) ℝ)
    {d : ℕ} (hp : p.IsHomogeneous d) (hl : d < l.length) :
    nuij_pderivL l p = 0 := by
  classical
  let l1 : List (Fin n) := l.take d
  let l2 : List (Fin n) := l.drop d
  have hsplit : l1 ++ l2 = l := by
    dsimp [l1, l2]
    exact List.take_append_drop d l
  have hlen1 : l1.length = d := by
    dsimp [l1]
    rw [List.length_take]
    have hmin : min d l.length = d := by omega
    simpa [hmin]
  have hlen2 : l2.length = l.length - d := by
    dsimp [l2]
    rw [List.length_drop]
  have hlen2pos : 0 < l2.length := by
    by_contra h0
    have hlen0 : l2.length = 0 := by omega
    have hz : l.length = d := by
      rw [← hsplit]
      rw [List.length_append, hlen1, hlen0]
      simp
    have hlt : d < d := by
      simpa [hz] using hl
    omega
  have hh : (nuij_pderivL l1 p).IsHomogeneous 0 := by
    have hh' := nuij_pderivL_isHomogeneous l1 p d hp
    have h : d - l1.length = 0 := by omega
    simpa [h] using hh'
  have hconst := hom0_eq_const (nuij_pderivL l1 p) hh
  -- pderivL l p = pderivL l2 (pderivL l1 p)
  have hmain : nuij_pderivL l p = nuij_pderivL l2 (nuij_pderivL l1 p) := by
    rw [← hsplit]
    rw [nuij_pderivL_append]
  rw [hmain]
  rcases l2 with _ | ⟨j, rest⟩
  · exfalso
    have : (0 : ℕ) < 0 := by simpa using hlen2pos
    omega
  · rw [nuij_pderivL_cons]
    rw [hconst]
    have hC : pderiv j (MvPolynomial.C ((nuij_pderivL l1 p).coeff 0)) = 0 := by
      exact pderiv_of_homogeneous_zero j (MvPolynomial.C ((nuij_pderivL l1 p).coeff 0))
        (MvPolynomial.isHomogeneous_C (Fin n) ((nuij_pderivL l1 p).coeff 0))
    rw [hC]
    exact nuij_pderivL_zero rest


-- =====================================================================
-- exponent partials (∂^α) : definitions and length/zero/constant facts
-- =====================================================================

/-- a canonical list realizing an exponent (all repetitions of each index). -/
noncomputable def exponentList {n : ℕ} (α : Fin n →₀ ℕ) : List (Fin n) := by
  classical
  exact List.flatMap (fun i => List.replicate (α i) i) α.support.toList

/-- the iterated partial derivative `∂^α` for an exponent `α`. -/
noncomputable def pderivExp {n : ℕ} (α : Fin n →₀ ℕ) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  nuij_pderivL (exponentList α) p

/-- sum over a list equals the sum over its `toFinset`, when the list has no repeats. -/
lemma list_sum_map_toFinset {α : Type*} [DecidableEq α] (l : List α) (hl : l.Nodup)
    (f : α → ℕ) : (l.map f).sum = ∑ x ∈ l.toFinset, f x := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have hnot : a ∉ t.toFinset := by
        have : a ∉ t := (List.nodup_cons.mp hl).1
        exact fun h => this (List.mem_toFinset.mp h)
      rw [List.map_cons, List.sum_cons]
      rw [List.toFinset_cons]
      rw [Finset.sum_insert hnot]
      rw [ih (List.nodup_cons.mp hl).2]

/-- the exponent list of `α` has length `weight 1 α`. -/
lemma exponentList_length {n : ℕ} (α : Fin n →₀ ℕ) :
    (exponentList α).length = Finsupp.weight (1 : Fin n → ℕ) α := by
  classical
  unfold exponentList
  rw [List.length_flatMap]
  have hfun : (fun i : Fin n => (List.replicate (α i) i).length) = (fun i : Fin n => α i) := by
    funext i
    simp [List.length_replicate]
  rw [hfun]
  have hbr := list_sum_map_toFinset (α.support.toList) (Finset.nodup_toList α.support)
    (fun i : Fin n => α i)
  have hto : α.support.toList.toFinset = α.support := by
    ext i
    simp
  rw [hbr, hto]
  rw [Finsupp.weight_eq_sum]
  rw [Finset.sum_subset (s₁ := α.support) (s₂ := Finset.univ)
    (f := fun x : Fin n => α x) (h := fun x hx => Finset.mem_univ x)
    (hf := fun x hxu hxs => by simp [Finsupp.notMem_support_iff.mp hxs])]
  simp

/-- differentiating a degree-`d` homogeneous polynomial along an exponent of weight
greater than `d` gives zero. -/
lemma pderivExp_zero_of_weight_gt {n d : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous d) (β : Fin n →₀ ℕ)
    (hβ : d < Finsupp.weight (1 : Fin n → ℕ) β) :
    pderivExp β p = 0 := by
  unfold pderivExp
  apply pderivL_zero_of_length_gt
  · exact hp
  · rw [exponentList_length]
    exact hβ

/-- if `weight 1 β = d` and `f ∈ P n d`, then `∂^β f` is a positive constant. -/
lemma pderivExp_const_pos_of_P {n d : ℕ} (f : H n d) (hf : f ∈ P n d)
    (β : Fin n →₀ ℕ) (hβ : Finsupp.weight (1 : Fin n → ℕ) β = d) :
    ∃ c : ℝ, 0 < c ∧ pderivExp β f.1 = MvPolynomial.C c := by
  unfold pderivExp
  apply pderivL_const_pos_of_P (l := exponentList β) f hf
  rw [exponentList_length]
  exact hβ


-- =====================================================================
-- commutation and permutation invariance of list derivatives
-- =====================================================================

/-- partial derivatives commute. -/
lemma nuij_pderiv_comm {n : ℕ} (i j : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  exact rayleigh_pre.pderiv_comm i j p

/-- iterated derivatives are invariant under permutation of the list. -/
lemma nuij_pderivL_perm {n : ℕ} {l₁ l₂ : List (Fin n)} (hp : l₁.Perm l₂)
    (p : MvPolynomial (Fin n) ℝ) : nuij_pderivL l₁ p = nuij_pderivL l₂ p := by
  revert p
  induction hp with
  | nil => intro p; rfl
  | cons a h ih =>
      intro p
      rw [nuij_pderivL_cons, nuij_pderivL_cons]
      exact ih (pderiv a p)
  | swap a b l =>
      intro p
      simp only [nuij_pderivL_cons]
      rw [nuij_pderiv_comm b a p]
  | trans h₁ h₂ ih₁ ih₂ =>
      intro p
      exact (ih₁ p).trans (ih₂ p)



-- =====================================================================
-- single-coordinate power rule
-- =====================================================================

/-- sum of two single-coordinate unit exponents. -/
lemma single_add_single {n : ℕ} (i : Fin n) (a b : ℕ) :
    Finsupp.single i a + Finsupp.single i b = Finsupp.single i (a + b) := by
  ext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [hj]



/-- derivative of `X i ^ m` is `m · X i^(m-1)`. -/
lemma pderiv_X_pow {n : ℕ} (i : Fin n) (m : ℕ) :
    pderiv i (X i ^ m) = (m : ℝ) • (X i ^ (m - 1) : MvPolynomial (Fin n) ℝ) := by
  ext t
  rw [MvPolynomial.coeff_pderiv]
  rw [MvPolynomial.coeff_X_pow]
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  rw [MvPolynomial.coeff_X_pow]
  by_cases m0 : m = 0
  · subst m
    have hcond : ¬ (0 = t + Finsupp.single i (1 : ℕ)) := by
      intro h0
      have hs : Finsupp.single i (0 : ℕ) = t + Finsupp.single i (1 : ℕ) := by simpa using h0
      have h0v : (0 : ℕ) = t i + 1 := by
        have hq := congrArg (fun q : Fin n →₀ ℕ => q i) hs
        simpa using hq
      omega
    simp [hcond]
  · have hm1 : 0 < m := Nat.pos_of_ne_zero m0
    have hm : m - 1 + 1 = m := Nat.sub_add_cancel hm1
    by_cases ht : t = Finsupp.single i (m - 1)
    · subst t
      have hsum : Finsupp.single i (m - 1) + Finsupp.single i 1 = Finsupp.single i m := by
        rw [single_add_single, hm]
      rw [hsum]
      rw [if_pos rfl, if_pos rfl]
      have hfac : ((Finsupp.single i (m - 1)) i : ℝ) + 1 = (m : ℝ) := by
        have hc : (Finsupp.single i (m - 1)) i = m - 1 := by simp
        rw [hc]
        have hca : ((m - 1 : ℕ) : ℝ) + 1 = ((m - 1 + 1 : ℕ) : ℝ) := by norm_num
        rw [hca]
        exact congrArg (fun k : ℕ => (k : ℝ)) hm
      rw [hfac]
      ring
    · have hne' : Finsupp.single i m ≠ t + Finsupp.single i 1 := by
        intro heq
        apply ht
        apply Finsupp.ext
        intro j
        by_cases hj : j = i
        · subst j
          have hi := congrArg (fun q : Fin n →₀ ℕ => q i) heq
          simp at hi
          have htineq : t i = m - 1 := by omega
          simpa [htineq]
        · have hval := congrArg (fun q : Fin n →₀ ℕ => q j) heq
          have hleft : (Finsupp.single i m) j = 0 := by simp [hj]
          have hright : (t + Finsupp.single i (1 : ℕ)) j = t j := by simp [hj]
          rw [hleft, hright] at hval
          simpa [hj] using hval.symm
      have hnot1 : ¬ Finsupp.single i m = t + Finsupp.single i 1 := hne'
      have hnot2 : ¬ Finsupp.single i (m - 1) = t := fun h => ht h.symm
      rw [if_neg hnot1]
      rw [if_neg hnot2]
      simp


/-- the product rule for `pderiv i (X i ^ m * u)`. -/
lemma pderiv_X_pow_mul {n : ℕ} (i : Fin n) (m : ℕ) (u : MvPolynomial (Fin n) ℝ) :
    pderiv i (X i ^ m * u) =
      (m : ℝ) • (X i ^ (m - 1)) * u + X i ^ m * pderiv i u := by
  rw [MvPolynomial.pderiv_mul]
  rw [pderiv_X_pow]


-- =====================================================================
-- leibniz_X_pow (step 3): induction bases
-- =====================================================================

/-- the empty exponent partial is the identity. -/
lemma pderivExp_zero {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : pderivExp 0 p = p := by
  simp [pderivExp, exponentList, nuij_pderivL]

/-- a single `i`-derivative in exponent form. -/
lemma pderivExp_single {n : ℕ} (i : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    pderivExp (Finsupp.single i 1) p = pderiv i p := by
  classical
  unfold pderivExp
  unfold exponentList
  simp [nuij_pderivL]


-- =====================================================================
-- L1 support lemmas
-- =====================================================================

/-- inserting into a `Finset` permutes the `toList` past a singleton. -/
lemma toList_insert_perm {α : Type*} [DecidableEq α] (s : Finset α) (a : α) (h : a ∉ s) :
    (insert a s).toList.Perm (a :: s.toList) :=
  Finset.toList_insert h


/-- removing the full `i`-power from an exponent leaves the support minus `i`. -/
lemma support_sub_single {n : ℕ} (α : Fin n →₀ ℕ) (i : Fin n) (ha : 0 < α i) :
    α.support = insert i (α - Finsupp.single i (α i)).support := by
  classical
  ext j
  constructor
  · intro hj
    have hmem : α j ≠ 0 := Finsupp.mem_support_iff.mp hj
    by_cases hj' : j = i
    · subst j
      simp
    · apply Finset.mem_insert_of_mem
      apply Finsupp.mem_support_iff.mpr
      have hsub : (α - Finsupp.single i (α i)) j = α j := by
        simp [hj']
      rw [hsub]
      exact hmem
  · intro hj
    simp at hj
    rcases hj with hji | hS
    · have hmem_i : i ∈ α.support := Finsupp.mem_support_iff.mpr (ne_of_gt ha)
      simpa [hji] using hmem_i
    · by_contra hz
      apply hS
      have hzero : α j = 0 := by
        by_contra hnot
        exact hz (Finsupp.mem_support_iff.mpr hnot)
      have hjne : j ≠ i := by
        intro hji
        subst j
        exact (ne_of_gt ha) hzero
      simp [hzero, hjne]

end

/-- the exponent list of `α` splits into the full `i`-part followed by the rest,
as a multiset (up to permutation). -/
lemma exponentList_concat_of_pos {n : ℕ} (α : Fin n →₀ ℕ) (i : Fin n) (ha : 0 < α i) :
    (exponentList (Finsupp.single i (α i)) ++ exponentList (α - Finsupp.single i (α i))).Perm
      (exponentList α) := by
  classical
  unfold exponentList
  let rest := α - Finsupp.single i (α i)
  have hnot : i ∉ rest.support := by
    intro h
    have hc : rest i ≠ 0 := Finsupp.mem_support_iff.mp h
    have hz : rest i = 0 := by simp [rest]
    exact hc hz
  have hsgl : (Finsupp.single i (α i)).support.toList = [i] := by
    rw [Finsupp.support_single i (ne_of_gt ha)]
    simp
  have hal : α.support.toList.Perm (i :: rest.support.toList) := by
    have hs := support_sub_single α i ha
    rw [hs]
    have hp := toList_insert_perm rest.support i hnot
    simpa [rest] using hp
  have hre : ∀ j : Fin n, j ∈ rest.support.toList → (List.replicate (rest j) j).Perm
      (List.replicate (α j) j) := by
    intro j hj
    have hjmem : j ∈ rest.support := Finset.mem_toList.mp hj
    have hjne : j ≠ i := by
      intro hji
      subst j
      exact hnot hjmem
    have hcoef : rest j = α j := by simp [rest, hjne]
    rw [hcoef]
  have hmain : (List.flatMap (fun j => List.replicate (α j) j) α.support.toList).Perm
      (List.flatMap (fun j => List.replicate (α j) j) (i :: rest.support.toList)) :=
    hal.flatMap (fun j _ => List.Perm.refl (List.replicate (α j) j))
  have hrew : (List.flatMap (fun j => List.replicate (α j) j) (i :: rest.support.toList)) =
      (List.replicate (α i) i ++ List.flatMap (fun j => List.replicate (α j) j) rest.support.toList) := by
    rw [List.flatMap_cons]
  rw [hrew] at hmain
  have hleft : (exponentList (Finsupp.single i (α i)) ++ exponentList rest).Perm
      (List.replicate (α i) i ++ List.flatMap (fun j => List.replicate (α j) j) rest.support.toList) := by
    apply List.Perm.append
    · dsimp [exponentList]
      rw [hsgl]
      simp [List.flatMap_cons, List.flatMap_nil]
    · apply List.Perm.flatMap (List.Perm.refl rest.support.toList)
      intro j hj
      exact hre j hj
  exact hleft.trans hmain.symm


/-- subtracting back a peeled `i`-power cancels it (coefficient-wise in `ℕ`). -/
lemma sub_single_add_cancel {n : ℕ} (u : Fin n →₀ ℕ) (a : Fin n) (b : ℕ) :
    (u + Finsupp.single a b) - Finsupp.single a b = u := by
  ext x
  by_cases hxa : x = a
  · subst x
    simp [Nat.add_sub_cancel]
  · simp [hxa]

/-- `∂^α` factors through the full `i`-power, peeling the `i`-coordinate of `α` off first. -/
lemma pderivExp_split {n : ℕ} (α : Fin n →₀ ℕ) (i : Fin n) (ha : 0 < α i)
    (p : MvPolynomial (Fin n) ℝ) :
    pderivExp (α - Finsupp.single i (α i)) (pderivExp (Finsupp.single i (α i)) p) = pderivExp α p := by
  unfold pderivExp
  have hp := nuij_pderivL_perm (exponentList_concat_of_pos α i ha) p
  rw [nuij_pderivL_append] at hp
  exact hp

/-- the exponent list of a pure power `single a z` is `z` repetitions of `a`. -/
lemma exponentList_single_all {n : ℕ} (a : Fin n) (z : ℕ) :
    exponentList (Finsupp.single a z) = List.replicate z a := by
  classical
  by_cases hz : z = 0
  · subst z
    unfold exponentList
    simp
  · unfold exponentList
    rw [Finsupp.support_single a hz]
    simp

/-- a single-coordinate derivative commutes with every other derivative. -/
lemma pderivExp_single_comm {n : ℕ} (a : Fin n) (x : ℕ) (f : Fin n →₀ ℕ)
    (q : MvPolynomial (Fin n) ℝ) :
    pderivExp (Finsupp.single a x) (pderivExp f q) = pderivExp f (pderivExp (Finsupp.single a x) q) := by
  unfold pderivExp
  rw [← nuij_pderivL_append]
  rw [← nuij_pderivL_append]
  exact nuij_pderivL_perm (List.perm_append_comm (l₁ := exponentList f) (l₂ := exponentList (Finsupp.single a x))) q

/-- powers of the same single-coordinate derivative compose. -/
lemma pderivExp_single_add {n : ℕ} (a : Fin n) (x y : ℕ) (q : MvPolynomial (Fin n) ℝ) :
    pderivExp (Finsupp.single a x) (pderivExp (Finsupp.single a y) q) =
      pderivExp (Finsupp.single a (x + y)) q := by
  unfold pderivExp
  have hrep : List.replicate y a ++ List.replicate x a = List.replicate (x + y) a := by
    rw [Nat.add_comm]
    exact (List.replicate_add y x a).symm
  calc
    nuij_pderivL (exponentList (Finsupp.single a x)) (nuij_pderivL (exponentList (Finsupp.single a y)) q)
        = nuij_pderivL (exponentList (Finsupp.single a y) ++ exponentList (Finsupp.single a x)) q := by
            rw [← nuij_pderivL_append]
    _ = nuij_pderivL (List.replicate y a ++ List.replicate x a) q := by
            congr 1
            rw [exponentList_single_all, exponentList_single_all]
    _ = nuij_pderivL (List.replicate (x + y) a) q := by
            exact congrArg (fun l : List (Fin n) => nuij_pderivL l q) hrep
    _ = nuij_pderivL (exponentList (Finsupp.single a (x + y))) q := by
            congr 1
            rw [exponentList_single_all]

/-- `∂^β` is additive in the polynomial argument. -/
lemma pderivExp_add_poly {n : ℕ} (β : Fin n →₀ ℕ) (p q : MvPolynomial (Fin n) ℝ) :
    pderivExp β (p + q) = pderivExp β p + pderivExp β q := by
  unfold pderivExp
  induction exponentList β using List.recOn generalizing p q with
  | nil => simp [nuij_pderivL]
  | cons j l ih =>
      change nuij_pderivL l (pderiv j (p + q)) = nuij_pderivL l (pderiv j p) + nuij_pderivL l (pderiv j q)
      have hm : pderiv j (p + q) = pderiv j p + pderiv j q := Derivation.map_add (pderiv j) p q
      rw [hm]
      exact ih (pderiv j p) (pderiv j q)

/-- `∂^β` is linear in the polynomial argument. -/
lemma pderivExp_smul {n : ℕ} (β : Fin n →₀ ℕ) (a : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    pderivExp β (a • p) = a • pderivExp β p := by
  unfold pderivExp
  induction exponentList β using List.recOn generalizing p with
  | nil => simp [nuij_pderivL]
  | cons j l ih =>
      change nuij_pderivL l (pderiv j (a • p)) = a • nuij_pderivL l (pderiv j p)
      have hm : pderiv j (a • p) = a • pderiv j p := Derivation.map_smul (pderiv j) a p
      rw [hm]
      exact ih (pderiv j p)

/-- derivatives in a list that never mentions `i` pass through multiplication by `X i`. -/
lemma nuij_pderivL_mul_X_of_ne {n : ℕ} :
    ∀ (l : List (Fin n)) (i : Fin n), (∀ j ∈ l, j ≠ i) →
      ∀ v : MvPolynomial (Fin n) ℝ,
        nuij_pderivL l (X i * v) = X i * nuij_pderivL l v := by
  intro l
  induction l with
  | nil => intro i hl v; simp [nuij_pderivL]
  | cons j t ih =>
      intro i hl v
      have hj : j ≠ i := hl j (by simp)
      have hrest : ∀ k ∈ t, k ≠ i := by
        intro k hk
        exact hl k (by simp [hk])
      change nuij_pderivL t (pderiv j (X i * v)) = X i * nuij_pderivL t (pderiv j v)
      have hm : pderiv j (X i * v) = X i * pderiv j v := by
        rw [MvPolynomial.pderiv_mul]
        rw [MvPolynomial.pderiv_X_of_ne (i := j) (j := i) (Ne.symm hj)]
        ring
      rw [hm]
      exact ih i hrest (pderiv j v)

/-- if `β i = 0` then `∂^β` passes through multiplication by `X i`. -/
lemma pderivExp_mul_X_of_coord_zero {n : ℕ} (i : Fin n) (β : Fin n →₀ ℕ) (hβ : β i = 0)
    (v : MvPolynomial (Fin n) ℝ) :
    pderivExp β (X i * v) = X i * pderivExp β v := by
  unfold pderivExp
  exact nuij_pderivL_mul_X_of_ne (exponentList β) i (by
    intro j hj
    -- j is in the exponent list, hence j ∈ β.support; β j ≠ 0 → j ≠ i (else β i ≠ 0)
    have hjβ : j ∈ β.support := by
      rcases (List.mem_flatMap.mp hj) with ⟨a, ha, hmem⟩
      have ha' : a ∈ β.support := Finset.mem_toList.mp ha
      have haj : j = a := (List.mem_replicate.mp hmem).2
      subst a
      simpa using ha'
    intro hji
    subst j
    have hz : β i ≠ 0 := Finsupp.mem_support_iff.mp hjβ
    exact hz hβ) v

/-- iterating one derivative `a` times then one more equals `a + 1` times. -/
lemma pderivExp_single_succ {n : ℕ} (i : Fin n) (a : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    pderivExp (Finsupp.single i (a + 1)) p = pderivExp (Finsupp.single i a) (pderiv i p) := by
  unfold pderivExp
  rw [exponentList_single_all, exponentList_single_all]
  rw [List.replicate_succ]
  rfl

/-- `∂^(β+γ) = ∂^β ∘ ∂^γ` for exponents (derivatives commute, order is immaterial). -/
lemma pderivExp_add {n : ℕ} (β γ : Fin n →₀ ℕ) (p : MvPolynomial (Fin n) ℝ) :
    pderivExp (β + γ) p = pderivExp β (pderivExp γ p) := by
  classical
  revert β p
  -- strong induction on the weight of γ
  let P : ℕ → Prop := fun w => ∀ (γ : Fin n →₀ ℕ),
      Finsupp.weight (1 : Fin n → ℕ) γ = w → ∀ β p, pderivExp (β + γ) p = pderivExp β (pderivExp γ p)
  have hmain : ∀ w : ℕ, P w := by
    intro w
    induction w using Nat.strong_induction_on with
    | h w ih =>
        intro γ hw β p
        by_cases hγ0 : γ = 0
        · subst γ
          simp [pderivExp_zero]
        · have hsupp : ∃ a : Fin n, γ a ≠ 0 := by
            by_contra h
            apply hγ0
            ext a
            by_contra hza
            exact h ⟨a, hza⟩
          rcases hsupp with ⟨a, hγa⟩
          let b := γ a
          let f := γ - Finsupp.single a b
          have hb0 : b ≠ 0 := hγa
          have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
          have hf0 : f a = 0 := by
            simp [f, b]
          have hγsplit : γ = f + Finsupp.single a b := by
            ext x
            by_cases hxa : x = a
            · subst x
              simp [f, b, Nat.add_sub_cancel]
            · simp [f, b, hxa]
          have hwadd : w = Finsupp.weight (1 : Fin n → ℕ) f + b := by
            rw [← hw]
            rw [hγsplit]
            simp [Finsupp.weight_single]
          have hwf : Finsupp.weight (1 : Fin n → ℕ) f < w := by
            omega
          -- full IH with arbitrary β
          have hih : ∀ (β' : Fin n →₀ ℕ) (p' : MvPolynomial (Fin n) ℝ),
              pderivExp (β' + f) p' = pderivExp β' (pderivExp f p') := by
            intro β' p'
            exact ih (Finsupp.weight (1 : Fin n → ℕ) f) hwf f rfl β' p'
          have hβ0a : (β - Finsupp.single a (β a)) a = 0 := by
            simp
          let β₀ := β - Finsupp.single a (β a)
          have hβsplit : β = β₀ + Finsupp.single a (β a) := by
            ext x
            by_cases hxa : x = a
            · subst x
              simp [β₀, Nat.add_sub_cancel]
            · simp [β₀, hxa]
          have hsplitγ : pderivExp (f + Finsupp.single a b) p =
              pderivExp f (pderivExp (Finsupp.single a b) p) := by
            have hval : (f + Finsupp.single a b) a = b := by
              simp [hf0]
            have hpos : 0 < (f + Finsupp.single a b) a := by
              rw [hval]
              exact hbpos
            have hs := pderivExp_split (f + Finsupp.single a b) a hpos p
            rw [hval] at hs
            have hcancel : (f + Finsupp.single a b) - Finsupp.single a b = f := by
              simpa [Nat.add_comm] using sub_single_add_cancel f a b
            rw [hcancel] at hs
            exact hs.symm
          -- factor out the a-power of β
          have hβfactor : ∀ w : MvPolynomial (Fin n) ℝ,
              pderivExp β w = pderivExp β₀ (pderivExp (Finsupp.single a (β a)) w) := by
            intro w
            by_cases hA : β a = 0
            · have hβ0 : β₀ = β := by
                simp [β₀, hA]
              have hS : Finsupp.single a (β a) = 0 := by
                simp [hA]
              rw [hβ0, hS]
              simp [pderivExp_zero]
            · have hpos : 0 < β a := Nat.pos_of_ne_zero hA
              have hs := pderivExp_split β a hpos w
              have hβ0eq : β - Finsupp.single a (β a) = β₀ := by
                rfl
              rw [hβ0eq] at hs
              exact hs.symm
          -- total reorganization β + γ = (β₀ + f) + single a (βa + b)
          have htot : β + (f + Finsupp.single a b) = (β₀ + f) + Finsupp.single a (β a + b) := by
            ext x
            by_cases hxa : x = a
            · subst x
              simp [β₀, hf0, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            · simp [β₀, hxa]
          -- the a-peel of the total
          have hmain2 : pderivExp ((β₀ + f) + Finsupp.single a (β a + b)) p =
              pderivExp (β₀ + f) (pderivExp (Finsupp.single a (β a + b)) p) := by
            have hval : ((β₀ + f) + Finsupp.single a (β a + b)) a = β a + b := by
              simp [β₀, hf0]
            have hpos : 0 < ((β₀ + f) + Finsupp.single a (β a + b)) a := by
              rw [hval]
              omega
            have hs := pderivExp_split ((β₀ + f) + Finsupp.single a (β a + b)) a hpos p
            rw [hval] at hs
            have hcancel : ((β₀ + f) + Finsupp.single a (β a + b)) - Finsupp.single a (β a + b) = β₀ + f := by
              simpa [Nat.add_comm, Nat.add_assoc] using sub_single_add_cancel (β₀ + f) a (β a + b)
            rw [hcancel] at hs
            exact hs.symm
          calc
            pderivExp (β + γ) p
                = pderivExp (β + (f + Finsupp.single a b)) p := by
                    rw [hγsplit]
            _ = pderivExp ((β₀ + f) + Finsupp.single a (β a + b)) p := by
                    rw [htot]
            _ = pderivExp (β₀ + f) (pderivExp (Finsupp.single a (β a + b)) p) := hmain2
            _ = pderivExp β₀ (pderivExp f (pderivExp (Finsupp.single a (β a + b)) p)) := by
                    rw [hih β₀ (pderivExp (Finsupp.single a (β a + b)) p)]
            _ = pderivExp β₀ (pderivExp f (pderivExp (Finsupp.single a (β a)) (pderivExp (Finsupp.single a b) p))) := by
                    rw [← pderivExp_single_add a (β a) b p]
            _ = pderivExp β₀ (pderivExp (Finsupp.single a (β a)) (pderivExp f (pderivExp (Finsupp.single a b) p))) := by
                    rw [← pderivExp_single_comm a (β a) f (pderivExp (Finsupp.single a b) p)]
            _ = pderivExp β₀ (pderivExp (Finsupp.single a (β a)) (pderivExp (f + Finsupp.single a b) p)) := by
                    rw [← hsplitγ]
            _ = pderivExp β (pderivExp (f + Finsupp.single a b) p) := by
                    rw [← hβfactor (pderivExp (f + Finsupp.single a b) p)]
            _ = pderivExp β (pderivExp γ p) := by
                    rw [hγsplit]
  exact hmain (Finsupp.weight (1 : Fin n → ℕ) γ) γ rfl


/-- peeling off the full `i`-power: `(α - αᵢ·eᵢ) + αᵢ·eᵢ = α`. -/
lemma exp_sub_single_add {n : ℕ} (α : Fin n →₀ ℕ) (i : Fin n) :
    (α - Finsupp.single i (α i)) + Finsupp.single i (α i) = α := by
  ext x
  by_cases hx : x = i
  · subst x
    simp
  · simp [hx]

/-- weight of the rest after removing the full `i`-power. -/
lemma weight_sub_single {n : ℕ} (α : Fin n →₀ ℕ) (i : Fin n) :
    Finsupp.weight (1 : Fin n → ℕ) (α - Finsupp.single i (α i)) + α i =
      Finsupp.weight (1 : Fin n → ℕ) α := by
  have hw := congrArg (Finsupp.weight (1 : Fin n → ℕ)) (exp_sub_single_add α i)
  rw [map_add] at hw
  rw [Finsupp.weight_single] at hw
  simpa using hw

/-- constant-multiplication equals scalar multiplication in `MvPolynomial`. -/
lemma C_mul_eq_smul {n : ℕ} (a : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.C a * p = a • p := by
  rw [← MvPolynomial.algebraMap_eq]
  rw [Algebra.smul_def]

/-- a scaled polynomial product `a • (C c · p) = C (a·c) · p`. -/
lemma smul_C_mul {n : ℕ} (a c : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    a • (MvPolynomial.C c * p) = MvPolynomial.C (a * c) * p := by
  rw [C_mul_eq_smul, C_mul_eq_smul]
  ext m
  simp [mul_assoc]

/-- if `β i = 0` then `∂^β` passes through multiplication by `X i ^ k`. -/
lemma pderivExp_mul_X_pow_of_coord_zero {n : ℕ} (i : Fin n) (β : Fin n →₀ ℕ)
    (hβ : β i = 0) (k : ℕ) (v : MvPolynomial (Fin n) ℝ) :
    pderivExp β (X i ^ k * v) = X i ^ k * pderivExp β v := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        pderivExp β (X i ^ (k + 1) * v)
            = pderivExp β (X i * (X i ^ k * v)) := by
                rw [pow_succ']
                ring_nf
        _ = X i * pderivExp β (X i ^ k * v) := by
                exact pderivExp_mul_X_of_coord_zero i β hβ (X i ^ k * v)
        _ = X i * (X i ^ k * pderivExp β v) := by rw [ih]
        _ = X i ^ (k + 1) * pderivExp β v := by
                rw [pow_succ']
                ring_nf

/-- pure power: `∂ᵢᵃ (Xᵢ^{a+2}) = c · Xᵢ²` with `0 < c`. -/
lemma pderivExp_single_X_pow_sq {n : ℕ} (i : Fin n) (a : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      pderivExp (Finsupp.single i a) (X i ^ (a + 2)) = MvPolynomial.C c * X i ^ 2 := by
  induction a with
  | zero =>
      refine ⟨1, by norm_num, ?_⟩
      simpa using pderivExp_zero (X i ^ (2 : ℕ))
  | succ a ih =>
      rcases ih with ⟨c, hc, hmain⟩
      have hsub : ((a + 1) + 2) - 1 = a + 2 := by omega
      rw [pderivExp_single_succ i a (X i ^ ((a + 1) + 2))]
      rw [pderiv_X_pow i ((a + 1) + 2)]
      rw [hsub]
      rw [pderivExp_smul]
      rw [hmain]
      have hsc : (((a + 1) + 2 : ℕ) : ℝ) • (MvPolynomial.C c * X i ^ 2) =
          MvPolynomial.C ((((a + 1) + 2 : ℕ) : ℝ) * c) * X i ^ 2 :=
        smul_C_mul (((a + 1) + 2 : ℕ) : ℝ) c (X i ^ 2)
      rw [hsc]
      refine ⟨(((a + 1) + 2 : ℕ) : ℝ) * c, by positivity, rfl⟩

/-- value of `∂^α (Xᵢ^{αᵢ+2} · ∂ₛ^{αᵢ+2} f)` on the line `x·eₛ − v` is `vᵢ²·c`, `c > 0`. -/
lemma claimII_term_value {n d : ℕ} (i s : Fin n) (his : i ≠ s)
    (f : H n d) (hf : f ∈ P n d) (α : Fin n →₀ ℕ)
    (hα : Finsupp.weight (1 : Fin n → ℕ) α + 2 = d) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (v : Fin n → ℝ) (x : ℝ),
        MvPolynomial.eval (fun k : Fin n => x * (if k = s then 1 else 0) - v k)
          (pderivExp α (X i ^ (α i + 2) * pderivExp ((α i + 2) • Finsupp.single s 1) f.1)) =
        (v i)^2 * c := by
  classical
  have hrest0 : (α - Finsupp.single i (α i)) i = 0 := by
    simp
  have hsingle : (α i + 2) • Finsupp.single s 1 = Finsupp.single s (α i + 2) := by
    rw [Finsupp.smul_single]
    simp
  have hαsplit : Finsupp.single i (α i) + (α - Finsupp.single i (α i)) = α := by
    rw [add_comm]
    exact exp_sub_single_add α i
  -- swap: ∂^α = ∂^{αᵢ·eᵢ} ∘ ∂^{rest}, and rest passes through X_i^{αᵢ+2}
  have hstep1 : pderivExp α (X i ^ (α i + 2) * pderivExp ((α i + 2) • Finsupp.single s 1) f.1) =
      pderivExp (Finsupp.single i (α i))
        (X i ^ (α i + 2) * pderivExp (α - Finsupp.single i (α i))
          (pderivExp ((α i + 2) • Finsupp.single s 1) f.1)) := by
    have hs2 := pderivExp_add (Finsupp.single i (α i)) (α - Finsupp.single i (α i))
      (X i ^ (α i + 2) * pderivExp ((α i + 2) • Finsupp.single s 1) f.1)
    rw [hαsplit] at hs2
    rw [hs2]
    rw [pderivExp_mul_X_pow_of_coord_zero i (α - Finsupp.single i (α i)) hrest0 (α i + 2)
      (pderivExp ((α i + 2) • Finsupp.single s 1) f.1)]
  -- the rest hits u = ∂ₛ^{αᵢ+2} f giving a positive constant
  have hrest_u : pderivExp (α - Finsupp.single i (α i))
      (pderivExp ((α i + 2) • Finsupp.single s 1) f.1) =
      pderivExp ((α - Finsupp.single i (α i)) + Finsupp.single s (α i + 2)) f.1 := by
    rw [hsingle]
    exact (pderivExp_add (α - Finsupp.single i (α i)) (Finsupp.single s (α i + 2)) f.1).symm
  have hw : Finsupp.weight (1 : Fin n → ℕ)
      ((α - Finsupp.single i (α i)) + Finsupp.single s (α i + 2)) = d := by
    rw [map_add, Finsupp.weight_single]
    simp
    have hw1 := weight_sub_single α i
    omega
  rcases pderivExp_const_pos_of_P f hf ((α - Finsupp.single i (α i)) + Finsupp.single s (α i + 2)) hw
    with ⟨c1, hc1, hc1eq⟩
  have hconst : pderivExp (α - Finsupp.single i (α i))
      (pderivExp ((α i + 2) • Finsupp.single s 1) f.1) = MvPolynomial.C c1 := by
    rw [hrest_u]
    exact hc1eq
  have hstep2 : pderivExp α (X i ^ (α i + 2) * pderivExp ((α i + 2) • Finsupp.single s 1) f.1) =
      pderivExp (Finsupp.single i (α i)) (X i ^ (α i + 2) * MvPolynomial.C c1) := by
    rw [hstep1, hconst]
  have hmulC : X i ^ (α i + 2) * MvPolynomial.C c1 = c1 • (X i ^ (α i + 2) : MvPolynomial (Fin n) ℝ) := by
    calc
      X i ^ (α i + 2) * MvPolynomial.C c1 = MvPolynomial.C c1 * X i ^ (α i + 2) := by rw [mul_comm]
      _ = c1 • (X i ^ (α i + 2) : MvPolynomial (Fin n) ℝ) := C_mul_eq_smul c1 (X i ^ (α i + 2))
  have hstep3 : pderivExp α (X i ^ (α i + 2) * pderivExp ((α i + 2) • Finsupp.single s 1) f.1) =
      pderivExp (Finsupp.single i (α i)) (c1 • (X i ^ (α i + 2))) := by
    rw [hstep2, hmulC]
  rw [hstep3]
  rw [pderivExp_smul (Finsupp.single i (α i)) c1 (X i ^ (α i + 2))]
  rcases pderivExp_single_X_pow_sq i (α i) with ⟨c2, hc2, hsq⟩
  rw [hsq]
  refine ⟨c1 * c2, by positivity, ?_⟩
  intro v x
  rw [smul_C_mul c1 c2 (X i ^ 2)]
  simp [pow_two]
  have his2 : ¬ i = s := his
  rw [if_neg his2]
  ring

/-- evaluation of the derivative `∂ⱼ` of a quadratic equals the Hessian bilinear form. -/
lemma eval_pderiv_quad {n : ℕ} (q : H n 2) (j : Fin n) (w : Fin n → ℝ) :
    MvPolynomial.eval w (MvPolynomial.pderiv j q.1) = quadReal q.hessian (evec j) w := by
  classical
  rw [hessian_aeval_eq_pderiv_eq_sum_hessian n q j]
  simp only [map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [quadReal]
  rw [Finset.sum_comm]
  simp [evec]

/-- `q` restricted to the line has a double (multiple) root at `c`. -/
def isDoubleRoot {n : ℕ} (q : H n 2) (s : Fin n) (v : Fin n → ℝ) (c : ℝ) : Prop :=
  MvPolynomial.eval (fun k : Fin n => c * (if k = s then 1 else 0) - v k) q.1 = 0 ∧
    quadReal q.hessian (evec s) (fun k : Fin n => c * (if k = s then 1 else 0) - v k) = 0

/-- `q` restricted to the line has two distinct real roots. -/
def twoRootsOf {n : ℕ} (q : H n 2) (s : Fin n) (v : Fin n → ℝ) : Prop :=
  ∃ a b : ℝ, a ≠ b ∧
    MvPolynomial.eval (fun k : Fin n => a * (if k = s then 1 else 0) - v k) q.1 = 0 ∧
    MvPolynomial.eval (fun k : Fin n => b * (if k = s then 1 else 0) - v k) q.1 = 0

/-- a positive stable quadratic with no two distinct roots on a line has a double root. -/
lemma stable_pos_quad_mult_zero {n : ℕ} (hn : 0 < n) (s : Fin n) (q : H n 2)
    (hq : q ∈ S n 2 ∩ P n 2) (v : Fin n → ℝ) (hnot : ¬ twoRootsOf q s v) :
    ∃ c : ℝ, isDoubleRoot q s v c := by
  classical
  have hS : q ∈ S n 2 := hq.1
  have hP : q ∈ P n 2 := hq.2
  have hq0 : q.1 ≠ 0 := stable_pos_quad_ne_zero hn q hP
  have hcard := stable_quad_hessian_card_le_one q hS hq0
  have hsymm : (q.hessian).IsSymm := hessian_symm n q
  have hQss : 0 < quadReal q.hessian (evec s) (evec s) := by
    have hpos : ∀ i j : Fin n, 0 < q.hessian i j := (mem_P_iff_hessian_pos n q).mp hP
    have : quadReal q.hessian (evec s) (evec s) = q.hessian s s := by simp [quadReal, evec]
    rw [this]
    exact hpos s s
  have hQss0 : quadReal q.hessian (evec s) (evec s) ≠ 0 := ne_of_gt hQss
  have hdisc := quad_line_discr_nonneg q s hP hcard v
  have hgt : ¬ (quadReal q.hessian (evec s) v) ^ 2 > quadReal q.hessian (evec s) (evec s) *
      quadReal q.hessian v v := by
    intro hgt
    apply hnot
    rcases two_roots_of_discr_gt (quadReal q.hessian (evec s) (evec s))
        (-2 * quadReal q.hessian (evec s) v) (quadReal q.hessian v v) hQss (by nlinarith)
      with ⟨a, b, hab, ha, hb⟩
    refine ⟨a, b, hab, ?_, ?_⟩
    · have hline := quad_line_value_eq q s v a
      rw [hline]
      nlinarith
    · have hline := quad_line_value_eq q s v b
      rw [hline]
      nlinarith
  have hle : (quadReal q.hessian (evec s) v) ^ 2 ≤ quadReal q.hessian (evec s) (evec s) *
      quadReal q.hessian v v := le_of_not_gt hgt
  have heq : (quadReal q.hessian (evec s) v) ^ 2 = quadReal q.hessian (evec s) (evec s) *
      quadReal q.hessian v v := le_antisymm hle hdisc
  refine ⟨quadReal q.hessian (evec s) v / quadReal q.hessian (evec s) (evec s), ?_, ?_⟩
  · have hline := quad_line_value_eq q s v (quadReal q.hessian (evec s) v /
      quadReal q.hessian (evec s) (evec s))
    rw [hline]
    field_simp [hQss0]
    nlinarith
  · have hline := quadReal_evec_line q.hessian hsymm s v (quadReal q.hessian (evec s) v /
      quadReal q.hessian (evec s) (evec s))
    rw [hline]
    field_simp [hQss0]
    ring

/-- a positive quadratic with a double root has no two distinct roots. -/
lemma doubleRoot_no_two_roots {n : ℕ} (s : Fin n) (q : H n 2) (hP : q ∈ P n 2)
    (v : Fin n → ℝ) {c : ℝ} (hc : isDoubleRoot q s v c) :
    ¬ twoRootsOf q s v := by
  classical
  intro htwo
  rcases htwo with ⟨a, b, hab, ha, hb⟩
  have hQss : 0 < quadReal q.hessian (evec s) (evec s) := by
    have hpos : ∀ i j : Fin n, 0 < q.hessian i j := (mem_P_iff_hessian_pos n q).mp hP
    have : quadReal q.hessian (evec s) (evec s) = q.hessian s s := by simp [quadReal, evec]
    rw [this]
    exact hpos s s
  have hsymm : (q.hessian).IsSymm := hessian_symm n q
  let Qss : ℝ := quadReal q.hessian (evec s) (evec s)
  let Qsv : ℝ := quadReal q.hessian (evec s) v
  let Qvv : ℝ := quadReal q.hessian v v
  have hFa' : Qss * a ^ 2 - 2 * Qsv * a + Qvv = 0 := by
    have hline := quad_line_value_eq q s v a
    have hz : (1 / 2 : ℝ) * (Qss * a ^ 2 - 2 * Qsv * a + Qvv) = 0 := by
      dsimp [Qss, Qsv, Qvv]
      rw [← hline]
      exact ha
    nlinarith
  have hFb' : Qss * b ^ 2 - 2 * Qsv * b + Qvv = 0 := by
    have hline := quad_line_value_eq q s v b
    have hz : (1 / 2 : ℝ) * (Qss * b ^ 2 - 2 * Qsv * b + Qvv) = 0 := by
      dsimp [Qss, Qsv, Qvv]
      rw [← hline]
      exact hb
    nlinarith
  have hgt := Commons.Data.Real.sq_gt_of_two_roots_quad Qss Qsv Qvv hQss ⟨a, b, hab, hFa', hFb'⟩
  have hFc' : Qss * c ^ 2 - 2 * Qsv * c + Qvv = 0 := by
    have hline := quad_line_value_eq q s v c
    have hz : (1 / 2 : ℝ) * (Qss * c ^ 2 - 2 * Qsv * c + Qvv) = 0 := by
      dsimp [Qss, Qsv, Qvv]
      rw [← hline]
      exact hc.1
    nlinarith
  have hQsvrel : Qsv = c * Qss := by
    have hqline := quadReal_evec_line q.hessian hsymm s v c
    have hgoal0 : quadReal q.hessian (evec s) v = c * quadReal q.hessian (evec s) (evec s) := by
      nlinarith [hqline, hc.2]
    dsimp [Qsv, Qss]
    exact hgoal0
  have hdisc'' : Qsv ^ 2 = Qss * Qvv := by
    have hQvv : Qvv = Qss * c ^ 2 := by
      nlinarith
    rw [hQsvrel, hQvv]
    ring
  nlinarith


open Commons.Combinatorics.MvPolynomial

/-- iterating the deformation `(1 + θ·X_i·∂_s)` `m` times on `H n d`. -/
noncomputable def iterDef {n d : ℕ} (i s : Fin n) (θ : ℝ) : ℕ → H n d → H n d
  | 0, f => f
  | m + 1, f => deformElem (n := n) (d := d) i s θ (iterDef i s θ m f)

lemma iterDef_succ {n d : ℕ} (i s : Fin n) (θ : ℝ) (m : ℕ) (f : H n d) :
    iterDef i s θ (m + 1) f = deformElem (n := n) (d := d) i s θ (iterDef i s θ m f) := rfl

/-- `(1 + θ·X_i·∂_s)` preserves `P n d`. -/
lemma deformElem_mem_P {n d : ℕ} (i s : Fin n) (θ : ℝ) (hθ : 0 ≤ θ)
    (f : H n d) (hf : f ∈ P n d) : deformElem (n := n) (d := d) i s θ f ∈ P n d := by
  intro m hm
  change 0 < (f.1 + (C θ) * X i * pderiv s f.1).coeff m
  rw [MvPolynomial.coeff_add]
  rw [mul_assoc, MvPolynomial.coeff_C_mul]
  have h1 : 0 < f.1.coeff m := hf m hm
  have hnn : ∀ a : Fin n →₀ ℕ, 0 ≤ (pderiv s f.1).coeff a :=
    coeff_pderiv_nonneg' s f.1 (P_coeff_nonneg f hf)
  have h2 : 0 ≤ (X i * pderiv s f.1).coeff m := coeff_X_mul_nonneg i (pderiv s f.1) hnn m
  nlinarith [mul_nonneg hθ h2]

/-- `(1 + θ·X_i·∂_s)` preserves `L n d` for `θ ≥ 0`, `d ≥ 0`. -/
lemma deformElem_mem_L {n d : ℕ} (hn : 0 < n) (i s : Fin n) (θ : ℝ) (hθ : 0 ≤ θ)
    (f : H n d) (hf : f ∈ L n d) : deformElem (n := n) (d := d) i s θ f ∈ L n d := by
  rcases deform_mem_L n d hn θ hθ i s f hf with ⟨g, hg, hgeq⟩
  have heq : deformElem (n := n) (d := d) i s θ f = g := by
    apply Subtype.ext
    rw [deformElem_val]
    exact hgeq.symm
  rwa [heq]

/-- iterates of the deformation preserve `P n d`. -/
lemma iterDef_mem_P {n d : ℕ} (i s : Fin n) (θ : ℝ) (hθ : 0 ≤ θ)
    (m : ℕ) (f : H n d) (hf : f ∈ P n d) : iterDef i s θ m f ∈ P n d := by
  induction m with
  | zero => simpa [iterDef] using hf
  | succ m ih =>
      rw [iterDef_succ]
      exact deformElem_mem_P i s θ hθ (iterDef i s θ m f) ih

/-- iterates of the deformation preserve `L n d`. -/
lemma iterDef_mem_L {n d : ℕ} (hn : 0 < n) (i s : Fin n) (θ : ℝ) (hθ : 0 ≤ θ)
    (m : ℕ) (f : H n d) (hf : f ∈ L n d) : iterDef i s θ m f ∈ L n d := by
  induction m with
  | zero => simpa [iterDef] using hf
  | succ m ih =>
      rw [iterDef_succ]
      exact deformElem_mem_L hn i s θ hθ (iterDef i s θ m f) ih

/-- the `d`-th iterate equals `(1 + θ·X_i·∂_s)^d` acting on `H n d`. -/
lemma iterDef_eq_nuij_power {n d : ℕ} (i s : Fin n) (θ : ℝ) (f : H n d) :
    iterDef i s θ d f = nuij_power (n := n) i s d θ f := by
  cases d with
  | zero => simp [iterDef, nuij_power]
  | succ k =>
      have hde : ∀ (x : H n (k + 1)), deformElem (n := n) (d := k + 1) i s θ x =
          (nuij_deformEnd (n := n) (k := k) i s θ) x := by
        intro x
        rw [deformElem_eq_deformH i s θ x]
        rw [nuij_deformEnd_eq_deformH k i s θ x]
      have hchain : ∀ m : ℕ, iterDef i s θ m f = ((nuij_deformEnd (n := n) (k := k) i s θ) ^ m) f := by
        intro m
        induction m with
        | zero => simp [iterDef]
        | succ m ih =>
            rw [iterDef_succ]
            rw [hde (iterDef i s θ m f)]
            rw [ih]
            rw [pow_succ']
            rfl
      change iterDef i s θ (k + 1) f = nuij_power (n := n) i s (k + 1) θ f
      rw [hchain (k + 1)]
      rfl

/-- the polynomial deformation `p ↦ p + θ·X_i·∂_s p`. -/
noncomputable def polyDef {n : ℕ} (i s : Fin n) (θ : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ := p + (C θ) * X i * pderiv s p

/-- iterating the polynomial deformation `m` times. -/
noncomputable def polyIter {n : ℕ} (i s : Fin n) (θ : ℝ) : ℕ → MvPolynomial (Fin n) ℝ → MvPolynomial (Fin n) ℝ
  | 0, p => p
  | m + 1, p => polyDef i s θ (polyIter i s θ m p)

/-- value of the polynomial iterate. -/
lemma iterDef_val {n d : ℕ} (i s : Fin n) (θ : ℝ) (m : ℕ) (f : H n d) :
    (iterDef i s θ m f).1 = polyIter i s θ m f.1 := by
  induction m with
  | zero => simp [iterDef, polyIter]
  | succ m ih =>
      rw [iterDef_succ]
      change (deformElem (n := n) (d := d) i s θ (iterDef i s θ m f)).1 =
        polyIter i s θ (m + 1) f.1
      rw [deformElem_val, ih]
      rfl

/-- `∂^α (X_i · u) = X_i·∂^α u + α_i · ∂^{α−e_i} u` (Leibniz, single `X`). -/
lemma pderivExp_X_mul {n : ℕ} (α : Fin n →₀ ℕ) (i : Fin n) (u : MvPolynomial (Fin n) ℝ) :
    pderivExp α (X i * u) = X i * pderivExp α u +
      ((α i : ℝ)) • pderivExp (α - ne n i) u := by
  classical
  let a : ℕ := α i
  let rest : Fin n →₀ ℕ := α - Finsupp.single i a
  have hrest0 : rest i = 0 := by
    dsimp [rest, a]
    simp
  have hsplit : Finsupp.single i a + rest = α := by
    dsimp [a, rest]
    rw [add_comm]
    exact exp_sub_single_add α i
  -- single-coordinate rule
  have hsingle : ∀ (b : ℕ) (v : MvPolynomial (Fin n) ℝ),
      pderivExp (Finsupp.single i b) (X i * v) = X i * pderivExp (Finsupp.single i b) v +
        (b : ℝ) • pderivExp (Finsupp.single i (b - 1)) v := by
    intro b
    induction b with
    | zero =>
        intro v
        simp [pderivExp_zero]
    | succ b ih =>
        intro v
        have hp1 : pderiv i (X i * v) = v + X i * pderiv i v := by
          have h := pderiv_X_pow_mul i 1 v
          norm_num at h
          simpa using h
        by_cases hb0 : b = 0
        · subst b
          have hz0 : (Finsupp.single i 0 : Fin n →₀ ℕ) = 0 := by
            ext x
            by_cases hx : x = i
            · subst x; simp
            · simp [hx]
          calc
            pderivExp (Finsupp.single i (0 + 1)) (X i * v)
                = pderivExp (Finsupp.single i 0) (pderiv i (X i * v)) := by
                    rw [pderivExp_single_succ i 0 (X i * v)]
            _ = pderiv i (X i * v) := by
                    rw [hz0]
                    exact pderivExp_zero (pderiv i (X i * v))
            _ = X i * pderiv i v + v := by rw [hp1]; ring
            _ = X i * pderivExp (Finsupp.single i (0 + 1)) v +
                  (((0 + 1 : ℕ) : ℝ)) • pderivExp (Finsupp.single i (0 + 1 - 1)) v := by
                    have h01 : (0 + 1 : ℕ) = 1 := by rfl
                    have h0 : (0 + 1 - 1 : ℕ) = 0 := by omega
                    rw [h0, h01, pderivExp_single i v, hz0, pderivExp_zero]
                    simp
        · have hbge : 1 ≤ b := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hb0)
          have hsub : b - 1 + 1 = b := Nat.sub_add_cancel hbge
          calc
            pderivExp (Finsupp.single i (b + 1)) (X i * v)
                = pderivExp (Finsupp.single i b) (pderiv i (X i * v)) := pderivExp_single_succ i b (X i * v)
            _ = pderivExp (Finsupp.single i b) (v + X i * pderiv i v) := by rw [hp1]
            _ = pderivExp (Finsupp.single i b) v + pderivExp (Finsupp.single i b) (X i * pderiv i v) := by
                    rw [pderivExp_add_poly]
            _ = pderivExp (Finsupp.single i b) v + (X i * pderivExp (Finsupp.single i b) (pderiv i v) +
                  (b : ℝ) • pderivExp (Finsupp.single i (b - 1)) (pderiv i v)) := by
                    rw [ih (pderiv i v)]
            _ = X i * pderivExp (Finsupp.single i (b + 1)) v +
                  (((b + 1 : ℕ) : ℝ)) • pderivExp (Finsupp.single i ((b + 1) - 1)) v := by
                    -- ∂^b (pderiv v) = ∂^{b+1} v ; ∂^{b-1}(pderiv v) = ∂^{b} v
                    rw [← pderivExp_single_succ i b v]
                    have h1 : pderivExp (Finsupp.single i (b - 1)) (pderiv i v) = pderivExp (Finsupp.single i b) v := by
                      rw [← pderivExp_single_succ i (b - 1) v]
                      rw [hsub]
                    rw [h1]
                    have hsub2 : (b + 1) - 1 = b := by omega
                    rw [hsub2]
                    have hscalar : (((b + 1 : ℕ) : ℝ) • pderivExp (Finsupp.single i b) v) =
                        ((b : ℕ) : ℝ) • pderivExp (Finsupp.single i b) v +
                          pderivExp (Finsupp.single i b) v := by
                      rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
                    rw [hscalar]
                    ac_rfl
  have hmain : pderivExp α (X i * u) = pderivExp (Finsupp.single i a) (pderivExp rest (X i * u)) := by
    have hs := pderivExp_add (Finsupp.single i a) rest (X i * u)
    rw [hsplit] at hs
    exact hs
  calc
    pderivExp α (X i * u)
        = pderivExp (Finsupp.single i a) (pderivExp rest (X i * u)) := hmain
    _ = pderivExp (Finsupp.single i a) (X i * pderivExp rest u) := by
            rw [pderivExp_mul_X_of_coord_zero i rest hrest0 u]
    _ = X i * pderivExp (Finsupp.single i a) (pderivExp rest u) +
          (a : ℝ) • pderivExp (Finsupp.single i (a - 1)) (pderivExp rest u) := hsingle a (pderivExp rest u)
    _ = X i * pderivExp α u + (a : ℝ) • pderivExp (α - ne n i) u := by
            have hs1 : pderivExp (Finsupp.single i a) (pderivExp rest u) = pderivExp α u := by
              have hs := pderivExp_add (Finsupp.single i a) rest u
              rw [hsplit] at hs
              exact hs.symm
            have hs2 : pderivExp (Finsupp.single i (a - 1)) (pderivExp rest u) =
                pderivExp ((Finsupp.single i (a - 1)) + rest) u := by
              exact (pderivExp_add (Finsupp.single i (a - 1)) rest u).symm
            have hsame : Finsupp.single i (a - 1) + rest = α - ne n i := by
              dsimp [a, rest, ne]
              ext x
              by_cases hx : x = i
              · subst x
                simp
              · simp [hx]
            rw [hs1, hs2, hsame]
/-- value of `∂^α` on the deformed polynomial (the Leibniz expansion of the deformation). -/
lemma deform_expansion {n d : ℕ} (i s : Fin n) (θ : ℝ) (α : Fin n →₀ ℕ) (g : H n d) :
    pderivExp α (deformElem (n := n) (d := d) i s θ g).1 =
      pderivExp α g.1 + (C θ) * X i * pderivExp (α + ne n s) g.1 +
        C (θ * (α i : ℝ)) * pderivExp ((α - ne n i) + ne n s) g.1 := by
  classical
  have hval : (deformElem (n := n) (d := d) i s θ g).1 = g.1 + (C θ) * X i * pderiv s g.1 := rfl
  have hpder : pderiv s g.1 = pderivExp (ne n s) g.1 := by
    symm
    exact pderivExp_single s g.1
  calc
    pderivExp α (deformElem (n := n) (d := d) i s θ g).1
        = pderivExp α (g.1 + (C θ) * X i * pderiv s g.1) := by rw [hval]
    _ = pderivExp α g.1 + pderivExp α ((C θ) * (X i * pderiv s g.1)) := by
            rw [mul_assoc]
            rw [pderivExp_add_poly]
    _ = pderivExp α g.1 + pderivExp α (θ • (X i * pderiv s g.1)) := by
            rw [C_mul_eq_smul θ (X i * pderiv s g.1)]
    _ = pderivExp α g.1 + θ • pderivExp α (X i * pderiv s g.1) := by
            rw [pderivExp_smul α θ (X i * pderiv s g.1)]
    _ = pderivExp α g.1 + θ • (X i * pderivExp α (pderiv s g.1) +
          (α i : ℝ) • pderivExp (α - ne n i) (pderiv s g.1)) := by
            rw [pderivExp_X_mul α i (pderiv s g.1)]
    _ = pderivExp α g.1 + θ • (X i * pderivExp (α + ne n s) g.1 +
          (α i : ℝ) • pderivExp ((α - ne n i) + ne n s) g.1) := by
            have hp1 : pderivExp α (pderiv s g.1) = pderivExp (α + ne n s) g.1 := by
              rw [hpder]
              exact (pderivExp_add α (ne n s) g.1).symm
            have hp2 : pderivExp (α - ne n i) (pderiv s g.1) = pderivExp ((α - ne n i) + ne n s) g.1 := by
              rw [hpder]
              exact (pderivExp_add (α - ne n i) (ne n s) g.1).symm
            rw [hp1, hp2]
    _ = pderivExp α g.1 + (C θ) * X i * pderivExp (α + ne n s) g.1 +
          C (θ * (α i : ℝ)) * pderivExp ((α - ne n i) + ne n s) g.1 := by
            let A : MvPolynomial (Fin n) ℝ := pderivExp (α + ne n s) g.1
            let B : MvPolynomial (Fin n) ℝ := pderivExp ((α - ne n i) + ne n s) g.1
            let β : ℝ := (α i : ℝ)
            have hA : θ • (X i * A) = (C θ) * X i * A := by
              dsimp [A]
              rw [← C_mul_eq_smul θ (X i * pderivExp (α + ne n s) g.1)]
              rw [← mul_assoc]
            have hB : θ • (β • B) = C (θ * β) * B := by
              rw [← mul_smul]
              rw [← C_mul_eq_smul (θ * β) B]
            have hsc : θ • (X i * A + β • B) = (C θ) * X i * A + C (θ * β) * B := by
              rw [smul_add]
              rw [hA, hB]
            rw [hsc]
            ring

/-- the quadratic `∂^α f` for an exponent `α` of weight `d − 2`, as an `H n 2` element. -/
noncomputable def quadOf {n d : ℕ} (hd : 2 ≤ d) (α : Fin n →₀ ℕ)
    (hα : Finsupp.weight (1 : Fin n → ℕ) α = d - 2) (f : H n d) : H n 2 :=
  ⟨pderivExp α f.1, by
    have hh := nuij_pderivL_isHomogeneous (exponentList α) f.1 d f.2
    have hl : d - (exponentList α).length = 2 := by
      rw [exponentList_length, hα]
      omega
    simpa [pderivExp, hl] using hh⟩

/-- `∂^α f ∈ S n 2` when `f ∈ L n d`. -/
lemma quadOf_mem_S {n d : ℕ} (hd : 2 ≤ d) (α : Fin n →₀ ℕ)
    (hα : Finsupp.weight (1 : Fin n → ℕ) α = d - 2) (f : H n d) (hf : f ∈ L n d) :
    quadOf hd α hα f ∈ S n 2 := by
  have hl : (exponentList α).length = d - 2 := by
    rw [exponentList_length, hα]
  rcases partials_mem_L_exact2 hd (exponentList α) hl f hf with ⟨u, hu, hu_eq⟩
  have heq : quadOf hd α hα f = u := by
    apply Subtype.ext
    change pderivExp α f.1 = u.1
    rw [pderivExp]
    exact hu_eq.symm
  rwa [heq]

/-- `∂^α f ∈ P n 2` when `f ∈ P n d`. -/
lemma quadOf_mem_P {n d : ℕ} (hd : 2 ≤ d) (α : Fin n →₀ ℕ)
    (hα : Finsupp.weight (1 : Fin n → ℕ) α = d - 2) (f : H n d) (hf : f ∈ P n d) :
    quadOf hd α hα f ∈ P n 2 := by
  intro m hm
  change 0 < (pderivExp α f.1).coeff m
  rw [pderivExp]
  apply coeff_pderivL_pos (l := exponentList α) (p := f.1) (m := m)
  · exact P_coeff_nonneg f hf
  · have hlen : (exponentList α).length = d - 2 := by
      rw [exponentList_length, hα]
    have hw' := Commons.Combinatorics.MvPolynomial.degN_eSum (σ := Fin n) (l := exponentList α)
    have hsum : Finsupp.weight (1 : Fin n → ℕ) (Commons.Combinatorics.MvPolynomial.eSum (exponentList α)) = d - 2 := by
      change Finsupp.weight (fun x : Fin n => (1 : ℕ)) (Commons.Combinatorics.MvPolynomial.eSum (exponentList α)) = d - 2
      simpa [Commons.Combinatorics.MvPolynomial.degN, hlen] using hw'
    have hw : Finsupp.weight (1 : Fin n → ℕ) (m + Commons.Combinatorics.MvPolynomial.eSum (exponentList α)) = d := by
      rw [map_add, hsum]
      omega
    exact hf (m + Commons.Combinatorics.MvPolynomial.eSum (exponentList α)) hw

/-- the quadratic `∂^α g` stays in `S n 2 ∩ P n 2` for `g ∈ L n d ∩ P n d`. -/
lemma quadOf_mem_SP {n d : ℕ} (hd : 2 ≤ d) (α : Fin n →₀ ℕ)
    (hα : Finsupp.weight (1 : Fin n → ℕ) α = d - 2) (g : H n d)
    (hg : g ∈ L n d ∩ P n d) :
    quadOf hd α hα g ∈ S n 2 ∩ P n 2 := by
  constructor
  · exact quadOf_mem_S hd α hα g hg.1
  · exact quadOf_mem_P hd α hα g hg.2

open Commons.Combinatorics.MvPolynomial

/-- `∂^{α+eⱼ} p = ∂ⱼ (∂^α p)`. -/
lemma pderivExp_single_add_deriv {n : ℕ} (α : Fin n →₀ ℕ) (j : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    pderivExp (α + ne n j) p = pderiv j (pderivExp α p) := by
  change pderivExp (α + Finsupp.single j 1) p = pderiv j (pderivExp α p)
  have h1 : pderivExp (α + Finsupp.single j 1) p = pderivExp α (pderivExp (Finsupp.single j 1) p) :=
    pderivExp_add α (Finsupp.single j 1) p
  rw [h1]
  rw [pderivExp_single j p]
  have hc1 : pderivExp α (pderiv j p) = pderiv j (pderivExp α p) := by
    have hc := pderivExp_single_comm j 1 α p
    rw [pderivExp_single j (pderivExp α p)] at hc
    rw [pderivExp_single j p] at hc
    exact hc.symm
  exact hc1

/-- `pderiv j (∂^α p) = ∂^{α+eⱼ} p`. -/
lemma pderiv_pderivExp_add {n : ℕ} (α : Fin n →₀ ℕ) (j : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    pderiv j (pderivExp α p) = pderivExp (α + ne n j) p :=
  (pderivExp_single_add_deriv α j p).symm

/-- exponent bookkeeping: `(α − eᵢ + eₛ) + eᵢ = α + eₛ` for `αᵢ > 0`, `i ≠ s`. -/
lemma exp_sub_add_ne {n : ℕ} (α : Fin n →₀ ℕ) (i s : Fin n) (hαi : 0 < α i) (his : i ≠ s) :
    ((α - ne n i) + ne n s) + ne n i = α + ne n s := by
  dsimp [ne]
  ext x
  by_cases hxi : x = i
  · subst x
    have hsub : α i - 1 + 1 = α i := Nat.sub_add_cancel hαi
    simp [hsub, his]
  · by_cases hxs : x = s
    · subst x
      simp [hxi]
    · simp [hxi, hxs]

/-- weight of `β = α − eᵢ + eₛ` is `d − 2` when `weight α = d − 2` and `αᵢ > 0`. -/
lemma exp_weight_sub_add {n : ℕ} (α : Fin n →₀ ℕ) (i s : Fin n) (hαi : 0 < α i)
    (d : ℕ) (hαw : Finsupp.weight (1 : Fin n → ℕ) α = d - 2) :
    Finsupp.weight (1 : Fin n → ℕ) ((α - ne n i) + ne n s) = d - 2 := by
  have hs : (α - ne n i) + ne n i = α := by
    dsimp [ne]
    ext x
    by_cases hxi : x = i
    · subst x
      have hsub : α i - 1 + 1 = α i := Nat.sub_add_cancel hαi
      simp [hsub]
    · simp [hxi]
  have hwmain : Finsupp.weight (1 : Fin n → ℕ) (α - ne n i) + 1 =
      Finsupp.weight (1 : Fin n → ℕ) α := by
    have hw := congrArg (Finsupp.weight (1 : Fin n → ℕ)) hs
    rw [map_add, Finsupp.weight_single] at hw
    simpa using hw
  rw [map_add, Finsupp.weight_single]
  simp
  rw [hwmain, hαw]

/-- `eval` of the line restriction of the deformed quadratic (bridge identity). -/
lemma restr_deform_line {n d : ℕ} (hd : 2 ≤ d) (i s : Fin n) (his : i ≠ s)
    (θ : ℝ) (α : Fin n →₀ ℕ) (hαw : Finsupp.weight (1 : Fin n → ℕ) α = d - 2)
    (hαi : 0 < α i) (g : H n d) (v : Fin n → ℝ) (x : ℝ) :
    MvPolynomial.eval (fun k : Fin n => x * (if k = s then 1 else 0) - v k)
        (pderivExp α (deformElem (n := n) (d := d) i s θ g).1) =
      MvPolynomial.eval (fun k : Fin n => x * (if k = s then 1 else 0) - v k) (pderivExp α g.1) +
        (-(θ * v i)) * quadReal (quadOf hd α hαw g).hessian (evec s)
          (fun k : Fin n => x * (if k = s then 1 else 0) - v k) +
        (θ * (α i : ℝ)) * MvPolynomial.eval (fun k : Fin n => x * (if k = s then 1 else 0) - v k)
          (pderivExp ((α - ne n i) + ne n s) g.1) := by
  classical
  have hde := deform_expansion i s θ α g
  rw [hde]
  rw [MvPolynomial.eval_add, MvPolynomial.eval_add]
  have hmid : MvPolynomial.eval (fun k : Fin n => x * (if k = s then 1 else 0) - v k)
        ((C θ) * X i * pderivExp (α + ne n s) g.1) =
      θ * (-(v i)) * quadReal (quadOf hd α hαw g).hessian (evec s)
        (fun k : Fin n => x * (if k = s then 1 else 0) - v k) := by
    rw [mul_assoc, MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    have hlin : x * (if i = s then 1 else 0) - v i = -(v i) := by
      by_cases his2 : i = s
      · exact False.elim (his his2)
      · simp [his2]
    rw [hlin]
    rw [pderivExp_single_add_deriv α s g.1]
    have hqA1 : (quadOf hd α hαw g).1 = pderivExp α g.1 := rfl
    rw [← hqA1]
    rw [eval_pderiv_quad (quadOf hd α hαw g) s (fun k : Fin n => x * (if k = s then 1 else 0) - v k)]
    ring
  have hlast : MvPolynomial.eval (fun k : Fin n => x * (if k = s then 1 else 0) - v k)
        (C (θ * (α i : ℝ)) * pderivExp ((α - ne n i) + ne n s) g.1) =
      (θ * (α i : ℝ)) * MvPolynomial.eval (fun k : Fin n => x * (if k = s then 1 else 0) - v k)
        (pderivExp ((α - ne n i) + ne n s) g.1) := by
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C]
  rw [hmid, hlast]
  ring

/-- the `eᵢ`-derivative of `qC` equals the `eₛ`-derivative of `qA` along the line (hB). -/
lemma restr_deriv_comm {n d : ℕ} (hd : 2 ≤ d) (i s : Fin n)
    (α : Fin n →₀ ℕ) (hαw : Finsupp.weight (1 : Fin n → ℕ) α = d - 2)
    (hαi : 0 < α i) (his : i ≠ s) (g : H n d) (v : Fin n → ℝ) (x : ℝ) :
    quadReal (quadOf hd α hαw g).hessian (evec s)
        (fun k : Fin n => x * (if k = s then 1 else 0) - v k) =
      quadReal (quadOf hd ((α - ne n i) + ne n s)
        (exp_weight_sub_add α i s hαi d hαw) g).hessian (evec i)
        (fun k : Fin n => x * (if k = s then 1 else 0) - v k) := by
  classical
  have hβw : Finsupp.weight (1 : Fin n → ℕ) ((α - ne n i) + ne n s) = d - 2 :=
    exp_weight_sub_add α i s hαi d hαw
  let qA : H n 2 := quadOf hd α hαw g
  let qC : H n 2 := quadOf hd ((α - ne n i) + ne n s) hβw g
  let w : Fin n → ℝ := fun k : Fin n => x * (if k = s then 1 else 0) - v k
  have hpi : pderiv i (pderivExp ((α - ne n i) + ne n s) g.1) =
      pderiv s (pderivExp α g.1) := by
    have hc1 := pderiv_pderivExp_add ((α - ne n i) + ne n s) i g.1
    rw [hc1]
    have hsame := exp_sub_add_ne α i s hαi his
    rw [hsame]
    exact pderivExp_single_add_deriv α s g.1
  have hqAp : qA.1 = pderivExp α g.1 := rfl
  have hqCp : qC.1 = pderivExp ((α - ne n i) + ne n s) g.1 := rfl
  calc
    quadReal qA.hessian (evec s) w
        = MvPolynomial.eval w (pderiv s qA.1) := (eval_pderiv_quad qA s w).symm
    _ = MvPolynomial.eval w (pderiv s (pderivExp α g.1)) := by rw [hqAp]
    _ = MvPolynomial.eval w (pderiv i (pderivExp ((α - ne n i) + ne n s) g.1)) := by rw [hpi]
    _ = MvPolynomial.eval w (pderiv i qC.1) := by rw [hqCp]
    _ = quadReal qC.hessian (evec i) w := eval_pderiv_quad qC i w

/-- a positive quadratic attaining a strictly negative value on a line has two roots. -/
lemma posQuad_neg_value_two_roots {n : ℕ} (s : Fin n) (q : H n 2) (hP : q ∈ P n 2)
    (v : Fin n → ℝ) {x₀ : ℝ}
    (hx : MvPolynomial.eval (fun k : Fin n => x₀ * (if k = s then 1 else 0) - v k) q.1 < 0) :
    twoRootsOf q s v := by
  classical
  let Qss : ℝ := quadReal q.hessian (evec s) (evec s)
  let Qsv : ℝ := quadReal q.hessian (evec s) v
  let Qvv : ℝ := quadReal q.hessian v v
  have hQss : 0 < Qss := by
    dsimp [Qss]
    have hpos : ∀ i j : Fin n, 0 < q.hessian i j := (mem_P_iff_hessian_pos n q).mp hP
    have : quadReal q.hessian (evec s) (evec s) = q.hessian s s := by simp [quadReal, evec]
    rw [this]
    exact hpos s s
  have hline := quad_line_value_eq q s v x₀
  have hmain : (1 / 2 : ℝ) * (Qss * x₀ ^ 2 - 2 * Qsv * x₀ + Qvv) < 0 := by
    dsimp [Qss, Qsv, Qvv] at hx ⊢
    rw [← hline]
    exact hx
  have hneg : ((1 / 2 : ℝ) * Qss) * x₀ ^ 2 + (-Qsv) * x₀ + (1 / 2 : ℝ) * Qvv < 0 := by
    have heq : ((1 / 2 : ℝ) * Qss) * x₀ ^ 2 + (-Qsv) * x₀ + (1 / 2 : ℝ) * Qvv =
        (1 / 2 : ℝ) * (Qss * x₀ ^ 2 - 2 * Qsv * x₀ + Qvv) := by ring
    rw [heq]
    exact hmain
  rcases two_roots_of_neg_value ((1 / 2 : ℝ) * Qss) (-Qsv) ((1 / 2 : ℝ) * Qvv)
      (by positivity) hneg with ⟨a, b, hab, ha, hb⟩
  have hFa' : Qss * a ^ 2 - 2 * Qsv * a + Qvv = 0 := by
    nlinarith
  have hFb' : Qss * b ^ 2 - 2 * Qsv * b + Qvv = 0 := by
    nlinarith
  refine ⟨a, b, hab, ?_, ?_⟩
  · have hla := quad_line_value_eq q s v a
    rw [hla]
    change (1 / 2 : ℝ) * (Qss * a ^ 2 - 2 * Qsv * a + Qvv) = 0
    nlinarith [hFa']
  · have hlb := quad_line_value_eq q s v b
    rw [hlb]
    change (1 / 2 : ℝ) * (Qss * b ^ 2 - 2 * Qsv * b + Qvv) = 0
    nlinarith [hFb']

/-- Claim (III): a double root of the deformed quadratic is a double root of the original. -/
lemma nuij_claimIII {n : ℕ} (hn : 0 < n) (d : ℕ) (hd : 3 ≤ d)
    (i s : Fin n) (his : i ≠ s) (θ : ℝ) (hθ : 0 < θ)
    (g : H n d) (hgL : g ∈ L n d) (hgP : g ∈ P n d)
    (α : Fin n →₀ ℕ) (hαw : Finsupp.weight (1 : Fin n → ℕ) α = d - 2) (hαi : 0 < α i)
    (v : Fin n → ℝ) (c : ℝ) :
    isDoubleRoot (quadOf (by omega : 2 ≤ d) α hαw (deformElem (n := n) (d := d) i s θ g)) s v c →
    isDoubleRoot (quadOf (by omega : 2 ≤ d) α hαw g) s v c := by
  classical
  have hd2 : 2 ≤ d := by omega
  intro hcD
  let qA : H n 2 := quadOf hd2 α hαw g
  let qD : H n 2 := quadOf hd2 α hαw (deformElem (n := n) (d := d) i s θ g)
  let β : Fin n →₀ ℕ := (α - ne n i) + ne n s
  have hβw : Finsupp.weight (1 : Fin n → ℕ) β = d - 2 := by
    dsimp [β]
    exact exp_weight_sub_add α i s hαi d hαw
  let qC : H n 2 := quadOf hd2 β hβw g
  have hgSP : g ∈ L n d ∩ P n d := ⟨hgL, hgP⟩
  have hA_SP : qA ∈ S n 2 ∩ P n 2 := by
    dsimp [qA]
    exact quadOf_mem_SP hd2 α hαw g hgSP
  have hD_SP : qD ∈ S n 2 ∩ P n 2 := by
    dsimp [qD]
    have hdeSP : deformElem (n := n) (d := d) i s θ g ∈ L n d ∩ P n d := by
      constructor
      · exact deformElem_mem_L hn i s θ (le_of_lt hθ) g hgL
      · exact deformElem_mem_P i s θ (le_of_lt hθ) g hgP
    exact quadOf_mem_SP hd2 α hαw (deformElem (n := n) (d := d) i s θ g) hdeSP
  have hC_SP : qC ∈ S n 2 ∩ P n 2 := by
    dsimp [qC]
    exact quadOf_mem_SP hd2 β hβw g hgSP
  have hnotD : ¬ twoRootsOf qD s v := doubleRoot_no_two_roots s qD hD_SP.2 v hcD
  have hnotA : ¬ twoRootsOf qA s v := by
    intro htwoA
    have hcC : (qC.hessian.charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1 := by
      have hq0 : qC.1 ≠ 0 := stable_pos_quad_ne_zero hn qC hC_SP.2
      exact stable_quad_hessian_card_le_one qC hC_SP.1 hq0
    rcases deform_line_two_roots i s qA qC hA_SP.2 hC_SP.2 hcC v
        (fun x => restr_deriv_comm hd2 i s α hαw hαi his g v x) htwoA θ hθ (α i)
      with ⟨r₁, r₂, hne, hr₁, hr₂⟩
    apply hnotD
    refine ⟨r₁, r₂, hne, ?_, ?_⟩
    · change MvPolynomial.eval (fun k : Fin n => r₁ * (if k = s then 1 else 0) - v k)
          (pderivExp α (deformElem (n := n) (d := d) i s θ g).1) = 0
      have hbr := restr_deform_line hd2 i s his θ α hαw hαi g v r₁
      rw [hbr]
      change MvPolynomial.eval (fun k : Fin n => r₁ * (if k = s then 1 else 0) - v k) qA.1 +
          (-(θ * v i)) * quadReal qA.hessian (evec s)
            (fun k : Fin n => r₁ * (if k = s then 1 else 0) - v k) +
          (θ * (α i : ℝ)) * MvPolynomial.eval (fun k : Fin n => r₁ * (if k = s then 1 else 0) - v k) qC.1 = 0
      exact hr₁
    · change MvPolynomial.eval (fun k : Fin n => r₂ * (if k = s then 1 else 0) - v k)
          (pderivExp α (deformElem (n := n) (d := d) i s θ g).1) = 0
      have hbr := restr_deform_line hd2 i s his θ α hαw hαi g v r₂
      rw [hbr]
      change MvPolynomial.eval (fun k : Fin n => r₂ * (if k = s then 1 else 0) - v k) qA.1 +
          (-(θ * v i)) * quadReal qA.hessian (evec s)
            (fun k : Fin n => r₂ * (if k = s then 1 else 0) - v k) +
          (θ * (α i : ℝ)) * MvPolynomial.eval (fun k : Fin n => r₂ * (if k = s then 1 else 0) - v k) qC.1 = 0
      exact hr₂
  rcases stable_pos_quad_mult_zero hn s qA hA_SP v hnotA with ⟨c', hA_dbl⟩
  -- (4) value bound: qD(c') ≤ 0, and if < 0 then two distinct roots; so qD(c') = 0
  have hDc' : MvPolynomial.eval (fun k : Fin n => c' * (if k = s then 1 else 0) - v k) qD.1 = 0 := by
    by_contra hn0
    have hle : MvPolynomial.eval (fun k : Fin n => c' * (if k = s then 1 else 0) - v k) qD.1 ≤ 0 := by
      change MvPolynomial.eval (fun k : Fin n => c' * (if k = s then 1 else 0) - v k)
          (pderivExp α (deformElem (n := n) (d := d) i s θ g).1) ≤ 0
      have hbr := restr_deform_line hd2 i s his θ α hαw hαi g v c'
      rw [hbr]
      change MvPolynomial.eval (fun k : Fin n => c' * (if k = s then 1 else 0) - v k) qA.1 +
          (-(θ * v i)) * quadReal qA.hessian (evec s)
            (fun k : Fin n => c' * (if k = s then 1 else 0) - v k) +
          (θ * (α i : ℝ)) * MvPolynomial.eval (fun k : Fin n => c' * (if k = s then 1 else 0) - v k) qC.1 ≤ 0
      have hCdrv : quadReal qC.hessian (evec i) (fun k : Fin n => c' * (if k = s then 1 else 0) - v k) = 0 := by
        rw [← restr_deriv_comm hd2 i s α hαw hαi his g v c']
        exact hA_dbl.2
      have hCle : MvPolynomial.eval (fun k : Fin n => c' * (if k = s then 1 else 0) - v k) qC.1 ≤ 0 := by
        exact stable_pos_quad_line_vertex_sign hn i s qC hC_SP v c' hCdrv
      have hpos : 0 ≤ θ * (α i : ℝ) := by positivity
      have hprod : (θ * (α i : ℝ)) * MvPolynomial.eval
          (fun k : Fin n => c' * (if k = s then 1 else 0) - v k) qC.1 ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos hpos hCle
      have hterm2 : (-(θ * v i)) * quadReal qA.hessian (evec s)
          (fun k : Fin n => c' * (if k = s then 1 else 0) - v k) = 0 := by
        rw [hA_dbl.2]
        ring
      nlinarith [hA_dbl.1, hterm2, hprod]
    have hlt : MvPolynomial.eval (fun k : Fin n => c' * (if k = s then 1 else 0) - v k) qD.1 < 0 :=
      lt_of_le_of_ne hle hn0
    exact hnotD (posQuad_neg_value_two_roots s qD hD_SP.2 v hlt)
  -- (5) c = c'
  have hc_eq : c = c' := by
    by_contra hcc
    apply hnotD
    refine ⟨c, c', hcc, ?_, ?_⟩
    · change MvPolynomial.eval (fun k : Fin n => c * (if k = s then 1 else 0) - v k)
          (pderivExp α (deformElem (n := n) (d := d) i s θ g).1) = 0
      exact hcD.1
    · exact hDc'
  subst c'
  exact hA_dbl

open Commons.Combinatorics.MvPolynomial

/-- the linear map `p ↦ Xᵢ·∂ₛ p`. -/
noncomputable def defL {n : ℕ} (i s : Fin n) : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ :=
  (LinearMap.mulLeft ℝ (X i)).comp (MvPolynomial.pderiv s).toLinearMap

/-- `∂ₛ (Xᵢʲ·w) = Xᵢʲ·∂ₛ w` for `i ≠ s`. -/
lemma pderiv_s_mul_X_pow {n : ℕ} (i s : Fin n) (his : i ≠ s) (j : ℕ)
    (w : MvPolynomial (Fin n) ℝ) :
    pderiv s (X i ^ j * w) = X i ^ j * pderiv s w := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc
        pderiv s (X i ^ (j + 1) * w) = pderiv s (X i * (X i ^ j * w)) := by
            rw [pow_succ']
            rw [mul_assoc]
        _ = X i * pderiv s (X i ^ j * w) := by
            rw [MvPolynomial.pderiv_mul]
            rw [MvPolynomial.pderiv_X_of_ne (i := s) (j := i) his]
            simp
        _ = X i ^ (j + 1) * pderiv s w := by
            rw [ih]
            rw [pow_succ']
            ring

/-- natural scalar equals the coerced real scalar on a real module. -/
lemma nsmul_eq_smul_real' {M : Type*} [AddCommMonoid M] [Module ℝ M] (c : ℕ) (x : M) :
    c • x = (c : ℝ) • x := by
  induction c with
  | zero => simp
  | succ c ih =>
      calc
        (c + 1) • x = c • x + x := succ_nsmul x c
        _ = ((c : ℝ) + 1) • x := by
              rw [add_smul, one_smul]
              rw [← ih]
        _ = ((c + 1 : ℕ) : ℝ) • x := by
              rw [Nat.cast_add]
              simp

/-- `(polyDef)` iterate equals the End power of `1 + θ·L`. -/
lemma polyIter_eq_pow {n : ℕ} (i s : Fin n) (θ : ℝ) (k : ℕ)
    (p : MvPolynomial (Fin n) ℝ) :
    polyIter i s θ k p =
      (((1 : Module.End ℝ (MvPolynomial (Fin n) ℝ)) + θ • defL i s) ^ k) p := by
  let L : Module.End ℝ (MvPolynomial (Fin n) ℝ) :=
    (1 : Module.End ℝ (MvPolynomial (Fin n) ℝ)) + θ • defL i s
  have hfun : ∀ q : MvPolynomial (Fin n) ℝ, polyDef i s θ q = L q := by
    intro q
    have hL : L q = q + θ • (X i * pderiv s q) := by
      dsimp [L]
      simp [defL]
    rw [hL]
    dsimp [polyDef]
    rw [mul_assoc, C_mul_eq_smul θ (X i * pderiv s q)]
  induction k with
  | zero => simp [polyIter]
  | succ k ih =>
      rw [show polyIter i s θ (k + 1) p = polyDef i s θ (polyIter i s θ k p) by rfl]
      rw [ih, hfun]
      rw [pow_succ']
      rfl

/-- `L^j p = Xᵢʲ · ∂ₛʲ p` for `i ≠ s` (End power). -/
lemma defL_pow {n : ℕ} (i s : Fin n) (his : i ≠ s) (j : ℕ)
    (p : MvPolynomial (Fin n) ℝ) :
    (((defL i s) ^ j : Module.End ℝ (MvPolynomial (Fin n) ℝ)) p) =
      X i ^ j * pderivExp (Finsupp.single s j) p := by
  induction j with
  | zero => simp [pderivExp_zero]
  | succ j ih =>
      rw [pow_succ']
      change (defL i s) ((((defL i s) ^ j : Module.End ℝ (MvPolynomial (Fin n) ℝ)) p)) =
        X i ^ (j + 1) * pderivExp (Finsupp.single s (j + 1)) p
      rw [ih]
      have hp2 : pderiv s (pderivExp (Finsupp.single s j) p) = pderivExp (Finsupp.single s (j + 1)) p := by
        have hc := pderivExp_single_comm s 1 (Finsupp.single s j) p
        rw [pderivExp_single s (pderivExp (Finsupp.single s j) p)] at hc
        rw [pderivExp_single s p] at hc
        rw [← pderivExp_single_succ s j p] at hc
        exact hc
      change X i * pderiv s (X i ^ j * pderivExp (Finsupp.single s j) p) =
        X i ^ (j + 1) * pderivExp (Finsupp.single s (j + 1)) p
      rw [pderiv_s_mul_X_pow i s his j (pderivExp (Finsupp.single s j) p)]
      rw [hp2]
      rw [pow_succ']
      ring

/-- power of a scalar-scaled endomorphism applied to `p`. -/
lemma smul_end_pow {n : ℕ} (L : Module.End ℝ (MvPolynomial (Fin n) ℝ)) (θ : ℝ) (j : ℕ)
    (p : MvPolynomial (Fin n) ℝ) :
    (((θ • L) ^ j : Module.End ℝ (MvPolynomial (Fin n) ℝ)) p) = θ ^ j • ((L ^ j) p) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ']
      rw [show (((θ • L) * (θ • L) ^ j : Module.End ℝ (MvPolynomial (Fin n) ℝ)) p) =
          (θ • L) ((((θ • L) ^ j : Module.End ℝ (MvPolynomial (Fin n) ℝ)) p)) by rfl]
      rw [ih]
      have hpow : (((L ^ (j + 1) : Module.End ℝ (MvPolynomial (Fin n) ℝ)) p)) =
          L ((((L ^ j : Module.End ℝ (MvPolynomial (Fin n) ℝ)) p))) := by
        rw [pow_succ']
        rfl
      rw [hpow]
      rw [map_smul]
      simp [pow_succ, pow_succ', smul_smul]

/-- sum of endomorphisms applied at a point. -/
lemma End_sum_apply {n : ℕ} (s : Finset ℕ) (f : ℕ → Module.End ℝ (MvPolynomial (Fin n) ℝ))
    (p : MvPolynomial (Fin n) ℝ) :
    ((∑ m ∈ s, f m) p) = ∑ m ∈ s, ((f m) p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [LinearMap.add_apply, ih]

/-- scalar-multiple of the identity applied after `φ` equals scalar times `φ`. -/
lemma End_mul_smul_one_apply {n : ℕ} (φ : Module.End ℝ (MvPolynomial (Fin n) ℝ)) (r : ℝ)
    (p : MvPolynomial (Fin n) ℝ) :
    ((φ * (r • (1 : Module.End ℝ (MvPolynomial (Fin n) ℝ)))) p) = r • (φ p) := by
  have h1 : r • (1 : Module.End ℝ (MvPolynomial (Fin n) ℝ)) =
      algebraMap ℝ (Module.End ℝ (MvPolynomial (Fin n) ℝ)) r := by
    rw [Algebra.smul_def, mul_one]
  rw [h1]
  have h2 : φ * algebraMap ℝ (Module.End ℝ (MvPolynomial (Fin n) ℝ)) r =
      r • φ := by
    have hc : φ * algebraMap ℝ (Module.End ℝ (MvPolynomial (Fin n) ℝ)) r =
        algebraMap ℝ (Module.End ℝ (MvPolynomial (Fin n) ℝ)) r * φ :=
      (Algebra.commutes r φ).symm
    rw [hc]
    have h3 : algebraMap ℝ (Module.End ℝ (MvPolynomial (Fin n) ℝ)) r * φ = r • φ := by
      rw [← h1]
      rw [smul_mul_assoc]
      simp
    exact h3
  rw [h2]
  simp

/-- binomial expansion of the iterated deformation (polynomial level). -/
lemma polyIter_binom {n : ℕ} (i s : Fin n) (his : i ≠ s) (θ : ℝ) (k : ℕ)
    (p : MvPolynomial (Fin n) ℝ) :
    polyIter i s θ k p =
      ∑ j ∈ Finset.range (k + 1),
        ((((Nat.choose k j : ℕ) : ℝ) * θ ^ j) •
          (X i ^ j * pderivExp (Finsupp.single s j) p)) := by
  classical
  have hcomm : (1 : Module.End ℝ (MvPolynomial (Fin n) ℝ)) + θ • defL i s =
      θ • defL i s + (1 : Module.End ℝ (MvPolynomial (Fin n) ℝ)) := by
    rw [add_comm]
  rw [polyIter_eq_pow]
  rw [hcomm]
  have hb := Commute.add_pow (Commute.one_right (θ • defL i s)) k
  rw [hb]
  rw [End_sum_apply]
  apply Finset.sum_congr rfl
  intro m hm
  have h1 : ((1 : Module.End ℝ (MvPolynomial (Fin n) ℝ)) ^ (k - m)) = 1 := by simp
  have hterm : (((θ • defL i s) ^ m * (1 : Module.End ℝ (MvPolynomial (Fin n) ℝ)) ^ (k - m) *
        ↑(Nat.choose k m : Module.End ℝ (MvPolynomial (Fin n) ℝ))) p) =
      (((Nat.choose k m : ℕ) : ℝ) * θ ^ m) •
        (X i ^ m * pderivExp (Finsupp.single s m) p) := by
    rw [h1]
    have hnat : ((Nat.choose k m : Module.End ℝ (MvPolynomial (Fin n) ℝ))) =
        (Nat.choose k m : ℕ) • (1 : Module.End ℝ (MvPolynomial (Fin n) ℝ)) := by simp
    rw [hnat, nsmul_eq_smul_real' (Nat.choose k m) (1 : Module.End ℝ (MvPolynomial (Fin n) ℝ))]
    have happ := End_mul_smul_one_apply
      (((θ • defL i s) ^ m * (1 : Module.End ℝ (MvPolynomial (Fin n) ℝ))))
      ((Nat.choose k m : ℕ) : ℝ) p
    rw [happ]
    simp
    rw [smul_end_pow (defL i s) θ m p]
    rw [defL_pow i s his m p]
    rw [smul_smul]
  rw [hterm]

open Commons.Combinatorics.MvPolynomial

/-- `∂^α` of zero is zero. -/
lemma pderivExp_zero_poly {n : ℕ} (α : Fin n →₀ ℕ) :
    pderivExp α (0 : MvPolynomial (Fin n) ℝ) = 0 := by
  have h := pderivExp_smul α (0 : ℝ) (0 : MvPolynomial (Fin n) ℝ)
  simpa using h

/-- `∂^α` over a finite sum. -/
lemma pderivExp_sum {n : ℕ} (α : Fin n →₀ ℕ) (s : Finset ℕ)
    (f : ℕ → MvPolynomial (Fin n) ℝ) :
    pderivExp α (∑ j ∈ s, f j) = ∑ j ∈ s, pderivExp α (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pderivExp_zero_poly]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [pderivExp_add_poly, ih]

/-- `∂^α` commutes with real scalars. -/
lemma pderivExp_smul' {n : ℕ} (α : Fin n →₀ ℕ) (c : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    pderivExp α (c • p) = c • pderivExp α p :=
  pderivExp_smul α c p

/-- `∂^α` over a scalar-weighted finite sum. -/
lemma pderivExp_weighted_sum {n : ℕ} (α : Fin n →₀ ℕ) (s : Finset ℕ)
    (c : ℕ → ℝ) (f : ℕ → MvPolynomial (Fin n) ℝ) :
    pderivExp α (∑ j ∈ s, c j • f j) = ∑ j ∈ s, c j • pderivExp α (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pderivExp_zero_poly]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [pderivExp_add_poly, pderivExp_smul', ih]

/-- eval of a scalar-weighted finite sum. -/
lemma eval_weighted_sum {n : ℕ} (w : Fin n → ℝ) (s : Finset ℕ)
    (c : ℕ → ℝ) (f : ℕ → MvPolynomial (Fin n) ℝ) :
    MvPolynomial.eval w (∑ j ∈ s, c j • f j) = ∑ j ∈ s, c j * MvPolynomial.eval w (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [MvPolynomial.eval_add]
      rw [show MvPolynomial.eval w (c a • f a) = c a * MvPolynomial.eval w (f a) by
        rw [← C_mul_eq_smul (c a) (f a)]
        rw [MvPolynomial.eval_mul, MvPolynomial.eval_C]]
      rw [ih]

/-- `m • single a 1 = single a m`. -/
lemma nat_smul_single {n : ℕ} (a : Fin n) (m : ℕ) :
    m • Finsupp.single a 1 = Finsupp.single a m := by
  ext x
  by_cases hx : x = a
  · subst x
    simp
  · simp [hx]

/-- triangular binomial inversion: if all binomial transforms vanish then all `t` vanish. -/
lemma binom_triangular {d : ℕ} (θ : ℝ) (hθ : θ ≠ 0) (t : ℕ → ℝ)
    (h : ∀ k ≤ d, ∑ j ∈ Finset.range (k + 1), ((Nat.choose k j : ℝ) * θ ^ j) * t j = 0) :
    ∀ j ≤ d, t j = 0 := by
  classical
  let P : ℕ → Prop := fun m => m ≤ d → t m = 0
  have hP : ∀ m, P m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro hm
        by_cases hm0 : m = 0
        · subst m
          have h0 := h 0 (by omega)
          simpa using h0
        · have hk := h m hm
          have hsum0 : (∑ i ∈ Finset.range m, ((Nat.choose m i : ℝ) * θ ^ i) * t i) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have hi_lt : i < m := Finset.mem_range.mp hi
            have hti : t i = 0 := ih i (by omega) (by omega)
            simp [hti]
          have hsplit : (∑ i ∈ Finset.range m, ((Nat.choose m i : ℝ) * θ ^ i) * t i) +
              ((Nat.choose m m : ℝ) * θ ^ m) * t m = 0 := by
            simpa [Finset.sum_range_succ] using hk
          have hlast : ((Nat.choose m m : ℝ) * θ ^ m) * t m = 0 := by
            linarith
          have hchoose : (Nat.choose m m : ℝ) = 1 := by simp
          have hθpow : θ ^ m ≠ 0 := pow_ne_zero m hθ
          rw [hchoose, one_mul] at hlast
          have hθt : θ ^ m * t m = 0 := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hlast
          exact (mul_eq_zero.mp hθt).resolve_left hθpow
  intro j hj
  exact hP j hj

/-- value expansion: `∂^α(polyIter) evaluated` equals the binomial combination of terms. -/
lemma polyIter_eval_expand {n : ℕ} (i s : Fin n) (his : i ≠ s) (θ : ℝ)
    (α : Fin n →₀ ℕ) (k : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (v : Fin n → ℝ) (x : ℝ) :
    MvPolynomial.eval (fun k : Fin n => x * (if k = s then 1 else 0) - v k)
        (pderivExp α (polyIter i s θ k p)) =
      ∑ j ∈ Finset.range (k + 1),
        (((Nat.choose k j : ℕ) : ℝ) * θ ^ j) *
          MvPolynomial.eval (fun k : Fin n => x * (if k = s then 1 else 0) - v k)
            (pderivExp α (X i ^ j * pderivExp (Finsupp.single s j) p)) := by
  classical
  rw [polyIter_binom i s his θ k p]
  rw [pderivExp_weighted_sum α (Finset.range (k + 1))
      (fun j => ((Nat.choose k j : ℕ) : ℝ) * θ ^ j)
      (fun j => X i ^ j * pderivExp (Finsupp.single s j) p)]
  rw [eval_weighted_sum (fun k : Fin n => x * (if k = s then 1 else 0) - v k)
      (Finset.range (k + 1))
      (fun j => ((Nat.choose k j : ℕ) : ℝ) * θ ^ j)
      (fun j => pderivExp α (X i ^ j * pderivExp (Finsupp.single s j) p))]

/-- Claim (II) when `αᵢ > 0` (via claim (III) propagation and the triangular system). -/
lemma nuij_claimII_alpha_pos {n : ℕ} (hn : 0 < n) (d : ℕ) (hd : 3 ≤ d)
    (i s : Fin n) (his : i ≠ s) (θ : ℝ) (hθ : 0 < θ)
    (f : H n d) (hfL : f ∈ L n d) (hfP : f ∈ P n d)
    (α : Fin n →₀ ℕ) (hαw : Finsupp.weight (1 : Fin n → ℕ) α = d - 2) (hαi : 0 < α i)
    (v : Fin n → ℝ) (hvi : v i ≠ 0) :
    twoRootsOf (quadOf (by omega : 2 ≤ d) α hαw (nuij_power i s d θ f)) s v := by
  classical
  have hd2 : 2 ≤ d := by omega
  have hθ0 : θ ≠ 0 := ne_of_gt hθ
  let R : ℕ → H n 2 := fun k => quadOf hd2 α hαw (iterDef i s θ k f)
  have hSPk : ∀ k : ℕ, R k ∈ S n 2 ∩ P n 2 := by
    intro k
    dsimp [R]
    have hik : iterDef i s θ k f ∈ L n d ∩ P n d := by
      constructor
      · exact iterDef_mem_L hn i s θ (le_of_lt hθ) k f hfL
      · exact iterDef_mem_P i s θ (le_of_lt hθ) k f hfP
    exact quadOf_mem_SP hd2 α hαw (iterDef i s θ k f) hik
  by_contra hnot
  have hnotR : ¬ twoRootsOf (R d) s v := by
    dsimp [R]
    have heq := iterDef_eq_nuij_power (n := n) (d := d) i s θ f
    convert hnot using 1
    rw [heq]
  rcases stable_pos_quad_mult_zero hn s (R d) (hSPk d) v hnotR with ⟨c, hcdbl⟩
  have hprop : ∀ k : ℕ, k < d →
      isDoubleRoot (R (k + 1)) s v c → isDoubleRoot (R k) s v c := by
    intro k hk hdbl
    have hik : iterDef i s θ k f ∈ L n d := iterDef_mem_L hn i s θ (le_of_lt hθ) k f hfL
    have hikP : iterDef i s θ k f ∈ P n d := iterDef_mem_P i s θ (le_of_lt hθ) k f hfP
    have hD : isDoubleRoot (quadOf hd2 α hαw
        (deformElem (n := n) (d := d) i s θ (iterDef i s θ k f))) s v c := by
      rw [← iterDef_succ i s θ k f]
      exact hdbl
    have hout := nuij_claimIII hn d hd i s his θ hθ (iterDef i s θ k f) hik hikP
        α hαw hαi v c hD
    dsimp [R] at hout ⊢
    exact hout
  have hdblk : ∀ k : ℕ, k ≤ d → isDoubleRoot (R k) s v c := by
    have hgo : ∀ m k : ℕ, k ≤ d → m = d - k → isDoubleRoot (R k) s v c := by
      intro m
      induction m with
      | zero =>
          intro k hk hm
          have hkeq : k = d := by omega
          subst k
          exact hcdbl
      | succ m ih =>
          intro k hk hm
          have hklt : k < d := by omega
          have hm' : m = d - (k + 1) := by omega
          have hnext := ih (k + 1) (by omega) hm'
          exact hprop k hklt hnext
    intro k hk
    exact hgo (d - k) k hk rfl
  have hzR : ∀ k : ℕ, k ≤ d →
      MvPolynomial.eval (fun x : Fin n => c * (if x = s then 1 else 0) - v x)
        (pderivExp α (polyIter i s θ k f.1)) = 0 := by
    intro k hk
    have hdbl := hdblk k hk
    dsimp [R] at hdbl
    have hval0 : MvPolynomial.eval (fun x : Fin n => c * (if x = s then 1 else 0) - v x)
        (quadOf hd2 α hαw (iterDef i s θ k f)).1 = 0 := hdbl.1
    change MvPolynomial.eval (fun x : Fin n => c * (if x = s then 1 else 0) - v x)
        (pderivExp α (iterDef i s θ k f).1) = 0 at hval0
    rw [iterDef_val] at hval0
    exact hval0
  let t : ℕ → ℝ := fun j => MvPolynomial.eval (fun x : Fin n => c * (if x = s then 1 else 0) - v x)
      (pderivExp α (X i ^ j * pderivExp (Finsupp.single s j) f.1))
  have htri : ∀ k : ℕ, k ≤ d →
      (∑ j ∈ Finset.range (k + 1), ((Nat.choose k j : ℝ) * θ ^ j) * t j) = 0 := by
    intro k hk
    have h1 := hzR k hk
    have h2 := polyIter_eval_expand i s his θ α k f.1 v c
    dsimp [t] at h2 ⊢
    rw [← h2]
    exact h1
  have ht0 : ∀ j : ℕ, j ≤ d → t j = 0 := binom_triangular θ hθ0 t htri
  let j0 : ℕ := α i + 2
  have hj0le : j0 ≤ d := by
    dsimp [j0]
    have hαile : α i ≤ Finsupp.weight (1 : Fin n → ℕ) α := by
      rw [Finsupp.weight_eq_sum]
      simpa using (Finset.single_le_sum (s := Finset.univ) (f := fun x : Fin n => α x)
        (by intro x hx; exact Nat.zero_le (α x)) (Finset.mem_univ i))
    omega
  have htj0 : t j0 = 0 := ht0 j0 hj0le
  rcases claimII_term_value i s his f hfP α (by omega) with ⟨c0, hc0, hval⟩
  have hvalc := hval v c
  have htj0' : t j0 = (v i)^2 * c0 := by
    dsimp [t, j0]
    have hnat : j0 • Finsupp.single s 1 = Finsupp.single s j0 := nat_smul_single s j0
    simpa [j0, hnat] using hvalc
  have hpos : 0 < (v i)^2 * c0 := by
    have hvi2 : 0 < (v i)^2 := sq_pos_of_ne_zero hvi
    positivity
  linarith


/-- the restriction of the deformed quadratic when `αᵢ = 0`: `D(x) = A(x) − θvᵢ·A'(x)`. -/
lemma restr_deform_line_alpha0 {n d : ℕ} (hd : 2 ≤ d) (i s : Fin n) (his : i ≠ s)
    (θ : ℝ) (α : Fin n →₀ ℕ) (hαw : Finsupp.weight (1 : Fin n → ℕ) α = d - 2)
    (hαi0 : α i = 0) (g : H n d) (v : Fin n → ℝ) (x : ℝ) :
    MvPolynomial.eval (fun k : Fin n => x * (if k = s then 1 else 0) - v k)
        (pderivExp α (deformElem (n := n) (d := d) i s θ g).1) =
      MvPolynomial.eval (fun k : Fin n => x * (if k = s then 1 else 0) - v k) (pderivExp α g.1) +
        (-(θ * v i)) * quadReal (quadOf hd α hαw g).hessian (evec s)
          (fun k : Fin n => x * (if k = s then 1 else 0) - v k) := by
  classical
  have hde := deform_expansion i s θ α g
  rw [hde]
  rw [MvPolynomial.eval_add, MvPolynomial.eval_add]
  have hzero : MvPolynomial.eval (fun k : Fin n => x * (if k = s then 1 else 0) - v k)
      (C (θ * (α i : ℝ)) * pderivExp ((α - ne n i) + ne n s) g.1) = 0 := by
    have hc0 : θ * (α i : ℝ) = 0 := by rw [hαi0]; ring
    simp [hc0]
  rw [hzero]
  have hmid : MvPolynomial.eval (fun k : Fin n => x * (if k = s then 1 else 0) - v k)
        ((C θ) * X i * pderivExp (α + ne n s) g.1) =
      (-(θ * v i)) * quadReal (quadOf hd α hαw g).hessian (evec s)
        (fun k : Fin n => x * (if k = s then 1 else 0) - v k) := by
    rw [mul_assoc, MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    have hlin : x * (if i = s then 1 else 0) - v i = -(v i) := by
      by_cases his2 : i = s
      · exact False.elim (his his2)
      · simp [his2]
    rw [hlin]
    rw [pderivExp_single_add_deriv α s g.1]
    have hqA1 : (quadOf hd α hαw g).1 = pderivExp α g.1 := rfl
    rw [← hqA1]
    rw [eval_pderiv_quad (quadOf hd α hαw g) s (fun k : Fin n => x * (if k = s then 1 else 0) - v k)]
    ring
  rw [hmid]
  ring

/-- Claim (II) when `αᵢ = 0` (discriminant argument through the last deformation step). -/
lemma nuij_claimII_alpha_zero {n : ℕ} (hn : 0 < n) (d : ℕ) (hd : 3 ≤ d)
    (i s : Fin n) (his : i ≠ s) (θ : ℝ) (hθ : 0 < θ)
    (f : H n d) (hfL : f ∈ L n d) (hfP : f ∈ P n d)
    (α : Fin n →₀ ℕ) (hαw : Finsupp.weight (1 : Fin n → ℕ) α = d - 2) (hαi0 : α i = 0)
    (v : Fin n → ℝ) (hvi : v i ≠ 0) :
    twoRootsOf (quadOf (by omega : 2 ≤ d) α hαw (nuij_power i s d θ f)) s v := by
  classical
  have hd2 : 2 ≤ d := by omega
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d = k + 1 := by
    refine ⟨d - 1, ?_⟩
    omega
  subst d
  -- now d = k+1, k ≥ 2
  have hkge : 2 ≤ k := by omega
  -- iterDef chain: level k and k+1
  let g0 : H n (k + 1) := iterDef i s θ k f
  have hg0L : g0 ∈ L n (k + 1) := by
    dsimp [g0]
    exact iterDef_mem_L hn i s θ (le_of_lt hθ) k f hfL
  have hg0P : g0 ∈ P n (k + 1) := by
    dsimp [g0]
    exact iterDef_mem_P i s θ (le_of_lt hθ) k f hfP
  let qA : H n 2 := quadOf hd2 α hαw g0
  let qD : H n 2 := quadOf hd2 α hαw (iterDef i s θ (k + 1) f)
  have hg0SP : g0 ∈ L n (k + 1) ∩ P n (k + 1) := ⟨hg0L, hg0P⟩
  have hA_SP : qA ∈ S n 2 ∩ P n 2 := by
    dsimp [qA]
    exact quadOf_mem_SP hd2 α hαw g0 hg0SP
  -- qD = quadOf (deformElem g0) α
  have hqD : qD = quadOf hd2 α hαw (deformElem (n := n) (d := k + 1) i s θ g0) := by
    dsimp [qD, g0]
    rw [iterDef_succ i s θ k f]
  -- statement qD's twoRoots: rewrite the target into qD
  have hgoal : twoRootsOf qD s v := by
    let Qss : ℝ := quadReal qA.hessian (evec s) (evec s)
    let Qsv : ℝ := quadReal qA.hessian (evec s) v
    let Qvv : ℝ := quadReal qA.hessian v v
    let A : ℝ := (1 / 2 : ℝ) * Qss
    let B : ℝ := -(Qsv + θ * v i * Qss)
    let C : ℝ := (1 / 2 : ℝ) * Qvv + θ * v i * Qsv
    have hQss : 0 < Qss := by
      dsimp [Qss]
      have hpos : ∀ i j : Fin n, 0 < qA.hessian i j := (mem_P_iff_hessian_pos n qA).mp hA_SP.2
      have : quadReal qA.hessian (evec s) (evec s) = qA.hessian s s := by simp [quadReal, evec]
      rw [this]
      exact hpos s s
    have hqA0 : qA.1 ≠ 0 := stable_pos_quad_ne_zero hn qA hA_SP.2
    have hcard := stable_quad_hessian_card_le_one qA hA_SP.1 hqA0
    have hdiscA : Qsv ^ 2 ≥ Qss * Qvv := by
      dsimp [Qsv, Qss, Qvv]
      exact quad_line_discr_nonneg qA s hA_SP.2 hcard v
    have hdiscD : B ^ 2 > 4 * A * C := by
      dsimp [A, B, C]
      have hmain : Qsv ^ 2 - Qss * Qvv + (θ * v i) ^ 2 * Qss ^ 2 > 0 := by
        have hθv : θ * v i ≠ 0 := mul_ne_zero (ne_of_gt hθ) hvi
        have hq : (θ * v i) ^ 2 > 0 := sq_pos_of_ne_zero hθv
        have hqsssq : 0 < Qss ^ 2 := sq_pos_of_ne_zero (ne_of_gt hQss)
        have hpos2 : 0 < (θ * v i) ^ 2 * Qss ^ 2 := by positivity
        nlinarith [hdiscA, hpos2]
      nlinarith
    have hqD1 : qD.1 = pderivExp α (deformElem (n := n) (d := k + 1) i s θ g0).1 := by
      rw [hqD]
      rfl
    have hAvalQ : ∀ x : ℝ, MvPolynomial.eval (fun k : Fin n => x * (if k = s then 1 else 0) - v k) qA.1 =
        (1 / 2 : ℝ) * (Qss * x ^ 2 - 2 * Qsv * x + Qvv) := by
      intro x
      have hAval := quad_line_value_eq qA s v x
      dsimp [Qss, Qsv, Qvv] at hAval ⊢
      exact hAval
    have hAdrvQ : ∀ x : ℝ, quadReal qA.hessian (evec s)
        (fun k : Fin n => x * (if k = s then 1 else 0) - v k) = x * Qss - Qsv := by
      intro x
      have hAdrv := quadReal_evec_line qA.hessian (by simpa using hessian_symm n qA) s v x
      dsimp [Qss, Qsv] at hAdrv ⊢
      exact hAdrv
    have hvalD : ∀ x : ℝ, MvPolynomial.eval (fun k : Fin n => x * (if k = s then 1 else 0) - v k) qD.1 =
        A * x ^ 2 + B * x + C := by
      intro x
      have hbr := restr_deform_line_alpha0 hd2 i s his θ α hαw hαi0 g0 v x
      rw [hqD1]
      rw [hbr]
      change MvPolynomial.eval (fun k : Fin n => x * (if k = s then 1 else 0) - v k) (pderivExp α g0.1) +
        (-(θ * v i)) * quadReal qA.hessian (evec s)
          (fun k : Fin n => x * (if k = s then 1 else 0) - v k) = A * x ^ 2 + B * x + C
      have hqA1 : qA.1 = pderivExp α g0.1 := rfl
      rw [← hqA1]
      rw [hAvalQ x, hAdrvQ x]
      dsimp [A, B, C]
      ring
    rcases two_roots_of_discr_gt A B C (by positivity) hdiscD with ⟨r₁, r₂, hne, hr₁, hr₂⟩
    refine ⟨r₁, r₂, hne, ?_, ?_⟩
    · have h1 := hvalD r₁
      change MvPolynomial.eval (fun k : Fin n => r₁ * (if k = s then 1 else 0) - v k) qD.1 = 0
      rw [h1]
      exact hr₁
    · have h2 := hvalD r₂
      change MvPolynomial.eval (fun k : Fin n => r₂ * (if k = s then 1 else 0) - v k) qD.1 = 0
      rw [h2]
      exact hr₂
  -- convert hgoal (twoRootsOf qD) to statement about nuij_power
  have heq : qD = quadOf hd2 α hαw (nuij_power i s (k + 1) θ f) := by
    dsimp [qD]
    congr 1
    exact iterDef_eq_nuij_power (n := n) (d := k + 1) i s θ f
  rwa [heq] at hgoal

open Commons.Combinatorics.MvPolynomial

/-- `(1+θXᵢ∂ₛ)^d` preserves `L n d`. -/
lemma nuij_power_mem_L {n d : ℕ} (hn : 0 < n) (i s : Fin n) (θ : ℝ) (hθ : 0 ≤ θ)
    (f : H n d) (hf : f ∈ L n d) : (nuij_power i s d θ) f ∈ L n d := by
  have h1 := iterDef_mem_L hn i s θ hθ d f hf
  rwa [iterDef_eq_nuij_power (n := n) i s θ f] at h1

/-- `(1+θXᵢ∂ₛ)^d` preserves `P n d`. -/
lemma nuij_power_mem_P' {n d : ℕ} (i s : Fin n) (θ : ℝ) (hθ : 0 ≤ θ)
    (f : H n d) (hf : f ∈ P n d) : (nuij_power i s d θ) f ∈ P n d :=
  nuij_power_mem_P i s d θ hθ f hf

/-- two single-coordinate deformations commute on polynomials (`i,j,s` pairwise-distinct
in the appropriate sense). -/
lemma polyDef_comm {n : ℕ} (i j s : Fin n) (his : i ≠ s) (hjs : j ≠ s) (hij : i ≠ j)
    (θ : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    polyDef i s θ (polyDef j s θ p) = polyDef j s θ (polyDef i s θ p) := by
  have hC0 : pderiv s (C θ) = 0 := by
    exact pderiv_of_homogeneous_zero s (C θ) (MvPolynomial.isHomogeneous_C (Fin n) θ)
  have hsl : ∀ w : MvPolynomial (Fin n) ℝ, pderiv s (C θ * w) = C θ * pderiv s w := by
    intro w
    rw [MvPolynomial.pderiv_mul]
    rw [hC0]
    simp
  have hXj : pderiv s (X j * pderiv s p) = X j * pderiv s (pderiv s p) := by
    rw [MvPolynomial.pderiv_mul]
    rw [MvPolynomial.pderiv_X_of_ne (i := s) (j := j) hjs]
    simp
  have hXi : pderiv s (X i * pderiv s p) = X i * pderiv s (pderiv s p) := by
    rw [MvPolynomial.pderiv_mul]
    rw [MvPolynomial.pderiv_X_of_ne (i := s) (j := i) his]
    simp
  calc
    polyDef i s θ (polyDef j s θ p)
        = (polyDef j s θ p) + (C θ) * X i * pderiv s (polyDef j s θ p) := rfl
    _ = p + (C θ) * X j * pderiv s p + (C θ) * X i * pderiv s p +
          (C θ) * (C θ * X i * X j * pderiv s (pderiv s p)) := by
            dsimp [polyDef]
            rw [show (C θ) * X j * pderiv s p = (C θ) * (X j * pderiv s p) by rw [mul_assoc]]
            rw [Derivation.map_add]
            -- pderiv s ((C θ) * (X j * pderiv s p)) = Cθ * (Xj ∂²p)
            have hterm : pderiv s ((C θ) * (X j * pderiv s p)) =
                (C θ) * (X j * pderiv s (pderiv s p)) := by
              rw [hsl (X j * pderiv s p)]
              rw [hXj]
            rw [hterm]
            rw [mul_assoc]
            ring
    _ = p + (C θ) * X i * pderiv s p + (C θ) * X j * pderiv s p +
          (C θ) * (C θ * X j * X i * pderiv s (pderiv s p)) := by
            ring
    _ = polyDef j s θ (polyDef i s θ p) := by
            dsimp [polyDef]
            rw [show (C θ) * X i * pderiv s p = (C θ) * (X i * pderiv s p) by rw [mul_assoc]]
            rw [Derivation.map_add]
            have hterm : pderiv s ((C θ) * (X i * pderiv s p)) =
                (C θ) * (X i * pderiv s (pderiv s p)) := by
              rw [hsl (X i * pderiv s p)]
              rw [hXi]
            rw [hterm]
            rw [mul_assoc]
            ring

/-- function-level commutation of single-coordinate deformations. -/
lemma polyDef_comm' {n : ℕ} (i j s : Fin n) (his : i ≠ s) (hjs : j ≠ s) (hij : i ≠ j)
    (θ : ℝ) : (polyDef i s θ) ∘ (polyDef j s θ) = (polyDef j s θ) ∘ (polyDef i s θ) := by
  funext p
  exact polyDef_comm i j s his hjs hij θ p


/-- one deformation commutes with iterates of another (values). -/
lemma polyDef_polyIter_comm {n : ℕ} (i j s : Fin n) (his : i ≠ s) (hjs : j ≠ s) (hij : i ≠ j)
    (θ : ℝ) (b : ℕ) (q : MvPolynomial (Fin n) ℝ) :
    polyDef i s θ (polyIter j s θ b q) = polyIter j s θ b (polyDef i s θ q) := by
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [show polyIter j s θ (b + 1) q = polyDef j s θ (polyIter j s θ b q) by rfl]
      rw [polyDef_comm i j s his hjs hij θ (polyIter j s θ b q)]
      rw [ih]
      rfl

/-- full iterates of two commuting single deformations commute (values). -/
lemma polyIter_comm {n : ℕ} (i j s : Fin n) (his : i ≠ s) (hjs : j ≠ s) (hij : i ≠ j)
    (θ : ℝ) (a b : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    polyIter i s θ a (polyIter j s θ b p) = polyIter j s θ b (polyIter i s θ a p) := by
  induction a with
  | zero => rfl
  | succ a ih =>
      rw [show polyIter i s θ (a + 1) (polyIter j s θ b p) =
          polyDef i s θ (polyIter i s θ a (polyIter j s θ b p)) by rfl]
      rw [ih]
      rw [polyDef_polyIter_comm i j s his hjs hij θ b (polyIter i s θ a p)]
      rfl

/-- iterates of the deformation commute on `H n d`. -/
lemma iterDef_comm {n d : ℕ} (i j s : Fin n) (his : i ≠ s) (hjs : j ≠ s) (hij : i ≠ j)
    (θ : ℝ) (a b : ℕ) (f : H n d) :
    iterDef i s θ a (iterDef j s θ b f) = iterDef j s θ b (iterDef i s θ a f) := by
  apply Subtype.ext
  change (iterDef i s θ a (iterDef j s θ b f)).1 = (iterDef j s θ b (iterDef i s θ a f)).1
  rw [iterDef_val, iterDef_val]
  rw [iterDef_val, iterDef_val]
  exact polyIter_comm i j s his hjs hij θ a b f.1

/-- `nuij_power` for different deformation coordinates commute (values). -/
lemma nuij_power_comm_val {n d : ℕ} (i j s : Fin n) (his : i ≠ s) (hjs : j ≠ s) (hij : i ≠ j)
    (θ : ℝ) (f : H n d) :
    (nuij_power i s d θ) ((nuij_power j s d θ) f) =
      (nuij_power j s d θ) ((nuij_power i s d θ) f) := by
  have h1 := iterDef_comm (n := n) (d := d) i j s his hjs hij θ d d f
  rw [iterDef_eq_nuij_power (n := n) i s θ (iterDef j s θ d f)] at h1
  rw [iterDef_eq_nuij_power (n := n) j s θ f] at h1
  rw [iterDef_eq_nuij_power (n := n) j s θ (iterDef i s θ d f)] at h1
  rw [iterDef_eq_nuij_power (n := n) i s θ f] at h1
  exact h1

/-- `nuij_power` for different coordinates commute as functions. -/
lemma nuij_power_comm_fn {n d : ℕ} (i j s : Fin n) (his : i ≠ s) (hjs : j ≠ s) (hij : i ≠ j)
    (θ : ℝ) : (fun x : H n d => (nuij_power i s d θ) x) ∘
        (fun x : H n d => (nuij_power j s d θ) x) =
      (fun x : H n d => (nuij_power j s d θ) x) ∘
        (fun x : H n d => (nuij_power i s d θ) x) := by
  funext x
  exact nuij_power_comm_val (n := n) (d := d) i j s his hjs hij θ x

open Commons.Combinatorics.MvPolynomial

/-- `∂^(eSum l) p = pderivL l p`. -/
lemma pderivExp_eSum_eq_pderivL {n : ℕ} (l : List (Fin n)) (p : MvPolynomial (Fin n) ℝ) :
    pderivExp (Commons.Combinatorics.MvPolynomial.eSum l) p = nuij_pderivL l p := by
  induction l with
  | nil => simp [pderivExp_zero, Commons.Combinatorics.MvPolynomial.eSum, nuij_pderivL]
  | cons a l ih =>
      rw [Commons.Combinatorics.MvPolynomial.eSum_cons]
      rw [pderivExp_add (Commons.Combinatorics.MvPolynomial.e a)
        (Commons.Combinatorics.MvPolynomial.eSum l) p]
      rw [pderivExp_single a (pderivExp (Commons.Combinatorics.MvPolynomial.eSum l) p)]
      rw [ih]
      -- pderiv a (nuij_pderivL l p) = nuij_pderivL l (pderiv a p) via permutation l++[a] ~ [a]++l
      have hp := nuij_pderivL_perm (List.perm_append_comm (l₁ := l) (l₂ := [a])) p
      -- nuij_pderivL (l ++ [a]) p = nuij_pderivL ([a] ++ l) p
      have h1 : nuij_pderivL (l ++ [a]) p = pderiv a (nuij_pderivL l p) := by
        simp [nuij_pderivL]
      calc
        pderiv a (nuij_pderivL l p) = nuij_pderivL (l ++ [a]) p := h1.symm
        _ = nuij_pderivL (a :: l) p := by
              rw [hp]
              rfl

/-- the weight of `eSum l` is `l.length`. -/
lemma weight_eSum {n : ℕ} (l : List (Fin n)) :
    Finsupp.weight (1 : Fin n → ℕ) (Commons.Combinatorics.MvPolynomial.eSum l) = l.length := by
  have hw' := Commons.Combinatorics.MvPolynomial.degN_eSum (σ := Fin n) (l := l)
  change Finsupp.weight (fun x : Fin n => (1 : ℕ)) (Commons.Combinatorics.MvPolynomial.eSum l) = l.length
  simpa [Commons.Combinatorics.MvPolynomial.degN] using hw'

/-- the deformation index list and the last coordinate. -/
def nuij_idx {n : ℕ} (hn2 : 2 ≤ n) : List (Fin n) :=
  (List.finRange (n - 1)).map (fun i : Fin (n - 1) => ⟨i.1, by omega⟩)

def nuij_s {n : ℕ} (hn2 : 2 ≤ n) : Fin n := ⟨n - 1, by omega⟩

/-- `nuij_T` equals the fold over the index list. -/
lemma nuij_T_eq_fold {n d : ℕ} (hn2 : 2 ≤ n) (θ : ℝ) (f : H n d) :
    nuij_T (n := n) (d := d) hn2 θ f =
      (nuij_idx hn2).foldl (fun acc i => (nuij_power i (nuij_s hn2) d θ) acc) f := by
  rfl

/-- indices in `nuij_idx` are distinct. -/
lemma nuij_idx_nodup {n : ℕ} (hn2 : 2 ≤ n) : (nuij_idx hn2).Nodup := by
  classical
  dsimp [nuij_idx]
  exact List.Nodup.map (by
    intro a b h
    apply Fin.ext
    simpa using congrArg Fin.val h) (List.nodup_finRange (n - 1))

/-- the last coordinate is not in the index list. -/
lemma nuij_idx_not_mem_s {n : ℕ} (hn2 : 2 ≤ n) :
    nuij_s hn2 ∉ nuij_idx hn2 := by
  classical
  intro h
  change nuij_s hn2 ∈ (List.finRange (n - 1)).map (fun i : Fin (n - 1) => (⟨i.1, by omega⟩ : Fin n)) at h
  rcases List.mem_map.mp h with ⟨j, hj, hji⟩
  have hval := congrArg Fin.val hji
  have : j.1 < n - 1 := j.2
  dsimp [nuij_s] at hval
  omega

/-- each element of the index list differs from the last coordinate. -/
lemma nuij_idx_ne_s {n : ℕ} (hn2 : 2 ≤ n) : ∀ j ∈ nuij_idx hn2, j ≠ nuij_s hn2 := by
  intro j hj hjneq
  exact nuij_idx_not_mem_s hn2 (by simpa [hjneq] using hj)

/-- an index of `nuij_idx` is an `i` with `i.1 < n - 1`. -/
lemma nuij_idx_mem_iff {n : ℕ} (hn2 : 2 ≤ n) (i : Fin n) :
    i ∈ nuij_idx hn2 ↔ i.1 < n - 1 := by
  classical
  dsimp [nuij_idx]
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨j, hj, hji⟩
    have hval := congrArg Fin.val hji
    simp at hval
    have : j.1 < n - 1 := j.2
    simpa [hval]
  · intro hi
    let j : Fin (n - 1) := ⟨i.1, hi⟩
    have hm : j ∈ List.finRange (n - 1) := List.mem_finRange j
    refine List.mem_map.mpr ⟨j, hm, ?_⟩
    apply Fin.ext
    rfl

/-- remove one index and append it back permutes `nuij_idx`. -/
lemma nuij_idx_erase_perm {n : ℕ} (hn2 : 2 ≤ n) (i : Fin n) (hi : i.1 < n - 1) :
    ((nuij_idx hn2).erase i ++ [i]).Perm (nuij_idx hn2) := by
  have hmem : i ∈ nuij_idx hn2 := (nuij_idx_mem_iff hn2 i).mpr hi
  exact Commons.Data.List.erase_append_perm (nuij_idx hn2) i hmem (nuij_idx_nodup hn2)

/-- folds over permutations of non-`s` index lists agree. -/
lemma idx_fold_perm {n d : ℕ} (hn2 : 2 ≤ n) (θ : ℝ)
    {l₁ l₂ : List (Fin n)} (hp : l₁.Perm l₂)
    (hgood : ∀ a ∈ l₁, a ≠ nuij_s hn2) (f : H n d) :
    l₁.foldl (fun acc i => (nuij_power i (nuij_s hn2) d θ) acc) f =
      l₂.foldl (fun acc i => (nuij_power i (nuij_s hn2) d θ) acc) f := by
  revert hgood f
  induction hp with
  | nil =>
      intro hgood f
      rfl
  | cons x h ih =>
      intro hgood f
      simp only [List.foldl_cons]
      exact ih (by intro a ha; exact hgood a (by simp [ha]))
        ((nuij_power x (nuij_s hn2) d θ) f)
  | swap x y l =>
      intro hgood f
      have hgx : x ≠ nuij_s hn2 := hgood x (by simp)
      have hgy : y ≠ nuij_s hn2 := hgood y (by simp)
      simp only [List.foldl_cons]
      by_cases hxy : x = y
      · subst y
        rfl
      · rw [nuij_power_comm_val (n := n) (d := d) x y (nuij_s hn2) hgx hgy hxy θ]
  | trans h₁ h₂ ih₁ ih₂ =>
      intro hgood f
      exact (ih₁ hgood f).trans (ih₂
        (by intro a ha; exact hgood a ((h₁.symm).subset ha)) f)

/-- `i ≠ s` follows from `i.1 < n - 1`. -/
lemma idx_ne_s {n : ℕ} (hn2 : 2 ≤ n) (i : Fin n) (hi : i.1 < n - 1) : i ≠ nuij_s hn2 := by
  intro h
  have hval := congrArg Fin.val h
  dsimp [nuij_s] at hval
  omega

/-- the fold over `nuij_idx` equals the fold with `i` moved to the end. -/
lemma nuij_T_factor {n d : ℕ} (hn2 : 2 ≤ n) (θ : ℝ) (i : Fin n) (hi : i.1 < n - 1)
    (f : H n d) :
    nuij_T (n := n) (d := d) hn2 θ f =
      (nuij_power i (nuij_s hn2) d θ)
        (((nuij_idx hn2).erase i).foldl
          (fun acc j => (nuij_power j (nuij_s hn2) d θ) acc) f) := by
  classical
  have hperm : (nuij_idx hn2).Perm ((nuij_idx hn2).erase i ++ [i]) :=
    (nuij_idx_erase_perm hn2 i hi).symm
  have hfold : (nuij_idx hn2).foldl (fun acc j => (nuij_power j (nuij_s hn2) d θ) acc) f =
      ((nuij_idx hn2).erase i ++ [i]).foldl
        (fun acc j => (nuij_power j (nuij_s hn2) d θ) acc) f :=
    idx_fold_perm hn2 θ hperm (nuij_idx_ne_s hn2) f
  rw [nuij_T_eq_fold]
  rw [hfold]
  rw [List.foldl_append]
  simp

/-- a fold of `nuij_power` over a list preserves `L ∩ P`. -/
lemma foldl_power_mem_LP {n d : ℕ} (hn : 0 < n) (θ : ℝ) (hθ0 : 0 ≤ θ)
    (l : List (Fin n)) (s : Fin n) (f : H n d) (hf : f ∈ L n d ∩ P n d) :
    l.foldl (fun acc i => (nuij_power i s d θ) acc) f ∈ L n d ∩ P n d := by
  revert f
  induction l with
  | nil => intro g hg; simpa using hg
  | cons a l ih =>
      intro g hg
      have hnew : (nuij_power a s d θ) g ∈ L n d ∩ P n d := by
        constructor
        · exact nuij_power_mem_L hn a s θ hθ0 g hg.1
        · exact nuij_power_mem_P' a s θ hθ0 g hg.2
      simpa [List.foldl_cons] using ih ((nuij_power a s d θ) g) hnew

/-- a coordinate different from the last index has small value. -/
lemma ne_s_val_lt {n : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjs : j ≠ nuij_s hn2) : j.1 < n - 1 := by
  by_contra hlt
  have hge : n - 1 ≤ j.1 := by omega
  have hjt : j.1 < n := j.2
  have hjeq : j.1 = n - 1 := by omega
  apply hjs
  apply Fin.ext
  dsimp [nuij_s]
  exact hjeq

/-- Claim (II): if `v_i ≠ 0`, the deformed `d`-th power has two distinct real zeros. -/
lemma nuij_claimII (n : ℕ) (hn : 0 < n) (d : ℕ) (hd : 3 ≤ d)
    (i s : Fin n) (his : i ≠ s) (θ : ℝ) (hθ : 0 < θ)
    (f : H n d) (hfL : f ∈ L n d) (hfP : f ∈ P n d)
    (α : Fin n →₀ ℕ) (hαw : Finsupp.weight (1 : Fin n → ℕ) α = d - 2)
    (v : Fin n → ℝ) (hvi : v i ≠ 0) :
    twoRootsOf (quadOf (by omega : 2 ≤ d) α hαw (nuij_power i s d θ f)) s v := by
  classical
  by_cases hαi0 : α i = 0
  · exact nuij_claimII_alpha_zero (n := n) hn d hd i s his θ hθ f hfL hfP α hαw hαi0 v hvi
  · have hαi : 0 < α i := Nat.pos_of_ne_zero hαi0
    exact nuij_claimII_alpha_pos (n := n) hn d hd i s his θ hθ f hfL hfP α hαw hαi v hvi

theorem nuij_smoothing (n d : ℕ) (hn2 : 2 ≤ n) (hd : 3 ≤ d) (θ : ℝ) (hθ : 0 < θ)
    (f : H n d) (hf : f ∈ L n d ∩ P n d) :
    nuij_T (n := n) (d := d) hn2 θ f ∈ Ŀ n d := by
  classical
  have hn : 0 < n := by omega
  have hd2 : 2 ≤ d := by omega
  have hθ0 : 0 ≤ θ := le_of_lt hθ
  let s : Fin n := nuij_s hn2
  let T : H n d := nuij_T (n := n) (d := d) hn2 θ f
  have hP : T ∈ P n d := by
    dsimp [T]
    exact nuij_T_mem_P hn2 θ hθ0 f hf.2
  refine strict_mem_of_pderivs hd2 T hP ?_
  intro l hl
  let α : Fin n →₀ ℕ := Commons.Combinatorics.MvPolynomial.eSum l
  have hαw : Finsupp.weight (1 : Fin n → ℕ) α = d - 2 := by
    dsimp [α]
    rw [weight_eSum l, hl]
  have hq : quadOf hd2 α hαw T ∈ Ŀ n 2 := by
    refine strict_of_line_roots n s (quadOf hd2 α hαw T) ?_ ?_
    · exact quadOf_mem_P hd2 α hαw T hP
    · intro v hv
      let j : Fin n := Classical.choose hv
      have hspec := Classical.choose_spec hv
      have hjs : j ≠ s := hspec.1
      have hvj : v j ≠ 0 := hspec.2
      have hi0 : j.1 < n - 1 := ne_s_val_lt hn2 j hjs
      let h0 : H n d := ((nuij_idx hn2).erase j).foldl
        (fun acc i => (nuij_power i (nuij_s hn2) d θ) acc) f
      have hfactor : T = (nuij_power j (nuij_s hn2) d θ) h0 := by
        dsimp [T, h0]
        exact nuij_T_factor hn2 θ j hi0 f
      have h0mem : h0 ∈ L n d ∩ P n d := by
        dsimp [h0]
        exact foldl_power_mem_LP hn θ hθ0 ((nuij_idx hn2).erase j) (nuij_s hn2) f hf
      have htwo := nuij_claimII (n := n) hn d hd j (nuij_s hn2) hjs θ hθ h0 h0mem.1 h0mem.2
        α hαw v hvj
      have htwoT : twoRootsOf (quadOf hd2 α hαw T) s v := by
        dsimp [s]
        convert htwo using 1
        rw [← hfactor]
      exact htwoT
  have heqel : pderivL2 hd2 l hl T = quadOf hd2 α hαw T := by
    apply Subtype.ext
    change nuij_pderivL l T.1 = pderivExp α T.1
    dsimp [α]
    exact (pderivExp_eSum_eq_pderivL l T.1).symm
  rw [heqel]
  exact hq
end Commons.LorentzianPolynomials
