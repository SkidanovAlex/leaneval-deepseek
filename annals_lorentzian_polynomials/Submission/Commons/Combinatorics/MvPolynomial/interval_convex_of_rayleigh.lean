import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Finsupp.Weight

/-!
# Interval convexity of the support of a (list-)Rayleigh polynomial

This file proves that the support of a polynomial with nonnegative coefficients
satisfying a `c`-Rayleigh inequality (for every iterated partial derivative,
every pair of indices, and every nonnegative evaluation point) is *interval
convex*: if `α ≤ γ ≤ β` coordinatewise and `α`, `β` lie in the support, then
so does `γ`.

The argument is the corrected proof of Lemma 2.22 (1) of
Brändén–Huh, "Lorentzian polynomials", Ann. of Math. 192 (2020):
choose a minimal counterexample (by total degree of the polynomial, then by
`|β|`, then by `|γ|`); contractions lower the degree; an evaluation at
`(ε,…,ε)` for small `ε > 0` contradicts the Rayleigh inequality.
-/

open Finsupp MvPolynomial
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Commons.Combinatorics.MvPolynomial

noncomputable section

/-! ## 1. Exponents: unit vectors, total degree -/

/-- the unit exponent vector `e_i` -/
abbrev e {σ : Type*} (i : σ) : σ →₀ ℕ := Finsupp.single i 1

/-- sum of the coordinates of an exponent vector -/
abbrev degN {σ : Type*} (m : σ →₀ ℕ) : ℕ := Finsupp.weight (fun _ : σ => (1 : ℕ)) m

lemma degN_zero {σ : Type*} : degN (0 : σ →₀ ℕ) = 0 := by simp [degN]

lemma degN_add {σ : Type*} (m₁ m₂ : σ →₀ ℕ) : degN (m₁ + m₂) = degN m₁ + degN m₂ := by
  exact map_add (Finsupp.weight (fun _ : σ => (1 : ℕ))) m₁ m₂

lemma degN_single {σ : Type*} (i : σ) (a : ℕ) : degN (Finsupp.single i a) = a := by
  simp [degN, Finsupp.weight_single]

lemma degN_e {σ : Type*} (i : σ) : degN (e i) = 1 := by simp [degN, e, Finsupp.weight_single]

lemma degN_eq_sum {σ : Type*} [Fintype σ] (m : σ →₀ ℕ) : degN m = ∑ i : σ, m i := by
  classical
  rw [degN, Finsupp.weight_eq_sum]
  simp

lemma coord_le_degN {σ : Type*} (m : σ →₀ ℕ) (i : σ) : m i ≤ degN m := by
  exact Finsupp.le_weight (fun _ : σ => (1 : ℕ)) (by simp) m

lemma sub_single_add {σ : Type*} (m : σ →₀ ℕ) (i : σ) (hi : m i ≠ 0) :
    (m - Finsupp.single i 1) + Finsupp.single i 1 = m := by
  classical
  ext k
  by_cases hk : k = i
  · subst k
    simp
    omega
  · simp [hk]

lemma add_sub_single {σ : Type*} (m : σ →₀ ℕ) (i : σ) :
    (m + Finsupp.single i 1) - Finsupp.single i 1 = m := by
  classical
  ext k
  by_cases hk : k = i
  · subst k
    simp
  · simp [hk]

lemma degN_sub_single {σ : Type*} (m : σ →₀ ℕ) (i : σ) (hi : m i ≠ 0) :
    degN (m - Finsupp.single i 1) = degN m - 1 := by
  have h : degN (m - Finsupp.single i 1) + 1 = degN m := by
    calc
      degN (m - Finsupp.single i 1) + 1 = degN ((m - Finsupp.single i 1) + Finsupp.single i 1) := by
        rw [degN_add, degN_single]
      _ = degN m := by rw [sub_single_add m i hi]
  omega

/-! ## 2. Derivatives along lists and their supports -/

lemma pderiv_comm {σ : Type*} (i j : σ) (p : MvPolynomial σ ℝ) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  ext m
  by_cases hij : i = j
  · subst j
    rfl
  · rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv]
    have h1 : (m + e i) j = m j := by simp [e, hij]
    have h2 : (m + e j) i = m i := by
      rw [Finsupp.add_apply]
      have hz : (e j) i = 0 := by
        change (Finsupp.single j (1 : ℕ)) i = 0
        exact Finsupp.single_eq_of_ne hij
      rw [hz, add_zero]
    have h12 : (m + e i) + e j = (m + e j) + e i := by
      rw [add_assoc, add_assoc, add_comm (e i) (e j)]
    rw [h12, h1, h2]
    ring

instance instRightCommPderiv {σ : Type*} :
    RightCommutative (fun (q : MvPolynomial σ ℝ) (i : σ) => pderiv i q) :=
  ⟨fun q a₁ a₂ => pderiv_comm a₂ a₁ q⟩

/-- membership in the support of a single derivative -/
lemma mem_support_pderiv {σ : Type*} (i : σ) (p : MvPolynomial σ ℝ) (m : σ →₀ ℕ) :
    m ∈ (pderiv i p).support ↔ m + e i ∈ p.support := by
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, coeff_pderiv]
  constructor
  · intro h
    by_contra hc
    apply h
    simp [hc]
  · intro h
    exact mul_ne_zero h (by positivity)

/-- support membership after subtracting `e_i` -/
lemma mem_support_pderiv_sub {σ : Type*} (i : σ) (p : MvPolynomial σ ℝ) (m : σ →₀ ℕ)
    (hi : m i ≠ 0) :
    m - e i ∈ (pderiv i p).support ↔ m ∈ p.support := by
  rw [mem_support_pderiv]
  rw [sub_single_add m i hi]

/-- nonnegativity of coefficients is preserved by `pderiv` -/
lemma coeff_pderiv_nonneg {σ : Type*} (i : σ) (p : MvPolynomial σ ℝ)
    (hp : ∀ m : σ →₀ ℕ, 0 ≤ p.coeff m) :
    ∀ m : σ →₀ ℕ, 0 ≤ (pderiv i p).coeff m := by
  intro m
  rw [coeff_pderiv]
  exact mul_nonneg (hp (m + e i)) (by positivity)

/-- iterated partial derivative along a list of variables -/
def pderivL {σ : Type*} (l : List σ) (p : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  l.foldl (fun q i => pderiv i q) p

@[simp] lemma pderivL_nil {σ : Type*} (p : MvPolynomial σ ℝ) : pderivL [] p = p := rfl

lemma pderivL_cons {σ : Type*} (i : σ) (l : List σ) (p : MvPolynomial σ ℝ) :
    pderivL (i :: l) p = pderivL l (pderiv i p) := rfl

lemma pderivL_append {σ : Type*} (l l' : List σ) (p : MvPolynomial σ ℝ) :
    pderivL (l ++ l') p = pderivL l' (pderivL l p) := by
  unfold pderivL
  rw [List.foldl_append]

lemma pderivL_perm {σ : Type*} {l l' : List σ} (hp : l.Perm l') (p : MvPolynomial σ ℝ) :
    pderivL l p = pderivL l' p := by
  simpa [pderivL] using (List.Perm.foldl_eq (f := fun q i => pderiv i q) hp p)

/-- derivative along a list commutes with a single derivative at the front -/
lemma pderivL_cons_append {σ : Type*} (i : σ) (l : List σ) (p : MvPolynomial σ ℝ) :
    pderivL l (pderiv i p) = pderivL (i :: l) p := by
  rw [pderivL_cons]

/-- multiset sum of the unit vectors indexed by a list -/
def eSum {σ : Type*} (l : List σ) : σ →₀ ℕ :=
  (l.map fun i => e i).sum

lemma eSum_cons {σ : Type*} (i : σ) (l : List σ) : eSum (i :: l) = e i + eSum l := by
  simp [eSum]

lemma eSum_nil {σ : Type*} : eSum ([] : List σ) = 0 := by simp [eSum]

lemma eSum_append {σ : Type*} (l₁ l₂ : List σ) : eSum (l₁ ++ l₂) = eSum l₁ + eSum l₂ := by
  simp [eSum, List.sum_append, add_assoc, add_comm, add_left_comm]

lemma degN_eSum {σ : Type*} (l : List σ) : degN (eSum l) = l.length := by
  classical
  induction l with
  | nil => simp [eSum, degN]
  | cons i l ih =>
      rw [eSum_cons, degN_add, degN_e, ih]
      simp
      omega

/-- support of an iterated derivative -/
lemma mem_support_pderivL {σ : Type*} (l : List σ) (p : MvPolynomial σ ℝ) (m : σ →₀ ℕ) :
    m ∈ (pderivL l p).support ↔ m + eSum l ∈ p.support := by
  classical
  revert p m
  induction l with
  | nil =>
      intro p m
      simp [eSum]
  | cons i l ih =>
      intro p m
      rw [pderivL_cons]
      rw [ih (pderiv i p) m]
      rw [mem_support_pderiv]
      rw [eSum_cons]
      constructor
      · intro h
        simpa [add_assoc, add_comm, add_left_comm] using h
      · intro h
        simpa [add_assoc, add_comm, add_left_comm] using h

lemma coeff_pderivL_nonneg {σ : Type*} (l : List σ) (p : MvPolynomial σ ℝ)
    (hp : ∀ m : σ →₀ ℕ, 0 ≤ p.coeff m) : ∀ m : σ →₀ ℕ, 0 ≤ (pderivL l p).coeff m := by
  classical
  revert p hp
  induction l with
  | nil =>
      intro p hp m
      simpa using hp m
  | cons i l ih =>
      intro p hp m
      rw [pderivL_cons]
      exact ih (pderiv i p) (coeff_pderiv_nonneg i p hp) m

/-- evaluation at the zero vector equals the constant coefficient -/
lemma eval_zero_eq_coeff {σ : Type*} (p : MvPolynomial σ ℝ) :
    MvPolynomial.eval (fun _ : σ => (0 : ℝ)) p = p.coeff 0 := by
  change MvPolynomial.eval (0 : σ → ℝ) p = p.coeff 0
  rw [MvPolynomial.eval_zero]
  rw [MvPolynomial.constantCoeff_eq]

lemma coeff_zero_pderivL_ne_zero {σ : Type*} (l : List σ) (p : MvPolynomial σ ℝ) :
    (pderivL l p).coeff 0 ≠ 0 ↔ eSum l ∈ p.support := by
  simpa using (mem_support_pderivL l p (0 : σ →₀ ℕ)).trans (by simp)

lemma eval_zero_pderivL_ne_zero_iff {σ : Type*} (l : List σ) (p : MvPolynomial σ ℝ) :
    MvPolynomial.eval (fun _ : σ => (0 : ℝ)) (pderivL l p) ≠ 0 ↔ eSum l ∈ p.support := by
  rw [eval_zero_eq_coeff]
  exact coeff_zero_pderivL_ne_zero l p

/-! ## 3. Nonnegativity of evaluations -/

lemma eval_nonneg_of_coeff_nonneg {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ)
    (hp : ∀ m : σ →₀ ℕ, 0 ≤ p.coeff m) {w : σ → ℝ} (hw : ∀ k : σ, 0 ≤ w k) :
    0 ≤ MvPolynomial.eval w p := by
  classical
  rw [← support_sum_monomial_coeff p]
  rw [eval_sum]
  exact Finset.sum_nonneg (by
    intro m hm
    rw [eval_monomial]
    exact mul_nonneg (hp m) (by
      rw [Finsupp.prod_pow]
      exact Finset.prod_nonneg (fun a _ => pow_nonneg (hw a) (m a))))

lemma eval_nonneg_pderivL {σ : Type*} [Fintype σ] (l : List σ) (p : MvPolynomial σ ℝ)
    (hp : ∀ m : σ →₀ ℕ, 0 ≤ p.coeff m) {w : σ → ℝ} (hw : ∀ k : σ, 0 ≤ w k) :
    0 ≤ MvPolynomial.eval w (pderivL l p) :=
  eval_nonneg_of_coeff_nonneg (pderivL l p) (coeff_pderivL_nonneg l p hp) hw

/-! ## 4. The list Rayleigh predicate -/

/-- list `c`-Rayleigh property (equivalent to the definition of Brändén–Huh) -/
def Ray {σ : Type*} (c : ℝ) (p : MvPolynomial σ ℝ) : Prop :=
  ∀ (l : List σ) (i j : σ) (w : σ → ℝ), (∀ k : σ, 0 ≤ w k) →
    MvPolynomial.eval w (pderivL l p) *
        MvPolynomial.eval w (pderivL (i :: j :: l) p) ≤
      c * (MvPolynomial.eval w (pderivL (i :: l) p) *
        MvPolynomial.eval w (pderivL (j :: l) p))

/-- contraction by a single derivative preserves the Rayleigh property -/
lemma ray_contraction_single {σ : Type*} (c : ℝ) (i : σ) (p : MvPolynomial σ ℝ)
    (hR : Ray c p) : Ray c (pderiv i p) := by
  intro l j k w hw
  have h := hR (i :: l) j k w hw
  have hF2 : pderivL (j :: k :: l) (pderiv i p) = pderivL (i :: j :: k :: l) p :=
    pderivL_cons_append i (j :: k :: l) p
  rw [pderivL_cons_append i l p]
  rw [hF2]
  have hp2 : pderivL (i :: j :: k :: l) p = pderivL (j :: k :: i :: l) p := by
    apply pderivL_perm
    exact List.Perm.trans (List.Perm.swap j i (k :: l))
      (List.Perm.cons j (List.Perm.swap i k l).symm)
  rw [hp2]
  have hp3 : pderivL (i :: j :: l) p = pderivL (j :: i :: l) p := by
    apply pderivL_perm
    exact (List.Perm.swap i j l).symm
  rw [pderivL_cons_append i (j :: l) p, hp3]
  have hp4 : pderivL (i :: k :: l) p = pderivL (k :: i :: l) p := by
    apply pderivL_perm
    exact (List.Perm.swap i k l).symm
  rw [pderivL_cons_append i (k :: l) p, hp4]
  exact h

/-- contraction along a list preserves the Rayleigh property -/
lemma ray_contraction {σ : Type*} (c : ℝ) (la : List σ) (p : MvPolynomial σ ℝ)
    (hR : Ray c p) : Ray c (pderivL la p) := by
  classical
  revert p hR
  induction la with
  | nil =>
      intro p hR
      simpa using hR
  | cons i la ih =>
      intro p hR
      rw [pderivL_cons]
      exact ih (pderiv i p) (ray_contraction_single c i p hR)
/-! ## 5. Degree of a polynomial -/

/-- total degree of a polynomial (sup over the support of the exponent degree) -/
def degPoly {σ : Type*} (p : MvPolynomial σ ℝ) : ℕ := p.support.sup degN

lemma degN_le_degPoly {σ : Type*} (p : MvPolynomial σ ℝ) {m : σ →₀ ℕ}
    (hm : m ∈ p.support) : degN m ≤ degPoly p := by
  exact Finset.le_sup hm

/-- degree strictly decreases under nonzero contraction -/
lemma degPoly_pderiv_lt {σ : Type*} (i : σ) (p : MvPolynomial σ ℝ)
    (hne : pderiv i p ≠ 0) : degPoly (pderiv i p) < degPoly p := by
  classical
  have hne_supp : ∃ m : σ →₀ ℕ, m ∈ (pderiv i p).support := by
    by_contra h
    apply hne
    ext m
    by_contra hc
    exact h ⟨m, MvPolynomial.mem_support_iff.mpr hc⟩
  rcases hne_supp with ⟨m0, hm0⟩
  have hle : degPoly (pderiv i p) ≤ degPoly p - 1 := by
    refine Finset.sup_le ?_
    intro m hm
    have hm' : m + e i ∈ p.support := (mem_support_pderiv i p m).mp hm
    have hd : degN m = degN (m + e i) - 1 := by
      have hne2 : (m + e i) i ≠ 0 := by simp
      calc
        degN m = degN ((m + e i) - e i) := by
          rw [add_sub_single m i]
        _ = degN (m + e i) - 1 := degN_sub_single (m + e i) i hne2
    calc
      degN m = degN (m + e i) - 1 := hd
      _ ≤ degPoly p - 1 := Nat.sub_le_sub_right (degN_le_degPoly p hm') 1
  have hpos : 1 ≤ degPoly p := by
    have hm0' : m0 + e i ∈ p.support := (mem_support_pderiv i p m0).mp hm0
    have hcoord : 1 ≤ (m0 + e i) i := by simp
    have hdeg1 : 1 ≤ degN (m0 + e i) :=
      le_trans hcoord (coord_le_degN (m0 + e i) i)
    exact le_trans hdeg1 (degN_le_degPoly p hm0')
  omega

/-! ## 6. Nonnegativity and evaluation bounds at (ε,…,ε) -/

/-- evaluation at the all-`ε` vector -/
lemma eval_eps_eq {σ : Type*} [Fintype σ] (ε : ℝ) (p : MvPolynomial σ ℝ) :
    MvPolynomial.eval (fun _ : σ => ε) p =
      ∑ m ∈ p.support, p.coeff m * ε ^ degN m := by
  classical
  rw [eval_eq']
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  rw [degN, Finsupp.weight_eq_sum]
  simp
  rw [Finset.prod_pow_eq_pow_sum]

/-- a single monomial term is no larger than the whole evaluation -/
lemma eval_ge_term {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ)
    (hp : ∀ m : σ →₀ ℕ, 0 ≤ p.coeff m) {w : σ → ℝ} (hw : ∀ k : σ, 0 ≤ w k)
    (m : σ →₀ ℕ) (hm : m ∈ p.support) :
    p.coeff m * (∏ i : σ, w i ^ m i) ≤ MvPolynomial.eval w p := by
  classical
  rw [eval_eq']
  refine Finset.single_le_sum (f := fun a : σ →₀ ℕ => p.coeff a * ∏ i : σ, w i ^ a i) ?_ hm
  intro a ha
  exact mul_nonneg (hp a) (Finset.prod_nonneg (fun k _ => pow_nonneg (hw k) (a k)))

/-- evaluation at (ε,…,ε) is bounded below by the monomial term -/
lemma eval_eps_ge_term {σ : Type*} [Fintype σ] (ε : ℝ) (hε : 0 ≤ ε) (p : MvPolynomial σ ℝ)
    (hp : ∀ m : σ →₀ ℕ, 0 ≤ p.coeff m) (m : σ →₀ ℕ) (hm : m ∈ p.support) :
    p.coeff m * ε ^ degN m ≤ MvPolynomial.eval (fun _ : σ => ε) p := by
  classical
  rw [eval_eps_eq]
  exact Finset.single_le_sum (fun a ha => by
    exact mul_nonneg (hp a) (pow_nonneg hε (degN a))) hm

/-- evaluation at (ε,…,ε), `ε ≤ 1`, bounded above by the coefficient sum -/
lemma eval_eps_le {σ : Type*} [Fintype σ] (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (p : MvPolynomial σ ℝ) (hp : ∀ m : σ →₀ ℕ, 0 ≤ p.coeff m)
    (L : ℕ) (hL : ∀ m : σ →₀ ℕ, m ∈ p.support → L ≤ degN m) :
    MvPolynomial.eval (fun _ : σ => ε) p ≤ (∑ m ∈ p.support, p.coeff m) * ε ^ L := by
  classical
  rw [eval_eps_eq]
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (by
    intro m hm
    have hdeg : ε ^ degN m ≤ ε ^ L := by
      exact pow_le_pow_of_le_one hε0 hε1 (hL m hm)
    exact mul_le_mul_of_nonneg_left hdeg (hp m))

/-- strict positivity of evaluation at positive weights, given a positive-coefficient monomial -/
lemma eval_eps_pos_of_mem {σ : Type*} [Fintype σ] (ε : ℝ) (hε : 0 < ε) (p : MvPolynomial σ ℝ)
    (hp : ∀ m : σ →₀ ℕ, 0 ≤ p.coeff m) (m : σ →₀ ℕ) (hm : m ∈ p.support) :
    0 < MvPolynomial.eval (fun _ : σ => ε) p := by
  classical
  have hc : 0 < p.coeff m := by
    exact lt_of_le_of_ne' (hp m) (MvPolynomial.mem_support_iff.mp hm)
  have hprod : 0 < ε ^ degN m := pow_pos hε (degN m)
  exact lt_of_lt_of_le (mul_pos hc hprod) (eval_eps_ge_term ε (le_of_lt hε) p hp m hm)


/-! ## 7. Minimal counterexample argument -/

/-- a "bad triple": `α ≤ γ ≤ β` with endpoints in the support and `γ` outside -/
def Bad {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (α γ β : Fin n →₀ ℕ) : Prop :=
  α ∈ p.support ∧ β ∈ p.support ∧ (∀ k : Fin n, α k ≤ γ k) ∧
    (∀ k : Fin n, γ k ≤ β k) ∧ γ ∉ p.support

/-- subtracting a unit vector is coordinatewise monotone -/
lemma sub_single_mono {σ : Type*} (i : σ) {m m' : σ →₀ ℕ} (h : ∀ k : σ, m k ≤ m' k) :
    ∀ k : σ, (m - e i) k ≤ (m' - e i) k := by
  intro k
  by_cases hk : k = i
  · subst k
    have h1 : (m - e i) i = m i - 1 := by simp [e]
    have h2 : (m' - e i) i = m' i - 1 := by simp [e]
    rw [h1, h2]
    exact Nat.sub_le_sub_right (h i) 1
  · have h1 : (m - e i) k = m k := by simp [e, hk]
    have h2 : (m' - e i) k = m' k := by simp [e, hk]
    rw [h1, h2]
    exact h k


lemma degN_pos_of_ne_zero {σ : Type*} (m : σ →₀ ℕ) (hm : m ≠ 0) : 1 ≤ degN m := by
  classical
  by_contra h
  apply hm
  ext i
  have hd : degN m = 0 := by omega
  have hc := coord_le_degN m i
  simp at hc ⊢
  omega

/-- subtracting unit vectors commutes -/
lemma sub_sub_comm {σ : Type*} (m : σ →₀ ℕ) (a b : σ) :
    (m - e a) - e b = (m - e b) - e a := by
  classical
  ext k
  simp [e]
  omega

/-- a vector is at least the same vector with a unit vector removed, coordinatewise -/
lemma sub_e_le_self {σ : Type*} (m : σ →₀ ℕ) (i : σ) :
    ∀ k : σ, (m - e i) k ≤ m k := by
  intro k
  by_cases hk : k = i
  · subst k
    simp [e]
  · simp [e, hk]

/-- interval convexity, formulated with the two inequalities separately -/
lemma interval_convex_iff (n : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    (∀ α γ β : Fin n →₀ ℕ, α ∈ p.support → β ∈ p.support →
      (∀ k, α k ≤ γ k) → (∀ k, γ k ≤ β k) → γ ∈ p.support) ↔
    ¬ ∃ α γ β : Fin n →₀ ℕ, Bad p α γ β := by
  constructor
  · intro h
    rintro ⟨α, γ, β, hα, hβ, hαγ, hγβ, hγn⟩
    exact hγn (h α γ β hα hβ hαγ hγβ)
  · intro h α γ β hα hβ hαγ hγβ
    by_contra hγn
    exact h ⟨α, γ, β, hα, hβ, hαγ, hγβ, hγn⟩




/-! ## 8. Auxiliary facts for the final ε-contradiction -/

/-- sum of coordinates over a subset is bounded by the total degree -/
lemma sum_le_degN {σ : Type*} [Fintype σ] (m : σ →₀ ℕ) (s : Finset σ) :
    (∑ x ∈ s, m x) ≤ degN m := by
  classical
  calc
    (∑ x ∈ s, m x) ≤ ∑ x ∈ (Finset.univ : Finset σ), m x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (by intro x hx1 hx2; exact Nat.zero_le _)
    _ = degN m := (degN_eq_sum m).symm

/-- a small positive `ε` violating the family of Rayleigh inequalities -/
lemma small_eps_contradiction (c : ℝ) (hc : 0 < c) (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (b : ℕ) (hb : 2 ≤ b)
    (hineq : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → A * ε ^ (b - 2) ≤ c * B * ε ^ (2 * b - 2)) : False := by
  let D : ℝ := A / (c * B)
  have hcB : 0 < c * B := mul_pos hc hB
  have hD : 0 < D := div_pos hA hcB
  let ε : ℝ := min (1 : ℝ) (D / 2)
  have hε0 : 0 < ε := lt_min (by norm_num) (div_pos hD (by norm_num))
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεsmall : c * B * ε ^ b < A := by
    have hpow : ε ^ b ≤ ε := by
      have hb1 : 1 ≤ b := by omega
      have h1 : ε ^ (b - 1) ≤ 1 := pow_le_one₀ (le_of_lt hε0) hε1
      calc
        ε ^ b = ε ^ (1 + (b - 1)) := by
          congr 1
          omega
        _ = ε * ε ^ (b - 1) := by rw [pow_add]; ring
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left h1 (le_of_lt hε0)
        _ = ε := by ring
    have h1 : c * B * ε ^ b ≤ c * B * ε := mul_le_mul_of_nonneg_left hpow (le_of_lt hcB)
    have h2 : c * B * ε ≤ c * B * (D / 2) :=
      mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) (D / 2)) (le_of_lt hcB)
    have h3 : c * B * (D / 2) < A := by
      have h4 : c * B * (D / 2) = A / 2 := by
        dsimp [D]
        field_simp [hA.ne', hcB.ne']
      nlinarith
    exact lt_of_le_of_lt (le_trans h1 h2) h3
  have hineqε := hineq ε hε0 hε1
  have hpow2 : ε ^ (2 * b - 2) = ε ^ (b - 2) * ε ^ b := by
    rw [← pow_add]
    congr 1
    omega
  have hbd : c * B * ε ^ (2 * b - 2) < A * ε ^ (b - 2) := by
    rw [hpow2]
    calc
      c * B * (ε ^ (b - 2) * ε ^ b) = (c * B * ε ^ b) * ε ^ (b - 2) := by ring
      _ < A * ε ^ (b - 2) := mul_lt_mul_of_pos_right hεsmall (pow_pos hε0 (b - 2))
  have hpow3 : 0 ≤ A * ε ^ (b - 2) := by positivity
  linarith


/-- ε-contradiction data: given a monomial `δ0` in the second derivative and the
degree bounds, the Rayleigh inequality fails for small `ε` -/
lemma eps_contra_data {n : ℕ} (c : ℝ) (hc : 0 < c)
    (f : MvPolynomial (Fin n) ℝ) (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ f.coeff m)
    (hrf : Ray c f) {β δ0 : Fin n →₀ ℕ} (k l : Fin n) (b0 : ℕ)
    (hb : degN β = b0) (hb2 : 2 ≤ b0)
    (hδ0deg : degN δ0 = b0 - 2)
    (hδ0supp : δ0 ∈ (pderiv l (pderiv k f)).support)
    (h0supp : (0 : Fin n →₀ ℕ) ∈ f.support)
    (hβsupp : β ∈ f.support)
    (hβk : 1 ≤ β k) (hβl : 1 ≤ β l)
    (hdegMin : ∀ (t : Fin n), 1 ≤ β t → ∀ δ : Fin n →₀ ℕ, δ ∈ f.support → 1 ≤ δ t → b0 ≤ degN δ) :
    False := by
  classical
  have hc0 : 0 < f.coeff 0 :=
    lt_of_le_of_ne' (hnn 0) (MvPolynomial.mem_support_iff.mp h0supp)
  have hnnk : ∀ m : Fin n →₀ ℕ, 0 ≤ (pderiv k f).coeff m := coeff_pderiv_nonneg k f hnn
  have hnnl : ∀ m : Fin n →₀ ℕ, 0 ≤ (pderiv l f).coeff m := coeff_pderiv_nonneg l f hnn
  have hnnq : ∀ m : Fin n →₀ ℕ, 0 ≤ (pderiv l (pderiv k f)).coeff m :=
    coeff_pderiv_nonneg l (pderiv k f) hnnk
  let C : ℝ := (pderiv l (pderiv k f)).coeff δ0
  have hC : 0 < C :=
    lt_of_le_of_ne' (hnnq δ0) (MvPolynomial.mem_support_iff.mp hδ0supp)
  let Sk : ℝ := ∑ m ∈ (pderiv k f).support, (pderiv k f).coeff m
  let Sl : ℝ := ∑ m ∈ (pderiv l f).support, (pderiv l f).coeff m
  have hSk : 0 < Sk := by
    have hβk0 : β k ≠ 0 := by omega
    have hmem : β - e k ∈ (pderiv k f).support := by
      rw [mem_support_pderiv_sub k f β hβk0]
      exact hβsupp
    have hpos : 0 < (pderiv k f).coeff (β - e k) :=
      lt_of_le_of_ne' (hnnk (β - e k)) (MvPolynomial.mem_support_iff.mp hmem)
    dsimp [Sk]
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun m hm => hnnk m) hmem)
  have hSl : 0 < Sl := by
    have hβl0 : β l ≠ 0 := by omega
    have hmem : β - e l ∈ (pderiv l f).support := by
      rw [mem_support_pderiv_sub l f β hβl0]
      exact hβsupp
    have hpos : 0 < (pderiv l f).coeff (β - e l) :=
      lt_of_le_of_ne' (hnnl (β - e l)) (MvPolynomial.mem_support_iff.mp hmem)
    dsimp [Sl]
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun m hm => hnnl m) hmem)
  have hdegK : ∀ m : Fin n →₀ ℕ, m ∈ (pderiv k f).support → b0 - 1 ≤ degN m := by
    intro m hm
    have hm' : m + e k ∈ f.support := (mem_support_pderiv k f m).mp hm
    have hdk : 1 ≤ (m + e k) k := by simp
    have hb' : b0 ≤ degN (m + e k) := hdegMin k hβk (m + e k) hm' hdk
    have hdegadd : degN (m + e k) = degN m + 1 := by
      rw [degN_add, degN_e]
    omega
  have hdegL : ∀ m : Fin n →₀ ℕ, m ∈ (pderiv l f).support → b0 - 1 ≤ degN m := by
    intro m hm
    have hm' : m + e l ∈ f.support := (mem_support_pderiv l f m).mp hm
    have hdl : 1 ≤ (m + e l) l := by simp
    have hb' : b0 ≤ degN (m + e l) := hdegMin l hβl (m + e l) hm' hdl
    have hdegadd : degN (m + e l) = degN m + 1 := by
      rw [degN_add, degN_e]
    omega
  have hineq : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      f.coeff 0 * C * ε ^ (b0 - 2) ≤ c * (Sk * Sl) * ε ^ (2 * b0 - 2) := by
    intro ε hε0 hε1
    let w : Fin n → ℝ := fun _ => ε
    have hw0 : ∀ x : Fin n, 0 ≤ w x := by intro x; dsimp [w]; exact le_of_lt hε0
    have hray := hrf [] k l w hw0
    have hEf : f.coeff 0 ≤ MvPolynomial.eval w f := by
      have := eval_eps_ge_term ε (le_of_lt hε0) f hnn (0 : Fin n →₀ ℕ) h0supp
      simpa [w, degN] using this
    have hEf0 : 0 ≤ MvPolynomial.eval w f := le_of_lt (lt_of_lt_of_le hc0 hEf)
    have hEq : C * ε ^ (b0 - 2) ≤ MvPolynomial.eval w (pderiv l (pderiv k f)) := by
      have := eval_eps_ge_term ε (le_of_lt hε0) (pderiv l (pderiv k f)) hnnq δ0 hδ0supp
      rw [hδ0deg] at this
      simpa [w, C] using this
    have hCε : 0 < C * ε ^ (b0 - 2) := mul_pos hC (pow_pos hε0 (b0 - 2))
    have hEq0 : 0 ≤ MvPolynomial.eval w (pderiv l (pderiv k f)) :=
      le_of_lt (lt_of_lt_of_le hCε hEq)
    have hEk : MvPolynomial.eval w (pderiv k f) ≤ Sk * ε ^ (b0 - 1) := by
      have := eval_eps_le ε (le_of_lt hε0) hε1 (pderiv k f) hnnk (b0 - 1) hdegK
      simpa [w, Sk] using this
    have hEl : MvPolynomial.eval w (pderiv l f) ≤ Sl * ε ^ (b0 - 1) := by
      have := eval_eps_le ε (le_of_lt hε0) hε1 (pderiv l f) hnnl (b0 - 1) hdegL
      simpa [w, Sl] using this
    have hprodL : f.coeff 0 * C * ε ^ (b0 - 2) ≤
        MvPolynomial.eval w f * MvPolynomial.eval w (pderiv l (pderiv k f)) := by
      have h1 : f.coeff 0 * (C * ε ^ (b0 - 2)) ≤
          MvPolynomial.eval w f * MvPolynomial.eval w (pderiv l (pderiv k f)) :=
        mul_le_mul hEf hEq hCε.le hEf0
      simpa [mul_assoc] using h1
    have hpowE : ε ^ (2 * b0 - 2) = ε ^ (b0 - 1) * ε ^ (b0 - 1) := by
      rw [← pow_add]
      congr 1
      omega
    have hSk0 : 0 ≤ Sk := by dsimp [Sk]; exact Finset.sum_nonneg (fun m hm => hnnk m)
    have hSl0 : 0 ≤ Sl := by dsimp [Sl]; exact Finset.sum_nonneg (fun m hm => hnnl m)
    have hSkε : 0 ≤ Sk * ε ^ (b0 - 1) :=
      mul_nonneg hSk0 (pow_nonneg (le_of_lt hε0) (b0 - 1))
    have hEl0 : 0 ≤ MvPolynomial.eval w (pderiv l f) :=
      eval_nonneg_of_coeff_nonneg (pderiv l f) hnnl hw0
    have hR1 : MvPolynomial.eval w (pderiv k f) * MvPolynomial.eval w (pderiv l f) ≤
        (Sk * ε ^ (b0 - 1)) * (Sl * ε ^ (b0 - 1)) :=
      mul_le_mul hEk hEl hEl0 hSkε
    have hR1' : (Sk * ε ^ (b0 - 1)) * (Sl * ε ^ (b0 - 1)) = Sk * Sl * ε ^ (2 * b0 - 2) := by
      rw [hpowE]
      ring
    calc
      f.coeff 0 * C * ε ^ (b0 - 2) ≤ MvPolynomial.eval w f *
          MvPolynomial.eval w (pderiv l (pderiv k f)) := hprodL
      _ ≤ c * (MvPolynomial.eval w (pderiv k f) * MvPolynomial.eval w (pderiv l f)) := by
            simpa [pderivL] using hray
      _ ≤ c * ((Sk * ε ^ (b0 - 1)) * (Sl * ε ^ (b0 - 1))) :=
            mul_le_mul_of_nonneg_left hR1 (le_of_lt hc)
      _ = c * (Sk * Sl) * ε ^ (2 * b0 - 2) := by
            rw [hR1']
            ring
  exact small_eps_contradiction c hc (f.coeff 0 * C) (Sk * Sl)
    (mul_pos hc0 hC) (mul_pos hSk hSl) b0 hb2 hineq

/-- Main theorem: the support of a (list-)Rayleigh polynomial with nonnegative
coefficients is interval convex. -/
theorem interval_convex_of_rayleigh (n : ℕ) (c : ℝ) (hc : 0 < c)
    (q : MvPolynomial (Fin n) ℝ)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ q.coeff m)
    (hr : ∀ (l : List (Fin n)) (i j : Fin n) (w : Fin n → ℝ),
      (∀ k : Fin n, 0 ≤ w k) →
        MvPolynomial.eval w (l.foldl (fun q i => MvPolynomial.pderiv i q) q) *
            MvPolynomial.eval w ((i :: j :: l).foldl (fun q i => MvPolynomial.pderiv i q) q) ≤
          c * (MvPolynomial.eval w ((i :: l).foldl (fun q i => MvPolynomial.pderiv i q) q) *
            MvPolynomial.eval w ((j :: l).foldl (fun q i => MvPolynomial.pderiv i q) q))) :
    ∀ α : Fin n →₀ ℕ, α ∈ q.support → ∀ β : Fin n →₀ ℕ, β ∈ q.support →
      ∀ γ : Fin n →₀ ℕ, (∀ k : Fin n, α k ≤ γ k) → (∀ k : Fin n, γ k ≤ β k) →
        γ ∈ q.support := by
  classical
  have hR : Ray c q := by
    simpa [Ray, pderivL] using hr
  -- strong induction on the total degree of the polynomial
  let P : ℕ → Prop := fun d => ∀ (f : MvPolynomial (Fin n) ℝ), degPoly f = d →
      (∀ m : Fin n →₀ ℕ, 0 ≤ f.coeff m) → Ray c f → ¬ ∃ α γ β : Fin n →₀ ℕ, Bad f α γ β
  have hP : ∀ d : ℕ, P d := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro f hdeg hnnf hrf hex
        -- choose a bad triple with |β| minimal, then |γ| minimal
        rcases hex with ⟨αx, γx, βx, hBx⟩
        have hex1 : ∃ b : ℕ, ∃ α γ β : Fin n →₀ ℕ, Bad f α γ β ∧ degN β = b :=
          ⟨degN βx, αx, γx, βx, hBx, rfl⟩
        let b0 := Nat.find hex1
        rcases (Nat.find_spec hex1) with ⟨αx2, γx2, βx2, hB2, hb0x⟩
        have hex2 : ∃ g : ℕ, ∃ α γ β : Fin n →₀ ℕ, Bad f α γ β ∧ degN β = b0 ∧ degN γ = g :=
          ⟨degN γx2, αx2, γx2, βx2, hB2, hb0x, rfl⟩
        let g0 := Nat.find hex2
        rcases (Nat.find_spec hex2) with ⟨α, γ, β, hB, hb0, hg0⟩
        rcases hB with ⟨hα, hβ, hαγ, hγβ, hγn⟩
        have hmin1 : ∀ b' : ℕ, b' < b0 →
            ¬ ∃ α γ β : Fin n →₀ ℕ, Bad f α γ β ∧ degN β = b' := by
          intro b' hb' h'
          have hle : b0 ≤ b' := Nat.find_le h'
          omega
        have hmin2 : ∀ g' : ℕ, g' < g0 →
            ¬ ∃ α γ β : Fin n →₀ ℕ, Bad f α γ β ∧ degN β = b0 ∧ degN γ = g' := by
          intro g' hg' h'
          have hle : g0 ≤ g' := Nat.find_le h'
          omega
        -- a bad triple in any contraction gives a contradiction via the induction hypothesis
        have contr : ∀ (j : Fin n) (α' γ' β' : Fin n →₀ ℕ),
            Bad (pderiv j f) α' γ' β' → False := by
          intro j α' γ' β' hB'
          have hne : pderiv j f ≠ 0 := by
            intro hz
            have : α' ∈ (0 : MvPolynomial (Fin n) ℝ).support := by
              simpa [hz] using hB'.1
            simpa using this
          have hdegLt : degPoly (pderiv j f) < degPoly f := degPoly_pderiv_lt j f hne
          have hnn' : ∀ m : Fin n →₀ ℕ, 0 ≤ (pderiv j f).coeff m :=
            coeff_pderiv_nonneg j f hnnf
          have hr' : Ray c (pderiv j f) := ray_contraction_single c j f hrf
          have hno : ¬ ∃ a g b : Fin n →₀ ℕ, Bad (pderiv j f) a g b :=
            ih (degPoly (pderiv j f)) (by omega) (pderiv j f) rfl hnn' hr'
          exact hno ⟨α', γ', β', hB'⟩
        -- (1) α = 0 : otherwise a contraction gives a smaller counterexample
        have hα0 : α = 0 := by
          ext j
          by_contra hαjnz
          have hmem1 : α - e j ∈ (pderiv j f).support := by
            rw [mem_support_pderiv_sub j f α hαjnz]
            exact hα
          have hmem2 : β - e j ∈ (pderiv j f).support := by
            have hβj : β j ≠ 0 := by
              intro hβj0
              have hαj1 : 1 ≤ α j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hαjnz)
              have h1 := hαγ j
              have h2 := hγβ j
              omega
            rw [mem_support_pderiv_sub j f β hβj]
            exact hβ
          have hmem3 : γ - e j ∉ (pderiv j f).support := by
            intro hmem
            have hγj : γ j ≠ 0 := by
              intro hγj0
              have hαj1 : 1 ≤ α j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hαjnz)
              have h1 := hαγ j
              omega
            have : γ ∈ f.support := (mem_support_pderiv_sub j f γ hγj).mp hmem
            exact hγn this
          have hord1 : ∀ k, (α - e j) k ≤ (γ - e j) k := sub_single_mono j hαγ
          have hord2 : ∀ k, (γ - e j) k ≤ (β - e j) k := sub_single_mono j hγβ
          exact contr j (α - e j) (γ - e j) (β - e j)
            ⟨hmem1, hmem2, hord1, hord2, hmem3⟩
        have h0mem : (0 : Fin n →₀ ℕ) ∈ f.support := by simpa [hα0] using hα
        have hγnz : γ ≠ 0 := by
          intro hγz
          apply hγn
          simpa [hγz] using h0mem
        have hβnz : β ≠ 0 := by
          intro hβz
          have : γ = 0 := by
            ext k
            have h1 := hγβ k
            simpa [hβz] using h1
          exact hγnz this
        have hb0pos : 1 ≤ b0 := by
          have : 1 ≤ degN β := degN_pos_of_ne_zero β hβnz
          simpa [hb0] using this
        have hg0pos : 1 ≤ g0 := by
          have hdeg : 1 ≤ degN γ := degN_pos_of_ne_zero γ hγnz
          rw [hg0] at hdeg
          exact hdeg
        -- (2) γ is a unit vector
        have hγunit : ∃ i : Fin n, γ = e i := by
          by_contra hnu
          have hcover : ∀ j : Fin n, 1 ≤ γ j → γ - e j ∈ f.support := by
            intro j hγj
            by_contra hmem
            have hord0 : ∀ k : Fin n, (0 : Fin n →₀ ℕ) k ≤ (γ - e j) k :=
              fun k => Nat.zero_le _
            have hord4 : ∀ k : Fin n, (γ - e j) k ≤ β k := by
              intro k
              by_cases hk : k = j
              · subst k
                have h2 := hγβ j
                simp [e]
                omega
              · simp [e, hk, hγβ k]
            have hB0 : Bad f 0 (γ - e j) β := ⟨h0mem, hβ, hord0, hord4, hmem⟩
            have hdegγ' : degN (γ - e j) = g0 - 1 := by
              have hγj0 : γ j ≠ 0 := ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hγj)
              have : degN (γ - e j) = degN γ - 1 := degN_sub_single γ j hγj0
              rwa [hg0] at this
            have hgLt : g0 - 1 < g0 := by omega
            exact hmin2 (g0 - 1) hgLt ⟨0, γ - e j, β, hB0, hb0, hdegγ'⟩
          -- choose j0 with γ j0 ≥ 1
          have hexj0 : ∃ j : Fin n, 1 ≤ γ j := by
            by_contra h
            apply hγnz
            ext j
            by_contra hc
            exact h ⟨j, Nat.succ_le_of_lt (Nat.pos_of_ne_zero hc)⟩
          rcases hexj0 with ⟨j0, hγj0⟩
          by_cases hsingle : ∀ k : Fin n, k ≠ j0 → γ k = 0
          · -- single coordinate case
            have hγj0ge2 : 2 ≤ γ j0 := by
              by_contra hlt
              have hγj0eq1 : γ j0 = 1 := by omega
              apply hnu
              refine ⟨j0, ?_⟩
              ext k
              by_cases hk : k = j0
              · subst k
                simpa [e] using hγj0eq1
              · have hγk0 : γ k = 0 := hsingle k hk
                simp [e, hk, hγk0]
            let L : Fin n →₀ ℕ := (γ - e j0) - e j0
            let M : Fin n →₀ ℕ := γ - e j0
            let U : Fin n →₀ ℕ := β - e j0
            have hmemL : L ∈ (pderiv j0 f).support := by
              have hcov : γ - e j0 ∈ f.support := hcover j0 hγj0
              have hme : L + e j0 = γ - e j0 := by
                dsimp [L]
                have hz : (γ - e j0) j0 ≠ 0 := by
                  have hz' : (γ - e j0) j0 = γ j0 - 1 := by simp [e]
                  rw [hz']
                  omega
                exact sub_single_add (γ - e j0) j0 hz
              rw [mem_support_pderiv]
              rw [hme]
              exact hcov
            have hmemM : M ∉ (pderiv j0 f).support := by
              intro hmem
              have hme : M + e j0 = γ := by
                dsimp [M]
                have hγj0nz : γ j0 ≠ 0 := by omega
                exact sub_single_add γ j0 hγj0nz
              have : γ ∈ f.support := by
                rw [mem_support_pderiv] at hmem
                simpa [hme] using hmem
              exact hγn this
            have hmemU : U ∈ (pderiv j0 f).support := by
              have hβj0 : β j0 ≠ 0 := by
                intro hβ0
                have h1 := hγβ j0
                omega
              rw [mem_support_pderiv_sub j0 f β hβj0]
              exact hβ
            have hordL : ∀ k, L k ≤ M k := by
              intro k
              dsimp [L, M]
              exact sub_e_le_self (γ - e j0) j0 k
            have hordM : ∀ k, M k ≤ U k := by
              intro k
              dsimp [M, U]
              exact sub_single_mono j0 hγβ k
            exact contr j0 L M U ⟨hmemL, hmemU, hordL, hordM, hmemM⟩
          · -- two distinct coordinates case
            push_neg at hsingle
            rcases hsingle with ⟨k, hkneq, hγk⟩
            have hγk1 : 1 ≤ γ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hγk)
            let L : Fin n →₀ ℕ := (γ - e j0) - e k
            let M : Fin n →₀ ℕ := γ - e j0
            let U : Fin n →₀ ℕ := β - e j0
            have hmemL : L ∈ (pderiv j0 f).support := by
              have hcov : γ - e k ∈ f.support := hcover k hγk1
              have hme : L + e j0 = γ - e k := by
                dsimp [L]
                rw [sub_sub_comm]
                have hz : (γ - e k) j0 ≠ 0 := by
                  have hz' : (γ - e k) j0 = γ j0 := by
                    simp [e, hkneq.symm]
                  rw [hz']
                  exact ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hγj0)
                exact sub_single_add (γ - e k) j0 hz
              rw [mem_support_pderiv]
              rw [hme]
              exact hcov
            have hmemM : M ∉ (pderiv j0 f).support := by
              intro hmem
              have hme : M + e j0 = γ := by
                dsimp [M]
                have hγj0nz : γ j0 ≠ 0 := by omega
                exact sub_single_add γ j0 hγj0nz
              have : γ ∈ f.support := by
                rw [mem_support_pderiv] at hmem
                simpa [hme] using hmem
              exact hγn this
            have hmemU : U ∈ (pderiv j0 f).support := by
              have hβj0 : β j0 ≠ 0 := by
                intro hβ0
                have h1 := hγβ j0
                omega
              rw [mem_support_pderiv_sub j0 f β hβj0]
              exact hβ
            have hordL : ∀ k, L k ≤ M k := by
              intro t
              dsimp [L, M]
              exact sub_e_le_self (γ - e j0) k t
            have hordM : ∀ k, M k ≤ U k := by
              intro t
              dsimp [M, U]
              exact sub_single_mono j0 hγβ t
            exact contr j0 L M U ⟨hmemL, hmemU, hordL, hordM, hmemM⟩
        rcases hγunit with ⟨i, hγei⟩
        have hei_n : e i ∉ f.support := by
          intro hm
          apply hγn
          simpa [hγei] using hm
        have hβi1 : 1 ≤ β i := by
          have hg := hγβ i
          rw [hγei] at hg
          simpa [e] using hg
        -- (3) no unit vector `e_k` with `β k ≥ 1` lies in the support
        have hnoUnit : ∀ k : Fin n, 1 ≤ β k → e k ∉ f.support := by
          intro k hβk
          by_contra hek
          by_cases hik : i = k
          · subst k
            exact hei_n hek
          · by_cases heik : e i + e k ∈ f.support
            · -- Rayleigh at the origin with the pair (i, k)
              have hineq := hrf [] i k (fun _ : Fin n => (0 : ℝ)) (by intro x; simp)
              have hc0 : 0 < f.coeff 0 :=
                lt_of_le_of_ne' (hnnf 0) (MvPolynomial.mem_support_iff.mp h0mem)
              have hmem0 : (0 : Fin n →₀ ℕ) ∈ (pderiv k (pderiv i f)).support := by
                rw [mem_support_pderiv]
                rw [mem_support_pderiv]
                simpa [add_assoc, add_comm, add_left_comm] using heik
              have hcik : 0 < (pderiv k (pderiv i f)).coeff 0 :=
                lt_of_le_of_ne' (coeff_pderiv_nonneg k (pderiv i f)
                  (coeff_pderiv_nonneg i f hnnf) 0)
                  (MvPolynomial.mem_support_iff.mp hmem0)
              have hci0 : (pderiv i f).coeff 0 = 0 := by
                by_contra hc
                have hmem : (0 : Fin n →₀ ℕ) ∈ (pderiv i f).support :=
                  MvPolynomial.mem_support_iff.mpr hc
                have hmem' : e i ∈ f.support := by
                  simpa using ((mem_support_pderiv i f (0 : Fin n →₀ ℕ)).mp (by simpa using hmem))
                exact hei_n hmem'
              have hLHS : 0 < MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) f *
                  MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) (pderiv k (pderiv i f)) := by
                rw [eval_zero_eq_coeff, eval_zero_eq_coeff]
                exact mul_pos hc0 hcik
              have hRHS : c * (MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) (pderiv i f) *
                  MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) (pderiv k f)) = 0 := by
                rw [eval_zero_eq_coeff, eval_zero_eq_coeff]
                rw [hci0]
                ring
              have hle0 : MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) f *
                  MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) (pderiv k (pderiv i f)) ≤ 0 := by
                calc
                  MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) f *
                      MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) (pderiv k (pderiv i f))
                      ≤ c * (MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) (pderiv i f) *
                          MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) (pderiv k f)) := by
                        simpa [pderivL] using hineq
                  _ = 0 := hRHS
              exact (not_lt_of_ge hle0) hLHS
            · -- otherwise (0, e_i, β - e_k) is a bad triple for ∂_k f
              have hmem1 : (0 : Fin n →₀ ℕ) ∈ (pderiv k f).support := by
                rw [mem_support_pderiv]
                simpa using hek
              have hmem2 : e i ∉ (pderiv k f).support := by
                intro hm
                have : e i + e k ∈ f.support := (mem_support_pderiv k f (e i)).mp hm
                exact heik this
              have hmem3 : β - e k ∈ (pderiv k f).support := by
                have hβk0 : β k ≠ 0 := by omega
                rw [mem_support_pderiv_sub k f β hβk0]
                exact hβ
              have hord1 : ∀ x : Fin n, (0 : Fin n →₀ ℕ) x ≤ (e i) x := fun x => Nat.zero_le _
              have hord2 : ∀ x : Fin n, (e i) x ≤ (β - e k) x := by
                intro x
                by_cases hxk : x = k
                · subst x
                  have hxi : (e i) k = 0 := by simp [e, hik]
                  rw [hxi]
                  exact Nat.zero_le _
                · have hβx : (β - e k) x = β x := by simp [e, hxk]
                  rw [hβx]
                  by_cases hxi : x = i
                  · subst x
                    simpa [e] using hβi1
                  · have hx0 : (e i) x = 0 := by simp [e, hxi]
                    rw [hx0]
                    exact Nat.zero_le _
              exact contr k 0 (e i) (β - e k) ⟨hmem1, hmem3, hord1, hord2, hmem2⟩
        -- (4) elements of the support using coordinate `k` have degree at least |β|
        have hdegMin : ∀ (t : Fin n), 1 ≤ β t → ∀ δ : Fin n →₀ ℕ, δ ∈ f.support →
            δ t ≥ 1 → b0 ≤ degN δ := by
          intro t hβt δ hδ hδt
          by_contra hlt
          have hlt' : degN δ < b0 := by omega
          have hnoθ : ∀ θ : Fin n →₀ ℕ, (∀ x, θ x ≤ δ x) → θ ∈ f.support := by
            intro θ hθle
            by_contra hθn
            have hB0 : Bad f 0 θ δ := ⟨h0mem, hδ, (fun x => Nat.zero_le _), hθle, hθn⟩
            exact hmin1 (degN δ) hlt' ⟨0, θ, δ, hB0, rfl⟩
          have hekt : e t ∈ f.support := by
            apply hnoθ
            intro x
            by_cases hx : x = t
            · subst x
              simp [e]
              exact hδt
            · simp [e, hx]
          exact hnoUnit t hβt hekt
        -- (5) choose the two derivative directions and reach the ε-contradiction
        by_cases hmore : ∃ j : Fin n, j ≠ i ∧ 1 ≤ β j
        · rcases hmore with ⟨j, hji, hβj⟩
          let δ0 : Fin n →₀ ℕ := (β - e i) - e j
          have hzβi : β i ≠ 0 := by omega
          have hzβi_j : (β - e i) j ≠ 0 := by
            have hz' : (β - e i) j = β j := by simp [e, hji.symm]
            rw [hz']
            exact ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hβj)
          have hδ0supp : δ0 ∈ (pderiv j (pderiv i f)).support := by
            rw [mem_support_pderiv]
            rw [mem_support_pderiv]
            have h1 : δ0 + e j = β - e i := by
              dsimp [δ0]
              exact sub_single_add (β - e i) j hzβi_j
            have h2 : (δ0 + e j) + e i = β := by
              rw [h1]
              exact sub_single_add β i hzβi
            simpa [h2] using hβ
          have hδ0deg : degN δ0 = b0 - 2 := by
            have h1 : degN (β - e i) = b0 - 1 := by
              have := degN_sub_single β i hzβi
              rwa [hb0] at this
            have h2 : degN ((β - e i) - e j) = b0 - 1 - 1 := by
              have := degN_sub_single (β - e i) j hzβi_j
              rwa [h1] at this
            have hb0m : b0 - 1 - 1 = b0 - 2 := by omega
            dsimp [δ0]
            rw [h2, hb0m]
          have hb02 : 2 ≤ b0 := by
            have hpair : β i + β j ≤ degN β := by
              rw [degN_eq_sum]
              have hsub : (∑ x ∈ ({i, j} : Finset (Fin n)), β x) ≤ ∑ x : Fin n, β x :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({i, j} : Finset (Fin n)))
                  (by intro x hx1 hx2; exact Nat.zero_le _)
              have hsum : (∑ x ∈ ({i, j} : Finset (Fin n)), β x) = β i + β j := by
                rw [Finset.sum_pair (a := i) (b := j) hji.symm]
              rw [← hsum]
              exact hsub
            rw [← hb0]
            omega
          exact eps_contra_data c hc f hnnf hrf (β := β) (δ0 := δ0) i j b0 hb0 hb02
            hδ0deg hδ0supp h0mem hβ hβi1 hβj hdegMin
        · -- the single-coordinate case β = b e_i
          have hβi2 : 2 ≤ β i := by
            by_contra h
            have hβi1' : β i = 1 := by omega
            have hβeq : β = e i := by
              ext x
              by_cases hx : x = i
              · subst x
                simpa [e] using hβi1'
              · have hβx : β x = 0 := by
                  by_contra hc
                  have hx1 : 1 ≤ β x := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hc)
                  exact hmore ⟨x, hx, hx1⟩
                simp [e, hx, hβx]
            apply hγn
            have : e i ∈ f.support := by simpa [hβeq] using hβ
            simpa [hγei] using this
          let δ0 : Fin n →₀ ℕ := (β - e i) - e i
          have hzβii : (β - e i) i ≠ 0 := by
            have hz' : (β - e i) i = β i - 1 := by simp [e]
            rw [hz']
            omega
          have hδ0supp : δ0 ∈ (pderiv i (pderiv i f)).support := by
            rw [mem_support_pderiv]
            rw [mem_support_pderiv]
            have h1 : δ0 + e i = β - e i := by
              dsimp [δ0]
              exact sub_single_add (β - e i) i hzβii
            have h2 : (δ0 + e i) + e i = β := by
              rw [h1]
              exact sub_single_add β i (by omega)
            simpa [h2] using hβ
          have hδ0deg : degN δ0 = b0 - 2 := by
            have h1 : degN (β - e i) = b0 - 1 := by
              have := degN_sub_single β i (by omega)
              rwa [hb0] at this
            have h2 : degN ((β - e i) - e i) = b0 - 1 - 1 := by
              have := degN_sub_single (β - e i) i hzβii
              rwa [h1] at this
            have hb0m : b0 - 1 - 1 = b0 - 2 := by omega
            dsimp [δ0]
            rw [h2, hb0m]
          have hb02 : 2 ≤ b0 := by
            rw [← hb0]
            exact le_trans hβi2 (coord_le_degN β i)
          exact eps_contra_data c hc f hnnf hrf (β := β) (δ0 := δ0) i i b0 hb0 hb02
            hδ0deg hδ0supp h0mem hβ hβi1 hβi1 hdegMin
  have hno : ¬ ∃ α γ β : Fin n →₀ ℕ, Bad q α γ β :=
    hP (degPoly q) q rfl hnn hR
  intro α hαq β hβq γ hαγ hγβ
  by_contra hγn
  exact hno ⟨α, γ, β, hαq, hβq, hαγ, hγβ, hγn⟩


end

end Commons.Combinatorics.MvPolynomial