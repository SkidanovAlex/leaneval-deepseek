import Mathlib
import Submission.Commons.Combinatorics.MvPolynomial.interval_convex_of_rayleigh

open Finsupp MvPolynomial
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Commons.Combinatorics.MvPolynomial

noncomputable section

/-! # Augmentation property of the support of a (list-)Rayleigh polynomial

This file proves that if `q` is a (list-)`c`-Rayleigh polynomial with nonnegative
coefficients and nonzero constant term, then its support satisfies the augmentation
property: for `α, β` in the support with `|α| < |β|` there is `j` with
`α j < β j` and `α + e_j` again in the support.

The proof follows Brändén–Huh, "Lorentzian polynomials" (Lemma 2.22 (2) +
Lemma 2.23-style augmentation argument), using the interval convexity theorem
(`interval_convex_of_rayleigh`) for the support.
-/

/-! ## 1. The support of a Rayleigh polynomial is an order ideal below each point -/

/-- The support of a (list-)Rayleigh polynomial with nonzero constant term is
down-closed: `δ ∈ support` and `γ ≤ δ` coordinatewise force `γ ∈ support`. -/
lemma support_down_closed_of_rayleigh (n : ℕ) (c : ℝ) (hc : 0 < c)
    (q : MvPolynomial (Fin n) ℝ)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ q.coeff m)
    (h0 : q.coeff 0 ≠ 0)
    (hr : Ray c q) :
    ∀ δ : Fin n →₀ ℕ, δ ∈ q.support → ∀ γ : Fin n →₀ ℕ,
      (∀ k : Fin n, γ k ≤ δ k) → γ ∈ q.support := by
  intro δ hδ γ hγle
  have h0supp : (0 : Fin n →₀ ℕ) ∈ q.support := MvPolynomial.mem_support_iff.mpr h0
  exact interval_convex_of_rayleigh n c hc q hnn hr (0 : Fin n →₀ ℕ) h0supp δ hδ γ
    (fun k => Nat.zero_le _) hγle

/-- The zero exponent lies in the support exactly when the constant coefficient is nonzero. -/
lemma zero_mem_support_iff {σ : Type*} (p : MvPolynomial σ ℝ) :
    (0 : σ →₀ ℕ) ∈ p.support ↔ p.coeff 0 ≠ 0 := by
  rw [MvPolynomial.mem_support_iff]

/-! ## 2. Lists realising an exponent vector -/

/-- A list of variables containing each `i` exactly `m i` times. -/
def exponentList {σ : Type*} [DecidableEq σ] (m : σ →₀ ℕ) : List σ :=
  Multiset.toList (Finsupp.toMultiset m)

/-- `eSum` of a list equals the counting function of its multiset. -/
lemma eSum_eq_toFinsupp {σ : Type*} [DecidableEq σ] (l : List σ) :
    eSum l = Multiset.toFinsupp (l : Multiset σ) := by
  classical
  induction l with
  | nil =>
      simp [eSum, Multiset.toFinsupp_zero]
  | cons i l ih =>
      rw [eSum_cons, ih]
      have hlift : (↑(i :: l) : Multiset σ) = ({i} : Multiset σ) + (l : Multiset σ) := by
        simp
      rw [hlift, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]

/-- `eSum` of the list associated with `m` is `m`. -/
lemma eSum_exponentList {σ : Type*} [DecidableEq σ] (m : σ →₀ ℕ) :
    eSum (exponentList m) = m := by
  classical
  rw [eSum_eq_toFinsupp]
  simp [exponentList, Finsupp.toMultiset_toFinsupp]

/-- membership in the support of a derivative along the exponent `m` -/
lemma mem_support_pderiv_exp {σ : Type*} [DecidableEq σ] (m : σ →₀ ℕ)
    (p : MvPolynomial σ ℝ) (γ : σ →₀ ℕ) :
    γ ∈ (pderivL (exponentList m) p).support ↔ γ + m ∈ p.support := by
  classical
  rw [mem_support_pderivL]
  rw [eSum_exponentList m]

/-- evaluation at the zero vector of the derivative along `m` is nonzero
iff `m` itself is in the support -/
lemma eval_zero_pderiv_exp_ne_zero_iff {σ : Type*} [DecidableEq σ] (m : σ →₀ ℕ)
    (p : MvPolynomial σ ℝ) :
    MvPolynomial.eval (fun _ : σ => (0 : ℝ)) (pderivL (exponentList m) p) ≠ 0 ↔
      m ∈ p.support := by
  rw [eval_zero_eq_coeff]
  have h := coeff_zero_pderivL_ne_zero (exponentList m) p
  rwa [eSum_exponentList m] at h

/-! ## 3. Evaluation of polynomials with no `w_i`-terms is independent of `w_i` -/

/-- if no monomial of `p` contains variable `i`, evaluation does not depend on `w i` -/
lemma eval_indep_of_not_i {n : ℕ} (i : Fin n) (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m i = 0)
    (w v : Fin n → ℝ) (hwi : ∀ k : Fin n, k ≠ i → w k = v k) :
    MvPolynomial.eval w p = MvPolynomial.eval v p := by
  classical
  rw [← MvPolynomial.support_sum_monomial_coeff p]
  rw [MvPolynomial.eval_sum, MvPolynomial.eval_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
  congr 1
  apply Finsupp.prod_congr
  intro a ha
  by_cases hane : a = i
  · subst a
    have hmi : m i = 0 := hp m hm
    simp [hmi]
  · rw [hwi a hane]

/-! ## 4. Coefficients of derivatives of a polynomial along an exponent vector -/

/-- coefficient of `w^γ` in `p` is positive iff `γ ∈ p.support` (coefficients nonneg) -/
lemma coeff_pos_of_mem {σ : Type*} (p : MvPolynomial σ ℝ)
    (hnn : ∀ m : σ →₀ ℕ, 0 ≤ p.coeff m) {γ : σ →₀ ℕ} (hγ : γ ∈ p.support) :
    0 < p.coeff γ :=
  lt_of_le_of_ne' (hnn γ) (MvPolynomial.mem_support_iff.mp hγ)

/-! ## 5. The final Rayleigh contradiction -/

/-- Rayleigh contradiction lemma.  If `g` is `c`-Rayleigh with nonnegative
coefficients, its support is down-closed from `0` and contains `0, e_i, e_j,
e_j + e_k` but not `e_i + e_j` or `e_i + e_k` (with `j, k ≠ i`), then the
Rayleigh inequality fails along `w_i = t`, `w_l = 1` for `l ≠ i`, as `t → ∞`. -/
lemma rayleigh_final_contradiction (n : ℕ) (c : ℝ) (hc : 0 < c)
    (g : MvPolynomial (Fin n) ℝ) (hnng : ∀ m : Fin n →₀ ℕ, 0 ≤ g.coeff m)
    (hrg : Ray c g) (i j k : Fin n) (hji : j ≠ i) (hki : k ≠ i)
    (hdown : ∀ δ : Fin n →₀ ℕ, δ ∈ g.support → ∀ γ : Fin n →₀ ℕ,
       (∀ t : Fin n, γ t ≤ δ t) → γ ∈ g.support)
    (hgi : e i ∈ g.support) (hg0 : (0 : Fin n →₀ ℕ) ∈ g.support)
    (hgj : e j ∈ g.support)
    (hgjk : e j + e k ∈ g.support)
    (hij : e i + e j ∉ g.support) (hik : e i + e k ∉ g.support) : False := by
  classical
  -- (1) no monomial of `g` contains both `i` and `j`, or both `i` and `k`
  have hijm : ∀ δ : Fin n →₀ ℕ, δ ∈ g.support → 1 ≤ δ i → 1 ≤ δ j → False := by
    intro δ hδ hδi hδj
    have hle : ∀ t : Fin n, (e i + e j) t ≤ δ t := by
      intro t
      by_cases hti : t = i
      · subst t
        have h1 : (e i + e j) i = 1 := by
          simp [e, hji]
        rw [h1]
        exact hδi
      · by_cases htj : t = j
        · subst t
          have h1 : (e i + e j) j = 1 := by
            simp [e, hti]
          rw [h1]
          exact hδj
        · have hz : (e i + e j) t = 0 := by
            simp [e, hti, htj]
          rw [hz]
          exact Nat.zero_le _
    have hin : e i + e j ∈ g.support := hdown δ hδ (e i + e j) hle
    exact hij hin
  have hikm : ∀ δ : Fin n →₀ ℕ, δ ∈ g.support → 1 ≤ δ i → 1 ≤ δ k → False := by
    intro δ hδ hδi hδk
    have hle : ∀ t : Fin n, (e i + e k) t ≤ δ t := by
      intro t
      by_cases hti : t = i
      · subst t
        have h1 : (e i + e k) i = 1 := by
          simp [e, hki]
        rw [h1]
        exact hδi
      · by_cases htk : t = k
        · subst t
          have h1 : (e i + e k) k = 1 := by
            simp [e, hti]
          rw [h1]
          exact hδk
        · have hz : (e i + e k) t = 0 := by
            simp [e, hti, htk]
          rw [hz]
          exact Nat.zero_le _
    have hin : e i + e k ∈ g.support := hdown δ hδ (e i + e k) hle
    exact hik hin
  -- (2) the derivatives `∂_j g`, `∂_k g`, `∂_k∂_j g` have no monomials in `w_i`
  have hnoi_j : ∀ m : Fin n →₀ ℕ, m ∈ (pderiv j g).support → m i = 0 := by
    intro m hm
    have hδ : m + e j ∈ g.support := (mem_support_pderiv j g m).mp hm
    by_contra hz
    have hmi : 1 ≤ m i := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hz)
    have hδi : 1 ≤ (m + e j) i := by
      rw [Finsupp.add_apply]
      have hej : (e j) i = 0 := by simp [e, hji]
      rw [hej, add_zero]
      exact hmi
    have hδj : 1 ≤ (m + e j) j := by
      rw [Finsupp.add_apply]
      have hej : (e j) j = 1 := by simp [e]
      rw [hej]
      omega
    exact hijm (m + e j) hδ hδi hδj
  have hnoi_k : ∀ m : Fin n →₀ ℕ, m ∈ (pderiv k g).support → m i = 0 := by
    intro m hm
    have hδ : m + e k ∈ g.support := (mem_support_pderiv k g m).mp hm
    by_contra hz
    have hmi : 1 ≤ m i := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hz)
    have hδi : 1 ≤ (m + e k) i := by
      rw [Finsupp.add_apply]
      have hek : (e k) i = 0 := by simp [e, hki]
      rw [hek, add_zero]
      exact hmi
    have hδk : 1 ≤ (m + e k) k := by
      rw [Finsupp.add_apply]
      have hek : (e k) k = 1 := by simp [e]
      rw [hek]
      omega
    exact hikm (m + e k) hδ hδi hδk
  have hnoi_jk : ∀ m : Fin n →₀ ℕ, m ∈ (pderiv k (pderiv j g)).support → m i = 0 := by
    intro m hm
    have hm1 : m + e k ∈ (pderiv j g).support := (mem_support_pderiv k (pderiv j g) m).mp hm
    have hδ : (m + e k) + e j ∈ g.support := (mem_support_pderiv j g (m + e k)).mp hm1
    by_contra hz
    have hmi : 1 ≤ m i := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hz)
    have hδi : 1 ≤ ((m + e k) + e j) i := by
      rw [Finsupp.add_apply, Finsupp.add_apply]
      have hej : (e j) i = 0 := by simp [e, hji]
      have hek : (e k) i = 0 := by simp [e, hki]
      rw [hek, hej, add_zero, add_zero]
      exact hmi
    have hδj : 1 ≤ ((m + e k) + e j) j := by
      rw [Finsupp.add_apply, Finsupp.add_apply]
      have hej : (e j) j = 1 := by simp [e]
      rw [add_assoc]
      have h1 : m j + e k j + 1 ≥ 1 := by omega
      rw [hej]
      omega
    exact hijm ((m + e k) + e j) hδ hδi hδj
  -- (3) constant evaluations
  let w1 : Fin n → ℝ := fun _ => 1
  let wt : ℝ → Fin n → ℝ := fun t r => if r = i then t else 1
  let C : ℝ := MvPolynomial.eval w1 (pderiv k (pderiv j g))
  let E1 : ℝ := MvPolynomial.eval w1 (pderiv j g)
  let E2 : ℝ := MvPolynomial.eval w1 (pderiv k g)
  have hw1 : ∀ x : Fin n, 0 ≤ w1 x := by intro x; simp [w1]
  have hC_pos : 0 < C := by
    dsimp [C]
    have hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ (pderiv k (pderiv j g)).coeff m :=
      coeff_pderiv_nonneg k (pderiv j g) (coeff_pderiv_nonneg j g hnng)
    have h0supp : (0 : Fin n →₀ ℕ) ∈ (pderiv k (pderiv j g)).support := by
      rw [mem_support_pderiv, mem_support_pderiv]
      simpa [add_assoc, add_comm, add_left_comm] using hgjk
    have hc0 : 0 < (pderiv k (pderiv j g)).coeff 0 := coeff_pos_of_mem _ hnn h0supp
    have hle := eval_ge_term (pderiv k (pderiv j g)) hnn (w := w1) hw1 (0 : Fin n →₀ ℕ) h0supp
    have hprod : (∏ i : Fin n, w1 i ^ (0 : Fin n →₀ ℕ) i) = 1 := by simp [w1]
    rw [hprod] at hle
    nlinarith
  have hE1_pos : 0 < E1 := by
    dsimp [E1]
    have hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ (pderiv j g).coeff m := coeff_pderiv_nonneg j g hnng
    have h0supp : (0 : Fin n →₀ ℕ) ∈ (pderiv j g).support := by
      rw [mem_support_pderiv]
      simpa using hgj
    have hc0 : 0 < (pderiv j g).coeff 0 := coeff_pos_of_mem _ hnn h0supp
    have hle := eval_ge_term (pderiv j g) hnn (w := w1) hw1 (0 : Fin n →₀ ℕ) h0supp
    have hprod : (∏ i : Fin n, w1 i ^ (0 : Fin n →₀ ℕ) i) = 1 := by simp [w1]
    rw [hprod] at hle
    nlinarith
  have hE2_pos : 0 < E2 := by
    dsimp [E2]
    have hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ (pderiv k g).coeff m := coeff_pderiv_nonneg k g hnng
    have hm_supp : e j ∈ (pderiv k g).support := by
      rw [mem_support_pderiv]
      simpa [add_comm] using hgjk
    have hc0 : 0 < (pderiv k g).coeff (e j) := coeff_pos_of_mem _ hnn hm_supp
    have hle := eval_ge_term (pderiv k g) hnn (w := w1) hw1 (e j) hm_supp
    have hprod : (∏ i : Fin n, w1 i ^ (e j) i) = 1 := by
      rw [← Finsupp.prod_pow]
      simp [e, w1]
    rw [hprod] at hle
    have hprodpos : 0 < (pderiv k g).coeff (e j) * 1 := by nlinarith
    nlinarith
  -- (4) independence of the three evaluations from `t`
  have hC_ind : ∀ t : ℝ, MvPolynomial.eval (wt t) (pderiv k (pderiv j g)) = C := by
    intro t
    dsimp [C]
    exact eval_indep_of_not_i i (pderiv k (pderiv j g)) hnoi_jk (wt t) w1
      (by intro r hr; simp [wt, w1, hr])
  have hE1_ind : ∀ t : ℝ, MvPolynomial.eval (wt t) (pderiv j g) = E1 := by
    intro t
    dsimp [E1]
    exact eval_indep_of_not_i i (pderiv j g) hnoi_j (wt t) w1
      (by intro r hr; simp [wt, w1, hr])
  have hE2_ind : ∀ t : ℝ, MvPolynomial.eval (wt t) (pderiv k g) = E2 := by
    intro t
    dsimp [E2]
    exact eval_indep_of_not_i i (pderiv k g) hnoi_k (wt t) w1
      (by intro r hr; simp [wt, w1, hr])
  -- (5) the growth bound on `g` along `w_i = t`
  let A : ℝ := g.coeff (e i)
  have hA_pos : 0 < A := coeff_pos_of_mem g hnng hgi
  have hgrow : ∀ t : ℝ, 0 ≤ t → A * t ≤ MvPolynomial.eval (wt t) g := by
    intro t ht
    have hw : ∀ x : Fin n, 0 ≤ wt t x := by
      intro x
      by_cases hxi : x = i
      · subst x
        simp [wt, ht]
      · simp [wt, hxi]
    have hle := eval_ge_term g hnng (w := wt t) hw (e i) hgi
    have hprod : (∏ x : Fin n, wt t x ^ (e i x)) = t := by
      rw [← Finsupp.prod_pow]
      simp [e, wt]
    rw [hprod] at hle
    dsimp [A]
    nlinarith
  -- (6) the Rayleigh inequality along `w_i = t`
  have hineq : ∀ t : ℝ, 0 ≤ t →
      MvPolynomial.eval (wt t) g * C ≤ c * E1 * E2 := by
    intro t ht
    have hw : ∀ x : Fin n, 0 ≤ wt t x := by
      intro x
      by_cases hxi : x = i
      · subst x
        simp [wt, ht]
      · simp [wt, hxi]
    have h := hrg [] j k (wt t) hw
    have h1 : MvPolynomial.eval (wt t) (pderivL [] g) = MvPolynomial.eval (wt t) g := by simp
    have h2 : MvPolynomial.eval (wt t) (pderivL (j :: k :: []) g) =
        MvPolynomial.eval (wt t) (pderiv k (pderiv j g)) := by
      simp [pderivL]
    have h3 : MvPolynomial.eval (wt t) (pderivL (j :: []) g) =
        MvPolynomial.eval (wt t) (pderiv j g) := by simp [pderivL]
    have h4 : MvPolynomial.eval (wt t) (pderivL (k :: []) g) =
        MvPolynomial.eval (wt t) (pderiv k g) := by simp [pderivL]
    rw [h1, h2, h3, h4] at h
    rw [hC_ind t, hE1_ind t, hE2_ind t] at h
    simpa [mul_assoc] using h
  -- (7) choose `t` large enough
  let t : ℝ := (c * E1 * E2) / (A * C) + 1
  have ht : 0 ≤ t := by
    dsimp [t]
    have hnum : 0 ≤ c * E1 * E2 := by positivity
    have hden : 0 < A * C := mul_pos hA_pos hC_pos
    positivity
  have htC : A * C * t > c * E1 * E2 := by
    dsimp [t]
    have hAC : A * C ≠ 0 := by positivity
    have hACpos : 0 < A * C := mul_pos hA_pos hC_pos
    field_simp [hAC]
    nlinarith
  have hineqt := hineq t ht
  have hgrowt := hgrow t ht
  have hle1 : A * t * C ≤ MvPolynomial.eval (wt t) g * C :=
    mul_le_mul_of_nonneg_right hgrowt (le_of_lt hC_pos)
  have hle2 : A * t * C ≤ c * E1 * E2 := le_trans hle1 hineqt
  have hgt : c * E1 * E2 < A * t * C := by
    have htmp : A * C * t = A * t * C := by ring
    nlinarith
  nlinarith


/-- The support of a (list-)Rayleigh polynomial `q` with nonnegative coefficients and nonzero
constant term satisfies the augmentation property: for `α, β` in the support with `|α| < |β|`
(totals of the coordinates), some coordinate `j` has `α j < β j` and `α + e_j` in the support. -/
theorem augmentation_of_rayleigh (n : ℕ) (c : ℝ) (hc : 0 < c)
    (q : MvPolynomial (Fin n) ℝ)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ q.coeff m)
    (h0 : q.coeff 0 ≠ 0)
    (hr : ∀ (l : List (Fin n)) (i j : Fin n) (w : Fin n → ℝ),
      (∀ k : Fin n, 0 ≤ w k) →
        MvPolynomial.eval w (l.foldl (fun q i => MvPolynomial.pderiv i q) q) *
            MvPolynomial.eval w ((i :: j :: l).foldl (fun q i => MvPolynomial.pderiv i q) q) ≤
          c * (MvPolynomial.eval w ((i :: l).foldl (fun q i => MvPolynomial.pderiv i q) q) *
            MvPolynomial.eval w ((j :: l).foldl (fun q i => MvPolynomial.pderiv i q) q))) :
    ∀ α : Fin n →₀ ℕ, α ∈ q.support → ∀ β : Fin n →₀ ℕ, β ∈ q.support →
      (∑ i : Fin n, α i) < (∑ i : Fin n, β i) →
      ∃ j : Fin n, α j < β j ∧ α + Finsupp.single j 1 ∈ q.support := by
  classical
  have hR : Ray c q := by
    simpa [Ray, pderivL] using hr
  -- a "failing pair": both in the support, first has smaller degree, and no coordinate can be
  -- added to the first one while staying in the support
  let Failing : MvPolynomial (Fin n) ℝ → (Fin n →₀ ℕ) → (Fin n →₀ ℕ) → Prop :=
    fun f a b => a ∈ f.support ∧ b ∈ f.support ∧ degN a < degN b ∧
      ∀ j : Fin n, a j < b j → a + e j ∉ f.support
  -- main strong induction on the degree of the polynomial
  have hP : ∀ d : ℕ, ∀ (f : MvPolynomial (Fin n) ℝ), degPoly f = d →
      (∀ m : Fin n →₀ ℕ, 0 ≤ f.coeff m) → Ray c f → f.coeff 0 ≠ 0 →
      ¬ ∃ a b : Fin n →₀ ℕ, Failing f a b := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ihD =>
        intro f hdeg hnnf hrf h0f hex
        rcases hex with ⟨a, b, hF⟩
        rcases hF with ⟨ha, hb, hlt, hfail⟩
        -- (0) basic consequences
        have h0supp : (0 : Fin n →₀ ℕ) ∈ f.support := MvPolynomial.mem_support_iff.mpr h0f
        have hdown : ∀ δ : Fin n →₀ ℕ, δ ∈ f.support → ∀ γ : Fin n →₀ ℕ,
            (∀ t : Fin n, γ t ≤ δ t) → γ ∈ f.support :=
          support_down_closed_of_rayleigh n c hc f hnnf h0f hrf
        -- nested strong induction on degN a
        have hC : ∀ (m : ℕ) (a b : Fin n →₀ ℕ), Failing f a b → degN a = m → False := by
          intro m
          induction m using Nat.strong_induction_on with
          | h m ihA =>
              intro a b hF' hdm
              rcases hF' with ⟨ha, hb, hlt, hfail⟩
              -- (1) a ≠ 0
              have ha_ne0 : a ≠ 0 := by
                intro haz
                subst a
                have hz0 : degN (0 : Fin n →₀ ℕ) = 0 := by simp [degN]
                have hb_ne0 : b ≠ 0 := by
                  intro hbz
                  have : degN b = 0 := by rw [hbz]; simp [degN]
                  omega
                have hexb : ∃ j : Fin n, 1 ≤ b j := by
                  by_contra hnone
                  apply hb_ne0
                  ext j
                  by_contra hc
                  exact hnone ⟨j, Nat.succ_le_of_lt (Nat.pos_of_ne_zero hc)⟩
                rcases hexb with ⟨j, hbj⟩
                have hfailj : e j ∉ f.support := by
                  have h0lt : (0 : ℕ) < b j := by omega
                  exact (by simpa using hfail j (by simpa using h0lt))
                have hejle : ∀ t : Fin n, (e j) t ≤ b t := by
                  intro t
                  by_cases htj : t = j
                  · subst t
                    have : (e j) j = 1 := by simp [e]
                    rw [this]
                    exact hbj
                  · have : (e j) t = 0 := by simp [e, htj]
                    rw [this]
                    exact Nat.zero_le _
                have hej : e j ∈ f.support := hdown b hb (e j) hejle
                exact hfailj hej
              have hdegpos : 1 ≤ degN a := degN_pos_of_ne_zero a ha_ne0
              have hexa : ∃ i : Fin n, 1 ≤ a i := by
                by_contra hnone
                apply ha_ne0
                ext i
                by_contra hc
                exact hnone ⟨i, Nat.succ_le_of_lt (Nat.pos_of_ne_zero hc)⟩
              rcases hexa with ⟨i, hai⟩
              have haine : a i ≠ 0 := by omega
              -- (2) coordinate i does not occur in b (otherwise contraction gives a
              -- smaller-degree counterexample)
              have hbi0 : b i = 0 := by
                by_contra hbiz
                have hbi : 1 ≤ b i := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hbiz)
                have hα' : a - e i ∈ (pderiv i f).support := by
                  rw [mem_support_pderiv_sub i f a haine]
                  exact ha
                have hβ' : b - e i ∈ (pderiv i f).support := by
                  rw [mem_support_pderiv_sub i f b (by omega)]
                  exact hb
                have hlt' : degN (a - e i) < degN (b - e i) := by
                  rw [degN_sub_single a i haine, degN_sub_single b i (by omega)]
                  omega
                have hfail' : ∀ x : Fin n, (a - e i) x < (b - e i) x →
                    (a - e i) + e x ∉ (pderiv i f).support := by
                  intro x hx hmem
                  have hmemf : ((a - e i) + e x) + e i ∈ f.support :=
                    (mem_support_pderiv i f ((a - e i) + e x)).mp hmem
                  have hsum : ((a - e i) + e x) + e i = a + e x := by
                    calc
                      ((a - e i) + e x) + e i = (a - e i) + (e x + e i) := by ac_rfl
                      _ = ((a - e i) + e i) + e x := by ac_rfl
                      _ = a + e x := by rw [sub_single_add a i haine]
                  have hax : a x < b x := by
                    by_cases hxi : x = i
                    · subst x
                      have h1 : (a - e i) i = a i - 1 := by simp [e]
                      have h2 : (b - e i) i = b i - 1 := by simp [e]
                      have hx' : a i - 1 < b i - 1 := by simpa [h1, h2] using hx
                      omega
                    · have h1 : (a - e i) x = a x := by simp [e, hxi]
                      have h2 : (b - e i) x = b x := by simp [e, hxi]
                      have hx' : a x < b x := by simpa [h1, h2] using hx
                      omega
                  have hfailx : a + e x ∉ f.support := hfail x hax
                  have hmemf' : a + e x ∈ f.support := by simpa [hsum] using hmemf
                  exact hfailx hmemf'
                have hne1 : pderiv i f ≠ 0 := by
                  intro hz
                  simp [hz] at hα'
                have hdeg1 : degPoly (pderiv i f) < degPoly f := degPoly_pderiv_lt i f hne1
                have hei : e i ∈ f.support := by
                  have hle : ∀ t : Fin n, (e i) t ≤ a t := by
                    intro t
                    by_cases hti : t = i
                    · subst t
                      have : (e i) i = 1 := by simp [e]
                      rw [this]
                      exact hai
                    · have : (e i) t = 0 := by simp [e, hti]
                      rw [this]
                      exact Nat.zero_le _
                  exact hdown a ha (e i) hle
                have h0g1 : (pderiv i f).coeff 0 ≠ 0 := by
                  rw [coeff_pderiv]
                  have hc : f.coeff (e i) ≠ 0 := MvPolynomial.mem_support_iff.mp hei
                  exact mul_ne_zero (by simpa using hc) (by norm_num)
                have hno1 : ¬ ∃ a2 b2 : Fin n →₀ ℕ, Failing (pderiv i f) a2 b2 :=
                  ihD (degPoly (pderiv i f)) (by omega) (pderiv i f) rfl
                    (coeff_pderiv_nonneg i f hnnf) (ray_contraction_single c i f hrf) h0g1
                exact hno1 ⟨a - e i, b - e i, hα', hβ', hlt', hfail'⟩
              -- (3) a - e_i ∈ support, and (a - e_i, b) is not a failing pair
              have ham : a - e i ∈ f.support := hdown a ha (a - e i) (by
                intro t
                exact sub_e_le_self a i t)
              have hltm : degN (a - e i) < degN b := by
                rw [degN_sub_single a i haine]
                omega
              have hnotF : ¬ Failing f (a - e i) b := by
                intro hF'
                have hdm' : degN (a - e i) = m - 1 := by
                  rw [degN_sub_single a i haine, hdm]
                have hlt' : m - 1 < m := by omega
                exact ihA (m - 1) hlt' (a - e i) b hF' hdm'
              have hexj : ∃ x : Fin n, (a - e i) x < b x ∧ (a - e i) + e x ∈ f.support := by
                by_contra hnone
                have hfailall : ∀ x : Fin n, (a - e i) x < b x → (a - e i) + e x ∉ f.support := by
                  intro x hx hmem
                  exact hnone ⟨x, hx, hmem⟩
                exact hnotF ⟨ham, hb, hltm, hfailall⟩
              rcases hexj with ⟨j, hjj, hwj⟩
              have hji : j ≠ i := by
                intro hz
                subst j
                have h1 : (a - e i) i = a i - 1 := by simp [e]
                have hx' : a i - 1 < b i := by simpa [h1] using hjj
                omega
              have haj : a j < b j := by
                have h1 : (a - e i) j = a j := by simp [e, hji]
                have hx' : a j < b j := by simpa [h1] using hjj
                exact hx'
              have hfailj : a + e j ∉ f.support := hfail j haj
              have hbj1 : 1 ≤ b j := by omega
              -- (4) ((a - e_i) + e_j, b) is not a failing pair
              have hmemj : (a - e i) + e j ∈ f.support := hwj
              have hltj : degN ((a - e i) + e j) < degN b := by
                rw [degN_add, degN_sub_single a i haine, degN_e]
                have hdeg : degN a - 1 + 1 = degN a := by omega
                omega
              have hnotFj : ¬ Failing f ((a - e i) + e j) b := by
                intro hFj
                have hα2 : a - e i ∈ (pderiv j f).support := by
                  rw [mem_support_pderiv]
                  simpa [add_comm, add_assoc] using hwj
                have hβ2 : b - e j ∈ (pderiv j f).support := by
                  rw [mem_support_pderiv_sub j f b (by omega)]
                  exact hb
                have hlt2 : degN (a - e i) < degN (b - e j) := by
                  rw [degN_sub_single a i haine, degN_sub_single b j (by omega)]
                  omega
                have hfail2 : ∀ x : Fin n, (a - e i) x < (b - e j) x →
                    (a - e i) + e x ∉ (pderiv j f).support := by
                  intro x hx hmem
                  have hmemf : ((a - e i) + e x) + e j ∈ f.support :=
                    (mem_support_pderiv j f ((a - e i) + e x)).mp hmem
                  have hsum : ((a - e i) + e x) + e j = ((a - e i) + e j) + e x := by ac_rfl
                  have hx2 : ((a - e i) + e j) x < b x := by
                    by_cases hxj : x = j
                    · subst x
                      have h1 : ((a - e i) + e j) j = (a - e i) j + 1 := by simp [e]
                      have h2 : (b - e j) j = b j - 1 := by simp [e]
                      have hx' : (a - e i) j < b j - 1 := by simpa [h2] using hx
                      rw [h1]
                      omega
                    · have h1 : ((a - e i) + e j) x = (a - e i) x := by simp [e, hxj]
                      have h2 : (b - e j) x = b x := by simp [e, hxj]
                      rw [h1]
                      rw [h2] at hx
                      exact hx
                  have hfailx : ((a - e i) + e j) + e x ∉ f.support := hFj.2.2.2 x hx2
                  have hmemf' : ((a - e i) + e j) + e x ∈ f.support := by simpa [hsum] using hmemf
                  exact hfailx hmemf'
                have hne2 : pderiv j f ≠ 0 := by
                  intro hz
                  simp [hz] at hα2
                have hdeg2 : degPoly (pderiv j f) < degPoly f := degPoly_pderiv_lt j f hne2
                have hej : e j ∈ f.support := by
                  have hle : ∀ t : Fin n, (e j) t ≤ b t := by
                    intro t
                    by_cases htj : t = j
                    · subst t
                      have : (e j) j = 1 := by simp [e]
                      rw [this]
                      exact hbj1
                    · have : (e j) t = 0 := by simp [e, htj]
                      rw [this]
                      exact Nat.zero_le _
                  exact hdown b hb (e j) hle
                have h0g2 : (pderiv j f).coeff 0 ≠ 0 := by
                  rw [coeff_pderiv]
                  have hc : f.coeff (e j) ≠ 0 := MvPolynomial.mem_support_iff.mp hej
                  exact mul_ne_zero (by simpa using hc) (by norm_num)
                have hno2 : ¬ ∃ a2 b2 : Fin n →₀ ℕ, Failing (pderiv j f) a2 b2 :=
                  ihD (degPoly (pderiv j f)) (by omega) (pderiv j f) rfl
                    (coeff_pderiv_nonneg j f hnnf) (ray_contraction_single c j f hrf) h0g2
                exact hno2 ⟨a - e i, b - e j, hα2, hβ2, hlt2, hfail2⟩
              have hexk : ∃ x : Fin n, ((a - e i) + e j) x < b x ∧
                  ((a - e i) + e j) + e x ∈ f.support := by
                by_contra hnone
                have hfailall : ∀ x : Fin n, ((a - e i) + e j) x < b x →
                    ((a - e i) + e j) + e x ∉ f.support := by
                  intro x hx hmem
                  exact hnone ⟨x, hx, hmem⟩
                exact hnotFj ⟨hmemj, hb, hltj, hfailall⟩
              rcases hexk with ⟨k, hkk, hwk⟩
              have hki : k ≠ i := by
                intro hz
                subst k
                have h1 : ((a - e i) + e j) i = (a - e i) i := by simp [e, hji]
                have h2 : (a - e i) i = a i - 1 := by simp [e]
                have hx' : a i - 1 < b i := by simpa [h1, h2] using hkk
                omega
              have hak : a k < b k := by
                by_cases hkj : k = j
                · subst k
                  have h1 : ((a - e i) + e j) j = a j + 1 := by
                    simp [e, hji]
                  have hx' : a j + 1 < b j := by simpa [h1] using hkk
                  omega
                · have h1 : ((a - e i) + e j) k = a k := by
                    simp [e, hki, hkj]
                  have hx' : a k < b k := by simpa [h1] using hkk
                  exact hx'
              have hfailk : a + e k ∉ f.support := hfail k hak
              -- (5) form the derivative g := ∂^(a - e_i) f and collect its support data
              let la : List (Fin n) := exponentList (a - e i)
              let g : MvPolynomial (Fin n) ℝ := pderivL la f
              have hRg : Ray c g := by
                dsimp [g]
                exact ray_contraction c la f hrf
              have hnng : ∀ m : Fin n →₀ ℕ, 0 ≤ g.coeff m := by
                dsimp [g]
                exact coeff_pderivL_nonneg la f hnnf
              have h0g_supp : (0 : Fin n →₀ ℕ) ∈ g.support := by
                dsimp [g]
                rw [mem_support_pderiv_exp]
                simpa using ham
              have h0g : g.coeff 0 ≠ 0 := by
                exact (zero_mem_support_iff g).mp h0g_supp
              have hdownG : ∀ δ : Fin n →₀ ℕ, δ ∈ g.support → ∀ γ : Fin n →₀ ℕ,
                  (∀ t : Fin n, γ t ≤ δ t) → γ ∈ g.support :=
                support_down_closed_of_rayleigh n c hc g hnng h0g hRg
              have hgi : e i ∈ g.support := by
                dsimp [g]
                rw [mem_support_pderiv_exp]
                have hsum : e i + (a - e i) = a := by
                  rw [add_comm]
                  exact sub_single_add a i haine
                simpa [hsum] using ha
              have hgj : e j ∈ g.support := by
                dsimp [g]
                rw [mem_support_pderiv_exp]
                have hsum : e j + (a - e i) = (a - e i) + e j := by ac_rfl
                simpa [hsum] using hwj
              have hgjk : e j + e k ∈ g.support := by
                dsimp [g]
                rw [mem_support_pderiv_exp]
                have hsum : (e j + e k) + (a - e i) = ((a - e i) + e j) + e k := by ac_rfl
                simpa [hsum] using hwk
              have hijg : e i + e j ∉ g.support := by
                intro hmem
                dsimp [g] at hmem
                rw [mem_support_pderiv_exp] at hmem
                have hia : e i + (a - e i) = a := by
                  rw [add_comm]
                  exact sub_single_add a i haine
                have hsum : (e i + e j) + (a - e i) = a + e j := by
                  calc
                    (e i + e j) + (a - e i) = e j + (e i + (a - e i)) := by ac_rfl
                    _ = e j + a := by rw [hia]
                    _ = a + e j := by ac_rfl
                exact hfailj (by simpa [hsum] using hmem)
              have hikg : e i + e k ∉ g.support := by
                intro hmem
                dsimp [g] at hmem
                rw [mem_support_pderiv_exp] at hmem
                have hsum : (e i + e k) + (a - e i) = a + e k := by
                  calc
                    (e i + e k) + (a - e i) = (e k + e i) + (a - e i) := by ac_rfl
                    _ = e k + (e i + (a - e i)) := by ac_rfl
                    _ = e k + a := by
                      have h1 : e i + (a - e i) = a := by
                        rw [add_comm]
                        exact sub_single_add a i haine
                      rw [h1]
                    _ = a + e k := by ac_rfl
                exact hfailk (by simpa [hsum] using hmem)
              exact rayleigh_final_contradiction n c hc g hnng hRg i j k hji hki hdownG hgi
                h0g_supp hgj hgjk hijg hikg
        -- finish the nested induction
        exact hC (degN a) a b ⟨ha, hb, hlt, hfail⟩ rfl
  -- the theorem follows from the degree induction
  intro α hαq β hβq hsize
  have hltdeg : degN α < degN β := by
    rw [← degN_eq_sum α, ← degN_eq_sum β] at hsize
    exact hsize
  have hnoFail : ¬ ∃ a b : Fin n →₀ ℕ, Failing q a b :=
    hP (degPoly q) q rfl hnn hR h0
  by_contra hconcl
  have hfailprop : ∀ j : Fin n, α j < β j → α + e j ∉ q.support := by
    intro j hj hmem
    exact hconcl ⟨j, hj, hmem⟩
  exact hnoFail ⟨α, β, hαq, hβq, hltdeg, hfailprop⟩

end
end Commons.Combinatorics.MvPolynomial
