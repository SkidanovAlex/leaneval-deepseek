import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

namespace Commons.Algebra.MvPolynomial

open Finsupp
open _root_.MvPolynomial
open scoped BigOperators

set_option autoImplicit false
noncomputable section

/-! ## Coeffwise-nonnegative polynomials over `ℝ`

We build a small API for polynomials all of whose coefficients are nonnegative.
Everything is expressed through the predicate `CoeffN P : ∀ m, 0 ≤ P.coeff m`.
-/

/-- All coefficients of `p` are nonnegative. -/
private def CoeffN {σ : Type*} (p : MvPolynomial σ ℝ) : Prop :=
  ∀ m : σ →₀ ℕ, 0 ≤ p.coeff m

private lemma coeffN_zero {σ : Type*} : CoeffN (0 : MvPolynomial σ ℝ) := by
  intro m
  simp

private lemma coeffN_one {σ : Type*} : CoeffN (1 : MvPolynomial σ ℝ) := by
  classical
  intro m
  by_cases h : (0 : σ →₀ ℕ) = m
  · subst m
    simp
  · rw [MvPolynomial.coeff_one, if_neg h]

private lemma coeffN_C {σ : Type*} {r : ℝ} (hr : 0 ≤ r) : CoeffN (MvPolynomial.C r : MvPolynomial σ ℝ) := by
  classical
  intro m
  by_cases h : (0 : σ →₀ ℕ) = m
  · subst m
    simp [hr]
  · rw [MvPolynomial.coeff_C, if_neg h]

private lemma coeffN_X {σ : Type*} (i : σ) : CoeffN (MvPolynomial.X i : MvPolynomial σ ℝ) := by
  classical
  intro m
  by_cases h : Finsupp.single i 1 = m
  · subst m
    rw [MvPolynomial.coeff_X, if_pos rfl]
    norm_num
  · rw [MvPolynomial.coeff_X, if_neg h]

private lemma coeffN_add {σ : Type*} {P Q : MvPolynomial σ ℝ} (hP : CoeffN P) (hQ : CoeffN Q) :
    CoeffN (P + Q) := by
  intro m
  rw [MvPolynomial.coeff_add]
  exact add_nonneg (hP m) (hQ m)

private lemma coeffN_sum {σ ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ)
    (h : ∀ i ∈ s, CoeffN (f i)) : CoeffN (∑ i ∈ s, f i) := by
  intro m
  rw [MvPolynomial.coeff_sum]
  exact Finset.sum_nonneg (fun i hi => h i hi m)

private lemma coeffN_mul {σ : Type*} {P Q : MvPolynomial σ ℝ} (hP : CoeffN P) (hQ : CoeffN Q) :
    CoeffN (P * Q) := by
  classical
  intro m
  rw [MvPolynomial.coeff_mul]
  exact Finset.sum_nonneg (fun x hx => mul_nonneg (hP x.1) (hQ x.2))

private lemma coeffN_C_mul {σ : Type*} {r : ℝ} (hr : 0 ≤ r) {P : MvPolynomial σ ℝ} (hP : CoeffN P) :
    CoeffN (MvPolynomial.C r * P) := by
  intro m
  rw [MvPolynomial.coeff_C_mul]
  exact mul_nonneg hr (hP m)

private lemma coeffN_pow {σ : Type*} {P : MvPolynomial σ ℝ} (hP : CoeffN P) (k : ℕ) :
    CoeffN (P ^ k) := by
  induction k with
  | zero =>
      simpa using (coeffN_one (σ := σ))
  | succ k ih =>
      rw [pow_succ]
      exact coeffN_mul ih hP

private lemma coeffN_sub {σ : Type*} {P Q : MvPolynomial σ ℝ}
    (h : ∀ m : σ →₀ ℕ, Q.coeff m ≤ P.coeff m) : CoeffN (P - Q) := by
  intro m
  change 0 ≤ P.coeff m - Q.coeff m
  exact sub_nonneg.mpr (h m)

/-- If `P` and `Q` have nonnegative coefficients and `Q ≤ P` coefficientwise, then
`P ^ k - Q ^ k` has nonnegative coefficients. -/
private lemma coeffN_pow_sub_pow {σ : Type*} {P Q : MvPolynomial σ ℝ} (k : ℕ)
    (hPQ : CoeffN (P - Q)) (hP : CoeffN P) (hQ : CoeffN Q) : CoeffN (P ^ k - Q ^ k) := by
  induction k with
  | zero =>
      simpa using (coeffN_zero (σ := σ))
  | succ k ih =>
      rw [pow_succ, pow_succ]
      have h1 : CoeffN (P ^ k * (P - Q)) := coeffN_mul (coeffN_pow hP k) hPQ
      have h2 : CoeffN ((P ^ k - Q ^ k) * Q) := coeffN_mul ih hQ
      have hEq : P ^ k * P - Q ^ k * Q = P ^ k * (P - Q) + (P ^ k - Q ^ k) * Q := by
        ring
      rw [hEq]
      exact coeffN_add h1 h2

private lemma coeffN_prod {σ ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ)
    (h : ∀ i ∈ s, CoeffN (f i)) : CoeffN (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simpa using (coeffN_one (σ := σ))
  | insert i s his ih =>
      rw [Finset.prod_insert his]
      exact coeffN_mul (h i (Finset.mem_insert_self i s)) (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private lemma coeffN_prod_sub_prod {σ ι : Type*} (s : Finset ι) {f g : ι → MvPolynomial σ ℝ}
    (hfg : ∀ i ∈ s, CoeffN (f i - g i)) (hf : ∀ i ∈ s, CoeffN (f i))
    (hg : ∀ i ∈ s, CoeffN (g i)) : CoeffN (∏ i ∈ s, f i - ∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simpa using (coeffN_zero (σ := σ))
  | insert i s his ih =>
      rw [Finset.prod_insert his, Finset.prod_insert his]
      have hA : CoeffN (∏ j ∈ s, f j - ∏ j ∈ s, g j) := ih
        (fun j hj => hfg j (Finset.mem_insert_of_mem hj))
        (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (fun j hj => hg j (Finset.mem_insert_of_mem hj))
      have h1 : CoeffN (f i * (∏ j ∈ s, f j - ∏ j ∈ s, g j)) :=
        coeffN_mul (hf i (Finset.mem_insert_self i s)) hA
      have hB : CoeffN (∏ j ∈ s, g j) := coeffN_prod s g (fun j hj => hg j (Finset.mem_insert_of_mem hj))
      have h2 : CoeffN ((f i - g i) * ∏ j ∈ s, g j) :=
        coeffN_mul (hfg i (Finset.mem_insert_self i s)) hB
      have hEq : f i * (∏ j ∈ s, f j) - g i * (∏ j ∈ s, g j)
          = f i * (∏ j ∈ s, f j - ∏ j ∈ s, g j) + (f i - g i) * ∏ j ∈ s, g j := by
        ring
      rw [hEq]
      exact coeffN_add h1 h2

private lemma coeff_le_of_coeffN {σ : Type*} {P Q : MvPolynomial σ ℝ} (h : CoeffN (P - Q))
    (m : σ →₀ ℕ) : Q.coeff m ≤ P.coeff m := by
  have hh := h m
  change 0 ≤ P.coeff m - Q.coeff m at hh
  exact sub_nonneg.mp hh

/-! ## Weight identities -/

private lemma sum_eq_weight {ι : Type*} [Fintype ι] (m : ι →₀ ℕ) :
    (∑ i : ι, m i) = Finsupp.weight (1 : ι → ℕ) m := by
  rw [Finsupp.weight_apply]
  rw [Finsupp.sum_fintype]
  · simp
  · intro i
    rfl

private lemma weight_eq_sum_id {ι : Type*} [Fintype ι] (m : ι →₀ ℕ) :
    Finsupp.weight (1 : ι → ℕ) m = m.sum (fun (_ : ι) (k : ℕ) => k) := by
  rw [Finsupp.weight_apply]
  apply Finsupp.sum_congr
  intro i hi
  simp

/-! ## Substitution of linear forms with nonnegative data

For `a, b ≥ 0` put `y_i = C a * X i + C b * (∑ j, X j)`.  Since `y_i ≥ C b * (∑ j, X j)`
coefficientwise and both sides have nonnegative coefficients, the monomial image
`∏_i y_i ^ (v i)` dominates `(C b * (∑ j, X j)) ^ (weight 1 v)` coefficientwise.
-/

private lemma aeval_monomial_one_eq_prod {ι : Type*} [Fintype ι]
    (y : ι → MvPolynomial ι ℝ) (v : ι →₀ ℕ) :
    MvPolynomial.aeval (R := ℝ) y (monomial v 1) = ∏ i : ι, y i ^ (v i) := by
  rw [MvPolynomial.aeval_monomial]
  rw [Finsupp.prod_fintype]
  · simp
  · intro i
    exact pow_zero (y i)

private lemma coeffN_prod_linearSubst_sub_pow {ι : Type*} [Fintype ι]
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (v : ι →₀ ℕ) :
    CoeffN ((∏ i : ι, (C a * X i + C b * (∑ j : ι, X j : MvPolynomial ι ℝ)) ^ (v i)) -
        (C b * (∑ j : ι, X j : MvPolynomial ι ℝ)) ^ (Finsupp.weight (1 : ι → ℕ) v)) := by
  classical
  let S : MvPolynomial ι ℝ := ∑ j : ι, X j
  let y : ι → MvPolynomial ι ℝ := fun i => C a * X i + C b * S
  have hSnn : CoeffN S := by
    dsimp [S]
    simpa using (coeffN_sum (Finset.univ : Finset ι) (fun j : ι => X j) (fun j hj => coeffN_X j))
  have hCSnn : CoeffN (C b * S) := coeffN_C_mul hb hSnn
  have hyS (i : ι) : CoeffN (y i - C b * S) := by
    dsimp [y]
    rw [show C a * X i + C b * S - C b * S = C a * X i by ring]
    exact coeffN_C_mul ha (coeffN_X i)
  have hy (i : ι) : CoeffN (y i) := by
    dsimp [y]
    exact coeffN_add (coeffN_C_mul ha (coeffN_X i)) hCSnn
  have hmain : CoeffN (∏ i ∈ (Finset.univ : Finset ι), y i ^ (v i) -
      ∏ i ∈ (Finset.univ : Finset ι), (C b * S) ^ (v i)) := by
    apply coeffN_prod_sub_prod (s := (Finset.univ : Finset ι))
      (f := fun i : ι => y i ^ (v i)) (g := fun i : ι => (C b * S) ^ (v i))
    · intro i hi
      exact coeffN_pow_sub_pow (v i) (hyS i) (hy i) hCSnn
    · intro i hi
      exact coeffN_pow (hy i) (v i)
    · intro i hi
      exact coeffN_pow hCSnn (v i)
  have hP : (∏ i : ι, (C a * X i + C b * (∑ j : ι, X j)) ^ (v i)) =
      ∏ i ∈ (Finset.univ : Finset ι), y i ^ (v i) := by
    dsimp [y]
  have hQ : (∏ i ∈ (Finset.univ : Finset ι), (C b * S) ^ (v i)) =
      (C b * (∑ j : ι, X j)) ^ (Finsupp.weight (1 : ι → ℕ) v) := by
    calc
      (∏ i ∈ (Finset.univ : Finset ι), (C b * S) ^ (v i))
          = (C b * S) ^ (∑ i : ι, v i) := by
            rw [Finset.prod_pow_eq_pow_sum]
      _ = (C b * S) ^ (Finsupp.weight (1 : ι → ℕ) v) := by rw [sum_eq_weight v]
      _ = (C b * (∑ j : ι, X j)) ^ (Finsupp.weight (1 : ι → ℕ) v) := by rfl
  rw [hP]
  rw [← hQ]
  exact hmain

/-! ## The main statement -/

theorem subst_coeff_pos (n d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m) (hp0 : p ≠ 0)
    (hpdeg : MvPolynomial.IsHomogeneous p d)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (m : Fin n →₀ ℕ)
    (hm : Finsupp.weight (1 : Fin n → ℕ) m = d) :
    0 < (MvPolynomial.aeval (fun j : Fin n =>
      MvPolynomial.C (1 - θ) * MvPolynomial.X j +
        MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i)) p).coeff m := by
  classical
  let y : Fin n → MvPolynomial (Fin n) ℝ := fun j =>
    MvPolynomial.C (1 - θ) * MvPolynomial.X j +
      MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i)
  have ha : 0 ≤ 1 - θ := by linarith
  have hb : 0 ≤ θ := le_of_lt hθ0
  let S : MvPolynomial (Fin n) ℝ := ∑ i : Fin n, X i
  have hpdeg_weight : ∀ v ∈ p.support, Finsupp.weight (1 : Fin n → ℕ) v = d := by
    intro v hv
    exact hpdeg (Finsupp.mem_support_iff.mp hv)
  -- representation of the coefficient as a sum over the support
  have hstep1 : MvPolynomial.aeval (R := ℝ) y p =
      ∑ v ∈ p.support, (p.coeff v) • MvPolynomial.aeval (R := ℝ) y (monomial v 1) := by
    conv_lhs => rw [p.as_sum]
    rw [MvPolynomial.aeval_sum]
    apply Finset.sum_congr rfl
    intro v hv
    have hms : monomial v (p.coeff v) = (p.coeff v) • monomial v 1 := by
      simpa using (LinearMap.map_smul (monomial v) (p.coeff v) (1 : ℝ))
    rw [hms]
    exact map_smul (MvPolynomial.aeval (R := ℝ) y) (p.coeff v) (monomial v 1)
  have hstep2 : coeff m (∑ v ∈ p.support, (p.coeff v) • MvPolynomial.aeval (R := ℝ) y (monomial v 1)) =
      ∑ v ∈ p.support, (p.coeff v) * coeff m (MvPolynomial.aeval (R := ℝ) y (monomial v 1)) := by
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_congr rfl
    intro v hv
    rw [MvPolynomial.coeff_smul]
    simp
  have hrep : coeff m (MvPolynomial.aeval (R := ℝ) y p) =
      ∑ v ∈ p.support, (p.coeff v) * coeff m (∏ i : Fin n, y i ^ (v i)) := by
    calc
      coeff m (MvPolynomial.aeval (R := ℝ) y p)
          = coeff m (∑ v ∈ p.support, (p.coeff v) • MvPolynomial.aeval (R := ℝ) y (monomial v 1)) := by
            rw [hstep1]
      _ = ∑ v ∈ p.support, (p.coeff v) * coeff m (MvPolynomial.aeval (R := ℝ) y (monomial v 1)) := hstep2
      _ = ∑ v ∈ p.support, (p.coeff v) * coeff m (∏ i : Fin n, y i ^ (v i)) := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [aeval_monomial_one_eq_prod (ι := Fin n) y v]
  -- the constant lower bound `K`
  let K : ℝ := coeff m ((C θ * (∑ i : Fin n, X i)) ^ d)
  have hK : K = θ ^ d * (m.multinomial : ℝ) := by
    dsimp [K]
    calc
      coeff m ((C θ * (∑ i : Fin n, X i)) ^ d)
          = coeff m (C (θ ^ d) * (∑ i : Fin n, X i) ^ d) := by
            have hpow : (C θ * (∑ i : Fin n, X i)) ^ d = C (θ ^ d) * (∑ i : Fin n, X i) ^ d := by
              rw [mul_pow, ← C_pow θ d]
            rw [hpow]
      _ = θ ^ d * coeff m ((∑ i : Fin n, X i) ^ d) := by rw [MvPolynomial.coeff_C_mul]
      _ = θ ^ d * (m.multinomial : ℝ) := by
            have hsumd : m.sum (fun (_ : Fin n) (k : ℕ) => k) = d := (weight_eq_sum_id m).symm.trans hm
            rw [MvPolynomial.coeff_sum_X_pow_of_fintype, if_pos hsumd]
  have hmm_pos : 0 < (m.multinomial : ℝ) := by
    rw [Nat.cast_pos]
    rw [Finsupp.multinomial_eq]
    exact Nat.multinomial_pos m.support (fun a => m a)
  have hK_pos : 0 < K := by
    rw [hK]
    exact mul_pos (pow_pos hθ0 d) hmm_pos
  -- per-monomial coefficient bound
  have hmono (v : Fin n →₀ ℕ) :
      coeff m ((C θ * (∑ i : Fin n, X i)) ^ (Finsupp.weight (1 : Fin n → ℕ) v)) ≤
        coeff m (∏ i : Fin n, y i ^ (v i)) := by
    have hC := coeffN_prod_linearSubst_sub_pow (ι := Fin n) (a := 1 - θ) (b := θ) ha hb v
    exact coeff_le_of_coeffN hC m
  have hterm (v : Fin n →₀ ℕ) (hv : v ∈ p.support) :
      (p.coeff v) * K ≤ (p.coeff v) * coeff m (∏ i : Fin n, y i ^ (v i)) := by
    have hwv : Finsupp.weight (1 : Fin n → ℕ) v = d := hpdeg_weight v hv
    have hb' := hmono v
    rw [hwv] at hb'
    exact mul_le_mul_of_nonneg_left hb' (hp v)
  have hsum_le : (∑ v ∈ p.support, (p.coeff v) * K) ≤ coeff m (MvPolynomial.aeval (R := ℝ) y p) := by
    rw [hrep]
    exact Finset.sum_le_sum (fun v hv => hterm v hv)
  have hfinal : (∑ v ∈ p.support, p.coeff v) * K ≤ coeff m (MvPolynomial.aeval (R := ℝ) y p) := by
    rw [Finset.sum_mul]
    exact hsum_le
  -- positivity of the sum of coefficients
  have hcs_pos : 0 < ∑ v ∈ p.support, p.coeff v := by
    rcases MvPolynomial.exists_coeff_ne_zero hp0 with ⟨v0, hv0ne⟩
    have hv0mem : v0 ∈ p.support := Finsupp.mem_support_iff.mpr hv0ne
    have hpos0 : 0 < p.coeff v0 := lt_of_le_of_ne (hp v0) (by
      intro hz
      exact hv0ne hz.symm)
    exact lt_of_lt_of_le hpos0 (Finset.single_le_sum (fun v hv => hp v) hv0mem)
  have hprod_pos : 0 < (∑ v ∈ p.support, p.coeff v) * K := mul_pos hcs_pos hK_pos
  exact lt_of_lt_of_le hprod_pos hfinal

end

end Commons.Algebra.MvPolynomial