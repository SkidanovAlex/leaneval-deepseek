import Mathlib
import Submission.Commons.Combinatorics.MvPolynomial.augmentation_of_rayleigh

open Finsupp MvPolynomial
open scoped BigOperators

set_option autoImplicit false

namespace Commons.Combinatorics.MvPolynomial

noncomputable section

/-! ## The translate `X_i ↦ X_i + 1`: evaluation and derivatives -/

/-- evaluation of the shifted polynomial `q(X+1,…,X+1)` -/
lemma eval_shift {σ : Type*} (w : σ → ℝ) (p : MvPolynomial σ ℝ) :
    MvPolynomial.eval w (bind₁ (fun i => X i + C (1 : ℝ) : σ → MvPolynomial σ ℝ) p) =
      MvPolynomial.eval (fun k => w k + 1) p := by
  classical
  rw [← MvPolynomial.aeval_eq_eval (S₁ := ℝ) (f := fun k => w k + 1)]
  change MvPolynomial.aeval w (bind₁ (fun i => X i + C (1 : ℝ)) p) = _
  rw [MvPolynomial.aeval_bind₁]
  have hfun : (fun i : σ => MvPolynomial.aeval w (X i + C (1 : ℝ))) = (fun k : σ => w k + 1) := by
    funext i
    simp
  simpa [hfun]

/-- constant coefficient of the shifted polynomial is its evaluation at all-ones -/
lemma coeff_zero_shift {σ : Type*} (p : MvPolynomial σ ℝ) :
    MvPolynomial.coeff 0 (bind₁ (fun i => X i + C (1 : ℝ) : σ → MvPolynomial σ ℝ) p) =
      MvPolynomial.eval (fun _ : σ => (1 : ℝ)) p := by
  classical
  calc
    MvPolynomial.coeff 0 (bind₁ (fun i => X i + C (1 : ℝ) : σ → MvPolynomial σ ℝ) p)
        = MvPolynomial.eval (0 : σ → ℝ) (bind₁ (fun i => X i + C (1 : ℝ)) p) := by
          rw [← MvPolynomial.constantCoeff_eq]
          rw [MvPolynomial.eval_zero]
    _ = MvPolynomial.eval (fun k : σ => (0 : ℝ) + 1) p := by
          exact eval_shift (σ := σ) (w := (0 : σ → ℝ)) p
    _ = MvPolynomial.eval (fun _ : σ => (1 : ℝ)) p := by
          rw [show (fun k : σ => (0 : ℝ) + 1) = fun _ : σ => (1 : ℝ) by funext k; norm_num]

/-- `pderiv` commutes with the shift `X_i ↦ X_i + 1` -/
lemma pderiv_shift {σ : Type*} (i : σ) (p : MvPolynomial σ ℝ) :
    pderiv i (bind₁ (fun j => X j + C (1 : ℝ) : σ → MvPolynomial σ ℝ) p) =
      bind₁ (fun j => X j + C (1 : ℝ) : σ → MvPolynomial σ ℝ) (pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp
  | add p q hp hq =>
      calc
        pderiv i (bind₁ (fun j => X j + C (1 : ℝ)) (p + q))
            = pderiv i (bind₁ (fun j => X j + C (1 : ℝ)) p + bind₁ (fun j => X j + C (1 : ℝ)) q) := by
              rw [map_add]
        _ = pderiv i (bind₁ (fun j => X j + C (1 : ℝ)) p) + pderiv i (bind₁ (fun j => X j + C (1 : ℝ)) q) := by
              rw [map_add]
        _ = bind₁ (fun j => X j + C (1 : ℝ)) (pderiv i p) + bind₁ (fun j => X j + C (1 : ℝ)) (pderiv i q) := by
              rw [hp, hq]
        _ = bind₁ (fun j => X j + C (1 : ℝ)) (pderiv i p + pderiv i q) := by
              rw [← map_add]
        _ = bind₁ (fun j => X j + C (1 : ℝ)) (pderiv i (p + q)) := by
              rw [← map_add]
  | mul_X p a hp =>
      calc
        pderiv i (bind₁ (fun j => X j + C (1 : ℝ)) (p * X a))
            = pderiv i (bind₁ (fun j => X j + C (1 : ℝ)) p * (X a + C (1 : ℝ))) := by
              rw [map_mul, MvPolynomial.bind₁_X_right]
        _ = pderiv i (bind₁ (fun j => X j + C (1 : ℝ)) p) * (X a + C (1 : ℝ))
            + bind₁ (fun j => X j + C (1 : ℝ)) p * pderiv i (X a + C (1 : ℝ)) := by
              rw [MvPolynomial.pderiv_mul]
        _ = bind₁ (fun j => X j + C (1 : ℝ)) (pderiv i p) * (X a + C (1 : ℝ))
            + bind₁ (fun j => X j + C (1 : ℝ)) p
              * bind₁ (fun j => X j + C (1 : ℝ)) (pderiv i (X a : MvPolynomial σ ℝ)) := by
              rw [hp]
              congr 2
              rw [show pderiv i (X a + C (1 : ℝ)) =
                  bind₁ (fun j => X j + C (1 : ℝ)) (pderiv i (X a : MvPolynomial σ ℝ)) by
                classical
                by_cases hia : i = a
                · subst a
                  simp
                · have hX : pderiv i (X a : MvPolynomial σ ℝ) = 0 := by simp [hia]
                  rw [hX]
                  simp [hia]]
        _ = bind₁ (fun j => X j + C (1 : ℝ)) (pderiv i p) * bind₁ (fun j => X j + C (1 : ℝ)) (X a)
            + bind₁ (fun j => X j + C (1 : ℝ)) p
              * bind₁ (fun j => X j + C (1 : ℝ)) (pderiv i (X a : MvPolynomial σ ℝ)) := by
              rw [show (X a + C (1 : ℝ)) = bind₁ (fun j => X j + C (1 : ℝ)) (X a : MvPolynomial σ ℝ)
                by rw [MvPolynomial.bind₁_X_right]]
        _ = bind₁ (fun j => X j + C (1 : ℝ)) (pderiv i p * X a + p * pderiv i (X a)) := by
              rw [← map_mul, ← map_mul, ← map_add]
        _ = bind₁ (fun j => X j + C (1 : ℝ)) (pderiv i (p * X a)) := by
              rw [MvPolynomial.pderiv_mul]

/-- iterated derivatives commute with the shift -/
lemma pderivL_shift {σ : Type*} (l : List σ) (p : MvPolynomial σ ℝ) :
    pderivL l (bind₁ (fun j => X j + C (1 : ℝ) : σ → MvPolynomial σ ℝ) p) =
      bind₁ (fun j => X j + C (1 : ℝ) : σ → MvPolynomial σ ℝ) (pderivL l p) := by
  classical
  revert p
  induction l with
  | nil =>
      intro p
      simp
  | cons i l ih =>
      intro p
      calc
        pderivL (i :: l) (bind₁ (fun j => X j + C (1 : ℝ) : σ → MvPolynomial σ ℝ) p)
            = pderivL l (pderiv i (bind₁ (fun j => X j + C (1 : ℝ)) p)) := by
              rw [pderivL_cons]
        _ = pderivL l (bind₁ (fun j => X j + C (1 : ℝ)) (pderiv i p)) := by
              rw [pderiv_shift]
        _ = bind₁ (fun j => X j + C (1 : ℝ)) (pderivL l (pderiv i p)) := ih (pderiv i p)
        _ = bind₁ (fun j => X j + C (1 : ℝ)) (pderivL (i :: l) p) := by
              rw [pderivL_cons]

/-- evaluating the translate of an iterated derivative at `w` equals evaluating the
derivative of `p` at `w + 1` -/
lemma eval_pderivL_shift {σ : Type*} (l : List σ) (p : MvPolynomial σ ℝ) (w : σ → ℝ) :
    MvPolynomial.eval w (pderivL l (bind₁ (fun j => X j + C (1 : ℝ) : σ → MvPolynomial σ ℝ) p)) =
      MvPolynomial.eval (fun k => w k + 1) (pderivL l p) := by
  rw [pderivL_shift]
  exact eval_shift w (pderivL l p)

/-! ## Coefficients of the translate in terms of iterated derivatives -/

/-- the `i`-th coordinate of `eSum l` is the number of occurrences of `i` in `l` -/
lemma eSum_apply_count {σ : Type*} [DecidableEq σ] (l : List σ) (i : σ) : eSum l i = l.count i := by
  classical
  rw [eSum_eq_toFinsupp]
  rw [Multiset.toFinsupp_apply]
  rw [Multiset.coe_count]

/-- factorial of a successor (cast to ℝ) -/
lemma cast_factorial_succ (n : ℕ) :
    (Nat.factorial (n + 1) : ℝ) = (n + 1 : ℝ) * (Nat.factorial n : ℝ) := by
  rw [Nat.factorial_succ]
  norm_num [Nat.cast_mul]

/-- count of the head element after consing -/
lemma count_cons_head (n : ℕ) (i : Fin n) (l : List (Fin n)) :
    (i :: l).count i = l.count i + 1 := by
  simpa using (List.count_cons_self (α := Fin n) (a := i) (l := l))

/-- count of another element after consing -/
lemma count_cons_other (n : ℕ) (i j : Fin n) (hij : j ≠ i) (l : List (Fin n)) :
    (j :: l).count i = l.count i := by
  simpa using (List.count_cons_of_ne (α := Fin n) (a := i) (b := j) (l := l) hij)

/-- the factorial-weighted count product for `i :: l` factors through `l` -/
lemma prod_factorial_count_cons (n : ℕ) (i : Fin n) (l : List (Fin n)) :
    (∏ j : Fin n, ((Nat.factorial ((i :: l).count j)) : ℝ)) =
      ((l.count i + 1 : ℕ) : ℝ) * (∏ j : Fin n, ((Nat.factorial (l.count j)) : ℝ)) := by
  classical
  calc
    (∏ j : Fin n, ((Nat.factorial ((i :: l).count j)) : ℝ))
        = (∏ j : Fin n, (((Nat.factorial (l.count j)) : ℝ) * (if j = i then ((l.count i + 1 : ℕ) : ℝ) else 1))) := by
          apply Finset.prod_congr rfl
          intro j hj
          by_cases hji : j = i
          · subst j
            simp [cast_factorial_succ]
            ring
          · have hc : (i :: l).count j = l.count j := count_cons_other n j i (Ne.symm hji) l
            rw [hc]
            simp [hji]
    _ = (∏ j : Fin n, ((Nat.factorial (l.count j)) : ℝ))
        * ∏ j : Fin n, (if j = i then ((l.count i + 1 : ℕ) : ℝ) else 1) := by
          rw [Finset.prod_mul_distrib]
    _ = (∏ j : Fin n, ((Nat.factorial (l.count j)) : ℝ)) * ((l.count i + 1 : ℕ) : ℝ) := by
          congr 2
          classical
          have h := Finset.prod_eq_single (s := (Finset.univ : Finset (Fin n))) (a := i)
            (f := fun j : Fin n => if j = i then ((l.count i + 1 : ℕ) : ℝ) else 1)
            (by intro b hb hbi; simp [hbi])
            (by intro hmem; simp at hmem)
          simpa using h
    _ = ((l.count i + 1 : ℕ) : ℝ) * (∏ j : Fin n, ((Nat.factorial (l.count j)) : ℝ)) := by
          ring

/-- constant coefficient of the `l`-fold derivative: `(∏ counts!) × coefficient at `eSum l`` -/
lemma coeff_zero_pderivL (n : ℕ) (l : List (Fin n)) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.coeff 0 (pderivL l p) =
      MvPolynomial.coeff (eSum l) p * (∏ j : Fin n, ((Nat.factorial (l.count j)) : ℝ)) := by
  classical
  revert p
  induction l with
  | nil =>
      intro p
      simp [eSum]
  | cons i l ih =>
      intro p
      calc
        MvPolynomial.coeff 0 (pderivL (i :: l) p)
            = MvPolynomial.coeff 0 (pderivL l (pderiv i p)) := by
              rw [pderivL_cons]
        _ = MvPolynomial.coeff (eSum l) (pderiv i p)
            * (∏ j : Fin n, ((Nat.factorial (l.count j)) : ℝ)) := ih (pderiv i p)
        _ = (MvPolynomial.coeff (eSum l + e i) p * ((eSum l) i + 1))
            * (∏ j : Fin n, ((Nat.factorial (l.count j)) : ℝ)) := by
              rw [MvPolynomial.coeff_pderiv]
        _ = MvPolynomial.coeff (eSum (i :: l)) p * ((l.count i + 1 : ℕ) : ℝ)
            * (∏ j : Fin n, ((Nat.factorial (l.count j)) : ℝ)) := by
              have h1 : eSum (i :: l) = eSum l + e i := by
                rw [eSum_cons]
                rw [add_comm]
              have h2 : ((l.count i + 1 : ℕ) : ℝ) = ((eSum l) i + 1) := by
                rw [eSum_apply_count]
                norm_num
              rw [← h1, ← h2]
        _ = MvPolynomial.coeff (eSum (i :: l)) p
            * (∏ j : Fin n, ((Nat.factorial ((i :: l).count j)) : ℝ)) := by
              rw [prod_factorial_count_cons]
              ring

/-- the number of occurrences of `i` in the exponent list of `γ` is `γ i` -/
lemma count_exponentList {σ : Type*} [DecidableEq σ] (γ : σ →₀ ℕ) (i : σ) :
    (exponentList γ).count i = γ i := by
  classical
  unfold exponentList
  rw [← Multiset.coe_count]
  rw [Multiset.coe_toList]
  exact Finsupp.count_toMultiset γ i

/-- constant coefficient of the derivative along `γ` -/
lemma coeff_zero_pderivL_exponent (n : ℕ) (γ : Fin n →₀ ℕ) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.coeff 0 (pderivL (exponentList γ) p) =
      (∏ i : Fin n, ((Nat.factorial (γ i)) : ℝ)) * MvPolynomial.coeff γ p := by
  classical
  rw [coeff_zero_pderivL n (exponentList γ) p]
  rw [eSum_exponentList]
  have hprod : (∏ j : Fin n, ((Nat.factorial ((exponentList γ).count j)) : ℝ)) =
      (∏ i : Fin n, ((Nat.factorial (γ i)) : ℝ)) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [count_exponentList]
  rw [hprod, mul_comm]

/-- the `γ`-coefficient of the translate is, up to `∏ γ_i!`, the value of `∂^γ q` at `1` -/
lemma coeff_translate_factor (n : ℕ) (γ : Fin n →₀ ℕ) (p : MvPolynomial (Fin n) ℝ) :
    (∏ i : Fin n, ((Nat.factorial (γ i)) : ℝ)) *
        MvPolynomial.coeff γ (bind₁ (fun j => X j + C (1 : ℝ) : Fin n → MvPolynomial (Fin n) ℝ) p) =
      MvPolynomial.eval (fun _ : Fin n => (1 : ℝ)) (pderivL (exponentList γ) p) := by
  classical
  calc
    (∏ i : Fin n, ((Nat.factorial (γ i)) : ℝ)) *
        MvPolynomial.coeff γ (bind₁ (fun j => X j + C (1 : ℝ)) p)
        = MvPolynomial.coeff 0
            (pderivL (exponentList γ) (bind₁ (fun j => X j + C (1 : ℝ)) p)) := by
          rw [← coeff_zero_pderivL_exponent n γ (bind₁ (fun j => X j + C (1 : ℝ)) p)]
    _ = MvPolynomial.coeff 0 (bind₁ (fun j => X j + C (1 : ℝ)) (pderivL (exponentList γ) p)) := by
          rw [pderivL_shift]
    _ = MvPolynomial.eval (fun _ : Fin n => (1 : ℝ)) (pderivL (exponentList γ) p) := by
          rw [coeff_zero_shift]

/-! ## Nonnegativity and support of the translate -/

/-- a nonzero polynomial with nonnegative coefficients evaluates positively at `(1,…,1)` -/
lemma eval_ones_pos_of_ne_zero {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ)
    (hp : ∀ m : σ →₀ ℕ, 0 ≤ p.coeff m) (hp0 : p ≠ 0) :
    0 < MvPolynomial.eval (fun _ : σ => (1 : ℝ)) p := by
  classical
  have hne : ∃ m : σ →₀ ℕ, m ∈ p.support := by
    by_contra h
    apply hp0
    ext m
    by_contra hc
    exact h ⟨m, MvPolynomial.mem_support_iff.mpr hc⟩
  rcases hne with ⟨m, hm⟩
  have hcpos : 0 < p.coeff m := lt_of_le_of_ne' (hp m) (MvPolynomial.mem_support_iff.mp hm)
  have hge := eval_ge_term (σ := σ) p hp (w := fun _ : σ => (1 : ℝ)) (fun k => by norm_num) m hm
  have hprod : (∏ i : σ, (1 : ℝ) ^ (m i)) = 1 := by simp
  have hle : p.coeff m * (∏ i : σ, (1 : ℝ) ^ (m i)) ≤ MvPolynomial.eval (fun _ : σ => 1) p := hge
  rw [hprod] at hle
  nlinarith

/-- support nonempty iff the polynomial is nonzero -/
lemma support_nonempty_iff_ne_zero {σ : Type*} (p : MvPolynomial σ ℝ) :
    (∃ m : σ →₀ ℕ, m ∈ p.support) ↔ p ≠ 0 := by
  constructor
  · rintro ⟨m, hm⟩ hpz
    exact (MvPolynomial.mem_support_iff.mp hm) (by simp [hpz])
  · intro hp
    by_contra hnone
    apply hp
    ext m
    by_contra hc
    exact hnone ⟨m, MvPolynomial.mem_support_iff.mpr hc⟩

/-- nonzero of the derivative along `γ` is witnessed by a support element above `γ` -/
lemma pderivL_exp_ne_zero_iff_exists_le {σ : Type*} [DecidableEq σ]
    (γ : σ →₀ ℕ) (p : MvPolynomial σ ℝ) :
    pderivL (exponentList γ) p ≠ 0 ↔ ∃ α ∈ p.support, ∀ k : σ, γ k ≤ α k := by
  classical
  rw [← (support_nonempty_iff_ne_zero (σ := σ) (pderivL (exponentList γ) p))]
  constructor
  · rintro ⟨m, hm⟩
    have hmq : m + γ ∈ p.support := by
      have h := (mem_support_pderivL (exponentList γ) p m).mp hm
      simpa [eSum_exponentList] using h
    refine ⟨m + γ, hmq, ?_⟩
    intro k
    rw [Finsupp.add_apply]
    exact Nat.le_add_left (γ k) (m k)
  · rintro ⟨α, hα, hle⟩
    let m : σ →₀ ℕ := α - γ
    have hsum : m + γ = α := by
      ext k
      dsimp [m]
      simp [hle k]
    refine ⟨m, ?_⟩
    have hmq : m + γ ∈ p.support := by simpa [hsum] using hα
    exact (mem_support_pderivL (exponentList γ) p m).mpr (by simpa [eSum_exponentList] using hmq)

/-- the factor `∏ γ_i!` is positive -/
lemma factprod_pos (n : ℕ) (γ : Fin n →₀ ℕ) :
    0 < (∏ i : Fin n, ((Nat.factorial (γ i)) : ℝ)) := by
  classical
  apply Finset.prod_pos
  intro i hi
  exact_mod_cast Nat.factorial_pos (γ i)

/-- the `γ`-coefficient of the translate is nonzero iff some support element of `q` dominates `γ` -/
lemma translate_coeff_ne_zero_iff (n : ℕ) (q : MvPolynomial (Fin n) ℝ)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ q.coeff m) (γ : Fin n →₀ ℕ) :
    MvPolynomial.coeff γ
        (bind₁ (fun i => X i + C (1 : ℝ) : Fin n → MvPolynomial (Fin n) ℝ) q) ≠ 0 ↔
      ∃ α ∈ q.support, ∀ k : Fin n, γ k ≤ α k := by
  classical
  let F : ℝ := ∏ i : Fin n, ((Nat.factorial (γ i)) : ℝ)
  let D : MvPolynomial (Fin n) ℝ := pderivL (exponentList γ) q
  have hFpos : 0 < F := by dsimp [F]; exact factprod_pos n γ
  have hFne : F ≠ 0 := ne_of_gt hFpos
  have hnnD : ∀ m : Fin n →₀ ℕ, 0 ≤ D.coeff m := by
    dsimp [D]
    exact coeff_pderivL_nonneg (exponentList γ) q hnn
  have hEq : F * MvPolynomial.coeff γ
        (bind₁ (fun i => X i + C (1 : ℝ) : Fin n → MvPolynomial (Fin n) ℝ) q) =
      MvPolynomial.eval (fun _ : Fin n => (1 : ℝ)) D := by
    dsimp [F, D]
    exact coeff_translate_factor n γ q
  have h1 : MvPolynomial.coeff γ
        (bind₁ (fun i => X i + C (1 : ℝ) : Fin n → MvPolynomial (Fin n) ℝ) q) ≠ 0 ↔
      MvPolynomial.eval (fun _ : Fin n => (1 : ℝ)) D ≠ 0 := by
    constructor
    · intro hc
      rw [← hEq]
      exact mul_ne_zero hFne hc
    · intro hd hc
      rw [hc, mul_zero] at hEq
      exact hd hEq.symm
  have h2 : MvPolynomial.eval (fun _ : Fin n => (1 : ℝ)) D ≠ 0 ↔ D ≠ 0 := by
    constructor
    · intro hev hz
      apply hev
      simp [hz]
    · intro hD
      exact ne_of_gt (eval_ones_pos_of_ne_zero (σ := Fin n) D hnnD hD)
  have h3 : D ≠ 0 ↔ ∃ α ∈ q.support, ∀ k : Fin n, γ k ≤ α k := by
    dsimp [D]
    exact pderivL_exp_ne_zero_iff_exists_le (σ := Fin n) γ q
  calc
    MvPolynomial.coeff γ
        (bind₁ (fun i => X i + C (1 : ℝ) : Fin n → MvPolynomial (Fin n) ℝ) q) ≠ 0
        ↔ MvPolynomial.eval (fun _ : Fin n => (1 : ℝ)) D ≠ 0 := h1
    _ ↔ D ≠ 0 := h2
    _ ↔ ∃ α ∈ q.support, ∀ k : Fin n, γ k ≤ α k := h3

/-- coefficients of the translate are nonnegative when those of `q` are -/
lemma translate_coeff_nonneg (n : ℕ) (q : MvPolynomial (Fin n) ℝ)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ q.coeff m) (γ : Fin n →₀ ℕ) :
    0 ≤ MvPolynomial.coeff γ
        (bind₁ (fun i => X i + C (1 : ℝ) : Fin n → MvPolynomial (Fin n) ℝ) q) := by
  classical
  let F : ℝ := ∏ i : Fin n, ((Nat.factorial (γ i)) : ℝ)
  let D : MvPolynomial (Fin n) ℝ := pderivL (exponentList γ) q
  have hFpos : 0 < F := by dsimp [F]; exact factprod_pos n γ
  have hnnD : ∀ m : Fin n →₀ ℕ, 0 ≤ D.coeff m := by
    dsimp [D]
    exact coeff_pderivL_nonneg (exponentList γ) q hnn
  have hev : 0 ≤ MvPolynomial.eval (fun _ : Fin n => (1 : ℝ)) D :=
    eval_nonneg_of_coeff_nonneg D hnnD (fun k => by norm_num)
  have hEq : F * MvPolynomial.coeff γ
        (bind₁ (fun i => X i + C (1 : ℝ) : Fin n → MvPolynomial (Fin n) ℝ) q) =
      MvPolynomial.eval (fun _ : Fin n => (1 : ℝ)) D := by
    dsimp [F, D]
    exact coeff_translate_factor n γ q
  have hmul : 0 ≤ F * MvPolynomial.coeff γ
        (bind₁ (fun i => X i + C (1 : ℝ) : Fin n → MvPolynomial (Fin n) ℝ) q) := by
    rw [hEq]
    exact hev
  exact (mul_nonneg_iff_of_pos_left hFpos).mp hmul

/-- support of the translate is exactly the set of `γ` below some support element of `q` -/
lemma translate_mem_support_iff (n : ℕ) (q : MvPolynomial (Fin n) ℝ)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ q.coeff m) (γ : Fin n →₀ ℕ) :
    γ ∈ (bind₁ (fun i => X i + C (1 : ℝ) : Fin n → MvPolynomial (Fin n) ℝ) q).support ↔
      ∃ α ∈ q.support, ∀ k : Fin n, γ k ≤ α k := by
  rw [MvPolynomial.mem_support_iff]
  exact translate_coeff_ne_zero_iff n q hnn γ



/-- Let q be a nonzero homogeneous degree-`d` polynomial with nonnegative coefficients that is
(list-)c-Rayleigh.  Its translate `g(X) := q(X + 1, …, X + 1)` (formal substitution) is again
(list-)c-Rayleigh with the same c, has nonnegative coefficients, its support is exactly the set
of γ for which some support element α of q dominates γ coordinatewise, every support element of g
has total weight at most d, and 0 is in its support. -/
theorem translate_package (n d : ℕ) (c : ℝ) (hc : 0 < c)
    (q : MvPolynomial (Fin n) ℝ)
    (hq : q.IsHomogeneous d) (hq0 : q ≠ 0)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ q.coeff m)
    (hr : ∀ (l : List (Fin n)) (i j : Fin n) (w : Fin n → ℝ),
      (∀ k : Fin n, 0 ≤ w k) →
        MvPolynomial.eval w (l.foldl (fun q i => MvPolynomial.pderiv i q) q) *
            MvPolynomial.eval w ((i :: j :: l).foldl (fun q i => MvPolynomial.pderiv i q) q) ≤
          c * (MvPolynomial.eval w ((i :: l).foldl (fun q i => MvPolynomial.pderiv i q) q) *
            MvPolynomial.eval w ((j :: l).foldl (fun q i => MvPolynomial.pderiv i q) q))) :
    let g : MvPolynomial (Fin n) ℝ :=
      MvPolynomial.bind₁ (fun i : Fin n => MvPolynomial.X i + MvPolynomial.C 1) q
    (∀ (l : List (Fin n)) (i j : Fin n) (w : Fin n → ℝ), (∀ k : Fin n, 0 ≤ w k) →
        MvPolynomial.eval w (l.foldl (fun q i => MvPolynomial.pderiv i q) g) *
            MvPolynomial.eval w ((i :: j :: l).foldl (fun q i => MvPolynomial.pderiv i q) g) ≤
          c * (MvPolynomial.eval w ((i :: l).foldl (fun q i => MvPolynomial.pderiv i q) g) *
            MvPolynomial.eval w ((j :: l).foldl (fun q i => MvPolynomial.pderiv i q) g))) ∧
    (∀ m : Fin n →₀ ℕ, 0 ≤ g.coeff m) ∧
    (∀ γ : Fin n →₀ ℕ, γ ∈ g.support ↔ ∃ α ∈ q.support, ∀ k : Fin n, γ k ≤ α k) ∧
    (∀ γ ∈ g.support, (∑ i : Fin n, γ i) ≤ d) ∧
    ((0 : Fin n →₀ ℕ) ∈ g.support) := by
  classical
  let g : MvPolynomial (Fin n) ℝ :=
      MvPolynomial.bind₁ (fun i : Fin n => MvPolynomial.X i + MvPolynomial.C 1) q
  -- 1. the translate is again (list-)c-Rayleigh
  have hR : Ray c q := by
    simpa [Ray, pderivL] using hr
  have hRg : Ray c g := by
    unfold Ray
    intro l i j w hw
    have hw1 : ∀ k : Fin n, 0 ≤ w k + (1 : ℝ) := by
      intro k
      linarith [hw k]
    have hq1 := hR l i j (fun k : Fin n => w k + 1) hw1
    have hEv : ∀ l' : List (Fin n),
        MvPolynomial.eval (fun k : Fin n => w k + 1) (pderivL l' q) =
          MvPolynomial.eval w (pderivL l' g) := by
      intro l'
      dsimp [g]
      exact (eval_pderivL_shift (σ := Fin n) l' q w).symm
    rw [hEv l, hEv (i :: j :: l), hEv (i :: l), hEv (j :: l)] at hq1
    exact hq1
  -- 2. nonnegativity of the coefficients
  have hnn_g : ∀ m : Fin n →₀ ℕ, 0 ≤ g.coeff m := by
    intro m
    simpa [g] using translate_coeff_nonneg n q hnn m
  -- 3. support characterization
  have hsupp : ∀ γ : Fin n →₀ ℕ, γ ∈ g.support ↔ ∃ α ∈ q.support, ∀ k : Fin n, γ k ≤ α k := by
    intro γ
    simpa [g] using translate_mem_support_iff n q hnn γ
  -- 4. weight bound
  have hweight : ∀ γ ∈ g.support, (∑ i : Fin n, γ i) ≤ d := by
    intro γ hγ
    rcases (hsupp γ).mp (by simpa [g] using hγ) with ⟨α, hαq, hγle⟩
    have hc : q.coeff α ≠ 0 := MvPolynomial.mem_support_iff.mp hαq
    have hdeg : Finsupp.degree α = d := by
      by_contra hd
      apply hc
      exact MvPolynomial.IsHomogeneous.coeff_eq_zero hq (d := α) hd
    have hsumα : (∑ i : Fin n, α i) = d := by
      calc
        (∑ i : Fin n, α i) = Finsupp.degree α := (Finsupp.degree_eq_sum α).symm
        _ = d := hdeg
    have hle : (∑ i : Fin n, γ i) ≤ ∑ i : Fin n, α i := by
      exact Finset.sum_le_sum (fun i hi => hγle i)
    rw [hsumα] at hle
    exact hle
  -- 5. zero is in the support
  have hzero : (0 : Fin n →₀ ℕ) ∈ g.support := by
    have hne : ∃ α : Fin n →₀ ℕ, α ∈ q.support :=
      (support_nonempty_iff_ne_zero q).mpr hq0
    rcases hne with ⟨α, hαq⟩
    simpa [g] using (translate_mem_support_iff n q hnn (0 : Fin n →₀ ℕ)).mpr
      ⟨α, hαq, fun k => Nat.zero_le _⟩
  -- assemble
  constructor
  · -- part (1)
    simpa [Ray, pderivL, g] using hRg
  constructor
  · exact hnn_g
  constructor
  · exact hsupp
  constructor
  · exact hweight
  · exact hzero

end
end Commons.Combinatorics.MvPolynomial
