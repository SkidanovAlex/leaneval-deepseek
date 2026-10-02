/-
Artin-Schreier point count (additive Stepanov / Weil bound).

`Commons.NumberTheory.ArtinSchreier.point_count` : for a prime `p` and `d ≥ 1` there is `C > 0`
depending only on `p` and `d` such that for every finite field `E` of characteristic `p`
(i.e. an algebra over `ZMod p`) with `d < p`, and every `g ∈ (ZMod p)[X]` of degree between
`1` and `d`,

  `|#{(x, y) ∈ E × E : y^p - y = g(x)} - #E| ≤ C √(#E)`.

The proof reduces the count to the number of `x ∈ E` with `Tr_{E/F_p}(g x) = 0`, and then
applies the additive (Artin-Schreier) form of Stepanov's elementary method, which is
formalized here on top of the shared commons:

* `Commons.NumberTheory.Stepanov.stepanov_numerics` — the numerical inequality which supplies
  the dimension count;
* the auxiliary-polynomial machinery (`Tf`, `Psi`, `Cond`, `Raux`, `additive_count`,
  `additive_independent`, `witness_exists`) — Stepanov's method in characteristic `p`.
-/
import Mathlib
import Submission.Commons.Algebra.Polynomial.hasseDeriv_mul_X_pow_prime_pow
import Submission.Commons.NumberTheory.Stepanov.stepanov_bound_general
import Submission.Commons.NumberTheory.Stepanov.stepanov_numerics
import Submission.Commons.Algebra.Polynomial.eval_add_eq_sum_hasseDeriv

set_option autoImplicit true
set_option maxHeartbeats 2000000

open Polynomial

namespace Commons.NumberTheory.ArtinSchreier

theorem sum_pow_charPow {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    {ι : Type*} (s : Finset ι) (a : ι → R) (k : ℕ) :
    (∑ i ∈ s, a i) ^ (p ^ k) = ∑ i ∈ s, (a i) ^ (p ^ k) := by
  classical
  induction s using Finset.induction with
  | empty => simp [zero_pow (pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero)]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      rw [add_pow_char_pow, ih]

section
variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]

/-- Coefficient of a sum of `C a * X^(s*k)` terms. -/
theorem coeff_sum_C_mul_X_pow_mul {d k m : ℕ} (a : ℕ → F) :
    (∑ s ∈ Finset.Icc 1 d, Polynomial.C (a s) * Polynomial.X ^ (s * k)).coeff m =
      ∑ s ∈ Finset.Icc 1 d, if s * k = m then a s else 0 := by
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Polynomial.coeff_C_mul_X_pow]
  by_cases h : m = s * k
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]

theorem taylor_eq_sum_hasse (x : F) (f : Polynomial F) :
    Polynomial.taylor x f = ∑ s ∈ Finset.range (f.natDegree + 1),
      Polynomial.C (Polynomial.eval x (Polynomial.hasseDeriv s f)) * Polynomial.X ^ s := by
  rw [← Polynomial.sum_C_mul_X_pow_eq (Polynomial.taylor x f), Polynomial.sum_def]
  rw [Finset.sum_subset (s₂ := Finset.range (f.natDegree + 1))]
  · refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Polynomial.taylor_coeff]
  · intro s hs
    rw [Polynomial.mem_support_iff] at hs
    have h1 : s ≤ (Polynomial.taylor x f).natDegree := Polynomial.le_natDegree_of_ne_zero hs
    rw [Polynomial.natDegree_taylor] at h1
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le h1)
  · intro s _ hs
    rw [Polynomial.notMem_support_iff.mp hs]
    simp

theorem sum_C_mul_X_pow_pow (d : ℕ) (c : ℕ → F) (i : ℕ) :
    (∑ s ∈ Finset.range (d+1), Polynomial.C (c s) * Polynomial.X ^ s) ^ (p^i)
      = ∑ s ∈ Finset.range (d+1), Polynomial.C ((c s) ^ (p^i)) * Polynomial.X ^ (s * p^i) := by
  rw [sum_pow_charPow]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [mul_pow, ← Polynomial.C_pow, ← pow_mul, mul_comm]

/-- The `p^i`-th power of the Taylor expansion, with the constant term split off. -/
theorem taylor_pow_eq (x : F) (f : Polynomial F) (i : ℕ) :
    (Polynomial.taylor x f) ^ (p^i) =
      Polynomial.C ((Polynomial.eval x f) ^ (p^i)) +
        ∑ s ∈ Finset.Icc 1 f.natDegree,
          Polynomial.C ((Polynomial.eval x (Polynomial.hasseDeriv s f)) ^ (p^i)) *
            Polynomial.X ^ (s * p^i) := by
  rw [taylor_eq_sum_hasse x f, sum_C_mul_X_pow_pow]
  have h0 : (0:ℕ) ∈ Finset.range (f.natDegree + 1) := Finset.mem_range.mpr (Nat.succ_pos _)
  rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr h0), Finset.sum_singleton]
  rw [show (Finset.range (f.natDegree+1)) \ {0} = Finset.Icc 1 f.natDegree from ?_]
  · rw [Polynomial.hasseDeriv_zero]
    simp only [Nat.zero_mul, pow_zero, mul_one, LinearMap.id_apply, add_comm]
  · ext n
    simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_range, Finset.mem_Icc]
    omega

end

section
variable {F : Type*} [Field F]

noncomputable def Tf (p : ℕ) (n : ℕ) (f : Polynomial F) : Polynomial F :=
  ∑ i ∈ Finset.range n, f ^ (p ^ i)

noncomputable def Psi (p : ℕ) (n : ℕ) (f : Polynomial F) : Polynomial (Polynomial F) :=
  ∑ i ∈ Finset.range n, ∑ s ∈ Finset.Icc 1 f.natDegree,
    Polynomial.C ((Polynomial.hasseDeriv s f) ^ (p ^ i)) *
      (Polynomial.X : Polynomial (Polynomial F)) ^ (s * p ^ i)

theorem Psi_coeff (p n : ℕ) (f : Polynomial F) (m : ℕ) :
    (Psi p n f).coeff m =
      ∑ i ∈ Finset.range n, ∑ s ∈ Finset.Icc 1 f.natDegree,
        if s * p ^ i = m then (Polynomial.hasseDeriv s f) ^ (p ^ i) else 0 := by
  rw [Psi, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl ?_
  intro s _
  rw [Polynomial.coeff_C_mul_X_pow]
  by_cases h : m = s * p ^ i
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]

theorem taylor_mul' (x : F) (g h : Polynomial F) :
    Polynomial.taylor x (g * h) = Polynomial.taylor x g * Polynomial.taylor x h := by
  rw [Polynomial.taylor_apply, Polynomial.mul_comp, Polynomial.taylor_apply, Polynomial.taylor_apply]

theorem taylor_Tf (p : ℕ) [Fact p.Prime] [CharP F p] (n : ℕ) (f : Polynomial F) (x : F) :
    Polynomial.taylor x (Tf p n f) = ∑ i ∈ Finset.range n, (Polynomial.taylor x f) ^ (p ^ i) := by
  rw [Tf]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.taylor_pow]

theorem eval_Psi_coeff_eq (p : ℕ) [Fact p.Prime] [CharP F p] (n : ℕ) (f : Polynomial F) {m : ℕ} (hm : 1 ≤ m) (x : F) :
    Polynomial.eval x ((Psi p n f).coeff m) =
      ∑ i ∈ Finset.range n, ∑ s ∈ Finset.Icc 1 f.natDegree,
        if s * p ^ i = m then (Polynomial.eval x (Polynomial.hasseDeriv s f)) ^ (p ^ i) else 0 := by
  rw [Psi_coeff]
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  by_cases h : s * p ^ i = m
  · rw [if_pos h, if_pos h, Polynomial.eval_pow]
  · rw [if_neg h, if_neg h, Polynomial.eval_zero]

theorem taylor_Tf_coeff_eq_Psi (p : ℕ) [Fact p.Prime] [CharP F p] (n : ℕ) (f : Polynomial F) {m : ℕ} (hm : 1 ≤ m) (x : F) :
    (Polynomial.taylor x (Tf p n f)).coeff m = Polynomial.eval x ((Psi p n f).coeff m) := by
  rw [taylor_Tf p n f x, eval_Psi_coeff_eq p n f hm x, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [taylor_pow_eq x f i, Polynomial.coeff_add, Polynomial.coeff_C]
  rw [if_neg (by omega : ¬ (m = 0))]
  rw [zero_add, coeff_sum_C_mul_X_pow_mul]

end

section
variable {F : Type*} [Field F]

theorem Psi_coeff_natDegree_le (p n : ℕ) [Fact p.Prime] [CharP F p]
    (f : Polynomial F) {s : ℕ} (hs : 1 ≤ s) :
    ((Psi p n f).coeff s).natDegree ≤ (f.natDegree - 1) * s := by
  rw [Psi_coeff]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Finset.sup_le (fun i _ => ?_)
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Finset.sup_le (fun s' hs' => ?_)
  rw [Finset.mem_Icc] at hs'
  obtain ⟨hs'1, hs'd⟩ := hs'
  simp only [Function.comp_apply]
  by_cases h : s' * p ^ i = s
  · rw [if_pos h, Polynomial.natDegree_pow]
    have h1 : (Polynomial.hasseDeriv s' f).natDegree ≤ f.natDegree - s' :=
      Polynomial.natDegree_hasseDeriv_le _ _
    have h2 : p ^ i * (Polynomial.hasseDeriv s' f).natDegree ≤ p ^ i * (f.natDegree - s') :=
      Nat.mul_le_mul_left _ h1
    have h3 : p ^ i * (f.natDegree - s') = p ^ i * f.natDegree - s := by
      rw [Nat.mul_sub]
      have : p ^ i * s' = s := by rw [mul_comm]; exact h
      rw [this]
    have h4 : p ^ i ≤ s := by
      conv_rhs => rw [← h]
      exact Nat.le_mul_of_pos_left _ (by positivity)
    have h5 : p ^ i * f.natDegree ≤ s * f.natDegree := Nat.mul_le_mul_right _ h4
    have h6 : s * f.natDegree - s ≤ (f.natDegree - 1) * s := by
      rcases Nat.eq_zero_or_pos f.natDegree with h0 | h0
      · simp [h0]
      · rw [Nat.sub_mul, one_mul, mul_comm s f.natDegree]
    calc p ^ i * (Polynomial.hasseDeriv s' f).natDegree
        ≤ p ^ i * (f.natDegree - s') := h2
      _ = p ^ i * f.natDegree - s := h3
      _ ≤ s * f.natDegree - s := Nat.sub_le_sub_right h5 s
      _ ≤ (f.natDegree - 1) * s := h6
  · rw [if_neg h]
    simp

end

section
variable {F : Type*} [Field F]

theorem pow_coeff_natDegree_le (P : Polynomial (Polynomial F)) (w : ℕ)
    (h0 : P.coeff 0 = 0) (hP : ∀ s, 1 ≤ s → (P.coeff s).natDegree ≤ w * s) :
    ∀ t m : ℕ, (((P ^ t).coeff m).natDegree) ≤ w * m := by
  intro t
  induction t with
  | zero =>
      intro m
      rw [pow_zero, Polynomial.coeff_one]
      split_ifs with h
      · simp
      · simp
  | succ t ih =>
      intro m
      rw [pow_succ, Polynomial.coeff_mul]
      refine (Polynomial.natDegree_sum_le _ _).trans ?_
      refine Finset.sup_le (fun ab hab => ?_)
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
      simp only [Function.comp_apply]
      by_cases hb : ab.2 = 0
      · rw [hb, h0, mul_zero, Polynomial.natDegree_zero]
        exact Nat.zero_le _
      · refine (Polynomial.natDegree_mul_le).trans ?_
        have hb1 : 1 ≤ ab.2 := by omega
        have h1 := ih ab.1
        have h2 := hP ab.2 hb1
        calc (Polynomial.natDegree ((P ^ t).coeff ab.1) + Polynomial.natDegree (P.coeff ab.2))
            ≤ w * ab.1 + w * ab.2 := add_le_add h1 h2
          _ = w * m := by rw [← hab, mul_add]

end

section
variable {F : Type*} [Field F]

theorem Psi_coeff_zero (p n : ℕ) [Fact p.Prime] (f : Polynomial F) : (Psi p n f).coeff 0 = 0 := by
  rw [Psi_coeff]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  refine Finset.sum_eq_zero (fun s hs => ?_)
  rw [Finset.mem_Icc] at hs
  rw [if_neg (by
    intro h
    have h1 : 1 ≤ s := hs.1
    have h2 : 0 < p ^ i := pow_pos (Fact.out : Nat.Prime p).pos i
    nlinarith [h1, h2])]

theorem taylor_Tf_eq_map_Psi (p n : ℕ) [Fact p.Prime] [CharP F p] (f : Polynomial F) {x : F}
    (hx : Polynomial.eval x (Tf p n f) = 0) :
    Polynomial.taylor x (Tf p n f) = Polynomial.map (Polynomial.evalRingHom x) (Psi p n f) := by
  ext m
  rw [Polynomial.coeff_map]
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0
    rw [Polynomial.taylor_coeff_zero, hx, Psi_coeff_zero p, map_zero]
  · rw [taylor_Tf_coeff_eq_Psi p n f h0 x]
    rfl

theorem eval_hasseDeriv_Tf_pow (p n : ℕ) [Fact p.Prime] [CharP F p] (f : Polynomial F) {x : F}
    (hx : Polynomial.eval x (Tf p n f) = 0) (t m : ℕ) :
    Polynomial.eval x (Polynomial.hasseDeriv m ((Tf p n f) ^ t)) =
      Polynomial.eval x (((Psi p n f) ^ t).coeff m) := by
  rw [← Polynomial.taylor_coeff x ((Tf p n f) ^ t) m, Polynomial.taylor_pow]
  rw [taylor_Tf_eq_map_Psi p n f hx, ← Polynomial.map_pow, Polynomial.coeff_map]
  rfl

end

section
variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] [Fintype F]

/-- The auxiliary polynomial `R = ∑_t A_t(X, X^q) · Tf^t`. -/
noncomputable def Raux (p n : ℕ) (f : Polynomial F) (A : Fin p → Polynomial (Polynomial F)) : Polynomial F :=
  ∑ t : Fin p, (A t).eval ((Polynomial.X : Polynomial F) ^ Fintype.card F) * (Tf p n f) ^ (t : ℕ)

/-- The Stepanov condition polynomials. -/
noncomputable def Cond (p n B : ℕ) (f : Polynomial F) (A : Fin p → Polynomial (Polynomial F)) (ℓ : ℕ) : Polynomial F :=
  ∑ t : Fin p, ∑ k ∈ Finset.range (ℓ+1), ∑ j ∈ Finset.range (B+1),
    (Polynomial.X : Polynomial F) ^ j * Polynomial.hasseDeriv k ((A t).coeff j) *
      ((Psi p n f) ^ (t : ℕ)).coeff (ℓ - k)

theorem eval_eq_sum_coeff (q : Polynomial F) (a : F) :
    q.eval a = ∑ j ∈ Finset.range (q.natDegree + 1), q.coeff j * a ^ j :=
  Polynomial.eval_eq_sum_range a

theorem hasseDeriv_term_eq (n t j ℓ : ℕ) (f : Polynomial F) (c : Polynomial F) (hℓ : ℓ < Fintype.card F)
    (hq : Fintype.card F = p ^ n) :
    Polynomial.hasseDeriv ℓ (c * (Polynomial.X : Polynomial F) ^ (Fintype.card F * j) * (Tf p n f) ^ t)
      = Polynomial.hasseDeriv ℓ (c * (Tf p n f) ^ t) * (Polynomial.X : Polynomial F) ^ (Fintype.card F * j) := by
  rw [mul_assoc, mul_comm ((Polynomial.X : Polynomial F) ^ (Fintype.card F * j)) ((Tf p n f) ^ t), ← mul_assoc]
  rw [show (Fintype.card F * j) = (j * p ^ n) by rw [hq, mul_comm]]
  exact Commons.Algebra.Polynomial.hasseDeriv_mul_X_pow_prime_pow (F := F) p n (Fact.out : p.Prime) ℓ j
    (by rw [← hq]; exact hℓ) (c * (Tf p n f) ^ t)

end

section
variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] [Fintype F]

theorem Raux_eq_sum (n : ℕ) (f : Polynomial F) (A : Fin p → Polynomial (Polynomial F)) :
    Raux p n f A = ∑ t : Fin p, ∑ j ∈ Finset.range ((A t).natDegree + 1),
      (A t).coeff j * (Polynomial.X : Polynomial F) ^ (Fintype.card F * j) * (Tf p n f) ^ (t : ℕ) := by
  rw [Raux]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← pow_mul, mul_assoc]


theorem hasseDeriv_mul_range (ℓ : ℕ) (c g : Polynomial F) :
    Polynomial.hasseDeriv ℓ (c * g) =
      ∑ i ∈ Finset.range (ℓ+1), Polynomial.hasseDeriv i c * Polynomial.hasseDeriv (ℓ - i) g := by
  rw [Polynomial.hasseDeriv_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem hasseDeriv_mul_Tf_pow_eval (p : ℕ) [Fact p.Prime] [CharP F p] (n ℓ : ℕ) (f : Polynomial F) {x : F}
    (hx : Polynomial.eval x (Tf p n f) = 0) (c : Polynomial F) (t : ℕ) :
    Polynomial.eval x (Polynomial.hasseDeriv ℓ (c * (Tf p n f) ^ t)) =
      ∑ i ∈ Finset.range (ℓ+1),
        Polynomial.eval x (Polynomial.hasseDeriv i c) *
          Polynomial.eval x (((Psi p n f) ^ t).coeff (ℓ - i)) := by
  rw [hasseDeriv_mul_range, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.eval_mul, eval_hasseDeriv_Tf_pow p n f hx t (ℓ - i)]

theorem hasseDeriv_Raux_eval (n B ℓ : ℕ) (hq : Fintype.card F = p ^ n) (hℓ : ℓ < Fintype.card F)
    (f : Polynomial F) (A : Fin p → Polynomial (Polynomial F))
    (hAn : ∀ t, (A t).natDegree ≤ B) {x : F}
    (hx : Polynomial.eval x (Tf p n f) = 0) :
    Polynomial.eval x (Polynomial.hasseDeriv ℓ (Raux p n f A)) =
      Polynomial.eval x (Cond p n B f A ℓ) := by
  have hxq : ∀ j : ℕ, x ^ (Fintype.card F * j) = x ^ j := by
    intro j
    rw [pow_mul, FiniteField.pow_card]
  have hstep1 : Polynomial.eval x (Polynomial.hasseDeriv ℓ (Raux p n f A)) =
      ∑ t : Fin p, ∑ j ∈ Finset.range ((A t).natDegree + 1),
        Polynomial.eval x (Polynomial.hasseDeriv ℓ ((A t).coeff j * (Polynomial.X : Polynomial F) ^ (Fintype.card F * j) * (Tf p n f) ^ (t:ℕ))) := by
    rw [Raux_eq_sum]
    rw [map_sum, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [map_sum, Polynomial.eval_finsetSum]
  have hstep2 : ∀ t : Fin p, ∀ j ∈ Finset.range ((A t).natDegree + 1),
      Polynomial.eval x (Polynomial.hasseDeriv ℓ ((A t).coeff j * (Polynomial.X : Polynomial F) ^ (Fintype.card F * j) * (Tf p n f) ^ (t:ℕ)))
        = Polynomial.eval x ((Polynomial.hasseDeriv ℓ ((A t).coeff j * (Tf p n f) ^ (t:ℕ))) *
            (Polynomial.X : Polynomial F) ^ (Fintype.card F * j)) := by
    intro t j hj
    rw [hasseDeriv_term_eq n (t:ℕ) j ℓ f ((A t).coeff j) hℓ hq]
  rw [hstep1, Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun j hj => hstep2 t j hj))]
  -- evaluate each term: (hasseDeriv ℓ (A_tj Tf^t))_x · x^(q j)
  have hstep3 : ∀ t : Fin p, ∀ j : ℕ,
      Polynomial.eval x ((Polynomial.hasseDeriv ℓ ((A t).coeff j * (Tf p n f) ^ (t:ℕ))) *
          (Polynomial.X : Polynomial F) ^ (Fintype.card F * j))
        = ∑ i ∈ Finset.range (ℓ+1), Polynomial.eval x (Polynomial.hasseDeriv i ((A t).coeff j)) *
            Polynomial.eval x (((Psi p n f) ^ (t:ℕ)).coeff (ℓ - i)) * x ^ j := by
    intro t j
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, hasseDeriv_mul_Tf_pow_eval p n ℓ f hx ((A t).coeff j) (t:ℕ), hxq j]
    rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun j hj => hstep3 t j))]
  -- compare with Cond
  rw [Cond, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Polynomial.eval_finsetSum]
  -- LHS: Σ_j Σ_i [term], RHS: Σ_k eval (Σ_{j≤B} X^j * hasseDeriv k (A_t.coeff j) * (Psi^t).coeff (ℓ-k))
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_range] at hk
  have hk' : k ≤ ℓ := Nat.lt_succ_iff.mp hk
  -- LHS now: Σ_j (eval x (hasseDeriv k (A_t.coeff j)) * eval x ((Psi^t).coeff (ℓ-k)) * x^j)
  have hL : (∑ j ∈ Finset.range ((A t).natDegree + 1),
        Polynomial.eval x (Polynomial.hasseDeriv k ((A t).coeff j)) *
          Polynomial.eval x (((Psi p n f) ^ (t:ℕ)).coeff (ℓ - k)) * x ^ j)
      = ∑ j ∈ Finset.range (B + 1),
        Polynomial.eval x (Polynomial.hasseDeriv k ((A t).coeff j)) *
          Polynomial.eval x (((Psi p n f) ^ (t:ℕ)).coeff (ℓ - k)) * x ^ j := by
    refine Finset.sum_subset ?_ ?_
    · intro j hj
      rw [Finset.mem_range] at hj ⊢
      exact lt_of_lt_of_le hj (Nat.succ_le_succ (hAn t))
    · intro j _ hj
      rw [Finset.mem_range, not_lt] at hj
      have hzero : (A t).coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hzero, map_zero, Polynomial.eval_zero, zero_mul, zero_mul]
  rw [hL]
  -- RHS: eval of the sum
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  ring

end

section
variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] [Fintype F]

theorem Tf_natDegree {n : ℕ} (hn : 1 ≤ n) (f : Polynomial F) (hf : 1 ≤ f.natDegree) :
    (Tf p n f).natDegree = p ^ (n-1) * f.natDegree := by
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hle : (Tf p n f).natDegree ≤ p ^ (n-1) * f.natDegree := by
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le ?_)
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [Function.comp_apply]
    rw [Polynomial.natDegree_pow]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
  refine le_antisymm hle ?_
  have hterm : (f ^ p ^ (n-1)).coeff (p ^ (n-1) * f.natDegree) ≠ 0 := by
    rw [show p ^ (n-1) * f.natDegree = (f ^ p ^ (n-1)).natDegree by rw [Polynomial.natDegree_pow]]
    exact Polynomial.leadingCoeff_ne_zero.mpr (pow_ne_zero _ fun h => by
      rw [h, Polynomial.natDegree_zero] at hf; omega)
  have hcoeff : (Tf p n f).coeff (p ^ (n-1) * f.natDegree) ≠ 0 := by
    rw [Tf, Polynomial.finsetSum_coeff, Finset.sum_eq_single (n-1)]
    · exact hterm
    · intro i hi hne
      rw [Finset.mem_range] at hi
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [Polynomial.natDegree_pow]
      exact Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by omega) (by omega)) (by omega)
    · intro hmem
      exact absurd (Finset.mem_range.mpr (by omega)) hmem
  exact le_natDegree_of_ne_zero hcoeff

end

section
variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] [Fintype F]

theorem Raux_natDegree_le (n B A₀ : ℕ) (f : Polynomial F) (A : Fin p → Polynomial (Polynomial F))
    (hAd : ∀ t j, ((A t).coeff j).natDegree ≤ A₀) (hAn : ∀ t, (A t).natDegree ≤ B) :
    (Raux p n f A).natDegree ≤ A₀ + Fintype.card F * B + (p-1) * (Tf p n f).natDegree := by
  rw [Raux_eq_sum]
  refine le_trans (Polynomial.natDegree_sum_le (Finset.univ : Finset (Fin p)) _) ?_
  refine Finset.sup_le (fun t _ => ?_)
  refine le_trans (Polynomial.natDegree_sum_le (Finset.range ((A t).natDegree + 1)) _) ?_
  refine Finset.sup_le (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  have h2 : ((Polynomial.X : Polynomial F) ^ (Fintype.card F * j)).natDegree = Fintype.card F * j := by simp
  have h3 : (((Tf p n f) ^ (t:ℕ))).natDegree = (t:ℕ) * (Tf p n f).natDegree :=
    Polynomial.natDegree_pow _ _
  calc ((A t).coeff j * (Polynomial.X : Polynomial F) ^ (Fintype.card F * j) * (Tf p n f) ^ (t:ℕ)).natDegree
      ≤ ((A t).coeff j * (Polynomial.X : Polynomial F) ^ (Fintype.card F * j)).natDegree + (((Tf p n f) ^ (t:ℕ))).natDegree := Polynomial.natDegree_mul_le
    _ ≤ (((A t).coeff j).natDegree + ((Polynomial.X : Polynomial F) ^ (Fintype.card F * j)).natDegree) + (((Tf p n f) ^ (t:ℕ))).natDegree := by
        exact Nat.add_le_add_right Polynomial.natDegree_mul_le _
    _ = ((A t).coeff j).natDegree + Fintype.card F * j + (t:ℕ) * (Tf p n f).natDegree := by rw [h2, h3]
    _ ≤ A₀ + Fintype.card F * B + (p-1) * (Tf p n f).natDegree := by
        have h4 : (t:ℕ) ≤ p - 1 := by have := t.isLt; omega
        have hjB : j ≤ B := by have h := hAn t; omega
        have h5 : Fintype.card F * j ≤ Fintype.card F * B := Nat.mul_le_mul_left _ hjB
        have h6 : (t:ℕ) * (Tf p n f).natDegree ≤ (p-1) * (Tf p n f).natDegree := Nat.mul_le_mul_right _ h4
        have h7 : ((A t).coeff j).natDegree ≤ A₀ := hAd t j
        exact Nat.add_le_add (Nat.add_le_add h7 h5) h6

end

section
variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] [Fintype F]

theorem additive_count (n M A₀ B : ℕ) [DecidableEq F] (hq : Fintype.card F = p ^ n)
    (f : Polynomial F) (hMq : ∀ ℓ < M, ℓ < Fintype.card F)
    (A : Fin p → Polynomial (Polynomial F))
    (hAd : ∀ t j, ((A t).coeff j).natDegree ≤ A₀) (hAn : ∀ t, (A t).natDegree ≤ B)
    (hcond : ∀ ℓ < M, Cond p n B f A ℓ = 0)
    (hne : Raux p n f A ≠ 0) (hn : 1 ≤ n) (hf : 1 ≤ f.natDegree) :
    (({x : F | Polynomial.eval x (Tf p n f) = 0} : Set F).ncard) * M ≤
      A₀ + Fintype.card F * B + (p - 1) * (p ^ (n-1) * f.natDegree) := by
  have hdvd : ∀ x ∈ ({x : F | Polynomial.eval x (Tf p n f) = 0} : Set F).toFinset,
      (Polynomial.X - Polynomial.C x) ^ M ∣ Raux p n f A := by
    intro x hx
    rw [Set.mem_toFinset, Set.mem_ofPred_eq] at hx
    refine Commons.NumberTheory.Stepanov.X_sub_C_pow_dvd_of_hasseDeriv (fun ℓ hℓ => ?_)
    rw [hasseDeriv_Raux_eval n B ℓ hq (hMq ℓ hℓ) f A hAn hx, hcond ℓ hℓ, Polynomial.eval_zero]
  have hcount := Commons.NumberTheory.Stepanov.card_mul_le_natDegree_of_pow_dvd hne hdvd
  rw [Set.ncard_eq_toFinset_card']
  exact hcount.trans (le_trans (Raux_natDegree_le n B A₀ f A hAd hAn)
    (by rw [Tf_natDegree hn f hf]))

end

section
variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]

/-- Window separation: for `t ≠ t' < p` and `d < p` prime to `p`, the "starts" `p*j + t*d`
are all distinct. -/
theorem window_no_tie {d t t' j j' : ℕ} (hd1 : 1 ≤ d) (hdp : d < p) (ht : t < p) (ht' : t' < p)
    (h : p * j + t * d = p * j' + t' * d) : t = t' ∧ j = j' := by
  have hpd : ¬ p ∣ d := by
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hcop : p.Coprime d := (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hpd
  have hmod : t * d ≡ t' * d [MOD p] := by
    have h1 : p * j + t * d ≡ t * d [MOD p] := by
      have : p * j ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right p j)
      simpa using this.add_right (t * d)
    have h2 : p * j' + t' * d ≡ t' * d [MOD p] := by
      have : p * j' ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right p j')
      simpa using this.add_right (t' * d)
    have h3 : p * j + t * d ≡ p * j' + t' * d [MOD p] := by rw [h]
    calc t * d ≡ p * j + t * d [MOD p] := h1.symm
      _ ≡ p * j' + t' * d [MOD p] := h3
      _ ≡ t' * d [MOD p] := h2
  have ht_eq : t ≡ t' [MOD p] := by
    have hcancel := Nat.ModEq.cancel_right_div_gcd (m := p) (a := t) (b := t') (c := d)
      (Fact.out : Nat.Prime p).pos hmod
    rw [hcop] at hcancel
    simpa using hcancel
  have htt : t = t' := ht_eq.eq_of_lt_of_lt ht ht'
  subst htt
  have : p * j = p * j' := by omega
  exact ⟨rfl, Nat.mul_left_cancel (Fact.out : Nat.Prime p).pos this⟩

end

section
variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] [Fintype F]

theorem term_natDegree_le (n : ℕ) (f : Polynomial F) (A : Fin p → Polynomial (Polynomial F))
    (t : Fin p) (j : ℕ) :
    ((A t).coeff j * (Polynomial.X : Polynomial F) ^ (Fintype.card F * j) * (Tf p n f) ^ (t:ℕ)).natDegree
      ≤ ((A t).coeff j).natDegree + Fintype.card F * j + (t:ℕ) * (Tf p n f).natDegree := by
  have h2 : ((Polynomial.X : Polynomial F) ^ (Fintype.card F * j)).natDegree = Fintype.card F * j := by simp
  have h3 : (((Tf p n f) ^ (t:ℕ))).natDegree = (t:ℕ) * (Tf p n f).natDegree := Polynomial.natDegree_pow _ _
  calc ((A t).coeff j * (Polynomial.X : Polynomial F) ^ (Fintype.card F * j) * (Tf p n f) ^ (t:ℕ)).natDegree
      ≤ ((A t).coeff j * (Polynomial.X : Polynomial F) ^ (Fintype.card F * j)).natDegree + (((Tf p n f) ^ (t:ℕ))).natDegree := Polynomial.natDegree_mul_le
    _ ≤ (((A t).coeff j).natDegree + ((Polynomial.X : Polynomial F) ^ (Fintype.card F * j)).natDegree) + (((Tf p n f) ^ (t:ℕ))).natDegree := by
        exact Nat.add_le_add_right Polynomial.natDegree_mul_le _
    _ = ((A t).coeff j).natDegree + Fintype.card F * j + (t:ℕ) * (Tf p n f).natDegree := by rw [h2, h3]

theorem Raux_eq_sum_uniform (n B : ℕ) (f : Polynomial F) (A : Fin p → Polynomial (Polynomial F))
    (hAn : ∀ t, (A t).natDegree ≤ B) :
    Raux p n f A = ∑ t : Fin p, ∑ j ∈ Finset.range (B+1),
      (A t).coeff j * (Polynomial.X : Polynomial F) ^ (Fintype.card F * j) * (Tf p n f) ^ (t:ℕ) := by
  rw [Raux_eq_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  refine Finset.sum_subset (fun j hj => ?_) (fun j _ hj => ?_)
  · rw [Finset.mem_range] at hj ⊢
    have := hAn t; omega
  · rw [Finset.mem_range, not_lt] at hj
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul, zero_mul]

end

section
variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] [Fintype F]

theorem start_ne {n : ℕ} (hn : 1 ≤ n) {d : ℕ} (hd1 : 1 ≤ d) (hdp : d < p)
    (hq : Fintype.card F = p ^ n) {t t' : Fin p} {j j' : ℕ}
    (h : Fintype.card F * j + (t:ℕ) * (p ^ (n-1) * d) = Fintype.card F * j' + (t':ℕ) * (p ^ (n-1) * d)) :
    (t : ℕ) = t' ∧ j = j' := by
  have hpow : 0 < p ^ (n-1) := pow_pos (Fact.out : Nat.Prime p).pos _
  have hn' : n - 1 + 1 = n := by omega
  have hkey : p ^ (n-1) * (p * j + (t:ℕ) * d) = p ^ (n-1) * (p * j' + (t':ℕ) * d) := by
    have hpn : p ^ n = p ^ (n-1) * p := by
      conv_lhs => rw [← hn']
      rw [pow_succ]
    have e1 : p ^ (n-1) * (p * j + (t:ℕ) * d) = Fintype.card F * j + (t:ℕ) * (p ^ (n-1) * d) := by
      rw [hq, hpn]; ring
    have e2 : p ^ (n-1) * (p * j' + (t':ℕ) * d) = Fintype.card F * j' + (t':ℕ) * (p ^ (n-1) * d) := by
      rw [hq, hpn]; ring
    rw [e1, e2, h]
  have h' : p * j + (t:ℕ) * d = p * j' + (t':ℕ) * d := Nat.mul_left_cancel hpow hkey
  have h2 : p * j + (t:ℕ) * d = p * j' + (t':ℕ) * d := h'
  have h3 := window_no_tie (p := p) hd1 hdp t.isLt t'.isLt h2
  exact ⟨by exact_mod_cast h3.1, h3.2⟩

theorem start_gap {n : ℕ} (hn : 1 ≤ n) {d : ℕ} (hd1 : 1 ≤ d) (hdp : d < p)
    (hq : Fintype.card F = p ^ n) {t t' : Fin p} {j j' : ℕ} (hne : (t,j) ≠ (t',j'))
    (hle : Fintype.card F * j + (t:ℕ) * (p ^ (n-1) * d) ≤ Fintype.card F * j' + (t':ℕ) * (p ^ (n-1) * d)) :
    Fintype.card F * j + (t:ℕ) * (p ^ (n-1) * d) + p ^ (n-1)
      ≤ Fintype.card F * j' + (t':ℕ) * (p ^ (n-1) * d) := by
  have hpow : 0 < p ^ (n-1) := pow_pos (Fact.out : Nat.Prime p).pos _
  have hn' : n - 1 + 1 = n := by omega
  have hpn : p ^ n = p ^ (n-1) * p := by
    conv_lhs => rw [← hn']
    rw [pow_succ]
  have hred : p * j + (t:ℕ) * d ≤ p * j' + (t':ℕ) * d := by
    have := hle
    rw [hq, hpn] at this
    have e1 : p ^ (n-1) * p * j + (t:ℕ) * (p ^ (n-1) * d) = p ^ (n-1) * (p * j + (t:ℕ) * d) := by ring
    have e2 : p ^ (n-1) * p * j' + (t':ℕ) * (p ^ (n-1) * d) = p ^ (n-1) * (p * j' + (t':ℕ) * d) := by ring
    rw [e1, e2] at this
    exact Nat.le_of_mul_le_mul_left this hpow
  have hlt : p * j + (t:ℕ) * d < p * j' + (t':ℕ) * d := by
    rcases lt_or_eq_of_le hred with h | h
    · exact h
    · exfalso
      have h2 : p * j + (t:ℕ) * d = p * j' + (t':ℕ) * d := h
      have h3 := window_no_tie (p := p) hd1 hdp t.isLt t'.isLt h2
      refine hne (Prod.ext ?_ ?_)
      · exact Fin.ext (by exact_mod_cast h3.1)
      · exact h3.2
  have h1 : p * j + (t:ℕ) * d + 1 ≤ p * j' + (t':ℕ) * d := hlt
  calc Fintype.card F * j + (t:ℕ) * (p ^ (n-1) * d) + p ^ (n-1)
      = p ^ (n-1) * (p * j + (t:ℕ) * d) + p ^ (n-1) := by rw [hq, hpn]; ring
    _ = p ^ (n-1) * ((p * j + (t:ℕ) * d) + 1) := by ring
    _ ≤ p ^ (n-1) * (p * j' + (t':ℕ) * d) := Nat.mul_le_mul_left _ h1
    _ = Fintype.card F * j' + (t':ℕ) * (p ^ (n-1) * d) := by rw [hq, hpn]; ring


end

section
variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] [Fintype F]

theorem term_natDegree_eq (n : ℕ) (f : Polynomial F) (hf : (Tf p n f) ≠ 0)
    (A : Fin p → Polynomial (Polynomial F)) (t : Fin p) (j : ℕ) (hj : (A t).coeff j ≠ 0) :
    ((A t).coeff j * (Polynomial.X : Polynomial F) ^ (Fintype.card F * j) * (Tf p n f) ^ (t:ℕ)).natDegree
      = Fintype.card F * j + (t:ℕ) * (Tf p n f).natDegree + ((A t).coeff j).natDegree := by
  have hX : ((Polynomial.X : Polynomial F) ^ (Fintype.card F * j)) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  have hT : ((Tf p n f) ^ (t:ℕ)) ≠ 0 := pow_ne_zero _ hf
  have hX' : ((Polynomial.X : Polynomial F) ^ (Fintype.card F * j)).natDegree = Fintype.card F * j := by simp
  have hT' : (((Tf p n f)) ^ (t:ℕ)).natDegree = (t:ℕ) * (Tf p n f).natDegree := Polynomial.natDegree_pow _ _
  rw [Polynomial.natDegree_mul (mul_ne_zero hj hX) hT, Polynomial.natDegree_mul hj hX, hX', hT']
  ring

theorem additive_indep (n : ℕ) (hn : 1 ≤ n) (f : Polynomial F) (hf1 : 1 ≤ f.natDegree)
    (hfp : f.natDegree < p) [DecidableEq F] (hq : Fintype.card F = p ^ n)
    (A₀ B : ℕ) (hA₀ : p * (A₀ + 1) ≤ Fintype.card F)
    (A : Fin p → Polynomial (Polynomial F))
    (hAd : ∀ t j, ((A t).coeff j).natDegree ≤ A₀) (hAn : ∀ t, (A t).natDegree ≤ B)
    (hR : Raux p n f A = 0) : ∀ t, A t = 0 := by
  classical
  have hpne : 0 < p := (Fact.out : Nat.Prime p).pos
  have hD : (Tf p n f).natDegree = p ^ (n-1) * f.natDegree := Tf_natDegree hn f hf1
  have hTf0 : (Tf p n f) ≠ 0 := by
    intro h0
    have h1 : (Tf p n f).natDegree = 0 := by rw [h0, Polynomial.natDegree_zero]
    rw [hD] at h1
    have : 0 < p ^ (n-1) * f.natDegree := Nat.mul_pos (pow_pos hpne _) (by omega)
    omega
  have hA₀lt : A₀ < p ^ (n-1) := by
    have h1 : p * (A₀ + 1) ≤ p ^ n := by rw [← hq]; exact hA₀
    have hpn : p ^ n = p ^ (n-1) * p := by
      have hn1 : n - 1 + 1 = n := by omega
      calc p ^ n = p ^ (n - 1 + 1) := by rw [hn1]
        _ = p ^ (n-1) * p := pow_succ _ _
    rw [hpn, mul_comm p (A₀+1)] at h1
    have := Nat.le_of_mul_le_mul_right h1 hpne
    omega
  by_contra hcon
  push_neg at hcon
  have hex : ∃ tt : Fin p, ∃ j, j ≤ B ∧ (A tt).coeff j ≠ 0 := by
    obtain ⟨t, ht⟩ := hcon
    by_contra hcontra
    push_neg at hcontra
    refine ht (Polynomial.ext (fun j => ?_))
    by_cases hj : j ≤ B
    · exact hcontra t j hj
    · have hlt : (A t).natDegree < j := by have := hAn t; omega
      exact Polynomial.coeff_eq_zero_of_natDegree_lt hlt
  obtain ⟨t₀, j₀, hj₀, hne₀⟩ := hex
  set w : Fin p × ℕ → ℕ := fun u => Fintype.card F * u.2 + (u.1 : ℕ) * (Tf p n f).natDegree with hw
  set S : Finset (Fin p × ℕ) := (Finset.univ ×ˢ Finset.range (B+1)).filter (fun u => (A u.1).coeff u.2 ≠ 0) with hS
  have hSmem : (t₀, j₀) ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨Finset.mem_univ _, by omega⟩, hne₀⟩
  obtain ⟨u₁, hmem₁, hmax⟩ := Finset.exists_max_image S w ⟨_, hSmem⟩
  obtain ⟨t₁, j₁⟩ := u₁
  rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hmem₁
  obtain ⟨⟨-, hj₁B⟩, hcoeff₁⟩ := hmem₁
  set N := w (t₁, j₁) + ((A t₁).coeff j₁).natDegree with hN
  -- any term's degree
  have htermdeg : ∀ t j, (t,j) ∈ S →
      ((A t).coeff j * (Polynomial.X : Polynomial F) ^ (Fintype.card F * j) * (Tf p n f) ^ (t:ℕ)).natDegree
        = w (t,j) + ((A t).coeff j).natDegree := by
    intro t j hj
    have hj' : (A t).coeff j ≠ 0 := by
      have := hj
      rw [hS, Finset.mem_filter] at this
      exact this.2
    rw [term_natDegree_eq n f hTf0 A t j hj', hw, hD]
  -- the key: a non-maximal term has coefficient 0 at N
  have hzero : ∀ (u : Fin p × ℕ), u ∈ S → u ≠ (t₁, j₁) →
      ((A u.1).coeff u.2 * (Polynomial.X : Polynomial F) ^ (Fintype.card F * u.2)
        * (Tf p n f) ^ (u.1:ℕ)).coeff N = 0 := by
    intro u hu hune
    obtain ⟨t, j⟩ := u
    have hw' : ∀ v : Fin p × ℕ,
        w v = Fintype.card F * v.2 + (v.1:ℕ) * (p ^ (n-1) * f.natDegree) := by
      intro v
      rw [hw]; simp only; rw [hD]
    have hred : Fintype.card F * j + (t:ℕ) * (p ^ (n-1) * f.natDegree) ≤
        Fintype.card F * j₁ + (t₁:ℕ) * (p ^ (n-1) * f.natDegree) := by
      rw [← hw' (t,j), ← hw' (t₁,j₁)]
      exact hmax _ hu
    have hne2 : ((t,j) : Fin p × ℕ) ≠ (t₁, j₁) := by
      intro hh
      exact hune (by rw [hh])
    have hne3 : (t,j) ≠ (t₁, j₁) := fun hh => hune (by rw [hh])
    have hgap := start_gap hn hf1 hfp hq hne3 hred
    have hgap' : w (t,j) + p ^ (n-1) ≤ w (t₁,j₁) := by
      rw [hw' (t,j), hw' (t₁,j₁)]; exact hgap
    have hlt : w (t,j) + A₀ < N := by
      have h2 : w (t,j) + A₀ < w (t₁,j₁) := by omega
      omega
    have hdec : (A t).coeff j = 0 ∨ (A t).coeff j ≠ 0 := eq_or_ne _ _
    rcases hdec with h0 | h0
    · rw [h0, zero_mul, zero_mul, Polynomial.coeff_zero]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
      rw [htermdeg t j hu]
      exact lt_of_le_of_lt (Nat.add_le_add_left (hAd t j) _) hlt
  -- conclude
  have hkey : (Raux p n f A).coeff N ≠ 0 := by
    rw [Raux_eq_sum_uniform n B f A hAn, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single t₁ ?_ ?_]
    · rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single j₁ ?_ ?_]
      · have hmem : (t₁, j₁) ∈ S := by
          rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          exact ⟨⟨Finset.mem_univ _, by omega⟩, hcoeff₁⟩
        have hdeg : ((A t₁).coeff j₁ * (Polynomial.X : Polynomial F) ^ (Fintype.card F * j₁)
            * (Tf p n f) ^ (t₁:ℕ)).natDegree = N := by
          rw [htermdeg t₁ j₁ hmem, hN]
        rw [← hdeg]
        exact Polynomial.leadingCoeff_ne_zero.mpr
          (mul_ne_zero (mul_ne_zero hcoeff₁ (pow_ne_zero _ Polynomial.X_ne_zero))
            (pow_ne_zero _ hTf0))
      · intro j hj hjne
        by_cases hjc : (A t₁).coeff j = 0
        · rw [hjc, zero_mul, zero_mul, Polynomial.coeff_zero]
        · have hmem : (t₁, j) ∈ S := by
            rw [hS, Finset.mem_filter, Finset.mem_product]
            exact ⟨⟨Finset.mem_univ _, hj⟩, hjc⟩
          exact hzero (t₁, j) hmem (by intro hh; exact hjne (by simpa using congrArg Prod.snd hh))
      · intro hmem
        exact absurd (by rw [Finset.mem_range]; omega) hmem
    · intro t ht htne
      rw [Polynomial.finsetSum_coeff]
      refine Finset.sum_eq_zero (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      by_cases hjc : (A t).coeff j = 0
      · rw [hjc, zero_mul, zero_mul, Polynomial.coeff_zero]
      · have hmem : (t, j) ∈ S := by
          rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          exact ⟨⟨Finset.mem_univ _, by omega⟩, hjc⟩
        exact hzero (t, j) hmem (by intro hh; exact htne (congrArg Prod.fst hh))
    · intro hmem
      exact absurd (Finset.mem_univ t₁) hmem
  rw [hR] at hkey
  exact hkey rfl

end

section
variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] [Fintype F] [DecidableEq F]

theorem sum_bounds (M A₀ B dd : ℕ) :
    (∑ ℓ : Fin M, (A₀ + B + dd * (ℓ:ℕ) + 1)) = M * (A₀ + B + 1) + dd * (M * (M-1) / 2) := by
  rw [Finset.sum_fin_eq_sum_range]
  have h1 : ∀ i ∈ Finset.range M,
      (if h : i < M then A₀ + B + dd * (↑(⟨i, h⟩ : Fin M)) + 1 else 0) = (A₀ + B + 1) + dd * i := by
    intro i hi
    rw [dif_pos (Finset.mem_range.mp hi)]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    ← Finset.mul_sum, Finset.sum_range_id]
  simp only [smul_eq_mul]

end

section
variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] [Fintype F]

theorem Cond_natDegree_le (n B A₀ : ℕ) (f : Polynomial F) (A : Fin p → Polynomial (Polynomial F))
    (hAd : ∀ t j, ((A t).coeff j).natDegree ≤ A₀) (ℓ : ℕ) :
    (Cond p n B f A ℓ).natDegree ≤ A₀ + B + (f.natDegree - 1) * ℓ := by
  rw [Cond]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Finset.sup_le (fun t _ => ?_)
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Finset.sup_le (fun k hk => ?_)
  rw [Finset.mem_range] at hk
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Finset.sup_le (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  have h1 : ((Polynomial.X : Polynomial F) ^ j).natDegree = j := by simp
  have h2 : (Polynomial.hasseDeriv k ((A t).coeff j)).natDegree ≤ A₀ - k :=
    le_trans (Polynomial.natDegree_hasseDeriv_le _ _) (Nat.sub_le_sub_right (hAd t j) k)
  have h3 : (((Psi p n f) ^ (t:ℕ)).coeff (ℓ - k)).natDegree ≤ (f.natDegree - 1) * (ℓ - k) :=
    pow_coeff_natDegree_le (Psi p n f) (f.natDegree - 1) (Psi_coeff_zero p n f)
      (fun s hs => Psi_coeff_natDegree_le p n f hs) (t:ℕ) (ℓ - k)
  calc ((Polynomial.X : Polynomial F) ^ j * Polynomial.hasseDeriv k ((A t).coeff j)
          * ((Psi p n f) ^ (t:ℕ)).coeff (ℓ - k)).natDegree
      ≤ ((Polynomial.X : Polynomial F) ^ j * Polynomial.hasseDeriv k ((A t).coeff j)).natDegree
          + (((Psi p n f) ^ (t:ℕ)).coeff (ℓ - k)).natDegree := Polynomial.natDegree_mul_le
    _ ≤ j + (A₀ - k) + (f.natDegree - 1) * (ℓ - k) := by
        refine Nat.add_le_add ?_ h3
        refine le_trans Polynomial.natDegree_mul_le ?_
        exact Nat.add_le_add (le_of_eq h1) h2
    _ ≤ A₀ + B + (f.natDegree - 1) * ℓ := by
        have h4 : j ≤ B := by omega
        have hk' : k ≤ ℓ := Nat.lt_succ_iff.mp hk
        have h5 : (f.natDegree - 1) * (ℓ - k) ≤ (f.natDegree - 1) * ℓ :=
          Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        omega


end

section
variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] [Fintype F]

/-- The `ℓ`-th Stepanov condition as a linear map of the auxiliary family. -/
noncomputable def CondL (n B : ℕ) (f : Polynomial F) (ℓ : ℕ) :
    (Fin p → Polynomial (Polynomial F)) →ₗ[F] Polynomial F :=
  ∑ t : Fin p, ∑ k ∈ Finset.range (ℓ+1), ∑ j ∈ Finset.range (B+1),
    (LinearMap.mulRight F ((Polynomial.X : Polynomial F) ^ j *
        ((Psi p n f) ^ (t:ℕ)).coeff (ℓ - k))).comp
      ((Polynomial.hasseDeriv k).comp
        (((Polynomial.lcoeff (Polynomial F) j).restrictScalars F).comp (LinearMap.proj t)))

theorem CondL_apply (n B : ℕ) (f : Polynomial F) (ℓ : ℕ)
    (A : Fin p → Polynomial (Polynomial F)) :
    CondL (p := p) n B f ℓ A = Cond p n B f A ℓ := by
  rw [CondL, Cond, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
    LinearMap.restrictScalars_apply, LinearMap.proj_apply, Polynomial.lcoeff_apply]
  ring

end

section
variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] [Fintype F]

/-- The monomial `X ^ i * Y ^ j` in `F[X][Y]`. -/
noncomputable def mono (i j : ℕ) : Polynomial (Polynomial F) :=
  Polynomial.C ((Polynomial.X : Polynomial F) ^ i) * (Polynomial.X : Polynomial (Polynomial F)) ^ j

theorem mono_coeff (i j i' j' : ℕ) :
    (Polynomial.coeff (mono (F := F) i j) j').coeff i' =
      if j' = j then (if i' = i then (1 : F) else 0) else 0 := by
  rw [mono, Polynomial.coeff_C_mul_X_pow]
  by_cases h : j' = j
  · rw [if_pos h, Polynomial.coeff_X_pow]
    simp [h]
  · rw [if_neg h, Polynomial.coeff_zero]
    simp [h]

noncomputable def cLinear : F →ₗ[F] Polynomial (Polynomial F) :=
  { toFun := fun x => Polynomial.C (Polynomial.C x)
    map_add' := by intro x y; simp
    map_smul' := by intro c x; simp }

noncomputable def psiTerm (i j : ℕ) : F →ₗ[F] Polynomial (Polynomial F) :=
  (LinearMap.mulRight F (mono (F := F) i j)).comp (cLinear (F := F))

/-- The monomial map: coefficient data `a` gives the auxiliary family
`A t = ∑_{i,j} a t i j · X^i Y^j`. -/
noncomputable def psiL (A₀ B : ℕ) :
    (Fin p → Fin (A₀+1) → Fin (B+1) → F) →ₗ[F] (Fin p → Polynomial (Polynomial F)) :=
  LinearMap.pi (fun t : Fin p =>
    ∑ i : Fin (A₀+1), ∑ j : Fin (B+1),
      (psiTerm (F := F) (i:ℕ) (j:ℕ)).comp
        ((LinearMap.proj (φ := fun _ : Fin (B+1) => F) j).comp
          ((LinearMap.proj (φ := fun _ : Fin (A₀+1) => (Fin (B+1) → F)) i).comp
            (LinearMap.proj (φ := fun _ : Fin p => (Fin (A₀+1) → Fin (B+1) → F)) t))))

theorem psiL_apply (A₀ B : ℕ) (a : Fin p → Fin (A₀+1) → Fin (B+1) → F) (t : Fin p) :
    psiL (p := p) A₀ B a t = ∑ i : Fin (A₀+1), ∑ j : Fin (B+1),
      Polynomial.C (Polynomial.C (a t i j)) * mono (F := F) (i:ℕ) (j:ℕ) := by
  rw [psiL, LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.proj_apply, LinearMap.proj_apply, psiTerm, LinearMap.comp_apply,
    LinearMap.mulRight_apply]
  rfl


theorem coeff_C_mono (c : F) (i j i' j' : ℕ) :
    (Polynomial.coeff (Polynomial.C (Polynomial.C c) * mono (F := F) i j) j').coeff i'
      = if j' = j then (if i' = i then c else 0) else 0 := by
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, mono_coeff]
  by_cases h : j' = j
  · rw [if_pos h, if_pos h]
    by_cases h2 : i' = i
    · rw [if_pos h2, if_pos h2, mul_one]
    · rw [if_neg h2, if_neg h2, mul_zero]
  · rw [if_neg h, if_neg h, mul_zero]

theorem psiL_coeff (A₀ B : ℕ) (a : Fin p → Fin (A₀+1) → Fin (B+1) → F)
    (t : Fin p) (i : Fin (A₀+1)) (j : Fin (B+1)) :
    (Polynomial.coeff (psiL (p := p) A₀ B a t) (j:ℕ)).coeff (i:ℕ) = a t i j := by
  rw [psiL_apply]
  simp only [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · rw [coeff_C_mono, if_pos rfl, if_pos rfl]
    · intro j' _ hjne
      rw [coeff_C_mono, if_neg (fun h => hjne (Fin.ext h.symm))]
    · intro hmem
      exact absurd (Finset.mem_univ j) hmem
  · intro i' _ hine
    refine Finset.sum_eq_zero (fun j' _ => ?_)
    rw [coeff_C_mono]
    by_cases h : (j:ℕ) = (j':ℕ)
    · rw [if_pos h, if_neg (fun hh => hine (Fin.ext hh.symm))]
    · rw [if_neg h]
  · intro hmem
    exact absurd (Finset.mem_univ i) hmem

end

section
variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] [Fintype F]

theorem coeff_C_mono_natDegree_le (c : F) (i j j' : ℕ) :
    ((Polynomial.coeff (Polynomial.C (Polynomial.C c) * mono (F:=F) i j) j').natDegree) ≤ i := by
  rw [Polynomial.coeff_C_mul, mono, Polynomial.coeff_C_mul_X_pow]
  by_cases h : j' = j
  · rw [if_pos h]
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_C, Nat.zero_add]
    simp
  · rw [if_neg h]
    simp

theorem psiL_coeff_natDegree_le (A₀ B : ℕ)
    (w : Fin p → Fin (A₀+1) → Fin (B+1) → F) (t : Fin p) (j : ℕ) :
    ((psiL (p:=p) A₀ B w t).coeff j).natDegree ≤ A₀ := by
  rw [psiL_apply]
  simp only [Polynomial.finsetSum_coeff]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Finset.sup_le (fun i _ => ?_)
  simp only [Function.comp_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Finset.sup_le (fun j' _ => ?_)
  simp only [Function.comp_apply]
  exact le_trans (coeff_C_mono_natDegree_le (w t i j') (i:ℕ) (j':ℕ) j) (Nat.lt_succ_iff.mp i.isLt)

theorem psiL_natDegree_le (A₀ B : ℕ)
    (w : Fin p → Fin (A₀+1) → Fin (B+1) → F) (t : Fin p) :
    (psiL (p:=p) A₀ B w t).natDegree ≤ B := by
  rw [psiL_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Finset.sup_le (fun i _ => ?_)
  simp only [Function.comp_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Finset.sup_le (fun j _ => ?_)
  simp only [Function.comp_apply]
  have hm : (mono (F:=F) (i:ℕ) (j:ℕ)).natDegree ≤ (j:ℕ) := by
    rw [mono]
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_C, Nat.zero_add, Polynomial.natDegree_X_pow]
  calc (Polynomial.C (Polynomial.C (w t i j)) * mono (F:=F) (i:ℕ) (j:ℕ)).natDegree
      ≤ (Polynomial.C (Polynomial.C (w t i j))).natDegree + (mono (F:=F) (i:ℕ) (j:ℕ)).natDegree := Polynomial.natDegree_mul_le
    _ = (mono (F:=F) (i:ℕ) (j:ℕ)).natDegree := by rw [Polynomial.natDegree_C, Nat.zero_add]
    _ ≤ (j:ℕ) := hm
    _ ≤ B := Nat.lt_succ_iff.mp j.isLt

theorem psiL_injective (A₀ B : ℕ) : Function.Injective (psiL (F:=F) (p:=p) A₀ B) := by
  intro a b hab
  funext t i j
  have h := congrFun hab t
  have h2 : (Polynomial.coeff (psiL (p:=p) A₀ B a t) (j:ℕ)).coeff (i:ℕ)
      = (Polynomial.coeff (psiL (p:=p) A₀ B b t) (j:ℕ)).coeff (i:ℕ) := by rw [h]
  rwa [psiL_coeff, psiL_coeff] at h2

end

section
variable {F : Type*} [Fintype F] [DecidableEq F]

theorem card_pi_fin_pow (M : ℕ) (L : Fin M → ℕ) :
    Fintype.card (∀ ℓ : Fin M, Fin (L ℓ) → F)
      = Fintype.card F ^ (∑ ℓ : Fin M, L ℓ) := by
  rw [Fintype.card_pi]
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl (fun ℓ _ => ?_)
  rw [Fintype.card_fun, Fintype.card_fin]

theorem card_domain (p A₀ B : ℕ) :
    Fintype.card (Fin p → Fin (A₀+1) → Fin (B+1) → F)
      = Fintype.card F ^ (p * (A₀+1) * (B+1)) := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fun]
  simp only [Fintype.card_fin]
  rw [← pow_mul, ← pow_mul]
  congr 1
  ring

end

section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {p : ℕ} [Fact p.Prime] [CharP F p]

theorem eq_zero_of_coeff_eq_zero_of_natDegree_lt {q : Polynomial F} {N : ℕ}
    (hdeg : q.natDegree < N) (h : ∀ k, k < N → q.coeff k = 0) : q = 0 := by
  ext k
  by_cases hk : k < N
  · exact h k hk
  · rw [Polynomial.coeff_zero]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem witness_exists {n M A₀ B : ℕ}
    (hn : 1 ≤ n) (hq : Fintype.card F = p ^ n) (f : Polynomial F)
    (hf1 : 1 ≤ f.natDegree) (hfp : f.natDegree < p)
    (hA₀q : p * (A₀ + 1) ≤ Fintype.card F)
    (hdim : M * (A₀ + B + 1) + (f.natDegree - 1) * (M * (M - 1) / 2)
      < p * (A₀ + 1) * (B + 1)) :
    ∃ A : Fin p → Polynomial (Polynomial F),
      (∀ t j, ((A t).coeff j).natDegree ≤ A₀) ∧ (∀ t, (A t).natDegree ≤ B) ∧
      (∀ ℓ, ℓ < M → Cond p n B f A ℓ = 0) ∧ Raux p n f A ≠ 0 := by
  classical
  set L : Fin M → ℕ := fun ℓ => A₀ + B + (f.natDegree - 1) * (ℓ : ℕ) + 1 with hL
  set Φ : (Fin p → Fin (A₀+1) → Fin (B+1) → F) →ₗ[F] (∀ ℓ : Fin M, Fin (L ℓ) → F) :=
    (LinearMap.pi (fun ℓ : Fin M => LinearMap.pi (fun k : Fin (L ℓ) =>
      (Polynomial.lcoeff F (k:ℕ)).comp (CondL (p:=p) n B f (ℓ:ℕ))))).comp
      (psiL (p:=p) A₀ B) with hΦ
  have hq2 : 1 < Fintype.card F := by
    rw [hq]
    exact Nat.one_lt_pow (by omega) (Fact.out : Nat.Prime p).one_lt
  have hcardD : Fintype.card (Fin p → Fin (A₀+1) → Fin (B+1) → F)
      = Fintype.card F ^ (p * (A₀+1) * (B+1)) := card_domain p A₀ B
  have hcardC : Fintype.card (∀ ℓ : Fin M, Fin (L ℓ) → F)
      = Fintype.card F ^ (∑ ℓ : Fin M, L ℓ) := card_pi_fin_pow M L
  have hsum : (∑ ℓ : Fin M, L ℓ)
      = M * (A₀ + B + 1) + (f.natDegree - 1) * (M * (M - 1) / 2) := by
    rw [hL]; exact sum_bounds M A₀ B (f.natDegree - 1)
  have hpow : Fintype.card (∀ ℓ : Fin M, Fin (L ℓ) → F)
      < Fintype.card (Fin p → Fin (A₀+1) → Fin (B+1) → F) := by
    rw [hcardC, hcardD, hsum]
    exact Nat.pow_lt_pow_right hq2 hdim
  have hnInj : ¬ Function.Injective Φ := fun hinj =>
    absurd (Fintype.card_le_of_injective Φ hinj) (not_le.mpr hpow)
  obtain ⟨w, hw0, hwker⟩ : ∃ w : Fin p → Fin (A₀+1) → Fin (B+1) → F, w ≠ 0 ∧ Φ w = 0 := by
    by_contra h
    push_neg at h
    apply hnInj
    intro x y hxy
    have h1 : Φ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (by by_contra h3; exact h (x - y) h3 h1)
  have hAd : ∀ t j, ((psiL (p:=p) A₀ B w t).coeff j).natDegree ≤ A₀ :=
    fun t j => psiL_coeff_natDegree_le A₀ B w t j
  have hAn : ∀ t, (psiL (p:=p) A₀ B w t).natDegree ≤ B :=
    fun t => psiL_natDegree_le A₀ B w t
  have hker : ∀ (ℓ : Fin M) (k : ℕ), k < L ℓ →
      (CondL (p:=p) n B f (ℓ:ℕ) (psiL (p:=p) A₀ B w)).coeff k = 0 := by
    intro ℓ k hk
    have h1 : Φ w ℓ ⟨k, hk⟩ = 0 := by rw [hwker]; rfl
    rw [hΦ] at h1
    simpa only [LinearMap.comp_apply, LinearMap.pi_apply, Polynomial.lcoeff_apply] using h1
  refine ⟨psiL (p:=p) A₀ B w, hAd, hAn, ?_, ?_⟩
  · intro ℓ hℓ
    rw [← CondL_apply]
    refine eq_zero_of_coeff_eq_zero_of_natDegree_lt ?_ (fun k hk => hker ⟨ℓ, hℓ⟩ k hk)
    have h2 := Cond_natDegree_le (p:=p) n B A₀ f (psiL (p:=p) A₀ B w) hAd ℓ
    rw [CondL_apply]
    show (Cond p n B f (psiL (p:=p) A₀ B w) ℓ).natDegree < L ⟨ℓ, hℓ⟩
    rw [hL]
    dsimp only
    omega
  · intro hR
    have hA0 : ∀ t, psiL (p:=p) A₀ B w t = 0 :=
      additive_indep n hn f hf1 hfp hq A₀ B hA₀q (psiL (p:=p) A₀ B w) hAd hAn hR
    refine hw0 (psiL_injective (F:=F) (p:=p) A₀ B ?_)
    rw [show psiL (p:=p) A₀ B w = 0 from funext hA0, map_zero]

end

section RootCount
variable {F : Type*} [Field F] [Fintype F]

theorem ncard_roots_le (f : Polynomial F) (hf : f ≠ 0) :
    ({x : F | f.eval x = 0} : Set F).ncard ≤ f.natDegree := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  rw [show ({x : F | f.eval x = 0} : Set F).toFinset = Finset.univ.filter (fun x => f.eval x = 0) from by
        ext x; simp]
  refine Polynomial.card_le_degree_of_subset_roots (fun x hx => ?_)
  rw [Finset.mem_val, Finset.mem_filter] at hx
  rw [Polynomial.mem_roots hf, Polynomial.IsRoot.def]
  exact hx.2

end RootCount

section ArtinSchreier
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] {p : ℕ} [Fact p.Prime]
  [CharP E p] [Algebra (ZMod p) E]

theorem ZMod.pow_prime_pow (a : ZMod p) (i : ℕ) : a ^ p ^ i = a := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, pow_mul, ih, ZMod.pow_card]

noncomputable def phiMap : E →ₗ[ZMod p] E where
  toFun x := x ^ p - x
  map_add' x y := by rw [add_pow_char]; ring
  map_smul' a x := by
    show (a • x) ^ p - a • x = a • (x ^ p - x)
    rw [Algebra.smul_def a x]
    rw [Algebra.smul_def a (x ^ p - x)]
    rw [mul_pow, ← map_pow, ZMod.pow_card, mul_sub]

theorem phiMap_apply (x : E) : phiMap (p:=p) x = x ^ p - x := rfl

noncomputable def psiMap (n : ℕ) : E →ₗ[ZMod p] E where
  toFun x := ∑ i ∈ Finset.range n, x ^ (p ^ i)
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => add_pow_char_pow x y p i)
  map_smul' a x := by
    show (∑ i ∈ Finset.range n, (a • x) ^ (p ^ i)) = a • ∑ i ∈ Finset.range n, x ^ (p ^ i)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    show (a • x) ^ (p ^ i) = a • x ^ (p ^ i)
    rw [Algebra.smul_def a x]
    rw [Algebra.smul_def a (x ^ (p ^ i))]
    rw [mul_pow, ← map_pow, ZMod.pow_prime_pow]

theorem psiMap_apply (n : ℕ) (x : E) :
    psiMap (p:=p) n x = ∑ i ∈ Finset.range n, x ^ (p ^ i) := rfl

theorem psiMap_pow (n : ℕ) (x : E) :
    psiMap (p:=p) n (x ^ p) = ∑ i ∈ Finset.range n, x ^ (p ^ (i+1)) := by
  rw [psiMap_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← pow_mul, pow_succ']

theorem psiMap_phiMap (n : ℕ) {x : E} (hx : x ^ p ^ n = x) :
    psiMap (p:=p) n (phiMap (p:=p) x) = 0 := by
  have h1 : psiMap (p:=p) n (x ^ p) = psiMap (p:=p) n x := by
    rw [psiMap_pow, psiMap_apply]
    calc ∑ i ∈ Finset.range n, x ^ (p ^ (i+1))
        = (∑ i ∈ Finset.range (n+1), x ^ (p^i)) - x ^ (p^0) := by
          rw [Finset.sum_range_succ']; abel
      _ = ((∑ i ∈ Finset.range n, x ^ (p^i)) + x ^ (p^n)) - x ^ (p^0) := by
          rw [Finset.sum_range_succ]
      _ = ∑ i ∈ Finset.range n, x ^ (p^i) := by rw [hx]; simp
  rw [phiMap_apply, map_sub, h1, sub_self]

theorem phiMap_mem_ker_psiMap (hq : Fintype.card E = p ^ n) (x : E) :
    phiMap (p:=p) x ∈ (psiMap (p:=p) n).ker := by
  rw [LinearMap.mem_ker]
  exact psiMap_phiMap (p:=p) n (by rw [← hq]; exact FiniteField.pow_card x)

theorem range_phiMap_le_ker_psiMap (hq : Fintype.card E = p ^ n) :
    (phiMap (p:=p) (E:=E)).range ≤ (psiMap (p:=p) (E:=E) n).ker := by
  intro x hx
  rw [LinearMap.mem_range] at hx
  obtain ⟨y, rfl⟩ := hx
  exact phiMap_mem_ker_psiMap (p:=p) (E:=E) hq y

theorem ker_phiMap_ncard :
    ((phiMap (p:=p) (E:=E)).ker : Set E).ncard = p := by
  classical
  have hroot : ((phiMap (p:=p) (E:=E)).ker : Set E)
      = {x : E | (Polynomial.X ^ p - Polynomial.X : Polynomial E).eval x = 0} := by
    ext x
    simp only [SetLike.mem_coe, LinearMap.mem_ker, phiMap_apply, Set.mem_ofPred_eq,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
  have hdeg : (Polynomial.X ^ p - Polynomial.X : Polynomial E).natDegree = p :=
    FiniteField.X_pow_card_sub_X_natDegree_eq E (Fact.out : p.Prime).one_lt
  have hne : (Polynomial.X ^ p - Polynomial.X : Polynomial E) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero E (Fact.out : p.Prime).one_lt
  have hinj : Function.Injective (algebraMap (ZMod p) E) := (algebraMap (ZMod p) E).injective
  have hsub : Set.range (algebraMap (ZMod p) E) ⊆ ((phiMap (p:=p) (E:=E)).ker : Set E) := by
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, phiMap_apply, sub_eq_zero, ← map_pow, ZMod.pow_card]
  have h1 : p = (Set.range (algebraMap (ZMod p) E)).ncard := by
    rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, ZMod.card]
  refine le_antisymm ?_ ?_
  · rw [hroot]
    exact (ncard_roots_le _ hne).trans_eq hdeg
  · calc p = (Set.range (algebraMap (ZMod p) E)).ncard := h1
      _ ≤ ((phiMap (p:=p) (E:=E)).ker : Set E).ncard := Set.ncard_le_ncard hsub

theorem ker_psiMap_ncard_le (hn : 1 ≤ n) :
    ((psiMap (p:=p) (E:=E) n).ker : Set E).ncard ≤ p ^ (n-1) := by
  have hroot : ((psiMap (p:=p) (E:=E) n).ker : Set E)
      = {x : E | (Tf p n (Polynomial.X : Polynomial E)).eval x = 0} := by
    ext x
    have h : (Tf p n (Polynomial.X : Polynomial E)).eval x = ∑ i ∈ Finset.range n, x ^ (p ^ i) := by
      rw [Tf, Polynomial.eval_finsetSum]
      exact Finset.sum_congr rfl (fun i _ => by rw [Polynomial.eval_pow, Polynomial.eval_X])
    simp only [SetLike.mem_coe, LinearMap.mem_ker, psiMap_apply, Set.mem_ofPred_eq, h]
  have hdeg : (Tf p n (Polynomial.X : Polynomial E)).natDegree = p ^ (n-1) := by
    rw [Tf_natDegree (p:=p) hn (Polynomial.X : Polynomial E) (by rw [Polynomial.natDegree_X]),
      Polynomial.natDegree_X, mul_one]
  have hne : (Tf p n (Polynomial.X : Polynomial E)) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    have h2 : 0 < p ^ (n-1) := pow_pos (Fact.out : p.Prime).pos _
    omega
  rw [hroot]
  exact (ncard_roots_le _ hne).trans_eq hdeg

theorem range_phiMap_ncard (hn : 1 ≤ n) (hq : Fintype.card E = p ^ n) :
    ((phiMap (p:=p) (E:=E)).range : Set E).ncard = p ^ (n-1) := by
  have hquot : Nat.card (E ⧸ (phiMap (p:=p) (E:=E)).ker) = p ^ (n-1) := by
    have hker : Nat.card ↥(phiMap (p:=p) (E:=E)).ker = p :=
      show ((phiMap (p:=p) (E:=E)).ker : Set E).ncard = p from ker_phiMap_ncard (p:=p) (E:=E)
    have h5 := Submodule.card_eq_card_quotient_mul_card (phiMap (p:=p) (E:=E)).ker
    rw [Nat.card_eq_fintype_card, hq, hker] at h5
    have h6 : p ^ n = p * p ^ (n-1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h6] at h5
    exact (Nat.mul_left_cancel (Fact.out : p.Prime).pos h5).symm
  rw [← hquot]
  exact (Nat.card_congr (LinearMap.quotKerEquivRange (phiMap (p:=p) (E:=E))).toEquiv).symm

theorem range_phiMap_eq_ker_psiMap (hn : 1 ≤ n) (hq : Fintype.card E = p ^ n) :
    (phiMap (p:=p) (E:=E)).range = (psiMap (p:=p) (E:=E) n).ker := by
  have hle := range_phiMap_le_ker_psiMap (p:=p) (E:=E) hq
  have hrange : ((phiMap (p:=p) (E:=E)).range : Set E).ncard = p ^ (n-1) :=
    range_phiMap_ncard (p:=p) (E:=E) hn hq
  have hkerle : ((psiMap (p:=p) (E:=E) n).ker : Set E).ncard ≤ p ^ (n-1) :=
    ker_psiMap_ncard_le (p:=p) (E:=E) hn
  have hset : ((phiMap (p:=p) (E:=E)).range : Set E) = ((psiMap (p:=p) (E:=E) n).ker : Set E) :=
    Set.eq_of_subset_of_ncard_le hle (hkerle.trans (le_of_eq hrange.symm))
  exact SetLike.ext (fun x => by
    rw [← SetLike.mem_coe, ← SetLike.mem_coe, hset])

end ArtinSchreier

section SumIte
variable {F : Type*} [Fintype F]

theorem sum_ite_eq_card (P : F → Prop) [DecidablePred P] (a : ℕ) :
    (∑ x : F, (if P x then a else 0)) = a * Nat.card {x : F // P x} := by
  classical
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

end SumIte

section ArtinSchreierCount
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] {p : ℕ} [Fact p.Prime]
  [CharP E p] [Algebra (ZMod p) E]

theorem mem_range_phiMap_iff {n : ℕ} (hn : 1 ≤ n) (hq : Fintype.card E = p ^ n) (c : E) :
    c ∈ (phiMap (p:=p) (E:=E)).range ↔ psiMap (p:=p) n c = 0 := by
  rw [range_phiMap_eq_ker_psiMap (p:=p) (E:=E) hn hq, LinearMap.mem_ker]

theorem eval_Tf_eq (n : ℕ) (g : Polynomial E) (x : E) :
    (Tf p n g).eval x = psiMap (p:=p) n (g.eval x) := by
  rw [psiMap_apply, Tf, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl (fun i _ => by rw [Polynomial.eval_pow])

theorem fib_card {n : ℕ} (hn : 1 ≤ n) (hq : Fintype.card E = p ^ n) (c : E) :
    Nat.card {y : E // phiMap (p:=p) y = c} = if psiMap (p:=p) n c = 0 then p else 0 := by
  classical
  have hmem : c ∈ (phiMap (p:=p) (E:=E)).range ↔ psiMap (p:=p) n c = 0 :=
    mem_range_phiMap_iff (p:=p) (E:=E) hn hq c
  by_cases hc : psiMap (p:=p) n c = 0
  · rw [if_pos hc]
    obtain ⟨y₀, hy₀⟩ := LinearMap.mem_range.mp (hmem.mpr hc)
    have he : {y : E // phiMap (p:=p) y = c} ≃ ↥(phiMap (p:=p) (E:=E)).ker :=
      { toFun := fun y => ⟨y.1 - y₀, by
            rw [LinearMap.mem_ker, map_sub, y.2, hy₀, sub_self]⟩
        invFun := fun z => ⟨z.1 + y₀, by
            rw [map_add, LinearMap.mem_ker.mp z.2, hy₀, zero_add]⟩
        left_inv := by intro y; ext; simp
        right_inv := by intro z; ext; simp }
    rw [Nat.card_congr he]
    exact show Nat.card ↥(phiMap (p:=p) (E:=E)).ker = p from ker_phiMap_ncard (p:=p) (E:=E)
  · rw [if_neg hc]
    refine Nat.card_eq_zero.mpr (Or.inl ⟨fun y => hc (hmem.mp ?_)⟩)
    exact LinearMap.mem_range.mpr ⟨y.1, y.2⟩

theorem artin_schreier_count {n : ℕ} (hn : 1 ≤ n) (hq : Fintype.card E = p ^ n)
    (g : Polynomial E) :
    Nat.card {z : E × E // phiMap (p:=p) z.2 = g.eval z.1}
      = p * Nat.card {x : E // (Tf p n g).eval x = 0} := by
  classical
  have h2 : Nat.card {z : E × E // phiMap (p:=p) z.2 = g.eval z.1}
      = ∑ x : E, Nat.card {y : E // phiMap (p:=p) y = g.eval x} := by
    rw [← Nat.card_sigma (β := fun x : E => {y : E // phiMap (p:=p) y = g.eval x})]
    exact Nat.card_congr
      { toFun := fun z => ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
        invFun := fun s => ⟨(s.1, s.2.1), s.2.2⟩
        left_inv := by intro z; rfl
        right_inv := by intro s; rfl }
  rw [h2]
  rw [show (∑ x : E, Nat.card {y : E // phiMap (p:=p) y = g.eval x})
      = ∑ x : E, (if (Tf p n g).eval x = 0 then p else 0) from
        Finset.sum_congr rfl (fun x _ => by
          rw [fib_card (p:=p) (E:=E) hn hq (g.eval x), ← eval_Tf_eq (p:=p) n g x])]
  exact sum_ite_eq_card (fun x : E => (Tf p n g).eval x = 0) p

end ArtinSchreierCount

section CountUpper
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {p : ℕ} [Fact p.Prime] [CharP F p]

theorem count_upper {n : ℕ} (hn : 1 ≤ n) (hq : Fintype.card F = p ^ n)
    (d : ℕ) (hd : 1 ≤ d) (hdp : d < p) (f : Polynomial F)
    (hf1 : 1 ≤ f.natDegree) (hfd : f.natDegree ≤ d)
    (hbig : (4 * p * (d + 1) + 2 * p ^ 3 * (d + 1) + 4) ^ 2 ≤ Fintype.card F) :
    (({x : F | Polynomial.eval x (Tf p n f) = 0} : Set F).ncard)
      ≤ Fintype.card F / p + 100 * (d + 1) * (p + 1) * Nat.sqrt (Fintype.card F) := by
  classical
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hp1 : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
  have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
  have hfp : f.natDegree < p := lt_of_le_of_lt hfd hdp
  have hbig' : (4 * p * (f.natDegree + 1) + 2 * p ^ 3 * (f.natDegree + 1) + 4) ^ 2
      ≤ Fintype.card F := by
    refine le_trans (Nat.pow_le_pow_left ?_ 2) hbig
    have h1 : f.natDegree + 1 ≤ d + 1 := by omega
    exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left (4 * p) h1)
      (Nat.mul_le_mul_left (2 * p ^ 3) h1)) (le_refl 4)
  set s := Nat.sqrt (Fintype.card F) with hs
  set A₀ := s * s / (2 * p) + 1 with hA₀def
  set B := s / p + f.natDegree + 3 with hBdef
  obtain ⟨hn1, hn2, hn3, hn4, hn5, hn6⟩ :=
    Commons.NumberTheory.Stepanov.stepanov_numerics p f.natDegree hp2 hf1 (f.natDegree - 1)
      (by omega) (Fintype.card F) hbig'
  rw [← hs] at hn1 hn2 hn3 hn4 hn5 hn6
  rw [← hA₀def] at hn5 hn6
  rw [← hBdef] at hn6
  have hs1 : 1 ≤ s := hn1
  have hs2 : 2 * p ≤ s := hn2
  have hA₀q : p * (A₀ + 1) ≤ Fintype.card F := by
    have h5' : p * A₀ + p ^ 3 * f.natDegree < Fintype.card F := by
      have := hn5
      rwa [Nat.sub_add_cancel hf1] at this
    have hp3df : p ≤ p ^ 3 * f.natDegree := by
      have h1 : p ≤ p ^ 3 := by
        have h2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp0
        calc p = p * 1 := by ring
          _ ≤ p * p ^ 2 := Nat.mul_le_mul_left p h2
          _ = p ^ 3 := by ring
      calc p ≤ p ^ 3 := h1
        _ = p ^ 3 * 1 := by ring
        _ ≤ p ^ 3 * f.natDegree := Nat.mul_le_mul_left _ hf1
    have heq : p * (A₀ + 1) = p * A₀ + p := by ring
    rw [heq]
    omega
  have hdim : s * (A₀ + B + 1) + (f.natDegree - 1) * (s * (s - 1) / 2)
      < p * (A₀ + 1) * (B + 1) := by
    rw [Nat.mul_assoc]
    exact hn6
  have hMq : ∀ ℓ < s, ℓ < Fintype.card F := by
    intro ℓ hℓ
    have h4 : s ≤ Fintype.card F - 1 := le_trans hn3 (Nat.div_le_self _ _)
    omega
  obtain ⟨A, hAd, hAn, hcond, hRne⟩ :=
    witness_exists (p:=p) (F:=F) (n:=n) (M:=s) (A₀:=A₀) (B:=B)
      hn hq f hf1 hfp hA₀q hdim
  have hcount := additive_count (p:=p) (F:=F) n s A₀ B hq f hMq A hAd hAn hcond hRne hn hf1
  have hqp : Fintype.card F = p ^ n := hq
  have hp_dvd : p * p ^ (n - 1) = p ^ n := by
    rw [← pow_succ']
    congr 1
    omega
  have hq2 : Fintype.card F ≤ 3 * (s * s) := by
    have h1 : Fintype.card F < (s + 1) * (s + 1) := by
      have h := Nat.lt_succ_sqrt' (Fintype.card F)
      rw [← hs] at h
      simpa [Nat.succ_eq_add_one, pow_two] using h
    have hss : s ≤ s * s := Nat.le_mul_of_pos_left s (by omega)
    linarith only [h1, hss]
  have hmain : p * (A₀ + Fintype.card F * B + (p - 1) * (p ^ (n - 1) * f.natDegree))
      ≤ (Fintype.card F + (100 * (d + 1) * (p + 1)) * p * s) * s := by
    have hA2 : p * A₀ ≤ 2 * (s * s) := by
      rw [hA₀def]
      have h1 : p * (s * s / (2 * p)) ≤ s * s / 2 := by
        rw [Nat.le_div_iff_mul_le (by omega : 0 < 2)]
        calc p * (s * s / (2 * p)) * 2 = (2 * p) * (s * s / (2 * p)) := by ring
          _ ≤ s * s := Nat.mul_div_le _ _
      have h2 : p ≤ s * s := le_trans (by omega : p ≤ s) (Nat.le_mul_of_pos_left s (by omega))
      calc p * (s * s / (2 * p) + 1) = p * (s * s / (2 * p)) + p := by ring
        _ ≤ s * s / 2 + s * s := add_le_add h1 h2
        _ ≤ 2 * (s * s) := by omega
    have hB2 : p * (Fintype.card F * B)
        ≤ Fintype.card F * s + p * Fintype.card F * f.natDegree + 3 * (p * Fintype.card F) := by
      rw [hBdef]
      have h1 : p * (s / p) ≤ s := by
        calc p * (s / p) = s / p * p := by ring
          _ ≤ s := Nat.div_mul_le_self _ _
      calc p * (Fintype.card F * (s / p + f.natDegree + 3))
          = Fintype.card F * (p * (s / p)) + p * Fintype.card F * f.natDegree
              + 3 * (p * Fintype.card F) := by ring
        _ ≤ Fintype.card F * s + p * Fintype.card F * f.natDegree
              + 3 * (p * Fintype.card F) := by
            exact add_le_add (add_le_add (Nat.mul_le_mul_left _ h1) (le_refl _)) (le_refl _)
    have hC2 : p * ((p - 1) * (p ^ (n - 1) * f.natDegree))
        ≤ p * Fintype.card F * f.natDegree := by
      have h1 : p * (p - 1) * p ^ (n - 1) ≤ p * Fintype.card F := by
        have h2 : p * p ^ (n - 1) = Fintype.card F := by rw [hp_dvd, ← hqp]
        calc p * (p - 1) * p ^ (n - 1) = (p - 1) * (p * p ^ (n - 1)) := by ring
          _ = (p - 1) * Fintype.card F := by rw [h2]
          _ ≤ p * Fintype.card F := Nat.mul_le_mul_right _ (Nat.sub_le p 1)
      calc p * ((p - 1) * (p ^ (n - 1) * f.natDegree))
          = (p * (p - 1) * p ^ (n - 1)) * f.natDegree := by ring
        _ ≤ (p * Fintype.card F) * f.natDegree := Nat.mul_le_mul_right _ h1
        _ = p * Fintype.card F * f.natDegree := by ring
    have h5 : p * Fintype.card F * f.natDegree ≤ 12 * d * p * s * s := by
      have h1 : p * Fintype.card F * f.natDegree ≤ p * (3 * (s * s)) * d := by
        calc p * Fintype.card F * f.natDegree ≤ p * (3 * (s * s)) * f.natDegree :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left p hq2)
          _ ≤ p * (3 * (s * s)) * d := Nat.mul_le_mul_left _ hfd
      calc p * Fintype.card F * f.natDegree ≤ p * (3 * (s * s)) * d := h1
        _ = 3 * (d * p * (s * s)) := by ring
        _ ≤ 12 * (d * p * (s * s)) := Nat.mul_le_mul_right _ (by omega : 3 ≤ 12)
        _ = 12 * d * p * s * s := by ring
    have h6 : 3 * (p * Fintype.card F) ≤ 9 * (p * (s * s)) := by
      have h := Nat.mul_le_mul_left p hq2
      calc 3 * (p * Fintype.card F) ≤ 3 * (p * (3 * (s * s))) := Nat.mul_le_mul_left 3 h
        _ = 9 * (p * (s * s)) := by ring
    have key : 2 * (s * s) + 24 * d * p * s * s + 9 * (p * (s * s))
        ≤ (100 * (d + 1) * (p + 1)) * p * s * s := by
      have hL : 2 * (s * s) + 24 * d * p * s * s + 9 * (p * (s * s))
          = (2 + 24 * d * p + 9 * p) * (s * s) := by ring
      have hR : (100 * (d + 1) * (p + 1)) * p * s * s
          = (100 * (d + 1) * (p + 1) * p) * (s * s) := by ring
      rw [hL, hR]
      refine Nat.mul_le_mul_right _ ?_
      have h1 : 2 ≤ 2 * d * p := by linarith only [Nat.mul_le_mul hd hp1]
      have h2 : 9 * p ≤ 9 * d * p := by
        calc 9 * p = 9 * 1 * p := by ring
          _ ≤ 9 * d * p := Nat.mul_le_mul_right p (Nat.mul_le_mul_left 9 hd)
      have h4 : 100 * d * p ≤ 100 * (d + 1) * (p + 1) * p := by
        have e : 100 * (d + 1) * (p + 1) * p
            = 100 * d * p * p + 100 * d * p + 100 * p * p + 100 * p := by ring
        rw [e]
        have h5 : 100 * d * p ≤ 100 * d * p * p := by
          calc 100 * d * p = 100 * d * p * 1 := by ring
            _ ≤ 100 * d * p * p := Nat.mul_le_mul_left _ hp1
        omega
      calc 2 + 24 * d * p + 9 * p ≤ 2 * d * p + 24 * d * p + 9 * d * p :=
            add_le_add (add_le_add h1 (le_refl _)) h2
        _ = 35 * (d * p) := by ring
        _ ≤ 100 * (d * p) := Nat.mul_le_mul_right (d * p) (by omega : 35 ≤ 100)
        _ = 100 * d * p := by ring
        _ ≤ 100 * (d + 1) * (p + 1) * p := h4
    calc p * (A₀ + Fintype.card F * B + (p - 1) * (p ^ (n - 1) * f.natDegree))
        = p * A₀ + p * (Fintype.card F * B)
            + p * ((p - 1) * (p ^ (n - 1) * f.natDegree)) := by ring
      _ ≤ 2 * (s * s)
            + (Fintype.card F * s + p * Fintype.card F * f.natDegree
                + 3 * (p * Fintype.card F)) + p * Fintype.card F * f.natDegree :=
          add_le_add (add_le_add hA2 hB2) hC2
      _ ≤ (Fintype.card F + (100 * (d + 1) * (p + 1)) * p * s) * s := by
          linarith only [h5, h6, key]
  have hN0 : (({x : F | Polynomial.eval x (Tf p n f) = 0} : Set F).ncard)
      ≤ Fintype.card F / p + 100 * (d + 1) * (p + 1) * s := by
    have h1 : (({x : F | Polynomial.eval x (Tf p n f) = 0} : Set F).ncard) * p * s
        ≤ (Fintype.card F + (100 * (d + 1) * (p + 1)) * p * s) * s := by
      calc (({x : F | Polynomial.eval x (Tf p n f) = 0} : Set F).ncard) * p * s
          = p * ((({x : F | Polynomial.eval x (Tf p n f) = 0} : Set F).ncard) * s) := by ring
        _ ≤ p * (A₀ + Fintype.card F * B + (p - 1) * (p ^ (n - 1) * f.natDegree)) :=
              Nat.mul_le_mul_left p hcount
        _ ≤ (Fintype.card F + (100 * (d + 1) * (p + 1)) * p * s) * s := hmain
    have h2 : (({x : F | Polynomial.eval x (Tf p n f) = 0} : Set F).ncard) * p
        ≤ Fintype.card F + (100 * (d + 1) * (p + 1)) * p * s :=
      Nat.le_of_mul_le_mul_right h1 (by omega)
    have h3 : (({x : F | Polynomial.eval x (Tf p n f) = 0} : Set F).ncard)
        ≤ (Fintype.card F + (100 * (d + 1) * (p + 1)) * p * s) / p :=
      (Nat.le_div_iff_mul_le hp0).mpr h2
    have h4 : (Fintype.card F + (100 * (d + 1) * (p + 1)) * p * s) / p
        = Fintype.card F / p + 100 * (d + 1) * (p + 1) * s := by
      have hh : (100 * (d + 1) * (p + 1)) * p * s
          = ((100 * (d + 1) * (p + 1)) * s) * p := by ring
      rw [hh, Nat.add_mul_div_right (Fintype.card F) ((100 * (d + 1) * (p + 1)) * s) hp0]
    exact h3.trans_eq h4
  exact hN0

end CountUpper

section FixField
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] {p : ℕ} [Fact p.Prime]
  [CharP E p] [Algebra (ZMod p) E]

theorem sum_shift_eq {n : ℕ} {x : E} (hx : x ^ p ^ n = x) :
    (∑ i ∈ Finset.range n, x ^ (p ^ (i+1))) = ∑ i ∈ Finset.range n, x ^ (p^i) := by
  calc ∑ i ∈ Finset.range n, x ^ (p ^ (i+1))
      = (∑ i ∈ Finset.range (n+1), x ^ (p^i)) - x ^ (p^0) := by
        rw [Finset.sum_range_succ']; abel
    _ = ((∑ i ∈ Finset.range n, x ^ (p^i)) + x ^ (p^n)) - x ^ (p^0) := by
        rw [Finset.sum_range_succ]
    _ = ∑ i ∈ Finset.range n, x ^ (p^i) := by rw [hx]; simp

theorem psiMap_pow_self {n : ℕ} {x : E} (hx : x ^ p ^ n = x) :
    psiMap (p:=p) n x ^ p = psiMap (p:=p) n x := by
  have h2 := sum_pow_charPow (s := Finset.range n) (a := fun i => x ^ (p^i)) 1
  rw [pow_one] at h2
  rw [psiMap_apply, h2]
  refine (Finset.sum_congr rfl (fun i _ => ?_)).trans (sum_shift_eq (p:=p) hx)
  rw [← pow_mul, ← pow_succ]

theorem fix_ncard_le :
    ({z : E | z ^ p = z} : Set E).ncard ≤ p := by
  have hne : (Polynomial.X ^ p - Polynomial.X : Polynomial E) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero E (Fact.out : p.Prime).one_lt
  have hdeg : (Polynomial.X ^ p - Polynomial.X : Polynomial E).natDegree = p :=
    FiniteField.X_pow_card_sub_X_natDegree_eq E (Fact.out : p.Prime).one_lt
  have hroot : ({z : E | z ^ p = z} : Set E)
      = {z : E | (Polynomial.X ^ p - Polynomial.X : Polynomial E).eval z = 0} := by
    ext z
    simp only [Set.mem_ofPred_eq, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      sub_eq_zero]
  rw [hroot]
  exact (ncard_roots_le _ hne).trans_eq hdeg

theorem range_algebraMap_subset_fix :
    (Set.range (algebraMap (ZMod p) E)) ⊆ {z : E | z ^ p = z} := by
  rintro _ ⟨a, rfl⟩
  rw [Set.mem_ofPred_eq, ← map_pow, ZMod.pow_card]

theorem range_algebraMap_ncard :
    (Set.range (algebraMap (ZMod p) E)).ncard = p := by
  rw [Set.ncard_range_of_injective (algebraMap (ZMod p) E).injective, Nat.card_eq_fintype_card,
    ZMod.card]

theorem range_algebraMap_eq_fix :
    (Set.range (algebraMap (ZMod p) E)) = {z : E | z ^ p = z} :=
  Set.eq_of_subset_of_ncard_le range_algebraMap_subset_fix
    (by rw [range_algebraMap_ncard]; exact fix_ncard_le (p:=p) (E:=E))

theorem range_psiMap_subset_fix {n : ℕ} (hq : Fintype.card E = p ^ n) :
    ((psiMap (p:=p) (E:=E) n).range : Set E) ⊆ {z : E | z ^ p = z} := by
  intro z hz
  rw [SetLike.mem_coe, LinearMap.mem_range] at hz
  obtain ⟨a, rfl⟩ := hz
  exact psiMap_pow_self (p:=p) (by rw [← hq]; exact FiniteField.pow_card a)

theorem range_psiMap_ncard (hn : 1 ≤ n) (hq : Fintype.card E = p ^ n) :
    ((psiMap (p:=p) (E:=E) n).range : Set E).ncard = p := by
  have hker : Nat.card ↥(psiMap (p:=p) (E:=E) n).ker = p ^ (n - 1) := by
    refine le_antisymm ?_ ?_
    · exact show ((psiMap (p:=p) (E:=E) n).ker : Set E).ncard ≤ p ^ (n-1) from
        ker_psiMap_ncard_le (p:=p) (E:=E) hn
    · have h := Set.ncard_le_ncard (range_phiMap_le_ker_psiMap (p:=p) (E:=E) hq)
      rw [range_phiMap_ncard (p:=p) (E:=E) hn hq] at h
      exact show p ^ (n-1) ≤ Nat.card ↥(psiMap (p:=p) (E:=E) n).ker from h
  have h5 := Submodule.card_eq_card_quotient_mul_card (psiMap (p:=p) (E:=E) n).ker
  rw [Nat.card_eq_fintype_card (α := E), hq, hker] at h5
  have hqQ : Nat.card (E ⧸ (psiMap (p:=p) (E:=E) n).ker)
      = Nat.card ↥(psiMap (p:=p) (E:=E) n).range :=
    Nat.card_congr (LinearMap.quotKerEquivRange (psiMap (p:=p) (E:=E) n)).toEquiv
  rw [hqQ] at h5
  have hpos : 0 < p ^ (n-1) := pow_pos (Fact.out : p.Prime).pos _
  have h6 : p ^ n = p ^ (n-1) * p := by
    rw [← pow_succ]; congr 1; omega
  rw [h6] at h5
  exact (Nat.mul_left_cancel hpos h5).symm

theorem range_psiMap_eq_range_algebraMap (hn : 1 ≤ n) (hq : Fintype.card E = p ^ n) :
    ((psiMap (p:=p) (E:=E) n).range : Set E) = Set.range (algebraMap (ZMod p) E) := by
  rw [range_algebraMap_eq_fix]
  exact Set.eq_of_subset_of_ncard_le (range_psiMap_subset_fix (p:=p) (E:=E) hq)
    (by rw [range_psiMap_ncard (p:=p) (E:=E) hn hq]; exact fix_ncard_le (p:=p) (E:=E))

theorem psiMap_surj (hn : 1 ≤ n) (hq : Fintype.card E = p ^ n) {y : E}
    (hy : y ∈ Set.range (algebraMap (ZMod p) E)) :
    ∃ a : E, psiMap (p:=p) n a = y := by
  have h := range_psiMap_eq_range_algebraMap (p:=p) (E:=E) hn hq
  rw [← h] at hy
  rwa [SetLike.mem_coe, LinearMap.mem_range] at hy

theorem Tf_sub_C (n : ℕ) (f : Polynomial E) (a : E) :
    Tf p n (f - Polynomial.C a) = Tf p n f - Polynomial.C (psiMap (p:=p) n a) := by
  rw [Tf, Tf, psiMap_apply, map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [sub_pow_char_pow, ← Polynomial.C_pow]

theorem Tf_sub_C_eval {n : ℕ} (f : Polynomial E) (a x : E) :
    (Tf p n (f - Polynomial.C a)).eval x = psiMap (p:=p) n (f.eval x) - psiMap (p:=p) n a := by
  rw [Tf_sub_C, Polynomial.eval_sub, Polynomial.eval_C, eval_Tf_eq]

end FixField

section PointCount

theorem psiMap_exists_algebraMap {E : Type*} [Field E] [Fintype E] [DecidableEq E] {p : ℕ}
    [Fact p.Prime] [CharP E p] [Algebra (ZMod p) E] {n : ℕ} (hn : 1 ≤ n)
    (hq : Fintype.card E = p ^ n) (x : E) :
    ∃ c : ZMod p, psiMap (p:=p) n x = algebraMap (ZMod p) E c := by
  have h : psiMap (p:=p) n x ∈ ((psiMap (p:=p) (E:=E) n).range : Set E) :=
    LinearMap.mem_range.mpr ⟨x, rfl⟩
  rw [range_psiMap_eq_range_algebraMap (p:=p) (E:=E) hn hq] at h
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.symm⟩

theorem ncard_eq_filter_card {F : Type*} [Fintype F] (P : F → Prop) [DecidablePred P] :
    (({x : F | P x} : Set F)).ncard = (Finset.univ.filter P).card := by
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext x
  simp

theorem point_count (p : ℕ) [Fact p.Prime] (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
        [Module.Finite (ZMod p) E] [Module.Free (ZMod p) E],
        d < p → 2 ∣ Module.finrank (ZMod p) E →
        ∀ (g : Polynomial (ZMod p)), 1 ≤ g.natDegree → g.natDegree ≤ d →
        (∀ q : ℕ, q.Prime → q ∣ p → ∀ (a : ZMod p) (h : Polynomial (ZMod p)),
          g ≠ Polynomial.C a * h ^ q) →
        |(({z : E × E | z.2 ^ p - z.2 = (g.map (algebraMap (ZMod p) E)).eval z.1} : Set (E × E)).ncard : ℝ)
            - (Fintype.card E : ℝ)|
          ≤ C * Real.sqrt ((Fintype.card E : ℕ) : ℝ) := by
  set P : ℕ := 4 * p * (d + 1) + 2 * p ^ 3 * (d + 1) + 4 with hP
  set K : ℕ := 100 * (d + 1) * (p + 1) with hK
  have hp1r : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).two_le
  refine ⟨(p : ℝ) * ((p : ℝ) - 1) * (K : ℝ) + ((p : ℝ) - 1) * (P : ℝ) ^ 2 + 1, ?_, ?_⟩
  · have h0 : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    have h1 : 0 ≤ (p : ℝ) * ((p : ℝ) - 1) * (K : ℝ) := by positivity
    have h2 : 0 ≤ ((p : ℝ) - 1) * (P : ℝ) ^ 2 := by positivity
    linarith
  · intro E _ _ _ _ _ _ hdp h2dvd g hg1 hgd hnd
    haveI hchar : CharP E p := (Algebra.charP_iff (ZMod p) E p).mp (ZMod.charP p)
    set n : ℕ := Module.finrank (ZMod p) E with hn
    have hq : Fintype.card E = p ^ n := by
      rw [Module.card_eq_pow_finrank (K := ZMod p) (V := E), ZMod.card, hn]
    have hn1 : 1 ≤ n := by
      have h2 : 2 ≤ Fintype.card E := Fintype.one_lt_card
      by_contra h
      have h0 : n = 0 := by omega
      rw [h0, pow_zero] at hq
      omega
    have hpcard : p ∣ Fintype.card E := by
      refine ⟨p ^ (n - 1), ?_⟩
      rw [hq, ← pow_succ']
      congr 1
      omega
    set gE : Polynomial E := g.map (algebraMap (ZMod p) E) with hgE
    have hgEdeg : gE.natDegree = g.natDegree := by
      rw [hgE]
      exact Polynomial.natDegree_map_eq_of_injective (algebraMap (ZMod p) E).injective g
    have hgE1 : 1 ≤ gE.natDegree := by rw [hgEdeg]; exact hg1
    have hgEd : gE.natDegree ≤ d := by rw [hgEdeg]; exact hgd
    set SS : ℕ := (({z : E × E | z.2 ^ p - z.2 = gE.eval z.1} : Set (E × E))).ncard with hSS
    set N0 : ℕ := (({x : E | (Tf p n gE).eval x = 0} : Set E)).ncard with hN0
    set Q : ℝ := (Fintype.card E : ℝ) with hQ
    set R : ℝ := Real.sqrt (Fintype.card E) with hR
    have hR0 : (0 : ℝ) ≤ R := Real.sqrt_nonneg _
    have hS : SS = p * N0 := by
      rw [hSS, hN0]
      exact artin_schreier_count (p:=p) (E:=E) hn1 hq gE
    have hN0le : N0 ≤ Fintype.card E := by
      rw [hN0]
      have h := Set.ncard_le_ncard (Set.subset_univ ({x : E | (Tf p n gE).eval x = 0} : Set E))
      rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at h
    have hSScast : (SS : ℝ) = (p : ℝ) * (N0 : ℝ) := by
      rw [hS]; push_cast; ring
    by_cases hbig : P ^ 2 ≤ Fintype.card E
    · -- ============ large q ============
      have hbig' : (4 * p * (d + 1) + 2 * p ^ 3 * (d + 1) + 4) ^ 2 ≤ Fintype.card E := by
        rw [← hP]; exact hbig
      have hN0ub : N0 ≤ Fintype.card E / p + K * Nat.sqrt (Fintype.card E) := by
        rw [hN0, hK]
        exact count_upper (p:=p) (F:=E) hn1 hq d hd hdp gE hgE1 hgEd hbig'
      set Y : ℕ := Fintype.card E / p + K * Nat.sqrt (Fintype.card E) with hY
      have hYub : N0 ≤ Y := hN0ub
      have hYr : (Y : ℝ) ≤ Q / p + (K : ℝ) * R := by
        rw [hY]
        have h1 : ((Fintype.card E / p : ℕ) : ℝ) = Q / p := by
          rw [Nat.cast_div hpcard (by positivity : (p : ℝ) ≠ 0)]
        have h2 : ((Nat.sqrt (Fintype.card E) : ℕ) : ℝ) ≤ R := Real.nat_sqrt_le_real_sqrt
        rw [Nat.cast_add, Nat.cast_mul, h1]
        have h3 : (0 : ℝ) ≤ (K : ℝ) := by positivity
        linarith only [mul_le_mul_of_nonneg_left h2 h3]
      have hex : ∀ c : ZMod p, ∃ a : E, psiMap (p:=p) n a = algebraMap (ZMod p) E c :=
        fun c => psiMap_surj (p:=p) (E:=E) hn1 hq (y := algebraMap (ZMod p) E c) ⟨c, rfl⟩
      choose ac hac using hex
      set M : ZMod p → ℕ := fun c =>
        (({x : E | psiMap (p:=p) n (gE.eval x) = algebraMap (ZMod p) E c} : Set E)).ncard with hM
      have hMbound : ∀ c : ZMod p, c ≠ 0 → M c ≤ Y := by
        intro c _hc
        have hfa : (gE - Polynomial.C (ac c)).natDegree = gE.natDegree := by
          refine Polynomial.natDegree_sub_eq_left_of_natDegree_lt ?_
          rw [Polynomial.natDegree_C]
          omega
        have h1 : 1 ≤ (gE - Polynomial.C (ac c)).natDegree := by rw [hfa]; exact hgE1
        have h2 : (gE - Polynomial.C (ac c)).natDegree ≤ d := by rw [hfa]; exact hgEd
        have h3 := count_upper (p:=p) (F:=E) hn1 hq d hd hdp (gE - Polynomial.C (ac c)) h1 h2 hbig'
        have hh : M c
            = (({x : E | psiMap (p:=p) n (gE.eval x) = algebraMap (ZMod p) E c} : Set E)).ncard := by
          rw [hM]
        have heq : M c
            = (({x : E | (Tf p n (gE - Polynomial.C (ac c))).eval x = 0} : Set E)).ncard := by
          rw [hh]
          congr 1
          ext x
          rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Tf_sub_C_eval, hac c, sub_eq_zero]
        rw [heq, hY]
        exact h3
      have hfib : ∀ x : E, ∃ c : ZMod p, psiMap (p:=p) n (gE.eval x) = algebraMap (ZMod p) E c :=
        fun x => psiMap_exists_algebraMap (p:=p) (E:=E) hn1 hq (gE.eval x)
      set fib : E → ZMod p := fun x => Classical.choose (hfib x) with hfibdef
      have hfibspec : ∀ x : E, psiMap (p:=p) n (gE.eval x) = algebraMap (ZMod p) E (fib x) :=
        fun x => Classical.choose_spec (hfib x)
      have hMeq : ∀ c : ZMod p,
          M c = (Finset.univ.filter (fun x : E => fib x = c)).card := by
        intro c
        have hh : M c
            = (({x : E | psiMap (p:=p) n (gE.eval x) = algebraMap (ZMod p) E c} : Set E)).ncard := by
          rw [hM]
        rw [hh, ncard_eq_filter_card]
        congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          have h2 := hfibspec x
          rw [h] at h2
          exact (algebraMap (ZMod p) E).injective h2.symm
        · intro h
          rw [hfibspec x, h]
      have hsum : ∑ c : ZMod p, M c = Fintype.card E := by
        have h1 : Fintype.card E
            = ∑ c : ZMod p, (Finset.univ.filter (fun x : E => fib x = c)).card := by
          rw [Fintype.card_congr (Equiv.sigmaFiberEquiv (fib)).symm, Fintype.card_sigma]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [Fintype.card_subtype]
        rw [h1]
        exact Finset.sum_congr rfl (fun c _ => hMeq c)
      have hM0sum : ∑ c ∈ (Finset.univ.erase (0 : ZMod p)), M c + M 0 = Fintype.card E := by
        rw [Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p)), hsum]
      have hnonzero : ∑ c ∈ (Finset.univ.erase (0 : ZMod p)), M c ≤ (p - 1) * Y := by
        calc ∑ c ∈ Finset.univ.erase (0 : ZMod p), M c
            ≤ ∑ _c ∈ Finset.univ.erase (0 : ZMod p), Y := by
              refine Finset.sum_le_sum (fun c hc => ?_)
              rw [Finset.mem_erase] at hc
              exact hMbound c hc.1
          _ = (Finset.univ.erase (0 : ZMod p)).card • Y := Finset.sum_const _
          _ = (p - 1) * Y := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)), Finset.card_univ,
                ZMod.card, smul_eq_mul]
      have hN0M0 : N0 = M 0 := by
        rw [hN0, hM]
        congr 1
        ext x
        rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, map_zero, ← eval_Tf_eq]
      -- real-number assembly
      have hN0ge : Q - (((p - 1) * Y : ℕ) : ℝ) ≤ (N0 : ℝ) := by
        have h1 : (((∑ c ∈ Finset.univ.erase (0 : ZMod p), M c) : ℕ) : ℝ) + (M 0 : ℝ) = Q := by
          have h1' : (((∑ c ∈ Finset.univ.erase (0 : ZMod p), M c) : ℕ) : ℝ) + (M 0 : ℝ)
              = (Fintype.card E : ℝ) := by exact_mod_cast hM0sum
          simpa [hQ] using h1'
        have h2 : (((∑ c ∈ Finset.univ.erase (0 : ZMod p), M c) : ℕ) : ℝ)
            ≤ (((p - 1) * Y : ℕ) : ℝ) := by exact_mod_cast hnonzero
        rw [hN0M0]
        linarith
      have hYr2 : (((p - 1) * Y : ℕ) : ℝ) ≤ ((p : ℝ) - 1) * (Q / p + (K : ℝ) * R) := by
        rw [Nat.cast_mul]
        have h4 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
        rw [h4]
        exact mul_le_mul_of_nonneg_left hYr (by linarith)
      have hpne : (p : ℝ) ≠ 0 := by positivity
      have hQp : (p : ℝ) * (Q / p) = Q := by
        rw [← mul_div_assoc, mul_div_cancel_left₀ Q hpne]
      have hub : (SS : ℝ) ≤ Q + (p : ℝ) * (K : ℝ) * R := by
        rw [hSScast]
        have h1 : (N0 : ℝ) ≤ Q / p + (K : ℝ) * R := by
          have h2 : (N0 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hYub
          linarith only [hYr, h2]
        calc (p : ℝ) * (N0 : ℝ) ≤ (p : ℝ) * (Q / p + (K : ℝ) * R) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = Q + (p : ℝ) * (K : ℝ) * R := by rw [mul_add, hQp]; ring
      have hlb : Q - (p : ℝ) * ((p : ℝ) - 1) * (K : ℝ) * R ≤ (SS : ℝ) := by
        rw [hSScast]
        have h2 : Q - ((p : ℝ) - 1) * (Q / p + (K : ℝ) * R) ≤ (N0 : ℝ) := by
          linarith only [hN0ge, hYr2]
        calc Q - (p : ℝ) * ((p : ℝ) - 1) * (K : ℝ) * R
            = (Q - ((p : ℝ) - 1) * (Q / p + (K : ℝ) * R)) * (p : ℝ) := by
              field_simp
              ring
          _ ≤ (N0 : ℝ) * (p : ℝ) := mul_le_mul_of_nonneg_right h2 (by positivity)
          _ = (p : ℝ) * (N0 : ℝ) := by ring
      have hCge : (p : ℝ) * ((p : ℝ) - 1) * (K : ℝ)
          ≤ (p : ℝ) * ((p : ℝ) - 1) * (K : ℝ) + ((p : ℝ) - 1) * (P : ℝ) ^ 2 + 1 := by
        have h1 : (0 : ℝ) ≤ ((p : ℝ) - 1) * (P : ℝ) ^ 2 := by
          have : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
          positivity
        linarith
      have hCgeR : (p : ℝ) * ((p : ℝ) - 1) * (K : ℝ) * R
          ≤ ((p : ℝ) * ((p : ℝ) - 1) * (K : ℝ) + ((p : ℝ) - 1) * (P : ℝ) ^ 2 + 1) * R :=
        mul_le_mul_of_nonneg_right hCge hR0
      have hPKle : (p : ℝ) * (K : ℝ) * R ≤ (p : ℝ) * ((p : ℝ) - 1) * (K : ℝ) * R := by
        have h1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
        have h2 : (0 : ℝ) ≤ (p : ℝ) * (K : ℝ) := by positivity
        have h3 : (p : ℝ) * (K : ℝ) * R * 1 ≤ (p : ℝ) * (K : ℝ) * R * ((p : ℝ) - 1) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg h2 hR0)
        linarith only [h3]
      have hub2 : (SS : ℝ) - Q
          ≤ ((p : ℝ) * ((p : ℝ) - 1) * (K : ℝ) + ((p : ℝ) - 1) * (P : ℝ) ^ 2 + 1) * R := by
        linarith only [hub, hPKle, hCgeR]
      have hlb2 : -(((p : ℝ) * ((p : ℝ) - 1) * (K : ℝ) + ((p : ℝ) - 1) * (P : ℝ) ^ 2 + 1) * R)
          ≤ (SS : ℝ) - Q := by
        linarith only [hlb, hCgeR]
      rw [abs_le]
      exact ⟨hlb2, hub2⟩
    · -- ============ small q ============
      push_neg at hbig
      have hPq : Q ≤ (P : ℝ) ^ 2 := by
        have h : (Fintype.card E : ℝ) ≤ (P : ℝ) ^ 2 := by
          exact_mod_cast (le_of_lt hbig : Fintype.card E ≤ P ^ 2)
        simpa [hQ] using h
      have hR1 : 1 ≤ R := by
        rw [← Real.sqrt_one, hR]
        exact Real.sqrt_le_sqrt (by exact_mod_cast (le_of_lt (Fintype.one_lt_card : 1 < Fintype.card E)))
      have hqle : Q ≤ (P : ℝ) ^ 2 * R := by
        calc Q ≤ (P : ℝ) ^ 2 := hPq
          _ = (P : ℝ) ^ 2 * 1 := by ring
          _ ≤ (P : ℝ) ^ 2 * R := mul_le_mul_of_nonneg_left hR1 (by positivity)
      have hSSle : (SS : ℝ) ≤ (p : ℝ) * Q := by
        rw [hSScast]
        have h2 : (N0 : ℝ) ≤ Q := by
          have h : (N0 : ℝ) ≤ (Fintype.card E : ℝ) := by exact_mod_cast hN0le
          simpa [hQ] using h
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
      have hp1m : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
      have h4 : ((p : ℝ) - 1) * Q ≤ ((p : ℝ) - 1) * ((P : ℝ) ^ 2 * R) :=
        mul_le_mul_of_nonneg_left hqle (by linarith)
      have hC : ((p : ℝ) - 1) * ((P : ℝ) ^ 2 * R)
          ≤ ((p : ℝ) * ((p : ℝ) - 1) * (K : ℝ) + ((p : ℝ) - 1) * (P : ℝ) ^ 2 + 1) * R := by
        have hle : ((p : ℝ) - 1) * (P : ℝ) ^ 2
            ≤ (p : ℝ) * ((p : ℝ) - 1) * (K : ℝ) + ((p : ℝ) - 1) * (P : ℝ) ^ 2 + 1 := by
          have h1 : (0 : ℝ) ≤ (p : ℝ) * ((p : ℝ) - 1) * (K : ℝ) := by positivity
          linarith
        calc ((p : ℝ) - 1) * ((P : ℝ) ^ 2 * R)
            = (((p : ℝ) - 1) * (P : ℝ) ^ 2) * R := by ring
          _ ≤ ((p : ℝ) * ((p : ℝ) - 1) * (K : ℝ) + ((p : ℝ) - 1) * (P : ℝ) ^ 2 + 1) * R :=
              mul_le_mul_of_nonneg_right hle hR0
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · have h1 : Q - (SS : ℝ) ≤ Q := by
          have : (0 : ℝ) ≤ (SS : ℝ) := by positivity
          linarith
        have h2 : Q ≤ ((p : ℝ) - 1) * Q := by
          exact le_mul_of_one_le_left (Nat.cast_nonneg (Fintype.card E)) hp1m
        linarith only [h1, h2, h4, hC]
      · have h1 : (SS : ℝ) - Q ≤ (p : ℝ) * Q - Q := by linarith only [hSSle]
        have h2 : (p : ℝ) * Q - Q = ((p : ℝ) - 1) * Q := by ring
        linarith only [h1, h2, h4, hC]

end PointCount


end Commons.NumberTheory.ArtinSchreier
