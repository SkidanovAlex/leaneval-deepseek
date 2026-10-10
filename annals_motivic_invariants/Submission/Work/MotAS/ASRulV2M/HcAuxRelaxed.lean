import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS.ASRulV2M

open MvPolynomial
open Finset

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-!
# The graded substitution lemma (relaxed linear part) [own copy: HcR]

This is a copy-and-adapt of the block `Work.MotK.TGen.HcAux` of
`Submission/Work/MotK/TGen/HcS10.lean`, with the single relaxation that the "linear" part `l i`
is only assumed to have `totalDegree ≤ 1` rather than to be homogeneous of degree `1`.
-/

namespace HcR

variable {σ : Type*} {R : Type*} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **Graded multiplicativity of `homogeneousComponent`** (in antidiagonal form): the degree-`k`
part of a product is the sum of the products of complementary parts. -/
theorem homogeneousComponent_mul (k : ℕ) (p q : MvPolynomial σ R) :
    homogeneousComponent k (p * q) =
      ∑ ij ∈ HasAntidiagonal.antidiagonal k,
        homogeneousComponent ij.1 p * homogeneousComponent ij.2 q := by
  classical
  have decompose_apply : ∀ (m : ℕ) (r : MvPolynomial σ R),
      ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ R) r) m : MvPolynomial σ R)
        = homogeneousComponent m r := by
    intro m r
    have h : (DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ R) r :
        DirectSum ℕ (fun i => ↥(MvPolynomial.homogeneousSubmodule σ R i)))
          = MvPolynomial.decomposition.decompose' r := rfl
    rw [h]
    exact MvPolynomial.decomposition.decompose'_apply r m
  calc homogeneousComponent k (p * q)
      = ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ R) (p * q)) k :
            MvPolynomial σ R) :=
          (decompose_apply k (p * q)).symm
    _ = ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ R) p *
          DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ R) q) k :
            MvPolynomial σ R) := by
          rw [DirectSum.decompose_mul]
    _ = ∑ ij ∈ HasAntidiagonal.antidiagonal k,
          ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ R) p) ij.1 :
              MvPolynomial σ R) *
          ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ R) q) ij.2 :
              MvPolynomial σ R) :=
          DirectSum.coe_mul_apply_eq_sum_antidiagonal (MvPolynomial.homogeneousSubmodule σ R) _ _ k
    _ = ∑ ij ∈ HasAntidiagonal.antidiagonal k,
          homogeneousComponent ij.1 p * homogeneousComponent ij.2 q := by
          refine Finset.sum_congr rfl fun ij _ => ?_
          rw [decompose_apply, decompose_apply]

/-- `Bound p n`: every monomial of `p` has total degree `≤ n`. -/
def Bound (p : MvPolynomial σ R) (n : ℕ) : Prop := ∀ k, n < k → homogeneousComponent k p = 0

/-- `Small p n`: every monomial of `p` has total degree `< n`. -/
def Small (p : MvPolynomial σ R) (n : ℕ) : Prop := ∀ k, n ≤ k → homogeneousComponent k p = 0

theorem Bound.zero (n : ℕ) : Bound (0 : MvPolynomial σ R) n := by
  intro k _
  simp

theorem Small.zero (n : ℕ) : Small (0 : MvPolynomial σ R) n := by
  intro k _
  simp

theorem Bound.mono {p : MvPolynomial σ R} {n m : ℕ} (h : Bound p n) (hmn : n ≤ m) :
    Bound p m :=
  fun k hk => h k (lt_of_le_of_lt hmn hk)

theorem Small.mono {p : MvPolynomial σ R} {n m : ℕ} (h : Small p n) (hmn : n ≤ m) :
    Small p m :=
  fun k hk => h k (le_trans hmn hk)

theorem Small.toBound {p : MvPolynomial σ R} {n : ℕ} (h : Small p n) : Bound p n :=
  fun k hk => h k (le_of_lt hk)

theorem Bound.toSmall {p : MvPolynomial σ R} {n : ℕ} (h : Bound p n) : Small p (n + 1) :=
  fun k hk => h k (lt_of_lt_of_le (Nat.lt_succ_self n) hk)

theorem Bound.of_isHomogeneous {p : MvPolynomial σ R} {n : ℕ} (h : p.IsHomogeneous n) :
    Bound p n := by
  intro k hk
  rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule n p).mpr h)]
  simp [ne_of_gt hk]

theorem Small.of_totalDegree {p : MvPolynomial σ R} {n : ℕ} (h : p.totalDegree < n) :
    Small p n :=
  fun k hk => homogeneousComponent_eq_zero k p (lt_of_lt_of_le h hk)

theorem Bound.add {p q : MvPolynomial σ R} {n : ℕ} (hp : Bound p n) (hq : Bound q n) :
    Bound (p + q) n := by
  intro k hk
  rw [map_add, hp k hk, hq k hk, add_zero]

theorem Small.add {p q : MvPolynomial σ R} {n m : ℕ} (hp : Small p n) (hq : Small q m) :
    Small (p + q) (max n m) := by
  intro k hk
  rw [map_add, hp k ((le_max_left n m).trans hk), hq k ((le_max_right n m).trans hk), add_zero]

theorem Bound.mul {p q : MvPolynomial σ R} {n m : ℕ} (hp : Bound p n) (hq : Bound q m) :
    Bound (p * q) (n + m) := by
  intro k hk
  rw [homogeneousComponent_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hij
  by_cases h : ij.1 ≤ n
  · rw [hq ij.2 (by omega), mul_zero]
  · rw [hp ij.1 (by omega), zero_mul]

theorem Bound.C_mul {p : MvPolynomial σ R} {n : ℕ} (c : R) (hp : Bound p n) :
    Bound (C c * p) n := by
  intro k hk
  rw [homogeneousComponent_C_mul, hp k hk, mul_zero]

theorem Bound.sum {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial σ R} {n : ℕ}
    (h : ∀ i ∈ s, Bound (f i) n) : Bound (∑ i ∈ s, f i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Bound.zero (σ := σ) (R := R) n
  | insert a t hat ih =>
      rw [Finset.sum_insert hat]
      exact (h a (Finset.mem_insert_self a t)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Bound.finsetProd {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial σ R} {A : ι → ℕ}
    (h : ∀ i ∈ s, Bound (f i) (A i)) : Bound (∏ i ∈ s, f i) (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using Bound.of_isHomogeneous (isHomogeneous_one σ R :
        (1 : MvPolynomial σ R).IsHomogeneous 0)
  | insert a t hat ih =>
      rw [Finset.prod_insert hat, Finset.sum_insert hat]
      exact (h a (Finset.mem_insert_self a t)).mul
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Bound.pow {p : MvPolynomial σ R} {n : ℕ} (hp : Bound p n) (m : ℕ) :
    Bound (p ^ m) (n * m) := by
  induction m with
  | zero =>
      simpa using Bound.of_isHomogeneous (isHomogeneous_one σ R :
        (1 : MvPolynomial σ R).IsHomogeneous 0)
  | succ m ih =>
      rw [pow_succ, Nat.mul_succ]
      exact ih.mul hp

theorem Bound.totalDegree_le {p : MvPolynomial σ R} {n : ℕ} (h : Bound p n) :
    p.totalDegree ≤ n := by
  rw [← sum_homogeneousComponent (φ := p)]
  refine totalDegree_finsetSum_le fun i hi => ?_
  rw [Finset.mem_range] at hi
  by_cases hin : i ≤ n
  · exact (homogeneousComponent_isHomogeneous i p).totalDegree_le.trans hin
  · rw [h i (by omega)]
    simp

/-- The degree-`(a+b)` part of `P * x`, for `P` homogeneous of degree `a` and `Bound x b`. -/
theorem homogeneousComponent_mul_of_bound_left {a b : ℕ} {P x : MvPolynomial σ R}
    (hP : P.IsHomogeneous a) (hx : Bound x b) :
    homogeneousComponent (a + b) (P * x) = P * homogeneousComponent b x := by
  rw [homogeneousComponent_mul]
  rw [Finset.sum_eq_single_of_mem (a, b)
    (HasAntidiagonal.mem_antidiagonal.mpr (by simp))]
  · rw [homogeneousComponent_eq_self hP]
  · rintro ⟨i, j⟩ hij hne
    rw [HasAntidiagonal.mem_antidiagonal] at hij
    rcases lt_trichotomy i a with h | h | h
    · rw [hx j (by omega), mul_zero]
    · exact absurd (Prod.ext h (by omega)) hne
    · rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule a P).mpr hP), if_neg (by omega),
        zero_mul]

/-- The degree-`(a+b)` part of `x * y`, for `Small x a` and `Bound y b`. -/
theorem homogeneousComponent_mul_eq_zero {a b : ℕ} {x y : MvPolynomial σ R}
    (hx : Small x a) (hy : Bound y b) : homogeneousComponent (a + b) (x * y) = 0 := by
  rw [homogeneousComponent_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hij
  by_cases h : a ≤ ij.1
  · rw [hx ij.1 h, zero_mul]
  · rw [hy ij.2 (by omega), mul_zero]

/-- Finset form: the degree-`(∑ A)` part of `∏ (P i + Q i)`, where each `P i` is homogeneous of
degree `A i` and each `Q i` has all monomials of degree `< A i`, is `∏ P i`. -/
theorem finsetProd_aux {ι : Type*} (s : Finset ι) {P Q : ι → MvPolynomial σ R} {A : ι → ℕ}
    (hP : ∀ i, (P i).IsHomogeneous (A i)) (hQ : ∀ i, Small (Q i) (A i)) :
    Bound (∏ i ∈ s, (P i + Q i)) (∑ i ∈ s, A i)
      ∧ homogeneousComponent (∑ i ∈ s, A i) (∏ i ∈ s, (P i + Q i)) = ∏ i ∈ s, P i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      constructor
      · simpa using Bound.of_isHomogeneous (isHomogeneous_one σ R :
          (1 : MvPolynomial σ R).IsHomogeneous 0)
      · simp
  | insert a t hat ih =>
      obtain ⟨ihB, ihC⟩ := ih
      rw [Finset.prod_insert hat, Finset.sum_insert hat, Finset.prod_insert hat]
      constructor
      · exact ((Bound.of_isHomogeneous (hP a)).add ((hQ a).toBound)).mul ihB
      · rw [add_mul, map_add, homogeneousComponent_mul_of_bound_left (hP a) ihB, ihC,
          homogeneousComponent_mul_eq_zero (hQ a) ihB, add_zero]

/-- The top part of `(Q + L)^k - Q^k` for `Q` homogeneous of degree `2` and `L` of total degree
`≤ 1`. -/
theorem totalDegree_pow_sub_pow_lt {Q L : MvPolynomial σ R} (hQ : Q.IsHomogeneous 2)
    (hL : L.totalDegree ≤ 1) (k : ℕ) (hk : 1 ≤ k) :
    ((Q + L) ^ k - Q ^ k).totalDegree < 2 * k := by
  induction k with
  | zero => omega
  | succ k ih =>
      rcases eq_or_lt_of_le hk with h | h
      · rw [← h]
        have h1 : (Q + L) ^ 1 - Q ^ 1 = L := by ring
        rw [h1]
        exact lt_of_le_of_lt hL (by norm_num)
      · have ihk : ((Q + L) ^ k - Q ^ k).totalDegree < 2 * k := ih (by omega)
        have hid : (Q + L) ^ (k + 1) - Q ^ (k + 1)
            = ((Q + L) ^ k - Q ^ k) * Q + (Q + L) ^ k * L := by ring
        rw [hid]
        have hQ2 : Q.totalDegree ≤ 2 := hQ.totalDegree_le
        have hL1 : L.totalDegree ≤ 1 := hL
        have hQL : (Q + L).totalDegree ≤ 2 :=
          (totalDegree_add Q L).trans (max_le hQ2 (hL1.trans (by norm_num)))
        have hp : ((Q + L) ^ k).totalDegree ≤ 2 * k := by
          have h := totalDegree_pow (Q + L) k
          calc ((Q + L) ^ k).totalDegree ≤ k * (Q + L).totalDegree := h
            _ ≤ k * 2 := Nat.mul_le_mul_left k hQL
            _ = 2 * k := by ring
        have h1 : (((Q + L) ^ k - Q ^ k) * Q).totalDegree ≤ 2 * k + 1 := by
          have h := totalDegree_mul ((Q + L) ^ k - Q ^ k) Q
          omega
        have h2 : ((Q + L) ^ k * L).totalDegree ≤ 2 * k + 1 := by
          have h := totalDegree_mul ((Q + L) ^ k) L
          omega
        calc (((Q + L) ^ k - Q ^ k) * Q + (Q + L) ^ k * L).totalDegree
            ≤ max _ _ := totalDegree_add _ _
          _ ≤ 2 * k + 1 := max_le h1 h2
          _ < 2 * (k + 1) := by omega

/-- **The main computation**: substituting `y_i = q_i + l_i` (`q_i` homogeneous of degree `2`,
`l_i` of total degree `≤ 1`) into a polynomial `W` with coefficients in the base ring, homogeneous
of degree `d`, the degree-`2d` component only sees the substitution `y_i = q_i`. -/
theorem homogeneousComponent_aeval_add {K : Type*} {τ : Type*} [CommRing K] {n d : ℕ}
    (q l : Fin n → MvPolynomial τ K) (W : MvPolynomial (Fin n) K)
    (hW : W.IsHomogeneous d) (hq : ∀ i, (q i).IsHomogeneous 2)
    (hl : ∀ i, (l i).totalDegree ≤ 1) :
    homogeneousComponent (2 * d) (aeval (fun i => q i + l i) W) = aeval q W := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum W, map_sum, map_sum]
  conv_rhs => rw [MvPolynomial.as_sum W, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : (Finsupp.degree m : ℕ) = d := by
    have h : (Finsupp.weight (fun _ : Fin n => (1 : ℕ))) m = d :=
      hW (by rwa [mem_support_iff] at hm)
    rw [Finsupp.weight_apply] at h
    rw [Finsupp.sum_of_support_subset m (s := m.support) (fun _ hx => hx)
      (fun _ c => c • (1 : ℕ)) (by intro i _; simp)] at h
    rw [Finsupp.degree_apply]
    simpa [smul_eq_mul] using h
  have hsum : (∑ i ∈ m.support, 2 * m i) = 2 * d := by
    rw [← Finset.mul_sum, ← Finsupp.degree_apply, hdeg]
  have key : homogeneousComponent (2 * d) (m.prod (fun i k => (q i + l i) ^ k))
      = m.prod (fun i k => (q i) ^ k) := by
    rw [← hsum,
      Finsupp.prod_of_support_subset m (s := m.support) (fun _ hx => hx)
        (fun i k => (q i + l i) ^ k) (by intro i _; simp),
      Finsupp.prod_of_support_subset m (s := m.support) (fun _ hx => hx)
        (fun i k => (q i) ^ k) (by intro i _; simp)]
    have hprod : (∏ i ∈ m.support, (q i + l i) ^ (m i))
        = ∏ i ∈ m.support,
            ((q i) ^ (m i) + ((q i + l i) ^ (m i) - (q i) ^ (m i))) :=
      Finset.prod_congr rfl fun i _ => by ring
    rw [hprod]
    refine (finsetProd_aux (m.support) (P := fun i => (q i) ^ (m i))
      (Q := fun i => (q i + l i) ^ (m i) - (q i) ^ (m i)) (A := fun i => 2 * m i)
      (fun i => (hq i).pow (m i)) (fun i => ?_)).2
    by_cases hi : m i = 0
    · rw [hi, pow_zero, pow_zero, sub_self]
      exact Small.zero _
    · exact Small.of_totalDegree (totalDegree_pow_sub_pow_lt (hq i) (hl i) (m i) (by omega))
  rw [aeval_monomial, aeval_monomial, MvPolynomial.algebraMap_eq, homogeneousComponent_C_mul, key]

/-- `Bound` version of `homogeneousComponent_aeval_add`. -/
theorem bound_aeval {K : Type*} {τ : Type*} [CommRing K] {n d : ℕ}
    (q l : Fin n → MvPolynomial τ K) (W : MvPolynomial (Fin n) K)
    (hW : W.IsHomogeneous d) (hq : ∀ i, (q i).IsHomogeneous 2)
    (hl : ∀ i, (l i).totalDegree ≤ 1) :
    Bound (aeval (fun i => q i + l i) W) (2 * d) := by
  classical
  intro k hk
  conv_lhs => rw [MvPolynomial.as_sum W, map_sum, map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hdeg : (Finsupp.degree m : ℕ) = d := by
    have h : (Finsupp.weight (fun _ : Fin n => (1 : ℕ))) m = d :=
      hW (by rwa [mem_support_iff] at hm)
    rw [Finsupp.weight_apply] at h
    rw [Finsupp.sum_of_support_subset m (s := m.support) (fun _ hx => hx)
      (fun _ c => c • (1 : ℕ)) (by intro i _; simp)] at h
    rw [Finsupp.degree_apply]
    simpa [smul_eq_mul] using h
  have hsum : (∑ i ∈ m.support, 2 * m i) = 2 * d := by
    rw [← Finset.mul_sum, ← Finsupp.degree_apply, hdeg]
  rw [aeval_monomial, MvPolynomial.algebraMap_eq, homogeneousComponent_C_mul]
  have hzero : homogeneousComponent k (m.prod (fun i k => (q i + l i) ^ k)) = 0 := by
    rw [Finsupp.prod_of_support_subset m (s := m.support) (fun _ hx => hx)
      (fun i k => (q i + l i) ^ k) (by intro i _; simp)]
    refine (Bound.finsetProd (s := m.support) (f := fun i => (q i + l i) ^ (m i))
      (A := fun i => 2 * m i) ?_) k ?_
    · intro i _
      exact Bound.pow ((Bound.of_isHomogeneous (hq i)).add
        ((Small.of_totalDegree (lt_of_le_of_lt (hl i) (by norm_num))).toBound)) (m i)
    · rw [hsum]
      exact hk
  rw [hzero, mul_zero]

/-- A nonzero degree-`n` component forces `n ≤ totalDegree`. -/
theorem le_totalDegree_of_homogeneousComponent_ne_zero {p : MvPolynomial σ R} {n : ℕ}
    (h : homogeneousComponent n p ≠ 0) : n ≤ p.totalDegree := by
  obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero h
  rw [MvPolynomial.coeff_homogeneousComponent] at hd
  split_ifs at hd with hdn
  · rw [← hdn, Finsupp.degree_eq_weight_one, Finsupp.weight_apply]
    simpa [smul_eq_mul] using le_totalDegree (p := p) (by rwa [MvPolynomial.mem_support_iff])
  · exact absurd hd (by simp)

end HcR

/-- **The graded substitution lemma.**  If `W` is homogeneous of degree `d` and each `q i` is
homogeneous of degree `2` while each `l i` has all its monomials of total degree `≤ 1`, then the
substitution `y_i = q_i + l_i` into `W` has degree-`2d` component `W(q)`; moreover nothing of
degree `> 2d` survives.

ROUTE (pure copy-and-adapt; the general lemmas already exist in the workspace).  The whole block
`Work.MotK.TGen.HcAux` of `Submission/Work/MotK/TGen/HcS10.lean` (lines ~30-330:
`homogeneousComponent_mul` in antidiagonal form, `Bound`, `Small` and their calculus,
`finsetProd_aux`, `totalDegree_pow_sub_pow_lt`, `homogeneousComponent_aeval_add`, `bound_aeval`,
`le_totalDegree_of_homogeneousComponent_ne_zero`) proves the same statement with the STRONGER
hypothesis `hl : ∀ i, (l i).IsHomogeneous 1`.  Copy it into this file (namespace
`Work.MotAS.ASRulV2M.HcAux`), with the ONE relaxation `hl : ∀ i, (l i).totalDegree ≤ 1`:

* `totalDegree_pow_sub_pow_lt`: reprove with `hQ : Q.IsHomogeneous 2`, `hL : L.totalDegree ≤ 1`
  via `(Q + L) ^ k - Q ^ k = L * ∑_{j<k} (Q+L)^j * Q^(k-1-j)` and the bounds
  `totalDegree_mul`, `totalDegree_add`, `totalDegree_pow` (`L.totalDegree ≤ 1` gives `≤ 2k-1`).
* everywhere `Bound.of_isHomogeneous (hl i)` is used, replace it by the `Bound` obtained from
  `hl i` through `Small.of_totalDegree (lt_of_le_of_lt (hl i) (by norm_num))` and `Small.toBound`.

The antidiagonal version of product multiplicativity needs
`attribute [local instance] MvPolynomial.gradedAlgebra` and
`DirectSum.decompose_mul` / `DirectSum.coe_mul_apply_eq_sum_antidiagonal` (as in `HcS10.lean`). -/
theorem homogeneousComponent_aeval_add {K : Type} [CommRing K] {τ : Type} {n d : ℕ}
    (q l : Fin n → MvPolynomial τ K) (W : MvPolynomial (Fin n) K)
    (hW : W.IsHomogeneous d) (hq : ∀ i, (q i).IsHomogeneous 2)
    (hl : ∀ i, (l i).totalDegree ≤ 1) :
    (MvPolynomial.homogeneousComponent (2 * d) (MvPolynomial.aeval (fun i => q i + l i) W)
        = MvPolynomial.aeval q W)
      ∧ (∀ k, 2 * d < k →
          MvPolynomial.homogeneousComponent k
            (MvPolynomial.aeval (fun i => q i + l i) W) = 0) := by
  exact ⟨HcR.homogeneousComponent_aeval_add q l W hW hq hl,
   HcR.bound_aeval q l W hW hq hl⟩

end Work.MotAS.ASRulV2M
