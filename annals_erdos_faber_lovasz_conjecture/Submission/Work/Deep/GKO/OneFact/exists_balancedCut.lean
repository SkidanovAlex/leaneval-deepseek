import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFactDefs
import Submission.Work.Deep.GKO.RegVocab
import Submission.Work.Deep.GKO.OneFact.union_bound_numeric
import Submission.Work.Deep.GKO.OneFact.pairedDeviation_tail

/-!
# A balanced cut with near-regular degrees

For every even `n` and every `r`-regular graph `G` on `Fin n` there is a set `A` of `n / 2`
vertices such that every vertex has a number of neighbours in `A`, and in the complement of `A`,
within `2 n^{2/3}` of `r / 2`.

The argument is the probabilistic method over the *one element per pair* model.  Fix a pairing of
the `n = 2m` vertices of `Fin n`, i.e. a bijection `Fin m × Fin 2 ≃ Fin n`; choose one element of
each pair independently at random.  The resulting set `A x` (indexed by `x : Fin m → Bool`) has
exactly `m = n / 2` elements, so the balance condition holds *deterministically*.

For a fixed vertex `v`, the deviation
`#{neighbours of v in A x} - r/2 = ∑_i σ_i ((if x i then 1 else 0) - 1/2)`
is a sum of independent centred two-valued random variables, with `|σ_i| ≤ 1`, so the elementary
Hoeffding bound `Work.Deep.GKO.OneFact.pairedDeviation_tail` applies.  Summing over the `n`
vertices (union bound) leaves a positive weight of good outcomes and hence some `x` for which every
deviation is `< 2 n^{2/3}`.

## Main results

* `Work.Deep.GKO.OneFact.exists_balancedCut` — the statement requested by the GKO chapter.
-/

namespace Work.Deep.GKO.OneFact

open scoped BigOperators
open Finset Classical

variable {m n : ℕ}

/-! ## The pairing and the balanced sets it produces -/

/-- The pairing of `Fin (m * 2)` into `m` pairs, transported to `Fin n` along `hn : m * 2 = n`. -/
def pairEquiv (hn : m * 2 = n) : Fin m × Fin 2 ≃ Fin n :=
  finProdFinEquiv.trans (finCongr hn)

/-- The element of the `i`-th pair selected by the coin pattern `x`. -/
def pairPick (hn : m * 2 = n) (x : Fin m → Bool) (i : Fin m) : Fin n :=
  pairEquiv hn (i, if x i then 1 else 0)

/-- The vertex set obtained by taking exactly one element of every pair. -/
def pairSet (hn : m * 2 = n) (x : Fin m → Bool) : Finset (Fin n) :=
  Finset.univ.image (pairPick hn x)

theorem pairPick_injective (hn : m * 2 = n) (x : Fin m → Bool) :
    Function.Injective (pairPick hn x) := by
  intro i i' h
  have h2 : (i, (if x i then (1 : Fin 2) else 0)) = (i', (if x i' then 1 else 0)) :=
    (pairEquiv hn).injective h
  simpa using congrArg Prod.fst h2

/-- Every `pairSet` has exactly one element per pair, hence `m = n / 2` elements. -/
theorem pairSet_card (hn : m * 2 = n) (x : Fin m → Bool) : (pairSet hn x).card = m := by
  rw [pairSet, Finset.card_image_of_injective _ (pairPick_injective hn x), Finset.card_univ,
    Fintype.card_fin]

/-- The degree of `v` into `pairSet hn x`, as a sum over the pairs. -/
theorem pairSet_degIn (hn : m * 2 = n) (G : SimpleGraph (Fin n)) (v : Fin n)
    (x : Fin m → Bool) :
    Work.Deep.GKO.degIn G v (pairSet hn x)
      = ∑ i : Fin m, (if G.Adj v (pairPick hn x i) then 1 else 0) := by
  rw [Work.Deep.GKO.degIn, Work.Deep.GKO.nbrFinset, pairSet, Finset.filter_image,
    Finset.card_image_of_injective _ (pairPick_injective hn x), Finset.card_filter]

/-- Splitting a sum over `Fin n` into the two elements of each pair. -/
theorem pair_sum_eq (hn : m * 2 = n) (g : Fin n → ℝ) :
    (∑ i : Fin m, (g (pairEquiv hn (i, 0)) + g (pairEquiv hn (i, 1)))) = ∑ u : Fin n, g u := by
  have h1 : (∑ i : Fin m, (g (pairEquiv hn (i, 0)) + g (pairEquiv hn (i, 1))))
      = ∑ u : Fin m × Fin 2, g (pairEquiv hn u) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun i _ => by rw [Fin.sum_univ_two])
  rw [h1]
  exact Fintype.sum_equiv (pairEquiv hn) (fun u => g (pairEquiv hn u)) g (fun u => rfl)

/-! ## Elementary degree identities -/

/-- The degree into the whole vertex set is the degree of the graph. -/
theorem degIn_univ (G : SimpleGraph (Fin n)) (v : Fin n) :
    Work.Deep.GKO.degIn G v Finset.univ = Nat.card (G.neighborSet v) := by
  rw [Work.Deep.GKO.degIn_eq_ncard, Finset.coe_univ, Set.inter_univ, ← Nat.card_coe_set_eq]

/-- The neighbours of `v` split between a set and its complement. -/
theorem degIn_add_degIn_sdiff (G : SimpleGraph (Fin n)) (v : Fin n) (A : Finset (Fin n)) :
    Work.Deep.GKO.degIn G v A + Work.Deep.GKO.degIn G v (Finset.univ \ A)
      = Nat.card (G.neighborSet v) := by
  classical
  have hunion : Work.Deep.GKO.nbrFinset G v A ∪ Work.Deep.GKO.nbrFinset G v (Finset.univ \ A)
      = Work.Deep.GKO.nbrFinset G v Finset.univ := by
    ext u
    simp only [Work.Deep.GKO.mem_nbrFinset, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ,
      true_and]
    tauto
  have hdisj : Disjoint (Work.Deep.GKO.nbrFinset G v A)
      (Work.Deep.GKO.nbrFinset G v (Finset.univ \ A)) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    simp only [Work.Deep.GKO.mem_nbrFinset, Finset.mem_sdiff, Finset.mem_univ, true_and] at hu hu'
    exact hu'.1 hu.1
  have h3 : (Work.Deep.GKO.nbrFinset G v A).card
      + (Work.Deep.GKO.nbrFinset G v (Finset.univ \ A)).card
      = (Work.Deep.GKO.nbrFinset G v Finset.univ).card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  exact h3.trans (degIn_univ G v)

/-- The number of neighbours of `v` as a sum of indicators. -/
theorem sum_adj_indicator (G : SimpleGraph (Fin n)) (v : Fin n) :
    (∑ u : Fin n, (if G.Adj v u then (1 : ℝ) else 0)) = (Nat.card (G.neighborSet v) : ℝ) := by
  have h : (Work.Deep.GKO.degIn G v Finset.univ : ℝ)
      = ∑ u : Fin n, (if G.Adj v u then (1 : ℝ) else 0) := by
    rw [Work.Deep.GKO.degIn, Work.Deep.GKO.nbrFinset, Finset.card_filter]
    push_cast
    rfl
  rw [← h, degIn_univ]

/-! ## The deviation tail bound at a single vertex

The probabilistic input `pairedDeviation_tail` is proved in
`Submission/Work/Deep/GKO/OneFact/pairedDeviation_tail.lean` and the numeric input
`union_bound_numeric` in `Submission/Work/Deep/GKO/OneFact/union_bound_numeric.lean`. -/

/-- **The deviation tail bound at one vertex.**  For an `r`-regular `G`, the `pairSet`-degrees of
a fixed vertex `v` deviate from `r / 2` by at least `t` only on a set of coin patterns of total
weight at most `2 exp (-2 t² / m)`. -/
theorem vertex_tail_bound (hn : m * 2 = n) (G : SimpleGraph (Fin n)) {r : ℕ}
    (hreg : Work.Deep.GKO.IsRegularOf G r) (v : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    (∑ x : Fin m → Bool, ((1 : ℝ) / 2) ^ m *
        (if t ≤ |((Work.Deep.GKO.degIn G v (pairSet hn x) : ℕ) : ℝ) - (r : ℝ) / 2|
          then 1 else 0))
      ≤ 2 * Real.exp (-(2 * t ^ 2) / (m : ℝ)) := by
  classical
  -- the coefficients of the deviation at `v`
  set c : Fin m → ℝ := fun i => (if G.Adj v (pairEquiv hn (i, 1)) then (1 : ℝ) else 0)
    - (if G.Adj v (pairEquiv hn (i, 0)) then (1 : ℝ) else 0) with hc
  have hc1 : ∀ i, |c i| ≤ 1 := by
    intro i
    rw [hc]
    simp only []
    split_ifs <;> norm_num
  -- the total number of neighbours, counted per pair
  have hpair0 : (∑ i : Fin m, ((if G.Adj v (pairEquiv hn (i, 0)) then (1 : ℝ) else 0)
      + (if G.Adj v (pairEquiv hn (i, 1)) then (1 : ℝ) else 0))) = (r : ℝ) := by
    rw [pair_sum_eq hn (fun u => if G.Adj v u then (1 : ℝ) else 0), sum_adj_indicator G v,
      hreg v]
  have hpair : (∑ i : Fin m, ((if G.Adj v (pairEquiv hn (i, 1)) then (1 : ℝ) else 0)
      + (if G.Adj v (pairEquiv hn (i, 0)) then (1 : ℝ) else 0))) = (r : ℝ) := by
    rw [← hpair0]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  -- the degree as a sum of the per-pair contributions
  have hdeg : ∀ x : Fin m → Bool, ((Work.Deep.GKO.degIn G v (pairSet hn x) : ℕ) : ℝ)
      = ∑ i : Fin m, (if x i = true then (if G.Adj v (pairEquiv hn (i, 1)) then (1 : ℝ) else 0)
          else (if G.Adj v (pairEquiv hn (i, 0)) then (1 : ℝ) else 0)) := by
    intro x
    rw [pairSet_degIn hn G v x]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hx : x i = true <;> simp [pairPick, hx]
  -- the deviation in the form used by the tail bound
  have hdev : ∀ x : Fin m → Bool,
      ((Work.Deep.GKO.degIn G v (pairSet hn x) : ℕ) : ℝ) - (r : ℝ) / 2
        = ∑ i : Fin m, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2) := by
    intro x
    rw [hdeg x, ← hpair, Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hc]
    by_cases hx : x i = true <;> simp [hx] <;> ring
  have key : (∑ x : Fin m → Bool, ((1 : ℝ) / 2) ^ (Fintype.card (Fin m)) *
        (if t ≤ |∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)| then 1 else 0))
      ≤ 2 * Real.exp (-(2 * t ^ 2) / (Fintype.card (Fin m))) := pairedDeviation_tail c hc1 ht
  have key' : (∑ x : Fin m → Bool, ((1 : ℝ) / 2) ^ m *
        (if t ≤ |∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)| then 1 else 0))
      ≤ 2 * Real.exp (-(2 * t ^ 2) / (m : ℝ)) := by simpa using key
  refine le_trans (le_of_eq ?_) key'
  apply Finset.sum_congr rfl
  intro x _
  rw [hdev x]

/-! ## The union bound over all vertices -/

/-- **Union bound.**  If the deviation at each vertex is controlled as in `vertex_tail_bound` and
the total weight `2 n exp (-2 t² / m)` of the bad events is `< 1`, then some coin pattern has all
deviations `< t`. -/
theorem exists_good_pairSet (hn : m * 2 = n) (G : SimpleGraph (Fin n)) {r : ℕ}
    {t : ℝ}
    (hvt : ∀ v : Fin n, (∑ x : Fin m → Bool, ((1 : ℝ) / 2) ^ m *
      (if t ≤ |((Work.Deep.GKO.degIn G v (pairSet hn x) : ℕ) : ℝ) - (r : ℝ) / 2|
        then 1 else 0)) ≤ 2 * Real.exp (-(2 * t ^ 2) / (m : ℝ)))
    (hnum : 2 * (n : ℝ) * Real.exp (-(2 * t ^ 2) / (m : ℝ)) < 1) :
    ∃ x : Fin m → Bool, ∀ v : Fin n,
      |((Work.Deep.GKO.degIn G v (pairSet hn x) : ℕ) : ℝ) - (r : ℝ) / 2| < t := by
  classical
  set w : ℝ := ((1 : ℝ) / 2) ^ m with hw
  have htot : (∑ _x : Fin m → Bool, w) = 1 := by
    rw [hw, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [← mul_pow]
    norm_num
  have hbad : (∑ x : Fin m → Bool, w * (if ∃ v : Fin n,
      t ≤ |((Work.Deep.GKO.degIn G v (pairSet hn x) : ℕ) : ℝ) - (r : ℝ) / 2|
        then 1 else 0)) < 1 := by
    set P : (Fin m → Bool) → Fin n → Prop := fun x v =>
      t ≤ |((Work.Deep.GKO.degIn G v (pairSet hn x) : ℕ) : ℝ) - (r : ℝ) / 2| with hP
    calc (∑ x : Fin m → Bool, w * (if ∃ v : Fin n, P x v then 1 else 0))
        ≤ ∑ x : Fin m → Bool, w * (∑ v : Fin n, (if P x v then 1 else 0)) := by
          apply Finset.sum_le_sum
          intro x _
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          by_cases h : ∃ v : Fin n, P x v
          · rw [if_pos h]
            obtain ⟨v0, hv0⟩ := h
            calc (1 : ℝ) = (if P x v0 then 1 else 0) := (if_pos hv0).symm
              _ ≤ ∑ v : Fin n, (if P x v then 1 else 0) :=
                  Finset.single_le_sum (f := fun v => if P x v then (1 : ℝ) else 0)
                    (fun v _ => by split_ifs <;> norm_num) (Finset.mem_univ v0)
          · rw [if_neg h]
            exact Finset.sum_nonneg (fun v _ => by split_ifs <;> norm_num)
      _ = ∑ v : Fin n, ∑ x : Fin m → Bool, w * (if P x v then 1 else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
      _ ≤ ∑ _v : Fin n, 2 * Real.exp (-(2 * t ^ 2) / (m : ℝ)) := by
          apply Finset.sum_le_sum
          intro v _
          simpa [hw, hP] using hvt v
      _ = (n : ℝ) * (2 * Real.exp (-(2 * t ^ 2) / (m : ℝ))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ < 1 := by linarith
  by_contra hcon
  simp only [not_exists, not_forall, not_lt] at hcon
  have heq : (∑ x : Fin m → Bool, w * (if ∃ v : Fin n,
      t ≤ |((Work.Deep.GKO.degIn G v (pairSet hn x) : ℕ) : ℝ) - (r : ℝ) / 2|
        then 1 else 0)) = ∑ x : Fin m → Bool, w := by
    apply Finset.sum_congr rfl
    intro x _
    rw [if_pos (hcon x), mul_one]
  rw [heq, htot] at hbad
  exact lt_irrefl 1 hbad

/-! ## The balanced cut -/

/-- **A balanced cut with near-regular degrees.**  In every `r`-regular graph on an even number
`n` of vertices there is a set `A` of `n / 2` vertices such that every vertex has a number of
neighbours in `A` — and likewise in the complement of `A` — within `2 n^{2/3}` of `r / 2`. -/
theorem exists_balancedCut {n : ℕ} (hn : Even n) (G : SimpleGraph (Fin n)) {r : ℕ}
    (hreg : Work.Deep.GKO.IsRegularOf G r) :
    ∃ A : Finset (Fin n), A.card = n / 2 ∧
      ∀ v : Fin n,
        |((Work.Deep.GKO.degIn G v A : ℕ) : ℝ) - (r : ℝ) / 2| ≤ 2 * (n : ℝ) ^ ((2 : ℝ) / 3) ∧
        |((Work.Deep.GKO.degIn G v (Finset.univ \ A) : ℕ) : ℝ) - (r : ℝ) / 2|
          ≤ 2 * (n : ℝ) ^ ((2 : ℝ) / 3) := by
  classical
  obtain ⟨m, hm⟩ := hn
  have hmul : m * 2 = n := by omega
  have hmhalf : n / 2 = m := by omega
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- `n = 0`: the empty set is balanced and the degree conditions are vacuous
    subst hm0
    exact ⟨∅, by simp [hm], fun v => absurd v.isLt (by omega)⟩
  · set t : ℝ := 2 * (n : ℝ) ^ ((2 : ℝ) / 3) with ht
    have hn2 : 2 ≤ n := by omega
    have ht0 : 0 ≤ t := by rw [ht]; positivity
    have hvt : ∀ v : Fin n, (∑ x : Fin m → Bool, ((1 : ℝ) / 2) ^ m *
        (if t ≤ |((Work.Deep.GKO.degIn G v (pairSet hmul x) : ℕ) : ℝ) - (r : ℝ) / 2|
          then 1 else 0)) ≤ 2 * Real.exp (-(2 * t ^ 2) / (m : ℝ)) :=
      fun v => vertex_tail_bound hmul G hreg v ht0
    have hnum : 2 * (n : ℝ) * Real.exp (-(2 * t ^ 2) / (m : ℝ)) < 1 := by
      have hcast : ((m : ℕ) : ℝ) = (n : ℝ) / 2 := by
        have h2 : (n : ℝ) = 2 * (m : ℝ) := by rw [hm]; push_cast; ring
        linarith
      rw [ht, hcast, neg_div]
      exact union_bound_numeric hn2
    obtain ⟨x, hx⟩ := exists_good_pairSet hmul G hvt hnum
    refine ⟨pairSet hmul x, ?_, ?_⟩
    · rw [pairSet_card hmul, hmhalf]
    · intro v
      have h1 : |((Work.Deep.GKO.degIn G v (pairSet hmul x) : ℕ) : ℝ) - (r : ℝ) / 2| < t :=
        hx v
      have hle : |((Work.Deep.GKO.degIn G v (pairSet hmul x) : ℕ) : ℝ) - (r : ℝ) / 2|
          ≤ 2 * (n : ℝ) ^ ((2 : ℝ) / 3) := by
        rw [ht] at h1
        exact le_of_lt h1
      have hsplit : Work.Deep.GKO.degIn G v (Finset.univ \ pairSet hmul x)
          = r - Work.Deep.GKO.degIn G v (pairSet hmul x) := by
        have h := degIn_add_degIn_sdiff G v (pairSet hmul x)
        rw [hreg v] at h
        omega
      have hdle : Work.Deep.GKO.degIn G v (pairSet hmul x) ≤ r := by
        have h := degIn_add_degIn_sdiff G v (pairSet hmul x)
        rw [hreg v] at h
        omega
      refine ⟨hle, ?_⟩
      rw [hsplit, Nat.cast_sub hdle]
      have hneg : (r : ℝ) - ((Work.Deep.GKO.degIn G v (pairSet hmul x) : ℕ) : ℝ) - (r : ℝ) / 2
          = -(((Work.Deep.GKO.degIn G v (pairSet hmul x) : ℕ) : ℝ) - (r : ℝ) / 2) := by ring
      rw [hneg, abs_neg]
      exact hle

end Work.Deep.GKO.OneFact
