import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs

/-!
# A Hamilton decomposition is a 1-factorization

This file proves `Work.Deep.GKO.oneFactorization_of_hamDecomp`: if `G` is an `r`-regular graph on
an even number `n` of vertices and `G` has a Hamilton decomposition (its edge set is partitioned
into Hamilton cycles), then the edge set of `G` is partitioned into `r` perfect matchings.

The proof has three parts.

* A Hamilton cycle `H` on an even number of vertices is the edge-disjoint union of two perfect
  matchings: enumerate the vertices of the cycle cyclically as `ψ 0, ψ 1, …, ψ (n-1)`, and take
  the edges `{ψ i, ψ (i+1)}` with `i` even, respectively with `i` odd (indices mod `n`).
* Each Hamilton cycle of the decomposition contributes exactly two neighbours to every vertex,
  so counting the neighbours of a fixed vertex gives `r = 2 * k` for a decomposition with `k`
  cycles.
* Splitting every cycle and re-indexing the resulting `2 * k` matchings by `Fin r` (using
  `r = 2 * k`) gives the 1-factorization.  The case `n = 0` (where `r` is not determined by the
  decomposition) is handled separately by taking the empty matchings.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.GKO

open SimpleGraph

noncomputable section

variable {n : ℕ}

namespace OneFact

/-! ## The cyclic successor and predecessor on `Fin n` -/

/-- The cyclic successor on `Fin n`: `j ↦ j + 1` for `j ≠ n - 1` and `j ↦ 0` for `j = n - 1`. -/
def cycSucc (j : Fin n) : Fin n :=
  if h : (j : ℕ) + 1 < n then ⟨(j : ℕ) + 1, h⟩ else ⟨0, by have := j.isLt; omega⟩

/-- The predecessor `j ↦ j - 1` of a *nonzero* index (`finPred 0 = 0`). -/
def finPred (i : Fin n) : Fin n := ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩

lemma finPred_val (i : Fin n) : (finPred i : ℕ) = (i : ℕ) - 1 := rfl

lemma cycSucc_val_of_lt {j : Fin n} (h : (j : ℕ) + 1 < n) : (cycSucc j : ℕ) = (j : ℕ) + 1 := by
  rw [cycSucc, dif_pos h]

lemma cycSucc_val_of_eq {j : Fin n} (h : (j : ℕ) + 1 = n) : (cycSucc j : ℕ) = 0 := by
  rw [cycSucc, dif_neg (by omega)]

lemma cycSucc_val (j : Fin n) : (cycSucc j : ℕ) = ((j : ℕ) + 1) % n := by
  by_cases h : (j : ℕ) + 1 < n
  · rw [cycSucc_val_of_lt h, Nat.mod_eq_of_lt h]
  · have hj : (j : ℕ) + 1 = n := by have := j.isLt; omega
    rw [cycSucc_val_of_eq hj, hj, Nat.mod_self]

lemma cycSucc_inj {i j : Fin n} (h : cycSucc i = cycSucc j) : i = j := by
  have hv := congrArg Fin.val h
  rw [cycSucc_val, cycSucc_val] at hv
  have hi := i.isLt
  have hj := j.isLt
  rcases lt_or_eq_of_le (show (i : ℕ) + 1 ≤ n by omega) with h1 | h1 <;>
    rcases lt_or_eq_of_le (show (j : ℕ) + 1 ≤ n by omega) with h2 | h2
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hv; omega
  · rw [Nat.mod_eq_of_lt h1, h2, Nat.mod_self] at hv; omega
  · rw [h1, Nat.mod_self, Nat.mod_eq_of_lt h2] at hv; omega
  · rw [h1, h2, Nat.mod_self] at hv; omega

lemma cycSucc_val_even {i : Fin n} (hn : Even n) (hi : Even (i : ℕ)) :
    (cycSucc i : ℕ) = (i : ℕ) + 1 := by
  obtain ⟨m, hm⟩ := hn
  obtain ⟨k, hk⟩ := hi
  exact cycSucc_val_of_lt (by omega)

lemma cycSucc_even_isOdd {i : Fin n} (hn : Even n) (hi : Even (i : ℕ)) :
    Odd (cycSucc i : ℕ) := by
  rw [cycSucc_val_even hn hi]
  obtain ⟨k, hk⟩ := hi
  exact ⟨k, by omega⟩

lemma cycSucc_odd_isEven {j : Fin n} (hn : Even n) (hj : Odd (j : ℕ)) :
    Even (cycSucc j : ℕ) := by
  by_cases h : (j : ℕ) + 1 < n
  · rw [cycSucc_val_of_lt h]
    obtain ⟨k, hk⟩ := hj
    exact ⟨k + 1, by omega⟩
  · rw [cycSucc_val_of_eq (by have := j.isLt; omega)]
    exact ⟨0, rfl⟩

lemma cycSucc_ne_self_of_even {j : Fin n} (hn : Even n) (h : Even (j : ℕ)) :
    cycSucc j ≠ j := by
  intro hc
  have := congrArg Fin.val hc
  rw [cycSucc_val_even hn h] at this
  omega

lemma cycSucc_ne_self_of_odd {j : Fin n} (hj : Odd (j : ℕ)) : cycSucc j ≠ j := by
  intro hc
  obtain ⟨k, hk⟩ := hj
  have hv := congrArg Fin.val hc
  rw [cycSucc_val] at hv
  have hj' := j.isLt
  rcases lt_or_eq_of_le (show (j : ℕ) + 1 ≤ n by omega) with h | h
  · rw [Nat.mod_eq_of_lt h] at hv; omega
  · rw [h, Nat.mod_self] at hv; omega

private lemma mod_add_mod (a b n : ℕ) (hb : b < n) : (a % n + b) % n = (a + b) % n := by
  have h : a % n + b = a % n + b % n := by rw [Nat.mod_eq_of_lt hb]
  rw [h]
  exact (Nat.add_mod a b n).symm

lemma cycSucc_succ_val (h2 : 2 ≤ n) (j : Fin n) :
    (cycSucc (cycSucc j) : ℕ) = ((j : ℕ) + 2) % n := by
  have h1 : 1 < n := by omega
  rw [cycSucc_val, cycSucc_val, mod_add_mod _ 1 n h1]

/-- The cyclic successor has no cycles of length two when `n ≥ 3`. -/
lemma cycSucc_succ_ne_self {j : Fin n} (h3 : 3 ≤ n) : cycSucc (cycSucc j) ≠ j := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [cycSucc_succ_val (by omega) j] at hv
  have hj := j.isLt
  have hmod : (n + 1) % n = 1 := by
    have h1 : 1 < n := by omega
    rw [Nat.add_comm n 1, Nat.add_mod]
    simp [Nat.mod_self, Nat.mod_eq_of_lt h1]
  have h1 : (j : ℕ) + 2 ≤ n + 1 := by omega
  rcases lt_or_eq_of_le h1 with h | h
  · rcases lt_or_eq_of_le (show (j : ℕ) + 2 ≤ n by omega) with h' | h'
    · rw [Nat.mod_eq_of_lt h'] at hv; omega
    · rw [h', Nat.mod_self] at hv; omega
  · rw [h, hmod] at hv
    omega

lemma cycSucc_finPred (i : Fin n) (h0 : (i : ℕ) ≠ 0) : cycSucc (finPred i) = i := by
  have hlt : (finPred i : ℕ) + 1 < n := by rw [finPred_val]; have := i.isLt; omega
  apply Fin.ext
  rw [cycSucc_val_of_lt hlt, finPred_val]
  omega

lemma even_pred_of_odd {i : Fin n} (h : Odd (i : ℕ)) : Even (finPred i : ℕ) := by
  obtain ⟨k, hk⟩ := h
  rw [finPred_val]
  exact ⟨k, by omega⟩

lemma odd_pred_of_even {i : Fin n} (h : Even (i : ℕ)) (h0 : (i : ℕ) ≠ 0) :
    Odd (finPred i : ℕ) := by
  obtain ⟨k, hk⟩ := h
  rw [finPred_val]
  exact ⟨k - 1, by omega⟩

/-! ## Two matchings from a cyclic enumeration of the vertices

Fix a bijection `ψ : Fin n ≃ Fin n` (the cyclic enumeration of the vertices of a Hamilton
cycle, so that consecutive indices are adjacent).  We build the two alternating matchings `MA`
and `MB` of the cycle. -/

variable (ψ : Fin n ≃ Fin n)

/-- The edge joining the `i`-th and the `(i+1)`-st vertex of the cyclic enumeration. -/
def AEdge (i : Fin n) : Sym2 (Fin n) := s(ψ i, ψ (cycSucc i))

/-- The edges at even positions. -/
def MA : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | ∃ i : Fin n, Even (i : ℕ) ∧ e = AEdge ψ i}

/-- The edges at odd positions. -/
def MB : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | ∃ i : Fin n, Odd (i : ℕ) ∧ e = AEdge ψ i}

lemma AEdge_mem_iff {i : Fin n} {x : Fin n} :
    x ∈ AEdge ψ i ↔ ψ.symm x = i ∨ ψ.symm x = cycSucc i := by
  rw [AEdge, Sym2.mem_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (by rw [h, Equiv.symm_apply_apply])
    · exact Or.inr (by rw [h, Equiv.symm_apply_apply])
  · rintro (h | h)
    · exact Or.inl (by rw [← h]; simp)
    · exact Or.inr (by rw [← h]; simp)

lemma AEdge_mem_inj {i j : Fin n} (hn : Even n) (hi : Even (i : ℕ)) (hj : Even (j : ℕ))
    {x : Fin n} (hx : x ∈ AEdge ψ i) (hx' : x ∈ AEdge ψ j) : i = j := by
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb⟩ := hj
  have hvi : (cycSucc i : ℕ) = (i : ℕ) + 1 := cycSucc_val_even hn ⟨a, ha⟩
  have hvj : (cycSucc j : ℕ) = (j : ℕ) + 1 := cycSucc_val_even hn ⟨b, hb⟩
  rw [AEdge_mem_iff] at hx hx'
  rcases hx with h | h <;> rcases hx' with h' | h'
  · exact h.symm.trans h'
  · have hij : i = cycSucc j := h.symm.trans h'
    have : (i : ℕ) = (j : ℕ) + 1 := by rw [hij, hvj]
    omega
  · have hji : j = cycSucc i := h'.symm.trans h
    have : (j : ℕ) = (i : ℕ) + 1 := by rw [hji, hvi]
    omega
  · have hss : cycSucc i = cycSucc j := h.symm.trans h'
    have : (i : ℕ) + 1 = (j : ℕ) + 1 := by rw [← hvi, ← hvj, hss]
    exact Fin.ext (by omega)

lemma AEdge_mem_inj_odd {i j : Fin n} (hn : Even n) (hi : Odd (i : ℕ)) (hj : Odd (j : ℕ))
    {x : Fin n} (hx : x ∈ AEdge ψ i) (hx' : x ∈ AEdge ψ j) : i = j := by
  rw [AEdge_mem_iff] at hx hx'
  rcases hx with h | h <;> rcases hx' with h' | h'
  · exact h.symm.trans h'
  · have hij : i = cycSucc j := h.symm.trans h'
    have hiσ : (i : ℕ) = (cycSucc j : ℕ) := congrArg Fin.val hij
    obtain ⟨a, ha⟩ := hi
    obtain ⟨b, hb⟩ := cycSucc_odd_isEven hn hj
    omega
  · have hji : j = cycSucc i := h'.symm.trans h
    have hjσ : (j : ℕ) = (cycSucc i : ℕ) := congrArg Fin.val hji
    obtain ⟨a, ha⟩ := hj
    obtain ⟨b, hb⟩ := cycSucc_odd_isEven hn hi
    omega
  · exact cycSucc_inj (h.symm.trans h')

lemma MA_le_H {H : SimpleGraph (Fin n)} (hAdj : ∀ j : Fin n, H.Adj (ψ j) (ψ (cycSucc j))) :
    MA ψ ≤ H := by
  intro x y hxy
  obtain ⟨⟨i, -, heq⟩, -⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
  rw [← SimpleGraph.mem_edgeSet, heq]
  exact (SimpleGraph.mem_edgeSet H).mpr (hAdj i)

lemma MB_le_H {H : SimpleGraph (Fin n)} (hAdj : ∀ j : Fin n, H.Adj (ψ j) (ψ (cycSucc j))) :
    MB ψ ≤ H := by
  intro x y hxy
  obtain ⟨⟨i, -, heq⟩, -⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
  rw [← SimpleGraph.mem_edgeSet, heq]
  exact (SimpleGraph.mem_edgeSet H).mpr (hAdj i)

lemma MA_isMatching (hn : Even n) : IsMatching' (MA ψ) := by
  intro x y y' hxy hxy'
  obtain ⟨⟨i, hi, hi'⟩, -⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
  obtain ⟨⟨j, hj, hj'⟩, -⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy'
  have hx : x ∈ AEdge ψ i := hi' ▸ Sym2.mem_mk_left x y
  have hx' : x ∈ AEdge ψ j := hj' ▸ Sym2.mem_mk_left x y'
  have hij : i = j := AEdge_mem_inj ψ hn hi hj hx hx'
  subst hij
  exact Sym2.congr_right.mp (hi'.trans hj'.symm)

lemma MB_isMatching (hn : Even n) : IsMatching' (MB ψ) := by
  intro x y y' hxy hxy'
  obtain ⟨⟨i, hi, hi'⟩, -⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
  obtain ⟨⟨j, hj, hj'⟩, -⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy'
  have hx : x ∈ AEdge ψ i := hi' ▸ Sym2.mem_mk_left x y
  have hx' : x ∈ AEdge ψ j := hj' ▸ Sym2.mem_mk_left x y'
  have hij : i = j := AEdge_mem_inj_odd ψ hn hi hj hx hx'
  subst hij
  exact Sym2.congr_right.mp (hi'.trans hj'.symm)

lemma MA_exists (hn : Even n) (x : Fin n) : ∃ y, (MA ψ).Adj x y := by
  set i : Fin n := ψ.symm x with hidx
  have hxψ : ψ i = x := ψ.apply_symm_apply x
  by_cases h : Even (i : ℕ)
  · refine ⟨ψ (cycSucc i), ?_⟩
    rw [MA, SimpleGraph.fromEdgeSet_adj]
    refine ⟨⟨i, h, ?_⟩, ?_⟩
    · rw [← hxψ]; rfl
    · intro hc
      exact cycSucc_ne_self_of_even hn h (ψ.injective (hxψ.trans hc)).symm
  · have hodd : Odd (i : ℕ) := Nat.not_even_iff_odd.mp h
    refine ⟨ψ (finPred i), ?_⟩
    rw [MA, SimpleGraph.fromEdgeSet_adj]
    refine ⟨⟨finPred i, even_pred_of_odd hodd, ?_⟩, ?_⟩
    · rw [AEdge, cycSucc_finPred i (by obtain ⟨k, hk⟩ := hodd; omega), ← hxψ]
      exact Sym2.eq_swap
    · intro hc
      have h2 := congrArg Fin.val (ψ.injective (hxψ.trans hc))
      rw [finPred_val] at h2
      obtain ⟨k, hk⟩ := hodd
      omega

lemma MB_exists (hn : Even n) (x : Fin n) : ∃ y, (MB ψ).Adj x y := by
  set i : Fin n := ψ.symm x with hidx
  have hxψ : ψ i = x := ψ.apply_symm_apply x
  have hnpos : 0 < n := by have := i.isLt; omega
  by_cases h : Odd (i : ℕ)
  · refine ⟨ψ (cycSucc i), ?_⟩
    rw [MB, SimpleGraph.fromEdgeSet_adj]
    refine ⟨⟨i, h, ?_⟩, ?_⟩
    · rw [← hxψ]; rfl
    · intro hc
      exact cycSucc_ne_self_of_odd h (ψ.injective (hxψ.trans hc)).symm
  · have hev : Even (i : ℕ) := Nat.not_odd_iff_even.mp h
    by_cases h0 : (i : ℕ) = 0
    · refine ⟨ψ ⟨n - 1, by omega⟩, ?_⟩
      rw [MB, SimpleGraph.fromEdgeSet_adj]
      refine ⟨⟨⟨n - 1, by omega⟩, ?_, ?_⟩, ?_⟩
      · obtain ⟨k, hk⟩ := hn
        refine ⟨k - 1, ?_⟩
        show n - 1 = 2 * (k - 1) + 1
        omega
      · have hlast : cycSucc (⟨n - 1, by omega⟩ : Fin n) = (⟨0, hnpos⟩ : Fin n) := by
          apply Fin.ext
          rw [cycSucc_val]
          have h1 : ((⟨n - 1, by omega⟩ : Fin n) : ℕ) + 1 = n := by
            rw [Fin.val_mk]; omega
          rw [h1, Nat.mod_self]
        rw [AEdge, hlast]
        have hx0 : x = ψ (⟨0, hnpos⟩ : Fin n) := by
          rw [← hxψ]; exact congrArg ψ (Fin.ext h0)
        exact Sym2.eq_iff.mpr (Or.inr ⟨hx0, rfl⟩)
      · intro hc
        have h2 := congrArg Fin.val (ψ.injective (hxψ.trans hc).symm)
        obtain ⟨k, hk⟩ := hn
        simp at h2
        omega
    · refine ⟨ψ (finPred i), ?_⟩
      rw [MB, SimpleGraph.fromEdgeSet_adj]
      refine ⟨⟨finPred i, odd_pred_of_even hev h0, ?_⟩, ?_⟩
      · rw [AEdge, cycSucc_finPred i h0, ← hxψ]
        exact Sym2.eq_swap
      · intro hc
        have h2 := congrArg Fin.val (ψ.injective (hxψ.trans hc))
        rw [finPred_val] at h2
        omega

lemma MA_perfect (hn : Even n) {H : SimpleGraph (Fin n)}
    (hAdj : ∀ j : Fin n, H.Adj (ψ j) (ψ (cycSucc j))) : IsPerfectMatching' H (MA ψ) :=
  ⟨MA_le_H ψ hAdj, fun x => (MA_exists ψ hn x).imp
    (fun y hy => ⟨hy, fun y' hy' => MA_isMatching ψ hn x y' y hy' hy⟩)⟩

lemma MB_perfect (hn : Even n) {H : SimpleGraph (Fin n)}
    (hAdj : ∀ j : Fin n, H.Adj (ψ j) (ψ (cycSucc j))) : IsPerfectMatching' H (MB ψ) :=
  ⟨MB_le_H ψ hAdj, fun x => (MB_exists ψ hn x).imp
    (fun y hy => ⟨hy, fun y' hy' => MB_isMatching ψ hn x y' y hy' hy⟩)⟩

/-- The two alternating matchings of a cycle are edge disjoint. -/
lemma MA_disjoint_MB (hn3 : 3 ≤ n) : Disjoint (MA ψ).edgeSet (MB ψ).edgeSet := by
  rw [Set.disjoint_left]
  intro e heA heB
  induction e using Sym2.ind with
  | _ x y =>
    rw [SimpleGraph.mem_edgeSet] at heA heB
    obtain ⟨⟨i, hi, hi'⟩, -⟩ := (SimpleGraph.fromEdgeSet_adj _).mp heA
    obtain ⟨⟨j, hj, hj'⟩, -⟩ := (SimpleGraph.fromEdgeSet_adj _).mp heB
    have heq : AEdge ψ i = AEdge ψ j := hi'.symm.trans hj'
    rw [AEdge, AEdge, Sym2.eq_iff] at heq
    obtain ⟨a, ha⟩ := hi
    obtain ⟨b, hb⟩ := hj
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hij : i = j := ψ.injective h1
      rw [hij] at ha
      omega
    · have hij : i = cycSucc j := ψ.injective h1
      have hji : cycSucc i = j := ψ.injective h2
      have hss : cycSucc (cycSucc j) = j := by rw [← hij]; exact hji
      exact (cycSucc_succ_ne_self hn3) hss

/-- Every edge of a Hamilton cycle lies in one of the two alternating matchings: the two
matchings cover the edge set of the cycle.  This uses that every vertex has exactly two
neighbours in the graph and that the two matchings provide two *distinct* neighbours. -/
lemma MA_MB_cover {H : SimpleGraph (Fin n)} (hn : Even n)
    (hdeg : ∀ v : Fin n, Nat.card (H.neighborSet v) = 2)
    (hAdj : ∀ j : Fin n, H.Adj (ψ j) (ψ (cycSucc j)))
    (hdisj : Disjoint (MA ψ).edgeSet (MB ψ).edgeSet) :
    ∀ e ∈ H.edgeSet, e ∈ (MA ψ).edgeSet ∨ e ∈ (MB ψ).edgeSet := by
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    have hadj : H.Adj x y := (SimpleGraph.mem_edgeSet H).mp he
    obtain ⟨w₀, hw₀⟩ := MA_exists ψ hn x
    obtain ⟨w₁, hw₁⟩ := MB_exists ψ hn x
    have hw₀H : w₀ ∈ H.neighborSet x :=
      (SimpleGraph.mem_neighborSet H x w₀).mpr (MA_le_H ψ hAdj hw₀)
    have hw₁H : w₁ ∈ H.neighborSet x :=
      (SimpleGraph.mem_neighborSet H x w₁).mpr (MB_le_H ψ hAdj hw₁)
    have hne : w₀ ≠ w₁ := by
      intro h
      rw [h] at hw₀
      exact (Set.disjoint_left.mp hdisj) ((SimpleGraph.mem_edgeSet (MA ψ)).mpr hw₀)
        ((SimpleGraph.mem_edgeSet (MB ψ)).mpr hw₁)
    have hx2 : (H.neighborSet x).ncard = 2 := by
      rw [← Nat.card_coe_set_eq]; exact hdeg x
    obtain ⟨a, b, hab, hset⟩ := Set.ncard_eq_two.mp hx2
    have hpairs : ({w₀, w₁} : Set (Fin n)) = {a, b} := by
      refine Set.eq_of_subset_of_ncard_le ?_ ?_
      · intro z hz
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact hset ▸ hw₀H
        · exact hset ▸ hw₁H
      · rw [Set.ncard_pair hab, Set.ncard_pair hne]
    have hy : y ∈ ({w₀, w₁} : Set (Fin n)) :=
      hpairs ▸ (hset ▸ ((SimpleGraph.mem_neighborSet H x y).mpr hadj))
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy
    · left
      rw [SimpleGraph.mem_edgeSet, hy]
      exact hw₀
    · right
      rw [SimpleGraph.mem_edgeSet, hy]
      exact hw₁

/-- A graph whose edge set is the (edge disjoint) union of two alternating perfect matchings
of a cyclic enumeration. -/
theorem two_matchings_of_cycleEnum {H : SimpleGraph (Fin n)} (hn : Even n)
    (hdeg : ∀ v : Fin n, Nat.card (H.neighborSet v) = 2)
    (hAdj : ∀ j : Fin n, H.Adj (ψ j) (ψ (cycSucc j))) (hn3 : 3 ≤ n) :
    ∃ MA' MB' : SimpleGraph (Fin n),
      IsPerfectMatching' H MA' ∧ IsPerfectMatching' H MB' ∧
      Disjoint MA'.edgeSet MB'.edgeSet ∧
      (∀ e ∈ H.edgeSet, e ∈ MA'.edgeSet ∨ e ∈ MB'.edgeSet) :=
  ⟨MA ψ, MB ψ, MA_perfect ψ hn hAdj, MB_perfect ψ hn hAdj,
    MA_disjoint_MB ψ hn3, MA_MB_cover ψ hn hdeg hAdj (MA_disjoint_MB ψ hn3)⟩

/-- From a Hamilton cycle on a graph on an even number of vertices we extract a cyclic
enumeration `ψ` of the vertices: the `ψ i` for `i = 0, …, n-1` are all the vertices and
consecutive ones (cyclically) are adjacent. -/
theorem exists_cycleEnum {H : SimpleGraph (Fin n)} (hn : Even n) (hH : IsHamiltonCycle' H) :
    ∃ ψ : Fin n ≃ Fin n, (∀ j : Fin n, H.Adj (ψ j) (ψ (cycSucc j))) ∧ 3 ≤ n := by
  obtain ⟨hHam, hdeg⟩ := hH
  obtain ⟨m, hm⟩ := hn
  obtain ⟨a, p, hp⟩ := hHam (by rw [Fintype.card_fin]; omega)
  have hlen : p.length = n := by rw [hp.length_eq, Fintype.card_fin]
  have hn3 : 3 ≤ n := by have := hp.three_le_length; omega
  have hpt := hp.isHamiltonian_tail
  have hlen' : p.tail.support.length = n := by rw [hpt.length_support, Fintype.card_fin]
  let ψ : Fin n ≃ Fin n := (finCongr hlen'.symm).trans hpt.getVertEquiv
  have hψ : ∀ j : Fin n, (ψ j : Fin n) = p.getVert ((j : ℕ) + 1) := by
    intro j
    show ((finCongr hlen'.symm).trans hpt.getVertEquiv) j = _
    rw [Equiv.trans_apply, finCongr_apply, hpt.getVertEquiv_apply]
    show p.tail.getVert (Fin.cast hlen'.symm j : ℕ) = p.getVert (↑j + 1)
    rw [SimpleGraph.Walk.getVert_tail, Fin.val_cast]
  refine ⟨ψ, fun j => ?_, hn3⟩
  rw [hψ j, hψ (cycSucc j)]
  by_cases hlast : (j : ℕ) + 1 < n
  · rw [cycSucc_val_of_lt hlast]
    exact p.adj_getVert_succ (by rw [hlen]; exact hlast)
  · have hj : (j : ℕ) + 1 = n := by have := j.isLt; omega
    rw [cycSucc_val_of_eq hj]
    have hstep : p.getVert (↑j + 1) = p.getVert 0 := by
      rw [p.getVert_of_length_le (i := ↑j + 1) (by rw [hlen, hj]), p.getVert_zero]
    rw [hstep]
    exact p.adj_getVert_succ (by rw [hlen]; omega)

/-- **A Hamilton cycle on an even number of vertices splits into two perfect matchings** whose
edge sets are disjoint and cover the edge set of the cycle. -/
theorem exists_two_perfectMatchings_of_hamCycle {H : SimpleGraph (Fin n)} (hn : Even n)
    (hH : IsHamiltonCycle' H) :
    ∃ MA' MB' : SimpleGraph (Fin n),
      IsPerfectMatching' H MA' ∧ IsPerfectMatching' H MB' ∧
      Disjoint MA'.edgeSet MB'.edgeSet ∧
      (∀ e ∈ H.edgeSet, e ∈ MA'.edgeSet ∨ e ∈ MB'.edgeSet) := by
  obtain ⟨ψ, hAdj, hn3⟩ := exists_cycleEnum hn hH
  exact two_matchings_of_cycleEnum ψ hn hH.2 hAdj hn3

/-- **Counting along a Hamilton decomposition.**  If the edge set of `G` is partitioned into
`k` Hamilton cycles and every vertex of `G` has exactly `r` neighbours, then `r = 2 * k`:
each Hamilton cycle contributes exactly two neighbours to every vertex. -/
theorem eq_two_mul_of_partition_into_cycles {G : SimpleGraph (Fin n)} {r k : ℕ}
    (hr : IsRegularOf G r) (C : Fin k → SimpleGraph (Fin n))
    (hcyc : ∀ i, IsHamiltonCycle' (C i)) (hle : ∀ i, C i ≤ G)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i).edgeSet (C j).edgeSet)
    (hcov : ∀ e ∈ G.edgeSet, ∃ i, e ∈ (C i).edgeSet) (v : Fin n) : r = 2 * k := by
  classical
  let g : (Σ i : Fin k, ↥((C i).neighborSet v)) → ↥(G.neighborSet v) :=
    fun p => ⟨p.2.1, (SimpleGraph.mem_neighborSet G v p.2.1).mpr
      (hle p.1 ((SimpleGraph.mem_neighborSet (C p.1) v p.2.1).mp p.2.2))⟩
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨i, w, hw⟩ ⟨j, z, hz⟩ heq
      have hwz : w = z := congrArg Subtype.val heq
      by_cases hij : i = j
      · subst hij
        subst hwz
        rfl
      · exfalso
        have h1 : s(v, w) ∈ (C i).edgeSet :=
          (SimpleGraph.mem_edgeSet (C i)).mpr ((SimpleGraph.mem_neighborSet (C i) v w).mp hw)
        have h2 : s(v, w) ∈ (C j).edgeSet := by
          rw [hwz]
          exact (SimpleGraph.mem_edgeSet (C j)).mpr ((SimpleGraph.mem_neighborSet (C j) v z).mp hz)
        exact (Set.disjoint_left.mp (hdisj i j hij)) h1 h2
    · intro y
      have hy : G.Adj v y.1 := (SimpleGraph.mem_neighborSet G v y.1).mp y.2
      obtain ⟨i, hi⟩ := hcov s(v, y.1) ((SimpleGraph.mem_edgeSet G).mpr hy)
      refine ⟨⟨i, ⟨y.1, ?_⟩⟩, ?_⟩
      · exact (SimpleGraph.mem_neighborSet (C i) v y.1).mpr
          ((SimpleGraph.mem_edgeSet (C i)).mp hi)
      · rfl
  have hcard : Fintype.card (Σ i : Fin k, ↥((C i).neighborSet v)) =
      Fintype.card ↥(G.neighborSet v) :=
    Fintype.card_congr (Equiv.ofBijective g hg)
  have key : (G.neighborSet v).ncard = ∑ i : Fin k, ((C i).neighborSet v).ncard := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, ← hcard, Fintype.card_sigma]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq])
  have h2 : (G.neighborSet v).ncard = 2 * k := by
    rw [key]
    have hsum : ∀ i : Fin k, ((C i).neighborSet v).ncard = 2 := by
      intro i
      rw [← Nat.card_coe_set_eq]
      exact (hcyc i).2 v
    calc ∑ i : Fin k, ((C i).neighborSet v).ncard
        = ∑ _i : Fin k, (2 : ℕ) := Finset.sum_congr rfl (fun i _ => hsum i)
      _ = k * 2 := by simp
      _ = 2 * k := by rw [Nat.mul_comm]
  have hr' := hr v
  rw [Nat.card_coe_set_eq] at hr'
  omega

end OneFact

/-- A Hamilton decomposition of an `r`-regular graph on an even number of vertices is a 1-factorization: each Hamilton cycle of the decomposition splits into two perfect matchings, and the number of cycles is `r/2` (the cycles partition `E(G)`, each Hamilton cycle has `n` edges and `2|E(G)| = rn`).

`Work.Deep.GKO.HasHamiltonDecomposition` uses `IsHamiltonCycle' H := H.IsHamiltonian ∧ (∀ v, Nat.card (H.neighborSet v) = 2)`, i.e. the parts really are Hamilton cycles (a single spanning cycle), not merely graphs containing one.

This is how the Kühn–Osthus Hamilton-decomposition result (`Work.Deep.GKO.KOStatement`) is applied in the reduction: it supplies `r` colours for the `r`-regular remainder. -/
theorem oneFactorization_of_hamDecomp {n : ℕ} (G : SimpleGraph (Fin n)) {r : ℕ}
    (hr : Work.Deep.GKO.IsRegularOf G r) (hn : Even n)
    (h : Work.Deep.GKO.HasHamiltonDecomposition G) :
    Work.Deep.GKO.HasOneFactorization G r := by
  classical
  obtain ⟨k, C, hle, hcyc, hdisj, hcov⟩ := h
  by_cases hn0 : n = 0
  · subst hn0
    refine ⟨fun _ => ⊥, ?_, ?_, ?_⟩
    · intro i
      exact ⟨bot_le, fun v => Fin.elim0 v⟩
    · intro i j hij
      rw [SimpleGraph.edgeSet_bot]
      exact disjoint_bot_left
    · intro e he
      induction e using Sym2.ind with
      | _ v w => exact Fin.elim0 v
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hsplit : ∀ i, ∃ MA MB : SimpleGraph (Fin n),
        IsPerfectMatching' (C i) MA ∧ IsPerfectMatching' (C i) MB ∧
        Disjoint MA.edgeSet MB.edgeSet ∧
        (∀ e ∈ (C i).edgeSet, e ∈ MA.edgeSet ∨ e ∈ MB.edgeSet) :=
      fun i => OneFact.exists_two_perfectMatchings_of_hamCycle hn (hcyc i)
    choose MA MB hMA hMB hdisjAB hcovAB using hsplit
    let N : Fin k → Fin 2 → SimpleGraph (Fin n) := fun i b => if b = 0 then MA i else MB i
    have hN0 : ∀ i, N i 0 = MA i := by
      intro i
      change (if (0 : Fin 2) = 0 then MA i else MB i) = MA i
      rw [if_pos rfl]
    have hN1 : ∀ i, N i 1 = MB i := by
      intro i
      change (if (1 : Fin 2) = 0 then MA i else MB i) = MB i
      rw [if_neg (by decide)]
    have hb01 : ∀ b : Fin 2, b = 0 ∨ b = 1 := by
      intro b
      have := b.isLt
      rcases Nat.eq_zero_or_pos (b : ℕ) with h | h
      · left; exact Fin.ext h
      · right; exact Fin.ext (by omega)
    have hMperf : ∀ (i : Fin k) (b : Fin 2), IsPerfectMatching' G (N i b) := by
      intro i b
      rcases hb01 b with rfl | rfl
      · rw [hN0]; exact ⟨le_trans (hMA i).1 (hle i), (hMA i).2⟩
      · rw [hN1]; exact ⟨le_trans (hMB i).1 (hle i), (hMB i).2⟩
    have hMdisj : ∀ (i i' : Fin k) (b b' : Fin 2), (i, b) ≠ (i', b') →
        Disjoint (N i b).edgeSet (N i' b').edgeSet := by
      intro i i' b b' hne
      by_cases hii : i = i'
      · subst hii
        have hbb : b ≠ b' := fun h => hne (by rw [h])
        rcases hb01 b with rfl | rfl <;> rcases hb01 b' with rfl | rfl
        · exact absurd rfl hbb
        · rw [hN0, hN1]; exact hdisjAB i
        · rw [hN1, hN0]; exact (hdisjAB i).symm
        · exact absurd rfl hbb
      · refine Disjoint.mono (SimpleGraph.edgeSet_mono ?_) (SimpleGraph.edgeSet_mono ?_)
          (hdisj i i' hii)
        · rcases hb01 b with rfl | rfl
          · rw [hN0]; exact (hMA i).1
          · rw [hN1]; exact (hMB i).1
        · rcases hb01 b' with rfl | rfl
          · rw [hN0]; exact (hMA i').1
          · rw [hN1]; exact (hMB i').1
    have hMcov : ∀ e ∈ G.edgeSet, ∃ (i : Fin k) (b : Fin 2), e ∈ (N i b).edgeSet := by
      intro e he
      obtain ⟨i, hi⟩ := hcov e he
      rcases hcovAB i e hi with h | h
      · exact ⟨i, 0, by rw [hN0]; exact h⟩
      · exact ⟨i, 1, by rw [hN1]; exact h⟩
    have hrk : r = 2 * k :=
      OneFact.eq_two_mul_of_partition_into_cycles hr C hcyc hle hdisj hcov ⟨0, hnpos⟩
    let e : Fin r ≃ Fin k × Fin 2 :=
      (finCongr hrk).trans ((finCongr (Nat.mul_comm 2 k)).trans finProdFinEquiv.symm)
    refine ⟨fun x => N (e x).1 (e x).2, ?_, ?_, ?_⟩
    · intro x; exact hMperf _ _
    · intro x y hxy
      exact hMdisj _ _ _ _ (fun h => hxy (e.injective h))
    · intro e' he'
      obtain ⟨i, b, hib⟩ := hMcov e' he'
      exact ⟨e.symm (i, b), by simpa using hib⟩

end

end Work.Deep.GKO
