import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds

set_option autoImplicit false

namespace Commons.Combinatorics.Fin

open Finset

/-! # Counting nested chains with dyadic cardinalities

A *chain* is a family of subsets of `α` indexed by the levels `0, …, m-1`
(a function `Fin m → Finset α`).  For a parameter `u : ℕ` it is *valid on
`S`* when level `0` is `S`, all levels are nested (decreasing with the index)
and level `j` has cardinality `u / 2^j`.

The main counting lemma (`chainCard_le_top`) says: if `|S| = u` then, for
every `m ≥ 1`, at most `4^u` valid chains on `S` exist.  The proof peels off
level `0`: choosing level `1` (`A ⊆ S`, `|A| = u/2`) leaves a valid chain on
`A` with parameter `u/2`, so by strong induction on `u` the number of chains
is at most `(u.choose (u/2)) · 4^(u/2) ≤ 2^u · 4^(u/2) ≤ 4^u`.

Summing over the choice of the top set `S ⊆ Fin n` with `t` elements gives
the bound `n.choose t · 4^t`. -/

section ChainCounting

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- positivity proofs derived from `2 ≤ m`, as definitions so that all
occurrences are definitionally equal -/
def chainTailPos {m : ℕ} (hm : 2 ≤ m) : 0 < m - 1 := by omega
def chainHeadPos {m : ℕ} (hm : 2 ≤ m) : 1 ≤ m := by omega
def chainNonemptyPos {m : ℕ} (hm : 2 ≤ m) : 0 < m := by omega

/-- level `0` of a chain with at least one level -/
def chainZero {m : ℕ} (hm : 0 < m) : Fin m := ⟨0, hm⟩

/-- level `1` of a chain with at least two levels -/
def chainOne {m : ℕ} (hm : 2 ≤ m) : Fin m := ⟨1, by omega⟩

/-- levels `1, 2, …, m-1` as a sub-type of the levels of a longer chain -/
def chainTailIdx {m : ℕ} (hm : 2 ≤ m) (i : Fin (m - 1)) : Fin m :=
  ⟨i.val + 1, by omega⟩

lemma chainTailIdx_one {m : ℕ} (hm : 2 ≤ m) :
    chainTailIdx hm (chainZero (chainTailPos hm)) = chainOne hm := by
  apply Fin.ext
  simp [chainTailIdx, chainZero, chainOne]

/-- predecessor of a non-zero level -/
def chainPredTail (m : ℕ) (j : Fin m) (hj : j.val ≠ 0) : Fin (m - 1) :=
  ⟨j.val - 1, by omega⟩

lemma chainTailIdx_predTail {m : ℕ} (hm : 2 ≤ m) (j : Fin m) (hj : j.val ≠ 0) :
    chainTailIdx hm (chainPredTail m j hj) = j := by
  apply Fin.ext
  simp [chainTailIdx, chainPredTail]
  omega

lemma chainPredTail_tailIdx {m : ℕ} (hm : 2 ≤ m) (i : Fin (m - 1)) :
    chainPredTail m (chainTailIdx hm i) (by simp [chainTailIdx]) = i := by
  apply Fin.ext
  simp [chainTailIdx, chainPredTail]

/-- every level is either level `0` or some tail level -/
lemma chain_eq_zero_or_tailIdx {m : ℕ} (hm : 2 ≤ m) (j : Fin m) :
    j = chainZero (chainNonemptyPos hm) ∨ ∃ i : Fin (m - 1), j = chainTailIdx hm i := by
  by_cases hj : j.val = 0
  · left
    apply Fin.ext
    exact hj
  · right
    exact ⟨chainPredTail m j hj, (chainTailIdx_predTail hm j hj).symm⟩

/-- the function with prescribed level `0` and prescribed tail (levels 1,2,…) -/
def chainWithHead {m : ℕ} (hm : 2 ≤ m) (S : Finset α) (g : Fin (m - 1) → Finset α) :
    Fin m → Finset α :=
  fun j => if hj : j.val = 0 then S else g (chainPredTail m j hj)

lemma chainWithHead_zero {m : ℕ} (hm : 2 ≤ m) (S : Finset α) (g : Fin (m - 1) → Finset α) :
    chainWithHead hm S g (chainZero (chainNonemptyPos hm)) = S := by
  simp [chainWithHead, chainZero]

lemma chainWithHead_tailIdx {m : ℕ} (hm : 2 ≤ m) (S : Finset α) (g : Fin (m - 1) → Finset α)
    (i : Fin (m - 1)) :
    chainWithHead hm S g (chainTailIdx hm i) = g i := by
  unfold chainWithHead
  rw [dif_neg (by simp [chainTailIdx] : (chainTailIdx hm i).val ≠ 0)]
  apply congrArg
  exact chainPredTail_tailIdx hm i

/-- head followed by tail is the tail at level 1 -/
lemma chainWithHead_one {m : ℕ} (hm : 2 ≤ m) (S : Finset α) (g : Fin (m - 1) → Finset α) :
    chainWithHead hm S g (chainOne hm) = g (chainZero (chainTailPos hm)) := by
  rw [← chainTailIdx_one hm]
  exact chainWithHead_tailIdx hm S g (chainZero (chainTailPos hm))

/-- tail of a function with `m` levels -/
def chainTail {m : ℕ} (hm : 2 ≤ m) (f : Fin m → Finset α) : Fin (m - 1) → Finset α :=
  fun i => f (chainTailIdx hm i)

lemma chainTail_one {m : ℕ} (hm : 2 ≤ m) (f : Fin m → Finset α) :
    chainTail hm f (chainZero (chainTailPos hm)) = f (chainOne hm) := by
  rw [← chainTailIdx_one hm]
  rfl

lemma chainTail_withHead {m : ℕ} (hm : 2 ≤ m) (S : Finset α) (g : Fin (m - 1) → Finset α) :
    chainTail hm (chainWithHead hm S g) = g := by
  funext i
  exact chainWithHead_tailIdx hm S g i

/-- `(u / 2) / 2^i = u / 2^(i+1)` -/
lemma chain_div_two_pow (u i : ℕ) : (u / 2) / 2 ^ i = u / 2 ^ (i + 1) := by
  rw [Nat.div_div_eq_div_mul]
  congr 1
  rw [pow_succ']

/-- valid chain on `S` with dyadic sizes and nesting -/
def ValidChainOn (u : ℕ) {m : ℕ} (hm : 0 < m) (S : Finset α) (f : Fin m → Finset α) : Prop :=
  f (chainZero hm) = S ∧
    (∀ j : Fin m, (f j).card = u / 2 ^ (j : ℕ)) ∧
    (∀ j k : Fin m, (j : ℕ) ≤ (k : ℕ) → f k ⊆ f j)

/-- the finite set of valid chains on `S` -/
noncomputable def chainSet (u : ℕ) {m : ℕ} (hm : 0 < m) (S : Finset α) :
    Finset (Fin m → Finset α) := by
  classical
  exact (Finset.univ : Finset (Fin m → Finset α)).filter (fun f : Fin m → Finset α =>
    ValidChainOn u hm S f)

/-- peeling level 0 preserves validity (parameter `u` becomes `u/2`) -/
lemma ValidChainOn_tail {u m : ℕ} (hm0 : 0 < m) (hm : 2 ≤ m) {S : Finset α} {f : Fin m → Finset α}
    (hf : ValidChainOn u hm0 S f) :
    ValidChainOn (u / 2) (chainTailPos hm) (f (chainOne hm)) (chainTail hm f) := by
  rcases hf with ⟨hf0, hcard, hnest⟩
  constructor
  · simpa [chainTail_one]
  · constructor
    · intro i
      have hi := hcard (chainTailIdx hm i)
      have hv : ((chainTailIdx hm i : Fin m) : ℕ) = (i : ℕ) + 1 := by simp [chainTailIdx]
      rw [hv] at hi
      dsimp [chainTail]
      rw [chain_div_two_pow]
      exact hi
    · intro i j hij
      have hsub := hnest (chainTailIdx hm i) (chainTailIdx hm j) (by
        dsimp [chainTailIdx]
        omega)
      simpa [chainTail] using hsub

/-- every level of a valid chain is a subset of the top set -/
lemma ValidChainOn_subset_top {u m : ℕ} (hm : 0 < m) {S : Finset α} {f : Fin m → Finset α}
    (hf : ValidChainOn u hm S f) (j : Fin m) : f j ⊆ S := by
  rcases hf with ⟨hf0, hcard, hnest⟩
  have hle : (chainZero hm : Fin m) ≤ j := by
    change (chainZero hm : Fin m).val ≤ (j : Fin m).val
    simp [chainZero]
  have := hnest (chainZero hm) j hle
  simpa [hf0] using this

/-- putting a head `S` on a valid tail with parameter `u/2` gives a valid chain on `S` -/
lemma ValidChainOn_withHead {u m : ℕ} (hm0 : 0 < m) (hm : 2 ≤ m) {S A : Finset α}
    (hS : S.card = u) (hAS : A ⊆ S) {g : Fin (m - 1) → Finset α}
    (hg : ValidChainOn (u / 2) (chainTailPos hm) A g) :
    ValidChainOn u hm0 S (chainWithHead hm S g) := by
  classical
  rcases hg with ⟨hg0, hgcard, hgnest⟩
  constructor
  · simp [chainWithHead, chainZero]
  · constructor
    · intro j
      rcases chain_eq_zero_or_tailIdx hm j with hzero | ⟨i, htail⟩
      · rw [hzero]
        change S.card = u / 2 ^ ((chainZero hm0 : Fin m) : ℕ)
        have hz : ((chainZero hm0 : Fin m) : ℕ) = 0 := rfl
        rw [hz]
        simpa using hS
      · rw [htail, chainWithHead_tailIdx]
        rw [show ((chainTailIdx hm i : Fin m) : ℕ) = (i : ℕ) + 1 by simp [chainTailIdx]]
        rw [← chain_div_two_pow]
        exact hgcard i
    · intro j k hjk
      rcases chain_eq_zero_or_tailIdx hm j with hzero | ⟨i, htailj⟩
      · rw [hzero]
        rw [show chainWithHead hm S g (chainZero hm0) = S by simp [chainWithHead, chainZero]]
        rcases chain_eq_zero_or_tailIdx hm k with hkzero | ⟨i', htailk⟩
        · rw [hkzero]
          rw [show chainWithHead hm S g (chainZero hm0) = S by simp [chainWithHead, chainZero]]
        · rw [htailk, chainWithHead_tailIdx]
          -- g i' ⊆ A ⊆ S
          have hgi' : g i' ⊆ A := by
            have hn := hgnest (chainZero (chainTailPos hm)) i' (by
              dsimp [chainZero, chainTailPos]
              omega)
            simpa [hg0] using hn
          exact le_trans hgi' hAS
      · -- j is a tail level; split on k
        rcases chain_eq_zero_or_tailIdx hm k with hkzero | ⟨i', htailk⟩
        · exfalso
          have hk0 : (k : ℕ) = 0 := by rw [hkzero]; rfl
          have hjge1 : 1 ≤ (j : ℕ) := by
            rw [htailj]
            simp [chainTailIdx]
          have : (j : ℕ) ≤ (k : ℕ) := hjk
          omega
        · rw [htailj, chainWithHead_tailIdx]
          rw [htailk, chainWithHead_tailIdx]
          have hj' : (j : ℕ) = (i : ℕ) + 1 := by
            rw [htailj]
            simp [chainTailIdx]
          have hk' : (k : ℕ) = (i' : ℕ) + 1 := by
            rw [htailk]
            simp [chainTailIdx]
          have hle : (i : ℕ) ≤ (i' : ℕ) := by omega
          exact hgnest i i' hle

/-- level-one set of a valid chain on `S` is a subset of `S` -/
lemma ValidChainOn_one_subset {u m : ℕ} (hm : 2 ≤ m) {S : Finset α} {f : Fin m → Finset α}
    (hf : ValidChainOn u (chainNonemptyPos hm) S f) :
    f (chainOne hm) ⊆ S := by
  exact ValidChainOn_subset_top (chainNonemptyPos hm) hf (chainOne hm)

/-- the fiber over level 1 equals the chain set over the tail with parameter `u/2` -/
lemma chainFiber_eq_tail {u m : ℕ} (hm0 : 0 < m) (hm : 2 ≤ m) (S A : Finset α)
    (hS : S.card = u) (hAS : A ⊆ S) :
    ((chainSet u hm0 S).filter (fun f : Fin m → Finset α => f (chainOne hm) = A)).card =
      (chainSet (u / 2) (chainTailPos hm) A).card := by
  classical
  refine Finset.card_bij
    (s := (chainSet u hm0 S).filter (fun f : Fin m → Finset α => f (chainOne hm) = A))
    (t := chainSet (u / 2) (chainTailPos hm) A)
    (fun f _ => chainTail hm f) ?hi ?hinj ?hsurj
  · -- image of the tail map is in the tail chain set
    intro f hf
    rcases Finset.mem_filter.mp hf with ⟨hfc, hfone⟩
    rcases Finset.mem_filter.mp hfc with ⟨_, hfvalid⟩
    refine Finset.mem_filter.mpr ?_
    constructor
    · simp
    · simpa [hfone] using ValidChainOn_tail hm0 hm hfvalid
  · -- injectivity
    intro f hf g hg htail_eq
    rcases Finset.mem_filter.mp hf with ⟨hfcs, hfone⟩
    rcases Finset.mem_filter.mp hfcs with ⟨_, hfvalid⟩
    rcases Finset.mem_filter.mp hg with ⟨hgcs, hgone⟩
    rcases Finset.mem_filter.mp hgcs with ⟨_, hgvalid⟩
    funext j
    rcases chain_eq_zero_or_tailIdx hm j with hzero | ⟨i, htail⟩
    · rw [hzero, hfvalid.1, hgvalid.1]
    · rw [htail]
      exact congrFun htail_eq i
  · -- surjectivity
    intro g hg
    rcases Finset.mem_filter.mp hg with ⟨_, hgvalid⟩
    refine ⟨chainWithHead hm S g, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ?_
      constructor
      · refine Finset.mem_filter.mpr ?_
        constructor
        · simp
        · exact ValidChainOn_withHead hm0 hm hS hAS hgvalid
      · have hg0 : g (chainZero (chainTailPos hm)) = A := hgvalid.1
        simpa [chainWithHead_one, hg0]
    · simpa using chainTail_withHead hm S g

/-- `2^u * 4^(u/2) ≤ 4^u` -/
private lemma pow_geom (u : ℕ) : (2 : ℕ) ^ u * 4 ^ (u / 2) ≤ 4 ^ u := by
  have hhalf : 2 * (u / 2) ≤ u := Nat.mul_div_le u 2
  calc
    (2 : ℕ) ^ u * 4 ^ (u / 2) ≤ (2 : ℕ) ^ u * (2 : ℕ) ^ u := by
      exact Nat.mul_le_mul_left (2 ^ u) (by
        calc 4 ^ (u / 2) = (2 ^ 2) ^ (u / 2) := by norm_num
        _ = 2 ^ (2 * (u / 2)) := by rw [pow_mul]
        _ ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num : (2 : ℕ) > 0) hhalf)
    _ = 4 ^ u := by
      calc (2 : ℕ) ^ u * (2 : ℕ) ^ u = 2 ^ (u + u) := by rw [← pow_add]
      _ = 2 ^ (2 * u) := by congr 1; omega
      _ = 4 ^ u := by
        rw [pow_mul]
        norm_num

/-- Main counting bound: for a top set `S` of cardinality `u`, there are at most
`4^u` valid chains on `S`, whatever the number of levels `m ≥ 1` is. -/
lemma chainCard_le_top (u m : ℕ) (hm : 0 < m) (S : Finset α) (hS : S.card = u) :
    (chainSet u hm S).card ≤ 4 ^ u := by
  classical
  revert m hm S hS
  refine Nat.strong_induction_on u ?_
  intro u ih m hm S hS
  by_cases hu0 : u = 0
  · -- u = 0: at most one (empty) chain
    subst hu0
    have hle : (chainSet 0 hm S).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro f hf g hg
      rcases Finset.mem_filter.mp hf with ⟨hfcs, hfvalid⟩
      rcases Finset.mem_filter.mp hg with ⟨hgcs, hgvalid⟩
      funext j
      have hfc : (f j).card = 0 := by simpa using hfvalid.2.1 j
      have hgc : (g j).card = 0 := by simpa using hgvalid.2.1 j
      rw [Finset.card_eq_zero.mp hfc, Finset.card_eq_zero.mp hgc]
    have h1 : 1 ≤ 4 ^ 0 := by simp
    exact le_trans hle h1
  · -- u ≥ 1
    have hu : 0 < u := Nat.pos_of_ne_zero hu0
    by_cases hm1 : m = 1
    · -- a single level: exactly one chain
      subst m
      have hle : (chainSet u hm S).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro f hf g hg
        rcases Finset.mem_filter.mp hf with ⟨hfcs, hfvalid⟩
        rcases Finset.mem_filter.mp hg with ⟨hgcs, hgvalid⟩
        funext j
        have hj : j = chainZero hm := by
          apply Fin.ext
          omega
        rw [hj, hfvalid.1, hgvalid.1]
      have h1 : 1 ≤ 4 ^ u := Nat.succ_le_of_lt (pow_pos (by norm_num : 0 < (4 : ℕ)) u)
      exact le_trans hle h1
    · -- at least two levels: peel level 0 off
      have hm2 : 2 ≤ m := by omega
      let B : Finset (Finset α) := Finset.powersetCard (u / 2) S
      have hdecomp : (chainSet u hm S).card =
          ∑ A ∈ B, ((chainSet u hm S).filter
            (fun f : Fin m → Finset α => f (chainOne hm2) = A)).card := by
        refine (Finset.card_eq_sum_card_fiberwise (s := chainSet u hm S)
          (t := B) (f := fun f : Fin m → Finset α => f (chainOne hm2))) ?_
        intro f hf
        rcases Finset.mem_filter.mp hf with ⟨hfcs, hfvalid⟩
        refine Finset.mem_powersetCard.mpr ?_
        constructor
        · exact ValidChainOn_subset_top hm hfvalid (chainOne hm2)
        · have hc := hfvalid.2.1 (chainOne hm2)
          have hone : ((chainOne hm2 : Fin m) : ℕ) = 1 := by simp [chainOne]
          rw [hone] at hc
          simpa using hc
      have hfib : ∀ A ∈ B, ((chainSet u hm S).filter
          (fun f : Fin m → Finset α => f (chainOne hm2) = A)).card ≤ 4 ^ (u / 2) := by
        intro A hA
        have hAS : A ⊆ S := (Finset.mem_powersetCard.mp hA).1
        have hAc : A.card = u / 2 := (Finset.mem_powersetCard.mp hA).2
        rw [chainFiber_eq_tail hm hm2 S A hS hAS]
        have hlt : u / 2 < u := Nat.div_lt_self hu (by norm_num : 1 < 2)
        exact ih (u / 2) hlt (m - 1) (chainTailPos hm2) A hAc
      calc
        (chainSet u hm S).card
            = ∑ A ∈ B, ((chainSet u hm S).filter
                (fun f : Fin m → Finset α => f (chainOne hm2) = A)).card := hdecomp
        _ ≤ ∑ A ∈ B, 4 ^ (u / 2) := Finset.sum_le_sum (by intro A hA; exact hfib A hA)
        _ = B.card * 4 ^ (u / 2) := by simp [Finset.sum_const]
        _ = S.card.choose (u / 2) * 4 ^ (u / 2) := by simp [B, Finset.card_powersetCard]
        _ = u.choose (u / 2) * 4 ^ (u / 2) := by rw [hS]
        _ ≤ (2 : ℕ) ^ u * 4 ^ (u / 2) := by
          exact Nat.mul_le_mul_right _ (Nat.choose_le_two_pow u (u / 2))
        _ ≤ 4 ^ u := pow_geom u

end ChainCounting

theorem nested_chain_card_bound {n t : ℕ} (ht : t ≤ n) :
    (((Finset.univ : Finset (Fin (n + 1) → Finset (Fin n))).filter
        (fun f => (∀ j : Fin (n + 1), (f j).card = t / 2 ^ (j : ℕ)) ∧
                  ∀ j k : Fin (n + 1), (j : ℕ) ≤ (k : ℕ) → f k ⊆ f j)).card : ℝ)
      ≤ (n.choose t : ℝ) * (4 : ℝ) ^ t := by
  classical
  -- the set of all valid chains (no fixed top set)
  let A : Finset (Fin (n + 1) → Finset (Fin n)) :=
    (Finset.univ : Finset (Fin (n + 1) → Finset (Fin n))).filter
      (fun f : Fin (n + 1) → Finset (Fin n) =>
        (∀ j : Fin (n + 1), (f j).card = t / 2 ^ (j : ℕ)) ∧
        (∀ j k : Fin (n + 1), (j : ℕ) ≤ (k : ℕ) → f k ⊆ f j))
  change (((A : Finset (Fin (n + 1) → Finset (Fin n))).card : ℝ) ≤
    (n.choose t : ℝ) * (4 : ℝ) ^ t)
  let hn0 : 0 < n + 1 := by omega
  -- the possible top sets: `t`-element subsets of `Fin n`
  let B : Finset (Finset (Fin n)) := Finset.powersetCard t (Finset.univ : Finset (Fin n))
  -- decompose by the top set `S = f 0`
  have hdecomp : A.card = ∑ S ∈ B,
      (A.filter (fun f : Fin (n + 1) → Finset (Fin n) => f (chainZero (m := n + 1) hn0) = S)).card := by
    refine (Finset.card_eq_sum_card_fiberwise (s := A)
      (t := B) (f := fun f : Fin (n + 1) → Finset (Fin n) => f (chainZero (m := n + 1) hn0))) ?_
    intro f hf
    rcases Finset.mem_filter.mp hf with ⟨hfcs, hfcond⟩
    have hcard0 : (f (chainZero (m := n + 1) hn0)).card = t := by
      have hc := hfcond.1 (chainZero (m := n + 1) hn0)
      have hz : ((chainZero (m := n + 1) hn0 : Fin (n + 1)) : ℕ) = 0 := rfl
      rw [hz] at hc
      simpa using hc
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard0⟩
  -- for each top set S, the number of chains on S is at most 4^t
  have hfib : ∀ S ∈ B, (A.filter (fun f : Fin (n + 1) → Finset (Fin n) =>
      f (chainZero (m := n + 1) hn0) = S)).card ≤ 4 ^ t := by
    intro S hS
    have hSc : S.card = t := (Finset.mem_powersetCard.mp hS).2
    have heq : (A.filter (fun f : Fin (n + 1) → Finset (Fin n) =>
        f (chainZero (m := n + 1) hn0) = S)) =
        (chainSet (α := Fin n) t (m := n + 1) hn0 S) := by
      ext f
      constructor
      · intro hf
        rcases Finset.mem_filter.mp hf with ⟨hfA, hf0⟩
        rcases Finset.mem_filter.mp hfA with ⟨hfcs, hfcond⟩
        refine Finset.mem_filter.mpr ?_
        constructor
        · simp
        · exact ⟨hf0, hfcond⟩
      · intro hf
        rcases Finset.mem_filter.mp hf with ⟨hfcs, hf0cond⟩
        refine Finset.mem_filter.mpr ?_
        constructor
        · refine Finset.mem_filter.mpr ?_
          constructor
          · simp
          · exact hf0cond.2
        · exact hf0cond.1
    rw [heq]
    exact chainCard_le_top (α := Fin n) t (n + 1) hn0 S hSc
  -- assemble
  have hnat : A.card ≤ n.choose t * 4 ^ t := by
    calc
      A.card = ∑ S ∈ B,
          (A.filter (fun f : Fin (n + 1) → Finset (Fin n) =>
            f (chainZero (m := n + 1) hn0) = S)).card := hdecomp
      _ ≤ ∑ S ∈ B, 4 ^ t := Finset.sum_le_sum (by intro S hS; exact hfib S hS)
      _ = B.card * 4 ^ t := by simp [Finset.sum_const]
      _ = ((Finset.univ : Finset (Fin n)).card).choose t * 4 ^ t := by
        simp [B, Finset.card_powersetCard]
      _ = n.choose t * 4 ^ t := by simp
  exact_mod_cast hnat

end Commons.Combinatorics.Fin