import Submission.EFL.BigEdges
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Counting edges of a linear hypergraph by pairs of vertices

In a *linear* hypergraph two distinct edges share at most one vertex, hence a
pair of vertices `{x, y}` lies in at most one edge.  Counting ordered pairs
of vertices inside edges therefore yields the classical double-counting bound
```
    ∑_{e ∈ 𝓗} |e| · (|e| − 1)  ≤  n · (n − 1)
```
for a linear hypergraph on `n` vertices, and consequently the bound
`# { e : |e| ≥ s } ≤ n(n−1) / (s(s−1))` on the number of edges of size at
least `s`.  These estimates are used throughout the proof of the
Erdős–Faber–Lovász conjecture (e.g. bounding the number of FPP-extremal or
huge edges of a linear hypergraph).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

/-- The vertices of a set `e ⊆ Fin n`, as a finset. -/
def verts {n : ℕ} (e : Set (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v : Fin n => v ∈ e)

/-- The size (number of vertices) of a set `e ⊆ Fin n`. -/
def edgeSize {n : ℕ} (e : Set (Fin n)) : ℕ :=
  (verts e).card

/-- Membership in `verts e` is membership in `e`. -/
@[simp]
theorem mem_verts {n : ℕ} (e : Set (Fin n)) (v : Fin n) : v ∈ verts e ↔ v ∈ e := by
  simp [verts]

/-- The size of an edge equals its cardinality. -/
theorem edgeSize_eq_ncard {n : ℕ} (e : Set (Fin n)) : edgeSize e = e.ncard := by
  classical
  unfold edgeSize verts
  let f : Finset (Fin n) := Finset.univ.filter (fun v : Fin n => v ∈ e)
  have hs : ((f : Finset (Fin n)) : Set (Fin n)).ncard = f.card := by
    simp
  have hcov : ((f : Finset (Fin n)) : Set (Fin n)) = e := by
    ext v
    simp [f]
  calc
    f.card = ((f : Finset (Fin n)) : Set (Fin n)).ncard := hs.symm
    _ = e.ncard := by rw [hcov]

/-- The ordered pairs `(x, y)` of distinct vertices inside an edge `e`. -/
def edgePairs {n : ℕ} (e : Set (Fin n)) : Finset (Fin n × Fin n) := by
  classical
  exact ((verts e) ×ˢ (verts e)).filter (fun p : Fin n × Fin n => p.1 ≠ p.2)

/-- Membership in `edgePairs e`. -/
theorem mem_edgePairs {n : ℕ} (e : Set (Fin n)) (p : Fin n × Fin n) :
    p ∈ edgePairs e ↔ p.1 ∈ e ∧ p.2 ∈ e ∧ p.1 ≠ p.2 := by
  classical
  simp [edgePairs, Finset.mem_product]
  tauto

/-- The ordered pairs of distinct vertices of `Fin n`. -/
def distinctPairs (n : ℕ) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2)

/-- The number of ordered pairs of distinct elements of an `n`-element set is `n(n-1)`. -/
theorem card_distinctPairs (n : ℕ) : (distinctPairs n).card = n * (n - 1) := by
  classical
  let U : Finset (Fin n × Fin n) := Finset.univ
  have hdiag_card : (U.filter (fun p : Fin n × Fin n => p.1 = p.2)).card = n := by
    have hdiag : U.filter (fun p : Fin n × Fin n => p.1 = p.2) =
        (Finset.univ : Finset (Fin n)).image (fun v : Fin n => (v, v)) := by
      ext p
      cases p with
      | mk a b =>
        simp [U]
    rw [hdiag]
    have hinj : Function.Injective (fun v : Fin n => (v, v)) := by
      intro a b h
      exact congrArg Prod.fst h
    rw [Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin n)))
      (f := fun v : Fin n => (v, v)) hinj]
    simp
  have hsum := Finset.card_filter_add_card_filter_not
    (s := U) (p := fun p : Fin n × Fin n => p.1 ≠ p.2)
  have hneg : U.filter (fun p : Fin n × Fin n => ¬ p.1 ≠ p.2) =
      U.filter (fun p : Fin n × Fin n => p.1 = p.2) := by
    ext p
    by_cases h : p.1 = p.2 <;> simp [h, U]
  have hmain : (distinctPairs n).card + n = n * n := by
    unfold distinctPairs
    rw [hneg] at hsum
    rw [hdiag_card] at hsum
    exact hsum.trans (by simp [U])
  have hsub : (distinctPairs n).card = n * n - n := by omega
  rw [hsub]
  rw [Nat.mul_sub_left_distrib, mul_one]

/-- If two distinct edges of a linear hypergraph both contain the same ordered
pair of distinct vertices, then they are equal; equivalently their edge-pair
sets are disjoint. -/
theorem edgePairs_disjoint_of_ne {n : ℕ} {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    {e₁ e₂ : 𝓗} (hne : e₁ ≠ e₂) :
    Disjoint (edgePairs (e₁ : Set (Fin n))) (edgePairs (e₂ : Set (Fin n))) := by
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  have h₁ := (mem_edgePairs (e₁ : Set (Fin n)) p).1 hp₁
  have h₂ := (mem_edgePairs (e₂ : Set (Fin n)) p).1 hp₂
  apply hne
  apply Subtype.ext
  exact IsLinear.eq_of_mem_pair hlin e₁.2 e₂.2 h₁.2.2 h₁.1 h₁.2.1 h₂.1 h₂.2.1

/-- The number of ordered pairs of distinct vertices inside an edge `e` of
size `edgeSize e` is `edgeSize e · (edgeSize e − 1)`. -/
theorem card_edgePairs {n : ℕ} (e : Set (Fin n)) :
    (edgePairs e).card = edgeSize e * (edgeSize e - 1) := by
  classical
  let V : Finset (Fin n) := verts e
  have hcardV : V.card = edgeSize e := by simp [V, edgeSize]
  have hprod : (V ×ˢ V).card = edgeSize e * edgeSize e := by
    exact (Finset.card_product V V).trans (by rw [hcardV])
  have hdiag : (V ×ˢ V).filter (fun p : Fin n × Fin n => p.1 = p.2) =
      V.image (fun v : Fin n => (v, v)) := by
    ext p
    cases p with
    | mk a b =>
      aesop
  have hdiag_card : ((V ×ˢ V).filter (fun p : Fin n × Fin n => p.1 = p.2)).card =
      edgeSize e := by
    rw [hdiag]
    have hinj : Function.Injective (fun v : Fin n => (v, v)) := by
      intro a b h
      exact congrArg Prod.fst h
    rw [Finset.card_image_of_injective (s := V) (f := fun v : Fin n => (v, v)) hinj]
    exact hcardV
  have hsum := Finset.card_filter_add_card_filter_not
    (s := V ×ˢ V) (p := fun p : Fin n × Fin n => p.1 ≠ p.2)
  have hneg : (V ×ˢ V).filter (fun p : Fin n × Fin n => ¬ p.1 ≠ p.2) =
      (V ×ˢ V).filter (fun p : Fin n × Fin n => p.1 = p.2) := by
    ext p
    by_cases h : p.1 = p.2 <;> simp [h]
  have hEq : (edgePairs e).card + edgeSize e = edgeSize e * edgeSize e := by
    unfold edgePairs
    rw [hneg] at hsum
    rw [hdiag_card] at hsum
    exact hsum.trans (by simpa [hcardV, Nat.mul_comm])
  have hsub' : (edgePairs e).card = edgeSize e * edgeSize e - edgeSize e := by omega
  rw [hsub']
  rw [Nat.mul_sub_left_distrib, mul_one]

/-- For a linear hypergraph on `n` vertices, the sum over all edges of the
number of ordered pairs of distinct vertices inside the edge is at most
`n(n-1)` (every such pair lies in at most one edge). -/
theorem sum_edgePairs_card_le {n : ℕ} {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (hlin : 𝓗.IsLinear) :
    ((Finset.univ : Finset 𝓗).sum fun e : 𝓗 => (edgePairs (e : Set (Fin n))).card) ≤
      n * (n - 1) := by
  classical
  let f : 𝓗 → Finset (Fin n × Fin n) := fun e => edgePairs (e : Set (Fin n))
  have hpd : ((Finset.univ : Finset 𝓗) : Set 𝓗).PairwiseDisjoint f := by
    intro e₁ _ e₂ _ hne
    exact edgePairs_disjoint_of_ne hlin hne
  let D : Finset (Fin n × Fin n) := (Finset.univ : Finset 𝓗).disjiUnion f hpd
  have hDcard : D.card = (Finset.univ : Finset 𝓗).sum (fun e => (f e).card) :=
    Finset.card_disjiUnion (Finset.univ : Finset 𝓗) f hpd
  have hsub : D ⊆ distinctPairs n := by
    intro p hp
    rw [Finset.mem_disjiUnion] at hp
    rcases hp with ⟨e, _he, hp⟩
    rw [distinctPairs, Finset.mem_filter]
    exact ⟨Finset.mem_univ p, (mem_edgePairs (e : Set (Fin n)) p).1 hp |>.2.2⟩
  have hle : D.card ≤ (distinctPairs n).card := Finset.card_le_card hsub
  rw [hDcard] at hle
  rw [card_distinctPairs] at hle
  dsimp [f] at hle ⊢
  exact hle

/-- For a linear hypergraph on `n` vertices,
`∑_{e} |e|·(|e|−1) ≤ n(n−1)`. -/
theorem sum_edgeSize_mul_sub_le {n : ℕ} {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (hlin : 𝓗.IsLinear) :
    ((Finset.univ : Finset 𝓗).sum fun e : 𝓗 =>
      edgeSize (e : Set (Fin n)) * (edgeSize (e : Set (Fin n)) - 1)) ≤
      n * (n - 1) := by
  classical
  have h := sum_edgePairs_card_le (𝓗 := 𝓗) hlin
  have hcongr : (Finset.univ : Finset 𝓗).sum (fun e : 𝓗 =>
        (edgePairs (e : Set (Fin n))).card) =
      (Finset.univ : Finset 𝓗).sum (fun e : 𝓗 =>
        edgeSize (e : Set (Fin n)) * (edgeSize (e : Set (Fin n)) - 1)) := by
    refine Finset.sum_congr rfl ?_
    intro e _he
    exact card_edgePairs (e : Set (Fin n))
  rw [hcongr] at h
  exact h

/-- In a linear hypergraph on `n` vertices, if `k` edges have size at least
`s`, then `k · s(s−1) ≤ n(n−1)`. -/
theorem card_edges_size_ge_mul_le {n : ℕ} {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (hlin : 𝓗.IsLinear) (s : ℕ) :
    (((Finset.univ : Finset 𝓗).filter (fun e : 𝓗 => s ≤ edgeSize (e : Set (Fin n)))).card) *
        (s * (s - 1)) ≤ n * (n - 1) := by
  classical
  let B : Finset 𝓗 := (Finset.univ : Finset 𝓗).filter (fun e : 𝓗 =>
    s ≤ edgeSize (e : Set (Fin n)))
  let f : 𝓗 → ℕ := fun e => edgeSize (e : Set (Fin n)) * (edgeSize (e : Set (Fin n)) - 1)
  have hmain : (Finset.univ : Finset 𝓗).sum f ≤ n * (n - 1) := by
    simpa [f] using sum_edgeSize_mul_sub_le (𝓗 := 𝓗) hlin
  -- split the sum into B-part and complement
  have hBle : B.sum f ≤ (Finset.univ : Finset 𝓗).sum f := by
    let C : Finset 𝓗 := (Finset.univ : Finset 𝓗).filter (fun e : 𝓗 =>
      ¬ s ≤ edgeSize (e : Set (Fin n)))
    have hunion : B ∪ C = (Finset.univ : Finset 𝓗) := by
      ext e
      constructor
      · intro _he
        simp
      · intro _he
        rw [Finset.mem_union]
        by_cases h : s ≤ edgeSize (e : Set (Fin n))
        · left
          dsimp [B]
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ e, h⟩
        · right
          dsimp [C]
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ e, h⟩
    have hdisj : Disjoint B C := by
      rw [Finset.disjoint_left]
      intro e heB heC
      exact (Finset.mem_filter.mp heC).2 (Finset.mem_filter.mp heB).2
    have hsplit : B.sum f + C.sum f = (Finset.univ : Finset 𝓗).sum f := by
      rw [← hunion, Finset.sum_union hdisj]
    calc
      B.sum f ≤ B.sum f + C.sum f := Nat.le_add_right _ _
      _ = (Finset.univ : Finset 𝓗).sum f := hsplit
  have hBsum : B.card * (s * (s - 1)) ≤ B.sum f := by
    have hterm : ∀ e ∈ B, s * (s - 1) ≤ f e := by
      intro e heB
      have he : s ≤ edgeSize (e : Set (Fin n)) := (Finset.mem_filter.mp heB).2
      by_cases h1 : s ≤ 1
      · have hs0 : s * (s - 1) = 0 := by
          interval_cases s <;> simp
        rw [hs0]
        exact Nat.zero_le _
      · have hs2 : 2 ≤ s := by omega
        have hmge : 2 ≤ edgeSize (e : Set (Fin n)) := le_trans hs2 he
        have hge1 : s - 1 ≤ edgeSize (e : Set (Fin n)) - 1 := Nat.sub_le_sub_right he 1
        have hmul : s * (s - 1) ≤ edgeSize (e : Set (Fin n)) *
            (edgeSize (e : Set (Fin n)) - 1) := Nat.mul_le_mul he hge1
        simpa [f] using hmul
    calc
      B.card * (s * (s - 1)) = B.sum fun _ : 𝓗 => s * (s - 1) := by
        rw [Finset.sum_const]
        simp
      _ ≤ B.sum f := by
        exact Finset.sum_le_sum hterm
  exact (hBsum.trans hBle).trans hmain

/-- In a linear hypergraph on `n` vertices the number of edges of size at
least `s ≥ 2` is at most `n(n−1) / (s(s−1))`. -/
theorem card_edges_size_ge_le {n s : ℕ} {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (hlin : 𝓗.IsLinear) (hs : 2 ≤ s) :
    ((Finset.univ : Finset 𝓗).filter (fun e : 𝓗 => s ≤ edgeSize (e : Set (Fin n)))).card ≤
      (n * (n - 1)) / (s * (s - 1)) := by
  classical
  have hmul := card_edges_size_ge_mul_le (𝓗 := 𝓗) hlin s
  have hpos : 0 < s * (s - 1) := by
    have hs1 : 1 ≤ s - 1 := by omega
    exact Nat.mul_pos (by omega : 0 < s) hs1
  exact (Nat.le_div_iff_mul_le hpos).2 hmul

/-- If two distinct edges of a family `s` of sets share at most one vertex,
then their edge-pair sets are disjoint. -/
theorem edgePairs_disjoint_of_subsingleton_inter {n : ℕ} {s : Finset (Set (Fin n))}
    (hsub : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ s → e₂ ∈ s → e₁ ≠ e₂ →
      (e₁ ∩ e₂ : Set (Fin n)).Subsingleton) {e₁ e₂ : Set (Fin n)}
    (he₁ : e₁ ∈ s) (he₂ : e₂ ∈ s) (hne : e₁ ≠ e₂) :
    Disjoint (edgePairs e₁) (edgePairs e₂) := by
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  have h₁ := (mem_edgePairs e₁ p).1 hp₁
  have h₂ := (mem_edgePairs e₂ p).1 hp₂
  exact h₁.2.2 (hsub he₁ he₂ hne ⟨h₁.1, h₂.1⟩ ⟨h₁.2.1, h₂.2.1⟩)

/-- For a family `s` of sets on `Fin n` any two of which share at most one
vertex, the sum over `e ∈ s` of the ordered distinct-vertex pairs inside `e`
is at most `n(n-1)`. -/
theorem sum_edgePairs_card_le_on {n : ℕ} (s : Finset (Set (Fin n)))
    (hsub : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ s → e₂ ∈ s → e₁ ≠ e₂ →
      (e₁ ∩ e₂ : Set (Fin n)).Subsingleton) :
    (s.sum fun e : Set (Fin n) => (edgePairs e).card) ≤ n * (n - 1) := by
  classical
  let f : Set (Fin n) → Finset (Fin n × Fin n) := fun e => edgePairs e
  have hpd : (s : Set (Set (Fin n))).PairwiseDisjoint f := by
    intro e₁ he₁ e₂ he₂ hne
    exact edgePairs_disjoint_of_subsingleton_inter (s := s) hsub he₁ he₂ hne
  let D : Finset (Fin n × Fin n) := s.disjiUnion f hpd
  have hDcard : D.card = s.sum (fun e => (f e).card) := Finset.card_disjiUnion s f hpd
  have hsubD : D ⊆ distinctPairs n := by
    intro p hp
    rw [Finset.mem_disjiUnion] at hp
    rcases hp with ⟨e, _he, hp⟩
    rw [distinctPairs, Finset.mem_filter]
    exact ⟨Finset.mem_univ p, (mem_edgePairs e p).1 hp |>.2.2⟩
  have hle : D.card ≤ (distinctPairs n).card := Finset.card_le_card hsubD
  rw [hDcard] at hle
  rw [card_distinctPairs] at hle
  simpa [f] using hle

/-- For a family `s` of sets on `Fin n` any two of which share at most one
vertex, `∑_{e ∈ s} |e|·(|e|−1) ≤ n(n−1)`. -/
theorem sum_edgeSize_mul_sub_le_on {n : ℕ} (s : Finset (Set (Fin n)))
    (hsub : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ s → e₂ ∈ s → e₁ ≠ e₂ →
      (e₁ ∩ e₂ : Set (Fin n)).Subsingleton) :
    (s.sum fun e : Set (Fin n) => edgeSize e * (edgeSize e - 1)) ≤ n * (n - 1) := by
  classical
  have h := sum_edgePairs_card_le_on s hsub
  have hcongr : s.sum (fun e : Set (Fin n) => (edgePairs e).card) =
      s.sum (fun e : Set (Fin n) => edgeSize e * (edgeSize e - 1)) := by
    refine Finset.sum_congr rfl ?_
    intro e _he
    exact card_edgePairs e
  simpa [hcongr] using h
