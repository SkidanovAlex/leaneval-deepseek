import Mathlib

open scoped BigOperators

set_option autoImplicit false

/-!
# Edges of the standard simplex

The symmetrisation argument of Kaluba–Kielak–Nowak (Method I/II) is organised around
the edges `E_n` of the standard `(n-1)`-simplex: two edges either coincide, are
*adjacent* (share exactly one vertex) or are *opposite* (are disjoint).  This file
provides the combinatorial framework: the type `Edge m` of edges, the action of the
symmetric group of the vertex set on it, the adjacency/opposite relations, and the
"configuration embeddings" (`Fin 2 ↪ Fin m`, `Fin 3 ↪ Fin m`, `Fin 4 ↪ Fin m`) which
turn transitivity statements into the multiple transitivity of the symmetric group.

An edge is represented by its two vertices in increasing order.
-/

namespace Submission.RouteB

/-- An edge of the standard `(m-1)`-simplex: an unordered pair of distinct vertices
of `Fin m`, represented by the ordered pair in increasing order. -/
abbrev Edge (m : ℕ) := {p : Fin m × Fin m // p.1 < p.2}

namespace Edge

variable {m : ℕ}

/-- The two vertices of an edge, as a finset. -/
def toFinset (p : Edge m) : Finset (Fin m) := {p.1.1, p.1.2}

@[simp] lemma mem_toFinset {p : Edge m} {k : Fin m} :
    k ∈ p.toFinset ↔ k = p.1.1 ∨ k = p.1.2 := by
  simp [toFinset]

lemma toFinset_card (p : Edge m) : p.toFinset.card = 2 := by
  have h : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  simp [toFinset, h]

lemma fst_mem_toFinset (p : Edge m) : p.1.1 ∈ p.toFinset := by simp

lemma snd_mem_toFinset (p : Edge m) : p.1.2 ∈ p.toFinset := by simp

lemma toFinset_injective : Function.Injective (toFinset : Edge m → Finset (Fin m)) := by
  intro p q h
  have h1 : p.1.1 ∈ q.toFinset := by rw [← h]; exact fst_mem_toFinset p
  have h2 : p.1.2 ∈ q.toFinset := by rw [← h]; exact snd_mem_toFinset p
  rw [mem_toFinset] at h1 h2
  have hp : p.1.1 < p.1.2 := p.2
  have hq : q.1.1 < q.1.2 := q.2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) (ne_of_lt hp)
  · exact Subtype.ext (Prod.ext h1 h2)
  · exact absurd (by rw [h2, h1]; exact hq) (not_lt_of_gt hp)
  · exact absurd (h1.trans h2.symm) (ne_of_lt hp)

lemma toFinset_inj {p q : Edge m} : p.toFinset = q.toFinset ↔ p = q :=
  ⟨fun h => toFinset_injective h, fun h => h ▸ rfl⟩

lemma eq_iff {p q : Edge m} : p = q ↔ p.1.1 = q.1.1 ∧ p.1.2 = q.1.2 :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun h => Subtype.ext (Prod.ext h.1 h.2)⟩

/-- The permutation action on edges: apply the permutation and re-sort. -/
def edgeMap (σ : Equiv.Perm (Fin m)) (p : Edge m) : Edge m :=
  if h : σ p.1.1 < σ p.1.2 then ⟨(σ p.1.1, σ p.1.2), h⟩
  else ⟨(σ p.1.2, σ p.1.1), by
    refine lt_of_le_of_ne (le_of_not_gt h) fun hh => ?_
    exact absurd (σ.injective hh.symm) (ne_of_lt p.2)⟩

lemma toFinset_edgeMap (σ : Equiv.Perm (Fin m)) (p : Edge m) :
    (edgeMap σ p).toFinset = p.toFinset.image σ := by
  by_cases h : σ p.1.1 < σ p.1.2
  · have hne : σ p.1.1 ≠ σ p.1.2 := ne_of_lt h
    simp [edgeMap, h, toFinset, hne]
  · have hne : σ p.1.1 ≠ σ p.1.2 := fun hh => absurd (σ.injective hh) (ne_of_lt p.2)
    simp [edgeMap, h, toFinset, hne, Finset.pair_comm]

@[simp] lemma edgeMap_one (p : Edge m) : edgeMap 1 p = p := by
  apply toFinset_injective
  rw [toFinset_edgeMap]
  simp

lemma edgeMap_mul (σ τ : Equiv.Perm (Fin m)) (p : Edge m) :
    edgeMap (σ * τ) p = edgeMap σ (edgeMap τ p) := by
  apply toFinset_injective
  rw [toFinset_edgeMap, toFinset_edgeMap, toFinset_edgeMap]
  simp [Finset.image_image, Function.comp_def]

instance : SMul (Equiv.Perm (Fin m)) (Edge m) := ⟨edgeMap⟩

instance : MulAction (Equiv.Perm (Fin m)) (Edge m) where
  one_smul := edgeMap_one
  mul_smul := edgeMap_mul

@[simp] lemma smul_def (σ : Equiv.Perm (Fin m)) (p : Edge m) : σ • p = edgeMap σ p := rfl

@[simp] lemma toFinset_smul (σ : Equiv.Perm (Fin m)) (p : Edge m) :
    (σ • p).toFinset = p.toFinset.image σ := toFinset_edgeMap σ p

/-- Two edges are *adjacent* if they share exactly one vertex. -/
def Adj (p q : Edge m) : Prop := p ≠ q ∧ ¬ Disjoint p.toFinset q.toFinset

/-- Two edges are *opposite* if they are disjoint. -/
def Op (p q : Edge m) : Prop := Disjoint p.toFinset q.toFinset

/-- Decidability of the adjacency relation. -/
instance instDecidableAdj (p q : Edge m) : Decidable (Adj p q) :=
  decidable_of_iff (p ≠ q ∧ (p.1.1 = q.1.1 ∨ p.1.1 = q.1.2 ∨ p.1.2 = q.1.1 ∨
    p.1.2 = q.1.2)) (by
    rw [Adj]
    constructor
    · rintro ⟨hne, h⟩
      refine ⟨hne, fun hd => ?_⟩
      have h' := Finset.disjoint_left.mp hd
      rcases h with h | h | h | h
      · exact h' (by rw [mem_toFinset]; exact Or.inl h.symm)
          (by rw [mem_toFinset]; exact Or.inl rfl)
      · exact h' (by rw [mem_toFinset]; exact Or.inl h.symm)
          (by rw [mem_toFinset]; exact Or.inr rfl)
      · exact h' (by rw [mem_toFinset]; exact Or.inr h.symm)
          (by rw [mem_toFinset]; exact Or.inl rfl)
      · exact h' (by rw [mem_toFinset]; exact Or.inr h.symm)
          (by rw [mem_toFinset]; exact Or.inr rfl)
    · rintro ⟨hne, hnd⟩
      refine ⟨hne, ?_⟩
      obtain ⟨k, hk1, hk2⟩ := Finset.not_disjoint_iff.mp hnd
      rw [mem_toFinset] at hk1 hk2
      rcases hk1 with hk1 | hk1 <;> rcases hk2 with hk2 | hk2
      · exact Or.inl (hk1.symm.trans hk2)
      · exact Or.inr (Or.inl (hk1.symm.trans hk2))
      · exact Or.inr (Or.inr (Or.inl (hk1.symm.trans hk2)))
      · exact Or.inr (Or.inr (Or.inr (hk1.symm.trans hk2))))

/-- Decidability of the opposite relation. -/
instance instDecidableOp (p q : Edge m) : Decidable (Op p q) :=
  decidable_of_iff (p.1.1 ≠ q.1.1 ∧ p.1.1 ≠ q.1.2 ∧ p.1.2 ≠ q.1.1 ∧ p.1.2 ≠ q.1.2) (by
    rw [Op, Finset.disjoint_left]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩ k hk hk2
      rw [mem_toFinset] at hk hk2
      rcases hk with rfl | rfl <;> rcases hk2 with hh | hh
      · exact h1 hh
      · exact h2 hh
      · exact h3 hh
      · exact h4 hh
    · intro h
      refine ⟨fun hh => ?_, fun hh => ?_, fun hh => ?_, fun hh => ?_⟩
      · exact h (by rw [mem_toFinset]; exact Or.inl rfl)
          (by rw [mem_toFinset]; exact Or.inl hh)
      · exact h (by rw [mem_toFinset]; exact Or.inl rfl)
          (by rw [mem_toFinset]; exact Or.inr hh)
      · exact h (by rw [mem_toFinset]; exact Or.inr rfl)
          (by rw [mem_toFinset]; exact Or.inl hh)
      · exact h (by rw [mem_toFinset]; exact Or.inr rfl)
          (by rw [mem_toFinset]; exact Or.inr hh))

lemma op_irrefl (p : Edge m) : ¬ Op p p := by
  intro h
  have h2 : p.toFinset = ∅ := by
    simpa [Finset.inter_self] using Finset.disjoint_iff_inter_eq_empty.mp h
  have hmem : p.1.1 ∈ (∅ : Finset (Fin m)) := by rw [← h2]; exact fst_mem_toFinset p
  exact Finset.notMem_empty _ hmem

lemma op_comm {p q : Edge m} : Op p q → Op q p := fun h => disjoint_comm.mp h

lemma op_ne {p q : Edge m} (h : Op p q) : p ≠ q := fun hpq => op_irrefl p (hpq ▸ h)

lemma adj_comm {p q : Edge m} : Adj p q → Adj q p := fun h =>
  ⟨h.1.symm, fun hd => h.2 (disjoint_comm.mpr hd)⟩

lemma adj_ne {p q : Edge m} (h : Adj p q) : p ≠ q := h.1

lemma trichotomy {p q : Edge m} (h : p ≠ q) : Adj p q ∨ Op p q := by
  by_cases hd : Disjoint p.toFinset q.toFinset
  · exact Or.inr hd
  · exact Or.inl ⟨h, hd⟩

lemma smul_eq_iff (σ : Equiv.Perm (Fin m)) (p q : Edge m) : (σ • p = σ • q) ↔ (p = q) := by
  constructor
  · intro h
    have h2 := congrArg (fun e : Edge m => (σ⁻¹) • e) h
    rw [← mul_smul, inv_mul_cancel, one_smul, ← mul_smul, inv_mul_cancel, one_smul] at h2
    exact h2
  · intro h
    rw [h]

lemma smul_disjoint_iff (σ : Equiv.Perm (Fin m)) (p q : Edge m) :
    Disjoint (σ • p).toFinset (σ • q).toFinset ↔ Disjoint p.toFinset q.toFinset := by
  have hmap : ((σ • p).toFinset ∩ (σ • q).toFinset)
      = (p.toFinset ∩ q.toFinset).image σ := by
    rw [toFinset_smul, toFinset_smul, Finset.image_inter _ _ σ.injective]
  rw [Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_iff_inter_eq_empty, hmap,
    Finset.image_eq_empty]

lemma smul_adj (σ : Equiv.Perm (Fin m)) (p q : Edge m) : Adj (σ • p) (σ • q) ↔ Adj p q := by
  rw [Adj, Adj]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun hpq => h1 ((smul_eq_iff σ p q).mpr hpq),
      fun hcon => h2 ((smul_disjoint_iff σ p q).mpr hcon)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun hpq => h1 ((smul_eq_iff σ p q).mp hpq),
      fun hcon => h2 ((smul_disjoint_iff σ p q).mp hcon)⟩

lemma smul_op (σ : Equiv.Perm (Fin m)) (p q : Edge m) : Op (σ • p) (σ • q) ↔ Op p q := by
  rw [Op, Op]
  exact smul_disjoint_iff σ p q

/-- The edge spanned by two distinct vertices. -/
def edgeOf (i j : Fin m) (h : i ≠ j) : Edge m :=
  if hij : i < j then ⟨(i, j), hij⟩
  else ⟨(j, i), lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm h)⟩

lemma toFinset_edgeOf {i j : Fin m} (h : i ≠ j) : (edgeOf i j h).toFinset = {i, j} := by
  by_cases hij : i < j
  · simp [edgeOf, hij, toFinset]
  · simp [edgeOf, hij, toFinset, Finset.pair_comm]

lemma edgeOf_comm {i j : Fin m} (h : i ≠ j) (h' : j ≠ i) : edgeOf i j h = edgeOf j i h' :=
  toFinset_injective (by rw [toFinset_edgeOf, toFinset_edgeOf, Finset.pair_comm])

lemma edgeOf_mem_iff {i j k : Fin m} (h : i ≠ j) :
    k ∈ (edgeOf i j h).toFinset ↔ k = i ∨ k = j := by
  rw [toFinset_edgeOf, Finset.mem_insert, Finset.mem_singleton]

lemma smul_edgeOf (σ : Equiv.Perm (Fin m)) {i j : Fin m} (h : i ≠ j) :
    σ • edgeOf i j h = edgeOf (σ i) (σ j) (fun he => h (σ.injective he)) := by
  apply toFinset_injective
  rw [toFinset_smul, toFinset_edgeOf, toFinset_edgeOf]
  simp

/-- Three distinct vertices give an embedding `Fin 3 ↪ Fin m`. -/
def emb3 (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : Fin 3 ↪ Fin m where
  toFun i := if i = 0 then x else if i = 1 then y else z
  inj' := by
    intro a b hab
    have ha : a = 0 ∨ a = 1 ∨ a = 2 := by
      have h : (a : ℕ) < 3 := a.isLt
      rcases Nat.eq_zero_or_pos (a : ℕ) with h0 | h0
      · exact Or.inl (Fin.ext (by omega))
      · rcases Nat.lt_or_ge (a : ℕ) 2 with h1 | h1
        · exact Or.inr (Or.inl (Fin.ext (by omega)))
        · exact Or.inr (Or.inr (Fin.ext (by omega)))
    have hb : b = 0 ∨ b = 1 ∨ b = 2 := by
      have h : (b : ℕ) < 3 := b.isLt
      rcases Nat.eq_zero_or_pos (b : ℕ) with h0 | h0
      · exact Or.inl (Fin.ext (by omega))
      · rcases Nat.lt_or_ge (b : ℕ) 2 with h1 | h1
        · exact Or.inr (Or.inl (Fin.ext (by omega)))
        · exact Or.inr (Or.inr (Fin.ext (by omega)))
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp_all

/-- Four distinct vertices give an embedding `Fin 4 ↪ Fin m`. -/
def emb4 (a b c d : Fin m) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : Fin 4 ↪ Fin m where
  toFun i := if i = 0 then a else if i = 1 then b else if i = 2 then c else d
  inj' := by
    intro p q hpq
    have hp : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by
      have h : (p : ℕ) < 4 := p.isLt
      rcases Nat.eq_zero_or_pos (p : ℕ) with h0 | h0
      · exact Or.inl (Fin.ext (by omega))
      · rcases Nat.lt_or_ge (p : ℕ) 2 with h1 | h1
        · exact Or.inr (Or.inl (Fin.ext (by omega)))
        · rcases Nat.lt_or_ge (p : ℕ) 3 with h2 | h2
          · exact Or.inr (Or.inr (Or.inl (Fin.ext (by omega))))
          · exact Or.inr (Or.inr (Or.inr (Fin.ext (by omega))))
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by
      have h : (q : ℕ) < 4 := q.isLt
      rcases Nat.eq_zero_or_pos (q : ℕ) with h0 | h0
      · exact Or.inl (Fin.ext (by omega))
      · rcases Nat.lt_or_ge (q : ℕ) 2 with h1 | h1
        · exact Or.inr (Or.inl (Fin.ext (by omega)))
        · rcases Nat.lt_or_ge (q : ℕ) 3 with h2 | h2
          · exact Or.inr (Or.inr (Or.inl (Fin.ext (by omega))))
          · exact Or.inr (Or.inr (Or.inr (Fin.ext (by omega))))
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;> simp_all

/-- The ordered pair of adjacent edges determined by a triple of distinct vertices
`(x, y, z)`: the edges `{x,y}` and `{x,z}`. -/
def tripToPair {m : ℕ} (f : Fin 3 ↪ Fin m) : Edge m × Edge m :=
  (edgeOf (f 0) (f 1) (fun h => by simpa using f.injective h),
   edgeOf (f 0) (f 2) (fun h => by simpa using f.injective h))

/-- The ordered pair of opposite edges determined by a quadruple of distinct vertices
`(a, b, c, d)`: the edges `{a,b}` and `{c,d}`. -/
def quadToPair {m : ℕ} (f : Fin 4 ↪ Fin m) : Edge m × Edge m :=
  (edgeOf (f 0) (f 1) (fun h => by simpa using f.injective h),
   edgeOf (f 2) (f 3) (fun h => by simpa using f.injective h))

lemma tripToPair_smul (σ : Equiv.Perm (Fin m)) (f : Fin 3 ↪ Fin m) :
    tripToPair (σ • f) = (σ • (tripToPair f).1, σ • (tripToPair f).2) := by
  refine Prod.ext ?_ ?_ <;> apply toFinset_injective <;>
    simp [tripToPair, toFinset_edgeOf, toFinset_edgeMap, Function.Embedding.smul_apply]

lemma quadToPair_smul (σ : Equiv.Perm (Fin m)) (f : Fin 4 ↪ Fin m) :
    quadToPair (σ • f) = (σ • (quadToPair f).1, σ • (quadToPair f).2) := by
  refine Prod.ext ?_ ?_ <;> apply toFinset_injective <;>
    simp [quadToPair, toFinset_edgeOf, toFinset_edgeMap, Function.Embedding.smul_apply]

lemma adj_tripToPair (f : Fin 3 ↪ Fin m) : Adj (tripToPair f).1 (tripToPair f).2 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h2 : ({f 0, f 1} : Finset (Fin m)) = {f 0, f 2} := by
      have := congrArg Edge.toFinset h
      simpa [tripToPair, toFinset_edgeOf] using this
    have h3 : f 1 ∈ ({f 0, f 2} : Finset (Fin m)) := by rw [← h2]; simp
    rw [Finset.mem_insert, Finset.mem_singleton] at h3
    rcases h3 with h3 | h3
    · exact absurd (f.injective h3) (by decide)
    · exact absurd (f.injective h3) (by decide)
  · intro hd
    have hmem1 : f 0 ∈ (tripToPair f).1.toFinset := by
      rw [tripToPair, toFinset_edgeOf]; simp
    have hmem2 : f 0 ∈ (tripToPair f).2.toFinset := by
      rw [tripToPair, toFinset_edgeOf]; simp
    exact Finset.disjoint_left.mp hd hmem1 hmem2

lemma op_quadToPair (f : Fin 4 ↪ Fin m) : Op (quadToPair f).1 (quadToPair f).2 := by
  rw [Op, Finset.disjoint_iff_inter_eq_empty, quadToPair, toFinset_edgeOf, toFinset_edgeOf]
  ext k
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h1 | h1, h2 | h2⟩ <;> exact absurd (f.injective (h1.symm.trans h2)) (by decide)
  · intro h
    exact absurd h (Finset.notMem_empty k)

end Edge

end Submission.RouteB
