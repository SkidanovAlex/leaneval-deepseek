import Submission.Work.RouteB.Simplex

open scoped BigOperators

set_option autoImplicit false

/-!
# Transitivity of the symmetric group on edges, adjacent pairs and opposite pairs

Using the "configuration embeddings" of `Simplex.lean`, transitivity statements become
instances of `Equiv.Perm.exists_smul_eq_embedding`.
-/

namespace Submission.RouteB

namespace Edge

variable {m : ℕ}

/-- The embedding `Fin 2 ↪ Fin m` given by the two vertices of an edge. -/
def emb (p : Edge m) : Fin 2 ↪ Fin m where
  toFun i := if i = 0 then p.1.1 else p.1.2
  inj' := by
    have hne : p.1.1 ≠ p.1.2 := ne_of_lt p.2
    intro a b hab
    have ha : a = 0 ∨ a = 1 := by
      have h : (a : ℕ) < 2 := a.isLt
      rcases Nat.eq_zero_or_pos (a : ℕ) with h0 | h0
      · exact Or.inl (Fin.ext (by omega))
      · exact Or.inr (Fin.ext (by omega))
    have hb : b = 0 ∨ b = 1 := by
      have h : (b : ℕ) < 2 := b.isLt
      rcases Nat.eq_zero_or_pos (b : ℕ) with h0 | h0
      · exact Or.inl (Fin.ext (by omega))
      · exact Or.inr (Fin.ext (by omega))
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

/-- The edge determined by an embedding `Fin 2 ↪ Fin m`. -/
def pairToEdge (f : Fin 2 ↪ Fin m) : Edge m :=
  edgeOf (f 0) (f 1) (fun h => by simpa using f.injective h)

lemma emb_zero (p : Edge m) : emb p 0 = p.1.1 := rfl

lemma emb_one (p : Edge m) : emb p 1 = p.1.2 := rfl

lemma emb3_zero {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    emb3 x y z hxy hxz hyz 0 = x := rfl

lemma emb3_one {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    emb3 x y z hxy hxz hyz 1 = y := rfl

lemma emb3_two {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    emb3 x y z hxy hxz hyz 2 = z := rfl

lemma emb4_zero {a b c d : Fin m} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : emb4 a b c d hab hac had hbc hbd hcd 0 = a :=
  rfl

lemma emb4_one {a b c d : Fin m} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : emb4 a b c d hab hac had hbc hbd hcd 1 = b :=
  rfl

lemma emb4_two {a b c d : Fin m} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : emb4 a b c d hab hac had hbc hbd hcd 2 = c :=
  rfl

lemma emb4_three {a b c d : Fin m} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    emb4 a b c d hab hac had hbc hbd hcd 3 = d := rfl

lemma pairToEdge_emb (p : Edge m) : pairToEdge (emb p) = p := by
  rw [← toFinset_inj]
  rw [pairToEdge, toFinset_edgeOf, emb_zero, emb_one, toFinset]

lemma pairToEdge_smul (σ : Equiv.Perm (Fin m)) (f : Fin 2 ↪ Fin m) :
    pairToEdge (σ • f) = σ • pairToEdge f := by
  rw [← toFinset_inj, pairToEdge, toFinset_edgeOf]
  rw [Function.Embedding.smul_apply, Function.Embedding.smul_apply, smul_def, toFinset_edgeMap,
    pairToEdge, toFinset_edgeOf]
  simp

lemma tripToPair_emb3 {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    tripToPair (emb3 x y z hxy hxz hyz) = (edgeOf x y hxy, edgeOf x z hxz) := by
  have h0 : emb3 x y z hxy hxz hyz 0 = x := rfl
  have h1 : emb3 x y z hxy hxz hyz 1 = y := rfl
  have h2 : emb3 x y z hxy hxz hyz 2 = z := rfl
  exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)

lemma quadToPair_emb4 {a b c d : Fin m} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    quadToPair (emb4 a b c d hab hac had hbc hbd hcd) = (edgeOf a b hab, edgeOf c d hcd) := by
  have h0 : emb4 a b c d hab hac had hbc hbd hcd 0 = a := rfl
  have h1 : emb4 a b c d hab hac had hbc hbd hcd 1 = b := rfl
  have h2 : emb4 a b c d hab hac had hbc hbd hcd 2 = c := rfl
  have h3 : emb4 a b c d hab hac had hbc hbd hcd 3 = d := rfl
  exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)

lemma exists_emb3_of_adj {p q : Edge m} (h : Adj p q) :
    ∃ f : Fin 3 ↪ Fin m, tripToPair f = (p, q) := by
  obtain ⟨x, hx1, hx2⟩ := Finset.not_disjoint_iff.mp h.2
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp (by
    rw [Finset.card_erase_of_mem hx1, toFinset_card] : (p.toFinset.erase x).card = 1)
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (by
    rw [Finset.card_erase_of_mem hx2, toFinset_card] : (q.toFinset.erase x).card = 1)
  have hpx : p.toFinset = {x, y} := by rw [← Finset.insert_erase hx1, hy]
  have hqx : q.toFinset = {x, z} := by rw [← Finset.insert_erase hx2, hz]
  have hyx : y ≠ x := by
    have : y ∈ p.toFinset.erase x := by rw [hy]; exact Finset.mem_singleton_self y
    exact (Finset.mem_erase.mp this).1
  have hzx : z ≠ x := by
    have : z ∈ q.toFinset.erase x := by rw [hz]; exact Finset.mem_singleton_self z
    exact (Finset.mem_erase.mp this).1
  have hyz : y ≠ z := by
    intro hyz
    have hsub : p.toFinset ⊆ q.toFinset := by
      rw [hpx]
      intro k hk
      rw [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · rw [hqx]; simp
      · rw [hyz, hqx]; simp
    have heq : p.toFinset = q.toFinset :=
      Finset.eq_of_subset_of_card_le hsub (by rw [toFinset_card, toFinset_card])
    exact h.1 (toFinset_injective heq)
  refine ⟨emb3 x y z (fun hh => hyx hh.symm) (fun hh => hzx hh.symm) hyz, ?_⟩
  have e1 : edgeOf x y (fun hh => hyx hh.symm) = p :=
    toFinset_injective (by rw [toFinset_edgeOf, hpx])
  have e2 : edgeOf x z (fun hh => hzx hh.symm) = q :=
    toFinset_injective (by rw [toFinset_edgeOf, hqx])
  rw [tripToPair_emb3, e1, e2]

lemma exists_emb4_of_op {p q : Edge m} (h : Op p q) :
    ∃ f : Fin 4 ↪ Fin m, quadToPair f = (p, q) := by
  obtain ⟨a, b, hab, hp⟩ := Finset.card_eq_two.mp (toFinset_card p)
  obtain ⟨c, d, hcd, hq⟩ := Finset.card_eq_two.mp (toFinset_card q)
  have hpa : a ∈ p.toFinset := by rw [hp]; simp
  have hpb : b ∈ p.toFinset := by rw [hp]; simp
  have hd1 : a ∉ ({c, d} : Finset (Fin m)) := by
    intro hc
    exact Finset.disjoint_left.mp h hpa (by rw [hq]; exact hc)
  have hd2 : b ∉ ({c, d} : Finset (Fin m)) := by
    intro hc
    exact Finset.disjoint_left.mp h hpb (by rw [hq]; exact hc)
  have hac : a ≠ c := fun hh => hd1 (by rw [← hh]; simp)
  have had : a ≠ d := fun hh => hd1 (by rw [← hh]; simp)
  have hbc : b ≠ c := fun hh => hd2 (by rw [← hh]; simp)
  have hbd : b ≠ d := fun hh => hd2 (by rw [← hh]; simp)
  refine ⟨emb4 a b c d hab hac had hbc hbd hcd, ?_⟩
  have e1 : edgeOf a b hab = p := toFinset_injective (by rw [toFinset_edgeOf, hp])
  have e2 : edgeOf c d hcd = q := toFinset_injective (by rw [toFinset_edgeOf, hq])
  rw [quadToPair_emb4, e1, e2]

/-- The symmetric group is transitive on edges. -/
theorem exists_smul_eq_edge (p q : Edge m) : ∃ σ : Equiv.Perm (Fin m), σ • p = q := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_smul_eq_embedding (emb p) (emb q)
  refine ⟨σ, ?_⟩
  rw [← pairToEdge_emb p, ← pairToEdge_emb q, ← pairToEdge_smul, hσ]

/-- The symmetric group is transitive on ordered pairs of adjacent edges. -/
theorem exists_smul_eq_adjPair {x y : Edge m × Edge m} (hx : Adj x.1 x.2) (hy : Adj y.1 y.2) :
    ∃ σ : Equiv.Perm (Fin m), σ • x = y := by
  obtain ⟨f, hf⟩ := exists_emb3_of_adj hx
  obtain ⟨g, hg⟩ := exists_emb3_of_adj hy
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_smul_eq_embedding f g
  have hfx : tripToPair f = x := hf
  have hgy : tripToPair g = y := hg
  refine ⟨σ, ?_⟩
  rw [← hfx, ← hgy,
    show (σ • tripToPair f) = tripToPair (σ • f) from (tripToPair_smul σ f).symm, hσ]

/-- The symmetric group is transitive on ordered pairs of opposite edges. -/
theorem exists_smul_eq_opPair {x y : Edge m × Edge m} (hx : Op x.1 x.2) (hy : Op y.1 y.2) :
    ∃ σ : Equiv.Perm (Fin m), σ • x = y := by
  obtain ⟨f, hf⟩ := exists_emb4_of_op hx
  obtain ⟨g, hg⟩ := exists_emb4_of_op hy
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_smul_eq_embedding f g
  have hfx : quadToPair f = x := hf
  have hgy : quadToPair g = y := hg
  refine ⟨σ, ?_⟩
  rw [← hfx, ← hgy,
    show (σ • quadToPair f) = quadToPair (σ • f) from (quadToPair_smul σ f).symm, hσ]

end Edge

end Submission.RouteB
