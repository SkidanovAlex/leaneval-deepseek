import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.NibbleRoundDefs
import Submission.Work.Deep.Kahn.Pad
import Submission.Work.Deep.Kahn.listDecomp
import Submission.Work.Deep.Kahn.padColourDegLe
import Submission.Work.Deep.Kahn.padColourDegSum
import Submission.Work.Deep.Nibble.exists_linear_regular_uniform

/-!
# The embedding (regularisation) step of Kahn's theorem

This module proves `Work.Deep.Kahn.EmbeddingStatement` (`prop:embedding` of the
Kahn subproject): every linear hypergraph with edges of size at most `C`, lists of
common size `Λ` and colour degrees at most `D` embeds into a linear hypergraph all
of whose edges have size exactly `C`, all of whose lists have size `Λ` and in which
every occurring colour degree is exactly `D`.

## The construction

* **Padding.**  `Submission.Work.Deep.Kahn.Pad` attaches `C - edgeSize e` fresh
  vertices to every edge `e`, producing the `C`-uniform linear hypergraph
  `padHyp C 𝓗` on the vertex type `PV n C 𝓗 = Fin n ⊕ (𝓗 × Fin C)`.

* **Copies and self-edges.**  Fix a prime `M` at least `C` and at least the number
  of self-edges needed below, and let the new vertices be pairs `(v, t)` with
  `v : PV n C 𝓗` and `t : Fin C × ZMod M`.  For every `v` we choose a family
  `Γ v : Fin (m v) → Finset (Fin c')` of `Λ`-sets of colours (its *self-edge lists*)
  with the property that colour `γ'` occurs in exactly `D - dE v γ'` of the lists,
  where `dE v γ'` is the number of padded edges through `v` whose list contains
  `γ'`; this is `listDecomp`.  The self-edge family on the copies of `v` is the
  cyclic design `{(a, s + k·a) : a < C}` (`Cyc.cycEdge`): the `m v` designs
  `k < m v` are pairwise orthogonal, so two copies of `v` are joined by at most one
  self-edge of each multiplier and the copies of `v` have degree exactly `m v`.

* **Diagonal edges.**  For every edge `e` of `𝓗` and every copy index `t` we add
  the diagonal copy `{(v, t) : v ∈ padEdge C 𝓗 e}` with list `(L e).image ρ`.

A vertex `(v, t)` then lies in exactly `m v` self-edges (with lists `Γ v`) and, for
every edge `e` through `v`, in the diagonal edge of `e` at copy `t`; consequently
the colour degree of `(v, t)` at `γ'` is `(D - dE v γ') + dE v γ' = D`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture
open Work.Deep.Nibble.Cyc

noncomputable section

variable {n c C D Λ c' M : ℕ}
variable {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
variable {L : 𝓗 → Finset (Fin c)}
variable {ρ : Fin c → Fin c'}

/-! ## The cyclic family of self-edges on the copies of a vertex -/

/-- The copy index set of the embedding: `C` "colour slots" and a `ZMod M` coordinate. -/
abbrev Copy (C M : ℕ) : Type := Fin C × ZMod M

/-- The set of copies of `x` sitting in the cyclic edge of multiplier `a` and shift `s`. -/
def selfEdge {V : Type*} (C M : ℕ) (x : V) (a s : ZMod M) : Set (V × Copy C M) :=
  Set.image (fun t : Copy C M => (x, t)) (cycEdge C M a s)

theorem mem_selfEdge {V : Type*} {C M : ℕ} {x v : V} {a s : ZMod M} {t : Copy C M} :
    (v, t) ∈ selfEdge C M x a s ↔ v = x ∧ t ∈ cycEdge C M a s := by
  constructor
  · rintro ⟨t', ht', h⟩
    obtain rfl : t' = t := congrArg Prod.snd h
    exact ⟨(congrArg Prod.fst h).symm, ht'⟩
  · rintro ⟨rfl, ht⟩
    exact ⟨t, ht, rfl⟩

theorem selfEdge_ncard {V : Type*} (C M : ℕ) (x : V) (a s : ZMod M) :
    (selfEdge C M x a s).ncard = C := by
  rw [selfEdge, Set.ncard_image_of_injective _ (fun t t' h => congrArg Prod.snd h),
    cycEdge_ncard]

theorem cycEdge_disjoint_of_ne {C M : ℕ} {a s s' : ZMod M} (h : s ≠ s') :
    Disjoint (cycEdge C M a s) (cycEdge C M a s') := by
  rw [Set.disjoint_left]
  rintro ⟨i, y⟩ h1 h2
  have h1' : y = s + a * finCast C M i := (mem_cycEdge a s i y).mp h1
  have h2' : y = s' + a * finCast C M i := (mem_cycEdge a s' i y).mp h2
  exact h (add_right_cancel (h1'.symm.trans h2'))

theorem cycEdge_inter_subsingleton' {C M : ℕ} [Fact M.Prime] (hCM : C ≤ M) {a a' s s' : ZMod M}
    (h : a ≠ a' ∨ s ≠ s') : (cycEdge C M a s ∩ cycEdge C M a' s').Subsingleton := by
  by_cases ha : a = a'
  · have hs : s ≠ s' := by
      rcases h with h' | h'
      · exact absurd ha h'
      · exact h'
    subst ha
    intro t ht u hu
    exact (Set.disjoint_left.mp (cycEdge_disjoint_of_ne hs) ht.1 ht.2).elim
  · exact cycEdge_inter_subsingleton hCM ha

theorem selfEdge_inter_subsingleton {V : Type*} {C M : ℕ} [Fact M.Prime] (hCM : C ≤ M)
    {x x' : V} {a a' s s' : ZMod M} (h : x ≠ x' ∨ a ≠ a' ∨ s ≠ s') :
    (selfEdge C M x a s ∩ selfEdge C M x' a' s').Subsingleton := by
  by_cases hx : x = x'
  · subst hx
    rw [selfEdge, selfEdge, ← Set.image_inter (f := fun t : Copy C M => (x, t))
      (fun t t' h => congrArg Prod.snd h)]
    apply Set.Subsingleton.image
    rcases h with h' | h'
    · exact absurd rfl h'
    · exact cycEdge_inter_subsingleton' hCM h'
  · intro v hv w hw
    exact absurd ((mem_selfEdge.mp hv.1).1.symm.trans (mem_selfEdge.mp hv.2).1) hx

theorem selfEdge_shift_existsUnique {V : Type*} {C M : ℕ} (x : V) (a : ZMod M)
    (t : Copy C M) : ∃! s : ZMod M, (x, t) ∈ selfEdge C M x a s := by
  refine ⟨t.2 - a * finCast C M t.1, ?_, ?_⟩
  · show (x, t) ∈ selfEdge C M x a (t.2 - a * finCast C M t.1)
    rw [mem_selfEdge]
    exact ⟨rfl, by rw [mem_cycEdge]; ring⟩
  · intro s hs
    have h' := (mem_selfEdge.mp hs).2
    have h'' := (mem_cycEdge a s t.1 t.2).mp h'
    rw [h'']; ring

theorem selfEdge_eq_of {V : Type*} {C M : ℕ} [Fact M.Prime] (hC : 2 ≤ C) (hCM : C ≤ M)
    {x x' : V} {a a' s s' : ZMod M} (h : selfEdge C M x a s = selfEdge C M x' a' s') :
    x = x' ∧ a = a' ∧ s = s' := by
  have hmem : (x, ((⟨0, by omega⟩ : Fin C), s)) ∈ selfEdge C M x' a' s' := by
    rw [← h]
    exact ⟨((⟨0, by omega⟩ : Fin C), s), (mem_cycEdge a s _ _).mpr (by simp [finCast]), rfl⟩
  have hx := (mem_selfEdge.mp hmem).1
  subst hx
  have hinj : Function.Injective (fun t : Copy C M => (x, t)) := fun t t' h => congrArg Prod.snd h
  have hc : cycEdge C M a s = cycEdge C M a' s' := (Set.image_injective.mpr hinj) h
  obtain ⟨rfl, rfl⟩ := (cycEdge_eq_iff hC hCM).mp hc
  exact ⟨rfl, rfl, rfl⟩


/-! ## The edge and list families of the embedding -/

/-- The vertex type of the embedding: the padded vertices, together with the copy index. -/
abbrev EmbVtx (n C : ℕ) (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) (M : ℕ) : Type :=
  PV n C 𝓗 × Copy C M

/-- The index type of the embedding: the diagonal copies of the padded edges (indexed by the
edge of `𝓗` and the copy), and the self-edges (indexed by the base vertex `v`, the multiplier
`k < m v` and the shift `s`). -/
abbrev EmbIdx (n C : ℕ) (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    (m : PV n C 𝓗 → ℕ) (M : ℕ) : Type :=
  (𝓗 × Copy C M) ⊕ (Σ v : PV n C 𝓗, Fin (m v) × ZMod M)

/-- The edge of the embedding attached to an index. -/
def embEdge {n C M : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {m : PV n C 𝓗 → ℕ} (i : EmbIdx n C 𝓗 m M) : Set (EmbVtx n C 𝓗 M) :=
  match i with
  | Sum.inl p => Set.image (fun y : PV n C 𝓗 => (y, p.2)) (padEdge C 𝓗 p.1)
  | Sum.inr q => selfEdge C M q.1 ((q.2.1).val : ZMod M) q.2.2

/-- The list of the edge of the embedding attached to an index. -/
def embList {n C c' M : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {c : ℕ} {L : 𝓗 → Finset (Fin c)} {ρ : Fin c → Fin c'} {m : PV n C 𝓗 → ℕ}
    (Γ : (v : PV n C 𝓗) → Fin (m v) → Finset (Fin c'))
    (i : EmbIdx n C 𝓗 m M) : Finset (Fin c') :=
  match i with
  | Sum.inl p => (L p.1).image ρ
  | Sum.inr q => Γ q.1 q.2.1

/-- Membership in a "constant second coordinate" image. -/
theorem mem_image_const {α β : Type*} {s : Set α} {b : β} {x : α × β} :
    x ∈ Set.image (fun a : α => (a, b)) s ↔ x.1 ∈ s ∧ x.2 = b := by
  constructor
  · rintro ⟨a, ha, h⟩
    exact ⟨(congrArg Prod.fst h).symm ▸ ha, (congrArg Prod.snd h).symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨x.1, h1, Prod.ext rfl h2.symm⟩

theorem embEdge_inl {m : PV n C 𝓗 → ℕ} {e : 𝓗} {t : Copy C M} :
    embEdge (𝓗 := 𝓗) (m := m) (Sum.inl (e, t)) =
      Set.image (fun y : PV n C 𝓗 => (y, t)) (padEdge C 𝓗 e) := rfl

theorem embEdge_inr {m : PV n C 𝓗 → ℕ} {q : Σ v : PV n C 𝓗, Fin (m v) × ZMod M} :
    embEdge (𝓗 := 𝓗) (Sum.inr q) =
      selfEdge C M q.1 ((q.2.1).val : ZMod M) q.2.2 := rfl

theorem embList_inl {m : PV n C 𝓗 → ℕ} {Γ : (v : PV n C 𝓗) → Fin (m v) → Finset (Fin c')} {e : 𝓗}
    {t : Copy C M} : embList (𝓗 := 𝓗) (L := L) (ρ := ρ) Γ (Sum.inl (e, t)) = (L e).image ρ := rfl

theorem embList_inr {m : PV n C 𝓗 → ℕ} {Γ : (v : PV n C 𝓗) → Fin (m v) → Finset (Fin c')}
    {q : Σ v : PV n C 𝓗, Fin (m v) × ZMod M} :
    embList (𝓗 := 𝓗) (L := L) (ρ := ρ) Γ (Sum.inr q) = Γ q.1 q.2.1 := rfl

/-- Two padded edges with distinct indices meet in at most one point (the padded hypergraph is
linear whenever `𝓗` is). -/
theorem padEdge_inter_subsingleton {n C : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    (hlin : 𝓗.IsLinear) (hedge : ∀ e : 𝓗, edgeSize (e : Set (Fin n)) ≤ C) {e f : 𝓗}
    (h : e ≠ f) : (padEdge C 𝓗 e ∩ padEdge C 𝓗 f).Subsingleton := by
  have hpair := padHyp_linear (C := C) hlin
  exact hpair ⟨e, rfl⟩ ⟨f, rfl⟩ (fun hEq => h (padEdge_injective hedge hEq))

/-- Every edge of the embedding has exactly `C` vertices. -/
theorem embEdge_ncard {n C M : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {m : PV n C 𝓗 → ℕ} (hedge : ∀ e : 𝓗, edgeSize (e : Set (Fin n)) ≤ C)
    (i : EmbIdx n C 𝓗 m M) : (embEdge (𝓗 := 𝓗) (m := m) i).ncard = C := by
  rcases i with ⟨e, t⟩ | ⟨x, k, s⟩
  · rw [embEdge_inl, Set.ncard_image_of_injective _ (fun a b h => congrArg Prod.fst h),
      padEdge_ncard hedge]
  · rw [embEdge_inr, selfEdge_ncard]

/-- **The family of edges of the embedding is linear.**  Two diagonal copies meet in at most one
point (they live in different copies of the vertex set when the copy indices differ, and
otherwise the padded hypergraph is linear); a diagonal copy meets a self-edge in at most one
point (a self-edge consists of copies of a single padded vertex); and two self-edges meet in at
most one point (the cyclic family `Cyc.cycEdge` is linear, and distinct multipliers are distinct
in `ZMod M` because `M` exceeds the number of self-edges). -/
theorem embLinear {n C M : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {m : PV n C 𝓗 → ℕ} [Fact M.Prime] (hC : 2 ≤ C) (hCM : C ≤ M)
    (hMm : ∀ v : PV n C 𝓗, m v ≤ M) (hlin : 𝓗.IsLinear)
    (hedge : ∀ e : 𝓗, edgeSize (e : Set (Fin n)) ≤ C) :
    ∀ i j : EmbIdx n C 𝓗 m M, i ≠ j → (embEdge i ∩ embEdge j).Subsingleton := by
  rintro (⟨e, t⟩ | ⟨x, k, s⟩) (⟨e', t'⟩ | ⟨x', k', s'⟩) hne
  · rw [embEdge_inl, embEdge_inl]
    by_cases htt : t = t'
    · subst htt
      have hef : e ≠ e' := by intro h; exact hne (by rw [h])
      rw [← Set.image_inter (f := fun y : PV n C 𝓗 => (y, t))
        (fun a b h => congrArg Prod.fst h)]
      exact (padEdge_inter_subsingleton hlin hedge hef).image (fun y : PV n C 𝓗 => (y, t))
    · intro v hv w hw
      exact absurd (((mem_image_const.mp hv.1).2).symm.trans ((mem_image_const.mp hv.2).2)) htt
  · rw [embEdge_inl, embEdge_inr]
    intro v hv w hw
    have h1 : v.1 = x' := (mem_selfEdge.mp hv.2).1
    have h2 : w.1 = x' := (mem_selfEdge.mp hw.2).1
    have h3 : v.2 = t := (mem_image_const.mp hv.1).2
    have h4 : w.2 = t := (mem_image_const.mp hw.1).2
    exact Prod.ext (h1.trans h2.symm) (h3.trans h4.symm)
  · rw [embEdge_inr, embEdge_inl]
    intro v hv w hw
    have h1 : v.1 = x := (mem_selfEdge.mp hv.1).1
    have h2 : w.1 = x := (mem_selfEdge.mp hw.1).1
    have h3 : v.2 = t' := (mem_image_const.mp hv.2).2
    have h4 : w.2 = t' := (mem_image_const.mp hw.2).2
    exact Prod.ext (h1.trans h2.symm) (h3.trans h4.symm)
  · rw [embEdge_inr, embEdge_inr]
    refine selfEdge_inter_subsingleton hCM ?_
    by_cases hx : x = x'
    · subst hx
      by_cases hk : (k.val : ZMod M) = (k'.val : ZMod M)
      · by_cases hs : s = s'
        · exfalso
          have hkk : k = k' :=
            finCast_injective (hMm x) (by simpa [finCast] using hk)
          exact hne (by rw [hkk, hs])
        · exact Or.inr (Or.inr hs)
      · exact Or.inr (Or.inl hk)
    · exact Or.inl hx

/-! ## The types of the transfer, and counting the edges through a vertex -/

/-- The shift is determined by the copy in the cyclic design. -/
theorem cycEdge_shift_existsUnique {C M : ℕ} (a : ZMod M) (t : Copy C M) :
    ∃! s : ZMod M, t ∈ cycEdge C M a s := by
  refine ⟨t.2 - a * finCast C M t.1, ?_, ?_⟩
  · show (t.1, t.2) ∈ cycEdge C M a (t.2 - a * finCast C M t.1)
    rw [mem_cycEdge]; ring
  · intro s hs
    have h := (mem_cycEdge a s t.1 t.2).mp hs
    rw [h]; ring

/-- The number of shifts `s` for which a copy lies in the cyclic edge of multiplier `a`,
subject to a condition `Q`, is `1` if `Q` holds and `0` otherwise. -/
theorem natCard_cycEdge_fiber {C M : ℕ} [NeZero M] (a : ZMod M) (t : Copy C M) (Q : Prop)
    [Decidable Q] :
    Nat.card {s : ZMod M // t ∈ cycEdge C M a s ∧ Q} = if Q then 1 else 0 := by
  classical
  obtain ⟨s₀, hs₀, huniq⟩ := cycEdge_shift_existsUnique (C := C) (M := M) a t
  by_cases hQ : Q
  · rw [if_pos hQ]
    have hle : Nat.card {s : ZMod M // t ∈ cycEdge C M a s ∧ Q} ≤ 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_le_one_iff_subsingleton]
      exact ⟨fun x y => Subtype.ext ((huniq x.1 x.2.1).trans (huniq y.1 y.2.1).symm)⟩
    have hge : 1 ≤ Nat.card {s : ZMod M // t ∈ cycEdge C M a s ∧ Q} := by
      haveI : Nonempty {s : ZMod M // t ∈ cycEdge C M a s ∧ Q} := ⟨⟨s₀, hs₀, hQ⟩⟩
      exact Nat.card_pos
    omega
  · rw [if_neg hQ]
    haveI : IsEmpty {s : ZMod M // t ∈ cycEdge C M a s ∧ Q} := ⟨fun x => hQ x.2.2⟩
    exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

/-- Splitting a subtype of a sum type into its two components. -/
def subtypeSumEquiv {α β : Type*} (P : α ⊕ β → Prop) :
    {i : α ⊕ β // P i} ≃ {a : α // P (Sum.inl a)} ⊕ {b : β // P (Sum.inr b)} where
  toFun i := match i with
    | ⟨Sum.inl a, h⟩ => Sum.inl ⟨a, h⟩
    | ⟨Sum.inr b, h⟩ => Sum.inr ⟨b, h⟩
  invFun x := match x with
    | Sum.inl a => ⟨Sum.inl a.1, a.2⟩
    | Sum.inr b => ⟨Sum.inr b.1, b.2⟩
  left_inv := by rintro ⟨(_ | _), _⟩ <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

/-- Dropping the second coordinate from a subtype of a product, the second coordinate being
forced to equal `b`. -/
def prodSubtypeEquiv {α β : Type*} (p : α → Prop) (b : β) :
    {a : α × β // p a.1 ∧ a.2 = b} ≃ {x : α // p x} where
  toFun a := ⟨a.1.1, a.2.1⟩
  invFun x := ⟨(x.1, b), x.2, rfl⟩
  left_inv a := by
    rcases a with ⟨⟨a1, a2⟩, hp, hb⟩
    exact Subtype.ext (Prod.ext rfl hb.symm)
  right_inv x := rfl

/-- Splitting a subtype of a sigma type into its fibres. -/
def sigmaSubtypeEquiv {α : Type*} {β : α → Type*} (P : (Σ a, β a) → Prop) :
    {q : Σ a, β a // P q} ≃ Σ a, {b : β a // P ⟨a, b⟩} where
  toFun q := ⟨q.1.1, q.1.2, q.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv q := by rcases q with ⟨⟨a, b⟩, h⟩; rfl
  right_inv x := by rcases x with ⟨a, b, h⟩; rfl

/-- Splitting a subtype of a product type into its fibres. -/
def prodSubtypeSigmaEquiv {α β : Type*} (P : α × β → Prop) :
    {p : α × β // P p} ≃ Σ a : α, {b : β // P (a, b)} where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  invFun x := ⟨(x.1, x.2.1), x.2.2⟩
  left_inv p := by rcases p with ⟨⟨a, b⟩, h⟩; rfl
  right_inv x := by rcases x with ⟨a, b, h⟩; rfl

/-- The cardinality of a subtype, as a filter cardinality. -/
theorem natCard_subtype_eq_filter {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    Nat.card {x : α // p x} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **Exact colour degrees of the embedding.**  If the self-edge lists `Γ v` are chosen so that
colour `γ'` occurs in exactly `D - dE v γ'` of them (where `dE v γ'` is the number of padded
edges through `v` whose list contains `γ'`, and `dE v γ' ≤ D`), then every vertex `(v,t)` of the
embedding and every colour `γ'` has colour degree exactly `D`: the `D - dE v γ'` self-edges
through `(v,t)` carrying `γ'` (one for each multiplier `k` with `γ' ∈ Γ v k`), together with the
`dE v γ'` diagonal copies at `t` of the padded edges through `v`, give exactly `D` edges. -/
theorem embDeg {n c C D c' M : ℕ} [NeZero M] {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {L : 𝓗 → Finset (Fin c)} {ρ : Fin c → Fin c'} {m : PV n C 𝓗 → ℕ}
    {Γ : (v : PV n C 𝓗) → Fin (m v) → Finset (Fin c')}
    (hΓcount : ∀ (v : PV n C 𝓗) (γ' : Fin c'),
      (Finset.univ.filter (fun k : Fin (m v) => γ' ∈ Γ v k)).card
        = D - Nat.card {e : 𝓗 // v ∈ padEdge C 𝓗 e ∧ γ' ∈ (L e).image ρ})
    (hdEle : ∀ (v : PV n C 𝓗) (γ' : Fin c'),
      Nat.card {e : 𝓗 // v ∈ padEdge C 𝓗 e ∧ γ' ∈ (L e).image ρ} ≤ D) :
    ∀ (v : EmbVtx n C 𝓗 M) (γ' : Fin c'),
      Nat.card {i : EmbIdx n C 𝓗 m M //
        v ∈ embEdge (𝓗 := 𝓗) (m := m) i ∧ γ' ∈ embList (L := L) (ρ := ρ) Γ i} = D := by
  classical
  intro v γ'
  have hdiag : Nat.card {a : 𝓗 × Copy C M //
        v ∈ embEdge (𝓗 := 𝓗) (m := m) (Sum.inl a)
          ∧ γ' ∈ embList (L := L) (ρ := ρ) Γ (Sum.inl a)}
      = Nat.card {e : 𝓗 // v.1 ∈ padEdge C 𝓗 e ∧ γ' ∈ (L e).image ρ} := by
    have heq : ∀ a : 𝓗 × Copy C M,
        (v ∈ embEdge (𝓗 := 𝓗) (m := m) (Sum.inl a)
          ∧ γ' ∈ embList (L := L) (ρ := ρ) Γ (Sum.inl a))
        ↔ ((fun e : 𝓗 => v.1 ∈ padEdge C 𝓗 e ∧ γ' ∈ (L e).image ρ) a.1 ∧ a.2 = v.2) := by
      rintro ⟨e, t'⟩
      change (v ∈ embEdge (𝓗 := 𝓗) (m := m) (Sum.inl (e, t'))
            ∧ γ' ∈ embList (L := L) (ρ := ρ) Γ (Sum.inl (e, t')))
          ↔ ((v.1 ∈ padEdge C 𝓗 e ∧ γ' ∈ (L e).image ρ) ∧ t' = v.2)
      rw [embEdge_inl, embList_inl]
      constructor
      · rintro ⟨h, h3⟩
        obtain ⟨y, hy, hyv⟩ := h
        have h1 : y = v.1 := congrArg Prod.fst hyv
        exact ⟨⟨h1 ▸ hy, h3⟩, congrArg Prod.snd hyv⟩
      · rintro ⟨⟨h1, h3⟩, h2⟩
        exact ⟨⟨v.1, h1, Prod.ext rfl h2⟩, h3⟩
    exact (Nat.card_congr (Equiv.subtypeEquivRight heq)).trans
      (Nat.card_congr (prodSubtypeEquiv (fun e : 𝓗 =>
        v.1 ∈ padEdge C 𝓗 e ∧ γ' ∈ (L e).image ρ) v.2))
  have hself : Nat.card {q : (Σ x : PV n C 𝓗, Fin (m x) × ZMod M) //
        v ∈ embEdge (𝓗 := 𝓗) (m := m) (Sum.inr q)
          ∧ γ' ∈ embList (L := L) (ρ := ρ) Γ (Sum.inr q)}
      = (Finset.univ.filter (fun k : Fin (m v.1) => γ' ∈ Γ v.1 k)).card := by
    have heq1 : ∀ q : (Σ x : PV n C 𝓗, Fin (m x) × ZMod M),
        (v ∈ embEdge (𝓗 := 𝓗) (m := m) (Sum.inr q)
          ∧ γ' ∈ embList (L := L) (ρ := ρ) Γ (Sum.inr q))
        ↔ (v ∈ embEdge (𝓗 := 𝓗) (m := m) (Sum.inr q) ∧ γ' ∈ Γ q.1 q.2.1) := by
      intro q
      rw [embList_inr]
    have heq2 : ∀ q : (Σ x : PV n C 𝓗, Fin (m x) × ZMod M),
        (v ∈ embEdge (𝓗 := 𝓗) (m := m) (Sum.inr q) ∧ γ' ∈ Γ q.1 q.2.1)
        ↔ (v.1 = q.1 ∧ v.2 ∈ cycEdge C M (q.2.1.val) q.2.2 ∧ γ' ∈ Γ q.1 q.2.1) := by
      intro q
      rw [embEdge_inr]
      constructor
      · rintro ⟨h, h3⟩
        obtain ⟨h1, h2⟩ := mem_selfEdge.mp h
        exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨mem_selfEdge.mpr ⟨h1, h2⟩, h3⟩
    rw [(Nat.card_congr (Equiv.subtypeEquivRight heq1)).trans
      (Nat.card_congr (Equiv.subtypeEquivRight heq2))]
    rw [Nat.card_congr (sigmaSubtypeEquiv (fun q : Σ x : PV n C 𝓗, Fin (m x) × ZMod M =>
      v.1 = q.1 ∧ v.2 ∈ cycEdge C M (q.2.1.val) q.2.2 ∧ γ' ∈ Γ q.1 q.2.1))]
    rw [Nat.card_sigma]
    have hzero : ∀ x ∈ (Finset.univ : Finset (PV n C 𝓗)), x ≠ v.1 →
        Nat.card {ks : Fin (m x) × ZMod M //
          v.1 = x ∧ v.2 ∈ cycEdge C M (ks.1.val) ks.2 ∧ γ' ∈ Γ x ks.1} = 0 := by
      intro x _ hx
      haveI : IsEmpty {ks : Fin (m x) × ZMod M //
          v.1 = x ∧ v.2 ∈ cycEdge C M (ks.1.val) ks.2 ∧ γ' ∈ Γ x ks.1} :=
        ⟨fun z => hx z.2.1.symm⟩
      exact Nat.card_eq_zero.mpr (Or.inl inferInstance)
    rw [Finset.sum_eq_single v.1 hzero (fun h => absurd (Finset.mem_univ v.1) h)]
    have heq3 : ∀ ks : Fin (m v.1) × ZMod M,
        ((fun ks : Fin (m v.1) × ZMod M =>
            v.1 = v.1 ∧ v.2 ∈ cycEdge C M (ks.1.val) ks.2 ∧ γ' ∈ Γ v.1 ks.1) ks)
        ↔ (v.2 ∈ cycEdge C M (ks.1.val) ks.2 ∧ γ' ∈ Γ v.1 ks.1) := by
      intro ks
      constructor
      · rintro ⟨-, h2, h3⟩; exact ⟨h2, h3⟩
      · rintro ⟨h2, h3⟩; exact ⟨rfl, h2, h3⟩
    rw [Nat.card_congr (Equiv.subtypeEquivRight heq3)]
    rw [Nat.card_congr (prodSubtypeSigmaEquiv (fun ks : Fin (m v.1) × ZMod M =>
      v.2 ∈ cycEdge C M (ks.1.val) ks.2 ∧ γ' ∈ Γ v.1 ks.1))]
    rw [Nat.card_sigma]
    have hfil : (Finset.univ.filter (fun k : Fin (m v.1) => γ' ∈ Γ v.1 k)).card
        = ∑ k : Fin (m v.1), (if γ' ∈ Γ v.1 k then 1 else 0) := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [hfil]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    change Nat.card {s : ZMod M // v.2 ∈ cycEdge C M (k.val) s ∧ γ' ∈ Γ v.1 k}
        = if γ' ∈ Γ v.1 k then 1 else 0
    exact natCard_cycEdge_fiber (C := C) (M := M) k.val v.2 (γ' ∈ Γ v.1 k)
  rw [Nat.card_congr (subtypeSumEquiv (fun i : EmbIdx n C 𝓗 m M =>
      v ∈ embEdge (𝓗 := 𝓗) (m := m) i ∧ γ' ∈ embList (L := L) (ρ := ρ) Γ i)),
    Nat.card_sum, hdiag, hself, hΓcount v.1 γ']
  have := hdEle v.1 γ'
  omega

/-! ## Injectivity of the edge map -/

/-- The two families of indices give edges of different "shape": the diagonal edge of `(e,t)` is
the graph of the constant map `y ↦ (y,t)` over the padded edge `padEdge C 𝓗 e` (which has
`C ≥ 2` points), while a self-edge consists of copies of a single padded vertex. -/
theorem embEdge_inl_ne_inr {n C M : ℕ}
    {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {m : PV n C 𝓗 → ℕ} (hC : 2 ≤ C)
    (hedge : ∀ e : 𝓗, edgeSize (e : Set (Fin n)) ≤ C)
    (e : 𝓗) (t : Copy C M) (q : Σ v : PV n C 𝓗, Fin (m v) × ZMod M) :
    embEdge (𝓗 := 𝓗) (m := m) (Sum.inl (e, t)) ≠ embEdge (𝓗 := 𝓗) (m := m) (Sum.inr q) := by
  intro h
  have hsub : ∀ y ∈ padEdge C 𝓗 e, y = q.1 := by
    intro y hy
    have hmem : (y, t) ∈ embEdge (𝓗 := 𝓗) (m := m) (Sum.inr q) := by
      rw [← h, embEdge_inl]
      exact Set.mem_image_of_mem _ hy
    rw [embEdge_inr] at hmem
    exact (mem_selfEdge.mp hmem).1
  have hsub2 : padEdge C 𝓗 e ⊆ {q.1} := fun y hy => by
    rw [Set.mem_singleton_iff]
    exact hsub y hy
  have hle : (padEdge C 𝓗 e).ncard ≤ 1 := by
    have h1 := Set.ncard_le_ncard hsub2 (Set.finite_singleton q.1)
    rwa [Set.ncard_singleton] at h1
  rw [padEdge_ncard hedge e] at hle
  omega

/-- **The edge map of the embedding is injective.** -/
theorem embInj {n C M : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {m : PV n C 𝓗 → ℕ} [Fact M.Prime] (hC : 2 ≤ C) (hCM : C ≤ M)
    (hMm : ∀ v : PV n C 𝓗, m v ≤ M)
    (hedge : ∀ e : 𝓗, edgeSize (e : Set (Fin n)) ≤ C) :
    Function.Injective
      (embEdge (𝓗 := 𝓗) (m := m) : EmbIdx n C 𝓗 m M → Set (EmbVtx n C 𝓗 M)) := by
  intro i j hij
  have hne : ∀ e : 𝓗, (padEdge C 𝓗 e).Nonempty := by
    intro e
    refine Set.nonempty_of_ncard_ne_zero ?_
    rw [padEdge_ncard hedge e]
    omega
  rcases i with ⟨e, t⟩ | ⟨v, k, s⟩ <;> rcases j with ⟨e', t'⟩ | ⟨v', k', s'⟩
  · rw [embEdge_inl, embEdge_inl] at hij
    obtain ⟨y, hy⟩ := hne e
    have h1 : (y, t) ∈ (fun a : PV n C 𝓗 => (a, t')) '' padEdge C 𝓗 e' := by
      rw [← hij]
      exact Set.mem_image_of_mem _ hy
    have ht : t = t' := (mem_image_const.mp h1).2
    rw [ht] at hij
    have hpp : padEdge C 𝓗 e = padEdge C 𝓗 e' :=
      (Set.image_injective (f := fun a : PV n C 𝓗 => (a, t'))).mpr
        (fun a b h => congrArg Prod.fst h) hij
    have hee : e = e' := padEdge_injective hedge hpp
    rw [hee, ht]
  · exact absurd hij (embEdge_inl_ne_inr hC hedge e t ⟨v', k', s'⟩)
  · exact absurd hij.symm (embEdge_inl_ne_inr hC hedge e' t' ⟨v, k, s⟩)
  · rw [embEdge_inr, embEdge_inr] at hij
    obtain ⟨hv, hk, hs⟩ := selfEdge_eq_of hC hCM hij
    subst hv
    subst hs
    have hkk : k = k' := by
      apply Fin.ext
      have h2 : k.val % M = k'.val % M := (ZMod.natCast_eq_natCast_iff' k.val k'.val M).mp hk
      have h1 : k.val < M := lt_of_lt_of_le k.isLt (hMm _)
      have h2' : k'.val < M := lt_of_lt_of_le k'.isLt (hMm _)
      rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2'] at h2
      exact h2
    rw [hkk]

theorem kahnEmbedding : Work.Deep.Kahn.EmbeddingStatement := by
  intro n c 𝓗 L C D Λ hC hD hΛ hlin hedge hlist hdeg
  classical
  -- (1) the extended colour set and the injection of the colours
  set c' : ℕ := Λ * D * (c + 2 * Λ + 1 + D) * (Nat.card 𝓗 + 1) with hc'def
  have hc'le : c ≤ c' := by
    rw [hc'def]
    have hfac : 1 ≤ Λ * D * (Nat.card 𝓗 + 1) :=
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    calc c ≤ c + 2 * Λ + 1 + D := by omega
      _ = (c + 2 * Λ + 1 + D) * 1 := by ring
      _ ≤ (c + 2 * Λ + 1 + D) * (Λ * D * (Nat.card 𝓗 + 1)) :=
          Nat.mul_le_mul_left _ hfac
      _ = Λ * D * (c + 2 * Λ + 1 + D) * (Nat.card 𝓗 + 1) := by ring
  have hc'div : Λ ∣ c' * D := by
    rw [hc'def]
    exact ⟨D * D * (c + 2 * Λ + 1 + D) * (Nat.card 𝓗 + 1), by ring⟩
  let ρ : Fin c → Fin c' := Fin.castLE hc'le
  have hρ : Function.Injective ρ := Fin.castLE_injective hc'le
  -- (2) the colour degrees of the padding and the demands
  let dE : PV n C 𝓗 → Fin c' → ℕ :=
    fun v γ' => Nat.card {e : 𝓗 // v ∈ padEdge C 𝓗 e ∧ γ' ∈ (L e).image ρ}
  have hdEle : ∀ (v : PV n C 𝓗) (γ' : Fin c'), dE v γ' ≤ D :=
    fun v γ' => padColourDegLe (C := C) (D := D) (𝓗 := 𝓗) (L := L) hD hdeg hρ v γ'
  have hdEsum : ∀ v : PV n C 𝓗,
      ∑ γ' : Fin c', dE v γ' = Λ * Nat.card {e : 𝓗 // v ∈ padEdge C 𝓗 e} :=
    fun v => padColourDegSum (C := C) (Λ := Λ) (𝓗 := 𝓗) (L := L) hlist hρ v
  let Ndeg : PV n C 𝓗 → ℕ := fun v => Nat.card {e : 𝓗 // v ∈ padEdge C 𝓗 e}
  have hNle : ∀ v : PV n C 𝓗, Ndeg v ≤ Nat.card 𝓗 := by
    intro v
    show Nat.card {e : 𝓗 // v ∈ padEdge C 𝓗 e} ≤ Nat.card 𝓗
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_le _
  -- (3) the number of self-edges at a vertex
  let mf : PV n C 𝓗 → ℕ := fun v => c' * D / Λ - Ndeg v
  have hmul : ∀ v : PV n C 𝓗, Λ * mf v = c' * D - Λ * Ndeg v := by
    intro v
    show Λ * (c' * D / Λ - Ndeg v) = c' * D - Λ * Ndeg v
    rw [Nat.mul_sub_left_distrib, Nat.mul_div_cancel' hc'div]
  have hc'mul : c' * D = Λ * (D * D * (c + 2 * Λ + 1 + D) * (Nat.card 𝓗 + 1)) := by
    rw [hc'def]; ring
  have hbig : ∀ N : ℕ, D + N ≤ D * D * (c + 2 * Λ + 1 + D) * (N + 1) := by
    intro N
    have hDc : 1 ≤ D * (c + 2 * Λ + 1 + D) := by
      have h := Nat.mul_le_mul hD (show 1 ≤ c + 2 * Λ + 1 + D by omega)
      simpa using h
    have h2 : D + N ≤ D * (N + 1) := by
      have hN : N ≤ D * N := Nat.le_mul_of_pos_left N (by omega)
      have e : D * (N + 1) = D * N + D := by ring
      omega
    have h3 : D * (N + 1) ≤ D * (D * (c + 2 * Λ + 1 + D) * (N + 1)) :=
      Nat.mul_le_mul_left D (Nat.le_mul_of_pos_left (N + 1) (by omega))
    calc D + N ≤ D * (N + 1) := h2
      _ ≤ D * (D * (c + 2 * Λ + 1 + D) * (N + 1)) := h3
      _ = D * D * (c + 2 * Λ + 1 + D) * (N + 1) := by ring
  have hmge : ∀ v : PV n C 𝓗, D ≤ mf v := by
    intro v
    apply Nat.le_of_mul_le_mul_left _ (show 0 < Λ by omega)
    rw [hmul v, hc'mul]
    have hN := hNle v
    have hkey : D + Ndeg v ≤ D * D * (c + 2 * Λ + 1 + D) * (Nat.card 𝓗 + 1) := by
      have h1 := hbig (Nat.card 𝓗)
      omega
    have h2 : Λ * D + Λ * Ndeg v ≤
        Λ * (D * D * (c + 2 * Λ + 1 + D) * (Nat.card 𝓗 + 1)) := by
      rw [← Nat.mul_add]
      exact Nat.mul_le_mul_left Λ hkey
    omega
  -- (4) the lists of the self-edges
  let δ : (v : PV n C 𝓗) → Fin c' → ℕ := fun v γ' => D - dE v γ'
  have hδle : ∀ (v : PV n C 𝓗) (γ' : Fin c'), δ v γ' ≤ mf v := by
    intro v γ'
    have h1 := hdEle v γ'
    have h2 := hmge v
    show D - dE v γ' ≤ mf v
    omega
  have hδsum : ∀ v : PV n C 𝓗, ∑ γ' : Fin c', δ v γ' = Λ * mf v := by
    intro v
    show ∑ γ' : Fin c', (D - dE v γ') = Λ * mf v
    have h1 : ∀ γ' : Fin c', (D - dE v γ') + dE v γ' = D := fun γ' =>
      Nat.sub_add_cancel (hdEle v γ')
    have hsum_add : (∑ γ' : Fin c', ((D - dE v γ') + dE v γ')) = c' * D := by
      rw [Finset.sum_congr rfl (fun γ' _ => h1 γ')]
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have h2 : ∑ γ' : Fin c', (D - dE v γ')
        = (∑ γ' : Fin c', ((D - dE v γ') + dE v γ')) - ∑ γ' : Fin c', dE v γ' := by
      rw [Finset.sum_add_distrib]
      omega
    rw [h2, hsum_add, hdEsum v]
    exact (hmul v).symm
  have hdec : ∀ v : PV n C 𝓗, ∃ Γ : Fin (mf v) → Finset (Fin c'),
      (∀ k : Fin (mf v), (Γ k).card = Λ) ∧
      ∀ γ' : Fin c', (Finset.univ.filter (fun k : Fin (mf v) => γ' ∈ Γ k)).card = δ v γ' :=
    fun v => listDecomp c' Λ (mf v) (δ v) (hδsum v) (hδle v)
  let Γ : (v : PV n C 𝓗) → Fin (mf v) → Finset (Fin c') := fun v => Classical.choose (hdec v)
  have hΓcard : ∀ (v : PV n C 𝓗) (k : Fin (mf v)), (Γ v k).card = Λ :=
    fun v k => (Classical.choose_spec (hdec v)).1 k
  have hΓcount : ∀ (v : PV n C 𝓗) (γ' : Fin c'),
      (Finset.univ.filter (fun k : Fin (mf v) => γ' ∈ Γ v k)).card = δ v γ' :=
    fun v γ' => (Classical.choose_spec (hdec v)).2 γ'
  -- (5) a prime exceeding all the numbers of self-edges
  obtain ⟨M, hMge, hMprime⟩ := Nat.exists_infinite_primes (C + c' * D + 1)
  have hMC : C ≤ M := by omega
  have hMm : ∀ v : PV n C 𝓗, mf v ≤ M := by
    intro v
    have h1 : mf v ≤ c' * D := by
      show c' * D / Λ - Ndeg v ≤ c' * D
      exact le_trans (Nat.sub_le _ _) (Nat.div_le_self _ _)
    omega
  haveI : Fact M.Prime := ⟨hMprime⟩
  -- (6) the structural facts about the edge family
  have hInj := embInj (𝓗 := 𝓗) (m := mf) hC hMC hMm hedge
  have hLin := embLinear (𝓗 := 𝓗) (m := mf) hC hMC hMm hlin hedge
  have hDeg := embDeg (M := M) (C := C) (D := D) (c' := c') (𝓗 := 𝓗) (L := L) (ρ := ρ)
    (m := mf) (Γ := Γ) hΓcount hdEle
  -- (7) the transfer to `Fin n'`
  let n' : ℕ := Fintype.card (EmbVtx n C 𝓗 M)
  let φ : EmbVtx n C 𝓗 M ≃ Fin n' := Fintype.equivFin _
  let μ : EmbIdx n C 𝓗 mf M → Set (Fin n') := fun i => (embEdge (𝓗 := 𝓗) (m := mf) i).image φ
  have hμ : Function.Injective μ := by
    intro i j hij
    exact hInj ((Set.image_injective (f := φ)).mpr φ.injective hij)
  let eIdx : EmbIdx n C 𝓗 mf M ≃ Set.range μ := Equiv.ofInjective μ hμ
  let 𝓗' : ErdosFaberLovaszConjecture.Hypergraph (Fin n') := Set.range μ
  let L' : 𝓗' → Finset (Fin c') := fun E => embList (L := L) (ρ := ρ) Γ (eIdx.symm E)
  let t₀ : Copy C M := (⟨0, by omega⟩, 0)
  let emb : Fin n → Fin n' := fun x => φ (inlP n C 𝓗 x, t₀)
  let iota : 𝓗 → 𝓗' := fun e => eIdx (Sum.inl (e, t₀))
  have hinc : ∀ (x : Fin n) (e : 𝓗), x ∈ (e : Set (Fin n)) → emb x ∈ (iota e : Set (Fin n')) := by
    intro x e hx
    have h1 : (inlP n C 𝓗 x, t₀) ∈ embEdge (𝓗 := 𝓗) (m := mf) (Sum.inl (e, t₀)) := by
      rw [embEdge_inl]
      exact Set.mem_image_of_mem _ (Set.mem_union_left _ ⟨x, hx, rfl⟩)
    exact Set.mem_image_of_mem φ h1
  have hdegAll : ∀ (x' : Fin n') (γ' : Fin c'),
      Nat.card {E : 𝓗' // x' ∈ (E : Set (Fin n')) ∧ γ' ∈ L' E} = D := by
    intro x' γ'
    have hcount := hDeg (φ.symm x') γ'
    have hiff : ∀ E : 𝓗', (x' ∈ (E : Set (Fin n')) ∧ γ' ∈ L' E)
        ↔ (φ.symm x' ∈ embEdge (𝓗 := 𝓗) (m := mf) (eIdx.symm E)
            ∧ γ' ∈ embList (L := L) (ρ := ρ) Γ (eIdx.symm E)) := by
      intro E
      have hE : (E : Set (Fin n')) = μ (eIdx.symm E) :=
        (congrArg Subtype.val (eIdx.apply_symm_apply E)).symm
      constructor
      · rintro ⟨h1, h2⟩
        rw [hE] at h1
        obtain ⟨y, hy, hyx⟩ := h1
        refine ⟨?_, h2⟩
        rw [show φ.symm x' = y from by rw [← hyx, φ.symm_apply_apply]]
        exact hy
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rw [hE]
        have h3 := Set.mem_image_of_mem φ h1
        rwa [φ.apply_symm_apply] at h3
    have hcard : Nat.card {E : 𝓗' // x' ∈ (E : Set (Fin n')) ∧ γ' ∈ L' E}
        = Nat.card {i : EmbIdx n C 𝓗 mf M //
            φ.symm x' ∈ embEdge (𝓗 := 𝓗) (m := mf) i
              ∧ γ' ∈ embList (L := L) (ρ := ρ) Γ i} :=
      Nat.card_congr (Equiv.subtypeEquiv eIdx.symm hiff)
    rw [hcard, hcount]
  refine ⟨n', c', 𝓗', L', emb, iota, ρ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    exact Sum.inl_injective (congrArg Prod.fst (φ.injective hxy))
  · intro e f hef
    exact congrArg Prod.fst (Sum.inl_injective (eIdx.injective hef))
  · exact hρ
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    rw [← Set.image_inter (f := φ) φ.injective]
    exact (hLin i j (fun h => hij (by rw [h]))).image φ
  · rintro ⟨s, i, rfl⟩
    rw [edgeSize_eq_ncard, Set.ncard_image_of_injective _ φ.injective]
    exact embEdge_ncard hedge i
  · rintro ⟨s, i, rfl⟩
    change (embList (L := L) (ρ := ρ) Γ (eIdx.symm (eIdx i))).card = Λ
    rw [Equiv.symm_apply_apply]
    rcases i with ⟨e, t⟩ | ⟨q, k, s'⟩
    · rw [embList_inl, Finset.card_image_of_injective _ hρ, hlist e]
    · rw [embList_inr]
      exact hΓcard q k
  · intro e
    change embList (L := L) (ρ := ρ) Γ (eIdx.symm (eIdx (Sum.inl (e, t₀)))) = (L e).image ρ
    rw [Equiv.symm_apply_apply, embList_inl]
  · exact hinc
  · rintro e f _ ⟨x, hxe, hxf⟩
    exact ⟨emb x, hinc x e hxe, hinc x f hxf⟩
  · intro x' γ' _
    exact hdegAll x' γ'
  · intro x γ
    rw [hdegAll (emb x) (ρ γ)]
    exact hdeg x γ

end

end Work.Deep.Kahn
