import Submission.EFL.Reservoir
import Submission.Commons.Combinatorics.Matching.upper_regular_exists_injective

/-!
# Vertex absorption to extend colour classes (§7 of the paper)

This module formalises the absorbing machinery of §7.  An *absorber* `R` (a
set of 2-edges) can be used to extend a matching `M` so that the resulting
matching covers almost all vertices of `U = V_+^{(1-ε)}(G)`, where
`G = 𝓗^{(2)}`.  We record

* `absorberFam R U` — the family `𝓕(R) = {N_R(u) ∩ U} ∪ {N_R(u) ∖ U}`;
* `PseudoRandom M 𝓕 γ κ` — Definition `pseudorandom-matching-def`: a matching
  `M` is `(γ,κ)`-pseudorandom with respect to `𝓕` when
  `|S ∖ V(M)| = γ|S| ± κn` for every `S ∈ 𝓕`;
* `AbsorbableByPseudo`/`AbsorbableBySmall`/`AbsorbableByTypical` —
  Definition `def:absorbable` of `(𝓗, M, R, S)` being
  `(ρ,ε,γ,κ,ξ)`-absorbable (alternatives `AB-pseudo`, `AB-med`, `AB-huge`);

and we prove the two matching propositions of §7:

* `exists_matching_covering_of_upperRegular` — Proposition
  `crossing-matching-prop` in the form used by the crossing absorption lemma:
  an upper `(ρ,ξ)`-regular family of 2-edges in which every vertex of `A` has
  `≥ 2ρ|A|` neighbours in `B` has a matching covering `A`;
* `exists_matching_covering_of_greedy` — the greedy/Hall counterpart used
  when `A` is small.

The main statements of the section (Lemma `crossing-absorption-lemma`,
Lemma `internal-absorption-lemma`, Lemma `huge-edge-absorption-lemma` and
Lemma `difficult-edge-absorption`) are built on top of these.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-- Membership in `Finset.product`. -/
theorem mem_product_aux {α β : Type*} {s : Finset α} {t : Finset β} {p : α × β} :
    p ∈ s.product t ↔ p.1 ∈ s ∧ p.2 ∈ t := by
  rw [show s.product t = s ×ˢ t from rfl, Finset.mem_product]

/-! ## The family `𝓕(R)` and pseudorandomness -/

/-- `𝓕(R)`: the `R`-neighbourhoods of the vertices, split by `U`
(paper §7, Definition 7.4). -/
def absorberFam (R : Hypergraph (Fin n)) (U : Set (Fin n)) : Set (Set (Fin n)) :=
  {S : Set (Fin n) | (∃ u : Fin n, S = nbrs R u ∩ U) ∨ (∃ u : Fin n, S = nbrs R u \ U)}

/-- **Definition `pseudorandom-matching-def`.**  A matching `M` in `𝓗` is
`(γ,κ)`-pseudorandom with respect to a family `𝓕` of vertex sets if every
`S ∈ 𝓕` loses a `γ`-fraction of its vertices to `V(M)`, up to an error `κn`. -/
def PseudoRandom {𝓗 : Hypergraph (Fin n)} (M : Set 𝓗) (𝓕 : Set (Set (Fin n)))
    (γ κ : ℝ) : Prop :=
  ∀ S ∈ 𝓕, |(((S \ matchVert M).ncard : ℝ)) - γ * (S.ncard : ℝ)| ≤ κ * (n : ℝ)

/-! ## Definition `def:absorbable` -/

/-- **Definition `def:absorbable`, alternative `AB-pseudo`.**  `(𝓗, M, R, S)`
is absorbable by pseudorandomness of `M`. -/
def AbsorbableByPseudo (𝓗 : Hypergraph (Fin n)) (M : Set 𝓗) (R : Hypergraph (Fin n))
    (U S : Set (Fin n)) (ρ ε γ κ ξ : ℝ) : Prop :=
  (∃ 𝓥 : Set (Set (Fin n)), U ∈ 𝓥 ∧ (Set.univ : Set (Fin n)) ∈ 𝓥 ∧
      IsAbsorber (incidentTwo 𝓗 U) R 𝓥 ρ (10 * γ) ξ) ∧
    (∀ e ∈ M, (e : Set (Fin n)) ∉ R) ∧
    PseudoRandom M (absorberFam R U ∪ {U, S}) γ κ

/-- **Definition `def:absorbable`, alternative `AB-med`.**  `(𝓗, M, R, S)` is
absorbable by smallness of `M`. -/
def AbsorbableBySmall (𝓗 : Hypergraph (Fin n)) (M : Set 𝓗) (R : Hypergraph (Fin n))
    (U S : Set (Fin n)) (ρ ε γ κ ξ : ℝ) : Prop :=
  (∃ 𝓥 : Set (Set (Fin n)), U ∈ 𝓥 ∧ (Set.univ : Set (Fin n)) ∈ 𝓥 ∧
      IsAbsorber (incidentTwo 𝓗 U) R 𝓥 ρ (10 * γ) ξ) ∧
    (∀ e ∈ M, (e : Set (Fin n)) ∉ R) ∧
    (matchVert M).ncard ≤ γ * (n : ℝ)

/-- **Definition `def:absorbable`, alternative `AB-huge`.**  `R` is an
absorber for a family `𝓥` containing `U`, `V(𝓗)` (`univ`), `U ∪ V(M)` and
`U ∖ V(M)`; `M` avoids `R`; and `M` has at most `εn` vertices in `U`. -/
def AbsorbableByTypical (𝓗 : Hypergraph (Fin n)) (M : Set 𝓗) (R : Hypergraph (Fin n))
    (U S : Set (Fin n)) (ρ ε γ κ ξ : ℝ) : Prop :=
  ∃ 𝓥 : Set (Set (Fin n)), U ∈ 𝓥 ∧ (Set.univ : Set (Fin n)) ∈ 𝓥 ∧
    U ∪ matchVert M ∈ 𝓥 ∧ U \ matchVert M ∈ 𝓥 ∧
    IsAbsorber (incidentTwo 𝓗 U) R 𝓥 ρ (10 * γ) ξ ∧
    (∀ e ∈ M, (e : Set (Fin n)) ∉ R) ∧
    ((matchVert M ∩ U).ncard : ℝ) ≤ ε * (n : ℝ)

/-- **Definition `def:absorbable`.**  `(𝓗, M, R, S)` is
`(ρ,ε,γ,κ,ξ)`-absorbable (at least one of the three alternatives holds). -/
def Absorbable (𝓗 : Hypergraph (Fin n)) (M : Set 𝓗) (R : Hypergraph (Fin n))
    (U S : Set (Fin n)) (ρ ε γ κ ξ : ℝ) : Prop :=
  AbsorbableByPseudo 𝓗 M R U S ρ ε γ κ ξ ∨
    AbsorbableBySmall 𝓗 M R U S ρ ε γ κ ξ ∨
    AbsorbableByTypical 𝓗 M R U S ρ ε γ κ ξ

/-! ## Matchings: the vertex set of a family, unions -/

/-- Membership in the vertex set of a family of edges. -/
theorem mem_matchVert {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} {x : Fin n} :
    x ∈ matchVert M ↔ ∃ e ∈ M, x ∈ (e : Set (Fin n)) := by
  simp [matchVert]

/-- The vertex set of a family is monotone. -/
theorem matchVert_mono {𝓗 : Hypergraph (Fin n)} {M N : Set 𝓗} (h : M ⊆ N) :
    matchVert M ⊆ matchVert N := by
  intro x hx
  rw [mem_matchVert] at hx ⊢
  obtain ⟨e, he, hxe⟩ := hx
  exact ⟨e, h he, hxe⟩

/-- Every edge of a family is contained in its vertex set. -/
theorem subset_matchVert {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} {e : 𝓗} (he : e ∈ M) :
    (e : Set (Fin n)) ⊆ matchVert M := by
  intro x hx
  rw [mem_matchVert]
  exact ⟨e, he, hx⟩

/-- The vertex set of a union. -/
theorem matchVert_union {𝓗 : Hypergraph (Fin n)} (M N : Set 𝓗) :
    matchVert (M ∪ N) = matchVert M ∪ matchVert N := by
  ext x
  simp only [mem_matchVert, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ⟨e, he | he, hxe⟩
    · exact Or.inl ⟨e, he, hxe⟩
    · exact Or.inr ⟨e, he, hxe⟩
  · rintro (⟨e, he, hxe⟩ | ⟨e, he, hxe⟩)
    · exact ⟨e, Or.inl he, hxe⟩
    · exact ⟨e, Or.inr he, hxe⟩

/-- The union of two matchings with disjoint vertex sets is a matching. -/
theorem isMatching_union {𝓗 : Hypergraph (Fin n)} {M N : Set 𝓗}
    (hM : IsMatching 𝓗 M) (hN : IsMatching 𝓗 N)
    (hdisj : Disjoint (matchVert M) (matchVert N)) : IsMatching 𝓗 (M ∪ N) := by
  intro e₁ he₁ e₂ he₂ hne
  rcases he₁ with he₁ | he₁ <;> rcases he₂ with he₂ | he₂
  · exact hM he₁ he₂ hne
  · refine Set.disjoint_left.mpr (fun x hx1 hx2 => ?_)
    exact Set.disjoint_left.mp hdisj (subset_matchVert he₁ hx1) (subset_matchVert he₂ hx2)
  · refine Set.disjoint_left.mpr (fun x hx1 hx2 => ?_)
    exact Set.disjoint_left.mp hdisj (subset_matchVert he₂ hx2) (subset_matchVert he₁ hx1)
  · exact hN he₁ he₂ hne

/-- `Covers` is monotone in both arguments. -/
theorem Covers.mono {𝓗 : Hypergraph (Fin n)} {M N : Set 𝓗} {X Y : Set (Fin n)}
    (hMN : M ⊆ N) (hXY : Y ⊆ X) (h : Covers M X) : Covers N Y :=
  fun x hx => matchVert_mono hMN (h (hXY hx))

/-- The family of 2-edges `{a, f a}` obtained from an injective pairing
`f : A → B` with `A`, `B` disjoint is a matching. -/
theorem isMatching_pairImage {𝓗 : Hypergraph (Fin n)} {A B : Finset (Fin n)}
    (hAB : Disjoint A B) (f : {a // a ∈ A} → {b // b ∈ B})
    (hinj : Function.Injective f)
    (hmem : ∀ a : {a // a ∈ A}, ({a.1, (f a).1} : Set (Fin n)) ∈ 𝓗) :
    IsMatching 𝓗 {e : 𝓗 | ∃ a : {a // a ∈ A},
      (e : Set (Fin n)) = ({a.1, (f a).1} : Set (Fin n))} := by
  intro e₁ he₁ e₂ he₂ hne
  obtain ⟨a₁, ha₁⟩ := he₁
  obtain ⟨a₂, ha₂⟩ := he₂
  refine Set.disjoint_left.mpr (fun x hx₁ hx₂ => ?_)
  have hx₁' : x ∈ ({a₁.1, (f a₁).1} : Set (Fin n)) := by rw [← ha₁]; exact hx₁
  have hx₂' : x ∈ ({a₂.1, (f a₂).1} : Set (Fin n)) := by rw [← ha₂]; exact hx₂
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx₁' hx₂'
  have hfa : a₁.1 ≠ (f a₂).1 := fun h =>
    Finset.disjoint_left.mp hAB a₁.2 (h ▸ (f a₂).2)
  have hfb : (f a₁).1 ≠ a₂.1 := fun h =>
    Finset.disjoint_left.mp hAB a₂.2 (h ▸ (f a₁).2)
  rcases hx₁' with h1 | h1 <;> rcases hx₂' with h2 | h2
  · exact hne (Subtype.ext (by rw [ha₁, ha₂, Subtype.ext (h1.symm.trans h2)]))
  · exact hfa (h1.symm.trans h2)
  · exact hfb (h1.symm.trans h2)
  · exact hne (Subtype.ext (by
      rw [ha₁, ha₂, hinj (Subtype.ext (h1.symm.trans h2))]))

/-- The vertex set of the pair family `{a, f a}`. -/
theorem matchVert_pairImage {𝓗 : Hypergraph (Fin n)} {A B : Finset (Fin n)}
    (f : {a // a ∈ A} → {b // b ∈ B})
    (hmem : ∀ a : {a // a ∈ A}, ({a.1, (f a).1} : Set (Fin n)) ∈ 𝓗)
    {x : Fin n} :
    x ∈ matchVert {e : 𝓗 | ∃ a : {a // a ∈ A},
        (e : Set (Fin n)) = ({a.1, (f a).1} : Set (Fin n))} ↔
      (∃ a : {a // a ∈ A}, x = a.1) ∨ (∃ a : {a // a ∈ A}, x = (f a).1) := by
  rw [mem_matchVert]
  constructor
  · rintro ⟨e, he, hxe⟩
    obtain ⟨a, ha⟩ := he
    have hx : x ∈ ({a.1, (f a).1} : Set (Fin n)) := by rw [← ha]; exact hxe
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    exact hx.elim (fun h => Or.inl ⟨a, h⟩) (fun h => Or.inr ⟨a, h⟩)
  · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact ⟨⟨{a.1, (f a).1}, hmem a⟩, ⟨a, rfl⟩, by simp⟩
    · exact ⟨⟨{a.1, (f a).1}, hmem a⟩, ⟨a, rfl⟩, by simp⟩

/-! ## Two matching propositions of §7 -/

/-- A bijection between the product of two subtypes of finsets and the product
of the corresponding finsets. -/
private theorem filter_product_bij {A B : Finset (Fin n)} {P : Fin n → Fin n → Prop}
    [DecidableRel P] (S : Finset {a // a ∈ A}) (T : Finset {b // b ∈ B}) :
    ((S.product T).filter (fun p => P p.1.1 p.2.1)).card =
      (((S.image Subtype.val).product (T.image Subtype.val)).filter
        (fun p => P p.1 p.2)).card := by
  classical
  refine Finset.card_bij (fun p _ => (p.1.1, p.2.1)) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter, mem_product_aux] at hp
    obtain ⟨⟨hp1, hp2⟩, hpP⟩ := hp
    rw [Finset.mem_filter, mem_product_aux]
    exact ⟨⟨Finset.mem_image.mpr ⟨p.1, hp1, rfl⟩,
      Finset.mem_image.mpr ⟨p.2, hp2, rfl⟩⟩, hpP⟩
  · intro p hp q hq heq
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext (Subtype.ext heq.1) (Subtype.ext heq.2)
  · intro q hq
    rw [Finset.mem_filter, mem_product_aux] at hq
    obtain ⟨⟨hq1, hq2⟩, hqP⟩ := hq
    obtain ⟨a, ha, haeq⟩ := Finset.mem_image.mp hq1
    obtain ⟨b, hb, hbeq⟩ := Finset.mem_image.mp hq2
    refine ⟨(a, b), ?_, ?_⟩
    · rw [Finset.mem_filter, mem_product_aux]
      refine ⟨⟨ha, hb⟩, ?_⟩
      show P ↑a ↑b
      rw [haeq, hbeq]
      exact hqP
    · show (↑a, ↑b) = q
      exact Prod.ext haeq hbeq

/-- The card of the filtered product of two finsets equals `edgeCount`. -/
theorem filter_product_card_eq_edgeCount (R : Hypergraph (Fin n)) (S T : Finset (Fin n)) :
    ((S.product T).filter (fun p => ({p.1, p.2} : Set (Fin n)) ∈ R)).card = edgeCount R S T := by
  unfold edgeCount
  rfl

/-- **Proposition `crossing-matching-prop`** in the form used by the crossing
absorption lemma.  Here `A` is the part to be covered, `B` is the complement
of `A` (so that the two parts of the bipartite graph together have all `n`
vertices, matching the hypotheses of `upper_regular_exists_injective`), and
`VN` is the set of vertices already covered by the matching being extended.
The relation pairs `a ∈ A` with `b ∈ B ∖ VN` joined by an edge of `R`. -/
theorem exists_matching_covering_of_upperRegular {R : Hypergraph (Fin n)}
    {A VN : Finset (Fin n)} {ρ ξ : ℝ} (hρ : 0 < ρ) (hξ : 0 ≤ ξ) (hξρ : ξ ≤ ρ)
    (hdeg : ∀ a ∈ A, 2 * ρ * (A.card : ℝ) ≤
      ((((Finset.univ \ A) : Finset (Fin n)).filter
        (fun b => ({a, b} : Set (Fin n)) ∈ R ∧ b ∉ VN)).card : ℝ))
    (hcard : ξ * (n : ℝ) ≤ ρ * (A.card : ℝ))
    (hreg : ∀ S T : Finset (Fin n), Disjoint S T →
        ξ * (n : ℝ) ≤ (S.card : ℝ) → ξ * (n : ℝ) ≤ (T.card : ℝ) →
        (edgeCount R S T : ℝ) ≤ (ρ + ξ) * (S.card : ℝ) * (T.card : ℝ)) :
    ∃ f : {a // a ∈ A} → {b // b ∈ ((Finset.univ \ A) : Finset (Fin n))},
      Function.Injective f ∧
      ∀ a : {a // a ∈ A}, ({a.1, (f a).1} : Set (Fin n)) ∈ R ∧ (f a).1 ∉ VN := by
  classical
  set B : Finset (Fin n) := Finset.univ \ A with hB
  have hAcard : (Fintype.card {a // a ∈ A} : ℝ) = (A.card : ℝ) := by rw [Fintype.card_coe]
  have hBcard : (Fintype.card {b // b ∈ B} : ℝ) = (B.card : ℝ) := by rw [Fintype.card_coe]
  have hBsum : A.card + B.card = n := by
    have hAle : A.card ≤ n := by
      have := Finset.card_le_univ A
      rwa [Fintype.card_fin] at this
    rw [hB, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    omega
  have hABeq : ((Fintype.card {a // a ∈ A} + Fintype.card {b // b ∈ B} : ℕ) : ℝ) = (n : ℝ) := by
    rw [Fintype.card_coe, Fintype.card_coe, hBsum]
  have hdeg' : ∀ a : {a // a ∈ A}, 2 * ρ * (Fintype.card {a // a ∈ A} : ℝ) ≤
      ((Finset.univ.filter (fun b : {b // b ∈ B} =>
        (({a.1, b.1} : Set (Fin n)) ∈ R ∧ b.1 ∉ VN))).card : ℝ) := by
    intro a
    have h1 := hdeg a.1 a.2
    have hbij : (Finset.univ.filter (fun b : {b // b ∈ B} =>
        (({a.1, b.1} : Set (Fin n)) ∈ R ∧ b.1 ∉ VN))).card =
        (B.filter (fun b => ({a.1, b} : Set (Fin n)) ∈ R ∧ b ∉ VN)).card := by
      refine Finset.card_bij (fun b _ => b.1) ?_ ?_ ?_
      · intro b hb
        rw [Finset.mem_filter] at hb ⊢
        exact ⟨b.2, hb.2⟩
      · intro b _ b' _ heq
        exact Subtype.ext heq
      · intro b hb
        rw [Finset.mem_filter] at hb
        exact ⟨⟨b, hb.1⟩, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hb.2⟩, rfl⟩
    rw [hbij, hAcard]
    rw [hB]
    exact h1
  have hcard' : ξ * ((Fintype.card {a // a ∈ A} + Fintype.card {b // b ∈ B} : ℕ) : ℝ) ≤
      ρ * (Fintype.card {a // a ∈ A} : ℝ) := by
    rw [hABeq, hAcard]
    exact hcard
  have hreg' : ∀ (S : Finset {a // a ∈ A}) (T : Finset {b // b ∈ B}),
      ξ * ((Fintype.card {a // a ∈ A} + Fintype.card {b // b ∈ B} : ℕ) : ℝ) ≤ (S.card : ℝ) →
      ξ * ((Fintype.card {a // a ∈ A} + Fintype.card {b // b ∈ B} : ℕ) : ℝ) ≤ (T.card : ℝ) →
      (((S.product T).filter (fun p =>
        (({p.1.1, p.2.1} : Set (Fin n)) ∈ R ∧ p.2.1 ∉ VN))).card : ℝ) ≤
        (ρ + ξ) * (S.card : ℝ) * (T.card : ℝ) := by
    intro S T hS hT
    rw [hABeq] at hS hT
    have hScard : (S.image Subtype.val).card = S.card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    have hTcard : (T.image Subtype.val).card = T.card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    have hSn : ξ * (n : ℝ) ≤ ((S.image Subtype.val).card : ℝ) := by rw [hScard]; exact hS
    have hTn : ξ * (n : ℝ) ≤ ((T.image Subtype.val).card : ℝ) := by rw [hTcard]; exact hT
    have hdisj : Disjoint (S.image Subtype.val) (T.image Subtype.val) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hbT, hb⟩ := Finset.mem_image.mp hx'
      have hbB : (b.1 : Fin n) ∈ B := b.2
      rw [hb, hB, Finset.mem_sdiff] at hbB
      exact hbB.2 a.2
    have hbound := hreg (S.image Subtype.val) (T.image Subtype.val) hdisj hSn hTn
    have hmono : ((S.product T).filter (fun p =>
        (({p.1.1, p.2.1} : Set (Fin n)) ∈ R ∧ p.2.1 ∉ VN))).card ≤
        ((S.product T).filter (fun p => ({p.1.1, p.2.1} : Set (Fin n)) ∈ R)).card := by
      refine Finset.card_le_card (fun p hp => ?_)
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, hp.2.1⟩
    have hbij := filter_product_bij (n := n) (A := A) (B := B)
      (P := fun a b => ({a, b} : Set (Fin n)) ∈ R) S T
    rw [hbij] at hmono
    rw [← filter_product_card_eq_edgeCount (R := R)
      (S := S.image Subtype.val) (T := T.image Subtype.val)] at hbound
    rw [hScard, hTcard] at hbound
    have hmono' : (((S.product T).filter (fun p =>
        (({p.1.1, p.2.1} : Set (Fin n)) ∈ R ∧ p.2.1 ∉ VN))).card : ℝ) ≤
        ((((S.image Subtype.val).product (T.image Subtype.val)).filter
          (fun p => ({p.1, p.2} : Set (Fin n)) ∈ R)).card : ℝ) := by exact_mod_cast hmono
    linarith [hmono', hbound]
  obtain ⟨f, hfinj, hf⟩ := Commons.Combinatorics.Matching.upper_regular_exists_injective
    (fun a : {a // a ∈ A} => fun b : {b // b ∈ B} =>
      (({a.1, b.1} : Set (Fin n)) ∈ R ∧ b.1 ∉ VN)) hρ hξ hξρ hdeg' hcard' hreg'
  exact ⟨fun a => ⟨(f a).1, (f a).2⟩, fun a b hab => hfinj (Subtype.ext (congrArg Subtype.val hab)),
    fun a => (hf a)⟩

/-- **Greedy/Hall counterpart.**  If every `a ∈ A` has strictly more than
`|A|` neighbours in `B` then there is a matching covering `A` (Hall's
condition holds trivially). -/
theorem exists_matching_covering_of_greedy {R : Hypergraph (Fin n)}
    {A B : Finset (Fin n)}
    (hdeg : ∀ a ∈ A, A.card < (B.filter (fun b => ({a, b} : Set (Fin n)) ∈ R)).card) :
    ∃ f : {a // a ∈ A} → {b // b ∈ B}, Function.Injective f ∧
      ∀ a : {a // a ∈ A}, ({a.1, (f a).1} : Set (Fin n)) ∈ R := by
  classical
  set N : {a // a ∈ A} → Finset {b // b ∈ B} :=
    fun a => Finset.univ.filter (fun b : {b // b ∈ B} => ({a.1, b.1} : Set (Fin n)) ∈ R)
    with hN
  have hNB : ∀ (a : {a // a ∈ A}) (b : {b // b ∈ B}),
      b ∈ N a ↔ ({a.1, b.1} : Set (Fin n)) ∈ R := by
    intro a b
    rw [hN, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hbcard : ∀ a : {a // a ∈ A}, (N a).card =
      (B.filter (fun b => ({a.1, b} : Set (Fin n)) ∈ R)).card := by
    intro a
    refine Finset.card_bij (fun b _ => b.1) ?_ ?_ ?_
    · intro b hb
      rw [hNB] at hb
      rw [Finset.mem_filter]
      exact ⟨b.2, hb⟩
    · intro b _ b' _ heq
      exact Subtype.ext heq
    · intro b hb
      rw [Finset.mem_filter] at hb
      exact ⟨⟨b, hb.1⟩, by rw [hNB]; exact hb.2, rfl⟩
  have hall : ∀ S : Finset {a // a ∈ A}, S.card ≤ (S.biUnion N).card := by
    intro S
    by_cases hS : S.Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty] at hS
      rw [hS]
      simp
    obtain ⟨a₀, ha₀⟩ := hS
    have hNsub : N a₀ ⊆ S.biUnion N := fun b hb => Finset.mem_biUnion.mpr ⟨a₀, ha₀, hb⟩
    have h1 : A.card < (N a₀).card := by
      rw [hbcard a₀]
      exact hdeg a₀.1 a₀.2
    have h2 : (N a₀).card ≤ (S.biUnion N).card := Finset.card_le_card hNsub
    have h3 : S.card ≤ A.card := by
      have := Finset.card_le_univ S
      rwa [Fintype.card_coe] at this
    exact le_trans (le_of_lt (lt_of_le_of_lt h3 h1)) h2
  obtain ⟨f, hfinj, hf⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective N).mp hall
  exact ⟨f, hfinj, fun a => (hNB a (f a)).mp (hf a)⟩

end

end ErdosFaberLovaszConjecture
