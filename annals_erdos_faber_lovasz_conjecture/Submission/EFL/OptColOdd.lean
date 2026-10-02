import Submission.EFL.OptCol

/-!
# The odd case of Corollary 10.13

The paper derives Corollary 10.13 (`cor:optcol`) from the Glock–Kühn–Osthus
theorem (Theorem 10.8), whose statement requires an *even* number of
vertices.  For odd `n` the paper adds a new vertex `v*` joined to exactly
`t := ⌊Δ(G) - 2ηn⌋` vertices of degree less than `Δ(G)`, obtaining a graph
`G*` on an even number of vertices with `Δ(G*) = Δ(G)`,
`δ(G*) = d_{G*}(v*) = t`, `Δ(G*) - δ(G*) ≤ 3η v(G*)`, satisfying the
`(def_ineq)` condition at `v*`, and lower `(p/4, 2ε)`-regular (by LR2 with
`α = 1/2`).  Theorem 10.8 applied to `G*` then yields a `Δ(G)`-colouring of
`G*`, whose restriction to `G` is the desired colouring.

This module formalises that reduction: `famImage`/`extendVertex` (the image
of a hypergraph under an injective vertex map, and the operation of adding a
new vertex), the degree/max-degree bookkeeping, the lower-regularity
transport, and finally `optcol_corollary_odd` together with the parity-free
`optcol_corollary`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## Images of a hypergraph under an injective vertex map -/

/-- The image `f '' 𝓖` of a hypergraph `𝓖` on `Fin n` under a map `f` of the
ground set. -/
def famImage {m : ℕ} (f : Fin n → Fin m) (𝓖 : Hypergraph (Fin n)) : Hypergraph (Fin m) :=
  {e : Set (Fin m) | ∃ e₀ ∈ 𝓖, f '' e₀ = e}

theorem mem_famImage {m : ℕ} {f : Fin n → Fin m} {𝓖 : Hypergraph (Fin n)}
    {e : Set (Fin m)} : e ∈ famImage f 𝓖 ↔ ∃ e₀ ∈ 𝓖, f '' e₀ = e := Iff.rfl

theorem edgeSize_famImage {m : ℕ} {f : Fin n → Fin m} (hf : Function.Injective f)
    {e₀ : Set (Fin n)} : edgeSize (f '' e₀ : Set (Fin m)) = edgeSize e₀ := by
  rw [edgeSize_eq_ncard, edgeSize_eq_ncard, Set.ncard_image_of_injective _ hf]

/-- Colourings transfer from an image family back to the original family. -/
theorem colorable_famImage {m : ℕ} {f : Fin n → Fin m} (hf : Function.Injective f)
    (𝓖 : Hypergraph (Fin n)) (k : ℕ) : (famImage f 𝓖).Colorable k → 𝓖.Colorable k := by
  rintro ⟨φ⟩
  refine ⟨⟨fun e => φ.labels ⟨f '' (e : Set (Fin n)),
    mem_famImage.mpr ⟨e, e.2, rfl⟩⟩, ?_⟩⟩
  intro e₁ e₂ hne hinter
  refine φ.isColoring _ _ ?_ ?_
  · intro hcon
    have himg : (f '' (e₁ : Set (Fin n))) = f '' (e₂ : Set (Fin n)) :=
      congrArg (fun x : famImage f 𝓖 => (x : Set (Fin m))) hcon
    have hset : (e₁ : Set (Fin n)) = e₂ := Set.image_injective.mpr hf himg
    exact hne (Subtype.ext hset)
  · rcases hinter with ⟨x, hx1, hx2⟩
    exact ⟨f x, ⟨x, hx1, rfl⟩, ⟨x, hx2, rfl⟩⟩

/-! ## Adding a new vertex to a 2-graph -/

/-- Add a new vertex `Fin.last n` to the 2-graph `𝓖`, joined exactly to the
vertices of `T`. -/
def extendVertex (𝓖 : Hypergraph (Fin n)) (T : Finset (Fin n)) : Hypergraph (Fin (n+1)) :=
  famImage Fin.castSucc 𝓖 ∪
    {e : Set (Fin (n+1)) | ∃ u ∈ T, e = ({Fin.castSucc u, Fin.last n} : Set (Fin (n+1)))}

theorem mem_extendVertex {𝓖 : Hypergraph (Fin n)} {T : Finset (Fin n)} {e : Set (Fin (n+1))} :
    e ∈ extendVertex 𝓖 T ↔
      (∃ e₀ ∈ 𝓖, Fin.castSucc '' e₀ = e) ∨
        (∃ u ∈ T, e = ({Fin.castSucc u, Fin.last n} : Set (Fin (n+1)))) := by
  simp only [extendVertex, Set.mem_union, Set.mem_setOf_eq, mem_famImage]

/-- Membership of the new vertex in the neighbourhood of an old vertex. -/
theorem mem_nbrs_extendVertex_castSucc {𝓖 : Hypergraph (Fin n)} {T : Finset (Fin n)}
    {u : Fin n} {w : Fin (n+1)} (hn : 1 ≤ n) :
    w ∈ nbrs (extendVertex 𝓖 T) (Fin.castSucc u) ↔
      (∃ w' : Fin n, Fin.castSucc w' = w ∧ ({u, w'} : Set (Fin n)) ∈ 𝓖) ∨
        (w = Fin.last n ∧ u ∈ T) := by
  change ({Fin.castSucc u, w} : Set (Fin (n+1))) ∈ extendVertex 𝓖 T ↔ _
  rw [mem_extendVertex]
  constructor
  · rintro (⟨e₀, he₀, heq⟩ | ⟨u', hu', heq⟩)
    · left
      have hw : w ∈ (Fin.castSucc '' e₀ : Set (Fin (n+1))) := by rw [heq]; simp
      obtain ⟨w', hw'e₀, hw'eq⟩ := hw
      refine ⟨w', hw'eq, ?_⟩
      have h2 : (Fin.castSucc '' e₀ : Set (Fin (n+1))) =
          Fin.castSucc '' ({u, w'} : Set (Fin n)) := by
        rw [heq, ← hw'eq, Set.image_pair]
      exact Set.image_injective.mpr (Fin.castSucc_injective n) h2 ▸ he₀
    · right
      have h1 : Fin.castSucc u ∈ ({Fin.castSucc u', Fin.last n} : Set (Fin (n+1))) := by
        rw [← heq]; simp
      have hlast : Fin.last n ∈ ({Fin.castSucc u, w} : Set (Fin (n+1))) := by
        rw [heq]; simp
      rcases h1 with h1 | h1
      · have hu : u = u' := Fin.castSucc_injective n h1
        rcases hlast with hlast | hlast
        · exact absurd hlast.symm (Fin.castSucc_ne_last u)
        · exact ⟨hlast.symm, hu ▸ hu'⟩
      · exact absurd h1 (Fin.castSucc_ne_last u)
  · rintro (⟨w', hw'eq, hmem⟩ | ⟨hw', hu'⟩)
    · left
      exact ⟨({u, w'} : Set (Fin n)), hmem, by rw [← hw'eq, Set.image_pair]⟩
    · right
      exact ⟨u, hu', by rw [hw']⟩

/-- The neighbourhood of the new vertex. -/
theorem mem_nbrs_extendVertex_last {𝓖 : Hypergraph (Fin n)} {T : Finset (Fin n)}
    {w : Fin (n+1)} (hn : 1 ≤ n) :
    w ∈ nbrs (extendVertex 𝓖 T) (Fin.last n) ↔ ∃ u ∈ T, w = Fin.castSucc u := by
  change ({Fin.last n, w} : Set (Fin (n+1))) ∈ extendVertex 𝓖 T ↔ _
  rw [mem_extendVertex]
  constructor
  · rintro (⟨e₀, he₀, heq⟩ | ⟨u, hu, heq⟩)
    · have hmem : Fin.last n ∈ (Fin.castSucc '' e₀ : Set (Fin (n+1))) := by rw [heq]; simp
      obtain ⟨x, -, hx⟩ := hmem
      exact absurd hx (Fin.castSucc_ne_last x)
    · have hmem : w ∈ ({Fin.castSucc u, Fin.last n} : Set (Fin (n+1))) := by rw [← heq]; simp
      rcases hmem with h | h
      · exact ⟨u, hu, h⟩
      · exfalso
        have h2 : Fin.castSucc u ∈ ({Fin.last n, w} : Set (Fin (n+1))) := by rw [heq]; simp
        rcases h2 with h2 | h2
        · exact absurd h2 (Fin.castSucc_ne_last u)
        · exact absurd (h2.trans h) (Fin.castSucc_ne_last u)
  · rintro ⟨u, hu, rfl⟩
    right
    exact ⟨u, hu, by simp [Set.pair_comm]⟩

theorem nbrs_extendVertex_castSucc_eq (𝓖 : Hypergraph (Fin n)) (T : Finset (Fin n))
    (u : Fin n) (hn : 1 ≤ n) :
    nbrs (extendVertex 𝓖 T) (Fin.castSucc u) =
      Fin.castSucc '' nbrs 𝓖 u ∪ (if u ∈ T then {Fin.last n} else ∅) := by
  classical
  ext w
  rw [mem_nbrs_extendVertex_castSucc (𝓖 := 𝓖) (T := T) (u := u) hn, Set.mem_union,
    Set.mem_image, nbrs]
  constructor
  · rintro (⟨w', hw', hmem⟩ | ⟨hlast, hT⟩)
    · exact Or.inl ⟨w', hmem, hw'⟩
    · exact Or.inr (by rw [if_pos hT]; exact hlast)
  · rintro (⟨w', hmem, hw'⟩ | h2)
    · exact Or.inl ⟨w', hw', hmem⟩
    · by_cases hT : u ∈ T
      · rw [if_pos hT, Set.mem_singleton_iff] at h2
        exact Or.inr ⟨h2, hT⟩
      · rw [if_neg hT] at h2
        exact absurd h2 (Set.notMem_empty _)

theorem degAt_extendVertex_castSucc (𝓖 : Hypergraph (Fin n)) (T : Finset (Fin n))
    (u : Fin n) (hn : 1 ≤ n) :
    degAt (extendVertex 𝓖 T) (Fin.castSucc u) = degAt 𝓖 u + (if u ∈ T then 1 else 0) := by
  classical
  have hdisj : Disjoint (Fin.castSucc '' nbrs 𝓖 u)
      ((if u ∈ T then ({Fin.last n} : Set (Fin (n+1))) else ∅)) := by
    rw [Set.disjoint_left]
    intro x hx hx2
    obtain ⟨y, -, rfl⟩ := hx
    by_cases hT : u ∈ T
    · rw [if_pos hT, Set.mem_singleton_iff] at hx2
      exact absurd hx2 (Fin.castSucc_ne_last y)
    · rw [if_neg hT] at hx2
      exact absurd hx2 (Set.notMem_empty _)
  simp only [degAt]
  rw [nbrs_extendVertex_castSucc_eq 𝓖 T u hn, Set.ncard_union_eq hdisj,
    Set.ncard_image_of_injective _ (Fin.castSucc_injective n)]
  by_cases hT : u ∈ T
  · rw [if_pos hT, Set.ncard_singleton, if_pos hT]
  · rw [if_neg hT, Set.ncard_empty, if_neg hT]

theorem degAt_extendVertex_last (𝓖 : Hypergraph (Fin n)) (T : Finset (Fin n)) (hn : 1 ≤ n) :
    degAt (extendVertex 𝓖 T) (Fin.last n) = T.card := by
  classical
  have hset : nbrs (extendVertex 𝓖 T) (Fin.last n) = Fin.castSucc '' (T : Set (Fin n)) := by
    ext w
    rw [mem_nbrs_extendVertex_last (𝓖 := 𝓖) (T := T) hn, Set.mem_image]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
  simp only [degAt]
  rw [hset, Set.ncard_image_of_injective _ (Fin.castSucc_injective n),
    Set.ncard_coe_finset (s := T)]

theorem edgeSize_extendVertex {𝓖 : Hypergraph (Fin n)} {T : Finset (Fin n)}
    (h2 : ∀ e ∈ 𝓖, edgeSize e = 2) (hn : 1 ≤ n) {e : Set (Fin (n+1))}
    (he : e ∈ extendVertex 𝓖 T) : edgeSize e = 2 := by
  rw [mem_extendVertex] at he
  rcases he with ⟨e₀, he₀, rfl⟩ | ⟨u, hu, rfl⟩
  · rw [edgeSize_famImage (Fin.castSucc_injective n)]
    exact h2 e₀ he₀
  · rw [edgeSize_eq_ncard, Set.ncard_pair (Fin.castSucc_ne_last u)]

/-! ## The maximum degree of the extended graph -/

theorem hypergraphDegree_extendVertex_castSucc {𝓖 : Hypergraph (Fin n)} {T : Finset (Fin n)}
    (h2 : ∀ e ∈ 𝓖, edgeSize e = 2) {u : Fin n} (hn : 1 ≤ n) :
    hypergraphDegree (extendVertex 𝓖 T) (Fin.castSucc u) =
      degAt 𝓖 u + (if u ∈ T then 1 else 0) := by
  rw [← ncard_nbrs_eq_hypergraphDegree (G := extendVertex 𝓖 T)
    (fun e he => edgeSize_extendVertex (𝓖 := 𝓖) (T := T) h2 hn he) (Fin.castSucc u)]
  exact degAt_extendVertex_castSucc 𝓖 T u hn

theorem hypergraphDegree_extendVertex_last {𝓖 : Hypergraph (Fin n)} {T : Finset (Fin n)}
    (h2 : ∀ e ∈ 𝓖, edgeSize e = 2) (hn : 1 ≤ n) :
    hypergraphDegree (extendVertex 𝓖 T) (Fin.last n) = T.card := by
  rw [← ncard_nbrs_eq_hypergraphDegree (G := extendVertex 𝓖 T)
    (fun e he => edgeSize_extendVertex (𝓖 := 𝓖) (T := T) h2 hn he) (Fin.last n)]
  exact degAt_extendVertex_last 𝓖 T hn

/-- `extendVertex` does not change the maximum degree, provided the new
neighbourhood `T` consists of vertices whose degree is strictly smaller than
the maximum degree. -/
theorem hypergraphMaxDegree_extendVertex {𝓖 : Hypergraph (Fin n)} {T : Finset (Fin n)}
    (h2 : ∀ e ∈ 𝓖, edgeSize e = 2) (hn : 1 ≤ n)
    (hT : ∀ u ∈ T, degAt 𝓖 u < hypergraphMaxDegree 𝓖)
    (hTcard : T.card ≤ hypergraphMaxDegree 𝓖) :
    hypergraphMaxDegree (extendVertex 𝓖 T) = hypergraphMaxDegree 𝓖 := by
  classical
  set Δ := hypergraphMaxDegree 𝓖 with hΔ
  have hsupG : Δ = (Finset.univ : Finset (Fin n)).sup (fun u => degAt 𝓖 u) :=
    hypergraphMaxDegree_eq_sup 𝓖 h2
  obtain ⟨u₀, -, hu₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun u => degAt 𝓖 u) (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
  have hu₀eq : degAt 𝓖 u₀ = Δ := by
    rw [hsupG]
    exact le_antisymm (Finset.le_sup (Finset.mem_univ u₀)) (Finset.sup_le hu₀)
  have hle : hypergraphMaxDegree (extendVertex 𝓖 T) ≤ Δ := by
    rw [hypergraphMaxDegree]
    refine Finset.sup_le (fun v _ => ?_)
    rcases lt_or_ge v.val n with hv | hv
    · have hvcast : Fin.castSucc (⟨v.val, hv⟩ : Fin n) = v := by
        ext; simp [Fin.castSucc]
      rw [← hvcast, hypergraphDegree_extendVertex_castSucc h2 hn]
      by_cases huT : (⟨v.val, hv⟩ : Fin n) ∈ T
      · rw [if_pos huT]
        have := hT _ huT
        omega
      · rw [if_neg huT, add_zero]
        exact degAt_le_maxDegree 𝓖 h2 ⟨v.val, hv⟩
    · have hvlast : v = Fin.last n := by
        ext
        simp only [Fin.val_last]
        omega
      rw [hvlast, hypergraphDegree_extendVertex_last h2 hn]
      exact hTcard
  have hge : Δ ≤ hypergraphMaxDegree (extendVertex 𝓖 T) := by
    have hnotmem : u₀ ∉ T := by
      intro hmem
      have := hT u₀ hmem
      rw [hu₀eq] at this
      exact lt_irrefl _ this
    have hd := hypergraphDegree_extendVertex_castSucc (𝓖 := 𝓖) (T := T) h2 (u := u₀) hn
    rw [if_neg hnotmem, hu₀eq, add_zero] at hd
    rw [← hd]
    exact hypergraphDegree_le_maxDegree _ _
  exact le_antisymm hle hge


/-! ## Degree bound in the extended graph -/

theorem degAt_extendVertex_le_max {𝓖 : Hypergraph (Fin n)} {T : Finset (Fin n)}
    (h2 : ∀ e ∈ 𝓖, edgeSize e = 2) (hn : 1 ≤ n)
    (hT : ∀ u ∈ T, degAt 𝓖 u < hypergraphMaxDegree 𝓖)
    (hTcard : T.card ≤ hypergraphMaxDegree 𝓖) (v : Fin (n+1)) :
    degAt (extendVertex 𝓖 T) v ≤ hypergraphMaxDegree 𝓖 := by
  rcases lt_or_ge v.val n with hv | hv
  · have hvcast : Fin.castSucc (⟨v.val, hv⟩ : Fin n) = v := by ext; simp [Fin.castSucc]
    rw [← hvcast, degAt_extendVertex_castSucc 𝓖 T _ hn]
    by_cases huT : (⟨v.val, hv⟩ : Fin n) ∈ T
    · rw [if_pos huT]
      have := hT _ huT
      omega
    · rw [if_neg huT, add_zero]
      exact degAt_le_maxDegree 𝓖 h2 _
  · have hvlast : v = Fin.last n := by
      ext
      simp only [Fin.val_last]
      omega
    rw [hvlast, degAt_extendVertex_last 𝓖 T hn]
    exact hTcard

/-! ## Transporting lower regularity to the image family -/

/-- The vertices of `Fin n` whose `Fin.castSucc`-image lies in `A`. -/
def castSuccFinset (A : Finset (Fin (n+1))) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun a => Fin.castSucc a ∈ A)

theorem mem_castSuccFinset {A : Finset (Fin (n+1))} {a : Fin n} :
    a ∈ castSuccFinset A ↔ Fin.castSucc a ∈ A := by
  simp [castSuccFinset]

theorem castSuccFinset_image {A : Finset (Fin (n+1))}
    (hA : ∀ a ∈ A, ∃ a' : Fin n, Fin.castSucc a' = a) :
    (castSuccFinset A).image Fin.castSucc = A := by
  ext a
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a', ha', rfl⟩
    exact mem_castSuccFinset.mp ha'
  · intro ha
    obtain ⟨a', rfl⟩ := hA a ha
    exact ⟨a', mem_castSuccFinset.mpr (by simpa using ha), rfl⟩

theorem card_castSuccFinset {A : Finset (Fin (n+1))}
    (hA : ∀ a ∈ A, ∃ a' : Fin n, Fin.castSucc a' = a) :
    (castSuccFinset A).card = A.card := by
  have h := Finset.card_image_of_injective (s := castSuccFinset A)
    (f := Fin.castSucc) (Fin.castSucc_injective n)
  rw [castSuccFinset_image hA] at h
  exact h.symm

/-- `edgeCount` between two `castSucc`-sets is transported to the original
vertex set. -/
theorem edgeCount_famImage_castSucc {𝓖 : Hypergraph (Fin n)} {A B : Finset (Fin (n+1))}
    (hA : ∀ a ∈ A, ∃ a' : Fin n, Fin.castSucc a' = a)
    (hB : ∀ b ∈ B, ∃ b' : Fin n, Fin.castSucc b' = b) :
    edgeCount (famImage Fin.castSucc 𝓖) A B =
      edgeCount 𝓖 (castSuccFinset A) (castSuccFinset B) := by
  classical
  have hmain : (((castSuccFinset A).product (castSuccFinset B)).filter
        (fun p : Fin n × Fin n => ({p.1, p.2} : Set (Fin n)) ∈ 𝓖)).card =
      (((A.product B).filter (fun p : Fin (n+1) × Fin (n+1) =>
        ({p.1, p.2} : Set (Fin (n+1))) ∈ famImage Fin.castSucc 𝓖))).card := by
    refine Finset.card_bij (fun p _ => (Fin.castSucc p.1, Fin.castSucc p.2)) ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_filter, mem_product'] at hp
      obtain ⟨⟨hp1, hp2⟩, hpR⟩ := hp
      rw [Finset.mem_filter, mem_product']
      refine ⟨⟨mem_castSuccFinset.mp hp1, mem_castSuccFinset.mp hp2⟩, ?_⟩
      exact mem_famImage.mpr ⟨({p.1, p.2} : Set (Fin n)), hpR, Set.image_pair ..⟩
    · intro p hp q hq heq
      simp only [Prod.mk.injEq] at heq
      exact Prod.ext (Fin.castSucc_injective n heq.1) (Fin.castSucc_injective n heq.2)
    · intro q hq
      rw [Finset.mem_filter, mem_product'] at hq
      obtain ⟨⟨hq1, hq2⟩, hqR⟩ := hq
      obtain ⟨a', ha'⟩ := hA q.1 hq1
      obtain ⟨b', hb'⟩ := hB q.2 hq2
      rw [mem_famImage] at hqR
      obtain ⟨e₀, he₀, heq⟩ := hqR
      have hset : e₀ = ({a', b'} : Set (Fin n)) := by
        refine Set.image_injective.mpr (Fin.castSucc_injective n) ?_
        rw [heq, Set.image_pair, ha', hb']
      refine ⟨(a', b'), ?_, Prod.ext ha' hb'⟩
      rw [Finset.mem_filter, mem_product']
      exact ⟨⟨mem_castSuccFinset.mpr (by rw [ha']; exact hq1),
        mem_castSuccFinset.mpr (by rw [hb']; exact hq2)⟩, by rw [← hset]; exact he₀⟩
  unfold edgeCount
  rw [hmain]

/-- Lower regularity of a subgraph is inherited by its image under
`Fin.castSucc`. -/
theorem selfLowerRegular_famImage_castSucc {𝓖 : Hypergraph (Fin n)} {X : Set (Fin n)}
    {ρ ξ : ℝ} (hlr : SelfLowerRegular 𝓖 X ρ ξ) :
    SelfLowerRegular (famImage Fin.castSucc 𝓖) (Fin.castSucc '' X) ρ ξ := by
  classical
  intro A B hA hB hdisj hAc hBc
  have hA' : ∀ a ∈ A, ∃ a' : Fin n, Fin.castSucc a' = a := by
    intro a ha
    obtain ⟨x, -, hxa⟩ := hA a ha
    exact ⟨x, hxa⟩
  have hB' : ∀ b ∈ B, ∃ b' : Fin n, Fin.castSucc b' = b := by
    intro b hb
    obtain ⟨x, -, hxb⟩ := hB b hb
    exact ⟨x, hxb⟩
  have hA₀ : ∀ a ∈ castSuccFinset A, a ∈ X := by
    intro a ha
    have h1 : Fin.castSucc a ∈ A := mem_castSuccFinset.mp ha
    obtain ⟨x, hxX, hxa⟩ := hA (Fin.castSucc a) h1
    rwa [Fin.castSucc_injective n hxa] at hxX
  have hB₀ : ∀ b ∈ castSuccFinset B, b ∈ X := by
    intro b hb
    have h1 : Fin.castSucc b ∈ B := mem_castSuccFinset.mp hb
    obtain ⟨x, hxX, hxb⟩ := hB (Fin.castSucc b) h1
    rwa [Fin.castSucc_injective n hxb] at hxX
  have hdisj₀ : Disjoint (castSuccFinset A) (castSuccFinset B) := by
    refine Finset.disjoint_left.mpr (fun a ha hb => ?_)
    exact Finset.disjoint_left.mp hdisj (mem_castSuccFinset.mp ha) (mem_castSuccFinset.mp hb)
  have hAcard : ξ * (X.ncard : ℝ) ≤ ((castSuccFinset A).card : ℝ) := by
    have h := hAc
    rw [Set.ncard_image_of_injective _ (Fin.castSucc_injective n)] at h
    rw [card_castSuccFinset hA']
    exact h
  have hBcard : ξ * (X.ncard : ℝ) ≤ ((castSuccFinset B).card : ℝ) := by
    have h := hBc
    rw [Set.ncard_image_of_injective _ (Fin.castSucc_injective n)] at h
    rw [card_castSuccFinset hB']
    exact h
  have hcore := hlr (castSuccFinset A) (castSuccFinset B) hA₀ hB₀ hdisj₀ hAcard hBcard
  rw [edgeCount_famImage_castSucc hA' hB', ← card_castSuccFinset hA', ← card_castSuccFinset hB']
  exact hcore

/-- Lower `(p,ε)`-regularity of `𝓖` on all of `Fin n` implies lower
`(p/4, 2ε)`-regularity of the extended graph. -/
theorem selfLowerRegular_extendVertex {𝓖 : Hypergraph (Fin n)} {T : Finset (Fin n)}
    {p ε : ℝ} (hn : 1 ≤ n) (hε : 0 < ε) (hlr : SelfLowerRegular 𝓖 Set.univ p ε)
    (hcard : ((n : ℝ) + 1) ≤ (1 + (1/2) * ε) * (n : ℝ)) :
    SelfLowerRegular (extendVertex 𝓖 T) Set.univ (p / 4) (2 * ε) := by
  have himg : SelfLowerRegular (famImage Fin.castSucc 𝓖)
      (Fin.castSucc '' (Set.univ : Set (Fin n))) p ε :=
    selfLowerRegular_famImage_castSucc hlr
  have hsub : famImage Fin.castSucc 𝓖 ⊆ extendVertex 𝓖 T := fun e he => Or.inl he
  have hGX : ∀ e ∈ famImage Fin.castSucc 𝓖, e ⊆ Fin.castSucc '' (Set.univ : Set (Fin n)) := by
    intro e he x hx
    rw [mem_famImage] at he
    obtain ⟨e₀, -, rfl⟩ := he
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, Set.mem_univ y, rfl⟩
  have hXY : (Fin.castSucc '' (Set.univ : Set (Fin n))) ⊆ (Set.univ : Set (Fin (n+1))) :=
    fun x _ => Set.mem_univ x
  have hXcard : ((Fin.castSucc '' (Set.univ : Set (Fin n))).ncard : ℝ) = (n : ℝ) := by
    rw [Set.ncard_image_of_injective _ (Fin.castSucc_injective n), Set.ncard_univ, Nat.card_fin]
  have hYcard : ((Set.univ : Set (Fin (n+1))).ncard : ℝ) = (n : ℝ) + 1 := by
    rw [Set.ncard_univ, Nat.card_fin]
    push_cast
    ring
  have hc : ((Set.univ : Set (Fin (n+1))).ncard : ℝ) ≤
      (1 + (1/2) * ε) * ((Fin.castSucc '' (Set.univ : Set (Fin n))).ncard : ℝ) := by
    rw [hXcard, hYcard]
    linarith [hcard]
  have hres := selfLowerRegular_mono (𝓖 := famImage Fin.castSucc 𝓖) (𝓗 := extendVertex 𝓖 T)
    hXY hGX hsub hc himg (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1) hε
  have h1 : p * (1 - 1/2) ^ 2 = p / 4 := by ring
  have h2' : ε / (1 - 1/2) = 2 * ε := by ring
  rw [h1, h2'] at hres
  exact hres


/-! ## The odd case of Corollary 10.13 -/

theorem optcol_corollary_odd (hGKO : GKOStatementLinear) {η ε p : ℝ} (hη : 0 < η) (hε : 0 < ε)
    (hεp : 8 * ε < p) (hp : p < 1) (hsmall : 10 ^ 12 * (η + ε) ≤ p) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, Odd n → ∀ 𝓖 : Hypergraph (Fin n),
      (∀ e ∈ 𝓖, edgeSize e = 2) → SelfLowerRegular 𝓖 Set.univ p ε →
      (∀ v : Fin n, ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) ≤ η * (n : ℝ)) →
      (({v : Fin n | degAt 𝓖 v < hypergraphMaxDegree 𝓖}.ncard : ℝ) ≥
        (hypergraphMaxDegree 𝓖 : ℝ)) →
      𝓖.Colorable (hypergraphMaxDegree 𝓖) := by
  have hηp : 24 * (η + ε) ≤ p := by nlinarith [hsmall]
  obtain ⟨Nc, hNc⟩ := optcol_corollary_core hGKO
    (by linarith : (0 : ℝ) < 3 * η) (by linarith : (0 : ℝ) < 2 * ε)
    (by nlinarith : 2 * ε < p / 4) (by nlinarith : p / 4 < 1)
    (by nlinarith [hsmall, hη, hε] : 10 ^ 10 * (3 * η + 2 * ε) ≤ p / 4)
  refine ⟨max Nc (100 + (⌈2 / ε⌉₊ + ⌈1 / η⌉₊)), ?_⟩
  intro n hn hodd 𝓖 h2 hlr hdeg hlow
  have hn1 : 1 ≤ n := by obtain ⟨k, hk⟩ := hodd; omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hNcle : Nc ≤ n := by omega
  have hεle : ⌈2 / ε⌉₊ ≤ n := by omega
  have hηle : ⌈1 / η⌉₊ ≤ n := by omega
  have hεn2 : 2 ≤ ε * (n : ℝ) := by
    have h1 : (2 : ℝ) / ε ≤ (n : ℝ) := Nat.ceil_le.mp hεle
    have h2 : ε * ((2 : ℝ) / ε) = 2 := by
      rw [mul_div_cancel₀ _ (ne_of_gt hε)]
    nlinarith [h1, hε.le, h2]
  have hεn : 1 ≤ ε * (n : ℝ) := by linarith
  have hηn1 : 1 ≤ η * (n : ℝ) := by
    have h1 : (1 : ℝ) / η ≤ (n : ℝ) := Nat.ceil_le.mp hηle
    have h2 : η * ((1 : ℝ) / η) = 1 := by
      rw [mul_one_div, div_self (ne_of_gt hη)]
    nlinarith [h1, hη.le, h2]
  have hε1 : ε ≤ 1 / 3 := by nlinarith [hεp, hp]
  have hεp' : ε ≤ p := by linarith
  set Δ : ℕ := hypergraphMaxDegree 𝓖 with hΔ
  have hΔge : (p - 3 * ε) * (n : ℝ) ≤ (Δ : ℝ) := by
    rw [hΔ]
    exact maxDegree_ge_of_selfLowerRegular 𝓖 h2 hlr hεn hε1 hεp' hp.le hn1
  have h2η : 2 * η + 3 * ε ≤ p := by nlinarith [hηp, hη, hε]
  have hDge : Δ ≤ {v : Fin n | degAt 𝓖 v < Δ}.ncard := by
    have := hlow
    rw [ge_iff_le] at this
    exact_mod_cast this
  set t : ℕ := ⌊(Δ : ℝ) - 2 * η * (n : ℝ)⌋₊ with ht
  have ht0 : (0 : ℝ) ≤ (Δ : ℝ) - 2 * η * (n : ℝ) := by
    have h1 : 2 * η * (n : ℝ) ≤ (p - 3 * ε) * (n : ℝ) := by nlinarith [h2η, hnR]
    linarith
  have ht2 : (t : ℝ) ≤ (Δ : ℝ) - 2 * η * (n : ℝ) := by
    rw [ht]; exact Nat.floor_le ht0
  have htleΔ : t ≤ Δ := by
    have h1 : (t : ℝ) ≤ (Δ : ℝ) := by nlinarith [ht2, hη, hnR]
    exact_mod_cast h1
  set S : Finset (Fin n) := Finset.univ.filter (fun v => degAt 𝓖 v < Δ) with hS
  have hScoe : (S : Set (Fin n)) = {v : Fin n | degAt 𝓖 v < Δ} := by
    ext v; simp [hS]
  have hScard : Δ ≤ S.card := by
    have h : S.card = ({v : Fin n | degAt 𝓖 v < Δ}).ncard := by
      rw [← Set.ncard_coe_finset (s := S), hScoe]
    rw [h]; exact hDge
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (s := S) (n := t)
    (le_trans htleΔ hScard)
  have hTmem : ∀ u ∈ T, degAt 𝓖 u < Δ := by
    intro u hu
    have := hTsub hu
    rw [hS, Finset.mem_filter] at this
    exact this.2
  have hTcard_le : T.card ≤ Δ := by rw [hTcard]; exact htleΔ
  have hTcard_eq : T.card = t := hTcard
  have h2ext : ∀ e ∈ extendVertex 𝓖 T, edgeSize e = 2 :=
    fun e he => edgeSize_extendVertex h2 hn1 he
  have hmaxEq : hypergraphMaxDegree (extendVertex 𝓖 T) = Δ := by
    rw [hΔ]
    exact hypergraphMaxDegree_extendVertex h2 hn1 hTmem hTcard_le
  have hev : Even (n + 1) := by obtain ⟨k, hk⟩ := hodd; exact ⟨k + 1, by omega⟩
  have hcardLR : ((n : ℝ) + 1) ≤ (1 + (1 / 2) * ε) * (n : ℝ) := by
    nlinarith [hεn2, hnR]
  have hlrExt : SelfLowerRegular (extendVertex 𝓖 T) Set.univ (p / 4) (2 * ε) :=
    selfLowerRegular_extendVertex hn1 hε hlr hcardLR
  have hdegExt : ∀ v : Fin (n + 1),
      ((hypergraphMaxDegree (extendVertex 𝓖 T) : ℝ) - (degAt (extendVertex 𝓖 T) v : ℝ))
        ≤ 3 * η * ((n : ℝ) + 1) := by
    intro v
    rw [hmaxEq]
    rcases lt_or_ge v.val n with hv | hv
    · have hvcast : Fin.castSucc (⟨v.val, hv⟩ : Fin n) = v := by ext; simp [Fin.castSucc]
      rw [← hvcast, degAt_extendVertex_castSucc 𝓖 T _ hn1]
      have hd := hdeg (⟨v.val, hv⟩ : Fin n)
      by_cases huT : (⟨v.val, hv⟩ : Fin n) ∈ T
      · rw [if_pos huT]
        have hcast : (((degAt 𝓖 (⟨v.val, hv⟩ : Fin n) + 1 : ℕ)) : ℝ)
            = (degAt 𝓖 (⟨v.val, hv⟩ : Fin n) : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        nlinarith [hd, hε, hη, hnR]
      · rw [if_neg huT]
        have hcast : (((degAt 𝓖 (⟨v.val, hv⟩ : Fin n) + 0 : ℕ)) : ℝ)
            = (degAt 𝓖 (⟨v.val, hv⟩ : Fin n) : ℝ) := by push_cast; ring
        rw [hcast]
        nlinarith [hd, hη, hnR]
    · have hvlast : v = Fin.last n := by
        ext; simp only [Fin.val_last]; omega
      rw [hvlast, degAt_extendVertex_last 𝓖 T hn1, hTcard_eq]
      have h3 : (Δ : ℝ) - (t : ℝ) < 2 * η * (n : ℝ) + 1 := by
        have := Nat.sub_one_lt_floor ((Δ : ℝ) - 2 * η * (n : ℝ))
        rw [ht]
        linarith
      nlinarith [h3, hηn1, hη]
  have hmin : ∀ v : Fin (n + 1),
      degAt (extendVertex 𝓖 T) (Fin.last n) ≤ degAt (extendVertex 𝓖 T) v := by
    intro v
    rw [degAt_extendVertex_last 𝓖 T hn1]
    rcases lt_or_ge v.val n with hv | hv
    · have hvcast : Fin.castSucc (⟨v.val, hv⟩ : Fin n) = v := by ext; simp [Fin.castSucc]
      rw [← hvcast, degAt_extendVertex_castSucc 𝓖 T _ hn1]
      have hd := hdeg (⟨v.val, hv⟩ : Fin n)
      have hle : (t : ℝ) ≤ (degAt 𝓖 (⟨v.val, hv⟩ : Fin n) : ℝ) := by
        have h1 : η * (n : ℝ) ≤ 2 * η * (n : ℝ) := by nlinarith [hη, hnR]
        rw [ht] at ht2
        nlinarith [ht2, hd, h1]
      have hnat : t ≤ degAt 𝓖 (⟨v.val, hv⟩ : Fin n) := by exact_mod_cast hle
      have hnat' : T.card ≤ degAt 𝓖 (⟨v.val, hv⟩ : Fin n)
          + (if (⟨v.val, hv⟩ : Fin n) ∈ T then 1 else 0) := by
        rw [hTcard_eq]
        exact le_trans hnat (Nat.le_add_right _ _)
      exact hnat'
    · have hvlast : v = Fin.last n := by
        ext; simp only [Fin.val_last]; omega
      rw [hvlast, degAt_extendVertex_last 𝓖 T hn1]
  have hkey : (Δ : ℝ) - (t : ℝ) ≤
      ∑ u ∈ (Finset.univ : Finset (Fin n)),
        ((Δ : ℝ) - (degAt (extendVertex 𝓖 T) (Fin.castSucc u) : ℝ)) := by
    set F : Finset (Fin n) := Finset.univ.filter
      (fun u => degAt (extendVertex 𝓖 T) (Fin.castSucc u) < Δ) with hF
    have hFle : (F.card : ℝ) ≤ ∑ u ∈ (Finset.univ : Finset (Fin n)),
        ((Δ : ℝ) - (degAt (extendVertex 𝓖 T) (Fin.castSucc u) : ℝ)) := by
      have h1 : (F.card : ℝ) ≤ ∑ u ∈ F,
          ((Δ : ℝ) - (degAt (extendVertex 𝓖 T) (Fin.castSucc u) : ℝ)) := by
        have hc : (F.card : ℝ) = ∑ _u ∈ F, (1 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [hc]
        refine Finset.sum_le_sum (fun u hu => ?_)
        have hu' : degAt (extendVertex 𝓖 T) (Fin.castSucc u) < Δ :=
          (Finset.mem_filter.mp hu).2
        have h2' : (degAt (extendVertex 𝓖 T) (Fin.castSucc u) : ℝ) + 1 ≤ (Δ : ℝ) := by
          exact_mod_cast hu'
        linarith
      refine le_trans h1 (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)
      intro u _ _
      have h := degAt_extendVertex_le_max h2 hn1 hTmem hTcard_le (Fin.castSucc u)
      have h' : (degAt (extendVertex 𝓖 T) (Fin.castSucc u) : ℝ) ≤ (Δ : ℝ) := by
        rw [hΔ]; exact_mod_cast h
      linarith
    have hFcard : (Δ : ℝ) - (t : ℝ) ≤ (F.card : ℝ) := by
      have hsub : S.filter (fun u => u ∉ T) ⊆ F := by
        intro u hu
        rw [Finset.mem_filter] at hu
        obtain ⟨huS, huT⟩ := hu
        have h1 : degAt 𝓖 u < Δ := by
          have := huS
          rw [hS, Finset.mem_filter] at this
          exact this.2
        rw [hF, Finset.mem_filter]
        exact ⟨Finset.mem_univ u, by
          rw [degAt_extendVertex_castSucc 𝓖 T u hn1, if_neg huT]; exact h1⟩
      have hcardF : (S.filter (fun u => u ∉ T)).card = S.card - T.card := by
        have hsum := Finset.card_filter_add_card_filter_not (s := S) (fun u => u ∈ T)
        have hfil : S.filter (fun u => u ∈ T) = T := by
          ext u
          rw [Finset.mem_filter]
          exact ⟨fun h => h.2, fun h => ⟨hTsub h, h⟩⟩
        rw [hfil] at hsum
        omega
      have h1 : Δ - t ≤ (S.filter (fun u => u ∉ T)).card := by
        rw [hcardF]
        omega
      have h2' : (S.filter (fun u => u ∉ T)).card ≤ F.card := Finset.card_le_card hsub
      have h3 : Δ - t ≤ F.card := le_trans h1 h2'
      have hcast : ((Δ - t : ℕ) : ℝ) = (Δ : ℝ) - (t : ℝ) := Nat.cast_sub htleΔ
      rw [← hcast]
      exact_mod_cast h3
    linarith
  have hsum : 2 * ((hypergraphMaxDegree (extendVertex 𝓖 T) : ℝ)
        - (degAt (extendVertex 𝓖 T) (Fin.last n) : ℝ)) ≤
      ∑ v ∈ (Finset.univ : Finset (Fin (n + 1))),
        ((hypergraphMaxDegree (extendVertex 𝓖 T) : ℝ) - (degAt (extendVertex 𝓖 T) v : ℝ)) := by
    rw [hmaxEq, degAt_extendVertex_last 𝓖 T hn1, hTcard_eq]
    rw [Fin.sum_univ_castSucc]
    rw [degAt_extendVertex_last 𝓖 T hn1, hTcard_eq]
    linarith [hkey]
  have hdegExt' : ∀ v : Fin (n + 1),
      ((hypergraphMaxDegree (extendVertex 𝓖 T) : ℝ) - (degAt (extendVertex 𝓖 T) v : ℝ))
        ≤ 3 * η * ((n + 1 : ℕ) : ℝ) := by
    intro v
    have h := hdegExt v
    have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hc]
    exact h
  have hres := hNc (n + 1) (by omega) hev (extendVertex 𝓖 T) h2ext hlrExt hdegExt'
    ⟨Fin.last n, hmin, hsum⟩
  rw [hmaxEq] at hres
  exact colorable_famImage (Fin.castSucc_injective n) 𝓖 Δ
    (Hypergraph.Colorable.restrict (fun e he => Or.inl he) hres)

/-! ## The faithful form of Corollary 10.13

The *faithful* (existential-threshold) form of Corollary 10.13, i.e. the form the paper states,
lives in `Submission/EFL/OptColFaithful.lean` under the name
`ErdosFaberLovaszConjecture.optcol_corollary`.  It cannot live in this module: it is derived
from the `GKO` chapter (`Work.S12Faithful.Cone`), while
`Submission/Work/Deep/GKO/corollary_10_13_odd_from_fixed.lean` imports *this* module for the
odd-case reduction, so an import of the chapter here would be a cycle.

What *is* available here are the *conditional* lemmas
`optcol_corollary_core`/`optcol_corollary_even`/`optcol_corollary_odd`, proved from the
linear-hierarchy input `GKOStatementLinear` (the paper's Corollary 10.13 under the stronger
hierarchy `10^10 · (ν + ε) ≤ p`, resp. `10^12 · (η + ε) ≤ p` for the odd case). -/

end

end ErdosFaberLovaszConjecture
