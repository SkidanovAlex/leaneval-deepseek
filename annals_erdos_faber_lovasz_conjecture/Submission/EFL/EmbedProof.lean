import Submission.EFL.Embed

/-!
# §8: the uniformisation step of `lem:embed`

The first step of the proof of the embedding lemma: every linear hypergraph all
of whose edges have size at most `r` can be made `r`-uniform by adding
`r - |e|` **fresh** vertices to every edge `e`.  We formalise this with the
vertex set `Fin (n + r * E)` (where `E = #E(𝓗)`), the old vertices being those
of `Fin n` (via `Fin.castLEEmb`) and the fresh vertices being the last `r * E`
ones; the block of `r` fresh vertices numbered
`[n + r*i, n + r*(i+1))` is reserved for the `i`-th edge of `𝓗`.

Because each edge of `𝓗` gets its own block, linearity is preserved, and the
construction is *recognisable*: the `r`-edges meeting `Fin n` are exactly the
extensions `ι '' e` of the edges `e ∈ 𝓗`, with `ι` injective; hence the degrees
at the old vertices are unchanged.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n r M : ℕ}

/-- For `ι : Fin n ↪ Fin M` of the form `Fin.castLEEmb h`, membership in the
range of `ι` is `w.val < n`. -/
theorem mem_range_castLEEmb {h : n ≤ M} {ι : Fin n ↪ Fin M} (hι : ι = Fin.castLEEmb h)
    (w : Fin M) : w ∈ Set.range ι ↔ w.val < n := by
  subst hι
  constructor
  · rintro ⟨v, rfl⟩
    exact v.isLt
  · intro hw
    exact ⟨⟨w.val, hw⟩, by ext; rfl⟩

/-- **The uniformisation step of `lem:embed`.**  From a linear hypergraph `𝓗` on
`Fin n` all of whose edges have size between `2` and `r`, one obtains an
`r`-uniform linear hypergraph `𝓖` on `Fin M`, an injection `ι : Fin n ↪ Fin M`
and, for every edge `e ∈ 𝓗`, a *unique* edge `e' ∈ 𝓖` meeting `ι '' Fin n` with
`e' ∩ ι '' Fin n = ι '' e`; conversely every edge of `𝓖` meeting `ι '' Fin n`
arises in this way, and the degrees at the old vertices agree:
`d_𝓖(ι v) = d_𝓗(v)`.  Moreover `M ≤ n + r·#E(𝓗)`. -/
theorem exists_uniform_extension {𝓗 : Hypergraph (Fin n)} {r : ℕ} (hr : 2 ≤ r)
    (hlin : 𝓗.IsLinear) (h2 : ∀ e ∈ 𝓗, 2 ≤ edgeSize e)
    (hsize : ∀ e ∈ 𝓗, edgeSize e ≤ r) :
    ∃ (M : ℕ) (ι : Fin n ↪ Fin M) (𝓖 : Hypergraph (Fin M)),
      (∀ e ∈ 𝓖, edgeSize e = r) ∧
      𝓖.IsLinear ∧
      (∀ e ∈ 𝓗, ∃! e' ∈ 𝓖, e' ∩ Set.range ι = ι '' e) ∧
      (∀ e' ∈ 𝓖, (e' ∩ Set.range ι).Nonempty) ∧
      (∀ v : Fin n, MultiHypergraph.hdeg 𝓖 (ι v) = MultiHypergraph.hdeg 𝓗 v) ∧
      (M : ℝ) ≤ (n : ℝ) + (r : ℝ) * (𝓗.ncard : ℝ) := by
  classical
  set E : ℕ := 𝓗.toFinset.card with hE
  have hncard : 𝓗.ncard = E := by rw [hE]; exact Set.ncard_eq_toFinset_card' 𝓗
  set M : ℕ := n + r * E with hM
  have hnM : n ≤ M := Nat.le_add_right n (r * E)
  set ι : Fin n ↪ Fin M := Fin.castLEEmb hnM with hι
  have hrange : ∀ w : Fin M, w ∈ Set.range ι ↔ w.val < n := mem_range_castLEEmb hι
  -- the index of an edge of `𝓗` among its edges
  set eIdx : {e : Set (Fin n) // e ∈ 𝓗} → Fin E := fun p =>
    (Finset.equivFin 𝓗.toFinset) ⟨p.1, by rw [Set.mem_toFinset]; exact p.2⟩ with heIdx
  have heIdx_inj : Function.Injective eIdx := by
    intro p q h
    have h1 : (⟨p.1, by rw [Set.mem_toFinset]; exact p.2⟩ : ↥𝓗.toFinset) =
        ⟨q.1, by rw [Set.mem_toFinset]; exact q.2⟩ :=
      (Finset.equivFin 𝓗.toFinset).injective h
    exact Subtype.ext (congrArg (fun x : ↥𝓗.toFinset => (x : Set (Fin n))) h1)
  -- the fresh vertices reserved for the edge `p`
  set fresh : {e : Set (Fin n) // e ∈ 𝓗} → Set (Fin M) := fun p =>
    {w : Fin M | ∃ j : ℕ, j < r - edgeSize p.1 ∧ w.val = n + r * (eIdx p).val + j}
    with hfresh
  have hfresh_ge : ∀ p w, w ∈ fresh p → n ≤ w.val := by
    rintro p w ⟨j, -, hw⟩
    omega
  have hfresh_notMem : ∀ p w, w ∈ fresh p → w ∉ Set.range ι := by
    intro p w hw hmem
    have := hfresh_ge p w hw
    rw [hrange] at hmem
    omega
  -- the extension of the edge `p`
  set star : {e : Set (Fin n) // e ∈ 𝓗} → Set (Fin M) := fun p =>
    ι '' p.1 ∪ fresh p with hstar
  have hstar_inter : ∀ p, star p ∩ Set.range ι = ι '' p.1 := by
    intro p
    apply Set.Subset.antisymm
    · rintro w ⟨hw, hmem⟩
      rcases hw with hw | hw
      · exact hw
      · exact absurd hmem (hfresh_notMem p w hw)
    · intro w hw
      refine ⟨Or.inl hw, ?_⟩
      obtain ⟨v, -, hivw⟩ := hw
      exact ⟨v, hivw⟩
  -- the number of fresh vertices is exactly `r - |e|`
  have hfresh_card : ∀ p, (fresh p).ncard = r - edgeSize p.1 := by
    intro p
    have hbnd : ∀ j : ℕ, j < r - edgeSize p.1 → n + r * (eIdx p).val + j < M := by
      intro j hj
      have hiE : (eIdx p).val < E := (eIdx p).isLt
      have hj' : j < r := lt_of_lt_of_le hj (Nat.sub_le _ _)
      have h3 : r * (eIdx p).val + j < r * ((eIdx p).val + 1) := by
        rw [Nat.mul_succ]; omega
      have h4 : r * ((eIdx p).val + 1) ≤ r * E := Nat.mul_le_mul_left r (by omega)
      rw [hM]
      omega
    let g : Fin (r - edgeSize p.1) → Fin M :=
      fun j => ⟨n + r * (eIdx p).val + j.val, hbnd j.val j.isLt⟩
    have hset : fresh p = Set.range g := by
      ext w
      constructor
      · rintro ⟨j, hj, hw⟩
        exact ⟨⟨j, hj⟩, Fin.ext (by simp only [g]; omega)⟩
      · rintro ⟨j, rfl⟩
        exact ⟨j.val, j.isLt, rfl⟩
    rw [hset, Set.ncard_range_of_injective]
    · simp
    · intro a b hab
      have := congrArg Fin.val hab
      simp only [g] at this
      exact Fin.ext (by omega)
  -- cardinality of an extension
  have hstar_card : ∀ p, (star p).ncard = r := by
    intro p
    have hdisj : Disjoint (ι '' p.1) (fresh p) := by
      rw [Set.disjoint_left]
      intro w hw hw'
      obtain ⟨v, -, hivw⟩ := hw
      exact hfresh_notMem p w hw' ⟨v, hivw⟩
    rw [hstar, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hfresh_card]
    have himg : (ι '' p.1).ncard = edgeSize p.1 := by
      rw [Set.ncard_image_of_injective _ ι.injective, ← edgeSize_eq_ncard]
    rw [himg]
    have hsp := hsize p.1 p.2
    omega
  -- injectivity of `star` (via `star p ∩ range ι = ι '' p.1`)
  have hstar_inj : Function.Injective star := by
    intro p q hpq
    have h1 : ι '' p.1 = ι '' q.1 := by
      rw [← hstar_inter p, ← hstar_inter q, hpq]
    have h2 : p.1 = q.1 := (Set.image_injective.mpr ι.injective) h1
    exact Subtype.ext h2
  -- linearity
  have hstar_disj : ∀ p q : {e : Set (Fin n) // e ∈ 𝓗}, p ≠ q →
      (star p ∩ star q).Subsingleton := by
    intro p q hpq
    have hne : p.1 ≠ q.1 := fun h => hpq (Subtype.ext h)
    have hsub : star p ∩ star q ⊆ ι '' (p.1 ∩ q.1) := by
      rintro w ⟨hw₁, hw₂⟩
      rcases hw₁ with hw₁ | hw₁
      · rcases hw₂ with hw₂ | hw₂
        · obtain ⟨a, ha, hia⟩ := hw₁
          obtain ⟨b, hb, hib⟩ := hw₂
          exact ⟨a, ⟨ha, ι.injective (hia.trans hib.symm) ▸ hb⟩, hia⟩
        · obtain ⟨v, -, hiv⟩ := hw₁
          exact absurd ⟨v, hiv⟩ (hfresh_notMem q w hw₂)
      · rcases hw₂ with hw₂ | hw₂
        · obtain ⟨v, -, hiv⟩ := hw₂
          exact absurd ⟨v, hiv⟩ (hfresh_notMem p w hw₁)
        · exfalso
          obtain ⟨j₁, hj₁, hw₁eq⟩ := hw₁
          obtain ⟨j₂, hj₂, hw₂eq⟩ := hw₂
          have hj₁' : j₁ < r := lt_of_lt_of_le hj₁ (Nat.sub_le _ _)
          have hj₂' : j₂ < r := lt_of_lt_of_le hj₂ (Nat.sub_le _ _)
          have hval : r * (eIdx p).val + j₁ = r * (eIdx q).val + j₂ := by omega
          have hlt₁ : r * (eIdx p).val < r * ((eIdx q).val + 1) := by
            rw [Nat.mul_succ]; omega
          have hlt₂ : r * (eIdx q).val < r * ((eIdx p).val + 1) := by
            rw [Nat.mul_succ]; omega
          have hi₁ : (eIdx p).val < (eIdx q).val + 1 :=
            (Nat.mul_lt_mul_left (by omega : 0 < r)).mp hlt₁
          have hi₂ : (eIdx q).val < (eIdx p).val + 1 :=
            (Nat.mul_lt_mul_left (by omega : 0 < r)).mp hlt₂
          have hidx : eIdx p = eIdx q := Fin.ext (by omega)
          exact hne (congrArg Subtype.val (heIdx_inj hidx))
    intro a ha b hb
    exact ((hlin p.2 q.2 hne).image ι) (hsub ha) (hsub hb)
  -- the extensions of the edges through `v` are the `𝓖`-edges through `ι v`
  have hset_eq : ∀ v : Fin n,
      {e' ∈ Set.range star | ι v ∈ e'} = star '' {p : {e : Set (Fin n) // e ∈ 𝓗} | v ∈ p.1} := by
    intro v
    ext e'
    constructor
    · rintro ⟨⟨p, hp⟩, hv⟩
      have hv' : ι v ∈ (ι '' p.1 : Set (Fin M)) := by
        rw [← hstar_inter p, hp]
        exact ⟨hv, ⟨v, rfl⟩⟩
      obtain ⟨u, hu, huu⟩ := hv'
      exact ⟨p, ⟨ι.injective huu ▸ hu, hp⟩⟩
    · rintro ⟨p, hp, rfl⟩
      refine ⟨⟨p, rfl⟩, ?_⟩
      exact Or.inl ⟨v, hp, rfl⟩
  refine ⟨M, ι, Set.range star, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- uniformity
    rintro e' ⟨p, rfl⟩
    rw [edgeSize_eq_ncard]
    exact hstar_card p
  · -- linearity of `𝓖`
    rintro e' ⟨p, rfl⟩ e'' ⟨q, rfl⟩ hne
    exact hstar_disj p q (fun hpq => hne (by rw [hpq]))
  · -- unique extension
    intro e he
    refine ExistsUnique.intro (star ⟨e, he⟩)
      ⟨⟨⟨e, he⟩, rfl⟩, hstar_inter ⟨e, he⟩⟩ ?_
    rintro e' ⟨⟨q, hq⟩, hqe⟩
    have h1 : ι '' q.1 = ι '' e := by rw [← hstar_inter q, hq, hqe]
    have h2 : q.1 = e := (Set.image_injective.mpr ι.injective) h1
    have hq_eq : q = ⟨e, he⟩ := Subtype.ext h2
    rw [← hq, hq_eq]
  · -- every edge of `𝓖` meets the old vertices
    rintro e' ⟨p, rfl⟩
    have hne : p.1.Nonempty := by
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      have h3 : 2 ≤ edgeSize (∅ : Set (Fin n)) := hcon ▸ h2 p.1 p.2
      rw [edgeSize_eq_ncard] at h3
      simp at h3
    obtain ⟨v, hv⟩ := hne
    exact ⟨ι v, ⟨Or.inl ⟨v, hv, rfl⟩, ⟨v, rfl⟩⟩⟩
  · -- the degrees agree
    intro v
    rw [MultiHypergraph.hdeg, MultiHypergraph.hdeg, hset_eq v,
      Set.ncard_image_of_injective _ hstar_inj]
    refine Set.ncard_congr (fun p _ => p.1) (fun p hp => ⟨p.2, hp⟩)
      (fun p q _ _ h => Subtype.ext h) ?_
    rintro e ⟨he, hve⟩
    exact ⟨⟨e, he⟩, hve, rfl⟩
  · -- the vertex bound
    rw [hM, hncard]
    push_cast
    exact le_refl _

end

end ErdosFaberLovaszConjecture
