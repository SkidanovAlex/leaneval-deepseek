import Submission.EFL.EmbedProof

/-!
# The uniformisation step, with private fresh vertices

`exists_uniform_extension` (in the cone) makes a linear hypergraph `r`-uniform by
adding `r - |e|` fresh vertices to every edge, reserving a private block of `r`
vertices for each edge.  This module records one consequence of that *particular*
construction which is not implied by the abstract properties of its output and
which the embedding lemma `lem:embed` needs: **every fresh vertex lies in at most
one edge of the output**.  (Without it the degree of `𝓗*` at a fresh vertex is
uncontrolled, and the glued designs cannot be sized.)
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n r M : ℕ}

/-- **The uniformisation step of `lem:embed`, with private fresh vertices.**

This is `ErdosFaberLovaszConjecture.exists_uniform_extension` with one extra
conclusion: a vertex outside `Set.range ι` (i.e. a fresh vertex added by the
construction) lies in *at most one* edge of `𝓖`.  This is what makes the degrees
of `𝓗*` in the embedding lemma controllable at the fresh vertices, and it is
needed because the abstract properties of `exists_uniform_extension` do not
determine it (a hypergraph with all its edges meeting `range ι` and agreeing on
the degrees of the old vertices may still have a fresh vertex of degree two).

The statement below is otherwise verbatim `exists_uniform_extension`. -/
theorem exists_uniform_extension' {𝓗 : Hypergraph (Fin n)} {r : ℕ} (hr : 2 ≤ r)
    (hlin : 𝓗.IsLinear) (h2 : ∀ e ∈ 𝓗, 2 ≤ edgeSize e)
    (hsize : ∀ e ∈ 𝓗, edgeSize e ≤ r) :
    ∃ (M : ℕ) (ι : Fin n ↪ Fin M) (𝓖 : Hypergraph (Fin M)),
      (∀ e ∈ 𝓖, edgeSize e = r) ∧
      𝓖.IsLinear ∧
      (∀ e ∈ 𝓗, ∃! e' ∈ 𝓖, e' ∩ Set.range ι = ι '' e) ∧
      (∀ e' ∈ 𝓖, (e' ∩ Set.range ι).Nonempty) ∧
      (∀ v : Fin n, MultiHypergraph.hdeg 𝓖 (ι v) = MultiHypergraph.hdeg 𝓗 v) ∧
      (∀ w : Fin M, w ∉ Set.range ι →
        ({g : Set (Fin M) | g ∈ 𝓖 ∧ w ∈ g} : Set (Set (Fin M))).ncard ≤ 1) ∧
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
  refine ⟨M, ι, Set.range star, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · -- fresh vertices lie in at most one edge
    intro w hw
    have hset : ({g : Set (Fin M) | g ∈ Set.range star ∧ w ∈ g} : Set (Set (Fin M)))
        = star '' {p : {e : Set (Fin n) // e ∈ 𝓗} | w ∈ fresh p} := by
      ext g; constructor
      · rintro ⟨⟨p, rfl⟩, hp⟩
        rw [hstar] at hp
        rcases hp with hp | hp
        · obtain ⟨v, -, hv⟩ := hp
          exact absurd ⟨v, hv⟩ hw
        · exact ⟨p, hp, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨⟨p, rfl⟩, Or.inr hp⟩
    rw [hset, Set.ncard_image_of_injective _ hstar_inj]
    rw [Set.ncard_le_one]
    intro p hp q hq
    simp only [Set.mem_ofPred_eq] at hp hq
    obtain ⟨j, hj, hjeq⟩ := hp
    obtain ⟨j', hj', hjeq'⟩ := hq
    have hsum : r * (eIdx p).val + j = r * (eIdx q).val + j' := by omega
    have hjlt : j < r := lt_of_lt_of_le hj (Nat.sub_le _ _)
    have hjlt' : j' < r := lt_of_lt_of_le hj' (Nat.sub_le _ _)
    have hmod : j = j' := by
      have h1 : (r * (eIdx p).val + j) % r = j := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hjlt]
      have h2 : (r * (eIdx q).val + j') % r = j' := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hjlt']
      rw [hsum, h2] at h1
      exact h1.symm
    have hidx : (eIdx p).val = (eIdx q).val := by
      have h2 : r * (eIdx p).val = r * (eIdx q).val := by omega
      exact Nat.mul_left_cancel (by omega) h2
    exact heIdx_inj (Fin.ext hidx)
  · -- the vertex bound
    rw [hM, hncard]
    push_cast
    exact le_refl _

end

end ErdosFaberLovaszConjecture
