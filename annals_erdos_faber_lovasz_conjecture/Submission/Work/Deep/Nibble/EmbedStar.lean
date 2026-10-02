import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.EmbedAux
import Submission.Work.Deep.Nibble.Hstar_unif_linear

/-!
# The degrees of `𝓗*` and the identification `κ`
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

noncomputable section

variable {N r : ℕ} {𝓗 : MultiHypergraph N}

theorem old_inj (U : UnifData N r 𝓗) : Function.Injective (old U) :=
  fun a b h => U.ι.injective (Sum.inl_injective h)

theorem ext_ne_extS (U : UnifData N r 𝓗) (hr : 2 ≤ r)
    (e : {e : Set (Fin N) // e ∈ 𝓗.edges}) (p : SC 𝓗) : ext U e ≠ extS U p := by
  intro h
  have h0 : Fin (r - 1) := ⟨0, by omega⟩
  have hmem : (Sum.inr ⟨p, h0⟩ : Vstar 𝓗 r U.M) ∈ extS U p := Or.inr (Set.mem_range_self h0)
  rw [← h] at hmem
  obtain ⟨y, -, hy⟩ := hmem
  exact Sum.inl_ne_inr hy

/-- Proper edges are supported on the non-isolated vertices. -/
theorem subset_verts {e : Set (Fin N)} (he : e ∈ 𝓗.edges) :
    e ⊆ {v : Fin N | 0 < 𝓗.deg v} := by
  intro v hv
  have h1 : 1 ≤ MultiHypergraph.hdeg 𝓗.edges v := by
    have hsub : ({e} : Set (Set (Fin N))) ⊆ {e' ∈ 𝓗.edges | v ∈ e'} := by
      intro e' he'
      rw [Set.mem_singleton_iff] at he'
      subst he'
      exact ⟨he, hv⟩
    have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
    simpa [MultiHypergraph.hdeg] using h2
  have h3 := MultiHypergraph.deg_def 𝓗 v
  show 0 < 𝓗.deg v
  rw [h3]
  omega

/-- A singleton copy is supported on a non-isolated vertex. -/
theorem mem_verts_of_SC (p : SC 𝓗) : p.1.1 ∈ {v : Fin N | 0 < 𝓗.deg v} := by
  have h3 := MultiHypergraph.deg_def 𝓗 p.1.1
  have hs : 0 < 𝓗.singles p.1.1 := lt_of_le_of_lt (Nat.zero_le _) p.2
  show 0 < 𝓗.deg p.1.1
  rw [h3]
  omega

theorem card_SC_fiber (v : Fin N) :
    ({p : SC 𝓗 | p.1.1 = v} : Set (SC 𝓗)).ncard = 𝓗.singles v := by
  rw [← Nat.card_coe_set_eq]
  let F : {p : SC 𝓗 // p.1.1 = v} → Fin (𝓗.singles v) :=
    fun p => ⟨p.1.1.2, by have h := p.1.2; rw [p.2] at h; exact h⟩
  have hinj : Function.Injective F := by
    intro a b h
    exact Subtype.ext (Subtype.ext (Prod.ext (a.2.trans b.2.symm) (congrArg Fin.val h)))
  have hsurj : Function.Surjective F := by
    intro k
    refine ⟨⟨⟨(v, k.1), by simpa using k.2⟩, rfl⟩, ?_⟩
    exact Fin.ext rfl
  have hF : Nat.card {p : SC 𝓗 // p.1.1 = v} = 𝓗.singles v :=
    (Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)).trans (Nat.card_fin _)
  exact hF

theorem card_edges_through (v : Fin N) :
    ({e : {e : Set (Fin N) // e ∈ 𝓗.edges} | v ∈ (e : Set (Fin N))} : Set _).ncard
      = MultiHypergraph.hdeg 𝓗.edges v := by
  rw [MultiHypergraph.hdeg]
  refine Set.ncard_congr (fun e _ => (e : Set (Fin N))) ?_ ?_ ?_
  · rintro e he; exact ⟨e.2, he⟩
  · rintro e _ e' _ h; exact Subtype.ext h
  · rintro e he; exact ⟨⟨e, he.1⟩, he.2, rfl⟩

/-- **The degree of `𝓗*` at the old vertices.** -/
theorem Hstar_deg_old (U : UnifData N r 𝓗) (hr : 2 ≤ r) (v : Fin N) :
    ({f ∈ Hstar U | old U v ∈ f} : Set (Set (Vstar 𝓗 r U.M))).ncard = 𝓗.deg v := by
  have hset : ({f ∈ Hstar U | old U v ∈ f} : Set (Set (Vstar 𝓗 r U.M)))
      = ext U '' {e : {e : Set (Fin N) // e ∈ 𝓗.edges} | v ∈ (e : Set (Fin N))}
        ∪ extS U '' {p : SC 𝓗 | p.1.1 = v} := by
    ext f; constructor
    · rintro ⟨hf, hm⟩
      rcases (mem_Hstar U).mp hf with ⟨e, rfl⟩ | ⟨p, rfl⟩
      · left
        refine ⟨e, ⟨?_, rfl⟩⟩
        have h2 : old U v ∈ ext U e ∩ Set.range (old U) := ⟨hm, ⟨v, rfl⟩⟩
        rw [ext_inter_old U e] at h2
        obtain ⟨w, hw, hwv⟩ := h2
        rwa [old_inj U hwv] at hw
      · right
        refine ⟨p, ⟨?_, rfl⟩⟩
        have h2 : old U v ∈ extS U p ∩ Set.range (old U) := ⟨hm, ⟨v, rfl⟩⟩
        rw [extS_inter_old U p, Set.mem_singleton_iff] at h2
        exact (old_inj U h2).symm
    · rintro (⟨e, ⟨hve, rfl⟩⟩ | ⟨p, ⟨hpv, rfl⟩⟩)
      · refine ⟨Or.inl ⟨e, rfl⟩, ?_⟩
        have h2 : old U v ∈ ext U e ∩ Set.range (old U) := by
          rw [ext_inter_old U e]
          exact ⟨v, hve, rfl⟩
        exact h2.1
      · refine ⟨Or.inr ⟨p, rfl⟩, ?_⟩
        have h2 : old U v = old U p.1.1 := by rw [hpv]
        rw [h2]
        exact Or.inl rfl
  have hdisj : Disjoint (ext U '' {e : {e : Set (Fin N) // e ∈ 𝓗.edges} | v ∈ (e : Set (Fin N))})
      (extS U '' {p : SC 𝓗 | p.1.1 = v}) := by
    rw [Set.disjoint_left]
    rintro f ⟨e, -, rfl⟩ ⟨p, -, hp⟩
    exact ext_ne_extS U hr e p hp.symm
  rw [hset, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    Set.ncard_image_of_injective _ (ext_inj U),
    Set.ncard_image_of_injective _ (extS_inj U hr),
    card_edges_through (𝓗 := 𝓗) v, card_SC_fiber (𝓗 := 𝓗) v]
  exact (MultiHypergraph.deg_def 𝓗 v).symm

/-- **The degree of `𝓗*` at a fresh vertex of a singleton copy.** -/
theorem Hstar_deg_fresh (U : UnifData N r 𝓗) (hr : 2 ≤ r)
    (q : Σ _p : SC 𝓗, Fin (r - 1)) :
    ({f ∈ Hstar U | (Sum.inr q : Vstar 𝓗 r U.M) ∈ f} : Set (Set (Vstar 𝓗 r U.M))).ncard
      = 1 := by
  have hset : ({f ∈ Hstar U | (Sum.inr q : Vstar 𝓗 r U.M) ∈ f} : Set (Set (Vstar 𝓗 r U.M)))
      = {extS U q.1} := by
    ext f; constructor
    · rintro ⟨hf, hm⟩
      rcases (mem_Hstar U).mp hf with ⟨e, rfl⟩ | ⟨p, rfl⟩
      · obtain ⟨y, -, hy⟩ := hm
        exact nomatch hy
      · rw [Set.mem_singleton_iff]
        have hp : p = q.1 := by
          rcases (mem_extS U p).mp hm with h | ⟨j, hj⟩
          · exact nomatch h
          · have h2 : q = ⟨p, j⟩ := (Sum.inr_injective hj).symm
            rw [h2]
        rw [hp]
    · intro hf
      rw [Set.mem_singleton_iff] at hf
      rw [hf]
      exact ⟨Or.inr ⟨q.1, rfl⟩, Or.inr ⟨q.2, rfl⟩⟩
  rw [hset, Set.ncard_singleton]

/-- **The degree of `𝓗*` at a fresh vertex of a proper-edge extension is at
most one.** -/
theorem HstarDeg_inl_le (U : UnifData N r 𝓗) (hr : 2 ≤ r) {m : Fin U.M}
    (hm : m ∉ Set.range U.ι) : HstarDeg U (Sum.inl m) ≤ 1 := by
  have hset : ({f ∈ Hstar U | (Sum.inl m : Vstar 𝓗 r U.M) ∈ f} : Set (Set (Vstar 𝓗 r U.M)))
      = ext U '' {e : {e : Set (Fin N) // e ∈ 𝓗.edges} |
          m ∈ Classical.choose (U.uniq e.1 e.2)} := by
    ext f; constructor
    · rintro ⟨hf, hmf⟩
      rcases (mem_Hstar U).mp hf with ⟨e, rfl⟩ | ⟨p, rfl⟩
      · refine ⟨e, ?_, rfl⟩
        simp only [ext, Set.mem_image] at hmf
        obtain ⟨y, hy, hy'⟩ := hmf
        rwa [Sum.inl_injective hy'] at hy
      · exfalso
        rcases (mem_extS U p).mp hmf with h | ⟨j, hj⟩
        · exact hm ⟨p.1.1, Sum.inl_injective h.symm⟩
        · exact nomatch hj
    · rintro ⟨e, he, rfl⟩
      exact ⟨Or.inl ⟨e, rfl⟩, ⟨_, he, rfl⟩⟩
  have hinj : Function.Injective
      (fun e : {e : Set (Fin N) // e ∈ 𝓗.edges} => Classical.choose (U.uniq e.1 e.2)) := by
    intro e e' h
    have h' : Classical.choose (U.uniq e.1 e.2) = Classical.choose (U.uniq e'.1 e'.2) := h
    have h1 : Classical.choose (U.uniq e.1 e.2) ∩ Set.range U.ι
        = Classical.choose (U.uniq e'.1 e'.2) ∩ Set.range U.ι := by rw [h']
    have h2 : U.ι '' e.1 = U.ι '' e'.1 := by
      rw [← (ext_spec U e).2, h1, (ext_spec U e').2]
    exact Subtype.ext (Set.image_injective.mpr U.ι.injective h2)
  have hsub : ((fun e : {e : Set (Fin N) // e ∈ 𝓗.edges} =>
        Classical.choose (U.uniq e.1 e.2)) '' {e | m ∈ Classical.choose (U.uniq e.1 e.2)})
      ⊆ {g : Set (Fin U.M) | g ∈ U.𝓖 ∧ m ∈ g} := by
    rintro g ⟨e, he, rfl⟩
    exact ⟨(ext_spec U e).1, he⟩
  calc HstarDeg U (Sum.inl m)
      = ({e : {e : Set (Fin N) // e ∈ 𝓗.edges} |
          m ∈ Classical.choose (U.uniq e.1 e.2)} : Set _).ncard := by
        rw [HstarDeg_def, hset, Set.ncard_image_of_injective _ (ext_inj U)]
    _ = (((fun e : {e : Set (Fin N) // e ∈ 𝓗.edges} => Classical.choose (U.uniq e.1 e.2)) ''
          {e | m ∈ Classical.choose (U.uniq e.1 e.2)}) : Set (Set (Fin U.M))).ncard :=
        (Set.ncard_image_of_injective _ hinj).symm
    _ ≤ ({g : Set (Fin U.M) | g ∈ U.𝓖 ∧ m ∈ g} : Set (Set (Fin U.M))).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 1 := U.freshdeg m hm

/-- **Every vertex of `𝓗*` has degree at most `D`.** -/
theorem HstarDeg_le (U : UnifData N r 𝓗) (hr : 2 ≤ r) {D : ℝ} (hD1 : 1 ≤ D)
    (hdegD : ∀ v : Fin N, (𝓗.deg v : ℝ) ≤ D) :
    ∀ u : Vstar 𝓗 r U.M, (HstarDeg U u : ℝ) ≤ D := by
  intro u
  rcases u with m | q
  · by_cases hm : m ∈ Set.range U.ι
    · obtain ⟨v, rfl⟩ := hm
      change (HstarDeg U (old U v) : ℝ) ≤ D
      rw [HstarDeg_def, Hstar_deg_old U hr v]
      exact hdegD v
    · have h1 : (HstarDeg U (Sum.inl m) : ℝ) ≤ 1 := by
        exact_mod_cast HstarDeg_inl_le U hr hm
      linarith
  · rw [HstarDeg_def, Hstar_deg_fresh U hr q]
    simpa using hD1

/-- The extension `ext U e` meets `old U '' {v | 0 < 𝓗.deg v}`. -/
theorem ext_meet_verts (U : UnifData N r 𝓗) (hlin : 𝓗.IsLinear)
    (e : {e : Set (Fin N) // e ∈ 𝓗.edges}) :
    (ext U e ∩ old U '' {v : Fin N | 0 < 𝓗.deg v}).Nonempty := by
  obtain ⟨v, hv⟩ : (e.1).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have h2 := hlin.1 e.1 e.2
    rw [hcon, edgeSize_eq_ncard] at h2
    simp at h2
  refine ⟨old U v, ?_, ⟨v, subset_verts e.2 hv, rfl⟩⟩
  have h2 : old U v ∈ ext U e ∩ Set.range (old U) := by
    rw [ext_inter_old U e]
    exact ⟨v, hv, rfl⟩
  exact h2.1

/-- The extension `ext U e` meets the old vertices exactly in `old '' e`, also
after intersecting with the non-isolated vertices. -/
theorem ext_inter_verts (U : UnifData N r 𝓗)
    (e : {e : Set (Fin N) // e ∈ 𝓗.edges}) :
    ext U e ∩ old U '' {v : Fin N | 0 < 𝓗.deg v} = old U '' e.1 := by
  have h1 : ext U e ∩ Set.range (old U) = old U '' e.1 := ext_inter_old U e
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hx1, hx2⟩
    have hx3 : x ∈ ext U e ∩ Set.range (old U) := ⟨hx1, by
      obtain ⟨v, -, rfl⟩ := hx2
      exact ⟨v, rfl⟩⟩
    rwa [h1] at hx3
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := hx
    refine ⟨?_, ⟨v, subset_verts e.2 hv, rfl⟩⟩
    have h2 : old U v ∈ ext U e ∩ Set.range (old U) := by
      rw [h1]
      exact ⟨v, hv, rfl⟩
    exact h2.1

/-- `extS U p` meets the non-isolated old vertices exactly in `{old U p.1.1}`. -/
theorem extS_inter_verts (U : UnifData N r 𝓗) (p : SC 𝓗) :
    extS U p ∩ old U '' {v : Fin N | 0 < 𝓗.deg v} = {old U p.1.1} := by
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨⟨Or.inl rfl, ⟨p.1.1, mem_verts_of_SC p, rfl⟩⟩, ?_⟩
  rintro x ⟨hx1, hx2⟩
  have hx3 : x ∈ extS U p ∩ Set.range (old U) := ⟨hx1, by
    obtain ⟨v, -, rfl⟩ := hx2
    exact ⟨v, rfl⟩⟩
  rw [extS_inter_old U p, Set.mem_singleton_iff] at hx3
  exact hx3

/-- **The identification `κ₀`** of the uniformisation step: the edges of `𝓗*`
meeting the non-isolated old vertices are exactly the extensions of the proper
edges and of the singleton copies, and `κ₀` identifies them. -/
theorem Hstar_ident (U : UnifData N r 𝓗) (hr : 2 ≤ r) (hlin : 𝓗.IsLinear) :
    ∃ κ₀ : ({e : Set (Fin N) // e ∈ 𝓗.edges} ⊕ SC 𝓗) ≃
        {f : Set (Vstar 𝓗 r U.M) // f ∈ Hstar U ∧
          (f ∩ old U '' {v : Fin N | 0 < 𝓗.deg v}).Nonempty},
      (∀ (e : Set (Fin N)) (he : e ∈ 𝓗.edges),
        ((κ₀ (Sum.inl ⟨e, he⟩) : Set (Vstar 𝓗 r U.M))
          ∩ old U '' {v : Fin N | 0 < 𝓗.deg v}) = old U '' e) ∧
      (∀ (p : SC 𝓗),
        ((κ₀ (Sum.inr p) : Set (Vstar 𝓗 r U.M))
          ∩ old U '' {v : Fin N | 0 < 𝓗.deg v}) = {old U p.1.1}) := by
  let Fl : {e : Set (Fin N) // e ∈ 𝓗.edges} →
      {f : Set (Vstar 𝓗 r U.M) // f ∈ Hstar U ∧
        (f ∩ old U '' {v : Fin N | 0 < 𝓗.deg v}).Nonempty} :=
    fun e => ⟨ext U e, Or.inl ⟨e, rfl⟩, ext_meet_verts U hlin e⟩
  let Fr : SC 𝓗 →
      {f : Set (Vstar 𝓗 r U.M) // f ∈ Hstar U ∧
        (f ∩ old U '' {v : Fin N | 0 < 𝓗.deg v}).Nonempty} :=
    fun p => ⟨extS U p, Or.inr ⟨p, rfl⟩, ⟨old U p.1.1, Or.inl rfl,
      ⟨p.1.1, mem_verts_of_SC p, rfl⟩⟩⟩
  have hinj : Function.Injective (Sum.elim Fl Fr) := by
    intro a b h
    rcases a with e | p <;> rcases b with e' | p'
    · have h2 : ext U e = ext U e' := congrArg Subtype.val h
      exact congrArg Sum.inl (ext_inj U h2)
    · exact absurd (congrArg Subtype.val h) (ext_ne_extS U hr e p')
    · exact absurd (congrArg Subtype.val h).symm (ext_ne_extS U hr e' p)
    · have h2 : extS U p = extS U p' := congrArg Subtype.val h
      exact congrArg Sum.inr (extS_inj U hr h2)
  have hsurj : Function.Surjective (Sum.elim Fl Fr) := by
    rintro ⟨f, hf, hm⟩
    rcases (mem_Hstar U).mp hf with ⟨e, rfl⟩ | ⟨p, rfl⟩
    · exact ⟨Sum.inl e, Subtype.ext rfl⟩
    · exact ⟨Sum.inr p, Subtype.ext rfl⟩
  refine ⟨Equiv.ofBijective (Sum.elim Fl Fr) ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro e he
    show (ext U ⟨e, he⟩ ∩ old U '' {v : Fin N | 0 < 𝓗.deg v}) = old U '' e
    exact ext_inter_verts U ⟨e, he⟩
  · intro p
    show (extS U p ∩ old U '' {v : Fin N | 0 < 𝓗.deg v}) = {old U p.1.1}
    exact extS_inter_verts U p


end

end Work.Deep.Nibble
