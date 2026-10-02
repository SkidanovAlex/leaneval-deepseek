import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.ObjDefs
import Submission.Work.Deep.Nibble.embedStatement

/-!
# `embedStatement_at_r`: `lem:embed` packaged at the explicit constant `C₀ = r`

`Work.Deep.Nibble.embedStatement` proves `EmbedStatement` with the *explicit*
constant `C₀ = (r : ℝ)` (the value produced by the construction, and the value
the §7/§8 reduction consumes: the threshold of `lem:pseudorandom_matching`
involves `C₀`).  That fact is hidden behind the existential `∃ C₀` of
`EmbedStatement`, so the theorem `embedStatement` alone only yields the
conclusion for `C ≥ C₀` for an unspecified `C₀ ≥ r`.

This module exposes the body at `C₀ = r`, i.e. `ErdosFaberLovaszConjecture.EmbedAtR r`:
the same construction, replayed with the constant `r` substituted for `C₀` (the
proof of `embedStatement` already establishes the body for every `C ≥ r`, so the
proof below is the body of that proof with the `∃ C₀` packaging removed).
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

noncomputable section

/-- **`lem:embed` at the explicit constant `C₀ = r`** (see
`ErdosFaberLovaszConjecture.EmbedAtR`).  This is `lem:embed` with the existential
`C₀` of `EmbedStatement` instantiated at the value `r` produced by the
construction: for every linear `r`-bounded `N`-vertex multi-hypergraph `𝓗` with
`Δ(𝓗) ≤ D` and `D - C ≤ d_𝓗(v)` at every non-isolated `v`, and `C ≥ r`, there is
an `r`-uniform linear `𝓖` on `M ≤ r(r-1)²D³N` vertices with an embedding `ι` of
`V(𝓗)` and a bijection `κ` of the edges meeting `ι '' V(𝓗)` with the (multi-)edges
of `𝓗`, degrees in `[D - C, D]`, and agreement with `d_𝓗` at non-isolated
vertices. -/
theorem embedStatement_at_r {r : ℕ} (hr : 3 ≤ r) :
    ErdosFaberLovaszConjecture.EmbedAtR r := by
  intro N D C 𝓗 hC hD0 hD1 hlin hsize hdegD hdegC
  have hr2 : 2 ≤ r := by omega
  have hC1 : 1 ≤ C := le_trans (by exact_mod_cast (by omega : 1 ≤ r)) hC
  obtain ⟨U⟩ := exists_unifData 𝓗 hr2 hlin hsize
  -- the vertex set of `𝓖`, and the transport to `Fin M`
  let Mf : ℕ := T hr D C U * Nat.card (Vstar 𝓗 r U.M)
  let vE : Vstar 𝓗 r U.M ≃ Fin (Nat.card (Vstar 𝓗 r U.M)) :=
    Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card (α := Vstar 𝓗 r U.M)).symm
  let eE : Fin (T hr D C U) × Vstar 𝓗 r U.M ≃ Fin Mf :=
    (Equiv.prodCongr (Equiv.refl (Fin (T hr D C U))) vE).trans finProdFinEquiv
  let ι : Fin N ↪ Fin Mf :=
    ⟨fun v => eE (iotaG hr D C U v), fun a b h => iotaG_inj hr U (eE.injective h)⟩
  let 𝒢 : Set (Set (Fin Mf)) := transportH eE (GG hr D C U)
  have hιS : ∀ S : Set (Fin N), eE '' (iotaG hr D C U '' S) = ι '' S := by
    intro S
    ext x; constructor
    · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨iotaG hr D C U v, ⟨v, hv, rfl⟩, rfl⟩
  have hι := hιS (Verts 𝓗)
  obtain ⟨κ₀, hκ₀e, hκ₀s⟩ := GG_ident hr hlin hD0 U hdegC
  let κ : ({e : Set (Fin N) // e ∈ 𝓗.edges} ⊕ SC 𝓗) ≃
      {f : Set (Fin Mf) // f ∈ 𝒢 ∧ (f ∩ ι '' Verts 𝓗).Nonempty} :=
    κ₀.trans ((transportH_ident eE (GG hr D C U) (iotaG hr D C U '' Verts 𝓗)).trans
      (subtype_congr_meet hι))
  have hκval : ∀ a : ({e : Set (Fin N) // e ∈ 𝓗.edges} ⊕ SC 𝓗),
      (κ a).1 = eE '' (κ₀ a).1 := fun a => rfl
  refine ⟨Mf, ι, 𝒢, κ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf
    rw [edgeSize_eq_ncard]
    exact transportH_ncard (𝓗 := GG hr D C U) (GG_ncard hr D C U) f hf
  · exact transportH_linear (𝓗 := GG hr D C U) (GG_linear hr D C U)
  · have h := card_G_le U hr hlin hC hD1 hdegD
    simpa only [Mf, Nat.cast_mul] using h
  · intro e he
    calc ((κ (Sum.inl ⟨e, he⟩)).1 ∩ ι '' Verts 𝓗)
        = eE '' ((κ₀ (Sum.inl ⟨e, he⟩)).1
            ∩ iotaG hr D C U '' Verts 𝓗) := by
          rw [hκval, ← hι, Set.image_inter eE.injective]
      _ = eE '' (iotaG hr D C U '' e) := by rw [hκ₀e e he]
      _ = ι '' e := hιS e
  · intro v k hk
    calc ((κ (Sum.inr ⟨(v, k), hk⟩)).1 ∩ ι '' Verts 𝓗)
        = eE '' ((κ₀ (Sum.inr ⟨(v, k), hk⟩)).1
            ∩ iotaG hr D C U '' Verts 𝓗) := by
          rw [hκval, ← hι, Set.image_inter eE.injective]
      _ = eE '' {iotaG hr D C U v} := by rw [hκ₀s ⟨(v, k), hk⟩]
      _ = {ι v} := by rw [Set.image_singleton]; rfl
  · intro w
    obtain ⟨x, rfl⟩ := eE.surjective w
    obtain ⟨i, u⟩ := x
    have hdeg : ({f ∈ 𝒢 | eE (i, u) ∈ f} : Set (Set (Fin Mf))).ncard
        = ({f ∈ GG hr D C U | (i, u) ∈ f} : Set _).ncard := by
      show ({f ∈ transportH eE (GG hr D C U) | eE (i, u) ∈ f} : Set _).ncard = _
      exact transportH_deg (i, u)
    have h1 : MultiHypergraph.hdeg 𝒢 (eE (i, u)) = mdeg D C U u := by
      rw [MultiHypergraph.hdeg, hdeg, GG_deg hr D C U i u]
    rw [h1]
    exact mdeg_bounds hr hC1 hD0 hD1 U hdegD u
  · intro v hv
    have h1 : MultiHypergraph.hdeg 𝒢 (ι v) = mdeg D C U (old U v) := by
      show ({f ∈ transportH eE (GG hr D C U)
        | eE (iotaG hr D C U v) ∈ f} : Set _).ncard = _
      rw [transportH_deg (iotaG hr D C U v)]
      simp only [iotaG]
      rw [GG_deg hr D C U ⟨0, T_pos hr D C U⟩ (old U v)]
    rw [h1, mdeg_old hr hD0 U hdegC hv]

end

end Work.Deep.Nibble
