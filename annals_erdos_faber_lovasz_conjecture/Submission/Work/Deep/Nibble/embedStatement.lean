import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.EmbedAux
import Submission.Work.Deep.Nibble.EmbedStar
import Submission.Work.Deep.Nibble.EmbedDes
import Submission.Work.Deep.Nibble.EmbedCount
import Submission.Work.Deep.Nibble.EmbedGlue
import Submission.Work.Deep.Nibble.EmbedTransport
import Submission.Work.Deep.Nibble.Hstar_unif_linear

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

noncomputable section

/-- **The embedding result `lem:embed` of §8, as `EmbedStatement`.**

`Submission/EFL/Embed.lean` states `EmbedStatement` (now with the paper's
`D ≥ D₀`, as `(1 : ℝ) ≤ D`) but only the *uniformisation step* of its proof is
formalised in the cone (`exists_uniform_extension` in `EmbedProof.lean`); this
module closes the gap, in the layering

* `EmbedAux` — the vocabulary: `UnifData`, `SC`, `Vstar`, `old`, `ext`, `extS`,
  `Hstar`, and the prescriptions `HstarDeg`, `mdeg`, `dprime`, `dmax`,
  `designPrime`, `T`, `des`;
* `EmbedUnif` — the uniformisation step, with the extra property that the fresh
  vertices of `𝓖₀` have degree at most one (needed so that `d_{𝓗*}` — and hence
  the prescribed degree `mdeg` — is controlled at *every* vertex of `𝓗*`);
* `EmbedStar` — the degrees of `𝓗*` and the identification `κ₀`;
* `EmbedDes` — the glued designs `des` (uniform, linear, degree `dprime`,
  empty when `dprime = 0`);
* `EmbedGlue` — the gluing `𝓖 = Clone.glue T 𝓗* des`, its uniformity,
  linearity, degrees and identification `κ`;
* `EmbedCount` — the double count and the vertex bound `(E3)`;
* `EmbedTransport` — the transport of the construction from
  `Fin T × V(𝓗*)` to `Fin M`.

The construction is exactly the paper's: uniformise the proper edges (each with
its own block of fresh vertices) and the singleton copies (each with its own
`r - 1` fresh vertices) to get the `r`-uniform linear `𝓗*`; take `T = r·p ≤ 2rD`
copies, `p` a prime `> max r dmax` (Bertrand, and `T = 1` when no design is
needed); and glue at the clones of every `u ∈ V(𝓗*)` a copy of the `d`-regular
design of `exists_linear_regular_uniform` with `d = dprime D C U u`, chosen so
that `d_{𝓗*}(u) + dprime u = mdeg D C U u ∈ [D - C, D]` — which is the paper's
`D - d_{𝓗*}(u)` at the isolated old vertices and the fresh vertices, and `0` at
the non-isolated old vertices (where `d_{𝓗*}(u) = d_𝓗(u) ≥ D - C` already). -/
theorem embedStatement : ErdosFaberLovaszConjecture.EmbedStatement := by
  intro r hr
  refine ⟨(r : ℝ), by positivity, le_refl _, ?_⟩
  intro N C D hC hD0 hD1 𝓗 hlin hsize hdegD hdegC
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
