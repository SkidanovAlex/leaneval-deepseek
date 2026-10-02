import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.EmbedAux

set_option autoImplicit false

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

noncomputable section

variable {N r : ℕ} {𝓗 : MultiHypergraph N}

/-- The extension of a proper edge of `𝓗` has exactly `r` vertices. -/
theorem ext_ncard (U : UnifData N r 𝓗) (e : {e : Set (Fin N) // e ∈ 𝓗.edges}) :
    (ext U e).ncard = r := by
  have hg : Classical.choose (U.uniq e.1 e.2) ∈ U.𝓖 := (ext_spec U e).1
  have h1 : (Classical.choose (U.uniq e.1 e.2)).ncard = r := by
    rw [← edgeSize_eq_ncard]
    exact U.unif _ hg
  rw [ext, Set.ncard_image_of_injective _ Sum.inl_injective]
  exact h1

/-- The extension of a singleton copy has exactly `r` vertices. -/
theorem extS_ncard (U : UnifData N r 𝓗) (hr : 2 ≤ r) (p : SC 𝓗) :
    (extS U p).ncard = r := by
  have hinj : Function.Injective
      (fun j : Fin (r - 1) => (Sum.inr ⟨p, j⟩ : Vstar 𝓗 r U.M)) := by
    intro a b h
    exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr_injective h)).2
  have hdisj : Disjoint ({old U p.1.1} : Set (Vstar 𝓗 r U.M))
      (Set.range (fun j : Fin (r - 1) => (Sum.inr ⟨p, j⟩ : Vstar 𝓗 r U.M))) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [Set.mem_singleton_iff] at hx
    obtain ⟨j, hj⟩ := Set.mem_range.mp hx'
    rw [hx] at hj
    exact Sum.inr_ne_inl hj
  rw [extS, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    Set.ncard_singleton, Set.ncard_range_of_injective hinj, Nat.card_fin]
  omega

/-- Two distinct proper-edge extensions meet in at most one vertex. -/
theorem ext_inter_ext (U : UnifData N r 𝓗) {e e' : {e : Set (Fin N) // e ∈ 𝓗.edges}}
    (hne : ext U e ≠ ext U e') : (ext U e ∩ ext U e').Subsingleton := by
  have hg : Classical.choose (U.uniq e.1 e.2) ∈ U.𝓖 := (ext_spec U e).1
  have hg' : Classical.choose (U.uniq e'.1 e'.2) ∈ U.𝓖 := (ext_spec U e').1
  have hgg : Classical.choose (U.uniq e.1 e.2) ≠ Classical.choose (U.uniq e'.1 e'.2) := by
    intro h
    exact hne (by rw [ext, ext, h])
  have hsub := U.lin hg hg' hgg
  rw [ext, ext, ← Set.image_inter Sum.inl_injective]
  exact hsub.image Sum.inl

/-- A proper-edge extension meets a singleton extension in at most one vertex. -/
theorem ext_inter_extS (U : UnifData N r 𝓗) (p : SC 𝓗)
    (e : {e : Set (Fin N) // e ∈ 𝓗.edges}) : (ext U e ∩ extS U p).Subsingleton := by
  have hsub : ext U e ∩ extS U p ⊆ ({old U p.1.1} : Set (Vstar 𝓗 r U.M)) := by
    rintro x ⟨hx1, hx2⟩
    rw [Set.mem_singleton_iff]
    rw [ext] at hx1
    obtain ⟨y, -, rfl⟩ := hx1
    have hxr : (Sum.inl y : Vstar 𝓗 r U.M) ∈
        extS U p ∩ Set.range (Sum.inl : Fin U.M → Vstar 𝓗 r U.M) := ⟨hx2, ⟨y, rfl⟩⟩
    rwa [extS_inter_inl U p] at hxr
  have hB : ({old U p.1.1} : Set (Vstar 𝓗 r U.M)).Subsingleton := Set.subsingleton_singleton
  exact hB.anti hsub

/-- Two distinct singleton extensions meet in at most one vertex. -/
theorem extS_inter_extS (U : UnifData N r 𝓗) {p p' : SC 𝓗}
    (hne : extS U p ≠ extS U p') : (extS U p ∩ extS U p').Subsingleton := by
  have hpp : p ≠ p' := fun h => hne (by rw [h])
  have hsub : extS U p ∩ extS U p' ⊆ ({old U p.1.1} : Set (Vstar 𝓗 r U.M)) := by
    rintro x ⟨hx1, hx2⟩
    rw [Set.mem_singleton_iff]
    rcases (mem_extS U p).mp hx1 with h | ⟨j, hj⟩
    · exact h
    · exfalso
      rw [← hj] at hx2
      rcases (mem_extS U p').mp hx2 with h' | ⟨j', hj'⟩
      · exact Sum.inr_ne_inl h'
      · exact hpp (Sigma.mk.inj_iff.mp (Sum.inr_injective hj')).1.symm
  have hB : ({old U p.1.1} : Set (Vstar 𝓗 r U.M)).Subsingleton := Set.subsingleton_singleton
  exact hB.anti hsub

open ErdosFaberLovaszConjecture in
/-- `𝓗*` is `r`-uniform and linear.  Ingredients already in
`Submission/Work/Deep/Nibble/EmbedAux.lean`: `ext_spec` (`ext U e = Sum.inl '' g`
with `g ∈ U.𝓖`, so `g.ncard = r` by `U.unif` + `edgeSize_eq_ncard`),
`mem_extS`, `extS_inter_inl`, `extS_inj`, `ext_inj`, and `Sum.inl_injective`. -/
theorem Hstar_unif_linear {N r : ℕ} (𝓗 : MultiHypergraph N) (U : Work.Deep.Nibble.UnifData N r 𝓗)
    (hr : 2 ≤ r) :
    (∀ f ∈ Work.Deep.Nibble.Hstar U, f.ncard = r) ∧
      (∀ ⦃f⦄, f ∈ Work.Deep.Nibble.Hstar U → ∀ ⦃f'⦄, f' ∈ Work.Deep.Nibble.Hstar U → f ≠ f' →
        (f ∩ f').Subsingleton) := by
  constructor
  · intro f hf
    rcases (mem_Hstar U).mp hf with ⟨e, rfl⟩ | ⟨p, rfl⟩
    · exact ext_ncard U e
    · exact extS_ncard U hr p
  · intro f hf f' hf' hne
    rcases (mem_Hstar U).mp hf with ⟨e, rfl⟩ | ⟨p, rfl⟩
    · rcases (mem_Hstar U).mp hf' with ⟨e', rfl⟩ | ⟨p', rfl⟩
      · exact ext_inter_ext U hne
      · exact ext_inter_extS U p' e
    · rcases (mem_Hstar U).mp hf' with ⟨e', rfl⟩ | ⟨p', rfl⟩
      · rw [Set.inter_comm]
        exact ext_inter_extS U p e'
      · exact extS_inter_extS U hne

end

end Work.Deep.Nibble
