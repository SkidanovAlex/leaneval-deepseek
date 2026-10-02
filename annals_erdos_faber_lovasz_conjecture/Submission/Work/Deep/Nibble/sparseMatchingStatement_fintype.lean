import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.Defs

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

/-- **Degree is preserved by transporting a hypergraph along an injective map.**
The degree of `a` in `𝓗` (the number of edges of `𝓗` containing `a`) equals the
degree of `f a` in the pushed-forward hypergraph `(Set.image f) '' 𝓗`. -/
private lemma natCard_deg_image {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (𝓗 : ErdosFaberLovaszConjecture.Hypergraph α) (a : α) :
    Nat.card {e : (Set.image f) '' 𝓗 // f a ∈ (e : Set β)}
      = Nat.card {e : 𝓗 // a ∈ (e : Set α)} := by
  classical
  have h₁ : Nat.card {e : ↥𝓗 // a ∈ (e : Set α)}
      = ({e : ↥𝓗 | a ∈ (e : Set α)} : Set ↥𝓗).ncard := Nat.card_coe_set_eq _
  have h₂ : Nat.card {e' : ↥((Set.image f) '' 𝓗) // f a ∈ (e' : Set β)}
      = ({e' : ↥((Set.image f) '' 𝓗) | f a ∈ (e' : Set β)} : Set ↥((Set.image f) '' 𝓗)).ncard
      := Nat.card_coe_set_eq _
  rw [h₁, h₂]
  symm
  refine Set.ncard_congr
    (fun (e : ↥𝓗) (_ : e ∈ ({e : ↥𝓗 | a ∈ (e : Set α)} : Set ↥𝓗)) =>
      (⟨Set.image f (e : Set α), ⟨(e : Set α), e.2, rfl⟩⟩ : ↥((Set.image f) '' 𝓗))) ?_ ?_ ?_
  · intro e he
    exact Set.mem_image_of_mem f he
  · intro e₁ _ e₂ _ heq
    apply Subtype.ext
    exact (Set.image_eq_image hf).mp (congrArg Subtype.val heq)
  · intro e' he'
    obtain ⟨x, hx, hxe⟩ := e'.2
    have hfa : f a ∈ (e' : Set β) := he'
    rw [← hxe] at hfa
    obtain ⟨y, hy, hfy⟩ := hfa
    have hya : y = a := hf hfy
    have hax : a ∈ x := by rw [← hya]; exact hy
    refine ⟨⟨x, hx⟩, hax, ?_⟩
    apply Subtype.ext
    exact hxe

/-- `cor:sparse_egj` (`SparseMatchingStatement`) transferred from `Fin n` to an
arbitrary finite vertex type: the vertex count is `Fintype.card α`, edge sizes
are `Set.ncard`, and `matchVert` is replaced by the union of the matching. -/
theorem sparseMatchingStatement_fintype
    (hS : ErdosFaberLovaszConjecture.SparseMatchingStatement) :
    ∀ r : ℕ, 2 ≤ r → ∀ κ γ : ℝ, 0 < κ → κ ≤ 1 → 0 < γ → γ ≤ 1 →
      ∃ n₀ : ℝ, 0 < n₀ ∧
      ∀ {α : Type} [Fintype α] [DecidableEq α], n₀ ≤ (Fintype.card α : ℝ) →
      ∀ D : ℝ, (Fintype.card α : ℝ) ^ ((1 : ℝ) / 100) ≤ D →
      ∀ 𝓗 : ErdosFaberLovaszConjecture.Hypergraph α, 𝓗.IsLinear → (∀ e ∈ 𝓗, e.ncard = r) →
        (∀ v : α, |((Nat.card {e : 𝓗 // v ∈ (e : Set α)} : ℝ)) - D| ≤ κ * D) →
        ∀ 𝓕 : Set (Set α),
          (𝓕.ncard : ℝ) ≤ (Fintype.card α : ℝ) ^ (2 * Real.log (Fintype.card α)) →
          ∃ M : Set 𝓗, ErdosFaberLovaszConjecture.IsMatching 𝓗 M ∧
            ∀ S ∈ 𝓕, D ^ ((1 : ℝ) / 20) ≤ (S.ncard : ℝ) →
              |(((S \ ⋃ e ∈ M, (e : Set α)).ncard : ℝ) - γ * (S.ncard : ℝ))| ≤
                4 * κ * (S.ncard : ℝ) := by
  intro r hr κ γ hκ0 hκ1 hγ0 hγ1
  obtain ⟨n₀, hn₀, hbody⟩ := hS r hr κ γ hκ0 hκ1 hγ0 hγ1
  refine ⟨n₀, hn₀, ?_⟩
  intro α _ _ hn D hD 𝓗 hlin hsize hdeg 𝓕 h𝓕
  classical
  -- Transport the whole configuration along `f : α ≃ Fin (Fintype.card α)`.
  let n : ℕ := Fintype.card α
  let f : α ≃ Fin n := Fintype.equivFin α
  have hf : Function.Injective (f : α → Fin n) := f.injective
  have hF : Function.Injective (Set.image (f : α → Fin n) : Set α → Set (Fin n)) :=
    Set.image_injective.mpr hf
  let 𝓗' : ErdosFaberLovaszConjecture.Hypergraph (Fin n) := (Set.image (f : α → Fin n)) '' 𝓗
  let 𝓕' : Set (Set (Fin n)) := (Set.image (f : α → Fin n)) '' 𝓕
  have hlin' : 𝓗'.IsLinear := by
    rintro e₁' ⟨e₁, he₁, rfl⟩ e₂' ⟨e₂, he₂, rfl⟩ hne
    have hne' : e₁ ≠ e₂ := fun h => hne (by rw [h])
    have him : (Set.image (f : α → Fin n) (e₁ ∩ e₂)).Subsingleton :=
      (hlin he₁ he₂ hne').image (f : α → Fin n)
    rwa [Set.image_inter hf] at him
  have hsize' : ∀ e ∈ 𝓗', edgeSize e = r := by
    rintro e' ⟨e, he, rfl⟩
    rw [edgeSize_eq_ncard, Set.ncard_image_of_injective _ hf]
    exact hsize e he
  have hdeg' : ∀ v : Fin n, |((hypergraphDegree 𝓗' v : ℝ)) - D| ≤ κ * D := by
    intro v
    have key : hypergraphDegree 𝓗' v = Nat.card {e : 𝓗 // f.symm v ∈ (e : Set α)} := by
      have h₁ : hypergraphDegree 𝓗' v
          = Nat.card {e : ↥𝓗' // f (f.symm v) ∈ (e : Set (Fin n))} := by
        rw [show hypergraphDegree 𝓗' v
              = Nat.card {e : ↥𝓗' // v ∈ (e : Set (Fin n))} from rfl,
            Equiv.apply_symm_apply f v]
      rw [h₁]
      exact natCard_deg_image (f : α → Fin n) hf 𝓗 (f.symm v)
    rw [key]
    exact hdeg (f.symm v)
  have h𝓕' : (𝓕'.ncard : ℝ) ≤ (n : ℝ) ^ (2 * Real.log n) := by
    have hnc : 𝓕'.ncard = 𝓕.ncard := Set.ncard_image_of_injective 𝓕 hF
    rw [hnc]
    exact h𝓕
  obtain ⟨M', hM'match, hM'prop⟩ := hbody n hn D hD 𝓗' hlin' hsize' hdeg' 𝓕' h𝓕'
  -- Pull the matching back to `α`.
  set Mset' : Set (Set (Fin n)) := Subtype.val '' M' with hMset'def
  have hMset'sub : Mset' ⊆ 𝓗' := by
    rintro z ⟨e', he', rfl⟩
    exact e'.2
  have hMset'pair : Mset'.Pairwise (fun a b => Disjoint a b) := by
    rintro z₁ ⟨e₁', he₁', rfl⟩ z₂ ⟨e₂', he₂', rfl⟩ hne
    exact hM'match he₁' he₂' (fun h => hne (by rw [h]))
  set Mset : Set (Set α) := (Set.image (f.symm : Fin n → α)) '' Mset' with hMsetdef
  have hMset_sub : Mset ⊆ 𝓗 := by
    rintro z ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxe⟩ := hMset'sub hy
    rw [← hxe, Equiv.symm_image_image f x]
    exact hx
  have hMset_pair : Mset.Pairwise (fun a b => Disjoint a b) := by
    rintro z₁ ⟨y₁, hy₁, rfl⟩ z₂ ⟨y₂, hy₂, rfl⟩ hne
    have hne' : y₁ ≠ y₂ := fun h => hne (by rw [h])
    rw [Set.disjoint_left]
    intro z hz hz2
    obtain ⟨u, hu, rfl⟩ := hz
    obtain ⟨v, hv, hvz⟩ := hz2
    have huv : v = u := (f.symm).injective hvz
    rw [huv] at hv
    exact (Set.disjoint_left.mp (hMset'pair hy₁ hy₂ hne')) hu hv
  set Mn : Set ↥𝓗 := {e : ↥𝓗 | (e : Set α) ∈ Mset} with hMndef
  refine ⟨Mn, ?_, ?_⟩
  · rintro e₁ he₁ e₂ he₂ hne
    have hne' : (e₁ : Set α) ≠ (e₂ : Set α) := fun h => hne (Subtype.ext h)
    exact hMset_pair he₁ he₂ hne'
  · intro S hS hScard
    have hS' : (Set.image (f : α → Fin n)) S ∈ 𝓕' := ⟨S, hS, rfl⟩
    have hS'card : ((Set.image (f : α → Fin n)) S).ncard = S.ncard :=
      Set.ncard_image_of_injective S hf
    have hS'thresh : D ^ ((1 : ℝ) / 20) ≤ (((Set.image (f : α → Fin n)) S).ncard : ℝ) := by
      rw [hS'card]; exact hScard
    have hres := hM'prop ((Set.image (f : α → Fin n)) S) hS' hS'thresh
    have hUnion : (⋃ e ∈ Mn, (e : Set α)) = ⋃₀ Mset := by
      have hval : Subtype.val '' Mn = Mset := by
        ext z
        constructor
        · rintro ⟨e, he, rfl⟩
          exact he
        · intro hz
          exact ⟨⟨z, hMset_sub hz⟩, hz, rfl⟩
      rw [← hval, Set.sUnion_image]
    have hMatchVert : matchVert M' = ⋃₀ Mset' := by
      rw [hMset'def, Set.sUnion_image]
      rfl
    have hImgUnion : (Set.image (f : α → Fin n)) (⋃₀ Mset) = matchVert M' := by
      rw [Set.image_sUnion, hMsetdef]
      have h2 : (Set.image (f : α → Fin n)) '' ((Set.image (f.symm : Fin n → α)) '' Mset')
          = Mset' := by
        rw [Set.image_image]
        have hid : (fun x : Set (Fin n) =>
            (Set.image (f : α → Fin n)) ((Set.image (f.symm : Fin n → α)) x)) = id := by
          funext x
          exact Equiv.image_symm_image f x
        rw [hid, Set.image_id]
      rw [h2, ← hMatchVert]
    have himg : (Set.image (f : α → Fin n)) (S \ ⋃ e ∈ Mn, (e : Set α))
        = (Set.image (f : α → Fin n)) S \ matchVert M' := by
      rw [Set.image_sdiff hf, hUnion, hImgUnion]
    have hcard : ((S \ ⋃ e ∈ Mn, (e : Set α)).ncard)
        = (((Set.image (f : α → Fin n)) S) \ matchVert M').ncard := by
      rw [← himg, Set.ncard_image_of_injective _ hf]
    calc |(((S \ ⋃ e ∈ Mn, (e : Set α)).ncard : ℝ) - γ * (S.ncard : ℝ))|
        = |(((((Set.image (f : α → Fin n)) S) \ matchVert M').ncard : ℝ)
            - γ * (((Set.image (f : α → Fin n)) S).ncard : ℝ))| := by
          rw [hcard, ← hS'card]
      _ ≤ 4 * κ * (((Set.image (f : α → Fin n)) S).ncard : ℝ) := hres
      _ = 4 * κ * (S.ncard : ℝ) := by rw [hS'card]

end Work.Deep.Nibble
