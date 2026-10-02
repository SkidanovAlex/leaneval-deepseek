import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.ObjDefs
import Submission.Work.Deep.Nibble.AuxDefs
import Submission.Work.Deep.Nibble.aux_card
import Submission.Work.Deep.Nibble.aux_uniform_and_linear
import Submission.Work.Deep.Nibble.aux_degree
import Submission.Work.Deep.Nibble.sum_hdeg_eq_card_mul
import Submission.Work.Deep.Nibble.psi_facts
import Submission.Work.Deep.Nibble.PsMHelpers
import Submission.Work.Deep.Nibble.card_bound_embed
import Submission.Work.Deep.Nibble.embedStatement_at_r
import Submission.Work.Deep.Nibble.sparseMatchingStatement_fintype
import Submission.Work.Deep.Nibble.objCover
import Submission.Work.Deep.Nibble.objThrough_ncard

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

noncomputable section

set_option allowUnsafeReducibility true in
attribute [local reducible] EdgeObj

/-! ## Transport of `SparseMatchingAbove` to an arbitrary finite vertex type -/

/-- Degree is preserved by transporting a hypergraph along an injective map.
(copy of the private helper of `sparseMatchingStatement_fintype`) -/
theorem natCard_deg_image_obj {α β : Type*} (f : α → β) (hf : Function.Injective f)
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

/-- `SparseMatchingAbove` transferred from `Fin n` to an arbitrary finite vertex
type.  This is `sparseMatchingStatement_fintype` with the existential threshold
replaced by the explicit `N₀` of `SparseMatchingAbove`. -/
theorem sparseMatchingAbove_fintype
    {N₀ r : ℕ} {κ γ : ℝ} (hS : ErdosFaberLovaszConjecture.SparseMatchingAbove N₀ r κ γ) :
    ∀ {α : Type} [Fintype α] [DecidableEq α], N₀ ≤ Fintype.card α →
      ∀ D : ℝ, (Fintype.card α : ℝ) ^ ((1 : ℝ) / 100) ≤ D →
      ∀ 𝓗 : ErdosFaberLovaszConjecture.Hypergraph α, 𝓗.IsLinear →
        (∀ e ∈ 𝓗, e.ncard = r) →
        (∀ v : α, |((Nat.card {e : 𝓗 // v ∈ (e : Set α)} : ℝ)) - D| ≤ κ * D) →
        ∀ 𝓕 : Set (Set α),
          (𝓕.ncard : ℝ) ≤ (Fintype.card α : ℝ) ^ (2 * Real.log (Fintype.card α)) →
          ∃ M : Set 𝓗, ErdosFaberLovaszConjecture.IsMatching 𝓗 M ∧
            ∀ S ∈ 𝓕, D ^ ((1 : ℝ) / 20) ≤ (S.ncard : ℝ) →
              |(((S \ ⋃ e ∈ M, (e : Set α)).ncard : ℝ) - γ * (S.ncard : ℝ))| ≤
                4 * κ * (S.ncard : ℝ) := by
  intro α _ _ hN₀ D hD 𝓗 hlin hsize hdeg 𝓕 h𝓕
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
      exact natCard_deg_image_obj (f : α → Fin n) hf 𝓗 (f.symm v)
    rw [key]
    exact hdeg (f.symm v)
  have h𝓕' : (𝓕'.ncard : ℝ) ≤ (n : ℝ) ^ (2 * Real.log n) := by
    have hnc : 𝓕'.ncard = 𝓕.ncard := Set.ncard_image_of_injective 𝓕 hF
    rw [hnc]
    exact h𝓕
  obtain ⟨M', hM'match, hM'prop⟩ := hS n hN₀ D hD 𝓗' hlin' hsize' hdeg' 𝓕' h𝓕'
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
  · intro S hS' hScard
    have hS' : (Set.image (f : α → Fin n)) S ∈ 𝓕' := ⟨S, hS', rfl⟩
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

/-! ## `lem:embed` packaged as an `EmbedWitness` -/

/-- `EmbedAtR r` produces an `EmbedWitness` whenever its hypotheses hold. -/
theorem embedWitness_of_embedAtR {r : ℕ} (hE : EmbedAtR r) {n : ℕ} (D' C : ℝ)
    (𝓗' : MultiHypergraph n) (hC : (r : ℝ) ≤ C) (hD0 : 0 < D') (hD1 : (1 : ℝ) ≤ D')
    (hlin : 𝓗'.IsLinear) (hsize : ∀ e ∈ 𝓗'.edges, edgeSize e ≤ r)
    (hle : ∀ v : Fin n, (𝓗'.deg v : ℝ) ≤ D')
    (hlo : ∀ v : Fin n, 0 < 𝓗'.deg v → D' - C ≤ (𝓗'.deg v : ℝ)) :
    Nonempty (EmbedWitness n r D' C 𝓗') := by
  obtain ⟨M, ι, 𝓖, κ, huni, hlin', hcard, hinl, hinr, hdeg, hdegold⟩ :=
    hE D' C 𝓗' hC hD0 hD1 hlin hsize hle hlo
  exact ⟨⟨M, ι, 𝓖, κ, huni, hlin', hcard, hinl, hinr,
    (fun w => (hdeg w).1), (fun w => (hdeg w).2), hdegold⟩⟩

/-! ## `ψ` of the `κ`-preimage of an edge object -/

section PsiOfKappa

variable {n r : ℕ} {D' C : ℝ} {𝓗' : MultiHypergraph n}

/-- `ψ` of the edge of `𝓖` attached to an edge object `x` of `𝓗'` is the vertex
set of `x` (`e` for a proper edge, `{v}` for a copy of the singleton `{v}`). -/
theorem psiOf_kappa (W : EmbedWitness n r D' C 𝓗') (x : EdgeObj 𝓗') :
    psiOf W (W.κ x) = EdgeObj.toSet x := by
  unfold psiOf
  rw [Equiv.symm_apply_apply]
  rcases x with e | p <;> rfl

end PsiOfKappa

/-- If `auxEdge f i = auxEdge f j` and `f` is nonempty and misses
`ι '' V(M j)`, then `i = j`.  (The hypothesis for `i` is not needed: the
`w^j`-clone of any `w ∈ f` lies in both edges.) -/
theorem auxEdge_eq_index_of_disj {n M D : ℕ} {𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin M)}
    {ι : Fin n ↪ Fin M} {Mfam : Fin D → Set (Set (Fin n))} {f : Set (Fin M)}
    (hf : f.Nonempty) {i j : Fin D}
    (hdj : f ∩ ι '' famVert (Mfam j) = ∅)
    (h : auxEdge n M D 𝓖 ι Mfam f i = auxEdge n M D 𝓖 ι Mfam f j) : i = j := by
  obtain ⟨v, hv⟩ := hf
  have hvj : v ∉ ι '' famVert (Mfam j) := by
    intro hmem
    have hmem' : v ∈ f ∩ ι '' famVert (Mfam j) := ⟨hv, hmem⟩
    rw [hdj] at hmem'
    exact hmem'
  have hmem : auxVInr n M D 𝓖 ι Mfam j v hvj ∈ auxEdge n M D 𝓖 ι Mfam f j :=
    (auxVInr_mem_auxEdge hvj).2 ⟨rfl, hv⟩
  rw [← h] at hmem
  rcases (val_mem_auxEdge (auxVInr n M D 𝓖 ι Mfam j v hvj) f i).mp hmem with hh | ⟨w, hh, _⟩
  · exact absurd hh Sum.inr_ne_inl
  · exact (congrArg Prod.fst (Sum.inr.inj hh)).symm

/-! ## The object family for `SparseMatchingBody` -/

/-- The family of `𝓖`-edges attached to a family of edge objects of `𝓗'`. -/
def kappaImg {n r : ℕ} {D' C : ℝ} {𝓗' : MultiHypergraph n} (W : EmbedWitness n r D' C 𝓗')
    (F : Set (EdgeObj 𝓗')) : Set (Set (Fin W.M)) := (fun x => (W.κ x).1) '' F

/-- The family `𝓕^aux` of the proof of `lem:pseudorandom_matching`, with the
`𝓕E`-part attached to the *objects* of `𝓕E` rather than to their `ψ`-images. -/
def auxFamObj {n r : ℕ} {D' C : ℝ} {𝓗' : MultiHypergraph n} (W : EmbedWitness n r D' C 𝓗')
    (D : ℕ) (𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin W.M)) (ι : Fin n ↪ Fin W.M)
    (Mfam : Fin D → Set (Set (Fin n))) (𝓕V : Set (Set (Fin n))) (𝓕E : Set (Set (EdgeObj 𝓗'))) :
    Set (Set (AuxVertex n W.M D 𝓖 ι Mfam)) :=
  (⋃ i : Fin D, phiSet n W.M D 𝓖 ι Mfam i '' 𝓕V) ∪
    (fun F : Set (EdgeObj 𝓗') => inlSet n W.M D 𝓖 ι Mfam (kappaImg W F)) '' 𝓕E

/-- Membership in `objFam` (unfolded, to keep pattern-matching predictable). -/
theorem mem_objFam_iff {n : ℕ} {𝓜 : MultiHypergraph n} {N : Set (EdgeObj 𝓜)} {e : Set (Fin n)} :
    e ∈ objFam N ↔ ∃ x ∈ N, EdgeObj.toSet x = e := Iff.rfl

theorem pseudorandomMatchingObj_of_embed_sparse
    {r : ℕ} (hr : 3 ≤ r) {β κ γ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hγ : 0 < γ)
    (h10β : 10 * β ≤ κ) (h4κ : 4 * κ ≤ γ) (hγ1 : γ ≤ 1)
    (hE : EmbedAtR r)
    {N₁ : ℕ} (hS : SparseMatchingAbove N₁ (r + 1) (2 * β) γ)
    {n : ℕ} (hn4 : 4 ≤ n) (hnr : 2 * r ^ 3 ≤ n) (hnN₁ : N₁ ≤ n)
    (hnβ : (r / (2 * β)) ^ 2 + 1 ≤ (n : ℝ)) (hnκ : (30 / κ) ^ 40 + 1 ≤ (n : ℝ))
    (hne : Real.exp 2 + 1 ≤ (n : ℝ)) :
    PseudorandomMatchingAtObj n r β κ γ := by
  classical
  intro 𝓗 𝓗' 𝓕V 𝓕E D M hDlo hDhi hlin hlin' hle hdeg hsize hFV hFE
    hMmatch hMout hMdisj hMsz hMint
  have _hMmatch := hMmatch
  have _hMout := hMout
  have _hMdisj := hMdisj
  have _hlin := hlin
  have _hle := hle
  -- ---------------------------------------------------------------- thresholds
  have hn4' : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hn1' : 1 ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn2r3 : 2 * (r : ℝ) ^ 3 ≤ (n : ℝ) := by exact_mod_cast hnr
  have hD1 : 1 ≤ D := by
    have h : (1 : ℝ) ≤ (D : ℝ) := le_trans (Real.one_le_rpow hn1 (by norm_num)) hDlo
    exact_mod_cast h
  have hD0 : (0 : ℝ) < (D : ℝ) :=
    lt_of_lt_of_le one_pos (by exact_mod_cast hD1 : (1 : ℝ) ≤ (D : ℝ))
  have hDn : D ≤ n := by exact_mod_cast hDhi
  have hD2 : (2 : ℝ) ≤ (D : ℝ) := by
    have h4 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by rw [← Real.sqrt_eq_rpow]; norm_num
    have h : (4 : ℝ) ^ ((1 : ℝ) / 2) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (by norm_num) hn4' (by norm_num)
    rw [h4] at h
    linarith
  have hκ1 : κ ≤ 1 := by linarith
  have hβle : β ≤ 1 / 4 := by linarith
  have hDinv : (D : ℝ) ^ (1 / 20 : ℝ) ≤ (κ / 20) * (D : ℝ) :=
    rpow_inv_bound hκ hκ1 (by linarith [hnκ]) hDlo
  -- every vertex of `𝓗'` is non-isolated
  have hVuniv : ∀ v : Fin n, 0 < 𝓗'.deg v := by
    intro v
    have h := hdeg v
    rw [abs_le] at h
    have hD1r : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
    have : (0 : ℝ) < (𝓗'.deg v : ℝ) := by nlinarith [h.1, hD1r, hβle, hD0, hβ]
    exact_mod_cast this
  -- -------------------------------------------------- the embedding `lem:embed`
  have hC₀pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hC₀le : (r : ℝ) ≤ 2 * β * (D : ℝ) := embed_C_bound hβ hC₀pos hnβ hDlo
  have hWDpos : (0 : ℝ) < (1 + β) * (D : ℝ) := mul_pos (by linarith) hD0
  have hWD1 : (1 : ℝ) ≤ (1 + β) * (D : ℝ) := by
    have h1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
    nlinarith [hβ, hD0, h1]
  have hdegD : ∀ v : Fin n, (𝓗'.deg v : ℝ) ≤ (1 + β) * (D : ℝ) := by
    intro v; have h := hdeg v; rw [abs_le] at h; linarith [h.2]
  have hdegC : ∀ v : Fin n, 0 < 𝓗'.deg v →
      (1 + β) * (D : ℝ) - 2 * β * (D : ℝ) ≤ (𝓗'.deg v : ℝ) := by
    intro v _; have h := hdeg v; rw [abs_le] at h; nlinarith [h.1]
  obtain ⟨W⟩ := embedWitness_of_embedAtR hE ((1 + β) * (D : ℝ)) (2 * β * (D : ℝ)) 𝓗'
    hC₀le hWDpos hWD1 hlin' hsize hdegD hdegC
  have hWuni : ∀ f ∈ W.𝓖, f.ncard = r := by
    intro f hf; rw [← edgeSize_eq_ncard]; exact W.uni f hf
  have hWlo : ∀ w : Fin W.M, (1 - β) * (D : ℝ) ≤ (MultiHypergraph.hdeg W.𝓖 w : ℝ) := by
    intro w; have h := W.deg_lo w; nlinarith [h]
  have hWhi : ∀ w : Fin W.M, (MultiHypergraph.hdeg W.𝓖 w : ℝ) ≤ (1 + β) * (D : ℝ) := W.deg_hi
  have hWM : (W.M : ℝ) ≤ (n : ℝ) ^ 5 := card_bound_embed hβ hβle hD0 hDhi hn2r3 W.card
  obtain ⟨hpsi1, hpsi2, hpsi3, hpsi4⟩ := psi_facts W hVuniv M hβ hMint
  have hunif := hpsi4
  have haux := aux_uniform_and_linear (n := n) (M := W.M) (D := D) (𝓖 := W.𝓖) (ι := W.ι)
    (Mfam := M) hWuni W.lin
  have huni_aux : ∀ A ∈ auxHypergraph n W.M D W.𝓖 W.ι M, A.ncard = r + 1 := haux.1
  have hlin_aux : (auxHypergraph n W.M D W.𝓖 W.ι M).IsLinear := haux.2
  have hdeg_aux : ∀ v : AuxVertex n W.M D W.𝓖 W.ι M,
      |((Nat.card {e : auxHypergraph n W.M D W.𝓖 W.ι M //
          v ∈ (e : Set (AuxVertex n W.M D W.𝓖 W.ι M))} : ℝ)) - (D : ℝ)| ≤
        (2 * β) * (D : ℝ) := by
    intro v
    have h := aux_degree (n := n) (M := W.M) (D := D) (r := r) (𝓖 := W.𝓖) (ι := W.ι)
      (Mfam := M) (β := β) (by omega) hWuni W.lin hβ (by linarith : β ≤ 1 / 2) hMsz hWlo
      hWhi hunif v
    rwa [degreeAt_eq] at h
  have hcard_aux := aux_card (n := n) (M := W.M) (D := D) (r := r) (𝓖 := W.𝓖) (ι := W.ι)
    (Mfam := M) (β := β) (by omega) hWuni (fun w => by have h := hWhi w; nlinarith [h, hβ])
    (by linarith : β ≤ 1 / 2) hMsz hWM hDhi hD2 (by linarith : (3 : ℝ) ≤ (n : ℝ))
  have hX_ge : N₁ ≤ Fintype.card (AuxVertex n W.M D W.𝓖 W.ι M) := by
    have h : (N₁ : ℝ) ≤ (Fintype.card (AuxVertex n W.M D W.𝓖 W.ι M) : ℝ) :=
      le_trans (by exact_mod_cast hnN₁) hcard_aux.1
    exact_mod_cast h
  have hX100 : (Fintype.card (AuxVertex n W.M D W.𝓖 W.ι M) : ℝ) ^ ((1 : ℝ) / 100) ≤ (D : ℝ) :=
    cardX_rpow_le_D (by positivity) hcard_aux.2 hn1 hDlo
  have hfamcard : ((auxFamObj W D W.𝓖 W.ι M 𝓕V 𝓕E).ncard : ℝ) ≤
      (Fintype.card (AuxVertex n W.M D W.𝓖 W.ι M) : ℝ) ^
        (2 * Real.log (Fintype.card (AuxVertex n W.M D W.𝓖 W.ι M) : ℝ)) := by
    have h1 : (auxFamObj W D W.𝓖 W.ι M 𝓕V 𝓕E).ncard ≤
        (⋃ i : Fin D, phiSet n W.M D W.𝓖 W.ι M i '' 𝓕V).ncard +
          ((fun F : Set (EdgeObj 𝓗') =>
            inlSet n W.M D W.𝓖 W.ι M (kappaImg W F)) '' 𝓕E).ncard := by
      unfold auxFamObj
      exact Set.ncard_union_le _ _
    have h2 : (⋃ i : Fin D, phiSet n W.M D W.𝓖 W.ι M i '' 𝓕V).ncard ≤ 𝓕V.ncard * D := by
      have h3 := ncard_iUnion_le (fun i : Fin D => phiSet n W.M D W.𝓖 W.ι M i '' 𝓕V)
      calc (⋃ i : Fin D, phiSet n W.M D W.𝓖 W.ι M i '' 𝓕V).ncard
          ≤ ∑ i : Fin D, (phiSet n W.M D W.𝓖 W.ι M i '' 𝓕V).ncard := h3
        _ ≤ ∑ _i : Fin D, 𝓕V.ncard := Finset.sum_le_sum (fun i _ => Set.ncard_image_le)
        _ = 𝓕V.ncard * D := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    have h4 : ((fun F : Set (EdgeObj 𝓗') =>
        inlSet n W.M D W.𝓖 W.ι M (kappaImg W F)) '' 𝓕E).ncard ≤ 𝓕E.ncard :=
      Set.ncard_image_le
    have h6 : (auxFamObj W D W.𝓖 W.ι M 𝓕V 𝓕E).ncard ≤ D * 𝓕V.ncard + 𝓕E.ncard := by
      calc (auxFamObj W D W.𝓖 W.ι M 𝓕V 𝓕E).ncard
          ≤ (⋃ i : Fin D, phiSet n W.M D W.𝓖 W.ι M i '' 𝓕V).ncard +
            ((fun F : Set (EdgeObj 𝓗') =>
              inlSet n W.M D W.𝓖 W.ι M (kappaImg W F)) '' 𝓕E).ncard := h1
        _ ≤ 𝓕V.ncard * D + 𝓕E.ncard := add_le_add h2 h4
        _ = D * 𝓕V.ncard + 𝓕E.ncard := by ring
    have h7 := auxFam_card_le (D := (D : ℝ)) (n := (n : ℝ))
      (X := (Fintype.card (AuxVertex n W.M D W.𝓖 W.ι M) : ℝ))
      (FV := (𝓕V.ncard : ℝ)) (FE := (𝓕E.ncard : ℝ))
      (by positivity) hDhi hcard_aux.1 (by linarith : Real.exp 2 ≤ (n : ℝ)) (by positivity) hFV hFE
    calc ((auxFamObj W D W.𝓖 W.ι M 𝓕V 𝓕E).ncard : ℝ)
        ≤ ((D * 𝓕V.ncard + 𝓕E.ncard : ℕ) : ℝ) := by exact_mod_cast h6
      _ = (D : ℝ) * (𝓕V.ncard : ℝ) + (𝓕E.ncard : ℝ) := by push_cast; ring
      _ ≤ (Fintype.card (AuxVertex n W.M D W.𝓖 W.ι M) : ℝ) ^
            (2 * Real.log (Fintype.card (AuxVertex n W.M D W.𝓖 W.ι M) : ℝ)) := h7
  obtain ⟨Nstar, hNmatch, hNcov⟩ :=
    sparseMatchingAbove_fintype hS hX_ge (D : ℝ) hX100
      (auxHypergraph n W.M D W.𝓖 W.ι M) hlin_aux huni_aux hdeg_aux
      (auxFamObj W D W.𝓖 W.ι M 𝓕V 𝓕E) hfamcard
  have hNpair : ∀ A ∈ Nstar, ∀ B ∈ Nstar, A ≠ B →
      Disjoint (A : Set (AuxVertex n W.M D W.𝓖 W.ι M)) (B : Set (AuxVertex n W.M D W.𝓖 W.ι M)) :=
    fun A hA B hB hAB => hNmatch hA hB hAB
  -- ------------------------------------------------------- the object family
  set Nobj : Fin D → Set (EdgeObj 𝓗') := fun i =>
    {x | ∃ A ∈ Nstar, A.1 = auxEdge n W.M D W.𝓖 W.ι M (W.κ x).1 i} with hNobjdef
  have hNobj_spec : ∀ (i : Fin D) (x : EdgeObj 𝓗'), x ∈ Nobj i ↔
      ∃ A ∈ Nstar, A.1 = auxEdge n W.M D W.𝓖 W.ι M (W.κ x).1 i := by
    intro i x; simp only [hNobjdef, Set.mem_setOf_eq]
  have hNobj_outM : ∀ (i : Fin D) (x : EdgeObj 𝓗'), x ∈ Nobj i →
      (W.κ x).1 ∩ W.ι '' famVert (M i) = ∅ := by
    intro i x hx
    obtain ⟨A, hA, hAeq⟩ := (hNobj_spec i x).mp hx
    have hf : (W.κ x).1 ∈ W.𝓖 := (W.κ x).2.1
    have hmem : auxVInl n W.M D W.𝓖 W.ι M (W.κ x).1 hf ∈ A.1 := by
      rw [hAeq]; exact (auxVInl_mem_auxEdge hf i).2 rfl
    obtain ⟨j, hdj, hjeq⟩ := (mem_auxHypergraph_auxVInl hf A.1).mp ⟨A.2, hmem⟩
    have hne : (W.κ x).1.Nonempty := by
      rw [← Set.ncard_pos, hWuni _ hf]; omega
    have hij : i = j := auxEdge_eq_index_of_disj hne hdj (hAeq.symm.trans hjeq)
    rwa [← hij] at hdj
  set Nnew : Fin D → Set (Set (Fin n)) := fun i =>
    {e | ∃ (f : Set (Fin W.M)) (hf : f ∈ W.𝓖)
        (hd : f ∩ W.ι '' famVert (M i) = ∅)
        (hm : (f ∩ W.ι '' {v : Fin n | 0 < 𝓗'.deg v}).Nonempty),
        e = psiOf W ⟨f, hf, hm⟩ ∧
        ∃ A ∈ Nstar, A.1 = auxEdge n W.M D W.𝓖 W.ι M f i} with hNnewdef
  have hNnew_spec : ∀ (i : Fin D) (e : Set (Fin n)), e ∈ Nnew i ↔
      ∃ (f : Set (Fin W.M)) (hf : f ∈ W.𝓖) (hd : f ∩ W.ι '' famVert (M i) = ∅)
        (hm : (f ∩ W.ι '' {v : Fin n | 0 < 𝓗'.deg v}).Nonempty),
        e = psiOf W ⟨f, hf, hm⟩ ∧
        ∃ A ∈ Nstar, A.1 = auxEdge n W.M D W.𝓖 W.ι M f i := by
    intro i e; simp only [hNnewdef, Set.mem_setOf_eq]
  have hNnew_prop : ∀ (i : Fin D) (e : Set (Fin n)), e ∈ Nnew i →
      ∃ (f : Set (Fin W.M)) (hf : f ∈ W.𝓖) (hd : f ∩ W.ι '' famVert (M i) = ∅)
        (hm : (f ∩ W.ι '' {v : Fin n | 0 < 𝓗'.deg v}).Nonempty),
        e = psiOf W ⟨f, hf, hm⟩ ∧
        ∃ A ∈ Nstar, A.1 = auxEdge n W.M D W.𝓖 W.ι M f i :=
    fun i e he => (hNnew_spec i e).mp he
  have hNnew_edgeSet : ∀ (i : Fin D) (e : Set (Fin n)), e ∈ Nnew i → e ∈ 𝓗'.edgeSet := by
    intro i e he
    obtain ⟨f, hf, _, hm, rfl, _⟩ := hNnew_prop i e he
    exact hpsi1 f hf hm
  have hNnew_disj : ∀ (i : Fin D) (e : Set (Fin n)), e ∈ Nnew i → e ∩ famVert (M i) = ∅ := by
    intro i e he
    obtain ⟨f, hf, hd, hm, rfl, _⟩ := hNnew_prop i e he
    rw [hpsi2 f hf hm]
    have h1 : ¬ (psiSet W.ι f ∩ famVert (M i)).Nonempty := by
      rw [← hpsi3 f i, hd]; exact Set.not_nonempty_empty
    rwa [Set.not_nonempty_iff_eq_empty] at h1
  set Vstar : Set (AuxVertex n W.M D W.𝓖 W.ι M) :=
    ⋃ A ∈ Nstar, (A : Set (AuxVertex n W.M D W.𝓖 W.ι M)) with hVstar
  have hNobj_fam : ∀ i, objFam (Nobj i) = Nnew i := by
    intro i
    ext e
    constructor
    · rintro ⟨x, hx, hxe⟩
      obtain ⟨A, hA, hAeq⟩ := (hNobj_spec i x).mp hx
      exact ⟨(W.κ x).1, (W.κ x).2.1, hNobj_outM i x hx, (W.κ x).2.2,
        by rw [← hxe]; exact (psiOf_kappa W x).symm, A, hA, hAeq⟩
    · intro he
      obtain ⟨f, hf, hd, hm, heq, A, hA, hAeq⟩ := (hNnew_spec i e).mp he
      refine ⟨W.κ.symm ⟨f, hf, hm⟩, ?_, ?_⟩
      · rw [hNobj_spec]
        refine ⟨A, hA, ?_⟩
        rw [hAeq]
        have hk : W.κ (W.κ.symm ⟨f, hf, hm⟩) = ⟨f, hf, hm⟩ := Equiv.apply_symm_apply W.κ _
        rw [hk]
      · have h1 := psiOf_kappa W (W.κ.symm ⟨f, hf, hm⟩)
        rw [Equiv.apply_symm_apply] at h1
        rw [← h1]; exact heq.symm
  have hobjVert : ∀ i, objVert (Nobj i) = famVert (Nnew i) := by
    intro i
    have h1 : objVert (Nobj i) = famVert (objFam (Nobj i)) := by
      ext v
      constructor
      · intro hv
        obtain ⟨x, hx, hvx⟩ := mem_objVert.mp hv
        rw [famVert, Set.mem_sUnion]
        exact ⟨EdgeObj.toSet x, mem_objFam_iff.mpr ⟨x, hx, rfl⟩, hvx⟩
      · intro hv
        rw [famVert, Set.mem_sUnion] at hv
        obtain ⟨e, he, hve⟩ := hv
        obtain ⟨x, hx, hxe⟩ := mem_objFam_iff.mp he
        exact mem_objVert.mpr ⟨x, hx, by rw [hxe]; exact hve⟩
    rw [h1, hNobj_fam i]
  have hVstar_iff : ∀ (x : EdgeObj 𝓗'),
      auxVInl n W.M D W.𝓖 W.ι M (W.κ x).1 (W.κ x).2.1 ∈ Vstar ↔
        ∃ c : Fin D, x ∈ Nobj c := by
    intro x
    constructor
    · intro hmem
      rw [hVstar, Set.mem_iUnion] at hmem
      obtain ⟨B, hmem⟩ := hmem
      rw [Set.mem_iUnion] at hmem
      obtain ⟨hB, hyB⟩ := hmem
      obtain ⟨c, hdc, hBeq⟩ := (mem_auxHypergraph_auxVInl (W.κ x).2.1 B.1).mp ⟨B.2, hyB⟩
      exact ⟨c, by rw [hNobj_spec]; exact ⟨B, hB, hBeq⟩⟩
    · rintro ⟨c, hx⟩
      obtain ⟨B, hB, hBeq⟩ := (hNobj_spec c x).mp hx
      rw [hVstar, Set.mem_iUnion]
      refine ⟨B, ?_⟩
      rw [Set.mem_iUnion]
      exact ⟨hB, by rw [hBeq]; exact (auxVInl_mem_auxEdge (W.κ x).2.1 c).2 rfl⟩
  have hNobj_matching : ∀ i, IsObjMatching (Nobj i) := by
    intro i x hx y hy hne
    rw [Set.disjoint_left]
    intro v hvx hvy
    obtain ⟨A, hA, hAeq⟩ := (hNobj_spec i x).mp hx
    obtain ⟨B, hB, hBeq⟩ := (hNobj_spec i y).mp hy
    have hvx' : W.ι v ∈ (W.κ x).1 := by
      have h1 : v ∈ psiOf W (W.κ x) := by rw [psiOf_kappa]; exact hvx
      rw [hpsi2 (W.κ x).1 (W.κ x).2.1 (W.κ x).2.2] at h1
      exact mem_psiSet.mp h1
    have hvy' : W.ι v ∈ (W.κ y).1 := by
      have h1 : v ∈ psiOf W (W.κ y) := by rw [psiOf_kappa]; exact hvy
      rw [hpsi2 (W.κ y).1 (W.κ y).2.1 (W.κ y).2.2] at h1
      exact mem_psiSet.mp h1
    have hnonmem : W.ι v ∉ W.ι '' famVert (M i) :=
      notMem_image_famVert_of_mem (hNobj_outM i x hx) hvx'
    have hAx : auxVInr n W.M D W.𝓖 W.ι M i (W.ι v) hnonmem ∈ A.1 := by
      rw [hAeq]; exact (auxVInr_mem_auxEdge hnonmem).2 ⟨rfl, hvx'⟩
    have hBy : auxVInr n W.M D W.𝓖 W.ι M i (W.ι v) hnonmem ∈ B.1 := by
      rw [hBeq]; exact (auxVInr_mem_auxEdge hnonmem).2 ⟨rfl, hvy'⟩
    by_cases hAB : A = B
    · have h1 : auxEdge n W.M D W.𝓖 W.ι M (W.κ x).1 i =
          auxEdge n W.M D W.𝓖 W.ι M (W.κ y).1 i := by rw [← hAeq, hAB, hBeq]
      have hne' : (W.κ x).1.Nonempty := by
        rw [← Set.ncard_pos, hWuni _ (W.κ x).2.1]; omega
      have hfg := auxEdge_inj (W.κ x).2.1 (W.κ y).2.1 (hNobj_outM i x hx) (hNobj_outM i y hy)
        hne' h1
      exact hne (W.κ.injective (Subtype.ext hfg.1))
    · exact (Set.disjoint_left.mp (hNpair A hA B hB hAB)) hAx hBy
  have hNobj_disj : ∀ i j, i ≠ j → Disjoint (Nobj i) (Nobj j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    obtain ⟨A, hA, hAeq⟩ := (hNobj_spec i x).mp hxi
    obtain ⟨B, hB, hBeq⟩ := (hNobj_spec j x).mp hxj
    by_cases hAB : A = B
    · have h1 : auxEdge n W.M D W.𝓖 W.ι M (W.κ x).1 i =
          auxEdge n W.M D W.𝓖 W.ι M (W.κ x).1 j := by rw [← hAeq, hAB, hBeq]
      have hne' : (W.κ x).1.Nonempty := by
        rw [← Set.ncard_pos, hWuni _ (W.κ x).2.1]; omega
      exact hij (auxEdge_eq_index_of_disj hne' (hNobj_outM j x hxj) h1)
    · have hmemA : auxVInl n W.M D W.𝓖 W.ι M (W.κ x).1 (W.κ x).2.1 ∈ A.1 := by
        rw [hAeq]; exact (auxVInl_mem_auxEdge (W.κ x).2.1 i).2 rfl
      have hmemB : auxVInl n W.M D W.𝓖 W.ι M (W.κ x).1 (W.κ x).2.1 ∈ B.1 := by
        rw [hBeq]; exact (auxVInl_mem_auxEdge (W.κ x).2.1 j).2 rfl
      exact (Set.disjoint_left.mp (hNpair A hA B hB hAB)) hmemA hmemB
  have hNB2 : ∀ i, PseudoRandomFam (Nnew i) 𝓕V γ κ := by
    intro i A hA
    have hSmem : phiSet n W.M D W.𝓖 W.ι M i A ∈ auxFamObj W D W.𝓖 W.ι M 𝓕V 𝓕E := by
      unfold auxFamObj
      exact Or.inl (Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem _ hA⟩)
    have hclone : ∀ {w : Fin n}, w ∉ famVert (M i) → W.ι w ∉ W.ι '' famVert (M i) := by
      rintro w hw ⟨a, ha, heq⟩
      exact hw (by rw [W.ι.injective heq] at ha; exact ha)
    have hclaim1 : ∀ (w : Fin n) (hw : w ∉ famVert (M i))
        (hw' : W.ι w ∉ W.ι '' famVert (M i)),
        (auxVInr n W.M D W.𝓖 W.ι M i (W.ι w) hw') ∈ Vstar ↔ w ∈ famVert (Nnew i) := by
      intro w hw hw'
      constructor
      · intro hmem
        rw [hVstar, Set.mem_iUnion] at hmem
        obtain ⟨B, hmem⟩ := hmem
        rw [Set.mem_iUnion] at hmem
        obtain ⟨hB, hyB⟩ := hmem
        obtain ⟨g, hg, hwg, hdg, hBeq⟩ :=
          (mem_auxHypergraph_auxVInr hw' B.1).mp ⟨B.2, hyB⟩
        have hm : (g ∩ W.ι '' {v : Fin n | 0 < 𝓗'.deg v}).Nonempty :=
          ⟨W.ι w, hwg, Set.mem_image_of_mem _ (hVuniv w)⟩
        have hmemnew : psiOf W ⟨g, hg, hm⟩ ∈ Nnew i := by
          rw [hNnew_spec]
          exact ⟨g, hg, hdg, hm, rfl, B, hB, hBeq⟩
        exact ⟨psiOf W ⟨g, hg, hm⟩, hmemnew,
          by rw [hpsi2 g hg hm]; exact mem_psiSet.mpr hwg⟩
      · rintro ⟨e, he, hwe⟩
        obtain ⟨g, hg, hd, hm, rfl, B, hB, hBeq⟩ := (hNnew_spec i e).mp he
        rw [hpsi2 g hg hm] at hwe
        have hwg : W.ι w ∈ g := mem_psiSet.mp hwe
        rw [hVstar, Set.mem_iUnion]
        refine ⟨B, ?_⟩
        rw [Set.mem_iUnion]
        refine ⟨hB, ?_⟩
        rw [hBeq]
        exact (auxVInr_mem_auxEdge (f := g) (i := i) (i' := i) (w := W.ι w) hw').2 ⟨rfl, hwg⟩
    have hcard : (A \ famVert (M i ∪ Nnew i)).ncard =
        (phiSet n W.M D W.𝓖 W.ι M i A \ Vstar).ncard := by
      have hset : (A \ famVert (M i ∪ Nnew i)) = (A \ famVert (M i)) \ famVert (Nnew i) := by
        rw [famVert, famVert, famVert, Set.sUnion_union]
        ext x; simp only [Set.mem_sdiff, Set.mem_union]; tauto
      rw [hset]
      refine Set.ncard_congr (fun (w : Fin n) (hw : w ∈ (A \ famVert (M i)) \ famVert (Nnew i)) =>
        (auxVInr n W.M D W.𝓖 W.ι M i (W.ι w) (hclone hw.1.2))) ?_ ?_ ?_
      · rintro w ⟨⟨hwA, hwM⟩, hwN⟩
        refine ⟨?_, ?_⟩
        · exact mem_phiSet.mpr ⟨w, hwA, rfl⟩
        · intro hmem
          exact hwN ((hclaim1 w hwM _).mp hmem)
      · rintro w w' _ _ heq
        have h2 : W.ι w = W.ι w' :=
          congrArg Prod.snd (Sum.inr.inj (congrArg Subtype.val heq))
        exact W.ι.injective h2
      · rintro y ⟨hyA, hyN⟩
        rw [mem_phiSet] at hyA
        obtain ⟨w, hwA, hwy⟩ := hyA
        have hy2 : W.ι w ∉ W.ι '' famVert (M i) := by
          have h := y.2
          rw [hwy] at h
          exact h
        have hwM : w ∉ famVert (M i) := fun hwmem => hy2 ⟨w, hwmem, rfl⟩
        have hEq : (auxVInr n W.M D W.𝓖 W.ι M i (W.ι w) hy2) = y := Subtype.ext hwy.symm
        have hnotstar : (auxVInr n W.M D W.𝓖 W.ι M i (W.ι w) hy2) ∉ Vstar := by
          rw [hEq]; exact hyN
        have hwN : w ∉ famVert (Nnew i) := fun h => hnotstar ((hclaim1 w hwM hy2).mpr h)
        exact ⟨w, ⟨⟨hwA, hwM⟩, hwN⟩, Subtype.ext hwy.symm⟩
    have hbound : |(((phiSet n W.M D W.𝓖 W.ι M i A \ Vstar).ncard : ℝ)) -
        γ * ((phiSet n W.M D W.𝓖 W.ι M i A).ncard : ℝ)| ≤
        8 * β * ((phiSet n W.M D W.𝓖 W.ι M i A).ncard : ℝ) + (D : ℝ) ^ (1 / 20 : ℝ) := by
      by_cases hcase : (D : ℝ) ^ (1 / 20 : ℝ) ≤ ((phiSet n W.M D W.𝓖 W.ι M i A).ncard : ℝ)
      · have h := hNcov _ hSmem hcase
        have hpos : (0 : ℝ) ≤ (D : ℝ) ^ (1 / 20 : ℝ) := Real.rpow_nonneg hD0.le _
        linarith
      · push_neg at hcase
        have h1 : ((phiSet n W.M D W.𝓖 W.ι M i A \ Vstar).ncard : ℝ) ≤
            ((phiSet n W.M D W.𝓖 W.ι M i A).ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard Set.sdiff_subset
        have h3 : ((phiSet n W.M D W.𝓖 W.ι M i A).ncard : ℝ) ≤ (D : ℝ) ^ (1 / 20 : ℝ) :=
          le_of_lt hcase
        have hSc : (0 : ℝ) ≤ ((phiSet n W.M D W.𝓖 W.ι M i A).ncard : ℝ) := by positivity
        have h5' : γ * ((phiSet n W.M D W.𝓖 W.ι M i A).ncard : ℝ) ≤
            ((phiSet n W.M D W.𝓖 W.ι M i A).ncard : ℝ) := by nlinarith [hγ1, hSc]
        have hY0 : (0 : ℝ) ≤ ((phiSet n W.M D W.𝓖 W.ι M i A \ Vstar).ncard : ℝ) := by
          positivity
        rw [abs_le]; constructor <;> nlinarith [h1, h3, h5', hY0, hSc, hβ, hγ]
    have hsplitR : ((phiSet n W.M D W.𝓖 W.ι M i A).ncard : ℝ) =
        (A.ncard : ℝ) - ((A ∩ famVert (M i)).ncard : ℝ) := by
      have hS_eq : (phiSet n W.M D W.𝓖 W.ι M i A).ncard = (A \ famVert (M i)).ncard := by
        refine (Set.ncard_congr (fun (w : Fin n) (hw : w ∈ A \ famVert (M i)) =>
          (auxVInr n W.M D W.𝓖 W.ι M i (W.ι w) (hclone hw.2))) ?_ ?_ ?_).symm
        · rintro w ⟨hwA, _⟩
          exact mem_phiSet.mpr ⟨w, hwA, rfl⟩
        · rintro w w' _ _ heq
          have h2 : W.ι w = W.ι w' :=
            congrArg Prod.snd (Sum.inr.inj (congrArg Subtype.val heq))
          exact W.ι.injective h2
        · intro y hy
          change ∃ v : Fin W.M, v ∈ W.ι '' A ∧ y.val = Sum.inr (i, v) at hy
          obtain ⟨v, hv, hyv⟩ := hy
          obtain ⟨w, hwA, rfl⟩ := hv
          have hy2 : W.ι w ∉ W.ι '' famVert (M i) := by
            have h := y.2
            rw [hyv] at h
            exact h
          have hwM : w ∉ famVert (M i) := fun hwmem => hy2 ⟨w, hwmem, rfl⟩
          exact ⟨w, ⟨hwA, hwM⟩, Subtype.ext hyv.symm⟩
      have hAset : A \ famVert (M i) = A \ (A ∩ famVert (M i)) := by
        ext x; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto
      have hsplit : (phiSet n W.M D W.𝓖 W.ι M i A).ncard + (A ∩ famVert (M i)).ncard
          = A.ncard := by
        have hU : A \ (A ∩ famVert (M i)) ∪ (A ∩ famVert (M i)) = A := by
          rw [Set.sdiff_union_self]; exact Set.union_eq_left.mpr Set.inter_subset_left
        have hD : Disjoint (A \ (A ∩ famVert (M i))) (A ∩ famVert (M i)) := by
          rw [Set.disjoint_left]
          intro x hx hx'
          exact hx.2 hx'
        rw [hS_eq, hAset, ← Set.ncard_union_eq hD (Set.toFinite _) (Set.toFinite _), hU]
      have h2 := congrArg (fun m : ℕ => (m : ℝ)) hsplit
      push_cast at h2
      linarith
    have hSle : ((phiSet n W.M D W.𝓖 W.ι M i A).ncard : ℝ) ≤ (A.ncard : ℝ) := by
      rw [hsplitR]; exact sub_le_self _ (by positivity)
    have hSle' : ((phiSet n W.M D W.𝓖 W.ι M i A).ncard : ℝ) ≤ (n : ℝ) := by
      have h2 : A.ncard ≤ n := by
        have h3 := Set.ncard_le_card A
        rwa [Nat.card_fin] at h3
      exact le_trans hSle (by exact_mod_cast h2)
    have hfamUnion : famVert (M i ∪ Nnew i) = famVert (M i) ∪ famVert (Nnew i) := by
      rw [famVert, famVert, famVert, Set.sUnion_union]
    have hdisjMN : Disjoint (famVert (M i)) (famVert (Nnew i)) := by
      rw [Set.disjoint_left]
      intro v hvM hvN
      rw [famVert, Set.mem_sUnion] at hvN
      obtain ⟨e, he, hve⟩ := hvN
      exact (Set.eq_empty_iff_forall_notMem.mp (hNnew_disj i e he)) v ⟨hve, hvM⟩
    have hsetEq : A \ famVert (Nnew i)
        = (A \ (famVert (M i) ∪ famVert (Nnew i))) ∪ (A ∩ famVert (M i)) := by
      ext v
      simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff, not_or]
      constructor
      · intro h
        by_cases hv : v ∈ famVert (M i)
        · exact Or.inr ⟨h.1, hv⟩
        · exact Or.inl ⟨h.1, hv, h.2⟩
      · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, h3⟩
        · exact ⟨h1, fun hcon => (Set.disjoint_left.mp hdisjMN h2 hcon)⟩
    have hdisj2 : Disjoint (A \ (famVert (M i) ∪ famVert (Nnew i))) (A ∩ famVert (M i)) := by
      rw [Set.disjoint_left]
      rintro v hv1 hv2
      rw [Set.mem_sdiff, Set.mem_union] at hv1
      rw [Set.mem_inter_iff] at hv2
      exact hv1.2 (Or.inl hv2.2)
    have hdiff : (A \ famVert (Nnew i)).ncard
        = (A \ famVert (M i ∪ Nnew i)).ncard + (A ∩ famVert (M i)).ncard := by
      rw [hsetEq, hfamUnion, Set.ncard_union_eq hdisj2 (Set.toFinite _) (Set.toFinite _)]
    have hkey : ((A \ famVert (Nnew i)).ncard : ℝ)
        = ((phiSet n W.M D W.𝓖 W.ι M i A \ Vstar).ncard : ℝ)
          + ((A ∩ famVert (M i)).ncard : ℝ) := by
      rw [hdiff, hcard]; push_cast; ring
    have hcap : ((A ∩ famVert (M i)).ncard : ℝ) ≤ β * (D : ℝ) :=
      le_trans (by exact_mod_cast Set.ncard_le_ncard Set.inter_subset_right) (hMsz i)
    have hc0 : (0 : ℝ) ≤ ((A ∩ famVert (M i)).ncard : ℝ) := by positivity
    have hDn' : (D : ℝ) ^ (1 / 20 : ℝ) ≤ (κ / 20) * (n : ℝ) :=
      le_trans hDinv (by nlinarith [hκ, hDhi])
    have h8βn : 8 * β * ((phiSet n W.M D W.𝓖 W.ι M i A).ncard : ℝ) ≤
        (8 / 10) * κ * (n : ℝ) := by
      nlinarith [h10β, hSle', hβ, hκ, hnpos]
    have hcn : ((A ∩ famVert (M i)).ncard : ℝ) ≤ (κ / 10) * (n : ℝ) := by
      nlinarith [hcap, h10β, hDhi, hκ, hβ, hnpos]
    rw [hkey, abs_le]
    constructor
    · have h1 := (abs_le.mp hbound).1
      nlinarith [h1, hsplitR, h8βn, hDn', hcn, hc0, hγ1, hκ, hnpos]
    · have h2 := (abs_le.mp hbound).2
      nlinarith [h2, hsplitR, h8βn, hDn', hcn, hc0, hγ1, hκ, hnpos]
  have kappaImg_sub : ∀ F : Set (EdgeObj 𝓗'), kappaImg W F ⊆ W.𝓖 := by
    intro F f hf
    change ∃ x ∈ F, (W.κ x).1 = f at hf
    obtain ⟨x, _, rfl⟩ := hf
    exact (W.κ x).2.1
  have ncard_kappaImg : ∀ F : Set (EdgeObj 𝓗'), (kappaImg W F).ncard = F.ncard := by
    intro F
    change ((fun x : EdgeObj 𝓗' => (W.κ x).1) '' F).ncard = F.ncard
    exact Set.InjOn.ncard_image (fun x _ y _ hxy => W.κ.injective (Subtype.ext hxy))
  have ncard_inlSet : ∀ S : Set (Set (Fin W.M)), S ⊆ W.𝓖 →
      (inlSet n W.M D W.𝓖 W.ι M S).ncard = S.ncard := by
    intro S hS
    have h : S.ncard = (inlSet n W.M D W.𝓖 W.ι M S).ncard := by
      refine Set.ncard_congr (fun (f : Set (Fin W.M)) (hf : f ∈ S) =>
        auxVInl n W.M D W.𝓖 W.ι M f (hS hf)) ?_ ?_ ?_
      · intro f hf
        show ∃ f' ∈ S, (auxVInl n W.M D W.𝓖 W.ι M f (hS hf)).val = Sum.inl f'
        exact ⟨f, hf, rfl⟩
      · intro f g hf hg hfg
        have h2 := congrArg (fun a : AuxVertex n W.M D W.𝓖 W.ι M => a.val) hfg
        simp only [auxVInl_val] at h2
        exact Sum.inl.inj h2
      · intro y hy
        change ∃ f ∈ S, y.val = Sum.inl f at hy
        obtain ⟨f, hf, hyf⟩ := hy
        exact ⟨f, hf, Subtype.ext hyf.symm⟩
    exact h.symm
  have hSn : ∀ F ∈ 𝓕E,
      ((inlSet n W.M D W.𝓖 W.ι M (kappaImg W F)).ncard : ℝ) = (F.ncard : ℝ) := by
    intro F _
    have h1 : (inlSet n W.M D W.𝓖 W.ι M (kappaImg W F)).ncard = F.ncard :=
      (ncard_inlSet (kappaImg W F) (kappaImg_sub F)).trans (ncard_kappaImg F)
    exact_mod_cast h1
  have hNB3 : LeftoverFamObj Nobj 𝓕E γ κ := by
    intro F hF
    have hSfam : inlSet n W.M D W.𝓖 W.ι M (kappaImg W F) ∈
        auxFamObj W D W.𝓖 W.ι M 𝓕V 𝓕E := by
      unfold auxFamObj
      exact Or.inr (Set.mem_image_of_mem _ hF)
    have hFcase : ((inlSet n W.M D W.𝓖 W.ι M (kappaImg W F)).ncard : ℝ) = (F.ncard : ℝ) :=
      hSn F hF
    have hcount : (({x ∈ F | ∀ c : Fin D, x ∉ Nobj c}).ncard : ℝ)
        = (((inlSet n W.M D W.𝓖 W.ι M (kappaImg W F)) \ Vstar).ncard : ℝ) := by
      have h1 : ({x ∈ F | ∀ c : Fin D, x ∉ Nobj c}).ncard
          = ((inlSet n W.M D W.𝓖 W.ι M (kappaImg W F)) \ Vstar).ncard := by
        refine Set.ncard_congr (fun (x : EdgeObj 𝓗')
          (_ : x ∈ {x ∈ F | ∀ c : Fin D, x ∉ Nobj c}) =>
          auxVInl n W.M D W.𝓖 W.ι M (W.κ x).1 (W.κ x).2.1) ?_ ?_ ?_
        · intro x hx
          refine ⟨?_, ?_⟩
          · show ∃ f ∈ kappaImg W F, (auxVInl n W.M D W.𝓖 W.ι M (W.κ x).1 (W.κ x).2.1).val
              = Sum.inl f
            refine ⟨(W.κ x).1, ?_, rfl⟩
            change ∃ x' ∈ F, (W.κ x').1 = (W.κ x).1
            exact ⟨x, hx.1, rfl⟩
          · intro hmem
            obtain ⟨c, hc⟩ := (hVstar_iff x).mp hmem
            exact hx.2 c hc
        · intro x y hx hy heq
          have h2 : (W.κ x).1 = (W.κ y).1 := by
            have h3 := congrArg (fun a : AuxVertex n W.M D W.𝓖 W.ι M => a.val) heq
            simp only [auxVInl_val] at h3
            exact Sum.inl.inj h3
          exact W.κ.injective (Subtype.ext h2)
        · intro y hy
          obtain ⟨hyS, hyV⟩ := hy
          change ∃ f ∈ kappaImg W F, y.val = Sum.inl f at hyS
          obtain ⟨f, hfF, hyf⟩ := hyS
          change ∃ x ∈ F, (W.κ x).1 = f at hfF
          obtain ⟨x, hxF, hxf⟩ := hfF
          have hEq : (auxVInl n W.M D W.𝓖 W.ι M (W.κ x).1 (W.κ x).2.1) = y := by
            refine Subtype.ext ?_
            simp only [auxVInl_val]
            rw [hyf, hxf]
          refine ⟨x, ⟨hxF, ?_⟩, hEq⟩
          intro c hxc
          exact hyV (hEq ▸ (hVstar_iff x).mpr ⟨c, hxc⟩)
      exact_mod_cast h1
    have hbound : |(((inlSet n W.M D W.𝓖 W.ι M (kappaImg W F) \ Vstar).ncard : ℝ)) -
        γ * ((inlSet n W.M D W.𝓖 W.ι M (kappaImg W F)).ncard : ℝ)| ≤
        8 * β * ((inlSet n W.M D W.𝓖 W.ι M (kappaImg W F)).ncard : ℝ) +
          (D : ℝ) ^ (1 / 20 : ℝ) := by
      by_cases hcase : (D : ℝ) ^ (1 / 20 : ℝ) ≤
          ((inlSet n W.M D W.𝓖 W.ι M (kappaImg W F)).ncard : ℝ)
      · have h := hNcov _ hSfam hcase
        have hpos : (0 : ℝ) ≤ (D : ℝ) ^ (1 / 20 : ℝ) := Real.rpow_nonneg hD0.le _
        linarith
      · push_neg at hcase
        have h1 : ((inlSet n W.M D W.𝓖 W.ι M (kappaImg W F) \ Vstar).ncard : ℝ) ≤
            ((inlSet n W.M D W.𝓖 W.ι M (kappaImg W F)).ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard Set.sdiff_subset
        have h3 : ((inlSet n W.M D W.𝓖 W.ι M (kappaImg W F)).ncard : ℝ) ≤
            (D : ℝ) ^ (1 / 20 : ℝ) := le_of_lt hcase
        have hSc : (0 : ℝ) ≤ ((inlSet n W.M D W.𝓖 W.ι M (kappaImg W F)).ncard : ℝ) := by
          positivity
        have h5' : γ * ((inlSet n W.M D W.𝓖 W.ι M (kappaImg W F)).ncard : ℝ) ≤
            ((inlSet n W.M D W.𝓖 W.ι M (kappaImg W F)).ncard : ℝ) := by
          nlinarith [hγ1, hSc]
        have hY0 : (0 : ℝ) ≤
            ((inlSet n W.M D W.𝓖 W.ι M (kappaImg W F) \ Vstar).ncard : ℝ) := by positivity
        rw [abs_le]; constructor <;> nlinarith [h1, h3, h5', hY0, hSc, hβ, hγ]
    have hFmax : (0 : ℝ) ≤ (F.ncard : ℝ) := by positivity
    have hDmax : (D : ℝ) ^ (1 / 20 : ℝ) ≤ (κ / 20) * max (F.ncard : ℝ) (D : ℝ) := by
      have h1 : (D : ℝ) ≤ max (F.ncard : ℝ) (D : ℝ) := le_max_right _ _
      nlinarith [hDinv, h1, hκ]
    have h8β : 8 * β * ((inlSet n W.M D W.𝓖 W.ι M (kappaImg W F)).ncard : ℝ) ≤
        (8 / 10) * κ * max (F.ncard : ℝ) (D : ℝ) := by
      have h1 : ((inlSet n W.M D W.𝓖 W.ι M (kappaImg W F)).ncard : ℝ) ≤ (F.ncard : ℝ) := by
        rw [hFcase]
      have h2 : (F.ncard : ℝ) ≤ max (F.ncard : ℝ) (D : ℝ) := le_max_left _ _
      nlinarith [h1, h2, h10β, hFmax, hκ]
    have hγF : γ * ((inlSet n W.M D W.𝓖 W.ι M (kappaImg W F)).ncard : ℝ) ≤
        γ * (F.ncard : ℝ) := by
      have h1 : ((inlSet n W.M D W.𝓖 W.ι M (kappaImg W F)).ncard : ℝ) ≤ (F.ncard : ℝ) := by
        rw [hFcase]
      nlinarith [h1, hγ]
    rw [hcount]
    calc ((inlSet n W.M D W.𝓖 W.ι M (kappaImg W F) \ Vstar).ncard : ℝ)
        ≤ γ * ((inlSet n W.M D W.𝓖 W.ι M (kappaImg W F)).ncard : ℝ) +
            (8 * β * ((inlSet n W.M D W.𝓖 W.ι M (kappaImg W F)).ncard : ℝ) +
              (D : ℝ) ^ (1 / 20 : ℝ)) := by linarith [(abs_le.mp hbound).2]
      _ ≤ γ * (F.ncard : ℝ) + ((8 / 10) * κ * max (F.ncard : ℝ) (D : ℝ) +
            (κ / 20) * max (F.ncard : ℝ) (D : ℝ)) := by linarith [hγF, h8β, hDmax]
      _ ≤ γ * (F.ncard : ℝ) + κ * max (F.ncard : ℝ) (D : ℝ) := by
          have hmax : (0 : ℝ) ≤ max (F.ncard : ℝ) (D : ℝ) := by positivity
          nlinarith [hmax, hκ]
  refine ⟨Nobj, hNobj_matching, hNobj_disj, ?_, ?_, hNB3⟩
  · intro i
    rw [hobjVert i, Set.disjoint_left]
    intro v hv hvM
    rw [famVert, Set.mem_sUnion] at hv
    obtain ⟨e, he, hve⟩ := hv
    exact (Set.eq_empty_iff_forall_notMem.mp (hNnew_disj i e he)) v ⟨hve, hvM⟩
  · intro i
    rw [hNobj_fam i]
    exact hNB2 i

end

end Work.Deep.Nibble
