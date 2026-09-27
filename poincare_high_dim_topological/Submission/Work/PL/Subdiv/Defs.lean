import Submission.Work.PL.Defs

/-!
# Barycentric subdivision: core definitions

Area A2 of the lead blueprint (`Submission/Work/NOTES_LEAD_poincare_blueprint.md`), G3.
This file contains the *interface* of the subdivision area: the barycenter `bary`,
chains of faces `IsChain`, the top of a chain `chainTop`, the set of subdivided faces
`sdFaces` and the subdivided complex `sd` (defined in `SdBasic.lean`).

Vocabulary is `PL` (`Submission.Work.PL.Defs`): `PL.E N = ℝᴺ`, `PL.Cx N` = geometric
simplicial complexes in `ℝᴺ`, `PL.simp s` = convex hull of a finite vertex set.
-/

open Set Metric
open scoped BigOperators
open PL

namespace Work.PL.Subdiv

noncomputable section

/-- **Barycenter** (centroid) of a finite set of points of `E N`. -/
def bary {N : ℕ} (s : Finset (E N)) : E N := (s.card : ℝ)⁻¹ • ∑ v ∈ s, v

@[simp] lemma bary_empty {N : ℕ} : bary (∅ : Finset (E N)) = 0 := by
  simp [bary]

@[simp] lemma bary_singleton {N : ℕ} (v : E N) : bary ({v} : Finset (E N)) = v := by
  simp [bary]

lemma bary_eq_smul_sum {N : ℕ} (s : Finset (E N)) :
    bary s = (s.card : ℝ)⁻¹ • ∑ v ∈ s, v := rfl

theorem bary_mem_simp {N : ℕ} {s : Finset (E N)} (hs : s.Nonempty) : bary s ∈ simp s := by
  have hne : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hs)
  have h1 : (∑ _v ∈ s, ((s.card : ℝ)⁻¹ : ℝ)) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hne]
  rw [bary_eq_smul_sum, Finset.smul_sum]
  exact (convex_convexHull ℝ (s : Set (E N))).sum_mem
    (fun v _ => inv_nonneg.mpr (Nat.cast_nonneg _)) h1
    (fun v hv => subset_convexHull ℝ (s : Set (E N)) (by simpa using hv))

/-- A **chain** of faces of `K`: a finite family of faces totally ordered by inclusion
(i.e. a flag).  The faces of the barycentric subdivision are the barycenters of chains. -/
def IsChain {N : ℕ} (K : Cx N) (C : Finset (Finset (E N))) : Prop :=
  (∀ ρ ∈ C, ρ ∈ K.faces) ∧ ∀ ρ ∈ C, ∀ ρ' ∈ C, ρ ⊆ ρ' ∨ ρ' ⊆ ρ

lemma IsChain.mono {N : ℕ} {K : Cx N} {C C' : Finset (Finset (E N))} (h : IsChain K C)
    (hsub : C' ⊆ C) : IsChain K C' :=
  ⟨fun ρ hρ => h.1 ρ (hsub hρ), fun ρ hρ ρ' hρ' => h.2 ρ (hsub hρ) ρ' (hsub hρ')⟩

lemma IsChain.erase {N : ℕ} {K : Cx N} {C : Finset (Finset (E N))} (h : IsChain K C)
    (ρ : Finset (E N)) : IsChain K (C.erase ρ) :=
  h.mono (Finset.erase_subset _ _)

/-- The **top** of a chain: the union of its elements.  For a nonempty chain this is its
maximum element (with respect to inclusion). -/
def chainTop {N : ℕ} (C : Finset (Finset (E N))) : Finset (E N) := C.sup id

lemma le_chainTop {N : ℕ} {C : Finset (Finset (E N))} {ρ : Finset (E N)} (hρ : ρ ∈ C) :
    ρ ⊆ chainTop C :=
  Finset.le_sup (f := id) hρ

lemma chainTop_le_iff {N : ℕ} {C : Finset (Finset (E N))} {ρ : Finset (E N)} :
    chainTop C ⊆ ρ ↔ ∀ ρ' ∈ C, ρ' ⊆ ρ := by
  simp [chainTop, Finset.sup_le_iff]

@[simp] lemma chainTop_empty {N : ℕ} : chainTop (∅ : Finset (Finset (E N))) = ∅ := by
  simp [chainTop]

/-- For a chain, the top is an element of the chain (when the chain is nonempty). -/
lemma chainTop_mem_chain {N : ℕ} {C : Finset (Finset (E N))}
    (hC : ∀ ρ ∈ C, ∀ ρ' ∈ C, ρ ⊆ ρ' ∨ ρ' ⊆ ρ) (h : C.Nonempty) : chainTop C ∈ C := by
  obtain ⟨ρ₀, hρ₀, hmax⟩ := Finset.exists_max_image C Finset.card h
  have hle : chainTop C ⊆ ρ₀ := by
    rw [chainTop_le_iff]
    intro ρ hρ
    rcases hC ρ hρ ρ₀ hρ₀ with hsub | hsub
    · exact hsub
    · exact le_of_eq (Finset.eq_of_subset_of_card_le hsub (hmax ρ hρ)).symm
  rwa [le_antisymm hle (le_chainTop hρ₀)]

lemma chainTop_mem_faces {N : ℕ} {K : Cx N} {C : Finset (Finset (E N))} (h : IsChain K C)
    (hne : C.Nonempty) : chainTop C ∈ K.faces := by
  have := chainTop_mem_chain h.2 hne
  exact h.1 _ this

lemma chainTop_nonempty_of_mem {N : ℕ} {K : Cx N} {C : Finset (Finset (E N))}
    {ρ : Finset (E N)} (h : IsChain K C) (hρ : ρ ∈ C) : (chainTop C).Nonempty := by
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces (h.1 ρ hρ)
  exact ⟨v, le_chainTop hρ hv⟩

/-- The set of faces of the barycentric subdivision: barycenters of chains of faces of `K`.
The empty chain gives the empty face, which `SimplicialComplex.ofErase` removes. -/
def sdFaces {N : ℕ} (K : Cx N) : Set (Finset (E N)) :=
  {t | ∃ C : Finset (Finset (E N)), IsChain K C ∧ t = C.image bary}

lemma mem_sdFaces_image {N : ℕ} {K : Cx N} {C : Finset (Finset (E N))} (h : IsChain K C) :
    C.image bary ∈ sdFaces K :=
  ⟨C, h, rfl⟩

end

end Work.PL.Subdiv
