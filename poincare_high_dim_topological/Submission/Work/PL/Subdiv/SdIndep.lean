import Submission.Work.PL.Subdiv.Coord

/-!
# Barycenters of chains are affinely independent (blueprint G3, `indep` axiom)

* `eq_of_subset_of_bary_eq` : if `ρ ⊆ ρ'`, `ρ` is nonempty, `ρ'` is a face of `K` and the
  barycenters agree then `ρ = ρ'`.
* `bary_eq_of_chain` : the barycenter map is injective on a chain of faces.
* `chain_bary_eq_zero` and `affineIndependent_bary_image` : the barycenters of the elements of a
  chain are affinely independent.
-/

open Set Metric
open scoped BigOperators
open PL

namespace Work.PL.Subdiv

noncomputable section

variable {N : ℕ}

/-- If `ρ ⊆ ρ'`, `ρ` is nonempty, `ρ'` is a face of `K` and `bary ρ = bary ρ'`, then `ρ = ρ'`. -/
lemma eq_of_subset_of_bary_eq {K : Cx N} {ρ ρ' : Finset (E N)} (hρ : ρ.Nonempty)
    (hρ' : ρ' ∈ K.faces) (hsub : ρ ⊆ ρ') (h : bary ρ = bary ρ') : ρ = ρ' := by
  have hB : AffineIndependent ℝ ((↑) : ρ' → E N) := K.indep hρ'
  have hne' : ρ'.Nonempty := Finset.Nonempty.mono hsub hρ
  have hcard : (ρ.card : ℝ) ≠ 0 := by
    simp only [Nat.cast_ne_zero]; exact Finset.card_ne_zero.mpr hρ
  have hcard' : (ρ'.card : ℝ) ≠ 0 := by
    simp only [Nat.cast_ne_zero]; exact Finset.card_ne_zero.mpr hne'
  set c : E N → ℝ := fun v => if v ∈ ρ then (ρ.card : ℝ)⁻¹ else 0 with hc
  have hsumc : (∑ v ∈ ρ', c v) = 1 := by
    rw [← Finset.sum_subset hsub (fun v _ hv => by simp [hc, hv])]
    have h2 : (∑ v ∈ ρ, c v) = ∑ v ∈ ρ, (ρ.card : ℝ)⁻¹ :=
      Finset.sum_congr rfl fun v hv => by simp [hc, hv]
    rw [h2, Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hcard]
  have hsum' : (∑ v ∈ ρ', (fun _ => (ρ'.card : ℝ)⁻¹) v) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hcard']
  have hptc : (∑ v ∈ ρ', c v • v) = bary ρ := by
    rw [← Finset.sum_subset hsub (fun v _ hv => by simp [hc, hv])]
    have h2 : (∑ v ∈ ρ, c v • v) = ∑ v ∈ ρ, (ρ.card : ℝ)⁻¹ • v :=
      Finset.sum_congr rfl fun v hv => by simp [hc, hv]
    rw [h2, ← Finset.smul_sum, bary_eq_smul_sum]
  have hpt' : (∑ v ∈ ρ', (fun _ => (ρ'.card : ℝ)⁻¹) v • v) = bary ρ' := by
    rw [← Finset.smul_sum, bary_eq_smul_sum]
  have huniq := coords_unique_of_affineIndependent hB (a := c)
    (a' := fun _ => (ρ'.card : ℝ)⁻¹) (by rw [hsumc, hsum']) (by rw [hptc, hpt', h])
  refine Finset.Subset.antisymm hsub fun v hv' => by
    by_contra hv
    have h1 : c v = 0 := by rw [hc]; simp [hv]
    have h2 := huniq v hv'
    rw [h1] at h2
    exact inv_ne_zero hcard' h2.symm

/-- The barycenter map is injective on a chain of faces of `K`. -/
lemma bary_eq_of_chain {K : Cx N} {C : Finset (Finset (E N))} (hC : IsChain K C)
    {ρ ρ' : Finset (E N)} (hρ : ρ ∈ C) (hρ' : ρ' ∈ C) (h : bary ρ = bary ρ') : ρ = ρ' := by
  rcases hC.2 ρ hρ ρ' hρ' with hsub | hsub
  · exact eq_of_subset_of_bary_eq (K.nonempty_of_mem_faces (hC.1 ρ hρ)) (hC.1 ρ' hρ') hsub h
  · exact (eq_of_subset_of_bary_eq (K.nonempty_of_mem_faces (hC.1 ρ' hρ')) (hC.1 ρ hρ) hsub
      h.symm).symm

/-- **A chain of barycenters is affinely independent** (primitive form). -/
lemma chain_bary_eq_zero {K : Cx N} :
    ∀ (C : Finset (Finset (E N))) (_ : IsChain K C) (c : Finset (E N) → ℝ),
      (∑ ρ ∈ C, c ρ) = 0 → (∑ ρ ∈ C, c ρ • bary ρ) = 0 → ∀ ρ ∈ C, c ρ = 0 := by
  intro C
  induction C using Finset.strongInductionOn with
  | _ C ih =>
    intro hC c hsum hpt
    by_cases hne : C.Nonempty
    · have hτC : chainTop C ∈ C := chainTop_mem_chain hC.2 hne
      have hex : ∃ v ∈ chainTop C, v ∉ chainTop (C.erase (chainTop C)) := by
        rcases Finset.eq_empty_or_nonempty (C.erase (chainTop C)) with hempty | hne'
        · obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces (hC.1 _ hτC)
          exact ⟨v, le_chainTop hτC hv, by rw [hempty]; exact Finset.notMem_empty v⟩
        · have hmem' : chainTop (C.erase (chainTop C)) ∈ C.erase (chainTop C) :=
            chainTop_mem_chain (fun ρ hρ ρ' hρ' => hC.2 ρ (Finset.mem_of_mem_erase hρ) ρ'
              (Finset.mem_of_mem_erase hρ')) hne'
          refine Finset.exists_of_ssubset (ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
          · exact chainTop_le_iff.mpr fun ρ hρ => le_chainTop (Finset.mem_of_mem_erase hρ)
          · intro hcon
            exact Finset.notMem_erase _ _ (hcon ▸ hmem')
      obtain ⟨v, hvτ, hvnot⟩ := hex
      have hcoord := sum_smul_bary_eq_sum_smul C (chainTop C) (fun ρ hρ => le_chainTop hρ) c
      have hsumα : (∑ x ∈ chainTop C,
          (∑ ρ ∈ C.filter (fun ρ => x ∈ ρ), c ρ / (ρ.card : ℝ))) = 0 := by
        rw [sum_coeff_filter C (chainTop C) (fun ρ hρ => le_chainTop hρ)
          (fun ρ hρ => K.nonempty_of_mem_faces (hC.1 ρ hρ)) c, hsum]
      have hptα : (∑ x ∈ chainTop C,
          (∑ ρ ∈ C.filter (fun ρ => x ∈ ρ), c ρ / (ρ.card : ℝ)) • x) = 0 := by
        rw [← hcoord, hpt]
      have hαzero := (K.indep (hC.1 _ hτC)).eq_zero_of_sum_eq_zero_subtype hsumα hptα
      have hfilter : C.filter (fun ρ => v ∈ ρ) = {chainTop C} := by
        ext ρ
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hρC, hvρ⟩
          by_contra hne'
          exact hvnot (le_chainTop (Finset.mem_erase.mpr ⟨hne', hρC⟩) hvρ)
        · rintro rfl
          exact ⟨hτC, hvτ⟩
      have hcτ : c (chainTop C) = 0 := by
        have h0 := hαzero v hvτ
        rw [hfilter, Finset.sum_singleton] at h0
        have hcard : ((chainTop C).card : ℝ) ≠ 0 := by
          simp only [Nat.cast_ne_zero]
          exact Finset.card_ne_zero.mpr (K.nonempty_of_mem_faces (hC.1 _ hτC))
        rcases div_eq_zero_iff.mp h0 with h | h
        · exact h
        · exact absurd h hcard
      have hC' : IsChain K (C.erase (chainTop C)) := hC.erase _
      have hlt : C.erase (chainTop C) ⊂ C := Finset.erase_ssubset hτC
      intro ρ hρ
      by_cases hρτ : ρ = chainTop C
      · rw [hρτ]; exact hcτ
      · refine ih _ hlt hC' c ?_ ?_ ρ (Finset.mem_erase.mpr ⟨hρτ, hρ⟩)
        · have h := Finset.sum_erase_add C c hτC
          rw [hsum, hcτ, add_zero] at h
          exact h
        · have h := Finset.sum_erase_add C (fun ρ => c ρ • bary ρ) hτC
          rw [hpt, hcτ, zero_smul, add_zero] at h
          exact h
    · intro ρ hρ
      exact absurd ⟨ρ, hρ⟩ hne

/-- The barycenters of the elements of a chain, indexed by the chain, are affinely independent. -/
lemma affineIndependent_bary_chain {K : Cx N} {C : Finset (Finset (E N))} (hC : IsChain K C) :
    AffineIndependent ℝ (fun ρ : ↥C => bary (ρ : Finset (E N))) := by
  rw [affineIndependent_iff]
  intro s w hw hpt
  classical
  set c : Finset (E N) → ℝ := fun ρ =>
    if h : ρ ∈ C then (if (⟨ρ, h⟩ : ↥C) ∈ s then w ⟨ρ, h⟩ else 0) else 0 with hc
  have hmem : ∀ x ∈ s, x ∈ C.attach := fun x _ => Finset.mem_attach C x
  have hsum : (∑ ρ ∈ C, c ρ) = 0 := by
    rw [← Finset.sum_attach C c, ← Finset.sum_subset hmem ?_, ← hw]
    · exact Finset.sum_congr rfl fun x hx => by simp [hc, x.2, hx]
    · intro x _ hx; simp [hc, x.2, hx]
  have hpt' : (∑ ρ ∈ C, c ρ • bary ρ) = 0 := by
    rw [← Finset.sum_attach C (fun ρ => c ρ • bary ρ), ← Finset.sum_subset hmem ?_, ← hpt]
    · exact Finset.sum_congr rfl fun x hx => by simp [hc, x.2, hx]
    · intro x _ hx; simp [hc, x.2, hx]
  intro ρ hρs
  have h := chain_bary_eq_zero C hC c hsum hpt' ρ ρ.2
  simpa [hc, ρ.2, hρs] using h

/-- The `Finset` of barycenters of a chain is affinely independent (the `indep` axiom). -/
lemma affineIndependent_bary_image {K : Cx N} {C : Finset (Finset (E N))} (hC : IsChain K C) :
    AffineIndependent ℝ ((↑) : (↑(C.image bary) : Set (E N)) → E N) := by
  have h1 := (affineIndependent_bary_chain (K := K) hC).range
  set f : ↥C → E N := fun ρ => bary (ρ : Finset (E N)) with hf
  have hset : Set.range f = (↑(C.image bary) : Set (E N)) := by
    ext b
    simp [hf]
  let e : (Set.range f) ≃ (↑(C.image bary) : Set (E N)) :=
    { toFun := fun x => ⟨x.1, by rw [← hset]; exact x.2⟩
      invFun := fun x => ⟨x.1, by rw [hset]; exact x.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  have hfun : ((fun b : (↑(C.image bary) : Set (E N)) => (b : E N)) ∘ (e : (Set.range f) → _))
      = (fun x : (Set.range f) => (x : E N)) := by
    funext x
    rfl
  refine (affineIndependent_equiv e).mp ?_
  simpa only [hfun] using h1

end

end Work.PL.Subdiv
