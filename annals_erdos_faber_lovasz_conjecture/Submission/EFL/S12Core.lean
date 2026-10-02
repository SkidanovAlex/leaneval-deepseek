import Submission.EFL.S12Assem

import Submission.EFL.NibbleFixed
/-!
# §12: the core assembly (Steps 5 -- 9)

This module contains the *generic* part of the §12 assembly: from the data of
Steps 1--5 (the colour sets, the reservoir and absorber, the matchings `𝓜_diff`
and `𝓜_hm`) it produces `𝓜_prev`, `R_final = R_res ∖ ⋃𝓜_prev` and
`𝓗_final = 𝓗 ∖ ⋃𝓜_prev`, together with the decomposition `(eqn:h_final)`, the
deficit bound `(eqn:deficit)`, the identity
`d_{𝓗_final}(w) = d_{G_final}(w) + |C_w|` and the degree bounds
`UC1`--`UC4` of §12 Step 9 (in the form of the structure `S12Out`).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-! ## Elementary glue -/

/-- If `G ⊆ M` consists of edges of `𝓗` of size at least `2`, then `G` is
contained in `toFam (famOf M)`. -/
theorem subset_toFam_famOf {𝓗 : Hypergraph (Fin n)} {G M : Set 𝓗}
    (hbig : ∀ f ∈ 𝓗, 2 ≤ edgeSize f) (h : G ⊆ M) :
    G ⊆ toFam (𝓗 := 𝓗) (famOf M) := by
  intro e he
  rw [mem_toFam, nonsing, Set.mem_ofPred_eq]
  refine ⟨⟨e, h he, rfl⟩, ?_⟩
  have := hbig e e.2
  rwa [edgeSize_eq_ncard] at this


/-! ## The decomposition of `𝓜_prev` and the size of its added edges -/

/-- **The decomposition of `𝓜_prev` at a colour**: every edge of the family of
`c` is either a colour-class edge of `φ` at `c` or one of the four "added"
families. -/
theorem prevFam_or_added {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)}
    {MD HM MM MB : Fin n → Set 𝓗} {Cmed Cdiff Chuge Cmain Cbuff : Finset (Fin n)}
    (hCmedD : Disjoint Cmed Cdiff)
    (hChuge_nd : ∀ c ∈ Chuge, c ∉ Cmed ∪ Cdiff)
    (hCmain_nd : ∀ c ∈ Cmain, c ∉ Cmed ∪ Cdiff ∪ Chuge)
    (hCbuff_nd : ∀ c ∈ Cbuff, c ∉ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain)
    {c : Fin n} (hc : c ∈ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff) {f : Set (Fin n)}
    (hf : f ∈ prevFam MD HM MM MB Cdiff Cmain Cbuff c) :
    f ∈ famOf (colourFam φ c) ∨
    (c ∈ Cdiff ∧ f ∈ famOf (MD c)) ∨ (c ∈ Cmed ∪ Chuge ∧ f ∈ famOf (HM c)) ∨
    (c ∈ Cmain ∧ f ∈ famOf (MM c)) ∨ (c ∈ Cbuff ∧ f ∈ famOf (MB c)) := by
  have hCdiff_of_main : c ∈ Cmain → c ∉ Cdiff := fun hx hh =>
    (hCmain_nd c hx) (Finset.mem_union_left Chuge (Finset.mem_union_right Cmed hh))
  have hCdiff_of_buff : c ∈ Cbuff → c ∉ Cdiff := fun hx hh =>
    (hCbuff_nd c hx) (Finset.mem_union_left Cmain (Finset.mem_union_left Chuge
      (Finset.mem_union_right Cmed hh)))
  have hCmain_of_buff : c ∈ Cbuff → c ∉ Cmain := fun hx hh =>
    (hCbuff_nd c hx) (Finset.mem_union_right (Cmed ∪ Cdiff ∪ Chuge) hh)
  have hCmedChuge : c ∈ Cmed ∪ Chuge → c ∈ Cmed ∪ Cdiff ∪ Chuge := by
    intro hx
    rcases Finset.mem_union.mp hx with h1 | h1
    · exact Finset.mem_union_left Chuge (Finset.mem_union_left Cdiff h1)
    · exact Finset.mem_union_right (Cmed ∪ Cdiff) h1
  have hCdiff_of_H : c ∈ Cmed ∪ Chuge → c ∉ Cdiff := by
    intro hx hh
    rcases Finset.mem_union.mp hx with h5 | h5
    · exact Finset.disjoint_left.mp hCmedD h5 hh
    · exact hChuge_nd c h5 (Finset.mem_union_right Cmed hh)
  have hCmain_of_H : c ∈ Cmed ∪ Chuge → c ∉ Cmain := fun hx hh =>
    (hCmain_nd c hh) (hCmedChuge hx)
  have hCbuff_of_H : c ∈ Cmed ∪ Chuge → c ∉ Cbuff := fun hx hh =>
    (hCbuff_nd c hh) (Finset.mem_union_left Cmain (hCmedChuge hx))
  have htag : c ∈ Cdiff ∨ c ∈ Cmain ∨ c ∈ Cbuff ∨ c ∈ Cmed ∪ Chuge := by
    simp only [Finset.mem_union] at hc
    rcases hc with (((h1 | h2) | h3) | h4) | h5
    · exact Or.inr (Or.inr (Or.inr (Finset.mem_union.mpr (Or.inl h1))))
    · exact Or.inl h2
    · exact Or.inr (Or.inr (Or.inr (Finset.mem_union.mpr (Or.inr h3))))
    · exact Or.inr (Or.inl h4)
    · exact Or.inr (Or.inr (Or.inl h5))
  rcases htag with h | h | h | h
  · rw [prevFam_of_mem_Cdiff h] at hf
    exact Or.inr (Or.inl ⟨h, hf⟩)
  · rw [prevFam_of_mem_Cmain (hCdiff_of_main h) h] at hf
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, hf⟩)))
  · rw [prevFam_of_mem_Cbuff (hCdiff_of_buff h) (hCmain_of_buff h) h] at hf
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hf⟩)))
  · rw [prevFam_of_notMem (hCdiff_of_H h) (hCmain_of_H h) (hCbuff_of_H h)] at hf
    exact Or.inr (Or.inr (Or.inl ⟨h, hf⟩))



/-! ## Transfer of cardinalities between `Fin n` and `↥S` -/

theorem ncard_subtype_le {S : Finset (Fin n)} {P : Fin n → Prop} :
    ({i : ↥S | P i.1} : Set ↥S).ncard ≤ ({i : Fin n | P i} : Set (Fin n)).ncard :=
  Set.ncard_le_ncard_of_injOn (fun i : ↥S => i.1) (fun i hi => hi)
    (fun a _ b _ h => Subtype.ext h)

theorem ncard_subtype_eq {S : Finset (Fin n)} {P : Fin n → Prop}
    (h : ∀ i ∉ S, ¬ P i) :
    ({i : Fin n | P i} : Set (Fin n)).ncard = ({i : ↥S | P i.1} : Set ↥S).ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  refine Nat.card_congr ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨i, hi⟩
    exact ⟨⟨i, by by_contra hc; exact h i hc hi⟩, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i.1, hi⟩
  · rintro ⟨i, hi⟩
    rfl
  · rintro ⟨i, hi⟩
    rfl

/-- `s \ t = ∅` when `s ⊆ t`. -/
theorem sdiff_eq_empty_of_subset {α : Type*} {s t : Set α} (h : s ⊆ t) : s \ t = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨x, hx⟩
  exact hx.2 (h hx.1)

/-! ## The core of §12: from Steps 4/5 to the final data (Steps 8/9) -/

/-- **§12, the core assembly.**  From the colour sets of Step 3, the reservoir
and absorber of Step 2, the Step-4 output (`𝓜_diff`, `R₁`, `S₁`) and the
Step-5 output (`𝓜_hm`, `R₂`, `S₂`), the nibble (Step 6) and the leftover
lemma (Step 7) produce `𝓜_prev`, and then Steps 8 and 9 give the final data
`R_final`, `𝓗_final`, the decomposition `(eqn:h_final)`, the deficit bound
`(eqn:deficit)`, the exact degree identity of `𝓗_final` and the bounds
`UC1`--`UC4`. -/
theorem s12_core {𝓗 : Hypergraph (Fin n)} {r₁ r₀ : ℕ} {β γ ρ ρ_abs ξ ε κ : ℝ}
    {φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n)} {U S S₁ : Set (Fin n)}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    {R_res R_abs R₁ R₂ : Hypergraph (Fin n)} {Mdiff Mhm : Fin n → Set 𝓗}
    (hlin : 𝓗.IsLinear) (hbig : ∀ f ∈ 𝓗, 2 ≤ edgeSize f)
    (hNib : NibblePointwise r₁ (2 * β) (2 * γ) ε ρ_abs ξ n)
    (hleft : LeftoverMargins n r₁ γ ρ ρ_abs ε ξ)
    (hS12 : IsS12Colours n 𝓗 (r₁ : ℝ) φ U (r₀ : ℝ) β γ ρ Cmed Cdiff Chuge Clarge Cmain
      Cbuff Cfinal)
    (hvert : ∀ c : Fin n, c ∉ Cmed → ¬ φ.AssignedToHuge β c →
      (φ.classVertexCount c : ℝ) ≤ β * (n : ℝ))
    (hres : IsReservoirTypeA1 𝓗 R_res (cvFinset φ U : Set (Set (Fin n))) ρ ξ ε ∨
      IsReservoirTypeA2 𝓗 R_res (cvFinset φ U : Set (Set (Fin n))) ρ ξ ε ∨
      (IsReservoirTypeB 𝓗 R_res (cvFinset φ U : Set (Set (Fin n))) ρ ξ ε ∧
        2 * ρ * ((n : ℝ) - 1) + 1 ≤ ε * (n : ℝ)))
    (hVuniv : (Set.univ : Set (Fin n)) ∈ (cvFinset φ U : Set (Set (Fin n))))
    (hU𝓥 : U ∈ (cvFinset φ U : Set (Set (Fin n))))
    (hU : U = Vplus 𝓗 (1 - ε))
    (hstep4 : IsS12Step4 𝓗 φ U S Cdiff R_abs R₁ S₁ Mdiff
      (cvFinset φ U : Set (Set (Fin n))) ρ_abs γ ξ)
    (S₂ : Set (Fin n)) (hstep5 : IsS12Step5 (φ := φ) (U := U) (S₁ := S₁) (S₂ := S₂)
      (r₀ := r₀) (β := β) (γ := γ) (ρ := ρ) (ρ_abs := ρ_abs) (ξ := ξ) (ε := ε)
      (Chuge := Chuge) (Cmed := Cmed) (R₁ := R₁) (R₂ := R₂) (Mhm := Mhm)
      (𝓥 := (cvFinset φ U : Set (Set (Fin n)))))
    (hm : S12Margins n r₁ r₀ β γ ρ ρ_abs ξ ε κ)
    (hRabs_sub : R_abs ⊆ R_res) (hRabs_pow2 : R_abs ⊆ 𝓗.pow2)
    (hS₁subU : S₁ ⊆ U)
    (hVn2U : Vn2set 𝓗 ⊆ U)
    (hresDeg : ∀ w : Fin n, w ∉ U → (degAt R_res w : ℝ) ≤ ρ * (1 - ε) * (n : ℝ) + ξ * (n : ℝ))
    (hCwLarge : ∀ w : Fin n, ((finalColoursAt φ Cfinal w).card : ℝ) ≤ 2 * (n : ℝ) / (r₀ : ℝ))
    (hUCnum1 : ρ * (1 - ε) * (n : ℝ) + ξ * (n : ℝ) ≤
      (Cfinal.card : ℝ) - ρ * ε * (n : ℝ) / 2)
    (hUCnum2 : 2 * (n : ℝ) / (r₀ : ℝ) ≤ ρ * ε * (n : ℝ) / 4)
    (hdeficitNum : (((Cdiff ∪ Chuge ∪ Cmed ∪ Cbuff).card : ℕ) : ℝ) +
      2 * γ * ((Cmain.card : ℕ) : ℝ) ≤ 15 * Real.sqrt γ * (n : ℝ)) :
    ∃ (Mprev : Fin n → Set 𝓗) (R_final 𝓗fin : Hypergraph (Fin n)),
      S12Out φ U S₁ (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff) Cfinal R_res Mprev R_final 𝓗fin
        ρ ε γ := by
  classical
  -- ## Step 6 (the nibble)
  have hR₂sub : R₂ ⊆ R_res := by
    intro e he
    rw [hstep5.hR₂_eq] at he
    have h2 : e ∈ R₁ := he.1
    rw [hstep4.hR₁_eq] at h2
    exact hRabs_sub h2.1
  have hS₂subU : S₂ ⊆ U := (hstep5.hS₂_sub.trans hS₁subU)
  obtain ⟨𝓗', 𝓗star, N, Mmain, h6₁, h6₂, h6₃, h6₄, h6₅, h6₆, h6₇, h6₈, h6₉, h6₁₀,
    h6₁₁, h6₁₂, h6₁₃, h6₁₄, h6₁₅, h6₁₆, h6₁₇, h6₁₈, h6₁₉, h6₂₀, h6₂₁, h6₂₂, h6₂₃⟩ :=
    s12_step6 (n := n) (𝓗 := 𝓗) (r₁ := r₁) (r₀ := r₀) (β := β) (γ := γ) (ρ := ρ)
      (ρ_abs := ρ_abs) (ξ := ξ) (ε := ε) hlin hbig hm.hmDeg hm.hn1 hm.hnpos hm.hr₀2 hNib
      hm.hnib hS12 hvert hres hVuniv hU𝓥 hstep4.hMdiff_supp hstep4.hMdiff_mat hstep5.hR₂_abs
      hRabs_sub hRabs_pow2 hS₂subU hR₂sub hU hstep5.hS₂_big hm.hγ0 hm.hγε hm.hnum1 hm.hnD
      hm.hEP2num
  -- the leftover hypergraph, the truncated absorber and the defect set
  set 𝓗rem : Hypergraph (Fin n) :=
    𝓗.smallEdges r₁ \ (R_res ∪ famUnionFinset Mdiff Cdiff ∪
      (⋃ i : Fin Cmain.card, N i)) with h𝓗rem
  set R₃ : Hypergraph (Fin n) := R₂ \ (⋃ i : Fin Cmain.card, N i) with hR₃def
  set S₃ : Set (Fin n) := S₂ \ (⋃ i : Fin Cmain.card, (U \ famVert (N i))) with hS₃def
  have hR₃eq : R₃ = R₂ \ (⋃ i : Fin Cmain.card, N i) := rfl
  have hR₃abs : IsAbsorber (incidentTwo 𝓗 U) R₃ (cvFinset φ U : Set (Set (Fin n)))
      ρ_abs (4 * γ) ξ := h6₁₈
  have hR₃pow : R₃ ⊆ 𝓗.pow2 := by
    intro e he
    rw [hR₃def] at he
    have h1 : e ∈ R₂ := he.1
    rw [hstep5.hR₂_eq] at h1
    have h2 : e ∈ R₁ := h1.1
    rw [hstep4.hR₁_eq] at h2
    exact hRabs_pow2 h2.1
  have hS₃sub : S₃ ⊆ U := by
    intro v hv
    rw [hS₃def] at hv
    exact hS₁subU (hstep5.hS₂_sub hv.1)
  have hS₃big : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      4 * ε * (n : ℝ) ≤ (S₃.ncard : ℝ) := h6₂₂
  have hremDeg : ∀ w : Fin n, (MultiHypergraph.hdeg 𝓗rem w : ℝ) ≤
      2 * γ * ((Cmain.card : ℕ) : ℝ) := h6₁₇
  have hL1 : (10 * Real.sqrt γ) * ((Cmain.card : ℕ) : ℝ) / 2 ≤ (Cbuff.card : ℝ) := by
    rw [hS12.hCmain_card, hS12.hCbuff_card]
    exact hm.hL1
  have hL4ov : (r₁ : ℝ) * (n : ℝ) / ((r₀ : ℝ) - 1) ≤ γ * ((Cmain.card : ℕ) : ℝ) := by
    rw [hS12.hCmain_card]
    exact hm.hL4ov
  -- ## Step 7 (the leftover)
  obtain ⟨Mbuff, h7₁, h7₂, h7₃, h7₄, h7₅, h7₆, h7₇, h7₈, h7₉⟩ :=
    s12_step7 (n := n) (𝓗 := 𝓗) (r₁ := r₁) (r₀ := r₀) (β := β) (γ := γ) (ρ := ρ)
      (ρ_abs := ρ_abs) (ξ := ξ) (ε := ε) (φ := φ) (U := U) (S₃ := S₃)
      hS12 hvert hlin hbig hleft hm.hnpos hm.hr₀2 hm.hr₁r₀ (Mdiff := Mdiff)
      (R_res := R_res) (R₂ := R₂) (R₃ := R₃) (𝓥 := (cvFinset φ U : Set (Set (Fin n))))
      (Ncm := N) hR₃eq hR₃abs hR₃pow hR₂sub hS₃sub hU hU𝓥 hVuniv hremDeg hm.hγ0 hS₃big
      hL1 hm.hβγ hm.hL3 hL4ov hm.hL5
  -- ## the final objects
  set Cprev : Finset (Fin n) := Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff with hCprevdef
  set Mprev : Fin n → Set 𝓗 := prevFamE Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff with hMprevdef
  set R_final : Hypergraph (Fin n) := R_res \ famUnionIdx Mprev with hRfinaldef
  set 𝓗fin : Hypergraph (Fin n) := hfinOf Mdiff Mhm Mmain Mbuff Cprev Cdiff Cmain Cbuff
    with h𝓗findef
  -- ## the disjointness of the colour sets
  have hCmedD : Disjoint Cmed Cdiff := hS12.hCdiff_med.symm
  have hChuge_nd : ∀ c ∈ Chuge, c ∉ Cmed ∪ Cdiff := by
    intro c hc
    rw [hS12.hChuge_eq] at hc
    have h1 := (Finset.mem_sdiff.mp hc).2
    intro h2
    rcases Finset.mem_union.mp h2 with h3 | h3
    · exact h1 (Finset.mem_union_left Cdiff h3)
    · exact h1 (Finset.mem_union_right Cmed h3)
  have hCmain_nd : ∀ c ∈ Cmain, c ∉ Cmed ∪ Cdiff ∪ Chuge := by
    intro c hc h2
    have h1 := hS12.hCmain_sub hc
    rw [Finset.mem_compl] at h1
    rcases Finset.mem_union.mp h2 with h3 | h3
    · exact h1 (Finset.mem_union_left Chuge h3)
    · exact h1 (Finset.mem_union_right (Cmed ∪ Cdiff) h3)
  have hCbuff_nd : ∀ c ∈ Cbuff, c ∉ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain := by
    intro c hc h2
    have h1 := hS12.hCbuff_sub hc
    rw [Finset.mem_compl] at h1
    rcases Finset.mem_union.mp h2 with h3 | h3
    · exact h1 (Finset.mem_union_left Cmain h3)
    · exact h1 (Finset.mem_union_right (Cmed ∪ Cdiff ∪ Chuge) h3)
  have hcu : ∀ c : Fin n, c ∈ Cmed ∪ Chuge → c ∈ Chuge ∪ Cmed := by
    intro c hc
    rcases Finset.mem_union.mp hc with h | h
    · exact Finset.mem_union_right Chuge h
    · exact Finset.mem_union_left Cmed h
  -- ## the location of the added edges of the four families
  have hDadd : ∀ c ∈ Cdiff, famOf (Mdiff c) ⊆ famOf (colourFam φ c) ∪ 𝓗.pow2 := by
    intro c hc f hf
    obtain ⟨e, he, heq⟩ := mem_famOf.mp hf
    by_cases hcol : e ∈ colourFam φ c
    · exact Or.inl (by rw [← heq]; exact ⟨e, hcol, rfl⟩)
    · exact Or.inr (by rw [← heq]; exact hstep4.hMdiff_add c hc e he hcol)
  have hHadd : ∀ c ∈ Cmed ∪ Chuge, famOf (Mhm c) ⊆ famOf (colourFam φ c) ∪ R₁ := by
    intro c hc f hf
    obtain ⟨e, he, heq⟩ := mem_famOf.mp hf
    by_cases hcol : e ∈ colourFam φ c
    · exact Or.inl (by rw [← heq]; exact ⟨e, hcol, rfl⟩)
    · exact Or.inr (by rw [← heq]; exact hstep5.hm_add c (hcu c hc) e he hcol)
  have hMadd : ∀ c ∈ Cmain, famOf (Mmain c) ⊆ famOf (colourFam φ c) ∪
      ((𝓗.smallEdges r₁ \ (R_res ∪ famUnionFinset Mdiff Cdiff)) ∪ R₂) := by
    intro c hc f hf
    obtain ⟨e, he, heq⟩ := mem_famOf.mp hf
    by_cases hcol : e ∈ colourFam φ c
    · exact Or.inl (by rw [← heq]; exact ⟨e, hcol, rfl⟩)
    · exact Or.inr (by rw [← heq]; exact h6₁₅ c hc e he hcol)
  have hMN : ∀ c ∈ Cmain, famOf (Mmain c) ⊆ famOf (colourFam φ c) ∪
      (⋃ i : Fin Cmain.card, N i) := by
    intro c hc f hf
    obtain ⟨e, he, heq⟩ := mem_famOf.mp hf
    by_cases hcol : e ∈ colourFam φ c
    · exact Or.inl (by rw [← heq]; exact ⟨e, hcol, rfl⟩)
    · exact Or.inr (by rw [← heq]; exact h6₁₉ c hc e he)
  have hBadd : ∀ c ∈ Cbuff, famOf (Mbuff c) ⊆ famOf (colourFam φ c) ∪ (𝓗rem ∪ R₃) := by
    intro c hc f hf
    obtain ⟨e, he, heq⟩ := mem_famOf.mp hf
    by_cases hcol : e ∈ colourFam φ c
    · exact Or.inl (by rw [← heq]; exact ⟨e, hcol, rfl⟩)
    · exact Or.inr (by rw [← heq]; exact h7₄ c hc e he hcol)
  -- ## the bookkeeping facts
  have hpowSize : ∀ e ∈ 𝓗.pow2, edgeSize e = 2 := fun e he => (mem_pow2.mp he).2
  have hsmallSize : ∀ e ∈ 𝓗.smallEdges r₁, edgeSize e ≤ r₁ :=
    fun e he => ((mem_smallEdges 𝓗 r₁ e).mp he).2
  have hR₁pow : R₁ ⊆ 𝓗.pow2 := by
    rw [hstep4.hR₁_eq]
    exact Set.sdiff_subset.trans hRabs_pow2
  have hR₂pow : R₂ ⊆ 𝓗.pow2 := by
    rw [hstep5.hR₂_eq]; exact Set.sdiff_subset.trans hR₁pow
  have hremSmall : 𝓗rem ⊆ 𝓗.smallEdges r₁ := by
    rw [h𝓗rem]
    exact fun e he => he.1
  have hR₂R₁ : R₂ ⊆ R₁ := by
    rw [hstep5.hR₂_eq]; exact Set.sdiff_subset
  have hR₃R₂ : R₃ ⊆ R₂ := by rw [hR₃def]; exact Set.sdiff_subset
  have hR₁res : R₁ ⊆ R_res := by
    rw [hstep4.hR₁_eq]; exact Set.sdiff_subset.trans hRabs_sub
  have hMD_R₁ : Disjoint (famUnionFinset Mdiff Cdiff) R₁ := by
    rw [hstep4.hR₁_eq, Set.disjoint_left]
    intro e he he'
    exact he'.2 (by
      obtain ⟨c, hc, hec⟩ := mem_famUnionFinset.mp he
      exact mem_famUnionIdx.mpr ⟨c, hec⟩)
  have hHM_R₂ : Disjoint (famUnionFinset Mhm (Cmed ∪ Chuge)) R₂ := by
    rw [hstep5.hR₂_eq, Set.disjoint_left]
    intro e he he'
    exact he'.2 (by
      obtain ⟨c, hc, hec⟩ := mem_famUnionFinset.mp he
      exact mem_famUnionFinset.mpr ⟨c, by
        rcases Finset.mem_union.mp hc with h | h
        · exact Finset.mem_union_right Chuge h
        · exact Finset.mem_union_left Cmed h, hec⟩)
  have hR₃N : R₃ ⊆ R₂ \ (⋃ i : Fin Cmain.card, N i) := by
    rw [hR₃def]
  have hrem : 𝓗rem ⊆ 𝓗.smallEdges r₁ \
      (R_res ∪ famUnionFinset Mdiff Cdiff ∪ (⋃ i : Fin Cmain.card, N i)) := by
    rw [h𝓗rem]
  have hHdisj : ∀ c ∈ Cmed ∪ Chuge, ∀ c' ∈ Cmed ∪ Chuge, c ≠ c' →
      Disjoint (famOf (Mhm c)) (famOf (Mhm c')) :=
    fun c hc c' hc' hne => disjoint_famOf (hstep5.hm_disj c (hcu c hc) c' (hcu c' hc') hne)
  have hMdisj : ∀ c ∈ Cmain, ∀ c' ∈ Cmain, c ≠ c' →
      Disjoint (famOf (Mmain c)) (famOf (Mmain c')) :=
    fun c hc c' hc' hne => disjoint_famOf (h6₂₀ c hc c' hc' hne)
  have hBdisj : ∀ c ∈ Cbuff, ∀ c' ∈ Cbuff, c ≠ c' →
      Disjoint (famOf (Mbuff c)) (famOf (Mbuff c')) := fun c _ c' _ hne => h7₆ c c' hne
  have hcoldisj : ∀ c c' : Fin n, c ≠ c' →
      Disjoint (famOf (colourFam φ c)) (famOf (colourFam φ c')) :=
    fun c c' hne => disjoint_famOf (disjoint_colourFam hne)
  -- ## the sizes of the colour classes and of the added edges
  have hcolBig : ∀ c ∈ Cprev, ∀ e ∈ famOf (colourFam φ c), (r₁ : ℝ) < (edgeSize e : ℝ) := by
    intro c hc e he
    obtain ⟨e', he', heq⟩ := mem_famOf.mp he
    rw [← heq]
    exact (mem_colourFam.mp he').1.2
  have haddedSize : ∀ c ∈ Cprev, ∀ f ∈ prevFam Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff c,
      f ∉ famOf (colourFam φ c) → (edgeSize f : ℝ) ≤ (r₁ : ℝ) := by
    intro c hc f hf hn
    have h2 : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hm.hr₁2
    rcases prevFam_or_added hCmedD hChuge_nd hCmain_nd hCbuff_nd hc hf with h | h
    · exact absurd h hn
    rcases h with ⟨hD, hfM⟩ | ⟨hH, hfM⟩ | ⟨hM, hfM⟩ | ⟨hB, hfM⟩
    · rcases hDadd c hD hfM with h | h
      · exact absurd h hn
      · rw [hpowSize f h]; exact h2
    · rcases hHadd c hH hfM with h | h
      · exact absurd h hn
      · rw [hpowSize f (hR₁pow h)]; exact h2
    · rcases hMadd c hM hfM with h | h
      · exact absurd h hn
      · rcases h with hin | hin
        · exact_mod_cast hsmallSize f hin.1
        · rw [hpowSize f (hR₂pow hin)]; exact h2
    · rcases hBadd c hB hfM with h | h
      · exact absurd h hn
      · rcases h with hin | hin
        · exact_mod_cast hsmallSize f (hremSmall hin)
        · rw [hpowSize f (hR₃pow hin)]; exact h2
  -- ## the pairwise edge-disjointness of the four families
  have hdisj : ∀ c ∈ Cprev, ∀ c' ∈ Cprev, c ≠ c' →
      Disjoint (prevFam Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff c)
        (prevFam Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff c') :=
    prevFam_pairwise_disjoint hCprevdef hCmedD hChuge_nd hCmain_nd hCbuff_nd
      hS12.hCdiff_card hcolBig haddedSize hDadd hHadd hMadd hBadd hMN hMD_R₁ hHM_R₂
      hR₂R₁ hR₃R₂ hR₁res hR₃N hrem hHdisj hMdisj hBdisj hcoldisj

  -- ## membership of `𝓜_prev` from its four branches
  have hCdiff_of_main : ∀ x ∈ Cmain, x ∉ Cdiff := fun x hx hh =>
    (hCmain_nd x hx) (Finset.mem_union_left Chuge (Finset.mem_union_right Cmed hh))
  have hCdiff_of_buff : ∀ x ∈ Cbuff, x ∉ Cdiff := fun x hx hh =>
    (hCbuff_nd x hx) (Finset.mem_union_left Cmain (Finset.mem_union_left Chuge
      (Finset.mem_union_right Cmed hh)))
  have hCmain_of_buff : ∀ x ∈ Cbuff, x ∉ Cmain := fun x hx hh =>
    (hCbuff_nd x hx) (Finset.mem_union_right (Cmed ∪ Cdiff ∪ Chuge) hh)
  have hCmedChuge : ∀ x ∈ Cmed ∪ Chuge, x ∈ Cmed ∪ Cdiff ∪ Chuge := by
    intro x hx
    rcases Finset.mem_union.mp hx with h1 | h1
    · exact Finset.mem_union_left Chuge (Finset.mem_union_left Cdiff h1)
    · exact Finset.mem_union_right (Cmed ∪ Cdiff) h1
  have hCdiff_of_H : ∀ x ∈ Cmed ∪ Chuge, x ∉ Cdiff := by
    intro x hx hh
    rcases Finset.mem_union.mp hx with h5 | h5
    · exact Finset.disjoint_left.mp hCmedD h5 hh
    · exact hChuge_nd x h5 (Finset.mem_union_right Cmed hh)
  have hCmain_of_H : ∀ x ∈ Cmed ∪ Chuge, x ∉ Cmain := fun x hx hh =>
    (hCmain_nd x hh) (hCmedChuge x hx)
  have hCbuff_of_H : ∀ x ∈ Cmed ∪ Chuge, x ∉ Cbuff := fun x hx hh =>
    (hCbuff_nd x hh) (Finset.mem_union_left Cmain (hCmedChuge x hx))
  have hCprev_mem : ∀ x ∈ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff,
      x ∈ Cprev := fun x hx => by rw [hCprevdef]; exact hx
  have hMdiff_of_famOf : ∀ c ∈ Cdiff, ∀ f : 𝓗,
      (f : Set (Fin n)) ∈ famOf (Mdiff c) → f ∈ Mdiff c := fun c hc f hf => by
    obtain ⟨f', hf', heq⟩ := mem_famOf.mp hf
    rwa [← Subtype.ext heq]
  have hMmain_of_famOf : ∀ i : Fin Cmain.card, ∀ f : 𝓗,
      (f : Set (Fin n)) ∈ N i → f ∈ Mmain (colourEnum Cmain i) := fun i f hf => by
    rw [h6₂₁ i, mem_toFam, nonsing, Set.mem_ofPred_eq]
    exact ⟨hf, by have := hbig f f.2; rwa [edgeSize_eq_ncard] at this⟩
  have hMprev_of_Mdiff : ∀ c ∈ Cdiff, ∀ f ∈ Mdiff c, f ∈ Mprev c := fun c hc f hf => by
    rw [hMprevdef, prevFamE, mem_toFam, nonsing, Set.mem_ofPred_eq]
    refine ⟨?_, by have := hbig f f.2; rwa [edgeSize_eq_ncard] at this⟩
    rw [prevFam_of_mem_Cdiff hc]
    exact ⟨f, hf, rfl⟩
  have hMprev_of_Mhm : ∀ c ∈ Cmed ∪ Chuge, ∀ f ∈ Mhm c, f ∈ Mprev c := fun c hc f hf => by
    rw [hMprevdef, prevFamE, mem_toFam, nonsing, Set.mem_ofPred_eq]
    refine ⟨?_, by have := hbig f f.2; rwa [edgeSize_eq_ncard] at this⟩
    rw [prevFam_of_notMem (hCdiff_of_H c hc) (hCmain_of_H c hc) (hCbuff_of_H c hc)]
    exact ⟨f, hf, rfl⟩
  have hMprev_of_Mmain : ∀ c ∈ Cmain, ∀ f ∈ Mmain c, f ∈ Mprev c := fun c hc f hf => by
    rw [hMprevdef, prevFamE, mem_toFam, nonsing, Set.mem_ofPred_eq]
    refine ⟨?_, by have := hbig f f.2; rwa [edgeSize_eq_ncard] at this⟩
    rw [prevFam_of_mem_Cmain (hCdiff_of_main c hc) hc]
    exact ⟨f, hf, rfl⟩
  have hMprev_of_N : ∀ i : Fin Cmain.card, ∀ f : 𝓗, (f : Set (Fin n)) ∈ N i →
      f ∈ Mprev (colourEnum Cmain i) := fun i f hf =>
    hMprev_of_Mmain _ (colourEnum_mem Cmain i) f (hMmain_of_famOf i f hf)
  have hMprev_of_Mbuff : ∀ c ∈ Cbuff, ∀ f ∈ Mbuff c, f ∈ Mprev c := fun c hc f hf => by
    rw [hMprevdef, prevFamE, mem_toFam, nonsing, Set.mem_ofPred_eq]
    refine ⟨?_, by have := hbig f f.2; rwa [edgeSize_eq_ncard] at this⟩
    rw [prevFam_of_mem_Cbuff (hCdiff_of_buff c hc) (hCmain_of_buff c hc) hc]
    exact ⟨f, hf, rfl⟩
  have hHsupp : ∀ c ∉ Cmed ∪ Chuge, Mhm c = ∅ := by
    intro c hc
    rw [Finset.union_comm] at hc
    exact hstep5.hm_supp c hc
  -- ## the basic fields of `S12Out`
  have hsup : ∀ c ∉ Cprev, Mprev c = ∅ := by
    intro c hc
    have hc' : c ∉ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff := fun hh => hc (hCprev_mem c hh)
    have h1 : prevFam Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff c = ∅ :=
      prevFam_eq_empty (Cmed := Cmed) (Cdiff := Cdiff) (Chuge := Chuge) (Cmain := Cmain)
        (Cbuff := Cbuff) hstep4.hMdiff_supp hHsupp h6₁₃ h7₁ hc'
    rw [hMprevdef, prevFamE, h1]
    ext e
    simp only [mem_toFam, nonsing, Set.mem_ofPred_eq, Set.mem_empty_iff_false, false_and]
  have hext : ∀ c ∈ Cprev, colourFam φ c ⊆ Mprev c := by
    intro c hc
    have hc' : c ∈ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff := by rwa [hCprevdef] at hc
    have htag : c ∈ Cdiff ∨ c ∈ Cmain ∨ c ∈ Cbuff ∨ c ∈ Cmed ∪ Chuge := by
      simp only [Finset.mem_union] at hc'
      rcases hc' with (((h1 | h2) | h3) | h4) | h5
      · exact Or.inr (Or.inr (Or.inr (Finset.mem_union.mpr (Or.inl h1))))
      · exact Or.inl h2
      · exact Or.inr (Or.inr (Or.inr (Finset.mem_union.mpr (Or.inr h3))))
      · exact Or.inr (Or.inl h4)
      · exact Or.inr (Or.inr (Or.inl h5))
    rcases htag with h | h | h | h
    · rw [hMprevdef, prevFamE, prevFam_of_mem_Cdiff h]
      exact subset_toFam_famOf hbig (hstep4.hMdiff_ext c h)
    · rw [hMprevdef, prevFamE, prevFam_of_mem_Cmain (hCdiff_of_main c h) h]
      exact subset_toFam_famOf hbig (h6₁₂ c h)
    · rw [hMprevdef, prevFamE, prevFam_of_mem_Cbuff (hCdiff_of_buff c h) (hCmain_of_buff c h) h]
      exact subset_toFam_famOf hbig (h7₂ c h)
    · rw [hMprevdef, prevFamE,
        prevFam_of_notMem (hCdiff_of_H c h) (hCmain_of_H c h) (hCbuff_of_H c h)]
      exact subset_toFam_famOf hbig (hstep5.hm_ext c (hcu c h))
  have hmat : ∀ c, IsMatching 𝓗 (Mprev c) := by
    intro c
    rw [hMprevdef, prevFamE]
    exact isMatching_prevFam_toFam hstep4.hMdiff_mat hstep5.hm_mat h6₁₄ h7₃ c
  have hres_pow2 : R_res ⊆ 𝓗.pow2 := by
    rcases hres with h | h | h
    · exact h.subset_pow2
    · exact h.subset_pow2
    · exact h.1.subset_pow2
  have hRfin : R_final = R_res \ famUnionIdx Mprev := by rw [hRfinaldef]
  have hRfin_sub : R_final ⊆ R_res := by rw [hRfinaldef]; exact Set.sdiff_subset
  have hRfin2 : ∀ e ∈ R_final, e.ncard = 2 := by
    intro e he
    have h1 : e ∈ R_res := hRfin_sub he
    have h2 := (mem_pow2.mp (hres_pow2 h1)).2
    rwa [← edgeSize_eq_ncard]


  -- ## the coverage of `C_prev` by the colour sets
  have hCprev_of_Cdiff : ∀ c ∈ Cdiff, c ∈ Cprev := fun c hc => hCprev_mem c (by
    exact Finset.mem_union_left Cbuff (Finset.mem_union_left Cmain
      (Finset.mem_union_left Chuge (Finset.mem_union_right Cmed hc))))
  have hCprev_of_Cmain : ∀ c ∈ Cmain, c ∈ Cprev := fun c hc => hCprev_mem c (by
    exact Finset.mem_union_left Cbuff (Finset.mem_union_right (Cmed ∪ Cdiff ∪ Chuge) hc))
  have hCprev_of_Cbuff : ∀ c ∈ Cbuff, c ∈ Cprev := fun c hc => hCprev_mem c (by
    exact Finset.mem_union_right (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain) hc)
  have hCprev_of_H : ∀ c ∈ Cmed ∪ Chuge, c ∈ Cprev := fun c hc => hCprev_mem c (by
    exact Finset.mem_union_left Cbuff (Finset.mem_union_left Cmain (by
      rcases Finset.mem_union.mp hc with h | h
      · exact Finset.mem_union_left Chuge (Finset.mem_union_left Cdiff h)
      · exact Finset.mem_union_right (Cmed ∪ Cdiff) h)))
  have hMprev_to_prevFam : ∀ c ∈ Cprev, ∀ f ∈ Mprev c,
      (f : Set (Fin n)) ∈ prevFam Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff c := by
    intro c hc f hf
    rw [hMprevdef, prevFamE, mem_toFam] at hf
    exact hf.1
  -- ## the decomposition of `𝓗`
  have hdecomp : ∀ e : 𝓗, (∃ c ∈ Cprev, e ∈ Mprev c) ∨
      ((e : Set (Fin n)) ∈ R_final ∨ ∃ c ∈ Cfinal, e ∈ colourFam φ c) := by
    intro e
    by_cases hM : ∃ c ∈ Cprev, e ∈ Mprev c
    · exact Or.inl hM
    · refine Or.inr ?_
      push_neg at hM
      by_cases hsmall : edgeSize (e : Set (Fin n)) ≤ r₁
      · -- `e` is a small edge: it lies in the reservoir or in `𝓜_prev`
        refine Or.inl ?_
        rw [hRfinaldef, Set.mem_sdiff]
        refine ⟨?_, ?_⟩
        · by_contra hR'
          have hrem : (e : Set (Fin n)) ∈ 𝓗rem := by
            rw [h𝓗rem]
            refine ⟨⟨e.2, hsmall⟩, ?_⟩
            intro hcon
            rcases hcon with (hR | hD) | hUn
            · exact hR' hR
            · obtain ⟨c, hc, hec⟩ := mem_famUnionFinset.mp hD
              exact hM c (hCprev_of_Cdiff c hc)
                (hMprev_of_Mdiff c hc e (hMdiff_of_famOf c hc e hec))
            · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hUn
              exact hM (colourEnum Cmain i) (hCprev_of_Cmain _ (colourEnum_mem Cmain i))
                (hMprev_of_N i e hi)
          obtain ⟨c, hc, hf⟩ := h7₅ (e : Set (Fin n)) hrem
          obtain ⟨e', he', heq⟩ := mem_famOf.mp hf
          have he'' : e ∈ Mbuff c := by rwa [Subtype.ext heq] at he'
          exact hM c (hCprev_of_Cbuff c hc) (hMprev_of_Mbuff c hc e he'')
        · rw [mem_famUnionIdx]
          rintro ⟨c, hfc⟩
          obtain ⟨e', he', heq⟩ := mem_famOf.mp hfc
          have he'' : e ∈ Mprev c := by rwa [Subtype.ext heq] at he'
          by_cases hcin : c ∈ Cprev
          · exact hM c hcin he''
          · rw [hsup c hcin] at he''
            exact absurd he'' (by simp)
      · -- `e` is a large edge: its colour in `φ` is in `C_prev` or in `C_final`
        push_neg at hsmall
        let e' : ↥(medLarge 𝓗 (r₁ : ℝ)) :=
          ⟨(e : Set (Fin n)), e.2, by exact_mod_cast hsmall⟩
        have hmem : e ∈ colourFam φ (φ.labels e') :=
          mem_colourFam.mpr ⟨⟨e.2, by exact_mod_cast hsmall⟩,
            (mem_colorClass φ (φ.labels e')
              ⟨(e : Set (Fin n)), e.2, by exact_mod_cast hsmall⟩).mpr
              (congrArg φ.labels (Subtype.ext rfl))⟩
        by_cases hc : φ.labels e' ∈ Cprev
        · exact absurd (hext (φ.labels e') hc hmem) (hM (φ.labels e') hc)
        · refine Or.inr ⟨φ.labels e', ?_, hmem⟩
          rw [hS12.hCfinal_eq, Finset.mem_sdiff]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [← hCprevdef]
          exact hc

  -- ## `𝓗_final` is `R_final` together with the colour classes of `C_final`
  have hprevFam_to_Mprev : ∀ c ∈ Cprev, ∀ f : 𝓗,
      (f : Set (Fin n)) ∈ prevFam Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff c → f ∈ Mprev c := by
    intro c hc f hf
    rw [hMprevdef, prevFamE, mem_toFam, nonsing, Set.mem_ofPred_eq]
    exact ⟨hf, by have := hbig f f.2; rwa [edgeSize_eq_ncard] at this⟩
  have hcfin_not_Cprev : ∀ c ∈ Cfinal, c ∉ Cprev := by
    intro c hc hcon
    have h1 : c ∈ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff := by
      rw [← hCprevdef]; exact hcon
    rw [hS12.hCfinal_eq] at hc
    exact (Finset.mem_sdiff.mp hc).2 h1
  have hfin_eq : 𝓗fin = R_final ∪ famUnionFinset (fun c => colourFam φ c) Cfinal := by
    rw [h𝓗findef]
    ext e
    rw [mem_hfinOf]
    constructor
    · rintro ⟨he𝓗, hnotM⟩
      rcases hdecomp ⟨e, he𝓗⟩ with ⟨c, hc, hmem⟩ | (hR | ⟨c, hc, hmem⟩)
      · exact absurd (hMprev_to_prevFam c hc ⟨e, he𝓗⟩ hmem) (hnotM ⟨c, hc⟩)
      · exact Or.inl hR
      · exact Or.inr (mem_famUnionFinset.mpr ⟨c, hc, ⟨⟨e, he𝓗⟩, hmem, rfl⟩⟩)
    · rintro (hR | hmem)
      · have he𝓗 : e ∈ 𝓗 := (mem_pow2.mp (hres_pow2 (hRfin_sub hR))).1
        refine ⟨he𝓗, ?_⟩
        intro c
        intro hc
        have h1 : (⟨e, he𝓗⟩ : 𝓗) ∈ Mprev c.1 := hprevFam_to_Mprev c.1 c.2 ⟨e, he𝓗⟩ hc
        rw [hRfinaldef] at hR
        exact hR.2 (mem_famUnionIdx.mpr ⟨c.1, ⟨⟨e, he𝓗⟩, h1, rfl⟩⟩)
      · obtain ⟨c, hc, hfc⟩ := mem_famUnionFinset.mp hmem
        obtain ⟨e'', he'', heq''⟩ := mem_famOf.mp hfc
        refine ⟨?_, ?_⟩
        · rw [← heq'']; exact e''.2
        · intro c'
          intro hc'
          by_cases hcol : (e : Set (Fin n)) ∈ famOf (colourFam φ c'.1)
          · obtain ⟨e₃, he₃, heq₃⟩ := mem_famOf.mp hcol
            have he₃' : e'' ∈ colourFam φ c'.1 := (Subtype.ext (heq₃.trans heq''.symm)) ▸ he₃
            have hcc : c = c'.1 := colourFam_eq_of_mem he'' he₃'
            exact (hcfin_not_Cprev c hc) (hcc ▸ c'.2)
          · have h2 := haddedSize c'.1 c'.2 (e : Set (Fin n)) hc' hcol
            have h3 : (r₁ : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ) := by
              rw [← heq'']
              exact (mem_colourFam.mp he'').1.2
            linarith

  -- ## the exact degree identity for `𝓗_final`
  have hdisjRF : Disjoint R_final (famUnionFinset (fun c => colourFam φ c) Cfinal) := by
    rw [Set.disjoint_left]
    intro e he he'
    have h1 : edgeSize e = 2 := (mem_pow2.mp (hres_pow2 (hRfin_sub he))).2
    obtain ⟨c, hc, hfc⟩ := mem_famUnionFinset.mp he'
    obtain ⟨e', he', heq⟩ := mem_famOf.mp hfc
    have h2 : (r₁ : ℝ) < (edgeSize (e' : Set (Fin n)) : ℝ) := (mem_colourFam.mp he').1.2
    rw [← heq] at h1
    rw [h1] at h2
    norm_num at h2
    linarith [hm.hr₁2]
  have hdeg_fin : ∀ w : Fin n, (MultiHypergraph.hdeg 𝓗fin w : ℝ) =
      (degAt R_final w : ℝ) + ((finalColoursAt φ Cfinal w).card : ℝ) := by
    intro w
    rw [hfin_eq, hdeg_union hdisjRF w, hdeg_eq_degAt R_final hRfin2 w,
      hdeg_famUnionFinset_colourFam (φ := φ) Cfinal w]
    push_cast
    ring

  -- ## the deficit bound
  set S : Fin n → Hypergraph (Fin n) :=
    fun i => prevFam Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff i with hSdef
  set T : Finset (Fin n) := Cdiff ∪ Chuge ∪ Cmed ∪ Cbuff with hTdef
  have hUnionEq : famUnionIdx (prevFamE Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff) =
      ⋃ i : Fin n, S i := by
    rw [hSdef]
    ext e
    rw [mem_famUnionIdx, Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨e', he', heq⟩ := mem_famOf.mp hi
      refine ⟨i, ?_⟩
      by_cases hic : i ∈ Cprev
      · have h1 : (e' : Set (Fin n)) ∈ prevFam Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff i :=
          hMprev_to_prevFam i hic e' he'
        rwa [heq] at h1
      · have h0 : prevFamE Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff i = ∅ := by
          rw [← hMprevdef]
          exact hsup i hic
        rw [h0] at he'
        exact absurd he' (by simp)
    · rintro ⟨i, hi⟩
      by_cases hic : i ∈ Cprev
      · have he𝓗 : e ∈ 𝓗 := prevFam_subset_hyp Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff i hi
        rw [← hMprevdef]
        exact ⟨i, ⟨⟨e, he𝓗⟩, hprevFam_to_Mprev i hic ⟨e, he𝓗⟩ hi, rfl⟩⟩
      · have h0 : prevFam Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff i = ∅ :=
          prevFam_eq_empty (Cmed := Cmed) (Cdiff := Cdiff) (Chuge := Chuge)
            (Cmain := Cmain) (Cbuff := Cbuff) hstep4.hMdiff_supp hHsupp h6₁₃ h7₁
            (fun hh => hic (hCprev_mem i hh))
        rw [h0] at hi
        exact absurd hi (by simp)
  have hdeficit : ∀ w : Fin n, (degAt (R_res \ R_final) w : ℝ) ≤
      15 * Real.sqrt γ * (n : ℝ) := by
    intro w
    have hRfin' : R_final = R_res \ (⋃ i : Fin n, S i) := by rw [hRfinaldef, hUnionEq]
    have hmatch : ∀ i ∈ T, ∀ w : Fin n, degAt (S i) w ≤ 1 := by
      intro i hi w
      rw [hTdef] at hi
      rw [Finset.mem_union, Finset.mem_union, Finset.mem_union] at hi
      change degAt (prevFam Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff i) w ≤ 1
      rcases hi with ((hD | hH) | hM) | hB
      · rw [prevFam_of_mem_Cdiff hD]
        exact ncard_nbrs_famOf_le_one (hstep4.hMdiff_mat i) w
      · have hD : i ∉ Cdiff := fun hh => hChuge_nd i hH (Finset.mem_union.mpr (Or.inr hh))
        have hM' : i ∉ Cmain := fun hh =>
          (hCmain_nd i hh) (Finset.mem_union.mpr (Or.inr hH))
        have hB' : i ∉ Cbuff := fun hh => (hCbuff_nd i hh)
          (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hH))))
        rw [prevFam_of_notMem hD hM' hB']
        exact ncard_nbrs_famOf_le_one (hstep5.hm_mat i) w
      · have hD : i ∉ Cdiff := Finset.disjoint_left.mp hCmedD hM
        have hM' : i ∉ Cmain := fun hh =>
          (hCmain_nd i hh) (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hM))))
        have hB' : i ∉ Cbuff := fun hh => (hCbuff_nd i hh)
          (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
            (Finset.mem_union.mpr (Or.inl hM))))))
        rw [prevFam_of_notMem hD hM' hB']
        exact ncard_nbrs_famOf_le_one (hstep5.hm_mat i) w
      · rw [prevFam_of_mem_Cbuff (hCdiff_of_buff i hB) (hCmain_of_buff i hB) hB]
        exact ncard_nbrs_famOf_le_one (h7₃ i) w
    have hTcard : (T.card : ℝ) + 2 * γ * ((Cmain.card : ℕ) : ℝ) ≤
        15 * Real.sqrt γ * (n : ℝ) := by
      rw [hTdef]
      exact hdeficitNum
    have hNsub : R_res ∩ (⋃ i ∈ ((Tᶜ : Finset (Fin n)) : Set (Fin n)), S i) ⊆
        R_abs ∩ (⋃ j : Fin Cmain.card, N j) := by
      rintro e ⟨heR, heU⟩
      rw [Set.mem_iUnion₂] at heU
      obtain ⟨i, hi_t, hi_mem⟩ := heU
      have hi_not : i ∉ T := by
        simpa [Finset.mem_coe] using hi_t
      simp only [hSdef] at hi_mem
      have hic : i ∈ Cprev := by
        by_contra hcon
        have h0 : prevFam Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff i = ∅ :=
          prevFam_eq_empty (Cmed := Cmed) (Cdiff := Cdiff) (Chuge := Chuge)
            (Cmain := Cmain) (Cbuff := Cbuff) hstep4.hMdiff_supp hHsupp h6₁₃ h7₁
            (fun hh => hcon (hCprev_mem i hh))
        rw [h0] at hi_mem
        exact absurd hi_mem (by simp)
      have hi_mem' : i ∈ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff := by
        rw [← hCprevdef]; exact hic
      have hiM : i ∈ Cmain := by
        by_contra hnot
        rw [hTdef] at hi_not
        apply hi_not
        simp only [Finset.mem_union] at hi_mem' ⊢
        rcases hi_mem' with (((h1 | h2) | h3) | h4) | h5
        · exact Or.inl (Or.inr h1)
        · exact Or.inl (Or.inl (Or.inl h2))
        · exact Or.inl (Or.inl (Or.inr h3))
        · exact absurd h4 hnot
        · exact Or.inr h5
      set j : Fin Cmain.card := (Cmain.orderIsoOfFin rfl).symm ⟨i, hiM⟩ with hj
      have hji : colourEnum Cmain j = i := by
        rw [hj]; exact colourEnum_symm hiM
      have hMmain_eq : Mmain i = toFam (𝓗 := 𝓗) (N j) := by
        rw [← hji]; exact h6₂₁ j
      have h2e : edgeSize e = 2 := (mem_pow2.mp (hres_pow2 heR)).2
      have heF : e ∈ famOf (Mmain i) := by
        rw [prevFam_of_mem_Cmain (hCdiff_of_main i hiM) hiM] at hi_mem
        exact hi_mem
      obtain ⟨e', he', heq⟩ := mem_famOf.mp heF
      have hNmem : e ∈ N j := by
        have h1 : e' ∈ toFam (𝓗 := 𝓗) (N j) := hMmain_eq ▸ he'
        rw [mem_toFam, nonsing, Set.mem_ofPred_eq] at h1
        have h2 : (e' : Set (Fin n)) ∈ N j := h1.1
        rwa [heq] at h2
      have hnotcol : e ∉ cmainFam φ Cmain j := by
        intro hcol
        have hbig2 := cmainFam_lt_edgeSize hcol
        rw [h2e] at hbig2
        norm_num at hbig2
        linarith [hm.hr₁2]
      have h7 := h6₇ j e hNmem hnotcol
      refine ⟨?_, Set.mem_iUnion.mpr ⟨j, hNmem⟩⟩
      rcases h7 with hst | hR₂
      · exfalso
        rw [MultiHypergraph.mem_edgeSet] at hst
        rcases hst with h1 | ⟨v, hv, -⟩
        · rw [h6₃, h6₁] at h1
          exact h1.1.2 heR
        · have h1 : edgeSize e = 1 := by rw [hv, edgeSize_eq_ncard, Set.ncard_singleton]
          omega
      · have h1 : e ∈ R₁ := by
          rw [hstep5.hR₂_eq] at hR₂
          exact hR₂.1
        rw [hstep4.hR₁_eq] at h1
        exact h1.1
    have hmain : ∀ w : Fin n, (degAt (R_res ∩ (⋃ i ∈ ((Tᶜ : Finset (Fin n)) :
        Set (Fin n)), S i)) w : ℝ) ≤ 2 * γ * ((Cmain.card : ℕ) : ℝ) := by
      intro w
      have h1 : degAt (R_res ∩ (⋃ i ∈ ((Tᶜ : Finset (Fin n)) : Set (Fin n)), S i)) w ≤
          degAt (R_abs ∩ (⋃ j : Fin Cmain.card, N j)) w :=
        degAt_mono hNsub w
      have h2 : degAt (R_abs ∩ (⋃ j : Fin Cmain.card, N j)) w =
          (MultiHypergraph.hdeg (R_abs ∩ (⋃ j : Fin Cmain.card, N j)) w) := by
        rw [hdeg_eq_degAt _ _ w]
        intro e he
        rw [← edgeSize_eq_ncard]
        exact (mem_pow2.mp (hRabs_pow2 he.1)).2
      have h3 : (MultiHypergraph.hdeg (R_abs ∩ (⋃ j : Fin Cmain.card, N j)) w : ℝ) =
          ((({e ∈ R_abs | w ∈ e} : Set (Set (Fin n))) ∩
            (⋃ i : Fin Cmain.card, N i)).ncard : ℝ) := by
        have hset : ({e ∈ R_abs ∩ (⋃ j : Fin Cmain.card, N j) | w ∈ e} : Set (Set (Fin n))) =
            ({e ∈ R_abs | w ∈ e} : Set (Set (Fin n))) ∩ (⋃ i : Fin Cmain.card, N i) := by
          ext e
          constructor
          · rintro ⟨⟨he1, he2⟩, he3⟩
            exact ⟨⟨he1, he3⟩, he2⟩
          · rintro ⟨⟨he1, he3⟩, he2⟩
            exact ⟨⟨he1, he2⟩, he3⟩
        rw [MultiHypergraph.hdeg, hset]
      calc (degAt (R_res ∩ (⋃ i ∈ ((Tᶜ : Finset (Fin n)) : Set (Fin n)), S i)) w : ℝ)
          ≤ (degAt (R_abs ∩ (⋃ j : Fin Cmain.card, N j)) w : ℝ) := by exact_mod_cast h1
        _ = (MultiHypergraph.hdeg (R_abs ∩ (⋃ j : Fin Cmain.card, N j)) w : ℝ) := by rw [h2]
        _ = ((({e ∈ R_abs | w ∈ e} : Set (Set (Fin n))) ∩
              (⋃ i : Fin Cmain.card, N i)).ncard : ℝ) := h3
        _ ≤ 2 * γ * ((Cmain.card : ℕ) : ℝ) := h6₁₆ w
    have hdef : (degAt (R_res \ R_final) w : ℝ) ≤
        (T.card : ℝ) + 2 * γ * ((Cmain.card : ℕ) : ℝ) :=
      s12_deficit T hRfin' hmatch hmain w
    linarith [hTcard, hm.hγ0]
  -- ## §12 Steps 8/9: the starred family `𝓜_prev^*` and the degree bounds
  --
  -- The matchings of `C_main` come from the nibble in the multi-hypergraph
  -- `𝓗_reg`; as in the paper we keep their singleton edges when counting the
  -- matchings that miss a vertex (the paper's `m(w)`), while the *edges*
  -- removed from `𝓗` are only their proper parts.
  let Mstar : ↥Cprev → Set (Set (Fin n)) := fun i =>
    if h : (i : Fin n) ∈ Cmain then N ((Cmain.orderIsoOfFin rfl).symm ⟨(i : Fin n), h⟩)
    else prevFam Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff (i : Fin n)
  have hMstar_m : ∀ (i : ↥Cprev) (h : (i : Fin n) ∈ Cmain),
      Mstar i = N ((Cmain.orderIsoOfFin rfl).symm ⟨(i : Fin n), h⟩) := fun i h => dif_pos h
  have hMstar_nm : ∀ i : ↥Cprev, (i : Fin n) ∉ Cmain →
      Mstar i = prevFam Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff (i : Fin n) :=
    fun i h => dif_neg h
  -- `famOf (toFam G) = nonsing G` when the proper parts of `G` lie in `𝓗`
  have hfamOf_toFam : ∀ G : Set (Set (Fin n)), nonsing G ⊆ 𝓗 →
      famOf (toFam (𝓗 := 𝓗) G) = nonsing G := by
    intro G hG
    ext e
    rw [mem_famOf]
    constructor
    · rintro ⟨e', he', rfl⟩
      exact mem_toFam.mp he'
    · intro he
      exact ⟨⟨e, hG he⟩, mem_toFam.mpr he, rfl⟩
  have hN_sub : ∀ j : Fin Cmain.card, nonsing (N j) ⊆ 𝓗 := by
    intro j e he
    have h1 := (h6₄ j).1 he.1
    rw [MultiHypergraph.mem_edgeSet] at h1
    rcases h1 with h1 | ⟨v, hv, -⟩
    · exact h1
    · rw [hv] at he
      exact absurd he.2 (by rw [Set.ncard_singleton]; norm_num)
  have hmstar_nonsing : ∀ i : ↥Cprev,
      nonsing (Mstar i) = prevFam Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff (i : Fin n) := by
    intro i
    by_cases hc : (i : Fin n) ∈ Cmain
    · rw [hMstar_m i hc]
      have hcd : (i : Fin n) ∉ Cdiff := fun h => (hCmain_nd (i : Fin n) hc)
        (Finset.mem_union_left Chuge (Finset.mem_union_right Cmed h))
      rw [prevFam_of_mem_Cmain hcd hc]
      have hMm : Mmain (i : Fin n) = toFam (𝓗 := 𝓗)
          (N ((Cmain.orderIsoOfFin rfl).symm ⟨(i : Fin n), hc⟩)) := by
        have h := h6₂₁ ((Cmain.orderIsoOfFin rfl).symm ⟨(i : Fin n), hc⟩)
        rwa [colourEnum_symm hc] at h
      rw [hMm, hfamOf_toFam _ (hN_sub _)]
    · rw [hMstar_nm i hc]
      exact nonsing_eq_self (fun e he => by
        have h := hbig e (prevFam_subset_hyp Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff (i : Fin n) he)
        rwa [edgeSize_eq_ncard] at h)
  -- the disjointness of the starred matchings (inherited from `𝓜_prev^*`)
  have hdisj_star : ∀ i j : ↥Cprev, i ≠ j → EdgeDisjointFam (Mstar i) (Mstar j) := by
    intro i j hij
    show Disjoint (nonsing (Mstar i)) (nonsing (Mstar j))
    rw [hmstar_nonsing i, hmstar_nonsing j]
    exact hdisj (i : Fin n) i.2 (j : Fin n) j.2 (fun h => hij (Subtype.ext h))
  -- the definition of `𝓗_final` in terms of the starred family
  have hbig_ncard : ∀ e ∈ 𝓗, 2 ≤ e.ncard := fun e he => by
    have := hbig e he
    rwa [edgeSize_eq_ncard] at this
  have hfin_star : ∀ e : Set (Fin n), e ∈ 𝓗fin ↔ e ∈ 𝓗 ∧ ∀ i : ↥Cprev, e ∉ Mstar i := by
    intro e
    rw [h𝓗findef, mem_hfinOf]
    constructor
    · rintro ⟨he𝓗, hM⟩
      refine ⟨he𝓗, fun i => ?_⟩
      intro hmem
      refine hM i ?_
      have h1 : e ∈ nonsing (Mstar i) := ⟨hmem, hbig_ncard e he𝓗⟩
      rwa [hmstar_nonsing i] at h1
    · rintro ⟨he𝓗, hM⟩
      refine ⟨he𝓗, fun i => ?_⟩
      intro hmem
      refine hM i ?_
      have h1 : e ∈ nonsing (Mstar i) := by
        rw [hmstar_nonsing i]
        exact hmem
      exact h1.1
  -- the number of colours `|C_prev|` is `n - |C_final|`
  have hcard_star : (Fintype.card ↥Cprev : ℝ) = (n : ℝ) - (Cfinal.card : ℝ) := by
    rw [Fintype.card_coe]
    have h := hS12.card_Cprev_real
    rwa [← hCprevdef] at h
  -- the singleton bookkeeping `hsingle` of `s12_deg_h_final`
  have hsingle : ∀ w : Fin n,
      (({i : ↥Cprev | w ∈ famVert (Mstar i) ∧
        ¬ ∃ e ∈ Mstar i, w ∈ e ∧ e ∈ 𝓗} : Set ↥Cprev)).ncard ≤
      n - 3 - MultiHypergraph.hdeg 𝓗 w := by
    intro w
    set X : Set ↥Cprev := {i | w ∈ famVert (Mstar i) ∧
      ¬ ∃ e ∈ Mstar i, w ∈ e ∧ e ∈ 𝓗} with hX
    have hCmainX : ∀ i ∈ X, (i : Fin n) ∈ Cmain := by
      intro i hi
      by_contra hc
      have hw : w ∈ famVert (Mstar i) := hi.1
      have hno : ¬ ∃ e ∈ Mstar i, w ∈ e ∧ e ∈ 𝓗 := hi.2
      rw [hMstar_nm i hc] at hw hno
      rw [mem_famVert] at hw
      obtain ⟨e, he, hwe⟩ := hw
      exact hno ⟨e, he, hwe,
        prevFam_subset_hyp Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff (i : Fin n) he⟩
    by_cases hcard0 : Cmain.card = 0
    · have hXempty : X = ∅ := by
        rw [← Set.not_nonempty_iff_eq_empty]
        rintro ⟨i, hi⟩
        have hci := hCmainX i hi
        rw [Finset.card_eq_zero] at hcard0
        rw [hcard0] at hci
        exact absurd hci (Finset.notMem_empty (i : Fin n))
      rw [hXempty, Set.ncard_empty]
      omega
    · have hpos : 0 < Cmain.card := Nat.pos_of_ne_zero hcard0
      let fc : ↥Cprev → Fin Cmain.card := fun i =>
        if h : (i : Fin n) ∈ Cmain then (Cmain.orderIsoOfFin rfl).symm ⟨(i : Fin n), h⟩
        else ⟨0, hpos⟩
      have hfc : ∀ i ∈ X, ({w} : Set (Fin n)) ∈ N (fc i) := by
        intro i hi
        have hc := hCmainX i hi
        have hfi : fc i = (Cmain.orderIsoOfFin rfl).symm ⟨(i : Fin n), hc⟩ := dif_pos hc
        rw [hfi]
        have hw : w ∈ famVert (Mstar i) := hi.1
        have hno : ¬ ∃ e ∈ Mstar i, w ∈ e ∧ e ∈ 𝓗 := hi.2
        rw [hMstar_m i hc] at hw hno
        rw [mem_famVert] at hw
        obtain ⟨e, he, hwe⟩ := hw
        by_contra hsing
        refine hno ⟨e, he, hwe, ?_⟩
        have h1 := (h6₄ _).1 he
        rw [MultiHypergraph.mem_edgeSet] at h1
        rcases h1 with h1 | ⟨v, hv, -⟩
        · exact h1
        · exfalso
          have h1' : w ∈ ({v} : Set (Fin n)) := hv ▸ hwe
          have hwv : w = v := Set.mem_singleton_iff.mp h1'
          exact hsing (by rw [hwv, ← hv]; exact he)
      have hfci : Set.InjOn fc X := by
        intro i hi j hj hij
        have hci := hCmainX i hi
        have hcj := hCmainX j hj
        have h1 : fc i = (Cmain.orderIsoOfFin rfl).symm ⟨(i : Fin n), hci⟩ := dif_pos hci
        have h2 : fc j = (Cmain.orderIsoOfFin rfl).symm ⟨(j : Fin n), hcj⟩ := dif_pos hcj
        have h3 := h1.symm.trans (hij.trans h2)
        have h4 := congrArg (fun x : Fin Cmain.card => colourEnum Cmain x) h3
        simp only [colourEnum_symm] at h4
        exact Subtype.ext h4
      calc X.ncard ≤ ({j : Fin Cmain.card | ({w} : Set (Fin n)) ∈ N j} :
            Set (Fin Cmain.card)).ncard := Set.ncard_le_ncard_of_injOn fc hfc hfci
        _ ≤ n - 3 - MultiHypergraph.hdeg 𝓗 w := h6₂₃ w
  -- ### (b) the coverage and miss bounds for the starred family
  -- a vertex of `C_buff` is never in `C_main` or `C_diff`
  have hCbuff_nd' : ∀ c ∈ Cbuff, c ∉ Cmain := fun c hc h =>
    (hCbuff_nd c hc) (Finset.mem_union_right (Cmed ∪ Cdiff ∪ Chuge) h)
  have hCbuff_d' : ∀ c ∈ Cbuff, c ∉ Cdiff := fun c hc h =>
    (hCbuff_nd c hc) (Finset.mem_union_left Cmain (Finset.mem_union_left Chuge
      (Finset.mem_union_right Cmed h)))
  -- (i) every matching of the starred family covers `U ∖ S₁`
  have hrestcov : ∀ i : ↥Cprev, i ∉ ({i : ↥Cprev | (i : Fin n) ∈ Cdiff} : Set ↥Cprev) →
      U \ famVert (Mstar i) ⊆ S₁ := by
    intro i hi
    have hid : (i : Fin n) ∉ Cdiff := hi
    by_cases hcm : (i : Fin n) ∈ Cmain
    · rw [hMstar_m i hcm]
      intro u hu
      refine hstep5.hS₂_sub ?_
      by_cases hU2 : (1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ)
      · exact (h6₁₁ hU2).2.1 _ hu
      · exact absurd ((h6₁₀ (not_lt.mp hU2) _) hu.1) hu.2
    · by_cases hcb : (i : Fin n) ∈ Cbuff
      · rw [hMstar_nm i hcm, prevFam_of_mem_Cbuff hid hcm hcb, famVert_famOf]
        intro u hu
        by_cases hU3 : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ)
        · have h3 : u ∈ S₃ := (h7₈ hU3).2 (i : Fin n) hcb hu
          rw [hS₃def] at h3
          exact hstep5.hS₂_sub h3.1
        · exact absurd ((h7₇ (not_lt.mp hU3) (i : Fin n) hcb) hu.1) hu.2
      · rw [hMstar_nm i hcm, prevFam_of_notMem hid hcm hcb, famVert_famOf]
        have hcuh : (i : Fin n) ∈ Chuge ∪ Cmed := by
          have h := mem_med_huge_of_mem_prev (by rw [← hCprevdef]; exact i.2) hid hcm hcb
          rcases Finset.mem_union.mp h with h' | h'
          · exact Finset.mem_union_right Chuge h'
          · exact Finset.mem_union_left Cmed h'
        by_cases hU5 : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ)
        · exact (hstep5.hm_near hU5).2 _ hcuh
        · intro u hu
          exact absurd (hstep5.hm_perf (not_lt.mp hU5) _ hcuh hu.1) hu.2
  -- (ii) `C_diff` has at most one colour
  have hdiff1 : (({i : ↥Cprev | (i : Fin n) ∈ Cdiff} : Set ↥Cprev)).ncard ≤ 1 := by
    have h1 : (({i : ↥Cprev | (i : Fin n) ∈ Cdiff} : Set ↥Cprev)).ncard ≤
        ((↑Cdiff : Set (Fin n))).ncard := ncard_subtype_le
    rw [Set.ncard_coe_finset] at h1
    exact le_trans h1 hS12.hCdiff_card
  -- (iii) `𝓜_diff` covers `V^{(n-1)}(𝓗)` and `V_+^{(n-2)}(𝓗) ∩ S₁`
  have hncm_of_diff : ∀ i : ↥Cprev, (i : Fin n) ∈ Cdiff → (i : Fin n) ∉ Cmain :=
    fun i hi h => (hCmain_nd (i : Fin n) h) (Finset.mem_union_left Chuge
      (Finset.mem_union_right Cmed hi))
  have hdiffVn1 : ∀ i ∈ ({i : ↥Cprev | (i : Fin n) ∈ Cdiff} : Set ↥Cprev),
      Vn1set 𝓗 ⊆ famVert (Mstar i) := by
    intro i hi
    rw [hMstar_nm i (hncm_of_diff i hi), prevFam_of_mem_Cdiff hi, famVert_famOf]
    exact hstep4.hMdiff_cov (i : Fin n) hi
  have hdiffVn2 : ∀ i ∈ ({i : ↥Cprev | (i : Fin n) ∈ Cdiff} : Set ↥Cprev),
      Vn2set 𝓗 ∩ S₁ ⊆ famVert (Mstar i) := by
    intro i hi
    rw [hMstar_nm i (hncm_of_diff i hi), prevFam_of_mem_Cdiff hi, famVert_famOf]
    intro v hv
    have hv1 := hv.1
    rw [Set.mem_union] at hv1
    rcases hv1 with h1 | h1
    · exact hstep4.hMdiff_cov (i : Fin n) hi h1
    · exact vn2_inter_S1_subset_matchVert hi hstep4.hS₁_eq ⟨h1, hv.2⟩
  -- (iv) perfect coverage of `U` when `|U| ≤ (1-10ε)n`
  have hperf : (U.ncard : ℝ) ≤ (1 - 10 * ε) * (n : ℝ) → ∀ i : ↥Cprev,
      i ∉ ({i : ↥Cprev | (i : Fin n) ∈ Cdiff} : Set ↥Cprev) → U ⊆ famVert (Mstar i) := by
    intro hU10 i hi
    have hid : (i : Fin n) ∉ Cdiff := hi
    by_cases hcm : (i : Fin n) ∈ Cmain
    · rw [hMstar_m i hcm]
      exact h6₁₀ (by nlinarith [hU10, hm.hε0, Nat.cast_nonneg (α := ℝ) n]) _
    · by_cases hcb : (i : Fin n) ∈ Cbuff
      · rw [hMstar_nm i hcm, prevFam_of_mem_Cbuff hid hcm hcb, famVert_famOf]
        exact h7₇ hU10 (i : Fin n) hcb
      · rw [hMstar_nm i hcm, prevFam_of_notMem hid hcm hcb, famVert_famOf]
        have hcuh : (i : Fin n) ∈ Chuge ∪ Cmed := by
          have h := mem_med_huge_of_mem_prev (by rw [← hCprevdef]; exact i.2) hid hcm hcb
          rcases Finset.mem_union.mp h with h' | h'
          · exact Finset.mem_union_right Chuge h'
          · exact Finset.mem_union_left Cmed h'
        exact hstep5.hm_perf hU10 _ hcuh
  -- (v) the per-vertex miss bound: at most one matching of the starred family
  -- outside `𝓜_diff` misses a given `u ∈ U`
  have hnc_of_med : ∀ c : Fin n, c ∈ Cmed ∪ Chuge → c ∉ Cmain ∧ c ∉ Cdiff ∧ c ∉ Cbuff := by
    intro c hc
    rcases Finset.mem_union.mp hc with h | h
    · refine ⟨fun hh => (hCmain_nd c hh) (Finset.mem_union_left Chuge
          (Finset.mem_union_left Cdiff h)),
        Finset.disjoint_right.mp hS12.hCdiff_med h,
        fun hh => (hCbuff_nd c hh) (Finset.mem_union_left Cmain (Finset.mem_union_left Chuge
          (Finset.mem_union_left Cdiff h)))⟩
    · refine ⟨fun hh => (hCmain_nd c hh) (Finset.mem_union_right (Cmed ∪ Cdiff) h),
        fun hh => (hChuge_nd c h) (Finset.mem_union_right Cmed hh),
        fun hh => (hCbuff_nd c hh) (Finset.mem_union_left Cmain
          (Finset.mem_union_right (Cmed ∪ Cdiff) h))⟩
  have hnp : ∀ u ∈ U, (({i : ↥Cprev | i ∉ ({i : ↥Cprev | (i : Fin n) ∈ Cdiff} : Set ↥Cprev) ∧
      u ∉ famVert (Mstar i)} : Set ↥Cprev)).ncard ≤ 1 := by
    intro u hu
    set X : Set ↥Cprev := {i | i ∉ ({i : ↥Cprev | (i : Fin n) ∈ Cdiff} : Set ↥Cprev) ∧
      u ∉ famVert (Mstar i)} with hX
    set Am : Set ↥Cprev := {i | (i : Fin n) ∈ Cmain ∧ u ∉ famVert (Mstar i)} with hAm
    set Ab : Set ↥Cprev := {i | (i : Fin n) ∈ Cbuff ∧ u ∉ famVert (Mstar i)} with hAb
    set Ah : Set ↥Cprev := {i | (i : Fin n) ∈ Cmed ∪ Chuge ∧ u ∉ famVert (Mstar i)} with hAh
    have hXsub : X ⊆ Am ∪ (Ab ∪ Ah) := by
      intro i hi
      have hid : (i : Fin n) ∉ Cdiff := hi.1
      by_cases hcm : (i : Fin n) ∈ Cmain
      · exact Or.inl ⟨hcm, hi.2⟩
      · by_cases hcb : (i : Fin n) ∈ Cbuff
        · exact Or.inr (Or.inl ⟨hcb, hi.2⟩)
        · have hcmu : (i : Fin n) ∈ Cmed ∪ Chuge :=
            mem_med_huge_of_mem_prev (by rw [← hCprevdef]; exact i.2) hid hcm hcb
          exact Or.inr (Or.inr ⟨hcmu, hi.2⟩)
    -- a vertex of `S₂` is covered by every `𝓜_hm`-matching
    have hS₂cov : u ∈ S₂ → ∀ c ∈ Cmed ∪ Chuge, u ∈ matchVert (Mhm c) := by
      intro huS2 c hc
      by_contra hmiss
      have h1 : u ∈ (⋃ c ∈ (Chuge ∪ Cmed : Finset (Fin n)), (U \ matchVert (Mhm c))) := by
        simp only [Set.mem_iUnion]
        exact ⟨c, hcu c hc, hu, hmiss⟩
      have h2 := huS2
      rw [hstep5.hS₂_eq, Set.mem_sdiff] at h2
      exact h2.2 h1
    -- a vertex of `S₃` is covered by every `𝓜_main`-matching
    have hS₃cov : u ∈ S₃ → ∀ j : Fin Cmain.card, u ∈ famVert (N j) := by
      intro huS3 j
      by_contra hmiss
      have h1 : u ∈ (⋃ j : Fin Cmain.card, (U \ famVert (N j))) :=
        Set.mem_iUnion.mpr ⟨j, hu, hmiss⟩
      have h2 := huS3
      rw [hS₃def, Set.mem_sdiff] at h2
      exact h2.2 h1
    have hAmS₂ : Am.Nonempty → u ∈ S₂ := by
      rintro ⟨i, hi⟩
      have hcm : (i : Fin n) ∈ Cmain := hi.1
      have hmiss : u ∉ famVert (N ((Cmain.orderIsoOfFin rfl).symm ⟨(i : Fin n), hcm⟩)) := by
        rw [← hMstar_m i hcm]
        exact hi.2
      by_cases hU2 : (1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ)
      · exact (h6₁₁ hU2).2.1 _ ⟨hu, hmiss⟩
      · exact absurd ((h6₁₀ (not_lt.mp hU2) _) hu) hmiss
    have hAbS₃ : Ab.Nonempty → u ∈ S₃ := by
      rintro ⟨i, hi⟩
      have hcb : (i : Fin n) ∈ Cbuff := hi.1
      have hcm : (i : Fin n) ∉ Cmain := hCbuff_nd' (i : Fin n) hcb
      have hcd : (i : Fin n) ∉ Cdiff := hCbuff_d' (i : Fin n) hcb
      have hmiss : u ∉ matchVert (Mbuff (i : Fin n)) := by
        have h1 : u ∉ famVert (prevFam Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff (i : Fin n)) := by
          rw [← hMstar_nm i hcm]
          exact hi.2
        rwa [prevFam_of_mem_Cbuff hcd hcm hcb, famVert_famOf] at h1
      by_cases hU3 : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ)
      · exact (h7₈ hU3).2 (i : Fin n) hcb ⟨hu, hmiss⟩
      · exact absurd ((h7₇ (not_lt.mp hU3) (i : Fin n) hcb) hu) hmiss
    have hAhS₂ : Ah.Nonempty → u ∉ S₂ := by
      rintro ⟨i, hi⟩ huS2
      have hcmu : (i : Fin n) ∈ Cmed ∪ Chuge := hi.1
      have hnc := hnc_of_med (i : Fin n) hcmu
      have hmiss : u ∉ matchVert (Mhm (i : Fin n)) := by
        have h1 : u ∉ famVert (prevFam Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff (i : Fin n)) := by
          rw [← hMstar_nm i hnc.1]
          exact hi.2
        rwa [prevFam_of_notMem hnc.2.1 hnc.1 hnc.2.2, famVert_famOf] at h1
      exact hmiss (hS₂cov huS2 (i : Fin n) hcmu)
    have hAmS₃ : Am.Nonempty → u ∉ S₃ := by
      rintro hA huS3
      obtain ⟨i, hi⟩ := hA
      have hcm : (i : Fin n) ∈ Cmain := hi.1
      have hNj : u ∉ famVert (N ((Cmain.orderIsoOfFin rfl).symm ⟨(i : Fin n), hcm⟩)) := by
        rw [← hMstar_m i hcm]
        exact hi.2
      exact hNj (hS₃cov huS3 _)
    have hpairA : ¬ (Am.Nonempty ∧ (Ab ∪ Ah).Nonempty) := by
      rintro ⟨h1, x, hx⟩
      have hnotS3 := hAmS₃ h1
      rcases hx with hb | hh
      · exact hnotS3 (hAbS₃ ⟨x, hb⟩)
      · exact hAhS₂ ⟨x, hh⟩ (hAmS₂ h1)
    have hpairB : ¬ (Ab.Nonempty ∧ Ah.Nonempty) := by
      rintro ⟨h1, h2⟩
      have h1' : u ∈ S₃ := hAbS₃ h1
      have h2' : u ∉ S₂ := hAhS₂ h2
      rw [hS₃def, Set.mem_sdiff] at h1'
      exact h2' h1'.1
    -- the per-family cardinality bounds
    have hL1 : ({j : Fin Cmain.card | u ∉ famVert (N j)} : Set (Fin Cmain.card)).ncard ≤ 1 := by
      by_cases hU2 : (1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ)
      · have h2 : (({j : Fin Cmain.card | u ∈ famVert (N j)} :
            Set (Fin Cmain.card)).ncard : ℝ) + 1 ≥ (Fintype.card (Fin Cmain.card) : ℝ) :=
          (h6₁₁ hU2).1 u hu
        rw [Fintype.card_fin] at h2
        have hsplit : ({j : Fin Cmain.card | u ∉ famVert (N j)} :
              Set (Fin Cmain.card)).ncard +
            ({j : Fin Cmain.card | u ∈ famVert (N j)} : Set (Fin Cmain.card)).ncard =
            Cmain.card := by
          have hcomp : ({j : Fin Cmain.card | u ∈ famVert (N j)} : Set (Fin Cmain.card))ᶜ =
              {j : Fin Cmain.card | u ∉ famVert (N j)} := by
            ext j
            simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
          have hc := Set.ncard_compl_add_ncard
            ({j : Fin Cmain.card | u ∈ famVert (N j)} : Set (Fin Cmain.card))
          rw [hcomp] at hc
          rw [hc, Nat.card_eq_fintype_card, Fintype.card_fin]
        have h3 : (({j : Fin Cmain.card | u ∉ famVert (N j)} :
            Set (Fin Cmain.card)).ncard : ℝ) ≤ 1 := by
          have h4 := congrArg (fun x : ℕ => (x : ℝ)) hsplit
          push_cast at h4
          linarith
        exact_mod_cast h3
      · have hempty : ({j : Fin Cmain.card | u ∉ famVert (N j)} : Set (Fin Cmain.card)) = ∅ := by
          rw [← Set.not_nonempty_iff_eq_empty]
          rintro ⟨j, hj⟩
          exact hj (h6₁₀ (not_lt.mp hU2) j hu)
        rw [hempty, Set.ncard_empty]
        omega
    have hAm_le : Am.ncard ≤ 1 := by
      by_cases hcard0 : Cmain.card = 0
      · have hAempty : Am = ∅ := by
          rw [← Set.not_nonempty_iff_eq_empty]
          rintro ⟨i, hi⟩
          have h1 := hi.1
          rw [Finset.card_eq_zero] at hcard0
          rw [hcard0] at h1
          exact absurd h1 (Finset.notMem_empty (i : Fin n))
        rw [hAempty, Set.ncard_empty]
        omega
      · have hpos : 0 < Cmain.card := Nat.pos_of_ne_zero hcard0
        let g : ↥Cprev → Fin Cmain.card := fun i =>
          if h : (i : Fin n) ∈ Cmain then (Cmain.orderIsoOfFin rfl).symm ⟨(i : Fin n), h⟩
          else ⟨0, hpos⟩
        have hg : ∀ i ∈ Am, u ∉ famVert (N (g i)) := by
          intro i hi
          have hgi : g i = (Cmain.orderIsoOfFin rfl).symm ⟨(i : Fin n), hi.1⟩ := dif_pos hi.1
          rw [hgi, ← hMstar_m i hi.1]
          exact hi.2
        have hgi : Set.InjOn g Am := by
          intro i hi j hj hij
          have h1 : g i = (Cmain.orderIsoOfFin rfl).symm ⟨(i : Fin n), hi.1⟩ := dif_pos hi.1
          have h2 : g j = (Cmain.orderIsoOfFin rfl).symm ⟨(j : Fin n), hj.1⟩ := dif_pos hj.1
          have h3 := h1.symm.trans (hij.trans h2)
          have h4 := congrArg (fun x : Fin Cmain.card => colourEnum Cmain x) h3
          simp only [colourEnum_symm] at h4
          exact Subtype.ext h4
        exact le_trans (Set.ncard_le_ncard_of_injOn g hg hgi) hL1
    have hAb_le : Ab.ncard ≤ 1 := by
      have hg : ∀ i ∈ Ab, (i : Fin n) ∈ ({c : Fin n | c ∈ Cbuff ∧ u ∉ matchVert (Mbuff c)} :
          Set (Fin n)) := by
        intro i hi
        have hcb : (i : Fin n) ∈ Cbuff := hi.1
        have hcm : (i : Fin n) ∉ Cmain := hCbuff_nd' (i : Fin n) hcb
        have hcd : (i : Fin n) ∉ Cdiff := hCbuff_d' (i : Fin n) hcb
        have h1 : u ∉ famVert (prevFam Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff (i : Fin n)) := by
          rw [← hMstar_nm i hcm]
          exact hi.2
        rw [prevFam_of_mem_Cbuff hcd hcm hcb, famVert_famOf] at h1
        exact ⟨hcb, h1⟩
      have hgi : Set.InjOn (fun i : ↥Cprev => (i : Fin n)) Ab :=
        fun i _ j _ hij => Subtype.ext hij
      exact le_trans (Set.ncard_le_ncard_of_injOn (fun i : ↥Cprev => (i : Fin n)) hg hgi)
        (h7₉ u hu)
    have hAh_le : Ah.ncard ≤ 1 := by
      have hg : ∀ i ∈ Ah, (i : Fin n) ∈ ({c : Fin n | c ∈ Chuge ∪ Cmed ∧
          u ∉ matchVert (Mhm c)} : Set (Fin n)) := by
        intro i hi
        have hnc := hnc_of_med (i : Fin n) hi.1
        have h1 : u ∉ famVert (prevFam Mdiff Mhm Mmain Mbuff Cdiff Cmain Cbuff (i : Fin n)) := by
          rw [← hMstar_nm i hnc.1]
          exact hi.2
        rw [prevFam_of_notMem hnc.2.1 hnc.1 hnc.2.2, famVert_famOf] at h1
        exact ⟨hcu (i : Fin n) hi.1, h1⟩
      have hgi : Set.InjOn (fun i : ↥Cprev => (i : Fin n)) Ah :=
        fun i _ j _ hij => Subtype.ext hij
      exact le_trans (Set.ncard_le_ncard_of_injOn (fun i : ↥Cprev => (i : Fin n)) hg hgi)
        (hstep5.hm_miss_vertex u hu)
    -- at most one of the three families is non-empty
    have hbound : X.ncard ≤ 1 := by
      by_cases hA : Am.Nonempty
      · have hrest : (Ab ∪ Ah) = ∅ := by
          rw [← Set.not_nonempty_iff_eq_empty]
          exact fun h => hpairA ⟨hA, h⟩
        have hXs : X ⊆ Am := by
          intro i hi
          rcases hXsub hi with h | h
          · exact h
          · rw [hrest] at h
            exact absurd h (by simp)
        exact le_trans (Set.ncard_le_ncard hXs (Set.toFinite _)) hAm_le
      · rw [Set.not_nonempty_iff_eq_empty] at hA
        have hXs : X ⊆ Ab ∪ Ah := by
          intro i hi
          rcases hXsub hi with h | h
          · rw [hA] at h
            exact absurd h (by simp)
          · exact h
        have h2 : (Ab ∪ Ah).ncard ≤ 1 := by
          by_cases hB : Ab.Nonempty
          · have hrest : Ah = ∅ := by
              rw [← Set.not_nonempty_iff_eq_empty]
              exact fun h => hpairB ⟨hB, h⟩
            rw [hrest, Set.union_empty]
            exact hAb_le
          · rw [Set.not_nonempty_iff_eq_empty] at hB
            rw [hB, Set.empty_union]
            exact hAh_le
        exact le_trans (Set.ncard_le_ncard hXs (Set.toFinite _)) h2
    exact hbound
  -- ### (c) the `m(w)`-bounds of Step 9
  have hm_rest :=
    s12_mbound (ι := ↥Cprev) (M := Mstar) (U := U) (S₁ := S₁) (ε := ε)
      ({i : ↥Cprev | (i : Fin n) ∈ Cdiff}) (Vn1set 𝓗) (Vn2set 𝓗)
      hdiff1 hdiffVn1 hdiffVn2 hrestcov hnp hperf (Vn1set_subset_Vn2set 𝓗) hVn2U
  have hm1a := hm_rest.1
  have hm1b := hm_rest.2.1
  have hm2a := hm_rest.2.2.1
  have hm2b := hm_rest.2.2.2.1
  have hm3 := hm_rest.2.2.2.2
  -- ### (d) `(eqn:deg_h_final)` and the degree bounds UC1--UC4
  have hdeg_bound : ∀ w : Fin n, (MultiHypergraph.hdeg 𝓗fin w : ℝ) ≤
      (Cfinal.card : ℝ) + (({i : ↥Cprev | w ∉ famVert (Mstar i)} :
        Set ↥Cprev).ncard : ℝ) -
        min ((n : ℝ) - (MultiHypergraph.hdeg 𝓗 w : ℝ)) 3 :=
    s12_deg_h_final (𝓗 := 𝓗) (𝓗fin := 𝓗fin) (Cfin := Cfinal.card) (M := Mstar)
      hbig_ncard hfin_star hcard_star hdisj_star hsingle
  have hVn1iff : ∀ w : Fin n, w ∈ Vn1set 𝓗 ↔ ((n : ℝ) - 1 ≤ (MultiHypergraph.hdeg 𝓗 w : ℝ)) :=
    fun w => mem_Vdeg_pred_iff hlin hbig hm.hn1
  have hVn2iff : ∀ w : Fin n, w ∈ Vn2set 𝓗 ↔ ((n : ℝ) - 2 ≤ (MultiHypergraph.hdeg 𝓗 w : ℝ)) :=
    fun w => mem_Vdeg_plus_iff hlin hbig (by have := hm.hn4; omega)
  have hdg_le : ∀ w : Fin n, (MultiHypergraph.hdeg 𝓗 w : ℝ) ≤ (n : ℝ) - 1 := fun w => by
    have h := hdeg_le_pred hlin hbig w
    have h2 : ((MultiHypergraph.hdeg 𝓗 w : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_sub hm.hn1, Nat.cast_one] at h2
    exact h2
  have hUC23 := s12_uc (ι := ↥Cprev) (M := Mstar) (𝓗 := 𝓗) (𝓗fin := 𝓗fin) (U := U)
    Cfinal (Vn1set 𝓗) (Vn2set 𝓗) hdeg_bound hVn1iff hVn2iff hdg_le hm2a hm2b
  have hUC1 : ∀ w : Fin n, w ∉ U → (MultiHypergraph.hdeg 𝓗fin w : ℝ) ≤
      (Cfinal.card : ℝ) - ρ * ε * (n : ℝ) / 4 := by
    intro w hw
    have hdecomp : ∀ x : Fin n, (MultiHypergraph.hdeg 𝓗fin x : ℝ) ≤
        (degAt R_final x : ℝ) + 2 * (n : ℝ) / (r₀ : ℝ) := by
      intro x
      rw [hdeg_fin x]
      have hx := hCwLarge x
      linarith
    exact s12_uc1 (U := U) (𝓗fin := 𝓗fin) (R_res := R_res) (R_final := R_final) Cfinal
      hRfin_sub hdecomp (fun x hx => hresDeg x hx) hUCnum1 hUCnum2 w ⟨Set.mem_univ w, hw⟩
  have hUC2 := hUC23.1
  have hUC3 := hUC23.2.1
  have hUC4 : ((∀ v : Fin n, v ∈ Vn1set 𝓗 → v ∉ S₁) ∨
      (U.ncard : ℝ) ≤ (1 - 10 * ε) * (n : ℝ)) →
      ∀ w : Fin n, w ∈ Vn1set 𝓗 → (MultiHypergraph.hdeg 𝓗fin w : ℝ) ≤ (Cfinal.card : ℝ) - 1 := by
    intro hdisj
    have hmiss0 : ∀ v ∈ Vn1set 𝓗,
        (({i : ↥Cprev | v ∉ famVert (Mstar i)} : Set ↥Cprev)).ncard = 0 := by
      intro v hv
      rcases hdisj with h1 | h2
      · exact hm1b v ⟨hv, h1 v hv⟩
      · exact (hm3 h2).2 v hv
    exact hUC23.2.2 hmiss0
  -- the number of vertices of smaller degree
  have hu_miss : ∀ i : ↥Cprev, i ∉ ({i : ↥Cprev | (i : Fin n) ∈ Cdiff} : Set ↥Cprev) →
      (U \ famVert (Mstar i)).ncard ≤ 1 := by
    intro i hi
    have hid : (i : Fin n) ∉ Cdiff := hi
    by_cases hcm : (i : Fin n) ∈ Cmain
    · rw [hMstar_m i hcm]
      by_cases hU2 : (1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ)
      · exact (h6₁₁ hU2).2.2 _
      · have hsub : U ⊆ famVert (N ((Cmain.orderIsoOfFin rfl).symm ⟨(i : Fin n), hcm⟩)) :=
          h6₁₀ (not_lt.mp hU2) _
        rw [sdiff_eq_empty_of_subset hsub, Set.ncard_empty]
        omega
    · by_cases hcb : (i : Fin n) ∈ Cbuff
      · rw [hMstar_nm i hcm, prevFam_of_mem_Cbuff hid hcm hcb, famVert_famOf]
        by_cases hU3 : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ)
        · exact (h7₈ hU3).1 (i : Fin n) hcb
        · have hsub : U ⊆ matchVert (Mbuff (i : Fin n)) :=
            h7₇ (not_lt.mp hU3) (i : Fin n) hcb
          rw [sdiff_eq_empty_of_subset hsub, Set.ncard_empty]
          omega
      · rw [hMstar_nm i hcm, prevFam_of_notMem hid hcm hcb, famVert_famOf]
        have hcuh : (i : Fin n) ∈ Chuge ∪ Cmed := by
          have h := mem_med_huge_of_mem_prev (by rw [← hCprevdef]; exact i.2) hid hcm hcb
          rcases Finset.mem_union.mp h with h' | h'
          · exact Finset.mem_union_right Chuge h'
          · exact Finset.mem_union_left Cmed h'
        by_cases hU5 : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ)
        · exact (hstep5.hm_near hU5).1 (i : Fin n) hcuh
        · have hsub : U ⊆ matchVert (Mhm (i : Fin n)) :=
            hstep5.hm_perf (not_lt.mp hU5) (i : Fin n) hcuh
          rw [sdiff_eq_empty_of_subset hsub, Set.ncard_empty]
          omega
  have hcount : (Cfinal.card : ℝ) ≤
      (({v : Fin n | (MultiHypergraph.hdeg 𝓗fin v : ℝ) < (Cfinal.card : ℝ)}) :
        Set (Fin n)).ncard := by
    refine s12_uc3_count (ι := ↥Cprev) (M := Mstar) (U := U) (Vn1 := Vn1set 𝓗)
      (𝓗fin := 𝓗fin) Cfinal (Vn1set_subset_Vn2set 𝓗 |>.trans hVn2U) hcard_star ?_ ?_ ?_ ?_
    · intro i
      by_cases hid : (i : Fin n) ∈ Cdiff
      · have hsub : Vn1set 𝓗 ⊆ famVert (Mstar i) :=
          hdiffVn1 i (by show (i : Fin n) ∈ Cdiff; exact hid)
        rw [sdiff_eq_empty_of_subset hsub, Set.ncard_empty]
        omega
      · refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _))
          (hu_miss i (by simpa using hid))
        intro v hv
        exact ⟨hVn2U (Vn1set_subset_Vn2set 𝓗 hv.1), hv.2⟩
    · intro v hv h0
      have h1 := hdeg_bound v
      rw [h0, Nat.cast_zero, add_zero] at h1
      have h2 : (1 : ℝ) ≤ min ((n : ℝ) - (MultiHypergraph.hdeg 𝓗 v : ℝ)) 3 := by
        refine le_min ?_ (by norm_num)
        have hv' := hdg_le v
        linarith
      linarith
    · intro w hw
      have h1 := hUC1 w hw
      have h2 : 0 < ρ * ε * (n : ℝ) / 4 := by
        nlinarith [hm.hmDeg.hρ0, hm.hmDeg.hε0, hm.hεn, Nat.cast_nonneg (α := ℝ) n]
      linarith
    · intro w hwU hw1
      have h1 := hUC2 w hwU hw1
      linarith
  exact ⟨Mprev, R_final, 𝓗fin, hsup, hext, hmat, hRfin, hRfin2, hRfin_sub, hfin_eq, hdeg_fin,
    hdecomp, hdeficit, hUC1, hUC2, hUC3, hUC4, hcount⟩

end

end ErdosFaberLovaszConjecture
