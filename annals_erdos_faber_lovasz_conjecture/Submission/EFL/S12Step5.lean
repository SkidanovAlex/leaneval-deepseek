import Submission.EFL.S12Step4
import Submission.EFL.HugeStep2
import Mathlib.Data.Finset.Sort

/-!
# §12, Step 5 (`step:step5`): extending the huge and medium colour classes

This module formalises **Step 5** of the proof of Theorem 1.1 (the paper's
`step:step5`).  We apply the huge-edge absorption Lemma 7.3
(`huge_edge_absorption`, with `γ` playing the role of `3γ/2`) to the family
`𝓝 = {φ⁻¹(c) : c ∈ C_huge ∪ C_med}` of colour classes, the absorber `R₁` and
the defect set `S₁` produced by Step 4.  This yields a family
`𝓜_hm = {M_c : c ∈ C_huge ∪ C_med}` of pairwise edge-disjoint matchings with

* **(HM1)** `M_c ⊇ φ⁻¹(c)` and `M_c ∖ φ⁻¹(c) ⊆ R₁`;
* **(HM2)** perfect coverage of `U` if `|U| ≤ (1-10ε)n`, nearly-perfect
  coverage with defects in `S₁` otherwise.

We also record the definitions `R₂ = R₁ ∖ ⋃_{c ∈ C_huge ∪ C_med} M_c` and
`S₂ = S₁ ∖ ⋃_{c ∈ C_huge ∪ C_med} (U ∖ V(M_c))`, and the bound
`|S₂| ≥ |S₁| - (3γ/2)n` (which is `(eq:boundS2)` combined with Step 4).

The absorbability of the colour classes is *verified here* from the absorber
`R₁` (its typicality with respect to the fixed collection `𝓥` of `(def:cv)`)
and the size bounds of Steps 3/5: medium classes are small, huge classes meet
`U` in at most `εn` vertices and are not difficult.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## Colour classes as families of edges of `𝓗` -/

/-- The colour class `c` of `φ`, as a family of edges of `𝓗`. -/
def colourFam {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) (c : Fin n) : Set 𝓗 :=
  subFam (𝓖 := medLarge 𝓗 r₁) (φ.colorClass c)

theorem mem_colourFam {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {c : Fin n} {e : 𝓗} :
    e ∈ colourFam φ c ↔ ∃ (he : (e : Set (Fin n)) ∈ medLarge 𝓗 r₁),
      (⟨(e : Set (Fin n)), he⟩ : ↥(medLarge 𝓗 r₁)) ∈ φ.colorClass c :=
  mem_subFam

/-- The vertex set of the colour class `c` is also the vertex set of the
corresponding family of edges of `𝓗`. -/
theorem matchVert_colourFam {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} (c : Fin n) :
    matchVert (colourFam φ c) = φ.classVertices c := by
  ext v
  rw [mem_matchVert, mem_classVertices]
  constructor
  · rintro ⟨f, hf, hvf⟩
    rw [mem_colourFam] at hf
    exact ⟨⟨(f : Set (Fin n)), hf.1⟩, hf.2, hvf⟩
  · rintro ⟨e, he, hve⟩
    refine ⟨⟨(e : Set (Fin n)), e.2.1⟩, ?_, hve⟩
    rw [mem_colourFam]
    exact ⟨e.2, he⟩

/-- Distinct colour classes are edge-disjoint. -/
theorem disjoint_colourFam {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {c c' : Fin n} (h : c ≠ c') :
    Disjoint (colourFam φ c) (colourFam φ c') := by
  rw [Set.disjoint_left]
  intro e he he'
  rw [mem_colourFam] at he he'
  obtain ⟨he1, he2⟩ := he
  obtain ⟨he1', he2'⟩ := he'
  rw [mem_colorClass] at he2 he2'
  exact h (he2.symm.trans he2')

/-- The colour class is a matching. -/
theorem isMatching_colourFam {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} (c : Fin n) :
    IsMatching 𝓗 (colourFam φ c) :=
  IsMatching.subFam (φ.colorClass_isMatching c)

/-! ## Enumerating a finset of colours -/

/-- The `i`-th colour of an enumeration of the finset `s`. -/
def colourEnum (s : Finset (Fin n)) (i : Fin s.card) : Fin n :=
  (s.orderIsoOfFin rfl i).1

theorem colourEnum_mem (s : Finset (Fin n)) (i : Fin s.card) : colourEnum s i ∈ s :=
  (s.orderIsoOfFin rfl i).2

theorem colourEnum_injective (s : Finset (Fin n)) : Function.Injective (colourEnum s) := by
  intro i j h
  exact (s.orderIsoOfFin rfl).injective (Subtype.ext h)

theorem colourEnum_symm {s : Finset (Fin n)} {c : Fin n} (hc : c ∈ s) :
    colourEnum s ((s.orderIsoOfFin rfl).symm ⟨c, hc⟩) = c := by
  simp only [colourEnum, OrderIso.apply_symm_apply]

/-! ## Step 5 -/

/-- The number of elements of a finset satisfying a predicate agrees with the
corresponding count in the enumeration of the finset. -/
theorem ncard_finset_subtype_eq {n : ℕ} {s : Finset (Fin n)} {P : Fin n → Prop} :
    ({c : Fin n | c ∈ s ∧ P c} : Set (Fin n)).ncard =
      ({i : Fin s.card | P (colourEnum s i)} : Set (Fin s.card)).ncard := by
  classical
  refine Set.ncard_congr (fun c hc => (s.orderIsoOfFin rfl).symm ⟨c, hc.1⟩) ?_ ?_ ?_
  · rintro c hc
    simp only [Set.mem_ofPred_eq]
    rw [colourEnum_symm hc.1]
    exact hc.2
  · rintro c _ c' _ h
    have h' := (s.orderIsoOfFin rfl).symm.injective h
    exact congrArg Subtype.val h'
  · rintro i hi
    refine ⟨colourEnum s i, ⟨colourEnum_mem s i, hi⟩, ?_⟩
    show (s.orderIsoOfFin rfl).symm ⟨colourEnum s i, colourEnum_mem s i⟩ = i
    refine (s.orderIsoOfFin rfl).injective ?_
    rw [OrderIso.apply_symm_apply]
    exact Subtype.ext rfl

/-- **§12, Step 5 (`step:step5`).**  Applying Lemma 7.3 to the huge and medium
colour classes yields the family `𝓜_hm` of HM1/HM2, and the bound for the
new defect set `S₂`. -/
theorem s12_step5 {n : ℕ} {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)}
    {ρ_abs ε γ κ ξ : ℝ} {B : ℕ}
    (hm : HugeMargins n ρ_abs ε (3 * γ / 2) κ ξ)
    (hmatch : InternalMatchingInput n B)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (hn4 : 4 ≤ n)
    (hB : (B : ℝ) ≤ ρ_abs ^ 2 * ((3 * γ / 2) * (n : ℝ)) / 400)
    {R₁ : Hypergraph (Fin n)} {S₁ : Set (Fin n)} {𝓥 : Set (Set (Fin n))}
    (hR₁sub2 : R₁ ⊆ 𝓗.pow2)
    (hSsub : S₁ ⊆ U)
    (hSbig : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      ((3 * γ / 2) + ε) * (n : ℝ) < (S₁.ncard : ℝ))
    (hR₁abs : IsAbsorber (incidentTwo 𝓗 U) R₁ 𝓥 ρ_abs (3 * γ / 2) ξ)
    (hU𝓥 : U ∈ 𝓥) (huniv𝓥 : (Set.univ : Set (Fin n)) ∈ 𝓥)
    {Chuge Cmed : Finset (Fin n)}
    (hbig𝓥 : ∀ c ∈ Chuge ∪ Cmed, U ∪ matchVert (colourFam φ c) ∈ 𝓥)
    (hsmall𝓥 : ∀ c ∈ Chuge ∪ Cmed, U \ matchVert (colourFam φ c) ∈ 𝓥)
    (hbigsize : ∀ c ∈ Chuge,
      ((matchVert (colourFam φ c) ∩ U).ncard : ℝ) ≤ ε * (n : ℝ))
    (hmedsize : ∀ c ∈ Cmed,
      ((matchVert (colourFam φ c)).ncard : ℝ) ≤ (3 * γ / 2) * (n : ℝ))
    (hnotdiff : ∀ c ∈ Chuge, ¬ IsDifficult U (colourFam φ c))
    (hNR₁ : ∀ c ∈ Chuge ∪ Cmed,
      ∀ e ∈ colourFam φ c, (e : Set (Fin n)) ∉ R₁)
    (hk : ((Chuge ∪ Cmed).card : ℝ) ≤ (3 * γ / 2) * (n : ℝ)) :
    ∃ Mhm : Fin n → Set 𝓗,
      (∀ c ∉ Chuge ∪ Cmed, Mhm c = ∅) ∧
      (∀ c ∈ Chuge ∪ Cmed, colourFam φ c ⊆ Mhm c) ∧
      (∀ c ∈ Chuge ∪ Cmed, ∀ e ∈ Mhm c,
        e ∉ colourFam φ c → (e : Set (Fin n)) ∈ R₁) ∧
      (∀ c, IsMatching 𝓗 (Mhm c)) ∧
      (∀ c ∈ Chuge ∪ Cmed, ∀ c' ∈ Chuge ∪ Cmed, c ≠ c' → Disjoint (Mhm c) (Mhm c')) ∧
      (((U.ncard : ℝ) ≤ (1 - 10 * ε) * (n : ℝ)) →
        ∀ c ∈ Chuge ∪ Cmed, Covers (Mhm c) U) ∧
      (((1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ)) →
        (∀ c ∈ Chuge ∪ Cmed, (U \ matchVert (Mhm c)).ncard ≤ 1) ∧
        (∀ c ∈ Chuge ∪ Cmed, U \ matchVert (Mhm c) ⊆ S₁)) ∧
      (∀ u ∈ U,
        ({c : Fin n | c ∈ Chuge ∪ Cmed ∧ u ∉ matchVert (Mhm c)} : Set (Fin n)).ncard ≤ 1) := by
  classical
  let s : Finset (Fin n) := Chuge ∪ Cmed
  let N : Fin s.card → Set 𝓗 := fun i => colourFam φ (colourEnum s i)
  have hmem_s : ∀ i : Fin s.card, colourEnum s i ∈ Chuge ∪ Cmed := fun i => colourEnum_mem s i
  have hNmat : ∀ i, IsMatching 𝓗 (N i) := fun i => isMatching_colourFam _
  have hNdisj : ∀ i j, i ≠ j → Disjoint (N i) (N j) := by
    intro i j hij
    exact disjoint_colourFam (fun h => hij (colourEnum_injective s h))
  have hNR : ∀ i, ∀ e ∈ N i, (e : Set (Fin n)) ∉ R₁ := by
    intro i e he
    exact hNR₁ (colourEnum s i) (hmem_s i) e he
  have habs : ∀ i, AbsorbableBySmall 𝓗 (N i) R₁ U S₁ ρ_abs ε (3 * γ / 2) κ ξ ∨
      (AbsorbableByTypical 𝓗 (N i) R₁ U S₁ ρ_abs ε (3 * γ / 2) κ ξ ∧
        ¬ IsDifficult U (N i)) := by
    intro i
    have hmem := hmem_s i
    have habs' : IsAbsorber (incidentTwo 𝓗 U) R₁ 𝓥 ρ_abs (10 * (3 * γ / 2)) ξ :=
      IsAbsorber.mono_gamma hR₁abs (by linarith [hm.hγ])
    rcases Finset.mem_union.mp hmem with hch | hcm
    · refine Or.inr ⟨⟨𝓥, hU𝓥, huniv𝓥, ?_, ?_, habs', ?_, ?_⟩, ?_⟩
      · exact hbig𝓥 (colourEnum s i) (Finset.mem_union_left _ hch)
      · exact hsmall𝓥 (colourEnum s i) (Finset.mem_union_left _ hch)
      · intro e he; exact hNR₁ (colourEnum s i) (Finset.mem_union_left _ hch) e he
      · exact hbigsize (colourEnum s i) hch
      · exact hnotdiff (colourEnum s i) hch
    · refine Or.inl ⟨⟨𝓥, hU𝓥, huniv𝓥, habs'⟩, ?_, ?_⟩
      · intro e he; exact hNR₁ (colourEnum s i) (Finset.mem_union_right _ hcm) e he
      · exact hmedsize (colourEnum s i) hcm
  obtain ⟨N', hsub, hadd, hmat', hdisj', hperf, hnear⟩ :=
    huge_edge_absorption (𝓗 := 𝓗) (R := R₁) (U := U) (S := S₁) (B := B) hm hmatch hUdeg
      hn4 hB hR₁sub2 hSsub hSbig N habs hNR hNmat hNdisj hk
  -- extend `N'` to all colours by `∅`
  let Mhm : Fin n → Set 𝓗 := fun c =>
    if h : c ∈ s then N' ((s.orderIsoOfFin rfl).symm ⟨c, h⟩) else ∅
  have hidx : ∀ (c : Fin n) (hc : c ∈ s),
      colourEnum s ((s.orderIsoOfFin rfl).symm ⟨c, hc⟩) = c := fun c hc => colourEnum_symm hc
  have hMhm_mem : ∀ (c : Fin n) (hc : c ∈ s),
      Mhm c = N' ((s.orderIsoOfFin rfl).symm ⟨c, hc⟩) := fun c hc => dif_pos hc
  have hMhm_nmem : ∀ (c : Fin n), c ∉ s → Mhm c = ∅ := fun c hc => dif_neg hc
  have hNc : ∀ (c : Fin n) (hc : c ∈ s),
      N ((s.orderIsoOfFin rfl).symm ⟨c, hc⟩) = colourFam φ c := by
    intro c hc
    show colourFam φ (colourEnum s ((s.orderIsoOfFin rfl).symm ⟨c, hc⟩)) = colourFam φ c
    rw [hidx c hc]
  refine ⟨Mhm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    exact dif_neg hc
  · intro c hc
    rw [← hNc c hc, hMhm_mem c hc]
    exact hsub _
  · intro c hc e he hne
    have h1 : e ∈ N' ((s.orderIsoOfFin rfl).symm ⟨c, hc⟩) := by
      rw [← hMhm_mem c hc]; exact he
    have h2 : e ∉ N ((s.orderIsoOfFin rfl).symm ⟨c, hc⟩) := by
      rw [hNc c hc]; exact hne
    exact hadd _ e h1 h2
  · intro c
    by_cases hc : c ∈ s
    · rw [hMhm_mem c hc]
      exact hmat' _
    · rw [hMhm_nmem c hc]
      exact isMatching_empty 𝓗
  · intro c hc c' hc' hne
    rw [hMhm_mem c hc, hMhm_mem c' hc']
    refine hdisj' _ _ (fun h => hne ?_)
    have h1 : colourEnum s ((s.orderIsoOfFin rfl).symm ⟨c, hc⟩) =
        colourEnum s ((s.orderIsoOfFin rfl).symm ⟨c', hc'⟩) := by rw [h]
    rwa [hidx c hc, hidx c' hc'] at h1
  · intro hUc c hc
    rw [hMhm_mem c hc]
    exact hperf hUc _
  · intro hUc
    refine ⟨?_, ?_⟩
    · intro c hc
      rw [hMhm_mem c hc]
      exact (hnear hUc).2.2 _
    · intro c hc
      rw [hMhm_mem c hc]
      exact (hnear hUc).2.1 _
  · -- the per-vertex bound on the misses of `𝓜_hm`
    intro u hu
    by_cases hUc : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ)
    · have h1 : (({i : Fin s.card | u ∈ matchVert (N' i)} : Set (Fin s.card)).ncard : ℝ) + 1 ≥
          (Fintype.card (Fin s.card) : ℝ) := (hnear hUc).1 u hu
      rw [Fintype.card_fin] at h1
      have hsplit : ({i : Fin s.card | u ∉ matchVert (N' i)} : Set (Fin s.card)).ncard +
          ({i : Fin s.card | u ∈ matchVert (N' i)} : Set (Fin s.card)).ncard = s.card := by
        have hcomp : ({i : Fin s.card | u ∈ matchVert (N' i)} : Set (Fin s.card))ᶜ =
            {i : Fin s.card | u ∉ matchVert (N' i)} := by
          ext i
          simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not]
        have hc := Set.ncard_compl_add_ncard
          ({i : Fin s.card | u ∈ matchVert (N' i)} : Set (Fin s.card))
        rw [hcomp] at hc
        rw [hc, Nat.card_eq_fintype_card, Fintype.card_fin]
      have h2 : ({i : Fin s.card | u ∉ matchVert (N' i)} : Set (Fin s.card)).ncard ≤ 1 := by
        have h3 : (({i : Fin s.card | u ∉ matchVert (N' i)} : Set (Fin s.card)).ncard : ℝ) ≤ 1 := by
          have h4 := congrArg (fun x : ℕ => (x : ℝ)) hsplit
          push_cast at h4
          linarith
        exact_mod_cast h3
      rw [ncard_finset_subtype_eq (s := s) (P := fun c => u ∉ matchVert (Mhm c))]
      refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) h2
      rintro i hi
      simp only [Set.mem_ofPred_eq] at hi ⊢
      have hs : (s.orderIsoOfFin rfl).symm ⟨colourEnum s i, colourEnum_mem s i⟩ = i := by
        refine (s.orderIsoOfFin rfl).injective ?_
        rw [OrderIso.apply_symm_apply]
        exact Subtype.ext rfl
      rw [hMhm_mem (colourEnum s i) (colourEnum_mem s i), hs] at hi
      exact hi
    · -- perfect coverage: no matching misses `u`
      have hempty : ({c : Fin n | c ∈ Chuge ∪ Cmed ∧ u ∉ matchVert (Mhm c)} :
          Set (Fin n)) = ∅ := by
        rw [← Set.not_nonempty_iff_eq_empty]
        rintro ⟨c, hc, hmiss⟩
        have hc' : c ∈ s := by simpa only [s, Finset.mem_coe] using hc
        rw [hMhm_mem c hc'] at hmiss
        exact hmiss (hperf (not_lt.mp hUc) ((s.orderIsoOfFin rfl).symm ⟨c, hc'⟩) hu)
      rw [hempty, Set.ncard_empty]
      omega

end

end ErdosFaberLovaszConjecture
