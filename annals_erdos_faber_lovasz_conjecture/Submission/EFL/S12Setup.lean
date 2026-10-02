import Submission.EFL.EasyObs
import Submission.EFL.LargeEdgeCase1
import Submission.EFL.Obs12
import Mathlib.Data.Finset.Max

/-!
# §12, Step 3 of the proof of Theorem 1.1: the colour sets

This module formalises **Step 3** of the proof of Theorem 1.1 (the paper's
`step:step3`): from the colouring `φ` of the medium and large edges of `𝓗`
(given by Theorem 6.7, `large-edge-thm`) one defines the colour sets

`C_med, C_diff, C_huge, C_large, C_main, C_buff, C_final`

that partition the colour set `[n]`, together with the `D` and `D'` parameters
`D = ⌊(1-ρ)(n-1)⌋` and `D' = ⌊10γ^{1/2}D⌋`, and proves the observations
`(T1)`, `(T2)` and the size bounds `(eqn:num_huge)`, `(eqn:bound_prev_colours)`:

* `C_med` — at most `γn` colours, all medium edges are coloured inside it;
* `C_diff` — at most one colour, a huge colour whose class is *difficult*;
* `C_huge = φ(𝓗_huge) ∖ (C_med ∪ C_diff)`;
* `C_large = φ(𝓗_large) ∖ (C_med ∪ C_diff ∪ C_huge)`;
* `C_main ⊆ [n] ∖ (C_med ∪ C_diff ∪ C_huge)` of size `D` maximizing
  `|C_large ∩ C_main|`;
* `C_buff ⊆ [n] ∖ (C_med ∪ C_diff ∪ C_huge ∪ C_main)` of size `D'`;
* `C_final = [n] ∖ (C_med ∪ C_diff ∪ C_huge ∪ C_main ∪ C_buff)`.

The two observations are

* **(T1)** if `φ` is of Type A then `φ⁻¹(c) = ∅` for `c ∈ C_buff ∪ C_final`;
* **(T2)** if `φ` is of Type B then `φ⁻¹(c) ⊆ 𝓗_large ∖ 𝓗_huge` for
  `c ∈ C_buff ∪ C_final` (so `|V(φ⁻¹(c))| ≤ βn`).

The remaining pieces of Step 3 (the bounds `(eqn:num_huge)` and
`(eqn:bound_prev_colours)`) are recorded as separate lemmas.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## Huge edges are medium or large -/

/-- A huge edge is an edge of size at least `βn/4`; if `r₁ < βn/4` it is an
edge of `𝓗_med ∪ 𝓗_large`. -/
theorem hugeEdges_subset_medLarge (𝓗 : Hypergraph (Fin n)) {r₁ β : ℝ}
    (h : r₁ < β * (n : ℝ) / 4) : 𝓗.hugeEdges β ⊆ medLarge 𝓗 r₁ := by
  intro e he
  rw [mem_hugeEdges] at he
  exact ⟨he.1, lt_of_lt_of_le h he.2⟩

/-! ## Difficult sets and the colour sets of Step 3 -/

/-- A vertex set is *difficult* (with respect to `U`) if `|Uᶜ| ≥ 2` and it
covers at least `3/4` of `Uᶜ`.  (This is `IsDifficult` applied to
`matchVert M`.) -/
def IsDifficultSet {n : ℕ} (U X : Set (Fin n)) : Prop :=
  2 ≤ (Uᶜ).ncard ∧ 3 * (Uᶜ).ncard ≤ 4 * (X ∩ Uᶜ).ncard

/-- `IsDifficult U M` only depends on the vertices covered by `M`. -/
theorem isDifficult_iff_difficultSet {𝓗 : Hypergraph (Fin n)} {U : Set (Fin n)}
    {M : Set 𝓗} : IsDifficult U M ↔ IsDifficultSet U (matchVert M) := Iff.rfl

/-- `φ(𝓗_huge)`: the set of colours assigned to a huge edge. -/
def Hypergraph.Coloring.hugeColourSet {n : ℕ} {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) (β : ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun c => ∃ e : ↥(medLarge 𝓗 r₁),
    φ.labels e = c ∧ edgeHuge β n (e : Set (Fin n)))

/-- `φ(𝓗_large)`: the set of colours assigned to a large edge. -/
def Hypergraph.Coloring.largeColourSet {n : ℕ} {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) (r₀ : ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun c => ∃ e : ↥(medLarge 𝓗 r₁),
    φ.labels e = c ∧ r₀ < (edgeSize (e : Set (Fin n)) : ℝ))

/-- `C_diff` of Step 3: the huge colours outside `C_med` whose colour class is
difficult. -/
def Hypergraph.Coloring.diffColourSet {n : ℕ} {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) (Cmed : Finset (Fin n)) (U : Set (Fin n))
    (β : ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun c => c ∈ φ.hugeColourSet β ∧ c ∉ Cmed ∧
    IsDifficultSet U (φ.classVertices c))

theorem Hypergraph.Coloring.mem_hugeColourSet {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {β : ℝ} {c : Fin n} :
    c ∈ φ.hugeColourSet β ↔ φ.AssignedToHuge β c := by
  classical
  simp only [Hypergraph.Coloring.hugeColourSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e, hlab, hhuge⟩
    exact ⟨e, by rw [mem_colorClass]; exact hlab, hhuge⟩
  · rintro ⟨e, he, hhuge⟩
    exact ⟨e, by rw [mem_colorClass] at he; exact he, hhuge⟩

theorem Hypergraph.Coloring.mem_largeColourSet {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {r₀ : ℝ} {c : Fin n} :
    c ∈ φ.largeColourSet r₀ ↔ ∃ e : ↥(medLarge 𝓗 r₁),
      φ.labels e = c ∧ r₀ < (edgeSize (e : Set (Fin n)) : ℝ) := by
  classical
  simp only [Hypergraph.Coloring.largeColourSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem Hypergraph.Coloring.mem_diffColourSet {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {Cmed : Finset (Fin n)} {U : Set (Fin n)}
    {β : ℝ} {c : Fin n} :
    c ∈ φ.diffColourSet Cmed U β ↔ c ∈ φ.hugeColourSet β ∧ c ∉ Cmed ∧
      IsDifficultSet U (φ.classVertices c) := by
  classical
  simp only [Hypergraph.Coloring.diffColourSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-! ## Bounding the size of the huge colour set -/

/-- The number of huge colours is at most the number of huge edges: distinct
colours have disjoint (hence distinct) huge edges. -/
theorem card_hugeColourSet_le (𝓗 : Hypergraph (Fin n)) {r₁ β : ℝ}
    (hsub : 𝓗.hugeEdges β ⊆ medLarge 𝓗 r₁)
    (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) :
    (φ.hugeColourSet β).card ≤ Nat.card (𝓗.hugeEdges β) := by
  classical
  have hsub' : ∀ e : ↥(𝓗.hugeEdges β), (e : Set (Fin n)) ∈ medLarge 𝓗 r₁ :=
    fun e => hsub e.2
  have himg : φ.hugeColourSet β ⊆ (Finset.univ : Finset ↥(𝓗.hugeEdges β)).image
      (fun (e : ↥(𝓗.hugeEdges β)) => φ.labels ⟨(e : Set (Fin n)), hsub' e⟩) := by
    intro c hc
    rw [Hypergraph.Coloring.mem_hugeColourSet] at hc
    obtain ⟨e, he, hhuge⟩ := hc
    rw [mem_colorClass] at he
    set e' : ↥(𝓗.hugeEdges β) := ⟨(e : Set (Fin n)), (mem_hugeEdges 𝓗 β _).mpr ⟨e.2.1, hhuge⟩⟩
      with he'
    refine Finset.mem_image.mpr ⟨e', Finset.mem_univ _, ?_⟩
    have hEq : (⟨(e' : Set (Fin n)), hsub' e'⟩ : ↥(medLarge 𝓗 r₁)) = e := Subtype.ext rfl
    rw [hEq, he]
  calc (φ.hugeColourSet β).card
      ≤ ((Finset.univ : Finset ↥(𝓗.hugeEdges β)).image
          (fun (e : ↥(𝓗.hugeEdges β)) => φ.labels ⟨(e : Set (Fin n)), hsub' e⟩)).card :=
        Finset.card_le_card himg
    _ ≤ (Finset.univ : Finset ↥(𝓗.hugeEdges β)).card := Finset.card_image_le
    _ = Nat.card (𝓗.hugeEdges β) := by
        rw [Finset.card_univ, Nat.card_eq_fintype_card]

/-! ## `C_diff` has at most one element -/

/-- **Step 3, `def:cdiff`.**  There is at most one huge colour outside `C_med`
whose colour class is difficult (Claim 12.1 (EP4)). -/
theorem card_diffColourSet_le_one_of_typeA (𝓗 : Hypergraph (Fin n)) (hlin : 𝓗.IsLinear)
    {r₁ σ γ₁ β r₀ : ℝ} (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) (U : Set (Fin n))
    (Cmed : Finset (Fin n)) (hA : IsTypeA σ γ₁ β r₁ r₀ 𝓗 φ) :
    (φ.diffColourSet Cmed U β).card ≤ 1 := by
  classical
  have hEP4 := easyObs_EP4 𝓗 hlin φ U hA
  set T : Finset (Fin n) :=
    Finset.univ.filter (fun c => φ.AssignedToHuge β c ∧ IsDifficultSet U (φ.classVertices c))
    with hT
  have hsub : φ.diffColourSet Cmed U β ⊆ T := by
    intro c hc
    rw [Hypergraph.Coloring.mem_diffColourSet] at hc
    rw [hT]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Hypergraph.Coloring.mem_hugeColourSet.mp hc.1, hc.2.2⟩
  have hset : ((T : Finset (Fin n)) : Set (Fin n)) =
      {c : Fin n | φ.AssignedToHuge β c ∧ IsDifficultSet U (φ.classVertices c)} := by
    rw [hT]
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe, Set.mem_ofPred_eq]
  have hcard : T.card ≤ 1 := by
    rw [← Set.ncard_coe_finset (s := T), hset]
    exact hEP4
  exact le_trans (Finset.card_le_card hsub) hcard

/-- **Step 3, `def:cdiff`, Type B case.**  In the Type B case there is no
difficult colour class at all, so `C_diff = ∅`. -/
theorem card_diffColourSet_le_one_of_typeB (𝓗 : Hypergraph (Fin n)) (hlin : 𝓗.IsLinear)
    {r₁ δ γ₂ γ₁ β r₀ ε : ℝ} (φ : (medLarge 𝓗 r₁).Coloring (Fin n))
    (Cmed : Finset (Fin n))
    (hB : IsTypeB δ γ₂ γ₁ β r₁ r₀ 𝓗 φ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (h3 : 3 ≤ (1 - δ) * Real.sqrt (n : ℝ)) (hδ3 : δ < 3 / 10)
    (hγδ : γ₁ ≤ δ) (hβδ : β ≤ δ) (hn1 : 1 ≤ n) :
    (φ.diffColourSet Cmed (Vplus 𝓗 (1 - ε)) β).card ≤ 1 := by
  classical
  have hnd := (easyObs_EP3 𝓗 hlin φ hB hδ0 hδ1 hε0 hε1 h3 hδ3 hγδ hβδ hn1).2
  have hempty : φ.diffColourSet Cmed (Vplus 𝓗 (1 - ε)) β = ∅ := by
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨c, hc⟩
    rw [Hypergraph.Coloring.mem_diffColourSet] at hc
    exact hnd c hc.2.2
  rw [hempty]
  simp


/-! ## Choosing a subset of prescribed size maximising an intersection -/

/-- Among the subsets of `S` of size `D` there is one maximising `|t ∩ A|`. -/
theorem exists_subset_card_max_inter {α : Type*} [DecidableEq α] (S A : Finset α) {D : ℕ}
    (hD : D ≤ S.card) :
    ∃ t ⊆ S, t.card = D ∧ ∀ t' ⊆ S, t'.card = D → (t' ∩ A).card ≤ (t ∩ A).card := by
  classical
  let T : Finset (Finset α) := S.powerset.filter (fun t => t.card = D)
  have hTne : T.Nonempty := by
    obtain ⟨t, htS, htc⟩ := Finset.exists_subset_card_eq hD
    exact ⟨t, by
      simp only [T, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨htS, htc⟩⟩
  obtain ⟨t, htT, hmax⟩ := Finset.exists_max_image T (fun t => (t ∩ A).card) hTne
  refine ⟨t, ?_, ?_, ?_⟩
  · exact Finset.mem_powerset.mp (Finset.mem_filter.mp htT).1
  · exact (Finset.mem_filter.mp htT).2
  · intro t' ht' hc'
    exact hmax t' (by
      simp only [T, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨ht', hc'⟩)

/-- If `A ⊆ S`, `|A| ≤ D`, and `t` maximises `|t' ∩ A|` among the `D`-element
subsets `t'` of `S`, then `A ⊆ t`. -/
theorem subset_of_subset_card_max_inter {α : Type*} [DecidableEq α] {S A t : Finset α} {D : ℕ}
    (hmax : ∀ t' ⊆ S, t'.card = D → (t' ∩ A).card ≤ (t ∩ A).card)
    (hAS : A ⊆ S) (hAD : A.card ≤ D) (hDS : D ≤ S.card) : A ⊆ t := by
  classical
  have hSDA : D - A.card ≤ (S \ A).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAS]
    omega
  obtain ⟨u, huS, huc⟩ := Finset.exists_subset_card_eq hSDA
  have huA : Disjoint A u := by
    rw [Finset.disjoint_left]
    intro x hxA hxu
    exact (Finset.mem_sdiff.mp (huS hxu)).2 hxA
  set t₁ := A ∪ u with ht₁
  have ht₁S : t₁ ⊆ S := by
    intro x hx
    rw [ht₁, Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact hAS hx
    · exact (Finset.mem_sdiff.mp (huS hx)).1
  have ht₁card : t₁.card = D := by
    rw [ht₁, Finset.card_union_of_disjoint huA, huc]
    omega
  have hkey := hmax t₁ ht₁S ht₁card
  have h1 : (t₁ ∩ A).card = A.card := by
    have h : t₁ ∩ A = A := by
      ext x
      simp only [ht₁, Finset.mem_inter, Finset.mem_union]
      tauto
    rw [h]
  have h2 : A.card ≤ (t ∩ A).card := by rw [← h1]; exact hkey
  have h3 : t ∩ A = A :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right h2
  intro x hx
  have hx' : x ∈ t ∩ A := by rw [h3]; exact hx
  exact (Finset.mem_inter.mp hx').1

/-! ## The `D` and `D'` parameters of Step 3 -/

/-- `D = ⌊(1-ρ)(n-1)⌋` (Step 3, `def:dd'`). -/
def Dparam (n : ℕ) (ρ : ℝ) : ℕ := ⌊(1 - ρ) * ((n : ℝ) - 1)⌋₊

/-- `D' = ⌊10γ^{1/2} D⌋` (Step 3, `def:dd'`). -/
def D'param (D : ℕ) (γ : ℝ) : ℕ := ⌊10 * Real.sqrt γ * (D : ℝ)⌋₊

/-- The union `C_med ∪ C_diff ∪ C_huge` has at most `|C_med| + e(𝓗_huge)`
elements. -/
theorem card_med_diff_huge_le {𝓗 : Hypergraph (Fin n)} {r₁ β : ℝ}
    (hsub : 𝓗.hugeEdges β ⊆ medLarge 𝓗 r₁)
    (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) {Cmed Cdiff Chuge : Finset (Fin n)}
    (hCdiff : Cdiff ⊆ φ.hugeColourSet β) (hChuge : Chuge ⊆ φ.hugeColourSet β) :
    (Cmed ∪ Cdiff ∪ Chuge).card ≤ Cmed.card + Nat.card (𝓗.hugeEdges β) := by
  classical
  have h1 : (Cmed ∪ Cdiff ∪ Chuge).card ≤ Cmed.card + (Cdiff ∪ Chuge).card := by
    rw [Finset.union_assoc]
    exact Finset.card_union_le _ _
  have h2 : (Cdiff ∪ Chuge).card ≤ (φ.hugeColourSet β).card := by
    refine Finset.card_le_card ?_
    intro c hc
    rw [Finset.mem_union] at hc
    exact hc.elim (fun h => hCdiff h) (fun h => hChuge h)
  have h3 : (φ.hugeColourSet β).card ≤ Nat.card (𝓗.hugeEdges β) :=
    card_hugeColourSet_le 𝓗 hsub φ
  omega


/-! ## The Step-3 colour-set package -/

/-- **§12, Step 3.**  The properties of the colour sets `C_med`, `C_diff`,
`C_huge`, `C_large`, `C_main`, `C_buff`, `C_final` of the final assembly. -/
structure IsS12Colours (n : ℕ) (𝓗 : Hypergraph (Fin n)) (r₁ : ℝ)
    (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) (U : Set (Fin n)) (r₀ β γ ρ : ℝ)
    (Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)) : Prop where
  hCmed_size : (Cmed.card : ℝ) ≤ γ * (n : ℝ)
  hCmed_med : ∀ e : ↥(medLarge 𝓗 r₁), edgeMedium r₁ r₀ (e : Set (Fin n)) → φ.labels e ∈ Cmed
  hCmed_vertex : ∀ c ∈ Cmed, (φ.classVertexCount c : ℝ) ≤ γ * (n : ℝ)
  hCdiff_sub : Cdiff ⊆ φ.hugeColourSet β
  hCdiff_med : Disjoint Cdiff Cmed
  hCdiff_card : Cdiff.card ≤ 1
  hCdiff_diff : ∀ c ∈ Cdiff, IsDifficultSet U (φ.classVertices c)
  hCdiff_full : ∀ c ∈ φ.hugeColourSet β, c ∉ Cmed →
    IsDifficultSet U (φ.classVertices c) → c ∈ Cdiff
  hChuge_eq : Chuge = φ.hugeColourSet β \ (Cmed ∪ Cdiff)
  hClarge_eq : Clarge = φ.largeColourSet r₀ \ (Cmed ∪ Cdiff ∪ Chuge)
  hCmain_card : Cmain.card = Dparam n ρ
  hCmain_sub : Cmain ⊆ (Cmed ∪ Cdiff ∪ Chuge)ᶜ
  hCmain_max : ∀ t ⊆ (Cmed ∪ Cdiff ∪ Chuge)ᶜ, t.card = Dparam n ρ →
    (t ∩ Clarge).card ≤ (Cmain ∩ Clarge).card
  hCbuff_card : Cbuff.card = D'param (Dparam n ρ) γ
  hCbuff_sub : Cbuff ⊆ (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain)ᶜ
  hCfinal_eq : Cfinal = (Finset.univ : Finset (Fin n)) \
    (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff)

/-- The core construction of Step 3: from the colour set `C_med` of the
medium edges, the bound on `C_diff` and the numerical hypotheses, build the
remaining colour sets. -/
theorem exists_S12Colours_of_data (𝓗 : Hypergraph (Fin n)) (hlin : 𝓗.IsLinear)
    {r₁ β γ ρ r₀ : ℝ} (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) (U : Set (Fin n))
    (Cmed : Finset (Fin n))
    (hCmed_size : (Cmed.card : ℝ) ≤ γ * (n : ℝ))
    (hCmed_med : ∀ e : ↥(medLarge 𝓗 r₁), edgeMedium r₁ r₀ (e : Set (Fin n)) → φ.labels e ∈ Cmed)
    (hCmed_vertex : ∀ c ∈ Cmed, (φ.classVertexCount c : ℝ) ≤ γ * (n : ℝ))
    (hdiff : (φ.diffColourSet Cmed U β).card ≤ 1)
    (hr1 : 𝓗.hugeEdges β ⊆ medLarge 𝓗 r₁)
    (hβ0 : 0 < β) (hβn : 8 ≤ β * (n : ℝ)) (hn1 : 1 ≤ n)
    (hnum : (Dparam n ρ : ℝ) + (D'param (Dparam n ρ) γ : ℝ) +
        (2 * γ * (n : ℝ) + 32 / β ^ 2) ≤ (n : ℝ)) :
    ∃ Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n),
      IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal := by
  classical
  set Cdiff := φ.diffColourSet Cmed U β with hCdiff
  set Chuge := φ.hugeColourSet β \ (Cmed ∪ Cdiff) with hChuge
  set Clarge := φ.largeColourSet r₀ \ (Cmed ∪ Cdiff ∪ Chuge) with hClarge
  have hCdiff_sub : Cdiff ⊆ φ.hugeColourSet β := by
    intro c hc; rw [Hypergraph.Coloring.mem_diffColourSet] at hc; exact hc.1
  have hChuge_sub : Chuge ⊆ φ.hugeColourSet β := by
    intro c hc; rw [hChuge, Finset.mem_sdiff] at hc; exact hc.1
  have hcard3 := card_med_diff_huge_le (Cmed := Cmed) hr1 φ hCdiff_sub hChuge_sub
  have hhuge32 := natCard_hugeEdges_le hlin hβ0 hβn hn1
  have h3R : ((Cmed ∪ Cdiff ∪ Chuge).card : ℝ) ≤ γ * (n : ℝ) + 32 / β ^ 2 := by
    have h2 : ((Cmed ∪ Cdiff ∪ Chuge).card : ℝ) ≤
        (Cmed.card : ℝ) + (Nat.card (𝓗.hugeEdges β) : ℝ) := by exact_mod_cast hcard3
    linarith
  have hDle : Dparam n ρ ≤ ((Cmed ∪ Cdiff ∪ Chuge)ᶜ : Finset (Fin n)).card := by
    have hR : (Dparam n ρ : ℝ) + ((Cmed ∪ Cdiff ∪ Chuge).card : ℝ) ≤ (n : ℝ) := by
      linarith [hnum, h3R]
    have hnat : Dparam n ρ + (Cmed ∪ Cdiff ∪ Chuge).card ≤ n := by exact_mod_cast hR
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨Cmain, hCmain_sub, hCmain_card, hCmain_max⟩ :=
    exists_subset_card_max_inter _ Clarge hDle
  have hD'le : D'param (Dparam n ρ) γ ≤
      ((Cmed ∪ Cdiff ∪ Chuge ∪ Cmain)ᶜ : Finset (Fin n)).card := by
    have hdisj : Disjoint (Cmed ∪ Cdiff ∪ Chuge) Cmain := by
      rw [Finset.disjoint_left]
      intro x hx hxc
      exact (Finset.mem_compl.mp (hCmain_sub hxc)) hx
    have hcard4 : (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain).card =
        (Cmed ∪ Cdiff ∪ Chuge).card + Cmain.card :=
      Finset.card_union_of_disjoint hdisj
    have hR : (D'param (Dparam n ρ) γ : ℝ) +
        ((Cmed ∪ Cdiff ∪ Chuge ∪ Cmain).card : ℝ) ≤ (n : ℝ) := by
      rw [hcard4, hCmain_card]
      push_cast
      linarith [hnum, h3R]
    have hnat : D'param (Dparam n ρ) γ + (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain).card ≤ n := by
      exact_mod_cast hR
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨Cbuff, hCbuff_sub, hCbuff_card⟩ := Finset.exists_subset_card_eq hD'le
  refine ⟨Cdiff, Chuge, Clarge, Cmain, Cbuff,
    (Finset.univ : Finset (Fin n)) \ (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff), ?_⟩
  exact
    { hCmed_size := hCmed_size
      hCmed_med := hCmed_med
      hCmed_vertex := hCmed_vertex
      hCdiff_sub := hCdiff_sub
      hCdiff_med := by
        rw [Finset.disjoint_left]
        intro c hc hcm
        rw [Hypergraph.Coloring.mem_diffColourSet] at hc
        exact hc.2.1 hcm
      hCdiff_card := hdiff
      hCdiff_diff := by
        intro c hc
        rw [Hypergraph.Coloring.mem_diffColourSet] at hc
        exact hc.2.2
      hCdiff_full := by
        intro c hc hcm hd
        rw [hCdiff, Hypergraph.Coloring.mem_diffColourSet]
        exact ⟨hc, hcm, hd⟩
      hChuge_eq := hChuge
      hClarge_eq := hClarge
      hCmain_card := hCmain_card
      hCmain_sub := hCmain_sub
      hCmain_max := hCmain_max
      hCbuff_card := hCbuff_card
      hCbuff_sub := hCbuff_sub
      hCfinal_eq := rfl }

/-- **§12, Step 3, Type A case.** -/
theorem exists_S12Colours_typeA (𝓗 : Hypergraph (Fin n)) (hlin : 𝓗.IsLinear)
    {r₁ σ γ₁ β γ ρ r₀ : ℝ} (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) (U : Set (Fin n))
    (hA : IsTypeA σ γ₁ β r₁ r₀ 𝓗 φ)
    (hγ : γ₁ ≤ γ)
    (hβ0 : 0 < β) (hβn : 8 ≤ β * (n : ℝ)) (hn1 : 1 ≤ n)
    (hr1 : r₁ < β * (n : ℝ) / 4)
    (hnum : (Dparam n ρ : ℝ) + (D'param (Dparam n ρ) γ : ℝ) +
        (2 * γ * (n : ℝ) + 32 / β ^ 2) ≤ (n : ℝ)) :
    ∃ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n),
      IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal ∧
      (∀ c : Fin n, c ∉ Cmed → ¬ φ.AssignedToHuge β c →
        (φ.classVertexCount c : ℝ) ≤ β * (n : ℝ)) ∧
      (((Cmed ∪ Cdiff ∪ Chuge).card : ℝ) ≤ γ * (n : ℝ) + 32 / β ^ 2) ∧
      ((1 - σ) * (n : ℝ) ≤ (Dparam n ρ : ℝ) → Clarge.card ≤ Dparam n ρ) := by
  classical
  have hA' := hA
  obtain ⟨C₁, Cmed, huse, hC₁, hCmedC₁, hCmedsz, hmed, hCmedvert, hsing, hlast⟩ := hA
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hCmedγ : (Cmed.card : ℝ) ≤ γ * (n : ℝ) := by
    have h1 : γ₁ * (n : ℝ) ≤ γ * (n : ℝ) := mul_le_mul_of_nonneg_right hγ hn0
    linarith
  have hvertex : ∀ c ∈ Cmed, (φ.classVertexCount c : ℝ) ≤ γ * (n : ℝ) := fun c hc =>
    le_trans (hCmedvert c hc) (by have := mul_le_mul_of_nonneg_right hγ hn0; linarith)
  have hdiff : (φ.diffColourSet Cmed U β).card ≤ 1 :=
    card_diffColourSet_le_one_of_typeA 𝓗 hlin φ U Cmed hA'
  obtain ⟨Cdiff, Chuge, Clarge, Cmain, Cbuff, Cfinal, hprops⟩ :=
    exists_S12Colours_of_data 𝓗 hlin φ U Cmed hCmedγ hmed hvertex hdiff
      (hugeEdges_subset_medLarge 𝓗 hr1) hβ0 hβn hn1 hnum
  have h3R : ((Cmed ∪ Cdiff ∪ Chuge).card : ℝ) ≤ γ * (n : ℝ) + 32 / β ^ 2 := by
    have hCdiff_sub : Cdiff ⊆ φ.hugeColourSet β := hprops.hCdiff_sub
    have hChuge_sub : Chuge ⊆ φ.hugeColourSet β := by
      intro c hc
      rw [hprops.hChuge_eq, Finset.mem_sdiff] at hc
      exact hc.1
    have hcard3 := card_med_diff_huge_le (𝓗 := 𝓗) (r₁ := r₁)
      (hugeEdges_subset_medLarge 𝓗 hr1) φ (Cmed := Cmed) hCdiff_sub hChuge_sub
    have hhuge32 := natCard_hugeEdges_le hlin hβ0 hβn hn1
    have h1 : ((Cmed ∪ Cdiff ∪ Chuge).card : ℝ) ≤
        (Cmed.card : ℝ) + (Nat.card (𝓗.hugeEdges β) : ℝ) := by exact_mod_cast hcard3
    linarith [h1, hcard3, hhuge32, hCmedγ]
  have hCl : (1 - σ) * (n : ℝ) ≤ (Dparam n ρ : ℝ) → Clarge.card ≤ Dparam n ρ := by
    intro hDlb
    have hsub : Clarge ⊆ C₁ := by
      intro c hc
      rw [hprops.hClarge_eq, Finset.mem_sdiff] at hc
      obtain ⟨h1, -⟩ := hc
      rw [Hypergraph.Coloring.mem_largeColourSet] at h1
      obtain ⟨e, he, -⟩ := h1
      rw [← he]
      exact huse e
    have h1 : (Clarge.card : ℝ) ≤ ((1 - σ) * (n : ℝ)) := by
      have h2 : Clarge.card ≤ C₁.card := Finset.card_le_card hsub
      have h3 : (Clarge.card : ℝ) ≤ (C₁.card : ℝ) := by exact_mod_cast h2
      linarith [h3, hC₁]
    have h4 : (Clarge.card : ℝ) ≤ (Dparam n ρ : ℝ) := le_trans h1 hDlb
    exact_mod_cast h4
  exact ⟨Cmed, Cdiff, Chuge, Clarge, Cmain, Cbuff, Cfinal, hprops, hlast, h3R, hCl⟩

/-- **§12, Step 3, Type B case.** -/
theorem exists_S12Colours_typeB (𝓗 : Hypergraph (Fin n)) (hlin : 𝓗.IsLinear)
    {r₁ δ γ₂ γ₁ β γ ρ r₀ ε : ℝ} (φ : (medLarge 𝓗 r₁).Coloring (Fin n))
    (hB : IsTypeB δ γ₂ γ₁ β r₁ r₀ 𝓗 φ)
    (hγ₂ : γ₂ ≤ γ) (hγ₁ : γ₁ ≤ γ)
    (hβ0 : 0 < β) (hβn : 8 ≤ β * (n : ℝ)) (hn1 : 1 ≤ n)
    (hr1 : r₁ < β * (n : ℝ) / 4)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (h3 : 3 ≤ (1 - δ) * Real.sqrt (n : ℝ)) (hδ3 : δ < 3 / 10)
    (hγδ : γ₁ ≤ δ) (hβδ : β ≤ δ)
    (hnum : (Dparam n ρ : ℝ) + (D'param (Dparam n ρ) γ : ℝ) +
        (2 * γ * (n : ℝ) + 32 / β ^ 2) ≤ (n : ℝ)) :
    ∃ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n),
      IsS12Colours n 𝓗 r₁ φ (Vplus 𝓗 (1 - ε)) r₀ β γ ρ
        Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal ∧
      (∀ c : Fin n, c ∉ Cmed → ¬ φ.AssignedToHuge β c →
        (φ.classVertexCount c : ℝ) ≤ β * (n : ℝ)) := by
  classical
  have hB' := hB
  obtain ⟨hW, Cmed, hCmedsz, hmed, hCmedvert, hassigned, hlast⟩ := hB
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hCmedγ : (Cmed.card : ℝ) ≤ γ * (n : ℝ) := by
    have h1 : γ₂ * (n : ℝ) ≤ γ * (n : ℝ) := mul_le_mul_of_nonneg_right hγ₂ hn0
    linarith
  have hvertex : ∀ c ∈ Cmed, (φ.classVertexCount c : ℝ) ≤ γ * (n : ℝ) := fun c hc =>
    le_trans (hCmedvert c hc) (by have := mul_le_mul_of_nonneg_right hγ₁ hn0; linarith)
  have hdiff : (φ.diffColourSet Cmed (Vplus 𝓗 (1 - ε)) β).card ≤ 1 :=
    card_diffColourSet_le_one_of_typeB 𝓗 hlin φ Cmed hB' hδ0 hδ1 hε0 hε1 h3 hδ3 hγδ hβδ hn1
  obtain ⟨Cdiff, Chuge, Clarge, Cmain, Cbuff, Cfinal, hprops⟩ :=
    exists_S12Colours_of_data 𝓗 hlin φ (Vplus 𝓗 (1 - ε)) Cmed hCmedγ hmed hvertex hdiff
      (hugeEdges_subset_medLarge 𝓗 hr1) hβ0 hβn hn1 hnum
  exact ⟨Cmed, Cdiff, Chuge, Clarge, Cmain, Cbuff, Cfinal, hprops, hlast⟩


/-! ## Derived consequences of Step 3 -/

/-- Every colour used by a medium or large edge lies in
`C_med ∪ C_diff ∪ C_huge ∪ C_large`. -/
theorem IsS12Colours.labels_mem {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} {r₀ β γ ρ : ℝ}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (h : IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal)
    (e : ↥(medLarge 𝓗 r₁)) :
    φ.labels e ∈ Cmed ∪ Cdiff ∪ Chuge ∪ Clarge := by
  by_cases hmed : edgeMedium r₁ r₀ (e : Set (Fin n))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (h.hCmed_med e hmed)))
  · have hle : ¬ (edgeSize (e : Set (Fin n)) : ℝ) ≤ r₀ := fun hle => hmed ⟨e.2.2, hle⟩
    have hlarge : r₀ < (edgeSize (e : Set (Fin n)) : ℝ) := lt_of_not_ge hle
    have hm : φ.labels e ∈ φ.largeColourSet r₀ :=
      Hypergraph.Coloring.mem_largeColourSet.mpr ⟨e, rfl, hlarge⟩
    by_cases hin : φ.labels e ∈ Cmed ∪ Cdiff ∪ Chuge
    · rcases Finset.mem_union.mp hin with h1 | h1
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h1)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h1)
    · exact Finset.mem_union_right _
        (by rw [h.hClarge_eq]; exact Finset.mem_sdiff.mpr ⟨hm, hin⟩)

/-- If `|C_large| ≤ D` then `C_large ⊆ C_main` (maximality of `C_main`). -/
theorem IsS12Colours.clarge_subset_cmain {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} {r₀ β γ ρ : ℝ}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (h : IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal)
    (hCl : Clarge.card ≤ Dparam n ρ) : Clarge ⊆ Cmain := by
  refine subset_of_subset_card_max_inter h.hCmain_max ?_ hCl ?_
  · intro x hx
    rw [h.hClarge_eq] at hx
    exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hx).2
  · rw [← h.hCmain_card]
    exact Finset.card_le_card h.hCmain_sub

/-- The colours of `C_buff ∪ C_final` avoid `C_med ∪ C_diff ∪ C_huge ∪ C_main`. -/
theorem IsS12Colours.notMem_of_buff_union_final {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} {r₀ β γ ρ : ℝ}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (h : IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal)
    {c : Fin n} (hc : c ∈ Cbuff ∪ Cfinal) :
    c ∉ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain := by
  rcases Finset.mem_union.mp hc with hc | hc
  · exact Finset.mem_compl.mp (h.hCbuff_sub hc)
  · rw [h.hCfinal_eq] at hc
    have h2 := (Finset.mem_sdiff.mp hc).2
    intro h1
    exact h2 (Finset.mem_union_left _ h1)

open Classical in
/-- **(T1)**  If `C_large ⊆ C_main` (which holds in the Type A case), then
every colour of `C_buff ∪ C_final` has empty colour class. -/
theorem IsS12Colours.class_eq_empty_of_buff_union_final {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} {r₀ β γ ρ : ℝ}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (h : IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal)
    (hCl : Clarge.card ≤ Dparam n ρ) :
    ∀ c ∈ Cbuff ∪ Cfinal, φ.colorClass c = ∅ := by
  have hsub := h.clarge_subset_cmain hCl
  intro c hc
  have hnotin := h.notMem_of_buff_union_final hc
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨e, he⟩
  have hlab : φ.labels e = c := he
  have hmem := h.labels_mem e
  rw [hlab] at hmem
  rcases Finset.mem_union.mp hmem with h1 | h1
  · exact hnotin (Finset.mem_union_left _ h1)
  · exact hnotin (Finset.mem_union_right _ (hsub h1))

/-- **(T2)**  Every colour of `C_buff ∪ C_final` is assigned only to large
non-huge edges. -/
theorem IsS12Colours.large_nonhuge_of_buff_union_final {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} {r₀ β γ ρ : ℝ}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (h : IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal)
    {c : Fin n} (hc : c ∈ Cbuff ∪ Cfinal) (e : ↥(medLarge 𝓗 r₁)) (hlab : φ.labels e = c) :
    r₀ < (edgeSize (e : Set (Fin n)) : ℝ) ∧ ¬ edgeHuge β n (e : Set (Fin n)) := by
  have hnotin := h.notMem_of_buff_union_final hc
  have hmed' : ¬ edgeMedium r₁ r₀ (e : Set (Fin n)) := by
    intro hmed
    have hcm : φ.labels e ∈ Cmed := h.hCmed_med e hmed
    rw [hlab] at hcm
    exact hnotin (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ hcm)))
  refine ⟨lt_of_not_ge (fun hle => hmed' ⟨e.2.2, hle⟩), ?_⟩
  intro hhuge
  have hIn : c ∈ φ.hugeColourSet β :=
    Hypergraph.Coloring.mem_hugeColourSet.mpr ⟨e, by rw [mem_colorClass]; exact hlab, hhuge⟩
  have hmem : c ∈ Chuge ∪ (Cmed ∪ Cdiff) := by
    rw [h.hChuge_eq, Finset.mem_union]
    by_cases hcm : c ∈ Cmed ∪ Cdiff
    · exact Or.inr hcm
    · exact Or.inl (Finset.mem_sdiff.mpr ⟨hIn, hcm⟩)
  rcases Finset.mem_union.mp hmem with h1 | h1
  · exact hnotin (Finset.mem_union_left _ (Finset.mem_union_right _ h1))
  · rcases Finset.mem_union.mp h1 with h2 | h2
    · exact hnotin (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ h2)))
    · exact hnotin (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_right _ h2)))

/-- In the Type B case the colour classes of `C_buff ∪ C_final` cover at most
`βn` vertices (T2 and (6.7:b)(iii)). -/
theorem IsS12Colours.classVertexCount_le_of_buff_union_final {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} {r₀ β γ ρ : ℝ}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (h : IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal)
    (hb : ∀ c : Fin n, c ∉ Cmed → ¬ φ.AssignedToHuge β c →
      (φ.classVertexCount c : ℝ) ≤ β * (n : ℝ)) :
    ∀ c ∈ Cbuff ∪ Cfinal, (φ.classVertexCount c : ℝ) ≤ β * (n : ℝ) := by
  intro c hc
  have hnotin := h.notMem_of_buff_union_final hc
  have hcmed : c ∉ Cmed := fun hcm => hnotin (Finset.mem_union_left _
    (Finset.mem_union_left _ (Finset.mem_union_left _ hcm)))
  refine hb c hcmed ?_
  rintro ⟨e, he, hh⟩
  rw [mem_colorClass] at he
  exact (h.large_nonhuge_of_buff_union_final hc e he).2 hh

/-- **(eqn:bound_prev_colours)**  If `|C_med ∪ C_diff ∪ C_huge| ≤ 5√γ·n` then
`|C_final| ≥ (ρ - 15√γ)n`. -/
theorem IsS12Colours.card_final_ge {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} {r₀ β γ ρ : ℝ}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (h : IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal)
    (hX : ((Cmed ∪ Cdiff ∪ Chuge).card : ℝ) ≤ 5 * Real.sqrt γ * (n : ℝ))
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hn1 : 1 ≤ n) :
    (ρ - 15 * Real.sqrt γ) * (n : ℝ) ≤ (Cfinal.card : ℝ) := by
  have hd1 : Disjoint (Cmed ∪ Cdiff ∪ Chuge) Cmain := by
    rw [Finset.disjoint_left]
    intro x hx hxc
    exact (Finset.mem_compl.mp (h.hCmain_sub hxc)) hx
  have hd2 : Disjoint (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain) Cbuff := by
    rw [Finset.disjoint_left]
    intro x hx hxc
    exact (Finset.mem_compl.mp (h.hCbuff_sub hxc)) hx
  have hempty : Cfinal = (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff)ᶜ := by
    rw [h.hCfinal_eq]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_compl]
  have hcardu : (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff).card =
      (Cmed ∪ Cdiff ∪ Chuge).card + Cmain.card + Cbuff.card := by
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  have hk : (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff).card ≤ n := by
    have h1 := Finset.card_le_univ (s := Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff)
    rwa [Fintype.card_fin] at h1
  rw [hempty, Finset.card_compl, Fintype.card_fin, Nat.cast_sub hk, hcardu,
    h.hCmain_card, h.hCbuff_card]
  push_cast
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hD : (Dparam n ρ : ℝ) ≤ (1 - ρ) * (n : ℝ) := by
    rw [Dparam]
    refine le_trans (Nat.floor_le ?_) ?_
    · nlinarith [hρ1, hn1']
    · nlinarith [hρ1, hn1']
  have hDn : (Dparam n ρ : ℝ) ≤ (n : ℝ) := by
    have : (1 - ρ) * (n : ℝ) ≤ (n : ℝ) := by nlinarith [hρ0, hn0]
    linarith [hD, this]
  have hD' : (D'param (Dparam n ρ) γ : ℝ) ≤ 10 * Real.sqrt γ * (n : ℝ) := by
    rw [D'param]
    refine le_trans (Nat.floor_le ?_) ?_
    · have := Real.sqrt_nonneg γ; positivity
    · have := Real.sqrt_nonneg γ
      nlinarith [hDn, this]
  nlinarith [hX, hD, hD', Real.sqrt_nonneg γ]


/-- **Step 5, Type A case.**  If `φ` is of Type A (so huge colour classes are
singletons) and `c ∈ C_huge`, then the colour class of `c` meets
`U = V_+^{(1-ε)}(G)` in at most `εn` vertices (Claim 12.1 (EP1)). -/
theorem IsS12Colours.huge_class_inter_U_le {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} {r₀ β γ ρ ε : ℝ}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (h : IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal)
    (hsing : φ.SingletonClassesForHuge β)
    (hU : U = Vplus 𝓗 (1 - ε)) (hlin : 𝓗.IsLinear)
    (hεn : 2 ≤ ε * (n : ℝ)) (_hε0 : 0 ≤ ε) {c : Fin n} (hc : c ∈ Chuge) :
    ((φ.classVertices c ∩ U).ncard : ℝ) ≤ ε * (n : ℝ) := by
  have hmem : c ∈ φ.hugeColourSet β := by
    rw [h.hChuge_eq] at hc
    exact (Finset.mem_sdiff.mp hc).1
  obtain ⟨e₀, he₀⟩ := hsing c (Hypergraph.Coloring.mem_hugeColourSet.mp hmem)
  have hv : φ.classVertices c = (e₀ : Set (Fin n)) :=
    classVertices_eq_of_colorClass_singleton he₀
  have hsub : (((e₀ : Set (Fin n)) ∩ U).ncard : ℝ) ≤ ((e₀ : Set (Fin n)).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard (Set.inter_subset_left) (Set.toFinite _)
  rw [hv]
  by_cases hmeet : ∃ u ∈ (e₀ : Set (Fin n)), u ∈ U
  · have hmeet' : ∃ u ∈ (e₀ : Set (Fin n)), u ∈ Vplus 𝓗 (1 - ε) := by
      obtain ⟨u, hu, huU⟩ := hmeet
      exact ⟨u, hu, by rwa [← hU]⟩
    have hle := edgeSize_le_of_meets_Vplus 𝓗 hlin hεn (medLarge_subset 𝓗 r₁ e₀.2) hmeet'
    rw [edgeSize_eq_ncard] at hle
    linarith
  · have hzero : (e₀ : Set (Fin n)) ∩ U = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨u, hu, huU⟩
      exact hmeet ⟨u, hu, huU⟩
    rw [hzero, Set.ncard_empty, Nat.cast_zero]
    linarith


end

end ErdosFaberLovaszConjecture
