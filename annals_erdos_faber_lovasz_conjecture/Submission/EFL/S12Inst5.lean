import Submission.EFL.S12Step10
import Submission.Commons.Combinatorics.Set.ncard_biUnion_le

/-!
# §12, Step 5, instantiated

The wrapper language of `Submission/EFL/S12Inst5.lean`:
`s12_step5` (the huge/medium absorption step of §12) is applied with the `𝓥` of
`(def:cv)` (`cvFinset φ U`), the parameter `B = 0` (so that the
`InternalMatchingInput` hypothesis is discharged by `internalMatchingInput`),
and the hypotheses of the step derived from the Step-3 colour-set data
(`IsS12Colours`) and the type A singleton hypothesis.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-- `(eqn:size_hm)`: the set `C_huge ∪ C_med` of colours of huge/medium edges has
at most `3γn/2` elements. -/
theorem card_chuge_union_cmed_le {𝓗 : Hypergraph (Fin n)} {r₁ β γ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} {r₀ ρ : ℝ}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (hlin : 𝓗.IsLinear)
    (hS12 : IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal)
    (hk2 : 32 / β ^ 2 ≤ γ * (n : ℝ) / 2)
    (hβ : 0 < β) (hβn : 8 ≤ β * (n : ℝ)) (hn1 : 1 ≤ n)
    (hr₁β : r₁ < β * (n : ℝ) / 4) :
    (((Chuge ∪ Cmed).card : ℕ) : ℝ) ≤ (3 * γ / 2) * (n : ℝ) := by
  classical
  have h1 : (Chuge ∪ Cmed).card ≤ Chuge.card + Cmed.card := Finset.card_union_le _ _
  have h2 : (Chuge.card : ℝ) ≤ 32 / β ^ 2 := by
    have hsub : 𝓗.hugeEdges β ⊆ medLarge 𝓗 r₁ := hugeEdges_subset_medLarge 𝓗 hr₁β
    have h3 : Chuge.card ≤ (φ.hugeColourSet β).card := by
      rw [hS12.hChuge_eq]
      exact Finset.card_le_card (Finset.sdiff_subset)
    have h4 : (φ.hugeColourSet β).card ≤ Nat.card (𝓗.hugeEdges β) :=
      card_hugeColourSet_le 𝓗 hsub φ
    have h5 : (Nat.card (𝓗.hugeEdges β) : ℝ) ≤ 32 / β ^ 2 :=
      natCard_hugeEdges_le hlin hβ hβn hn1
    calc (Chuge.card : ℝ) ≤ ((φ.hugeColourSet β).card : ℝ) := by exact_mod_cast h3
      _ ≤ (Nat.card (𝓗.hugeEdges β) : ℝ) := by exact_mod_cast h4
      _ ≤ 32 / β ^ 2 := h5
  have hcast : (((Chuge ∪ Cmed).card : ℕ) : ℝ) ≤ (Chuge.card : ℝ) + (Cmed.card : ℝ) := by
    exact_mod_cast h1
  have hcm := hS12.hCmed_size
  nlinarith [hk2, h2, hcm, hcast]

/-- **§12, Step 5, instantiated.**  Applying Lemma 7.3 (`huge_edge_absorption`)
to the huge and medium colour classes of `φ` yields the family `𝓜_hm` of
HM1/HM2, with the hypotheses discharged from the Step-3 data. -/
theorem s12_step5_inst {𝓗 : Hypergraph (Fin n)} {r₁ r₀ σ γ₁ β γ ρ ρ_abs ξ ε κ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U S : Set (Fin n)}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (hlin : 𝓗.IsLinear)
    (hS12 : IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal)
    (hsing : φ.SingletonClassesForHuge β)
    (hm : HugeMargins n ρ_abs ε (3 * γ / 2) κ ξ)
    (hU : U = Vplus 𝓗 (1 - ε))
    (hn4 : 4 ≤ n) (hγ0 : 0 ≤ γ) (hε0 : 0 ≤ ε) (hεn : 2 ≤ ε * (n : ℝ))
    (hk2 : 32 / β ^ 2 ≤ γ * (n : ℝ) / 2)
    (hβ : 0 < β) (hβn : 8 ≤ β * (n : ℝ)) (hn1 : 1 ≤ n)
    (hr₁2 : 2 ≤ r₁) (hr₁β : r₁ < β * (n : ℝ) / 4)
    {R₁ : Hypergraph (Fin n)} {S₁ : Set (Fin n)}
    (hR₁sub2 : R₁ ⊆ 𝓗.pow2)
    (hSsub : S₁ ⊆ U)
    (hSbig : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      ((3 * γ / 2) + ε) * (n : ℝ) < (S₁.ncard : ℝ))
    (hR₁abs : IsAbsorber (incidentTwo 𝓗 U) R₁ (cvFinset φ U : Set (Set (Fin n)))
      ρ_abs (3 * γ / 2) ξ) :
    ∃ Mhm : Fin n → Set 𝓗,
      (∀ c ∉ Chuge ∪ Cmed, Mhm c = ∅) ∧
      (∀ c ∈ Chuge ∪ Cmed, colourFam φ c ⊆ Mhm c) ∧
      (∀ c ∈ Chuge ∪ Cmed, ∀ e ∈ Mhm c, e ∉ colourFam φ c → (e : Set (Fin n)) ∈ R₁) ∧
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
  -- the degree hypothesis at `U`
  have hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ) := by
    intro u hu
    rw [degAt_incidentTwo_eq 𝓗 hu]
    rw [hU] at hu
    exact hu
  -- the memberships of `(def:cv)`
  have hU𝓥 : U ∈ (cvFinset φ U : Set (Set (Fin n))) := mem_cvFinset_U
  have huniv𝓥 : (Set.univ : Set (Fin n)) ∈ (cvFinset φ U : Set (Set (Fin n))) :=
    mem_cvFinset_univ
  have hbig𝓥 : ∀ c ∈ Chuge ∪ Cmed,
      U ∪ matchVert (colourFam φ c) ∈ (cvFinset φ U : Set (Set (Fin n))) := by
    intro c _
    rw [matchVert_colourFam c]
    exact mem_cvFinset_union c
  have hsmall𝓥 : ∀ c ∈ Chuge ∪ Cmed,
      U \ matchVert (colourFam φ c) ∈ (cvFinset φ U : Set (Set (Fin n))) := by
    intro c _
    rw [matchVert_colourFam c]
    exact mem_cvFinset_sdiff c
  -- the size hypotheses on the colour classes
  have hbigsize : ∀ c ∈ Chuge,
      ((matchVert (colourFam φ c) ∩ U).ncard : ℝ) ≤ ε * (n : ℝ) := by
    intro c hc
    rw [matchVert_colourFam]
    exact hS12.huge_class_inter_U_le hsing hU hlin hεn hε0 hc
  have hmedsize : ∀ c ∈ Cmed,
      ((matchVert (colourFam φ c)).ncard : ℝ) ≤ (3 * γ / 2) * (n : ℝ) := by
    intro c hc
    rw [matchVert_colourFam]
    have h := hS12.hCmed_vertex c hc
    rw [Hypergraph.Coloring.classVertexCount] at h
    linarith
  -- no huge/medium colour class is difficult
  have hnotdiff : ∀ c ∈ Chuge, ¬ IsDifficult U (colourFam φ c) := by
    intro c hc hdiff
    rw [hS12.hChuge_eq] at hc
    obtain ⟨hcs, hcnot⟩ := Finset.mem_sdiff.mp hc
    have hds : IsDifficultSet U (φ.classVertices c) := by
      rw [← matchVert_colourFam c]
      exact isDifficult_iff_difficultSet.mp hdiff
    exact hcnot (Finset.mem_union_right _
      (hS12.hCdiff_full c hcs (fun h => hcnot (Finset.mem_union_left _ h)) hds))
  -- the colour classes avoid `R₁` (they consist of edges of size `> r₁ ≥ 2`)
  have hNR₁ : ∀ c ∈ Chuge ∪ Cmed, ∀ e ∈ colourFam φ c, (e : Set (Fin n)) ∉ R₁ := by
    intro c _ e he hR1
    have hpow := (mem_pow2.mp (hR₁sub2 hR1)).2
    obtain ⟨hmed, -⟩ := mem_colourFam.mp he
    have hsz := hmed.2
    rw [hpow] at hsz
    norm_num at hsz
    linarith
  -- the cardinality of `C_huge ∪ C_med`
  have hk : (((Chuge ∪ Cmed).card : ℕ) : ℝ) ≤ (3 * γ / 2) * (n : ℝ) :=
    card_chuge_union_cmed_le hlin hS12 hk2 hβ hβn hn1 hr₁β

  -- `B = 0` satisfies the size condition
  have hB : ((0 : ℕ) : ℝ) ≤ ρ_abs ^ 2 * ((3 * γ / 2) * (n : ℝ)) / 400 := by
    have h1 : (0 : ℝ) ≤ ρ_abs ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) ≤ (3 * γ / 2) * (n : ℝ) := by
      have h3 := hm.hγ
      have h4 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
    have h3 : (0 : ℝ) ≤ ρ_abs ^ 2 * ((3 * γ / 2) * (n : ℝ)) := mul_nonneg h1 h2
    linarith
  exact s12_step5 (n := n) (𝓗 := 𝓗) (r₁ := r₁) (φ := φ) (U := U)
    (ρ_abs := ρ_abs) (ε := ε) (γ := γ) (κ := κ) (ξ := ξ) (B := 0)
    (hm := hm) (hmatch := internalMatchingInput n 0) (hUdeg := hUdeg) (hn4 := hn4)
    (hB := hB) (R₁ := R₁) (S₁ := S₁) (𝓥 := (cvFinset φ U : Set (Set (Fin n))))
    (hR₁sub2 := hR₁sub2) (hSsub := hSsub) (hSbig := hSbig) (hR₁abs := hR₁abs)
    (hU𝓥 := hU𝓥) (huniv𝓥 := huniv𝓥) (Chuge := Chuge) (Cmed := Cmed)
    (hbig𝓥 := hbig𝓥) (hsmall𝓥 := hsmall𝓥) (hbigsize := hbigsize) (hmedsize := hmedsize)
    (hnotdiff := hnotdiff) (hNR₁ := hNR₁) (hk := hk)

end

noncomputable section

variable {n : ℕ}

/-! ## The union of a family of matchings has degree at most the number of colours -/

/-- The union of a family of matchings has at most `C.card` edges through any
vertex. -/
theorem hdeg_famUnionFinset_le_card {𝓗 : Hypergraph (Fin n)} {M : Fin n → Set 𝓗}
    {C : Finset (Fin n)} (hmat : ∀ c, IsMatching 𝓗 (M c)) (w : Fin n) :
    MultiHypergraph.hdeg (famUnionFinset M C) w ≤ C.card := by
  classical
  have heq : {e ∈ famUnionFinset M C | w ∈ e} =
      ⋃ c ∈ C, {e ∈ famOf (M c) | w ∈ e} := by
    ext e
    simp only [Set.mem_ofPred_eq, mem_famUnionFinset, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨c, hc, he⟩, hwe⟩
      exact ⟨c, hc, he, hwe⟩
    · rintro ⟨c, hc, he, hwe⟩
      exact ⟨⟨c, hc, he⟩, hwe⟩
  rw [MultiHypergraph.hdeg, heq]
  calc (⋃ c ∈ C, {e ∈ famOf (M c) | w ∈ e}).ncard
      ≤ ∑ c ∈ C, ({e ∈ famOf (M c) | w ∈ e}).ncard :=
        Commons.Combinatorics.Set.ncard_biUnion_le C _ (fun c _ => Set.toFinite _)
    _ ≤ ∑ _c ∈ C, 1 := Finset.sum_le_sum (fun c _ => MultiHypergraph.hdeg_famOf_le_one (hmat c) w)
    _ = C.card := by simp

/-! ## The output of §12 Step 5 -/

/-- **§12 Step 5 (`step:step5`), the output.**  The matchings `𝓜_hm` extending
the huge/medium colour classes (HM1), their coverage property (HM2), and the
truncated absorber `R₂ = R₁ ∖ ⋃𝓜_hm` and defect set
`S₂ = S₁ ∖ ⋃_c (U ∖ V(M_c))` with `(eq:R2abs)` and `(eq:boundS2)`. -/
structure IsS12Step5 {n : ℕ} {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) (U S₁ S₂ : Set (Fin n)) {r₀ β γ ρ ρ_abs ξ ε : ℝ}
    (Chuge Cmed : Finset (Fin n)) (R₁ R₂ : Hypergraph (Fin n)) (Mhm : Fin n → Set 𝓗)
    (𝓥 : Set (Set (Fin n))) : Prop where
  /-- the matchings are supported on `C_huge ∪ C_med`. -/
  hm_supp : ∀ c ∉ Chuge ∪ Cmed, Mhm c = ∅
  /-- `M_c ⊇ φ⁻¹(c)` (HM1). -/
  hm_ext : ∀ c ∈ Chuge ∪ Cmed, colourFam φ c ⊆ Mhm c
  /-- the added edges lie in `R₁` (HM1). -/
  hm_add : ∀ c ∈ Chuge ∪ Cmed, ∀ e ∈ Mhm c, e ∉ colourFam φ c → (e : Set (Fin n)) ∈ R₁
  /-- every `M_c` is a matching. -/
  hm_mat : ∀ c, IsMatching 𝓗 (Mhm c)
  /-- distinct matchings are edge-disjoint. -/
  hm_disj : ∀ c ∈ Chuge ∪ Cmed, ∀ c' ∈ Chuge ∪ Cmed, c ≠ c' → Disjoint (Mhm c) (Mhm c')
  /-- HM2: perfect coverage of `U` when `|U| ≤ (1-10ε)n`. -/
  hm_perf : ((U.ncard : ℝ) ≤ (1 - 10 * ε) * (n : ℝ)) →
    ∀ c ∈ Chuge ∪ Cmed, Covers (Mhm c) U
  /-- HM2: nearly-perfect coverage with defects in `S₁` otherwise. -/
  hm_near : ((1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ)) →
    (∀ c ∈ Chuge ∪ Cmed, (U \ matchVert (Mhm c)).ncard ≤ 1) ∧
    (∀ c ∈ Chuge ∪ Cmed, U \ matchVert (Mhm c) ⊆ S₁)
  /-- the per-vertex bound on the number of `𝓜_hm`-matchings missing a vertex
  of `U`. -/
  hm_miss_vertex : ∀ u ∈ U,
    ({c : Fin n | c ∈ Chuge ∪ Cmed ∧ u ∉ matchVert (Mhm c)} : Set (Fin n)).ncard ≤ 1
  /-- `(def:r2s2)`: `R₂ = R₁ ∖ ⋃𝓜_hm`. -/
  hR₂_eq : R₂ = R₁ \ famUnionFinset Mhm (Chuge ∪ Cmed)
  /-- `(eq:R2abs)`: `R₂` is a `(ρ_abs, 2γ, ξ)`-absorber. -/
  hR₂_abs : IsAbsorber (incidentTwo 𝓗 U) R₂ 𝓥 ρ_abs (2 * γ) ξ
  /-- `(def:r2s2)`: `S₂ = S₁ ∖ ⋃_c (U ∖ V(M_c))`. -/
  hS₂_eq : S₂ = S₁ \ (⋃ c ∈ (Chuge ∪ Cmed : Finset (Fin n)), (U \ matchVert (Mhm c)))
  /-- `S₂ ⊆ S₁`. -/
  hS₂_sub : S₂ ⊆ S₁
  /-- `(eq:boundS2)`. -/
  hS₂_big : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) →
    (Dparam n ρ : ℝ) + 4 * ε * (n : ℝ) ≤ (S₂.ncard : ℝ)

/-- **§12 Step 5, packaged.**  From the Step-4 output (`IsS12Step4`) and the
`(eqn:rs)` lower bound on the defect set `S`, produce the Step-5 output. -/
theorem s12_step5_pack {𝓗 : Hypergraph (Fin n)} {r₁ r₀ σ γ₁ β γ ρ ρ_abs ξ ε κ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U S S₁ : Set (Fin n)}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    {R_abs R₁ : Hypergraph (Fin n)} {Mdiff : Fin n → Set 𝓗}
    (hlin : 𝓗.IsLinear)
    (hS12 : IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal)
    (hsing : φ.SingletonClassesForHuge β)
    (hm : HugeMargins n ρ_abs ε (3 * γ / 2) κ ξ)
    (hU : U = Vplus 𝓗 (1 - ε))
    (hstep4 : IsS12Step4 𝓗 φ U S Cdiff R_abs R₁ S₁ Mdiff (cvFinset φ U : Set (Set (Fin n)))
      ρ_abs γ ξ)
    (hR_abs_pow2 : R_abs ⊆ 𝓗.pow2) (hSsubU : S ⊆ U)
    {ζ : ℝ} (hR₁_small : IsAbsorber (incidentTwo 𝓗 U) R₁ (cvFinset φ U : Set (Set (Fin n)))
      ρ_abs ζ ξ)
    (hξγ2 : ζ + 3 * γ / 2 ≤ 2 * γ)
    (hn4 : 4 ≤ n) (hγ0 : 0 ≤ γ) (hε0 : 0 ≤ ε) (hεn : 2 ≤ ε * (n : ℝ))
    (hk2 : 32 / β ^ 2 ≤ γ * (n : ℝ) / 2)
    (hβ : 0 < β) (hβn : 8 ≤ β * (n : ℝ)) (hn1 : 1 ≤ n)
    (hr₁2 : 2 ≤ r₁) (hr₁β : r₁ < β * (n : ℝ) / 4)
    (hS_big : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      (1 - ρ) * (n : ℝ) + 5 * ε * (n : ℝ) ≤ (S.ncard : ℝ))
    (hS₂num : (Dparam n ρ : ℝ) + 3 * γ * (n : ℝ) / 2 + 5 + 4 * ε * (n : ℝ) ≤
      (1 - ρ) * (n : ℝ) + 5 * ε * (n : ℝ)) :
    ∃ (Mhm : Fin n → Set 𝓗) (R₂ : Hypergraph (Fin n)) (S₂ : Set (Fin n)),
      IsS12Step5 (φ := φ) (U := U) (S₁ := S₁) (S₂ := S₂) (r₀ := r₀) (β := β) (γ := γ)
        (ρ := ρ) (ρ_abs := ρ_abs) (ξ := ξ) (ε := ε) (Chuge := Chuge) (Cmed := Cmed)
        (R₁ := R₁) (R₂ := R₂) (Mhm := Mhm) (𝓥 := (cvFinset φ U : Set (Set (Fin n)))) := by
  classical
  -- the cardinality bound `(eqn:size_hm)`
  have hk : (((Chuge ∪ Cmed).card : ℕ) : ℝ) ≤ (3 * γ / 2) * (n : ℝ) :=
    card_chuge_union_cmed_le hlin hS12 hk2 hβ hβn hn1 hr₁β
  -- `R₁ ⊆ 𝓗.pow2`
  have hR₁sub2 : R₁ ⊆ 𝓗.pow2 := by
    rw [hstep4.hR₁_eq]
    exact Set.sdiff_subset.trans hR_abs_pow2
  -- the `(eqn:rs)` consequence for `S₁`
  have hS₁big : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      ((3 * γ / 2) + ε) * (n : ℝ) < (S₁.ncard : ℝ) := by
    intro hUbig
    have h1 := hS_big hUbig
    have h2 := hstep4.hS₁_big
    have h3 : (0 : ℝ) ≤ (Dparam n ρ : ℝ) := Nat.cast_nonneg _
    have h4 : (3 * ε) * (n : ℝ) ≤ 4 * ε * (n : ℝ) + 3 * γ * (n : ℝ) / 2 := by
      nlinarith [hγ0, Nat.cast_nonneg (α := ℝ) n]
    nlinarith [hS₂num, h1, h2, h3]
  -- the Step-5 absorption
  obtain ⟨Mhm, hm_supp, hm_ext, hm_add, hm_mat, hm_disj, hm_perf, hm_near, hm_miss⟩ :=
    s12_step5_inst (𝓗 := 𝓗) (r₁ := r₁) (r₀ := r₀) (σ := σ) (γ₁ := γ₁) (β := β) (γ := γ)
      (ρ := ρ) (ρ_abs := ρ_abs) (ξ := ξ) (ε := ε) (κ := κ) (φ := φ) (U := U) (S := S)
      (hlin := hlin) (hS12 := hS12) (hsing := hsing) (hm := hm) (hU := hU) (hn4 := hn4)
      (hγ0 := hγ0) (hε0 := hε0) (hεn := hεn) (hk2 := hk2) (hβ := hβ) (hβn := hβn)
      (hn1 := hn1) (hr₁2 := hr₁2) (hr₁β := hr₁β) (hR₁sub2 := hR₁sub2)
      (hSsub := hstep4.hS₁_sub.trans hSsubU) (hSbig := hS₁big) (hR₁abs := hstep4.hR₁_abs)
  set X : Hypergraph (Fin n) := famUnionFinset Mhm (Chuge ∪ Cmed) with hX
  set R₂ : Hypergraph (Fin n) := R₁ \ X with hR₂
  set Y : Set (Fin n) :=
    ⋃ c ∈ (Chuge ∪ Cmed : Finset (Fin n)), (U \ matchVert (Mhm c)) with hY
  set S₂ : Set (Fin n) := S₁ \ Y with hS₂
  refine ⟨Mhm, R₂, S₂, hm_supp, hm_ext, hm_add, hm_mat, hm_disj, hm_perf, hm_near,
    hm_miss, hR₂, ?_, hS₂, Set.sdiff_subset, ?_⟩
  · -- `(eq:R2abs)`
    have hR₂sub : R₂ ⊆ R₁ := Set.sdiff_subset
    have hΔ : ∀ v : Fin n, (degAt (R₁ \ R₂) v : ℝ) ≤ (3 * γ / 2) * (n : ℝ) := by
      intro v
      have hsub : R₁ \ R₂ ⊆ X := by
        intro e he
        rw [Set.mem_sdiff] at he
        by_contra hXe
        exact he.2 (by rw [hR₂, Set.mem_sdiff]; exact ⟨he.1, hXe⟩)
      have h1 : degAt (R₁ \ R₂) v ≤ degAt X v := degAt_mono hsub v
      have h2 : degAt X v ≤ MultiHypergraph.hdeg X v := degAt_le_hdeg _ v
      have h3 : MultiHypergraph.hdeg X v ≤ (Chuge ∪ Cmed).card := by
        rw [hX]; exact hdeg_famUnionFinset_le_card hm_mat v
      have h4 : (degAt (R₁ \ R₂) v : ℝ) ≤ ((Chuge ∪ Cmed).card : ℝ) := by
        exact_mod_cast le_trans (le_trans h1 h2) h3
      linarith
    have hdel := IsAbsorber.delete (α := 3 * γ / 2) hR₁_small hR₂sub hΔ
    exact IsAbsorber.mono_gamma hdel hξγ2
  · -- `(eq:boundS2)`
    intro hUbig
    have hYle : (Y.ncard : ℝ) ≤ ((Chuge ∪ Cmed).card : ℝ) := by
      have h1 : Y.ncard ≤ ∑ c ∈ (Chuge ∪ Cmed), (U \ matchVert (Mhm c)).ncard := by
        rw [hY]
        exact Commons.Combinatorics.Set.ncard_biUnion_le (Chuge ∪ Cmed) _
          (fun c _ => Set.toFinite _)
      have h2 : ∑ c ∈ (Chuge ∪ Cmed), (U \ matchVert (Mhm c)).ncard ≤
          (Chuge ∪ Cmed).card := by
        calc ∑ c ∈ (Chuge ∪ Cmed), (U \ matchVert (Mhm c)).ncard
            ≤ ∑ _c ∈ (Chuge ∪ Cmed), 1 :=
              Finset.sum_le_sum (fun c hc => (hm_near hUbig).1 c hc)
          _ = (Chuge ∪ Cmed).card := by simp
      exact_mod_cast le_trans h1 h2
    have hsplit : S₁ = S₂ ∪ (S₁ ∩ Y) := by
      rw [hS₂]
      ext x
      simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]
      tauto
    have hdisj : Disjoint S₂ (S₁ ∩ Y) := by
      rw [Set.disjoint_left]
      rintro x ⟨-, hxY⟩ ⟨-, hxY'⟩
      exact hxY hxY'
    have hncard : (S₁.ncard : ℝ) ≤ (S₂.ncard : ℝ) + (Y.ncard : ℝ) := by
      have h1 : S₁.ncard = S₂.ncard + (S₁ ∩ Y).ncard := by
        have h1' : S₁.ncard = (S₂ ∪ (S₁ ∩ Y)).ncard := by
          conv_lhs => rw [hsplit]
        rw [h1', Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
      have h2 : ((S₁ ∩ Y).ncard : ℝ) ≤ (Y.ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard Set.inter_subset_right (Set.toFinite _)
      have h3 : (S₁.ncard : ℝ) = (S₂.ncard : ℝ) + ((S₁ ∩ Y).ncard : ℝ) := by
        rw [h1]; push_cast; ring
      linarith
    have h1 := hS_big hUbig
    have h2 := hstep4.hS₁_big
    have h3 : (S₁.ncard : ℝ) ≤ (S₂.ncard : ℝ) + (3 * γ / 2) * (n : ℝ) := by
      linarith [hk]
    linarith

end

end ErdosFaberLovaszConjecture
