import Submission.EFL.S12ChainGen
import Submission.EFL.S12BNum
import Submission.EFL.EasyObs
import Submission.EFL.S12Step1Full
import Submission.EFL.S12MainA
import Submission.EFL.NibbleFixed
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-- **The colour-side Hall count.**  For `c ∈ C_final` the number of vertices
`w` with `c ∈ C_w` is exactly the number of vertices covered by the colour
class of `c`. -/
theorem card_filter_finalColoursAt {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {Cfin : Finset (Fin n)} {c : Fin n}
    (hc : c ∈ Cfin) :
    (Finset.univ.filter (fun w => c ∈ finalColoursAt φ Cfin w)).card =
      (matchVert (colourFam φ c)).ncard := by
  have hset : (Finset.univ.filter (fun w => c ∈ finalColoursAt φ Cfin w)) =
      (matchVert (colourFam φ c)).toFinset := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset,
      mem_finalColoursAt]
    exact ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩
  rw [hset]
  exact (Set.ncard_eq_toFinset_card' (matchVert (colourFam φ c))).symm

/-- **`(eqn:bound_prev_colours)` for a Step-3 output.**  `|C_med ∪ C_diff ∪
C_huge| ≤ γn + 32/β²` (the huge colours are those of the huge edges, and there
are at most `32/β²` of them). -/
theorem IsS12Colours.card_med_diff_huge_le_bound {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    {r₁ : ℝ} {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} {r₀ β γ ρ : ℝ}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (h : IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal)
    (hr₁ : r₁ < β * (n : ℝ) / 4) (hβ0 : 0 < β) (hβn : 8 ≤ β * (n : ℝ)) (hn1 : 1 ≤ n) :
    (((Cmed ∪ Cdiff ∪ Chuge).card : ℕ) : ℝ) ≤ γ * (n : ℝ) + 32 / β ^ 2 := by
  have hChuge : Chuge ⊆ φ.hugeColourSet β := by
    intro c hc
    rw [h.hChuge_eq, Finset.mem_sdiff] at hc
    exact hc.1
  have hcard3 := card_med_diff_huge_le (𝓗 := 𝓗) (r₁ := r₁)
    (hugeEdges_subset_medLarge 𝓗 hr₁) φ (Cmed := Cmed) h.hCdiff_sub hChuge
  have hhuge32 := natCard_hugeEdges_le hlin hβ0 hβn hn1
  have h1 : (((Cmed ∪ Cdiff ∪ Chuge).card : ℕ) : ℝ) ≤
      (Cmed.card : ℝ) + (Nat.card (𝓗.hugeEdges β) : ℝ) := by exact_mod_cast hcard3
  linarith [h1, h.hCmed_size, hhuge32]

/-- **§12, the Type B branch.**  For the constants of `S12BNum` (`ρ = ρ_abs =
10⁻⁵`, `ε = 10⁻⁴`, `γ = γ₂ ≤ 10⁻²⁴`, `δ ≤ 10⁻²⁴`), a Type B colouring `φ` of
`𝓗_med ∪ 𝓗_large` and the Type B reservoir of Step 2, the chromatic index of
`𝓗` is at most `n`.  This is the paper's Steps 3--10 in the extremal case. -/
theorem s12_branch_B {𝓗 : Hypergraph (Fin n)} {γ γ₁ β δ ξ : ℝ} {r₁ r₀ : ℕ}
    {φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n)} {R_res : Hypergraph (Fin n)}
    (hNib : NibblePointwise r₁ (2 * β) (2 * γ) (1 / 10 ^ 4) (1 / 10 ^ 5) ξ n)
    (hleft : LeftoverMargins n r₁ γ (1 / 10 ^ 5) (1 / 10 ^ 5) (1 / 10 ^ 4) ξ)
    (hBN : S12BNum n r₁ r₀ β γ δ ξ)
    (hβ0 : 0 < β) (hβγ₁ : β ≤ γ₁) (hγ₁γ : γ₁ ≤ γ) (hγ0 : 0 < γ)
    (hγδ : γ₁ ≤ δ) (hβδ : β ≤ δ) (hδ0 : 0 < δ)
    (hlin : 𝓗.IsLinear) (hbig : ∀ e ∈ 𝓗, 2 ≤ edgeSize e)
    (hB : IsTypeB δ γ γ₁ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 φ)
    (hR : IsReservoirTypeB 𝓗 R_res
      (cvFinset φ (Vplus 𝓗 (1 - 1 / 10 ^ 4)) : Set (Set (Fin n))) (1 / 10 ^ 5) ξ (1 / 10 ^ 4)) :
    𝓗.chromaticIndex ≤ n := by
  classical
  set U : Set (Fin n) := Vplus 𝓗 (1 - 1 / 10 ^ 4) with hUdef
  have hn1 : 1 ≤ n := hBN.hm.hn1
  have hn2 : 2 ≤ n := le_trans (by norm_num) hBN.hm.hn4
  have hε0 : (0 : ℝ) ≤ 1 / 10 ^ 4 := by norm_num
  have hε1 : (1 / 10 ^ 4 : ℝ) ≤ 1 / 2 := by norm_num
  -- ## Step 3
  obtain ⟨Cmed, Cdiff, Chuge, Clarge, Cmain, Cbuff, Cfinal, hS12, hassigned, hVn2U, -, -,
    hlastB⟩ :=
    s12_step3_typeB (n := n) (𝓗 := 𝓗) (r₁ := (r₁ : ℝ)) (r₀ := (r₀ : ℝ)) (δ := δ)
      (γ₂ := γ) (γ₁ := γ₁) (β := β) (γ := γ) (ρ := 1 / 10 ^ 5) (ε := 1 / 10 ^ 4)
      hlin hbig hB le_rfl hγ₁γ hβ0 hBN.hm.hβn hn2 hBN.hm.hr₁β (le_of_lt hδ0) hBN.hδ1
      hε0 hε1 hBN.h3 hBN.hδ3 hγδ hβδ hBN.hεn3 hBN.hnum3
  -- ## Claim 12.1 (EP3): `|U| ≤ 2δn` and no difficult class
  have hEP3 := easyObs_EP3 𝓗 hlin φ hB (le_of_lt hδ0) hBN.hδ1 hε0 hε1 hBN.h3 hBN.hδ3
    hγδ hβδ hn1
  have hU2δ : (U.ncard : ℝ) ≤ 2 * δ * (n : ℝ) := hEP3.1
  have hCdiff_empty : Cdiff = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro c hc
    exact hEP3.2 c (hS12.hCdiff_diff c hc)
  -- ## Step 4 (trivial)
  have hγξ : ξ ≤ 3 * γ / 2 := by linarith only [hBN.hm.hξγ2, hγ0]
  have hξγ2' : ξ + 3 * γ / 2 ≤ 2 * γ := by linarith only [hBN.hm.hξγ2, hBN.hm.hξ0]
  have hstep4 : IsS12Step4 𝓗 φ U U Cdiff R_res R_res U
      (fun _ : Fin n => (∅ : Set 𝓗)) (cvFinset φ U : Set (Set (Fin n))) (1 / 10 ^ 5) γ ξ :=
    isS12Step4_of_Cdiff_empty (𝓥 := (cvFinset φ U : Set (Set (Fin n)))) (R_abs := R_res)
      (S := U) hCdiff_empty hR hγξ
  -- ## the huge/medium class size bounds of Step 5
  have hbigsize : ∀ c ∈ Chuge,
      ((matchVert (colourFam φ c) ∩ U).ncard : ℝ) ≤ (1 / 10 ^ 4) * (n : ℝ) := by
    intro c hc
    rw [matchVert_colourFam]
    have hmem : c ∈ φ.hugeColourSet β := by
      rw [hS12.hChuge_eq] at hc
      exact (Finset.mem_sdiff.mp hc).1
    have h1 := hassigned c (Hypergraph.Coloring.mem_hugeColourSet.mp hmem)
    have h2 : ((φ.classVertices c ∩ U).ncard : ℝ) ≤ (φ.classVertexCount c : ℝ) := by
      rw [Hypergraph.Coloring.classVertexCount]
      exact_mod_cast Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)
    have h3 : δ * (n : ℝ) ≤ (1 / 10 ^ 4) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hBN.hδε (Nat.cast_nonneg _)
    linarith only [h1, h2, h3]
  have hmedsize : ∀ c ∈ Cmed,
      ((matchVert (colourFam φ c)).ncard : ℝ) ≤ (3 * γ / 2) * (n : ℝ) := by
    intro c hc
    rw [matchVert_colourFam]
    have h := hS12.hCmed_vertex c hc
    rw [Hypergraph.Coloring.classVertexCount] at h
    nlinarith only [h, hBN.hm.hγ0, Nat.cast_nonneg (α := ℝ) n]
  -- ## the numeric hypotheses of the chain
  have hγ1' : γ ≤ 1 := by
    have h1 := hBN.hm.hL5
    have hc : (3 : ℝ) * (1 / 10 ^ 4) / 10 < 1 := by norm_num
    have h2 : Real.sqrt γ < 1 := by linarith only [h1, hc]
    have h3 : (Real.sqrt γ) ^ 2 < 1 := pow_lt_one₀ (Real.sqrt_nonneg γ) h2 (by norm_num)
    have h4 : γ = (Real.sqrt γ) ^ 2 := (Real.sq_sqrt (le_of_lt hγ0)).symm
    linarith only [h3, h4]
  have hγs : γ ≤ Real.sqrt γ := by
    nlinarith only [Real.sq_sqrt (le_of_lt hγ0), hγ0, hγ1', Real.sqrt_nonneg γ]
  have h3R : (((Cmed ∪ Cdiff ∪ Chuge).card : ℕ) : ℝ) ≤ γ * (n : ℝ) + 32 / β ^ 2 :=
    hS12.card_med_diff_huge_le_bound hlin hBN.hm.hr₁β hβ0 hBN.hm.hβn hn1
  have hX : (((Cmed ∪ Cdiff ∪ Chuge).card : ℕ) : ℝ) ≤ 5 * Real.sqrt γ * (n : ℝ) := by
    have hk2 := hBN.hm.hk2
    have h6 : 3 * γ * (n : ℝ) ≤ 10 * Real.sqrt γ * (n : ℝ) := by
      nlinarith only [hγs, Real.sqrt_nonneg γ, Nat.cast_nonneg (α := ℝ) n]
    linarith only [h3R, hk2, h6]
  have hUCnum1 : (1 / 10 ^ 5) * (1 - 1 / 10 ^ 4) * (n : ℝ) + ξ * (n : ℝ) ≤
      (Cfinal.card : ℝ) - (1 / 10 ^ 5) * (1 / 10 ^ 4) * (n : ℝ) / 2 := by
    have hcfg := hS12.card_final_ge hX (by norm_num) (by norm_num) hn1
    have h15 := hBN.h15ρ
    have h15' : (15 * Real.sqrt γ + ξ) * (n : ℝ) ≤
        ((1 / 10 ^ 5) * (1 / 10 ^ 4) / 2) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right h15 (Nat.cast_nonneg (α := ℝ) n)
    nlinarith only [hcfg, h15']
  have hUCnum2 : 2 * (n : ℝ) / (r₀ : ℝ) ≤
      (1 / 10 ^ 5) * (1 / 10 ^ 4) * (n : ℝ) / 4 := by
    have h8 := hBN.h8r₀
    have h8' : (2 : ℝ) ≤ (1 / 10 ^ 5) * (1 / 10 ^ 4) * (r₀ : ℝ) / 4 := by
      linarith only [h8]
    have hr0 : (0 : ℝ) < (r₀ : ℝ) := by
      have h2 : 2 ≤ r₀ := hBN.hm.hr₀2
      exact_mod_cast (by omega : 0 < r₀)
    rw [div_le_iff₀ hr0]
    nlinarith only [h8', Nat.cast_nonneg (α := ℝ) n]
  have hDn : (Dparam n (1 / 10 ^ 5) : ℝ) ≤ (n : ℝ) := by
    have h1 := hBN.hnum3
    have h2 : (0 : ℝ) ≤ (D'param (Dparam n (1 / 10 ^ 5)) γ : ℝ) := Nat.cast_nonneg _
    have h3 : (0 : ℝ) ≤ 2 * γ * (n : ℝ) := by positivity
    have h4 : (0 : ℝ) ≤ 32 / β ^ 2 := by positivity
    linarith only [h1, h2, h3, h4]
  have hdeficitNum : (((Cdiff ∪ Chuge ∪ Cmed ∪ Cbuff).card : ℕ) : ℝ) +
      2 * γ * ((Cmain.card : ℕ) : ℝ) ≤ 15 * Real.sqrt γ * (n : ℝ) := by
    have hk2 := hBN.hm.hk2
    have hCbuff : ((Cbuff.card : ℕ) : ℝ) ≤ 10 * Real.sqrt γ * (n : ℝ) := by
      rw [hS12.hCbuff_card]
      have h2 : (D'param (Dparam n (1 / 10 ^ 5)) γ : ℝ) ≤
          10 * Real.sqrt γ * (Dparam n (1 / 10 ^ 5) : ℝ) := by
        rw [D'param]
        exact Nat.floor_le (by positivity)
      have h4 : 10 * Real.sqrt γ * (Dparam n (1 / 10 ^ 5) : ℝ) ≤
          10 * Real.sqrt γ * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hDn (by positivity)
      linarith only [h2, h4]
    have hCmain : ((Cmain.card : ℕ) : ℝ) ≤ (n : ℝ) := by
      rw [hS12.hCmain_card]
      exact hDn
    have hset : (Cdiff ∪ Chuge ∪ Cmed) = (Cmed ∪ Cdiff ∪ Chuge) := by
      ext x; simp only [Finset.mem_union]; tauto
    have h3R' : (((Cdiff ∪ Chuge ∪ Cmed).card : ℕ) : ℝ) ≤ γ * (n : ℝ) + 32 / β ^ 2 := by
      rw [hset]; exact h3R
    have hcard_union : (Cdiff ∪ Chuge ∪ Cmed ∪ Cbuff).card ≤
        (Cdiff ∪ Chuge ∪ Cmed).card + Cbuff.card := Finset.card_union_le _ _
    have h1 : (((Cdiff ∪ Chuge ∪ Cmed ∪ Cbuff).card : ℕ) : ℝ) ≤
        (((Cdiff ∪ Chuge ∪ Cmed).card : ℕ) : ℝ) + ((Cbuff.card : ℕ) : ℝ) := by
      exact_mod_cast hcard_union
    have hfin : γ * (n : ℝ) + 32 / β ^ 2 + 10 * Real.sqrt γ * (n : ℝ) + 2 * γ * (n : ℝ) ≤
        15 * Real.sqrt γ * (n : ℝ) := by
      nlinarith only [hk2, hγs, hγ0, Real.sqrt_nonneg γ, Nat.cast_nonneg (α := ℝ) n]
    have hCmain' : 2 * γ * ((Cmain.card : ℕ) : ℝ) ≤ 2 * γ * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hCmain (by positivity)
    linarith only [h1, h3R', hCbuff, hCmain', hfin]
  have hS_big : (1 - 10 * (1 / 10 ^ 4)) * (n : ℝ) < (U.ncard : ℝ) →
      (1 - 1 / 10 ^ 5) * (n : ℝ) + 5 * (1 / 10 ^ 4) * (n : ℝ) ≤ (U.ncard : ℝ) :=
    S_big_typeB (δ := δ) (ρ := 1 / 10 ^ 5) (ε := 1 / 10 ^ 4) hU2δ hBN.hδ2
  have hCwLarge := card_finalColoursAt_le_of_T2 (𝓗 := 𝓗) hlin hBN.hm.hr₀2 hS12
  -- ## the chain (Steps 5--9)
  obtain ⟨Mprev, R_final, 𝓗fin, hout⟩ :=
    s12_to_S12Out_gen (𝓗 := 𝓗) (r₁ := r₁) (r₀ := r₀) (β := β) (γ := γ) (ρ := 1 / 10 ^ 5)
      (ρ_abs := 1 / 10 ^ 5) (ξ := ξ) (ε := 1 / 10 ^ 4) (κ := 1 / 2) (φ := φ) (U := U)
      (S := U) (S₁ := U) (Cmed := Cmed) (Cdiff := Cdiff) (Chuge := Chuge)
      (Clarge := Clarge) (Cmain := Cmain) (Cbuff := Cbuff) (Cfinal := Cfinal)
      (R_res := R_res) (R_abs := R_res) (R₁ := R_res) (Mdiff := fun _ => ∅)
      hlin hbig hNib hleft hS12 hlastB (Or.inr (Or.inr ⟨hR, hBN.hmargB⟩)) mem_cvFinset_univ
      mem_cvFinset_U rfl hstep4 (fun e he => incidentTwo_subset_pow2 𝓗 U (hR.1 he)) hR hξγ2'
      subset_rfl hS_big hBN.hm subset_rfl hVn2U hbigsize hmedsize hCwLarge hUCnum1 hUCnum2
      hdeficitNum
  -- ## Step 10 (Hall)
  have hdisj : Disjoint (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff) Cfinal := by
    rw [Finset.disjoint_left]
    intro x hx hxc
    rw [hS12.hCfinal_eq, Finset.mem_sdiff] at hxc
    exact hxc.2 hx
  have hRsub : R_final ⊆ 𝓗 := fun e he =>
    (mem_pow2.mp (mem_incidentTwo.mp (hR.1 (hout.hRfin_sub he))).1).1
  have hUle : (U.ncard : ℝ) ≤ (1 - 10 * (1 / 10 ^ 4)) * (n : ℝ) := by
    nlinarith only [hU2δ, hBN.hδ2, Nat.cast_nonneg (α := ℝ) n]
  have hC7 : 7 * (2 * δ) * (n : ℝ) ≤ (Cfinal.card : ℝ) := by
    have h1 := hS12.card_final_ge hX (by norm_num) (by norm_num) hn1
    have h2 : 7 * (2 * δ) ≤ 1 / 10 ^ 5 - 15 * Real.sqrt γ := by linarith only [hBN.hCfin]
    nlinarith only [h1, h2, Nat.cast_nonneg (α := ℝ) n]
  have hUfin : (U.ncard : ℝ) ≤ (2 * δ) * (n : ℝ) := hU2δ
  have hUcov : ∀ e ∈ R_final, ∃ u ∈ e, u ∈ U := fun e he =>
    (mem_incidentTwo.mp (hR.1 (hout.hRfin_sub he))).2
  have hdeg : ∀ w : Fin n, degAt R_final w + (finalColoursAt φ Cfinal w).card ≤
      Cfinal.card - 1 := by
    intro w
    have hfin := hout.hdeg_fin w
    have h3 : (degAt R_final w : ℝ) + ((finalColoursAt φ Cfinal w).card : ℝ) ≤
        (Cfinal.card : ℝ) - 1 := by
      by_cases hwU : w ∈ U
      · by_cases hw1 : w ∈ Vn1set 𝓗
        · have h := hout.hUC4 (Or.inr hUle) w hw1
          linarith only [h, hfin]
        · have h := hout.hUC2 w hwU hw1
          linarith only [h, hfin]
      · have h := hout.hUC1 w hwU
        have hnum : (1 : ℝ) ≤ (1 / 10 ^ 5) * (1 / 10 ^ 4) * (n : ℝ) / 4 := by
          linarith only [hBN.h4ρεn]
        linarith only [h, hfin, hnum]
    have h4 : degAt R_final w + (finalColoursAt φ Cfinal w).card + 1 ≤ Cfinal.card := by
      have h5 : ((degAt R_final w + (finalColoursAt φ Cfinal w).card : ℕ) : ℝ) + 1 ≤
          (Cfinal.card : ℝ) := by
        push_cast
        linarith only [h3]
      exact_mod_cast h5
    omega
  have hCw : ∀ w : Fin n, ((finalColoursAt φ Cfinal w).card : ℝ) ≤ (2 * δ) * (n : ℝ) := by
    intro w
    have h1 := hCwLarge w
    have h2 : 2 * (n : ℝ) / (r₀ : ℝ) ≤ (2 * δ) * (n : ℝ) := by
      have hr0 : (0 : ℝ) < (r₀ : ℝ) := by
        have h2 : 2 ≤ r₀ := hBN.hm.hr₀2
        exact_mod_cast (by omega : 0 < r₀)
      rw [div_le_iff₀ hr0]
      have h3 : (1 : ℝ) ≤ δ * (r₀ : ℝ) := by linarith only [hBN.hδr₀]
      nlinarith only [h3, Nat.cast_nonneg (α := ℝ) n]
    linarith only [h1, h2]
  have hCcol : ∀ c ∈ Cfinal,
      (((Finset.univ : Finset (Fin n)).filter
        (fun w => c ∈ finalColoursAt φ Cfinal w)).card : ℝ) ≤ (2 * δ) * (n : ℝ) := by
    intro c hc
    rw [card_filter_finalColoursAt hc, matchVert_colourFam]
    have hnc : c ∉ Cmed := by
      rw [hS12.hCfinal_eq, Finset.mem_sdiff] at hc
      exact fun h => hc.2 (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ h))))
    have hnh : ¬ φ.AssignedToHuge β c := by
      intro hh
      have hmem : c ∈ φ.hugeColourSet β := Hypergraph.Coloring.mem_hugeColourSet.mpr hh
      have hch : c ∈ Chuge := by
        rw [hS12.hChuge_eq]
        exact Finset.mem_sdiff.mpr ⟨hmem, fun hcon => hnc (by
          rw [hCdiff_empty] at hcon
          simpa using hcon)⟩
      rw [hS12.hCfinal_eq, Finset.mem_sdiff] at hc
      exact hc.2 (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ hch)))
    have h1 := hlastB c hnc hnh
    rw [Hypergraph.Coloring.classVertexCount] at h1
    have h2 : β * (n : ℝ) ≤ (2 * δ) * (n : ℝ) := by
      have h3 : β ≤ 2 * δ := by linarith only [hBN.hβδ2, le_of_lt hδ0]
      exact mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _)
    linarith only [h1, h2]
  have h2δ0 : (0 : ℝ) < 2 * δ := by linarith only [hδ0]
  have h2δ1 : 2 * δ < 1 := by
    have hc : (0 : ℝ) ≤ 10 * (1 / 10 ^ 4) := by norm_num
    linarith only [hBN.hδ2, hc]
  exact s12_finish_B hout hdisj hRsub h2δ0 h2δ1 hC7 hUfin hUcov hdeg hCw hCcol

end

end ErdosFaberLovaszConjecture

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-- **§12, the Type B branch with a threshold.**  For the constant hierarchy of
`s12_step1` there is `N` such that every linear `n`-vertex hypergraph all of
whose edges have at least two vertices, `n ≥ N`, that admits a Type B colouring
of its medium and large edges satisfies `χ'(𝓗) ≤ n`. -/
theorem s12_B_main {σ γ γ₁ β δ : ℝ} {r₁ r₀ : ℕ}
    (hNib : NibbleStatementFixed) (hK : KahnStatement)
    (hβ0 : 0 < β) (hβγ₁ : β ≤ γ₁) (hβsq₁ : β ≤ γ₁ ^ 2 / 16)
    (hβ4₁ : β ≤ γ₁ ^ 4 / 10 ^ 12)
    (hγ₁σ : γ₁ ≤ σ ^ 10 / 10 ^ 250)
    (hσ0 : 0 < σ) (hσ24 : σ ≤ (10 : ℝ) ^ (-24 : ℤ)) (hσδ : σ ≤ δ)
    (hδ0 : 0 < δ) (hδγ : δ ≤ γ) (hγ0 : 0 < γ) (hγ24 : γ ≤ (10 : ℝ) ^ (-30 : ℤ))
    (hr₁2 : 2 ≤ r₁) (hr₀2 : 2 ≤ r₀) (hr₁r₀ : r₁ < r₀)
    (hβr1 : 32 ≤ β * (r₁ : ℝ)) (hr₁β₀ : (r₁ : ℝ) ≤ β * ((r₀ : ℝ) - 1))
    (hr₀big : (r₁ : ℝ) < γ₁ / 4 * ((r₀ : ℝ) - 1)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear →
      (∀ e ∈ 𝓗, 2 ≤ edgeSize e) →
      (∃ φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n),
        IsTypeB δ γ γ₁ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 φ) →
      𝓗.chromaticIndex ≤ n := by
  classical
  have hδ24₀ : δ ≤ (10 : ℝ) ^ (-30 : ℤ) := le_trans hδγ hγ24
  have hc₃₀₂₄ : (10 : ℝ) ^ (-30 : ℤ) ≤ (10 : ℝ) ^ (-24 : ℤ) := by norm_num
  have hδ24 : δ ≤ (10 : ℝ) ^ (-24 : ℤ) := le_trans hδ24₀ hc₃₀₂₄
  have hγ24' : γ ≤ (10 : ℝ) ^ (-24 : ℤ) := le_trans hγ24 hc₃₀₂₄
  have hσ1 : σ ≤ 1 := by have h := hσ24; norm_num at h ⊢; linarith
  -- `β ≪ γ²`: the separation used by the Nibble Lemma
  have hγ₁γ : γ₁ ≤ γ := by
    have h1 : σ ^ 10 / 10 ^ 250 ≤ σ := by
      have hc : (1 : ℝ) ≤ 10 ^ 250 := by norm_num
      have h2 : σ ^ 10 ≤ σ := by
        simpa using pow_le_pow_of_le_one (le_of_lt hσ0) hσ1 (show 1 ≤ 10 by norm_num)
      have h3 : σ ^ 10 / 10 ^ 250 ≤ σ ^ 10 := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 250)]
        nlinarith only [hc, pow_nonneg (le_of_lt hσ0) 10]
      linarith only [h3, h2]
    linarith only [hγ₁σ, h1, hσδ, hδγ]
  have hγ₁0 : 0 < γ₁ := lt_of_lt_of_le hβ0 hβγ₁
  have hβsq : 8 * β ≤ γ ^ 2 := by nlinarith only [hβsq₁, hγ₁γ, hγ₁0, hβ0]
  have hβ4 : β ≤ γ ^ 4 / 10 ^ 12 := by
    have h1 : γ₁ ^ 4 ≤ γ ^ 4 := pow_le_pow_left₀ (le_of_lt hγ₁0) hγ₁γ 4
    linarith only [hβ4₁, h1]
  obtain ⟨ξ, hξ0, N₁, hN₁⟩ :=
    exists_S12BNum (r₁ := r₁) (r₀ := r₀) (β := β) (γ := γ) (δ := δ) (σ := σ) (γ₁ := γ₁)
      hβ0 hβγ₁ hβsq hβ4 hγ₁σ hσ0 hσ24 hσδ hδ0 hδ24 hδγ hγ0 hγ24' hr₁2 hr₀2 hr₁r₀ hβr1 hr₁β₀
      hr₀big
  obtain ⟨N₂, hN₂⟩ :=
    s12_step2_typeB (ρ := 1 / 10 ^ 5) (ξ := ξ) (by norm_num) (by norm_num) hξ0
  obtain ⟨N₃, hN₃⟩ := exists_cvFinset_card_le
  -- ## the numerical margins of the Leftover Lemma
  have hγ30 : γ ≤ 1 / 10 ^ 30 := by
    have hc : (10 : ℝ) ^ (-30 : ℤ) = 1 / 10 ^ 30 := by norm_num
    exact le_trans hγ24 (le_of_eq hc)
  have hξγρ : 4000 * ξ ≤ (3 * γ / 2) * (1 / 10 ^ 5) :=
    (hN₁ (max N₁ 1) (le_max_left _ _)).hm.hmHuge.hξγρ
  obtain ⟨N₄, hN₄⟩ :=
    exists_leftoverMargins_B hK (r₁ := r₁) (γ := γ) (ξ := ξ) hγ0 hγ30 hξ0 hξγρ
  refine ⟨N₁ + N₂ + N₃ + N₄ + nibbleThr r₁ (2 * β) (2 * γ) (1 / 10 ^ 4) (1 / 10 ^ 5) ξ,
    fun n hn 𝓗 hlin hbig ⟨φ, hB⟩ => ?_⟩
  have hThr : nibbleThr r₁ (2 * β) (2 * γ) (1 / 10 ^ 4) (1 / 10 ^ 5) ξ ≤ n := by omega
  have hn₁ : N₁ ≤ n := by omega
  have hn₂ : N₂ ≤ n := by omega
  have hn₃ : N₃ ≤ n := by omega
  have hn₄ : N₄ ≤ n := by omega
  have hBN := hN₁ n hn₁
  have hVcard := hN₃ n hn₃ φ (Vplus 𝓗 (1 - 1 / 10 ^ 4))
  obtain ⟨R_res, -, hR, -, -, -⟩ :=
    hN₂ n hn₂ 𝓗 hlin φ (Vplus 𝓗 (1 - 1 / 10 ^ 4)) rfl hBN.hm.hn1 hVcard
  have hγ₁δ : γ₁ ≤ δ := by
    have h1 : γ₁ ≤ σ := by
      refine le_trans hγ₁σ ?_
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 250)]
      have hc : (1 : ℝ) ≤ 10 ^ 250 := by norm_num
      have h2 : σ ^ 10 ≤ σ := by
        have h := pow_le_pow_of_le_one (le_of_lt hσ0) hσ1 (show 1 ≤ 10 by norm_num)
        simpa using h
      nlinarith only [h2, hc, hσ0]
    linarith only [h1, hσδ]
  have hβδ : β ≤ δ := le_trans hβγ₁ hγ₁δ
  have hγ₁γ : γ₁ ≤ γ := le_trans hγ₁δ hδγ
  -- ## the Nibble Lemma, pointwise at the constants of this branch
  have hγ1 : γ ≤ 1 := le_trans hγ24 (by norm_num)
  have hβ1 : β ≤ 1 := le_trans hβγ₁ (le_trans hγ₁γ hγ1)
  have hr32 : (32 : ℝ) ≤ (r₁ : ℝ) := by
    have hle : β * (r₁ : ℝ) ≤ (r₁ : ℝ) := by
      simpa using mul_le_mul_of_nonneg_right hβ1 (Nat.cast_nonneg (α := ℝ) r₁)
    linarith only [hβr1, hle]
  have hr3 : 3 ≤ r₁ := by
    have h3 : (3 : ℝ) ≤ (r₁ : ℝ) := by linarith only [hr32]
    exact_mod_cast h3
  have hε9 : 4 * (10 : ℝ) ^ (-9 : ℤ) * (1 / 10 ^ 4) ≤ 1 / 10 ^ 5 := by
    have hc : (4 : ℝ) * 10 ^ (-9 : ℤ) = 4 / 10 ^ 9 := by norm_num [zpow_neg]
    rw [hc]; norm_num
  have hMC : Work.Deep.Nibble.MarginsConst r₁ (2 * β) (2 * γ) (1 / 10 ^ 4) (1 / 10 ^ 5) ξ :=
    marginsConst_of_bundle hBN.hm.hnib hr3 hε9
  have hNibP : NibblePointwise r₁ (2 * β) (2 * γ) (1 / 10 ^ 4) (1 / 10 ^ 5) ξ n :=
    nibbleAbove_nibbleThr hMC hThr
  exact s12_branch_B hNibP (hN₄ n hn₄) hBN hβ0 hβγ₁ hγ₁γ hγ0 hγ₁δ hβδ hδ0 hlin hbig hB hR

end

end ErdosFaberLovaszConjecture
