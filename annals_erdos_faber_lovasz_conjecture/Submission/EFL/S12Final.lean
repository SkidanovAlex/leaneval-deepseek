import Submission.EFL.S12Finish
import Submission.EFL.S12Core
import Submission.EFL.S12Numeric

import Submission.EFL.NibbleFixed
/-!
# §12: the final assembly (Step 1 and the numerical glue)

This module assembles the pieces of §12 into the paper's Theorem 1.1 (modulo
the deep inputs `MolloyReedStatement`, `KahnStatement`, `NibbleStatement`,
`LeftoverStatement`).  It is written incrementally; the declarations below are
the self-contained ingredients of the assembly that are already proved.

* `card_finalColoursAt_le`: the counting fact `|C_w| ≤ 2n/r₀` used by UC1
  (`hCwLarge` of `s12_core`): a colour of `C_final` whose colour class meets `w`
  carries a large edge (of size `> r₀`) through `w`, and by linearity a vertex
  is in at most `2n/r₀` edges of size more than `r₀`
  (`hdeg_largeEdges_le` of `S12Numeric.lean`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-- **`|C_w| ≤ 2n/r₀`.**  If every colour class of `C_final` consists of edges
of size more than `r₀`, then the number of colours of `C_final` whose colour
class meets `w` is at most `2n/r₀`.

(For a Type A colouring the left-hand side is even zero by (T1); for Type B
this is the counting `d_{𝓗_large}(w) ≤ 2n/r₀` of `hdeg_largeEdges_le`.) -/
theorem card_finalColoursAt_le {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    {r₁ : ℝ} {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {Cfinal : Finset (Fin n)} {r₀ : ℕ}
    (hr₀ : 2 ≤ r₀)
    (hbig : ∀ c ∈ Cfinal, ∀ e ∈ colourFam φ c,
      (r₀ : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ))
    (w : Fin n) :
    ((finalColoursAt φ Cfinal w).card : ℝ) ≤ 2 * (n : ℝ) / (r₀ : ℝ) := by
  classical
  -- for every colour of `C_w` there is an edge of its class through `w`
  have hex : ∀ c ∈ finalColoursAt φ Cfinal w,
      ∃ e ∈ colourFam φ c, w ∈ (e : Set (Fin n)) := by
    intro c hc
    rw [finalColoursAt, Finset.mem_filter] at hc
    rw [mem_matchVert] at hc
    exact hc.2
  -- choose such an edge
  let f : Fin n → Set (Fin n) := fun c =>
    if h : c ∈ finalColoursAt φ Cfinal w then ((Classical.choose (hex c h) : 𝓗) : Set (Fin n))
    else ∅
  have hfeq : ∀ (c : Fin n) (hc : c ∈ finalColoursAt φ Cfinal w),
      f c = ((Classical.choose (hex c hc) : 𝓗) : Set (Fin n)) := fun c hc => dif_pos hc
  have hCfin : ∀ c ∈ finalColoursAt φ Cfinal w, c ∈ Cfinal := by
    intro c hc
    rw [finalColoursAt, Finset.mem_filter] at hc
    exact hc.1
  have hfbig : ∀ c ∈ finalColoursAt φ Cfinal w, f c ∈ 𝓗.largeEdges r₀ := by
    intro c hc
    have hspec := Classical.choose_spec (hex c hc)
    have hsz : r₀ < edgeSize ((Classical.choose (hex c hc) : 𝓗) : Set (Fin n)) := by
      have h := hbig c (hCfin c hc) (Classical.choose (hex c hc)) hspec.1
      exact_mod_cast h
    have hmem : ((Classical.choose (hex c hc) : 𝓗) : Set (Fin n)) ∈ 𝓗.largeEdges r₀ :=
      (mem_largeEdges 𝓗 r₀ _).mpr ⟨((mem_colourFam.mp hspec.1).1).1, hsz⟩
    rw [hfeq c hc]
    exact hmem
  have hfw : ∀ c ∈ finalColoursAt φ Cfinal w, w ∈ f c := by
    intro c hc
    rw [hfeq c hc]
    exact (Classical.choose_spec (hex c hc)).2
  have hfinj : Set.InjOn f ((finalColoursAt φ Cfinal w : Finset (Fin n)) : Set (Fin n)) := by
    intro c hc c' hc' heq
    by_contra hne
    have h1 : Classical.choose (hex c hc) = Classical.choose (hex c' hc') := by
      refine Subtype.ext ?_
      rw [← hfeq c hc, ← hfeq c' hc']
      exact heq
    have h2 := (Classical.choose_spec (hex c hc)).1
    have h3 := (Classical.choose_spec (hex c' hc')).1
    rw [h1] at h2
    exact Set.disjoint_left.mp (disjoint_colourFam hne) h2 h3
  have hle : (finalColoursAt φ Cfinal w).card ≤
      MultiHypergraph.hdeg (𝓗.largeEdges r₀) w := by
    rw [MultiHypergraph.hdeg, ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn f ?_ hfinj
    intro c hc
    exact ⟨hfbig c hc, hfw c hc⟩
  have h2 := hdeg_largeEdges_le hlin hr₀ w
  have h3 : ((finalColoursAt φ Cfinal w).card : ℝ) ≤
      (MultiHypergraph.hdeg (𝓗.largeEdges r₀) w : ℝ) := by exact_mod_cast hle
  linarith

-- ## The instances of `card_finalColoursAt_le` and the size of `C_final`

/-- In a Type A colouring (T1) the colour classes of `C_final` are empty, so
`C_w = ∅`. -/
theorem card_finalColoursAt_le_of_T1 {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {Cfinal : Finset (Fin n)} {r₀ : ℕ}
    (hT1 : ∀ c ∈ Cfinal, colourFam φ c = ∅) (w : Fin n) :
    ((finalColoursAt φ Cfinal w).card : ℝ) ≤ 2 * (n : ℝ) / (r₀ : ℝ) := by
  have h0 : finalColoursAt φ Cfinal w = ∅ := by
    rw [finalColoursAt, Finset.filter_eq_empty_iff]
    intro c hc
    rw [hT1 c hc]
    simp [matchVert]
  rw [h0, Finset.card_empty, Nat.cast_zero]
  positivity

/-- In a Type B colouring (T2) every colour class of `C_final` consists of
large, non-huge edges, so the counting of `card_finalColoursAt_le` applies. -/
theorem card_finalColoursAt_le_of_T2 {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} {r₀ : ℕ} {β γ ρ : ℝ}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (hlin : 𝓗.IsLinear) (hr₀ : 2 ≤ r₀)
    (hS12 : IsS12Colours n 𝓗 r₁ φ U (r₀ : ℝ) β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff
      Cfinal)
    (w : Fin n) :
    ((finalColoursAt φ Cfinal w).card : ℝ) ≤ 2 * (n : ℝ) / (r₀ : ℝ) := by
  refine card_finalColoursAt_le hlin hr₀ ?_ w
  intro c hc e he
  obtain ⟨hmed, hcl⟩ := mem_colourFam.mp he
  have hlab : φ.labels (⟨(e : Set (Fin n)), hmed⟩ : ↥(medLarge 𝓗 r₁)) = c := by
    rw [← mem_colorClass]
    exact hcl
  have h := (IsS12Colours.large_nonhuge_of_buff_union_final hS12
    (Finset.mem_union_right Cbuff hc) ⟨(e : Set (Fin n)), hmed⟩ hlab).1
  exact_mod_cast h

/-- `|C_final| ≥ (ρ - 15γ^{1/2})n` is positive as soon as `30γ^{1/2} ≤ ρ` and
`ρn ≥ 2`. -/
theorem one_le_card_Cfinal {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} {r₀ β γ ρ : ℝ}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (hS12 : IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal)
    (hX : ((Cmed ∪ Cdiff ∪ Chuge).card : ℝ) ≤ 5 * Real.sqrt γ * (n : ℝ))
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hn1 : 1 ≤ n)
    (hnum : 30 * Real.sqrt γ ≤ ρ) (hn : 2 ≤ ρ * (n : ℝ)) :
    1 ≤ Cfinal.card := by
  have h := hS12.card_final_ge hX hρ0 hρ1 hn1
  have h2 : (1 : ℝ) ≤ (Cfinal.card : ℝ) := by
    have : 15 * Real.sqrt γ ≤ ρ / 2 := by linarith
    nlinarith [h, hn]
  exact_mod_cast h2

/-- The numeric hypothesis `hnum` of `s12_finish_A1`/`_A2`: `1 ≤ ρεn/4`. -/
theorem one_le_rho_eps_mul {ρ ε : ℝ} (hεn : 4 ≤ ρ * ε * (n : ℝ)) :
    1 ≤ ρ * ε * (n : ℝ) / 4 := by
  linarith


-- ## The chain Step 5 -> Step 8/9

/-- **§12, the middle of the assembly.**  From the Step-1--Step-4 data (the
colour sets `IsS12Colours`, the reservoir and absorber of Step 2, the Step-4
package) and the numerical margins, produce the final data `𝓜_prev`,
`R_final = R_res ∖ ⋃𝓜_prev` and `𝓗_final = 𝓗 ∖ ⋃𝓜_prev` together with all the
fields of `S12Out`.  This is Step 5 (`s12_step5_pack_gen`) followed by the core
(`s12_core`); the two hypotheses `hT1`/`hT2data`-style bounds on `|C_w|` are
supplied by the caller (`hCwLarge`). -/
theorem s12_chain {𝓗 : Hypergraph (Fin n)} {r₁ r₀ : ℕ} {β γ ρ ρ_abs ξ ε κ : ℝ}
    {φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n)} {U S S₁ : Set (Fin n)}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    {R_res R_abs R₁ : Hypergraph (Fin n)} {Mdiff : Fin n → Set 𝓗}
    (hlin : 𝓗.IsLinear) (hbig : ∀ f ∈ 𝓗, 2 ≤ edgeSize f)
    (hNib : NibblePointwise r₁ (2 * β) (2 * γ) ε ρ_abs ξ n)
    (hleft : LeftoverMargins n r₁ γ ρ ρ_abs ε ξ)
    (hS12 : IsS12Colours n 𝓗 (r₁ : ℝ) φ U (r₀ : ℝ) β γ ρ Cmed Cdiff Chuge Clarge Cmain
      Cbuff Cfinal)
    (hsing : φ.SingletonClassesForHuge β)
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
    (hR_abs_pow2 : R_abs ⊆ 𝓗.pow2)
    {ζ : ℝ} (hR₁_small : IsAbsorber (incidentTwo 𝓗 U) R₁ (cvFinset φ U : Set (Set (Fin n)))
      ρ_abs ζ ξ)
    (hξγ2 : ζ + 3 * γ / 2 ≤ 2 * γ)
    (hSsubU : S ⊆ U)
    (hS_big : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      (1 - ρ) * (n : ℝ) + 5 * ε * (n : ℝ) ≤ (S.ncard : ℝ))
    (hm : S12Margins n r₁ r₀ β γ ρ ρ_abs ξ ε κ)
    (hRabs_sub : R_abs ⊆ R_res)
    (hVn2U : Vn2set 𝓗 ⊆ U)
    (hCwLarge : ∀ w : Fin n, ((finalColoursAt φ Cfinal w).card : ℝ) ≤
      2 * (n : ℝ) / (r₀ : ℝ))
    (hUCnum1 : ρ * (1 - ε) * (n : ℝ) + ξ * (n : ℝ) ≤
      (Cfinal.card : ℝ) - ρ * ε * (n : ℝ) / 2)
    (hUCnum2 : 2 * (n : ℝ) / (r₀ : ℝ) ≤ ρ * ε * (n : ℝ) / 4)
    (hdeficitNum : (((Cdiff ∪ Chuge ∪ Cmed ∪ Cbuff).card : ℕ) : ℝ) +
      2 * γ * ((Cmain.card : ℕ) : ℝ) ≤ 15 * Real.sqrt γ * (n : ℝ)) :
    ∃ (Mprev : Fin n → Set 𝓗) (R_final 𝓗fin : Hypergraph (Fin n)),
      S12Out φ U S₁ (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff) Cfinal R_res Mprev R_final
        𝓗fin ρ ε γ := by
  have hρ0 : 0 < ρ := hm.hmDeg.hρ0
  have hγ0 : 0 ≤ γ := hm.hγ0
  have hε0 : 0 ≤ ε := hm.hε0
  have hβ0 : 0 < β := hm.hβ0
  have hn1 : 1 ≤ n := hm.hn1
  have hn4 : 4 ≤ n := hm.hn4
  have hεn : 2 ≤ ε * (n : ℝ) := hm.hεn
  have hβn : 8 ≤ β * (n : ℝ) := hm.hβn
  have hk2 : 32 / β ^ 2 ≤ γ * (n : ℝ) / 2 := hm.hk2
  have hr₁2 : 2 ≤ r₁ := hm.hr₁2
  have hr₁β : (r₁ : ℝ) < β * (n : ℝ) / 4 := hm.hr₁β
  have hS₂num : (Dparam n ρ : ℝ) + 3 * γ * (n : ℝ) / 2 + 5 + 4 * ε * (n : ℝ) ≤
      (1 - ρ) * (n : ℝ) + 5 * ε * (n : ℝ) := hm.hS₂num
  -- the size bounds on the huge and medium colour classes
  have hbigsize : ∀ c ∈ Chuge,
      ((matchVert (colourFam φ c) ∩ U).ncard : ℝ) ≤ ε * (n : ℝ) := by
    intro c hc
    rw [matchVert_colourFam]
    exact hS12.huge_class_inter_U_le hsing hU hlin hεn hε0 hc
  have hmedsize : ∀ c ∈ Cmed, ((matchVert (colourFam φ c)).ncard : ℝ) ≤
      (3 * γ / 2) * (n : ℝ) := by
    intro c hc
    rw [matchVert_colourFam]
    have h := hS12.hCmed_vertex c hc
    rw [Hypergraph.Coloring.classVertexCount] at h
    nlinarith [h, hγ0, Nat.cast_nonneg (α := ℝ) n]
  -- the reservoir degree bound outside `U`
  have hresDeg : ∀ w : Fin n, w ∉ U →
      (degAt R_res w : ℝ) ≤ ρ * (1 - ε) * (n : ℝ) + ξ * (n : ℝ) := fun w hw =>
    degAt_Rres_le_of_notMem_Vplus (le_of_lt hρ0) hm.hnpos hres hVuniv (by rwa [hU] at hw)
  -- Step 5
  obtain ⟨Mhm, R₂, S₂, hstep5⟩ :=
    s12_step5_pack_gen (𝓗 := 𝓗) (r₁ := (r₁ : ℝ)) (r₀ := (r₀ : ℝ)) (β := β) (γ := γ)
      (ρ := ρ) (ρ_abs := ρ_abs) (ξ := ξ) (ε := ε) (κ := κ) (φ := φ) (U := U) (S := S)
      (S₁ := S₁) (Cmed := Cmed) (Cdiff := Cdiff) (Chuge := Chuge) (Clarge := Clarge)
      (Cmain := Cmain) (Cbuff := Cbuff) (Cfinal := Cfinal) (R_abs := R_abs) (R₁ := R₁)
      (Mdiff := Mdiff) hlin hS12 hm.hmHuge hU hstep4 hR_abs_pow2 hSsubU hR₁_small hξγ2 hn4
      hγ0 hε0 hεn hk2 hβ0 hβn hn1 (by exact_mod_cast hr₁2) hr₁β hS_big hS₂num hbigsize
      hmedsize
  exact s12_core (𝓗 := 𝓗) (r₁ := r₁) (r₀ := r₀) (β := β) (γ := γ) (ρ := ρ)
    (ρ_abs := ρ_abs) (ξ := ξ) (ε := ε) (κ := κ) (φ := φ) (U := U) (S := S) (S₁ := S₁)
    (Cmed := Cmed) (Cdiff := Cdiff) (Chuge := Chuge) (Clarge := Clarge) (Cmain := Cmain)
    (Cbuff := Cbuff) (Cfinal := Cfinal) (R_res := R_res) (R_abs := R_abs) (R₁ := R₁)
    (R₂ := R₂) (Mdiff := Mdiff) (Mhm := Mhm) hlin hbig hNib hleft hS12 hvert hres hVuniv
    hU𝓥 hU hstep4 S₂ hstep5 hm hRabs_sub hR_abs_pow2 (hstep4.hS₁_sub.trans hSsubU) hVn2U
    hresDeg hCwLarge hUCnum1 hUCnum2 hdeficitNum



/-- **§12, Type A₁, end to end (modulo the numerics).**  `s12_chain` produces
the Step-8/9 output `S12Out` and then `s12_finish_A1` (Vizing) colours the
leftover graph.  The two type-specific inputs are (T1) for the Type A colouring
and the property `V^{(n-1)}(𝓗) ∩ S₁ = ∅` of the Type A₁ defect set. -/
theorem s12_main_A1 {𝓗 : Hypergraph (Fin n)} {r₁ r₀ : ℕ} {β γ ρ ρ_abs ξ ε κ : ℝ}
    {φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n)} {U S S₁ : Set (Fin n)}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    {R_res R_abs R₁ : Hypergraph (Fin n)} {Mdiff : Fin n → Set 𝓗}
    (hlin : 𝓗.IsLinear) (hbig : ∀ f ∈ 𝓗, 2 ≤ edgeSize f)
    (hNib : NibblePointwise r₁ (2 * β) (2 * γ) ε ρ_abs ξ n)
    (hleft : LeftoverMargins n r₁ γ ρ ρ_abs ε ξ)
    (hS12 : IsS12Colours n 𝓗 (r₁ : ℝ) φ U (r₀ : ℝ) β γ ρ Cmed Cdiff Chuge Clarge Cmain
      Cbuff Cfinal)
    (hsing : φ.SingletonClassesForHuge β)
    (hvert : ∀ c : Fin n, c ∉ Cmed → ¬ φ.AssignedToHuge β c →
      (φ.classVertexCount c : ℝ) ≤ β * (n : ℝ))
    (hres : IsReservoirTypeA1 𝓗 R_res (cvFinset φ U : Set (Set (Fin n))) ρ ξ ε)
    (hVuniv : (Set.univ : Set (Fin n)) ∈ (cvFinset φ U : Set (Set (Fin n))))
    (hU𝓥 : U ∈ (cvFinset φ U : Set (Set (Fin n))))
    (hU : U = Vplus 𝓗 (1 - ε))
    (hstep4 : IsS12Step4 𝓗 φ U S Cdiff R_abs R₁ S₁ Mdiff
      (cvFinset φ U : Set (Set (Fin n))) ρ_abs γ ξ)
    (hR_abs_pow2 : R_abs ⊆ 𝓗.pow2)
    {ζ : ℝ} (hR₁_small : IsAbsorber (incidentTwo 𝓗 U) R₁ (cvFinset φ U : Set (Set (Fin n)))
      ρ_abs ζ ξ)
    (hξγ2 : ζ + 3 * γ / 2 ≤ 2 * γ)
    (hSsubU : S ⊆ U)
    (hS_big : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      (1 - ρ) * (n : ℝ) + 5 * ε * (n : ℝ) ≤ (S.ncard : ℝ))
    (hm : S12Margins n r₁ r₀ β γ ρ ρ_abs ξ ε κ)
    (hRabs_sub : R_abs ⊆ R_res)
    (hVn2U : Vn2set 𝓗 ⊆ U)
    (hUCnum1 : ρ * (1 - ε) * (n : ℝ) + ξ * (n : ℝ) ≤
      (Cfinal.card : ℝ) - ρ * ε * (n : ℝ) / 2)
    (hUCnum2 : 2 * (n : ℝ) / (r₀ : ℝ) ≤ ρ * ε * (n : ℝ) / 4)
    (hdeficitNum : (((Cdiff ∪ Chuge ∪ Cmed ∪ Cbuff).card : ℕ) : ℝ) +
      2 * γ * ((Cmain.card : ℕ) : ℝ) ≤ 15 * Real.sqrt γ * (n : ℝ))
    (hT1 : ∀ c ∈ Cfinal, colourFam φ c = ∅)
    (hVn1 : ∀ v : Fin n, v ∈ Vn1set 𝓗 → v ∉ S₁)
    (hk1 : 1 ≤ Cfinal.card) (hnum : 1 ≤ ρ * ε * (n : ℝ) / 4) :
    𝓗.chromaticIndex ≤ n := by
  obtain ⟨Mprev, R_final, 𝓗fin, hout⟩ :=
    s12_chain (𝓗 := 𝓗) (r₁ := r₁) (r₀ := r₀) (β := β) (γ := γ) (ρ := ρ)
      (ρ_abs := ρ_abs) (ξ := ξ) (ε := ε) (κ := κ) (φ := φ) (U := U) (S := S) (S₁ := S₁)
      (Cmed := Cmed) (Cdiff := Cdiff) (Chuge := Chuge) (Clarge := Clarge)
      (Cmain := Cmain) (Cbuff := Cbuff) (Cfinal := Cfinal) (R_res := R_res)
      (R_abs := R_abs) (R₁ := R₁) (Mdiff := Mdiff) hlin hbig hNib hleft hS12 hsing hvert
      (Or.inl hres) hVuniv hU𝓥 hU hstep4 hR_abs_pow2 hR₁_small hξγ2 hSsubU hS_big hm
      hRabs_sub hVn2U (fun w => card_finalColoursAt_le_of_T1 hT1 w) hUCnum1 hUCnum2
      hdeficitNum
  have hdisj : Disjoint (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff) Cfinal := by
    rw [Finset.disjoint_left]
    intro x hx hxc
    rw [hS12.hCfinal_eq, Finset.mem_sdiff] at hxc
    exact hxc.2 hx
  have hRsub : R_final ⊆ 𝓗 := fun e he =>
    (mem_pow2.mp (hres.subset_pow2 (hout.hRfin_sub he))).1
  exact s12_finish_A1 hout hdisj hRsub hk1 hnum hT1 hVn1


end

end ErdosFaberLovaszConjecture
