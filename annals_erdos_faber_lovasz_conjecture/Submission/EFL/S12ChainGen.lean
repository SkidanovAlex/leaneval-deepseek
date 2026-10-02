import Submission.EFL.S12Final

import Submission.EFL.NibbleFixed
/-!
# §12: the chain of Steps 5--9 with explicit class-size bounds

`s12_chain` derives the size bounds on the huge/medium colour classes
(`hbigsize`/`hmedsize`) from `SingletonsForHuge` -- which holds in Type A but
*not* in Type B.  This module repeats the chain with those two bounds as
hypotheses, so it applies in all three types.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-- **§12, the middle of the assembly (generic form).**  As `s12_chain`, but
with the size bounds `hbigsize`/`hmedsize` on the huge/medium colour classes
supplied directly (they follow from `SingletonsForHuge` in Type A and from
`(6.7:b)` in Type B). -/
theorem s12_chain_gen {𝓗 : Hypergraph (Fin n)} {r₁ r₀ : ℕ} {β γ ρ ρ_abs ξ ε κ : ℝ}
    {φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n)} {U S S₁ : Set (Fin n)}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    {R_res R_abs R₁ : Hypergraph (Fin n)} {Mdiff : Fin n → Set 𝓗}
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
    (hbigsize : ∀ c ∈ Chuge,
      ((matchVert (colourFam φ c) ∩ U).ncard : ℝ) ≤ ε * (n : ℝ))
    (hmedsize : ∀ c ∈ Cmed,
      ((matchVert (colourFam φ c)).ncard : ℝ) ≤ (3 * γ / 2) * (n : ℝ))
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
  have hresDeg : ∀ w : Fin n, w ∉ U →
      (degAt R_res w : ℝ) ≤ ρ * (1 - ε) * (n : ℝ) + ξ * (n : ℝ) := fun w hw =>
    degAt_Rres_le_of_notMem_Vplus (le_of_lt hρ0) hm.hnpos hres hVuniv (by rwa [hU] at hw)
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

/-- **The chain of §12 (Steps 5--9), generic form.**  As `s12_to_S12Out` but
with the explicit size bounds on the huge/medium colour classes. -/
theorem s12_to_S12Out_gen {𝓗 : Hypergraph (Fin n)} {r₁ r₀ : ℕ} {β γ ρ ρ_abs ξ ε κ : ℝ}
    {φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n)} {U S S₁ : Set (Fin n)}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    {R_res R_abs R₁ : Hypergraph (Fin n)} {Mdiff : Fin n → Set 𝓗}
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
    (hbigsize : ∀ c ∈ Chuge,
      ((matchVert (colourFam φ c) ∩ U).ncard : ℝ) ≤ ε * (n : ℝ))
    (hmedsize : ∀ c ∈ Cmed,
      ((matchVert (colourFam φ c)).ncard : ℝ) ≤ (3 * γ / 2) * (n : ℝ))
    (hCwLarge : ∀ w : Fin n, ((finalColoursAt φ Cfinal w).card : ℝ) ≤
      2 * (n : ℝ) / (r₀ : ℝ))
    (hUCnum1 : ρ * (1 - ε) * (n : ℝ) + ξ * (n : ℝ) ≤
      (Cfinal.card : ℝ) - ρ * ε * (n : ℝ) / 2)
    (hUCnum2 : 2 * (n : ℝ) / (r₀ : ℝ) ≤ ρ * ε * (n : ℝ) / 4)
    (hdeficitNum : (((Cdiff ∪ Chuge ∪ Cmed ∪ Cbuff).card : ℕ) : ℝ) +
      2 * γ * ((Cmain.card : ℕ) : ℝ) ≤ 15 * Real.sqrt γ * (n : ℝ)) :
    ∃ (Mprev : Fin n → Set 𝓗) (R_final 𝓗fin : Hypergraph (Fin n)),
      S12Out φ U S₁ (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff) Cfinal R_res Mprev R_final
        𝓗fin ρ ε γ :=
  s12_chain_gen (𝓗 := 𝓗) (r₁ := r₁) (r₀ := r₀) (β := β) (γ := γ) (ρ := ρ)
    (ρ_abs := ρ_abs) (ξ := ξ) (ε := ε) (κ := κ) (φ := φ) (U := U) (S := S) (S₁ := S₁)
    (Cmed := Cmed) (Cdiff := Cdiff) (Chuge := Chuge) (Clarge := Clarge)
    (Cmain := Cmain) (Cbuff := Cbuff) (Cfinal := Cfinal) (R_res := R_res)
    (R_abs := R_abs) (R₁ := R₁) (Mdiff := Mdiff) hlin hbig hNib hleft hS12 hvert
    hres hVuniv hU𝓥 hU hstep4 hR_abs_pow2 hR₁_small hξγ2 hSsubU hS_big hm
    hRabs_sub hVn2U hbigsize hmedsize hCwLarge hUCnum1 hUCnum2 hdeficitNum

end

end ErdosFaberLovaszConjecture
