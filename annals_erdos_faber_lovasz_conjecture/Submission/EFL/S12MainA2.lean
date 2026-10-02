import Submission.EFL.S12MainA
import Submission.EFL.OptCol

import Submission.EFL.NibbleFixed
/-!
# §12: the Type A₂ branch of the proof of Theorem 1.1

This module assembles the Type A₂ case of §12: `𝓗` *is* `(ρ,ε)`-full (with
`ρ = σ/2`, `ε = σ³/10⁴²`), the reservoir is of Type A₂ and the final colouring
is obtained either from Vizing's theorem or from Corollary 10.13
(`cor:optcol`, the GKO input).

The new ingredients with respect to the Type A₁ branch are

* the lower regularity of `G_final` (`stat:r_rem`), which uses the
  lower-regular absorber `R_abs` of the Type A₂ reservoir and the robustness
  Proposition 10.3 (`s12_selfLowerRegular_U`, `s12_lowerRegular_final`);
* Corollary 10.13 with `p = ρ/4`, `ε = ζ = ε^{1/3} = σ/10¹⁴` and
  `η = 22ε` (`optcol_corollary`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-- **`stat:r_rem` (second half), with the target parameter as an argument.**
Passing from `G_final[U]` (lower `(ρ/3, η)`-regular on `U`) to `G_final` (lower
`(ρ/4, ζ)`-regular) by the robustness Lemma 10.3(2). -/
theorem s12_lowerRegular_final_gen {R_final : Hypergraph (Fin n)} {U : Set (Fin n)}
    {ρ η αt ζ : ℝ}
    (hcard : ((Set.univ : Set (Fin n)).ncard : ℝ) ≤ (1 + αt * η) * (U.ncard : ℝ))
    (hlr : SelfLowerRegular (induceU R_final U) U (ρ / 3) η)
    (hα0 : 0 ≤ αt) (hα1 : αt < 1) (hη : 0 < η)
    (hnum1 : ρ / 4 - ζ ≤ ρ / 3 * (1 - αt) ^ 2 - η / (1 - αt))
    (hnum2 : η / (1 - αt) ≤ ζ) :
    SelfLowerRegular R_final Set.univ (ρ / 4) ζ := by
  have h1 : SelfLowerRegular R_final Set.univ (ρ / 3 * (1 - αt) ^ 2) (η / (1 - αt)) :=
    selfLowerRegular_mono (induceU R_final U) R_final (X := U) (Y := Set.univ)
      (α := αt) (ρ := ρ / 3) (ξ := η)
      (fun _ _ => Set.mem_univ _) (fun _ he => he.2) (fun _ he => he.1)
      hcard hlr hα0 hα1 hη
  exact h1.mono hnum2 hnum1

/-- **§12 Step 10, Case A₂ (general parameters).**  In the Type A₂ case the
colour classes of `C_final` are empty (T1), `Δ(G_final) ≤ |C_final|`, and if
`Δ(G_final) ≤ |C_final| - 1` Vizing's theorem finishes; otherwise
`Δ(G_final) = |C_final|` and Corollary 10.13 (the `GKO` input, instantiated
for `p = ρ/4`, regularity parameter `ζ` and `η = η0`) finishes. -/
theorem s12_finish_A2_gen {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U S₁ : Set (Fin n)}
    {Cprev Cfinal : Finset (Fin n)} {R_res R_final 𝓗fin : Hypergraph (Fin n)}
    {Mprev : Fin n → Set 𝓗} {ρ ε γ ζ η0 : ℝ}
    (h : S12Out φ U S₁ Cprev Cfinal R_res Mprev R_final 𝓗fin ρ ε γ)
    (hdisj : Disjoint Cprev Cfinal) (hRsub : R_final ⊆ 𝓗)
    (hk1 : 1 ≤ Cfinal.card) (hnum : 1 ≤ ρ * ε * (n : ℝ) / 4)
    (hT1 : ∀ c ∈ Cfinal, colourFam φ c = ∅)
    (hreg : SelfLowerRegular R_final Set.univ (ρ / 4) ζ)
    (hdelta : ∀ v : Fin n, ((hypergraphMaxDegree R_final : ℝ) - (degAt R_final v : ℝ)) ≤
      η0 * (n : ℝ))
    (hcor : ∀ 𝓖 : Hypergraph (Fin n), (∀ e ∈ 𝓖, edgeSize e = 2) →
      SelfLowerRegular 𝓖 Set.univ (ρ / 4) ζ →
      (∀ v : Fin n, ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) ≤ η0 * (n : ℝ)) →
      (({v : Fin n | degAt 𝓖 v < hypergraphMaxDegree 𝓖}.ncard : ℝ) ≥
        (hypergraphMaxDegree 𝓖 : ℝ)) →
      𝓖.Colorable (hypergraphMaxDegree 𝓖)) :
    𝓗.chromaticIndex ≤ n := by
  classical
  have hdeg_le : ∀ w : Fin n, degAt R_final w ≤ Cfinal.card := by
    intro w
    have h1 : (degAt R_final w : ℝ) = (MultiHypergraph.hdeg 𝓗fin w : ℝ) :=
      degAt_R_final_of_T1 h hT1 w
    by_cases hw : w ∈ U
    · by_cases hw1 : w ∈ Vn1set 𝓗
      · have h2 := h.hUC3 w hw1
        rw [← h1] at h2
        have h3 : degAt R_final w ≤ Cfinal.card := by
          by_contra hc
          push_neg at hc
          have h4 : ((Cfinal.card : ℕ) : ℝ) + 1 ≤ (degAt R_final w : ℝ) := by
            have : Cfinal.card + 1 ≤ degAt R_final w := hc
            exact_mod_cast this
          linarith
        exact h3
      · have h2 := h.hUC2 w hw hw1
        rw [← h1] at h2
        have h6 : degAt R_final w + 1 ≤ Cfinal.card := by
          have h7 : (degAt R_final w : ℝ) + 1 ≤ (Cfinal.card : ℝ) := by linarith
          exact_mod_cast h7
        omega
    · have h2 := h.hUC1 w hw
      rw [← h1] at h2
      have h6 : degAt R_final w + 1 ≤ Cfinal.card := by
        have h7 : (degAt R_final w : ℝ) + 1 ≤ (Cfinal.card : ℝ) := by linarith
        exact_mod_cast h7
      omega
  by_cases hV : ∀ w : Fin n, degAt R_final w ≤ Cfinal.card - 1
  · have hdeg' : ∀ w : Fin n,
        {x : Fin n | x ≠ w ∧ ({w, x} : Set (Fin n)) ∈ R_final}.ncard ≤ Cfinal.card - 1 := by
      intro w
      rw [← degAt_eq_pair_offdiag h.hRfin2 w]
      exact hV w
    obtain ⟨Mfin, hMfin⟩ :=
      exists_finishing_vizing_of_degAt hRsub h.hRfin2 hdeg' hk1 hT1
    exact chromaticIndex_le_of_prev_and_finishing hdisj h.hmat hMfin h.hdecomp
  · push_neg at hV
    obtain ⟨w₀, hw₀⟩ := hV
    have hR2' : ∀ e ∈ R_final, edgeSize e = 2 := fun e he => by
      rw [edgeSize_eq_ncard]; exact h.hRfin2 e he
    have hle : hypergraphMaxDegree R_final ≤ Cfinal.card := by
      have h1 : (hypergraphMaxDegree R_final : ℝ) ≤ (Cfinal.card : ℝ) :=
        hypergraphMaxDegree_le_of_le hR2' (Nat.cast_nonneg _)
          (fun v => by exact_mod_cast hdeg_le v)
      exact_mod_cast h1
    have hge : Cfinal.card ≤ hypergraphMaxDegree R_final := by
      have h1 : Cfinal.card - 1 < degAt R_final w₀ := hw₀
      have h2 : degAt R_final w₀ ≤ hypergraphMaxDegree R_final := by
        rw [← hdeg_eq_degAt R_final h.hRfin2 w₀, hdeg_eq_hypergraphDegree]
        exact Finset.le_sup (Finset.mem_univ w₀)
      omega
    have hmax : hypergraphMaxDegree R_final = Cfinal.card := le_antisymm hle hge
    have hsetEq : ({v : Fin n | degAt R_final v < hypergraphMaxDegree R_final} : Set (Fin n)) =
        ({v : Fin n | (MultiHypergraph.hdeg 𝓗fin v : ℝ) < (Cfinal.card : ℝ)} : Set (Fin n)) := by
      ext v
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hmax]
      constructor
      · intro hv
        have h1 : (degAt R_final v : ℝ) = (MultiHypergraph.hdeg 𝓗fin v : ℝ) :=
          degAt_R_final_of_T1 h hT1 v
        rw [← h1]
        exact_mod_cast hv
      · intro hv
        have h1 : (degAt R_final v : ℝ) = (MultiHypergraph.hdeg 𝓗fin v : ℝ) :=
          degAt_R_final_of_T1 h hT1 v
        rw [← h1] at hv
        exact_mod_cast hv
    have hcount' : (({v : Fin n | degAt R_final v < hypergraphMaxDegree R_final}.ncard : ℝ) ≥
        (hypergraphMaxDegree R_final : ℝ)) := by
      rw [hsetEq, hmax]
      exact h.hcount
    have hcol : R_final.Colorable (hypergraphMaxDegree R_final) :=
      hcor R_final hR2' hreg hdelta hcount'
    rw [hmax] at hcol
    obtain ⟨Mfin, hMfin⟩ := exists_finishing_of_colorable hRsub hcol hT1
    exact chromaticIndex_le_of_prev_and_finishing hdisj h.hmat hMfin h.hdecomp

/-- **The chain of §12 (Steps 5--9).**  This is the `S12Out` output of
`s12_chain` (extracted from `s12_main_A1`, so that the Type A₂ finishing can
reuse it). -/
theorem s12_to_S12Out {𝓗 : Hypergraph (Fin n)} {r₁ r₀ : ℕ} {β γ ρ ρ_abs ξ ε κ : ℝ}
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
        𝓗fin ρ ε γ :=
  s12_chain (𝓗 := 𝓗) (r₁ := r₁) (r₀ := r₀) (β := β) (γ := γ) (ρ := ρ)
    (ρ_abs := ρ_abs) (ξ := ξ) (ε := ε) (κ := κ) (φ := φ) (U := U) (S := S) (S₁ := S₁)
    (Cmed := Cmed) (Cdiff := Cdiff) (Chuge := Chuge) (Clarge := Clarge)
    (Cmain := Cmain) (Cbuff := Cbuff) (Cfinal := Cfinal) (R_res := R_res)
    (R_abs := R_abs) (R₁ := R₁) (Mdiff := Mdiff) hlin hbig hNib hleft hS12 hsing hvert
    hres hVuniv hU𝓥 hU hstep4 hR_abs_pow2 hR₁_small hξγ2 hSsubU hS_big hm
    hRabs_sub hVn2U hCwLarge hUCnum1 hUCnum2 hdeficitNum

/-- `√(15√γ) ≤ σ/10³²` when `γ ≤ σ¹⁰/10²⁵⁰` and `σ ≤ 1` (used by the Type A₂
branch). -/
lemma sqrt_fifteen_sqrt_gamma_le {γ σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hγ0 : 0 < γ)
    (hγσ : γ ≤ σ ^ 10 / 10 ^ 250) : Real.sqrt (15 * Real.sqrt γ) ≤ σ / 10 ^ 32 := by
  have h1 : Real.sqrt γ ≤ σ ^ 5 / 10 ^ 125 := by
    have h2 : γ ≤ (σ ^ 5 / 10 ^ 125) ^ 2 := by
      have h3 : ((σ ^ 5 / 10 ^ 125) ^ 2 : ℝ) = σ ^ 10 / 10 ^ 250 := by ring
      linarith [hγσ, h3.ge]
    exact calc Real.sqrt γ ≤ Real.sqrt ((σ ^ 5 / 10 ^ 125) ^ 2) := Real.sqrt_le_sqrt h2
      _ = σ ^ 5 / 10 ^ 125 := Real.sqrt_sq (by positivity)
  have h2 : 15 * Real.sqrt γ ≤ (σ / 10 ^ 32) ^ 2 := by
    have h3 : ((σ / 10 ^ 32) ^ 2 : ℝ) = σ ^ 2 / 10 ^ 64 := by ring
    rw [h3]
    have h4 : σ ^ 5 / 10 ^ 125 ≤ σ ^ 2 / 10 ^ 64 := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10 ^ 125), div_mul_eq_mul_div,
        le_div_iff₀ (by norm_num : (0:ℝ) < 10 ^ 64)]
      have h5 : σ ^ 5 ≤ σ ^ 2 := pow_le_pow_of_le_one hσ0.le hσ1 (by norm_num)
      nlinarith only [h5, pow_nonneg hσ0.le 2]
    have hc : (15 : ℝ) * (1 / 10 ^ 125) ≤ 1 / 10 ^ 64 := by norm_num
    have h5 : (15 : ℝ) * (σ ^ 5 / 10 ^ 125) ≤ σ ^ 2 / 10 ^ 64 := by
      have h4'' : (15 : ℝ) * (σ ^ 5 / 10 ^ 125) ≤ 15 * (σ ^ 2 / 10 ^ 125) := by
        have h5 : σ ^ 5 ≤ σ ^ 2 := pow_le_pow_of_le_one hσ0.le hσ1 (by norm_num)
        nlinarith only [h5, pow_nonneg hσ0.le 2]
      have hc' : (15 : ℝ) * (σ ^ 2 / 10 ^ 125) ≤ σ ^ 2 / 10 ^ 64 := by
        nlinarith only [hc, pow_nonneg hσ0.le 2]
      linarith only [h4'', hc']
    have h6 : 15 * Real.sqrt γ ≤ 15 * (σ ^ 5 / 10 ^ 125) := by linarith only [h1]
    linarith only [h5, h6]
  calc Real.sqrt (15 * Real.sqrt γ) ≤ Real.sqrt ((σ / 10 ^ 32) ^ 2) := Real.sqrt_le_sqrt h2
    _ = σ / 10 ^ 32 := Real.sqrt_sq (by positivity)

/-- **§12, the Type A₂ branch.**  For the constants of `S12ANum` with
`ρ = σ/2 ≤ 10⁻²⁵`, `ρ_abs = σ/4`, `ε = σ³/10⁴²`, a colouring `φ` of Type A with
`𝓗` `(ρ,ε)`-full, the Type A₂ reservoir data and the Corollary 10.13 input
`hcor` (with `p = ρ/4`, `ζ = σ/10¹⁴`, `η = 22ε`), the chromatic index of `𝓗` is
at most `n`. -/
theorem s12_branch_A2 {𝓗 : Hypergraph (Fin n)} {σ γ β ξ : ℝ} {r₁ r₀ : ℕ}
    {φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n)} {U : Set (Fin n)}
    (hNib : NibblePointwise r₁ (2 * β) (2 * γ) (σ ^ 3 / 10 ^ 42) (σ / 4) ξ n)
    (hleft : LeftoverMargins n r₁ γ (σ / 2) (σ / 4) (σ ^ 3 / 10 ^ 42) ξ)
    (hAN : S12ANum n r₁ r₀ β γ σ ξ (σ / 4))
    (hσ0 : 0 < σ) (hσ24 : σ ≤ (10 : ℝ) ^ (-24 : ℤ)) (hγ0 : 0 < γ)
    (hγσ : γ ≤ σ ^ 10 / 10 ^ 250) (hβ0 : 0 < β) (hβγ : β ≤ γ)
    (hr₁2 : 2 ≤ r₁) (hr₀2 : 2 ≤ r₀) (hr₁r₀ : r₁ < r₀)
    (hβr1 : 32 ≤ β * (r₁ : ℝ)) (hr₁β₀ : (r₁ : ℝ) ≤ β * ((r₀ : ℝ) - 1))
    (hr₀big : (r₁ : ℝ) < γ / 4 * ((r₀ : ℝ) - 1))
    (hlin : 𝓗.IsLinear) (hbig : ∀ e ∈ 𝓗, 2 ≤ edgeSize e)
    (hU : U = Vplus 𝓗 (1 - σ ^ 3 / 10 ^ 42))
    (hA : IsTypeA σ γ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 φ)
    (hfull : IsFull 𝓗 (σ / 2) (σ ^ 3 / 10 ^ 42))
    {R_res R_abs : Hypergraph (Fin n)}
    (hRres_pow2 : R_res ⊆ 𝓗.pow2)
    (hRabs : IsAbsorber (incidentTwo 𝓗 U) R_abs (cvFinset φ U : Set (Set (Fin n)))
      (σ / 4) ξ ξ)
    (hRabs_low : LowerRegular (incidentTwo 𝓗 U) R_abs (σ / 4) ξ)
    (hRabs_sub : R_abs ⊆ R_res) (hRabs_pow2 : R_abs ⊆ 𝓗.pow2)
    (hregres : ∃ Rreg : Hypergraph (Fin n),
      R_res = R_abs ∪ Rreg ∧ IsRegularising 𝓗 R_abs Rreg (σ / 2) ξ (σ ^ 3 / 10 ^ 42))
    (hcor : ∀ 𝓖 : Hypergraph (Fin n), (∀ e ∈ 𝓖, edgeSize e = 2) →
      SelfLowerRegular 𝓖 Set.univ ((σ / 2) / 4) (σ / 10 ^ 14) →
      (∀ v : Fin n, ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) ≤
        (22 * (σ ^ 3 / 10 ^ 42)) * (n : ℝ)) →
      (({v : Fin n | degAt 𝓖 v < hypergraphMaxDegree 𝓖}.ncard : ℝ) ≥
        (hypergraphMaxDegree 𝓖 : ℝ)) →
      𝓖.Colorable (hypergraphMaxDegree 𝓖)) :
    𝓗.chromaticIndex ≤ n := by
  classical
  have hn1 : 1 ≤ n := hAN.hm.hn1
  have hn2 : 2 ≤ n := le_trans (by norm_num) hAN.hm.hn4
  have hσhalf : σ ≤ 1 / 2 := by
    have h24 := hσ24
    norm_num at h24
    linarith only [h24]
  have hσone : σ ≤ 1 := le_trans hσhalf (by norm_num)
  have hγ1 : γ ≤ 1 := by
    have h1 : σ ^ 10 / 10 ^ 250 ≤ 1 := by
      have h2 : σ ^ 10 ≤ 1 := pow_le_one₀ hσ0.le hσone (n := 10)
      linarith only [h2]
    linarith only [hγσ, h1]
  have hβ1 : β ≤ 1 := le_trans hβγ hγ1
  have hγsqrt1 : Real.sqrt γ ≤ 1 := Real.sqrt_le_one.mpr hγ1
  have hγs : γ ≤ Real.sqrt γ := by
    nlinarith [Real.sq_sqrt hγ0.le, hγsqrt1, Real.sqrt_nonneg γ]
  -- ## Step 3
  obtain ⟨Cmed, Cdiff, Chuge, Clarge, Cmain, Cbuff, Cfinal, hS12, hsing, hVn2U, hVn1char,
    hVn2char, hvert, h3R, hCl⟩ :=
    s12_step3_typeA (n := n) (𝓗 := 𝓗) (r₁ := (r₁ : ℝ)) (r₀ := (r₀ : ℝ)) (σ := σ)
      (γ₁ := γ) (β := β) (γ := γ) (ρ := σ / 2) (ε := σ ^ 3 / 10 ^ 42)
      hlin hbig hA le_rfl hβ0 hAN.hm.hβn hn2 hAN.hm.hr₁β hAN.hεn3 hU hAN.hnum3 hAN.hDlb
  -- ## Step 4
  have hRabs10 : IsAbsorber (incidentTwo 𝓗 U) R_abs (cvFinset φ U : Set (Set (Fin n)))
      (σ / 4) (10 * ξ) ξ := IsAbsorber.mono_gamma hRabs (by linarith [hAN.hm.hξ0])
  have hDM : DiffMargins n β := ⟨hβ0, hβ1, by nlinarith only [hAN.hm.hmDeg.hβn]⟩
  have hbig' : ∀ f ∈ 𝓗, 2 ≤ f.ncard := fun f hf => by
    have h := hbig f hf
    rwa [edgeSize_eq_ncard] at h
  have hξγ : 10 * ξ + 1 / (n : ℝ) ≤ 3 * γ / 2 := by
    have h := hAN.hξsharp
    linarith only [h, hγ0]
  rcases s12_step4_inst (n := n) (𝓗 := 𝓗) (r₁ := (r₁ : ℝ)) (r₀ := (r₀ : ℝ)) (σ := σ)
      (γ₁ := γ) (β := β) (γ := γ) (ρ := σ / 2) (ρ_abs := σ / 4) (ξ := ξ)
      (ε := σ ^ 3 / 10 ^ 42) (S := U) hlin hbig' hU hS12 hA hDM hn1 hξγ hRabs10 with
      hχ | ⟨Mdiff, R₁, S₁, hstep4⟩
  · exact hχ
  · -- ## the sharp absorber
    have hR₁sharp : IsAbsorber (incidentTwo 𝓗 U) R₁ (cvFinset φ U : Set (Set (Fin n)))
        (σ / 4) (10 * ξ + 1 / (n : ℝ)) ξ :=
      IsAbsorber.delete_step4 hRabs10 hstep4 hS12.hCdiff_card hn1
    -- ## the numeric hypotheses
    have hT1 : ∀ c ∈ Cfinal, colourFam φ c = ∅ := fun c hc =>
      colourFam_eq_empty (hS12.class_eq_empty_of_buff_union_final hCl c
        (Finset.mem_union_right Cbuff hc))
    have hX : (((Cmed ∪ Cdiff ∪ Chuge).card : ℕ) : ℝ) ≤ 5 * Real.sqrt γ * (n : ℝ) := by
      have hk2 := hAN.hm.hk2
      have h6 : 3 * γ * (n : ℝ) ≤ 10 * Real.sqrt γ * (n : ℝ) := by
        nlinarith only [hγs, Real.sqrt_nonneg γ, Nat.cast_nonneg (α := ℝ) n]
      linarith only [h3R, hk2, h6]
    have hUCnum1 : (σ / 2) * (1 - σ ^ 3 / 10 ^ 42) * (n : ℝ) + ξ * (n : ℝ) ≤
        (Cfinal.card : ℝ) - (σ / 2) * (σ ^ 3 / 10 ^ 42) * (n : ℝ) / 2 := by
      have hcfg := hS12.card_final_ge hX (by positivity) (by linarith only [hσhalf]) hn1
      have h15 := hAN.h15ρ
      have h15' : (15 * Real.sqrt γ + ξ) * (n : ℝ) ≤
          ((σ / 2) * (σ ^ 3 / 10 ^ 42) / 2) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right h15 (Nat.cast_nonneg (α := ℝ) n)
      nlinarith only [hcfg, h15']
    have hUCnum2 : 2 * (n : ℝ) / (r₀ : ℝ) ≤
        (σ / 2) * (σ ^ 3 / 10 ^ 42) * (n : ℝ) / 4 := by
      have h8 := hAN.h8r₀
      have h8' : (2 : ℝ) ≤ (σ / 2) * (σ ^ 3 / 10 ^ 42) * (r₀ : ℝ) / 4 := by
        linarith only [h8]
      have hr0 : (0 : ℝ) < (r₀ : ℝ) := by exact_mod_cast (by omega : 0 < r₀)
      rw [div_le_iff₀ hr0]
      nlinarith only [h8', Nat.cast_nonneg (α := ℝ) n]
    have hDn : (Dparam n (σ / 2) : ℝ) ≤ (n : ℝ) := by
      have h1 := hAN.hnum3
      have h2 : (0 : ℝ) ≤ (D'param (Dparam n (σ / 2)) γ : ℝ) := Nat.cast_nonneg _
      have h3 : (0 : ℝ) ≤ 2 * γ * (n : ℝ) := by positivity
      have h4 : (0 : ℝ) ≤ 32 / β ^ 2 := by positivity
      linarith only [h1, h2, h3, h4]
    have hdeficitNum : (((Cdiff ∪ Chuge ∪ Cmed ∪ Cbuff).card : ℕ) : ℝ) +
        2 * γ * ((Cmain.card : ℕ) : ℝ) ≤ 15 * Real.sqrt γ * (n : ℝ) := by
      have hk2 := hAN.hm.hk2
      have hCbuff : ((Cbuff.card : ℕ) : ℝ) ≤ 10 * Real.sqrt γ * (n : ℝ) := by
        rw [hS12.hCbuff_card]
        have h2 : (D'param (Dparam n (σ / 2)) γ : ℝ) ≤
            10 * Real.sqrt γ * (Dparam n (σ / 2) : ℝ) := by
          rw [D'param]
          exact Nat.floor_le (by positivity)
        have h4 : 10 * Real.sqrt γ * (Dparam n (σ / 2) : ℝ) ≤ 10 * Real.sqrt γ * (n : ℝ) :=
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
    have hk1 : 1 ≤ Cfinal.card :=
      one_le_card_Cfinal hS12 hX (by positivity) (by linarith only [hσhalf]) hn1 hAN.h30
        (by linarith only [hAN.hρn25])
    have hnum : 1 ≤ (σ / 2) * (σ ^ 3 / 10 ^ 42) * (n : ℝ) / 4 :=
      one_le_rho_eps_mul hAN.h4ρεn
    have hCwLarge : ∀ w : Fin n, ((finalColoursAt φ Cfinal w).card : ℝ) ≤
        2 * (n : ℝ) / (r₀ : ℝ) := fun w => card_finalColoursAt_le_of_T1 hT1 w
    have hS_big : (1 - 10 * (σ ^ 3 / 10 ^ 42)) * (n : ℝ) < (U.ncard : ℝ) →
        (1 - σ / 2) * (n : ℝ) + 5 * (σ ^ 3 / 10 ^ 42) * (n : ℝ) ≤ (U.ncard : ℝ) :=
      S_big_typeA2 hAN.h15ε
    -- ## the reservoir data
    obtain ⟨Rreg, hRres_eq, hReg⟩ := hregres
    have hσ4 : (σ / 2) / 2 = σ / 4 := by ring
    have hRabs' : IsAbsorber (incidentTwo 𝓗 (Vplus 𝓗 (1 - σ ^ 3 / 10 ^ 42))) R_abs
        (cvFinset φ U : Set (Set (Fin n))) ((σ / 2) / 2) ξ ξ := by
      rw [← hU, hσ4]; exact hRabs
    have hRabs_low' : LowerRegular (incidentTwo 𝓗 (Vplus 𝓗 (1 - σ ^ 3 / 10 ^ 42))) R_abs
        ((σ / 2) / 2) ξ := by
      rw [← hU, hσ4]; exact hRabs_low
    have hresA2 : IsReservoirTypeA2 𝓗 R_res (cvFinset φ U : Set (Set (Fin n)))
        (σ / 2) ξ (σ ^ 3 / 10 ^ 42) :=
      ⟨hRres_pow2, R_abs, Rreg, hRres_eq, hRabs', hRabs_low', hReg⟩
    -- ## the chain (Steps 5--9)
    obtain ⟨Mprev, R_final, 𝓗fin, hout⟩ :=
      s12_to_S12Out (𝓗 := 𝓗) (r₁ := r₁) (r₀ := r₀) (β := β) (γ := γ) (ρ := σ / 2)
        (ρ_abs := σ / 4) (ξ := ξ) (ε := σ ^ 3 / 10 ^ 42) (κ := 1 / 2) (φ := φ) (U := U)
        (S := U) (S₁ := S₁) (Cmed := Cmed) (Cdiff := Cdiff) (Chuge := Chuge)
        (Clarge := Clarge) (Cmain := Cmain) (Cbuff := Cbuff) (Cfinal := Cfinal)
        (R_res := R_res) (R_abs := R_abs) (R₁ := R₁) (Mdiff := Mdiff)
        hlin hbig hNib hleft hS12 hsing hvert (Or.inr (Or.inl hresA2)) mem_cvFinset_univ
        mem_cvFinset_U hU hstep4 hRabs_pow2 hR₁sharp (by linarith only [hAN.hξsharp, hγ0])
        subset_rfl hS_big hAN.hm hRabs_sub hVn2U hCwLarge hUCnum1 hUCnum2 hdeficitNum
    -- ## `stat:r_rem`
    have hdef : ∀ w : Fin n, (degAt (R_abs \ R_final) w : ℝ) ≤ (15 * Real.sqrt γ) * (n : ℝ) := by
      intro w
      have hsub : R_abs \ R_final ⊆ R_res \ R_final :=
        Set.sdiff_subset_sdiff hRabs_sub subset_rfl
      have h3 := hout.hdeficit w
      have h4 : (degAt (R_abs \ R_final) w : ℝ) ≤ (degAt (R_res \ R_final) w : ℝ) := by
        exact_mod_cast degAt_mono hsub w
      linarith only [h3, h4]
    have hfullU : (1 - 10 * (σ ^ 3 / 10 ^ 42)) * (n : ℝ) ≤ (U.ncard : ℝ) := by
      have h := hfull.1
      rwa [← hU] at h
    have hε0 : (0 : ℝ) < σ ^ 3 / 10 ^ 42 := hAN.hε0'
    have hη0 : (0 : ℝ) < σ / 10 ^ 30 := by positivity
    have hα0 : (0 : ℝ) ≤ 15 * Real.sqrt γ := by positivity
    have hε10 : 10 * (σ ^ 3 / 10 ^ 42) ≤ 1 / 2 := by
      have h1 : 1000 * (σ ^ 3 / 10 ^ 42) ≤ 1 := hAN.hm.hmHuge.hεsmall
      nlinarith only [h1, hε0]
    have hsqrtε : Real.sqrt (σ ^ 3 / 10 ^ 42) ≤ σ / 10 ^ 30 := by
      have h2 : σ ^ 3 / 10 ^ 42 ≤ (σ / 10 ^ 30) ^ 2 := by
        have h3 : ((σ / 10 ^ 30) ^ 2 : ℝ) = σ ^ 2 / 10 ^ 60 := by ring
        rw [h3]
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10 ^ 42), div_mul_eq_mul_div,
          le_div_iff₀ (by norm_num : (0:ℝ) < 10 ^ 60)]
        have h4 : σ ^ 3 ≤ σ ^ 2 := pow_le_pow_of_le_one hσ0.le hσone (by norm_num)
        have hσ18 : σ ≤ 1 / 10 ^ 18 := by
          have h24 := hσ24
          norm_num at h24
          linarith only [h24]
        nlinarith only [h4, hσ18, pow_nonneg hσ0.le 2, hσ0]
      calc Real.sqrt (σ ^ 3 / 10 ^ 42) ≤ Real.sqrt ((σ / 10 ^ 30) ^ 2) := Real.sqrt_le_sqrt h2
        _ = σ / 10 ^ 30 := Real.sqrt_sq (by positivity)
    have hsqα : Real.sqrt (15 * Real.sqrt γ) ≤ σ / 10 ^ 32 :=
      sqrt_fifteen_sqrt_gamma_le hσ0 hσone hγ0 hγσ
    have hξε : ξ + Real.sqrt (15 * Real.sqrt γ) ≤ σ / (5 * 10 ^ 31) := by
      have h1 : σ ^ 5 / 10 ^ 125 ≤ σ / 10 ^ 32 := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10 ^ 125), div_mul_eq_mul_div,
          le_div_iff₀ (by norm_num : (0:ℝ) < 10 ^ 32)]
        have h5 : σ ^ 5 ≤ σ := by
          simpa using pow_le_pow_of_le_one hσ0.le hσone (show 1 ≤ 5 by norm_num)
        have hc : (10 : ℝ) ^ 32 ≤ 10 ^ 125 := by norm_num
        nlinarith only [h5, hc, hσ0]
      nlinarith only [hAN.hξle, hsqα, h1, hσ0]
    have hth : (ξ + Real.sqrt (15 * Real.sqrt γ)) * (n : ℝ) ≤ (σ / 10 ^ 30) * (U.ncard : ℝ) := by
      have h1 : ξ + Real.sqrt (15 * Real.sqrt γ) ≤
          (σ / 10 ^ 30) * (1 - 10 * (σ ^ 3 / 10 ^ 42)) := by
        have h2 : (σ / 10 ^ 30) * (1 / 2) ≤ (σ / 10 ^ 30) * (1 - 10 * (σ ^ 3 / 10 ^ 42)) := by
          have h3 : (0 : ℝ) ≤ σ / 10 ^ 30 := le_of_lt hη0
          nlinarith only [h3, hε10]
        have h4 : σ / (5 * 10 ^ 31) ≤ (σ / 10 ^ 30) * (1 / 2) := by
          have he : (σ / 10 ^ 30) * (1 / 2) = σ / (2 * 10 ^ 30) := by ring
          rw [he]
          rw [div_le_iff₀ (by norm_num : (0:ℝ) < 5 * 10 ^ 31), div_mul_eq_mul_div,
            le_div_iff₀ (by norm_num : (0:ℝ) < 2 * 10 ^ 30)]
          nlinarith only [hσ0]
        linarith only [hξε, h2, h4]
      have h6 : (0 : ℝ) ≤ 1 - 10 * (σ ^ 3 / 10 ^ 42) := by linarith only [hε10, hε0]
      have h7 : (ξ + Real.sqrt (15 * Real.sqrt γ)) * (n : ℝ) ≤
          (σ / 10 ^ 30) * ((1 - 10 * (σ ^ 3 / 10 ^ 42)) * (n : ℝ)) := by
        nlinarith only [h1, h6, Nat.cast_nonneg (α := ℝ) n]
      have h5 : (σ / 10 ^ 30) * ((1 - 10 * (σ ^ 3 / 10 ^ 42)) * (n : ℝ)) ≤
          (σ / 10 ^ 30) * (U.ncard : ℝ) :=
        mul_le_mul_of_nonneg_left hfullU (le_of_lt hη0)
      linarith only [h7, h5]
    have hnumε : Real.sqrt (σ ^ 3 / 10 ^ 42) ≤ σ / 10 ^ 30 := hsqrtε
    have hnum2' : (σ / 2) / 2 * (1 - 2 * Real.sqrt (σ ^ 3 / 10 ^ 42)) ≥
        (ξ + Real.sqrt (15 * Real.sqrt γ)) + ((σ / 2) / 3 - σ / 10 ^ 30) := by
      have h1 : 2 * Real.sqrt (σ ^ 3 / 10 ^ 42) ≤ σ / 10 ^ 29 := by
        have h2 : Real.sqrt (σ ^ 3 / 10 ^ 42) ≤ σ / 10 ^ 30 := hsqrtε
        have hc : (2 : ℝ) * (1 / 10 ^ 30) ≤ 1 / 10 ^ 29 := by norm_num
        nlinarith only [h2, hc, hσ0]
      have h3 : ξ + Real.sqrt (15 * Real.sqrt γ) ≤ σ / (5 * 10 ^ 31) := hξε
      have h4 : (σ / 2) * Real.sqrt (σ ^ 3 / 10 ^ 42) ≤ σ / 24 := by
        have hσ18 : σ ≤ 1 / 10 ^ 18 := by
          have h24 := hσ24
          norm_num at h24
          linarith only [h24]
        nlinarith only [h1, hσ18, hσ0]
      have h5 : ξ + Real.sqrt (15 * Real.sqrt γ) ≤ σ / 24 := by
        have h6 : σ / (5 * 10 ^ 31) ≤ σ / 24 := by
          rw [div_le_iff₀ (by norm_num : (0:ℝ) < 5 * 10 ^ 31), div_mul_eq_mul_div,
            le_div_iff₀ (by norm_num : (0:ℝ) < 24)]
          nlinarith only [hσ0]
        linarith only [h3, h6]
      nlinarith only [h4, h5, hη0, hσ0]
    have hlr := s12_selfLowerRegular_U (𝓗 := 𝓗) (R_abs := R_abs) (R_final := R_final)
      (U := U) (ρ := σ / 2) (ξ := ξ) (α := 15 * Real.sqrt γ) (ξ' := σ / 10 ^ 30)
      (ε := σ ^ 3 / 10 ^ 42) (by rw [hU]) (by positivity)
      (by rw [hσ4]; exact hRabs_low) hdef hα0
      (by nlinarith only [hfullU, hε10, Nat.cast_nonneg (α := ℝ) n])
      hAN.hm.hξ0 (le_of_lt hη0) (by positivity) hth hnumε hnum2'
    have hcard : ((Set.univ : Set (Fin n)).ncard : ℝ) ≤
        (1 + (1 / 10 ^ 4) * (σ / 10 ^ 30)) * (U.ncard : ℝ) := by
      have h1 : (Set.univ : Set (Fin n)).ncard = n := by simp
      rw [h1]
      have h2 : (1 : ℝ) ≤ (1 + (1 / 10 ^ 4) * (σ / 10 ^ 30)) *
          (1 - 10 * (σ ^ 3 / 10 ^ 42)) := by
        have h3 : (0 : ℝ) ≤ (1 / 10 ^ 4) * (σ / 10 ^ 30) := by positivity
        have hσ18 : σ ≤ 1 / 10 ^ 18 := by
          have h24 := hσ24
          norm_num at h24
          linarith only [h24]
        have hc : 20 * (σ ^ 3 / 10 ^ 42) ≤ (1 / 10 ^ 4) * (σ / 10 ^ 30) := by
          have hsq : σ ^ 2 ≤ 1 := by nlinarith only [hσone, hσ0]
          rw [show (1 : ℝ) / 10 ^ 4 * (σ / 10 ^ 30) = σ / 10 ^ 34 by ring]
          rw [show (20 : ℝ) * (σ ^ 3 / 10 ^ 42) = 20 * σ ^ 3 / 10 ^ 42 by ring,
            div_le_iff₀ (by norm_num : (0:ℝ) < 10 ^ 42), div_mul_eq_mul_div,
            le_div_iff₀ (by norm_num : (0:ℝ) < 10 ^ 34)]
          nlinarith only [hsq, hσ0]
        nlinarith only [h3, hc, hε10, hσ0]
      have h4 : (0 : ℝ) ≤ 1 + (1 / 10 ^ 4) * (σ / 10 ^ 30) := by positivity
      have h5 : (1 : ℝ) * (n : ℝ) ≤ (1 + (1 / 10 ^ 4) * (σ / 10 ^ 30)) *
          ((1 - 10 * (σ ^ 3 / 10 ^ 42)) * (n : ℝ)) := by
        have h6 := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg (α := ℝ) n)
        linarith only [h6]
      have h7 : (1 + (1 / 10 ^ 4) * (σ / 10 ^ 30)) *
          ((1 - 10 * (σ ^ 3 / 10 ^ 42)) * (n : ℝ)) ≤
          (1 + (1 / 10 ^ 4) * (σ / 10 ^ 30)) * (U.ncard : ℝ) :=
        mul_le_mul_of_nonneg_left hfullU h4
      linarith only [h5, h7]
    have hαt0 : (0 : ℝ) ≤ 1 / 10 ^ 4 := by norm_num
    have hαt1 : (1 / 10 ^ 4 : ℝ) < 1 := by norm_num
    have hnum1 : (σ / 2) / 4 - σ / 10 ^ 14 ≤
        (σ / 2) / 3 * (1 - 1 / 10 ^ 4) ^ 2 - (σ / 10 ^ 30) / (1 - 1 / 10 ^ 4) := by
      have h1 : (σ / 10 ^ 30) / (1 - 1 / 10 ^ 4) ≤ σ / 10 ^ 14 := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 1 - 1 / 10 ^ 4)]
        have hc : (1 : ℝ) / 10 ^ 30 ≤ (1 / 10 ^ 14) * (1 - 1 / 10 ^ 4) := by norm_num
        nlinarith only [hc, hσ0]
      have h2 : (σ / 2) / 4 ≤ (σ / 2) / 3 * (1 - 1 / 10 ^ 4) ^ 2 := by
        have hc : (1 : ℝ) / 4 ≤ (1 / 3) * (1 - 1 / 10 ^ 4) ^ 2 := by norm_num
        nlinarith only [hc, hσ0]
      linarith only [h1, h2]
    have hnum2 : (σ / 10 ^ 30) / (1 - 1 / 10 ^ 4) ≤ σ / 10 ^ 14 := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 1 - 1 / 10 ^ 4)]
      have hc : (1 : ℝ) / 10 ^ 30 ≤ (1 / 10 ^ 14) * (1 - 1 / 10 ^ 4) := by norm_num
      nlinarith only [hc, hσ0]
    have hreg : SelfLowerRegular R_final Set.univ ((σ / 2) / 4) (σ / 10 ^ 14) :=
      s12_lowerRegular_final_gen (R_final := R_final) (U := U) (ρ := σ / 2)
        (η := σ / 10 ^ 30) (αt := 1 / 10 ^ 4) (ζ := σ / 10 ^ 14)
        hcard hlr hαt0 hαt1 hη0 hnum1 hnum2
    have hub : ∀ w : Fin n, (degAt R_res w : ℝ) ≤ (σ / 2 + ξ) * (n : ℝ) := by
      intro w
      rw [hRres_eq]
      by_cases hw : w ∈ Vplus 𝓗 (1 - σ ^ 3 / 10 ^ 42)
      · have h1 := (abs_le.mp (hReg.1 w hw)).2
        have h2 : (degAt 𝓗.pow2 w : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast degAt_le_n 𝓗.pow2 w
        nlinarith only [h1, h2, hσ0, hAN.hm.hξ0]
      · have h1 := (hReg.2 w hw).2
        have h2 : (0 : ℝ) ≤ (σ / 2) * (σ ^ 3 / 10 ^ 42) * (n : ℝ) := by positivity
        nlinarith only [h1, h2, hσ0, hAN.hm.hξ0]
    have hlb : ∀ w : Fin n, (σ / 2 - 20 * (σ ^ 3 / 10 ^ 42)) * (n : ℝ) ≤
        (degAt R_res w : ℝ) := by
      intro w
      rw [hRres_eq]
      by_cases hw : w ∈ Vplus 𝓗 (1 - σ ^ 3 / 10 ^ 42)
      · have h1 := (abs_le.mp (hReg.1 w hw)).1
        have h2 : (1 - σ ^ 3 / 10 ^ 42) * (n : ℝ) ≤ (degAt 𝓗.pow2 w : ℝ) := hw
        have h3 : ξ * (n : ℝ) ≤ 19 * (σ ^ 3 / 10 ^ 42) * (n : ℝ) := by
          have h4 : ξ ≤ 19 * (σ ^ 3 / 10 ^ 42) := by
            have hc : (1 : ℝ) * (1 / 10 ^ 125) ≤ 19 * (1 / 10 ^ 42) := by norm_num
            have h53 : σ ^ 5 ≤ σ ^ 3 := pow_le_pow_of_le_one hσ0.le hσone (by norm_num)
            nlinarith only [hAN.hξle, h53, hσ0, hc]
          nlinarith only [h4, Nat.cast_nonneg (α := ℝ) n]
        have h4 : (σ / 2) * ((1 - σ ^ 3 / 10 ^ 42) * (n : ℝ)) ≤
            (σ / 2) * (degAt 𝓗.pow2 w : ℝ) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        have h5 : (σ / 2) * ((1 - σ ^ 3 / 10 ^ 42) * (n : ℝ)) - ξ * (n : ℝ) ≤
            (degAt (R_abs ∪ Rreg) w : ℝ) := by linarith only [h4, h1]
        have h7 : (σ / 2) * (σ ^ 3 / 10 ^ 42) * (n : ℝ) ≤
            (σ ^ 3 / 10 ^ 42) * (n : ℝ) := by
          have h8 : σ / 2 ≤ 1 := by linarith only [hσhalf]
          have h9 : (0 : ℝ) ≤ (σ ^ 3 / 10 ^ 42) * (n : ℝ) := by positivity
          have h10 := mul_le_mul_of_nonneg_right h8 h9
          have he : (σ / 2) * (σ ^ 3 / 10 ^ 42) * (n : ℝ) =
              (σ / 2) * ((σ ^ 3 / 10 ^ 42) * (n : ℝ)) := by ring
          rw [he]
          linarith only [h10]
        nlinarith only [h5, h3, h7, hσ0, hε0]
      · have h1 := (hReg.2 w hw).1
        have h2 : (σ / 2 - 20 * (σ ^ 3 / 10 ^ 42)) * (n : ℝ) ≤
            max ((σ / 2) * (degAt 𝓗.pow2 w : ℝ))
              ((σ / 2 - 20 * (σ ^ 3 / 10 ^ 42)) * (n : ℝ)) := le_max_right _ _
        exact le_trans h2 h1
    have hdelta : ∀ v : Fin n, ((hypergraphMaxDegree R_final : ℝ) - (degAt R_final v : ℝ)) ≤
        (22 * (σ ^ 3 / 10 ^ 42)) * (n : ℝ) :=
      s12_delta_le (R_res := R_res) (R_final := R_final) (ρ := σ / 2) (ξ := ξ)
        (ε := σ ^ 3 / 10 ^ 42) (γ := γ) hout.hRfin_sub
        (fun e he => by rw [edgeSize_eq_ncard]; exact hout.hRfin2 e he)
        (by nlinarith only [hσ0, hAN.hm.hξ0, Nat.cast_nonneg (α := ℝ) n]) hub hlb
        (fun w => hout.hdeficit w) (by
          have h1 : 15 * Real.sqrt γ ≤ 15 * (σ ^ 5 / 10 ^ 125) := by
            linarith only [hAN.hsqrtγ]
          have h2 : ξ ≤ σ ^ 5 / 10 ^ 125 := hAN.hξle
          have h3 : σ ^ 5 / 10 ^ 125 ≤ σ ^ 3 / 10 ^ 43 := by
            rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10 ^ 125), div_mul_eq_mul_div,
              le_div_iff₀ (by norm_num : (0:ℝ) < 10 ^ 43)]
            have h5 : σ ^ 5 ≤ σ ^ 3 := pow_le_pow_of_le_one hσ0.le hσone (by norm_num)
            nlinarith only [h5, hσ0]
          have h4 : (0:ℝ) ≤ σ ^ 3 / 10 ^ 42 := by positivity
          nlinarith only [h1, h2, h3, hσ0, h4])
    have hdisj : Disjoint (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff) Cfinal := by
      rw [Finset.disjoint_left]
      intro x hx hxc
      rw [hS12.hCfinal_eq, Finset.mem_sdiff] at hxc
      exact hxc.2 hx
    have hRsub : R_final ⊆ 𝓗 := fun e he =>
      (mem_pow2.mp (hRres_pow2 (hout.hRfin_sub he))).1
    exact s12_finish_A2_gen hout hdisj hRsub hk1 hnum hT1 hreg hdelta hcor


end

end ErdosFaberLovaszConjecture
