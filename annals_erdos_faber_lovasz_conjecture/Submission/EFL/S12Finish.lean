import Submission.EFL.S12Assem

/-!
# §12, Step 10: the finishers

This module contains the three cases of the final step of §12.  Each of them
consumes the output of Steps 8/9 (the structure `S12Out`: `𝓜_prev`, `R_final`,
`𝓗_final`, the identity `d_{𝓗_final}(w) = d_{G_final}(w) + |C_w|`, the
decomposition `(eqn:h_final)` and the bounds `UC1`--`UC4`) together with the
type-specific data of Step 1, and produces `S12Finishing`, hence
`χ'(𝓗) ≤ n` by `chromaticIndex_le_of_prev_and_finishing`.

* `s12_finish_A1`: Type A₁ -- (T1) holds, so `𝓗_final = R_final`, and
  `Δ(R_final) ≤ |C_final| - 1`; Vizing's theorem finishes.
* `s12_finish_A2`: Type A₂ -- (T1) holds and the regularity of `G_final`
  (Lemma 11.3's conclusion, `stat:r_rem`) plus Corollary 10.13 finish.
* `s12_finish_B`: Type B -- the Hall-based finishing (Lemma 10.2).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-- In a Type A colouring, (T1) holds: the colour classes of `C_final` are
empty, so `d_{𝓗_final}(w) = d_{G_final}(w)`. -/
theorem degAt_R_final_of_T1 {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U S₁ : Set (Fin n)}
    {Cprev Cfinal : Finset (Fin n)} {R_res R_final 𝓗fin : Hypergraph (Fin n)}
    {Mprev : Fin n → Set 𝓗}
    {ρ ε γ : ℝ} (h : S12Out φ U S₁ Cprev Cfinal R_res Mprev R_final 𝓗fin ρ ε γ)
    (hT1 : ∀ c ∈ Cfinal, colourFam φ c = ∅) (w : Fin n) :
    (degAt R_final w : ℝ) = (MultiHypergraph.hdeg 𝓗fin w : ℝ) := by
  have h1 := h.hdeg_fin w
  have h2 : (finalColoursAt φ Cfinal w).card = 0 := by
    rw [Finset.card_eq_zero, finalColoursAt, Finset.filter_eq_empty_iff]
    intro c hc
    rw [hT1 c hc]
    simp [matchVert]
  rw [h2, Nat.cast_zero, add_zero] at h1
  linarith

/-- **§12 Step 10, Case A₁ (Vizing).**  In the Type A₁ case the colour classes
of `C_final` are empty, `R_final` is precisely the set of uncoloured edges, and
its maximum degree is at most `|C_final| - 1`, so Vizing's theorem produces the
final colouring. -/
theorem s12_finish_A1 {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U S₁ : Set (Fin n)}
    {Cprev Cfinal : Finset (Fin n)} {R_res R_final 𝓗fin : Hypergraph (Fin n)}
    {Mprev : Fin n → Set 𝓗}
    {ρ ε γ : ℝ} (h : S12Out φ U S₁ Cprev Cfinal R_res Mprev R_final 𝓗fin ρ ε γ)
    (hdisj : Disjoint Cprev Cfinal) (hRsub : R_final ⊆ 𝓗)
    (hk1 : 1 ≤ Cfinal.card) (hnum : 1 ≤ ρ * ε * (n : ℝ) / 4)
    (hT1 : ∀ c ∈ Cfinal, colourFam φ c = ∅)
    (hVn1 : ∀ v : Fin n, v ∈ Vn1set 𝓗 → v ∉ S₁) :
    𝓗.chromaticIndex ≤ n := by
  classical
  have hdeg : ∀ w : Fin n, degAt R_final w ≤ Cfinal.card - 1 := by
    intro w
    have h1 : (degAt R_final w : ℝ) = (MultiHypergraph.hdeg 𝓗fin w : ℝ) :=
      degAt_R_final_of_T1 h hT1 w
    by_cases hw : w ∈ U
    · by_cases hw1 : w ∈ Vn1set 𝓗
      · have h2 := h.hUC4 (Or.inl hVn1) w hw1
        rw [← h1] at h2
        have h3 : (degAt R_final w : ℝ) ≤ (Cfinal.card : ℝ) - 1 := h2
        have h4 : (0 : ℝ) ≤ (degAt R_final w : ℝ) := Nat.cast_nonneg _
        have h6 : degAt R_final w + 1 ≤ Cfinal.card := by
          have h7 : (degAt R_final w : ℝ) + 1 ≤ (Cfinal.card : ℝ) := by linarith
          exact_mod_cast h7
        omega
      · have h2 := h.hUC2 w hw hw1
        rw [← h1] at h2
        have h3 : (degAt R_final w : ℝ) ≤ (Cfinal.card : ℝ) - 1 := h2
        have h4 : (0 : ℝ) ≤ (degAt R_final w : ℝ) := Nat.cast_nonneg _
        have h6 : degAt R_final w + 1 ≤ Cfinal.card := by
          have h7 : (degAt R_final w : ℝ) + 1 ≤ (Cfinal.card : ℝ) := by linarith
          exact_mod_cast h7
        omega
    · have h2 := h.hUC1 w hw
      rw [← h1] at h2
      have h3 : (degAt R_final w : ℝ) ≤ (Cfinal.card : ℝ) - 1 := by linarith
      have h6 : degAt R_final w + 1 ≤ Cfinal.card := by
        have h7 : (degAt R_final w : ℝ) + 1 ≤ (Cfinal.card : ℝ) := by linarith
        exact_mod_cast h7
      omega
  have hdeg' : ∀ w : Fin n,
      {x : Fin n | x ≠ w ∧ ({w, x} : Set (Fin n)) ∈ R_final}.ncard ≤ Cfinal.card - 1 := by
    intro w
    rw [← degAt_eq_pair_offdiag h.hRfin2 w]
    exact hdeg w
  obtain ⟨Mfin, hMfin⟩ :=
    exists_finishing_vizing_of_degAt hRsub h.hRfin2 hdeg' hk1 hT1
  exact chromaticIndex_le_of_prev_and_finishing hdisj h.hmat hMfin h.hdecomp


/-- **§12 Step 10, Case A₂.**  In the Type A₂ case the colour classes of
`C_final` are again empty.  If `Δ(G_final) ≤ |C_final| - 1` Vizing's theorem
finishes as in Case A₁; otherwise `Δ(G_final) = |C_final|` and Corollary 10.13
(the `GKO` input, instantiated for the given `n`) together with the regularity
of `G_final` gives the colouring. -/
theorem s12_finish_A2 {𝓗 : Hypergraph (Fin n)} {r₁ r₀ : ℕ} {β γ ρ ρ_abs ξ ε κ : ℝ}
    {φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n)} {U S₁ : Set (Fin n)}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    {R_res R_final 𝓗fin : Hypergraph (Fin n)} {Mprev : Fin n → Set 𝓗}
    (h : S12Out φ U S₁ (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff) Cfinal R_res Mprev R_final
      𝓗fin ρ ε γ)
    (hdisj : Disjoint (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff) Cfinal)
    (hRsub : R_final ⊆ 𝓗) (hk1 : 1 ≤ Cfinal.card) (hnum : 1 ≤ ρ * ε * (n : ℝ) / 4)
    (hT1 : ∀ c ∈ Cfinal, colourFam φ c = ∅)
    (hVn1 : ∀ v : Fin n, v ∈ Vn1set 𝓗 → v ∉ S₁)
    (hreg : SelfLowerRegular R_final Set.univ (ρ / 4) (ε ^ (1 / 3 : ℝ)))
    (hdelta : ∀ v : Fin n, ((hypergraphMaxDegree R_final : ℝ) - (degAt R_final v : ℝ)) ≤
      (22 * ε) * (n : ℝ))
    (hcor : ∀ 𝓖 : Hypergraph (Fin n), (∀ e ∈ 𝓖, edgeSize e = 2) →
      SelfLowerRegular 𝓖 Set.univ (ρ / 4) (ε ^ (1 / 3 : ℝ)) →
      (∀ v : Fin n, ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) ≤ (22 * ε) * (n : ℝ)) →
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
  · -- Vizing's theorem applies
    have hdeg' : ∀ w : Fin n,
        {x : Fin n | x ≠ w ∧ ({w, x} : Set (Fin n)) ∈ R_final}.ncard ≤ Cfinal.card - 1 := by
      intro w
      rw [← degAt_eq_pair_offdiag h.hRfin2 w]
      exact hV w
    obtain ⟨Mfin, hMfin⟩ :=
      exists_finishing_vizing_of_degAt hRsub h.hRfin2 hdeg' hk1 hT1
    exact chromaticIndex_le_of_prev_and_finishing hdisj h.hmat hMfin h.hdecomp
  · -- `Δ(G_final) = |C_final|`: Corollary 10.13 applies
    push_neg at hV
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

/-- **§12 Step 10, Case B.**  In the Type B case the final colouring is obtained
from the Hall-based finishing lemma (Lemma 10.2): the colouring `ψ` of the
leftover graph `R_final` avoids, at both ends of every edge, the colours already
used by `φ` at that vertex, and `ψ⁻¹(c) ∪ φ⁻¹(c)` is then a matching. -/
theorem s12_finish_B {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U S₁ : Set (Fin n)}
    {Cprev Cfinal : Finset (Fin n)} {R_res R_final 𝓗fin : Hypergraph (Fin n)}
    {Mprev : Fin n → Set 𝓗} {ρ ε γ δ : ℝ}
    (h : S12Out φ U S₁ Cprev Cfinal R_res Mprev R_final 𝓗fin ρ ε γ)
    (hdisj : Disjoint Cprev Cfinal) (hRsub : R_final ⊆ 𝓗)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hC : 7 * δ * (n : ℝ) ≤ (Cfinal.card : ℝ))
    (hUfin : (U.ncard : ℝ) ≤ δ * (n : ℝ))
    (hUcov : ∀ e ∈ R_final, ∃ u ∈ e, u ∈ U)
    (hdeg : ∀ w : Fin n, degAt R_final w +
      (finalColoursAt φ Cfinal w).card ≤ Cfinal.card - 1)
    (hCw : ∀ w : Fin n, ((finalColoursAt φ Cfinal w).card : ℝ) ≤ δ * (n : ℝ))
    (hCcol : ∀ c ∈ Cfinal,
      (((Finset.univ : Finset (Fin n)).filter
        (fun w => c ∈ finalColoursAt φ Cfinal w)).card : ℝ) ≤ δ * (n : ℝ)) :
    𝓗.chromaticIndex ≤ n := by
  obtain ⟨Mfin, hMfin⟩ :=
    exists_finishing_hall_of_margins hRsub h.hRfin2 hδ0 hδ1 hC hUfin hUcov hdeg hCw hCcol
  exact chromaticIndex_le_of_prev_and_finishing hdisj h.hmat hMfin h.hdecomp

end

end ErdosFaberLovaszConjecture

