import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.asmDefs

/-!
# The absorption step with a conditional defect-set hypothesis

`absorbBatch` requires `γp n ≤ |S|` unconditionally; in the §7 assembly this is
only available when `(1 - 2ε)n < |U|`.  The same conclusion holds with the
conditional hypothesis: in the small-`U` case the absorption produces *perfect*
coverage (`crossing_absorption_multi`, or `internal_absorption_multi` with
`S := U`, which is legitimate because then `n/100 < |U|`).
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

local notation "Hypergraph" => ErdosFaberLovaszConjecture.Hypergraph

noncomputable section

theorem absorbBatch_cond {n : ℕ} {K' : ℕ}
    {𝓗 : MultiHypergraph n}
    {R Rcur : Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {U S : Set (Fin n)} {ρ ε γp κa ξ : ℝ}
    (hm : InternalMargins n ρ ε γp κa ξ)
    (hc : CrossingMargins n ρ ε γp κa ξ)
    (hR2 : ∀ e ∈ Rcur, edgeSize e = 2)
    (habs : IsAbsorber
      (incidentTwo (MultiHypergraph.pow2 𝓗) U) Rcur 𝓥 ρ (10 * γp) ξ)
    (hU𝓥 : U ∈ 𝓥)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤
      (degAt (incidentTwo (MultiHypergraph.pow2 𝓗) U) u : ℝ))
    (hγp1 : γp ≤ 1 / 100) (hSsub : S ⊆ U)
    (hS : (1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ) → γp * (n : ℝ) ≤ (S.ncard : ℝ))
    (N : Fin K' → Set (Set (Fin n)))
    (hNmat : ∀ i, MultiHypergraph.IsMatching 𝓗 (N i))
    (hNdisj : ∀ i j, i ≠ j → EdgeDisjointFam (N i) (N j))
    (hNR : ∀ i, ∀ e ∈ N i, e ∉ Rcur)
    (hpseudo : ∀ i, PseudoRandomFam (N i) (absorbFam Rcur U S) γp κa)
    (hk : (K' : ℝ) ≤ κa * (n : ℝ)) :
    ∃ N' : Fin K' → Set (Set (Fin n)),
      (∀ i, N i ⊆ N' i) ∧
      (∀ i, ∀ e ∈ N' i, e ∉ N i → e ∈ Rcur) ∧
      (∀ i, MultiHypergraph.IsMatching 𝓗 (N' i)) ∧
      (∀ i j, i ≠ j → EdgeDisjointFam (N' i) (N' j)) ∧
      (((U.ncard : ℝ) ≤ (1 - 2 * ε) * (n : ℝ)) → ∀ i, CoversFamMulti (N' i) U) ∧
      (((1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ)) →
        NearlyPerfectCoverageFam N' U S) := by
  by_cases hUbig : (1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ)
  · exact absorbBatch (R := R) hm hc hR2 habs hU𝓥 hUdeg hSsub (hS hUbig) N hNmat hNdisj hNR
      hpseudo hk
  · by_cases hsmall : (U.ncard : ℝ) ≤ (n : ℝ) / 100
    · obtain ⟨N', h1, h2, h3, h4, h5⟩ :=
        crossing_absorption_multi (𝓜 := 𝓗) (R := Rcur) (𝓥 := 𝓥) (U := U)
          (ρ := ρ) (ε := ε) (γ := γp) (κ := κa) (ξ := ξ)
          hc hsmall hUdeg habs hU𝓥 N hNmat hNdisj hNR
          (fun i => (hpseudo i).mono (absorbFam_subset_crossing Rcur U S)) hk
      exact ⟨N', h1, h2, h3, h4, fun _ i => h5 i, fun hbig => absurd hbig hUbig⟩
    · have hgt : (n : ℝ) / 100 < (U.ncard : ℝ) := not_le.mp hsmall
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hgn : γp * (n : ℝ) ≤ (n : ℝ) / 100 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 100)]
        nlinarith
      have hS' : γp * (n : ℝ) ≤ (U.ncard : ℝ) := by linarith
      have hsubU : absorbFam Rcur U U ⊆ absorbFam Rcur U S := by
        intro X hX
        simp only [absorbFam, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hX ⊢
        tauto
      obtain ⟨N', h1, h2, h3, h4, h5, h6⟩ :=
        absorbBatch (R := R) (S := U) hm hc hR2 habs hU𝓥 hUdeg (subset_rfl) hS' N hNmat hNdisj
          hNR (fun i => (hpseudo i).mono hsubU) hk
      exact ⟨N', h1, h2, h3, h4, h5, fun hbig => absurd hbig hUbig⟩

end

end Work.Deep.Nibble
