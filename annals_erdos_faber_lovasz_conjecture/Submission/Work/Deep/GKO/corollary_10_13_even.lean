import Submission.Work.Deep.GKO.Defs
import Submission.Work.Deep.GKO.gkoStatementFixed_of_KO
import Submission.Work.Deep.GKO.OptColImport

/-!
# Corollary 10.13 of the paper (even order), corrected form

The paper's Corollary 10.13 has the hierarchy `0 < 1/n₀ ≪ η, ε ≪ p < 1`.  Here the
thresholds are existential in `p`, matching `Work.Deep.GKO.GKOStatementFixed`; the
derivation is the one in `Submission/EFL/OptCol.lean` (`optcol_corollary_even`) with the
explicit smallness hypothesis replaced by the existential thresholds.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.GKO

open ErdosFaberLovaszConjecture

noncomputable section

/-- **Corollary 10.13 (`cor:optcol`), even order.**  For each `p ∈ (0,1)` there are
thresholds `η₀, ε₀ > 0` such that for all `0 < η ≤ η₀`, `0 < ε ≤ ε₀`, every 2-uniform
hypergraph on `Fin n` with `n` large and even that is lower `(p,ε)`-regular, satisfies
`Δ - d(v) ≤ ηn` for all `v`, and has at least `Δ(𝓖)` vertices of degree less than `Δ(𝓖)`
is `Δ(𝓖)`-edge-colourable. -/
theorem corollary_10_13_even (hGKO : Work.Deep.GKO.GKOStatementFixed) :
    ∀ p : ℝ, 0 < p → p < 1 → ∃ η₀ ε₀ : ℝ, 0 < η₀ ∧ 0 < ε₀ ∧ ε₀ ≤ p ∧
      (∀ η ε : ℝ, 0 < η → η ≤ η₀ → 0 < ε → ε ≤ ε₀ → ∃ N₀ : ℕ,
        ∀ n ≥ N₀, Even n → ∀ 𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin n),
        (∀ e ∈ 𝓖, ErdosFaberLovaszConjecture.edgeSize e = 2) →
        ErdosFaberLovaszConjecture.SelfLowerRegular 𝓖 Set.univ p ε →
        (∀ v : Fin n, ((ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖 : ℝ) -
            (ErdosFaberLovaszConjecture.degAt 𝓖 v : ℝ)) ≤ η * (n : ℝ)) →
        (({v : Fin n | ErdosFaberLovaszConjecture.degAt 𝓖 v <
              ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖}.ncard : ℝ) ≥
            (ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖 : ℝ)) →
        ErdosFaberLovaszConjecture.Hypergraph.Colorable
          (ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖) 𝓖) := by
  intro p hp0 hp1
  obtain ⟨ν₀, ε₀', hν₀, hε₀, -, hmain⟩ := hGKO p hp0 hp1
  refine ⟨min ν₀ (p / 4), min ε₀' (p / 6), lt_min hν₀ (by linarith), lt_min hε₀ (by linarith),
    le_trans (min_le_right _ _) (by linarith), ?_⟩
  intro η ε hη hη₀ hε hε₀
  have hην : η ≤ ν₀ := le_trans hη₀ (min_le_left _ _)
  have hεε : ε ≤ ε₀' := le_trans hε₀ (min_le_left _ _)
  have hεp6 : ε ≤ p / 6 := le_trans hε₀ (min_le_right _ _)
  have hηp4 : η ≤ p / 4 := le_trans hη₀ (min_le_right _ _)
  have hηp : 2 * η ≤ p - 3 * ε := by linarith
  obtain ⟨N₀, hN₀⟩ := hmain η ε hη hην hε hεε
  refine ⟨max N₀ (max 4 (max ⌈(1 : ℝ) / ε⌉₊ ⌈(1 : ℝ) / η⌉₊)), ?_⟩
  intro n hn hev 𝓖 h2 hlr hdeg hlow
  have hN₀le : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hεle : ⌈(1 : ℝ) / ε⌉₊ ≤ n :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn))
  have hn1 : 1 ≤ n := by
    have : (4 : ℕ) ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
    omega
  have hεn : 1 ≤ ε * (n : ℝ) := by
    have h1 : (1 : ℝ) / ε ≤ (n : ℝ) := Nat.ceil_le.mp hεle
    have h2 : 1 ≤ ε * ((1 : ℝ) / ε) := by
      rw [mul_one_div, div_self (ne_of_gt hε)]
    have h3 : ε * ((1 : ℝ) / ε) ≤ ε * (n : ℝ) := mul_le_mul_of_nonneg_left h1 hε.le
    linarith
  have hε1 : ε ≤ 1 / 3 := by nlinarith [hεp6, hp1, hε]
  have hΔ : (p - 3 * ε) * (n : ℝ) ≤ (hypergraphMaxDegree 𝓖 : ℝ) :=
    maxDegree_ge_of_selfLowerRegular 𝓖 h2 hlr hεn hε1 (by linarith) hp1.le hn1
  have hsum : (hypergraphMaxDegree 𝓖 : ℝ) ≤
      ∑ v ∈ (Finset.univ : Finset (Fin n)),
        ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) :=
    maxDegree_le_sum_sub 𝓖 h2 hlow
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact ⟨⟨0, hn1⟩⟩
  obtain ⟨w, -, hw⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n))
    (fun v => degAt 𝓖 v) hne
  have hwle : ∀ v : Fin n, degAt 𝓖 w ≤ degAt 𝓖 v := fun v => hw v (Finset.mem_univ v)
  have hδ : (hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 w : ℝ) ≤ η * (n : ℝ) := hdeg w
  have hΔδ : 2 * ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 w : ℝ)) ≤
      (p - 3 * ε) * (n : ℝ) := by
    have h1 : 2 * (η * (n : ℝ)) ≤ (p - 3 * ε) * (n : ℝ) := by nlinarith [hηp, hη.le]
    linarith [h1, hδ]
  refine hN₀ n hN₀le 𝓖 h2 hlr hdeg hev ⟨w, hwle, ?_⟩
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun v => ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ))) (Finset.mem_univ w)
  linarith [hΔ, hΔδ, hsum, hsplit]

end

end Work.Deep.GKO
