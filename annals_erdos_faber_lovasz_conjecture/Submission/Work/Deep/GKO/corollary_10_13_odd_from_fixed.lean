import Submission.EFL.OptColOdd
import Submission.Work.Deep.GKO.Defs
import Submission.Work.Deep.GKO.corollary_10_13_even

/-!
# The odd case of Corollary 10.13, from the faithful form of Theorem 10.8

`Submission/EFL/OptColOdd.lean` proves the odd case of Corollary 10.13 from the
linear-hierarchy deep input `ErdosFaberLovaszConjecture.GKOStatement`.  This module carries out
the same reduction against the faithful form `Work.Deep.GKO.GKOStatementFixed` (existential
thresholds in `p`), so that a consumer of the faithful statement has both parities available:
`Work.Deep.GKO.corollary_10_13_even` (even case) and
`Work.Deep.GKO.corollary_10_13_odd_from_fixed` (odd case).

The reduction is verbatim the one of `optcol_corollary_odd` — add a new vertex `v*` joined to
`t := ⌊Δ(G) - 2ηn⌋` vertices of degree below `Δ`, obtaining `G*` on `n+1` (even) vertices with
`Δ(G*) = Δ(G)`, spread `≤ 3η(n+1)` and lower `(p/4, 2ε)`-regularity — except that the
existential thresholds of `GKOStatementFixed` are read off at `p/4` and absorbed into the
thresholds `η₀ := min (ν₀/3) (p/100)`, `ε₀ := min (ε₀'/2) (p/100)`.
-/

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.GKO

open ErdosFaberLovaszConjecture

noncomputable section

/-- **Corollary 10.13 (odd case), from `GKOStatementFixed`.**  For every `p ∈ (0,1)` there are
`η₀, ε₀ > 0` such that for all odd `n`, every 2-uniform `𝓖` on `Fin n` that is lower
`(p,ε)`-regular, has degree spread `Δ - d(v) ≤ η n`, at least `Δ(𝓖)` deficient vertices, is
`Δ(𝓖)`-colourable. -/
theorem corollary_10_13_odd_from_fixed (hGKO : GKOStatementFixed) :
    ∀ p : ℝ, 0 < p → p < 1 → ∃ η₀ ε₀ : ℝ, 0 < η₀ ∧ 0 < ε₀ ∧ ε₀ ≤ p ∧
      (∀ η ε : ℝ, 0 < η → η ≤ η₀ → 0 < ε → ε ≤ ε₀ → ∃ N₀ : ℕ,
        ∀ n ≥ N₀, Odd n → ∀ 𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin n),
        (∀ e ∈ 𝓖, edgeSize e = 2) →
        SelfLowerRegular 𝓖 Set.univ p ε →
        (∀ v : Fin n, ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) ≤ η * (n : ℝ)) →
        (({v : Fin n | degAt 𝓖 v < hypergraphMaxDegree 𝓖}.ncard : ℝ) ≥
          (hypergraphMaxDegree 𝓖 : ℝ)) →
        𝓖.Colorable (hypergraphMaxDegree 𝓖)) := by
  intro p hp0 hp1
  obtain ⟨ν₀, ε₀', hν₀, hε₀', hε₀'p, hmain⟩ := hGKO (p / 4) (by linarith) (by linarith)
  refine ⟨min (ν₀ / 3) (p / 100), min (ε₀' / 2) (p / 100),
    lt_min (by linarith) (by linarith), lt_min (by linarith) (by linarith),
    le_trans (min_le_right _ _) (by linarith), ?_⟩
  intro η ε hη hη₀ hε hε₀
  have hp : p < 1 := hp1
  have hηp100 : η ≤ p / 100 := le_trans hη₀ (min_le_right _ _)
  have hεp100 : ε ≤ p / 100 := le_trans hε₀ (min_le_right _ _)
  have h3ην : 3 * η ≤ ν₀ := by
    have h : η ≤ ν₀ / 3 := le_trans hη₀ (min_le_left _ _)
    linarith
  have h2εε₀ : 2 * ε ≤ ε₀' := by
    have h : ε ≤ ε₀' / 2 := le_trans hε₀ (min_le_left _ _)
    linarith

  have hεp : 8 * ε < p := by nlinarith [hεp100, hp0]
  have hηp : 24 * (η + ε) ≤ p := by nlinarith [hηp100, hεp100, hp0]
  obtain ⟨Nc, hNc⟩ := hmain (3 * η) (2 * ε) (by linarith) h3ην (by linarith) h2εε₀
  refine ⟨max Nc (100 + (⌈2 / ε⌉₊ + ⌈1 / η⌉₊)), ?_⟩
  intro n hn hodd 𝓖 h2 hlr hdeg hlow
  have hn1 : 1 ≤ n := by obtain ⟨k, hk⟩ := hodd; omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hNcle : Nc ≤ n := by omega
  have hεle : ⌈2 / ε⌉₊ ≤ n := by omega
  have hηle : ⌈1 / η⌉₊ ≤ n := by omega
  have hεn2 : 2 ≤ ε * (n : ℝ) := by
    have h1 : (2 : ℝ) / ε ≤ (n : ℝ) := Nat.ceil_le.mp hεle
    have h2 : ε * ((2 : ℝ) / ε) = 2 := by
      rw [mul_div_cancel₀ _ (ne_of_gt hε)]
    nlinarith [h1, hε.le, h2]
  have hεn : 1 ≤ ε * (n : ℝ) := by linarith
  have hηn1 : 1 ≤ η * (n : ℝ) := by
    have h1 : (1 : ℝ) / η ≤ (n : ℝ) := Nat.ceil_le.mp hηle
    have h2 : η * ((1 : ℝ) / η) = 1 := by
      rw [mul_one_div, div_self (ne_of_gt hη)]
    nlinarith [h1, hη.le, h2]
  have hε1 : ε ≤ 1 / 3 := by nlinarith [hεp, hp]
  have hεp' : ε ≤ p := by linarith
  set Δ : ℕ := hypergraphMaxDegree 𝓖 with hΔ
  have hΔge : (p - 3 * ε) * (n : ℝ) ≤ (Δ : ℝ) := by
    rw [hΔ]
    exact maxDegree_ge_of_selfLowerRegular 𝓖 h2 hlr hεn hε1 hεp' hp.le hn1
  have h2η : 2 * η + 3 * ε ≤ p := by nlinarith [hηp, hη, hε]
  have hDge : Δ ≤ {v : Fin n | degAt 𝓖 v < Δ}.ncard := by
    have := hlow
    rw [ge_iff_le] at this
    exact_mod_cast this
  set t : ℕ := ⌊(Δ : ℝ) - 2 * η * (n : ℝ)⌋₊ with ht
  have ht0 : (0 : ℝ) ≤ (Δ : ℝ) - 2 * η * (n : ℝ) := by
    have h1 : 2 * η * (n : ℝ) ≤ (p - 3 * ε) * (n : ℝ) := by nlinarith [h2η, hnR]
    linarith
  have ht2 : (t : ℝ) ≤ (Δ : ℝ) - 2 * η * (n : ℝ) := by
    rw [ht]; exact Nat.floor_le ht0
  have htleΔ : t ≤ Δ := by
    have h1 : (t : ℝ) ≤ (Δ : ℝ) := by nlinarith [ht2, hη, hnR]
    exact_mod_cast h1
  set S : Finset (Fin n) := Finset.univ.filter (fun v => degAt 𝓖 v < Δ) with hS
  have hScoe : (S : Set (Fin n)) = {v : Fin n | degAt 𝓖 v < Δ} := by
    ext v; simp [hS]
  have hScard : Δ ≤ S.card := by
    have h : S.card = ({v : Fin n | degAt 𝓖 v < Δ}).ncard := by
      rw [← Set.ncard_coe_finset (s := S), hScoe]
    rw [h]; exact hDge
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (s := S) (n := t)
    (le_trans htleΔ hScard)
  have hTmem : ∀ u ∈ T, degAt 𝓖 u < Δ := by
    intro u hu
    have := hTsub hu
    rw [hS, Finset.mem_filter] at this
    exact this.2
  have hTcard_le : T.card ≤ Δ := by rw [hTcard]; exact htleΔ
  have hTcard_eq : T.card = t := hTcard
  have h2ext : ∀ e ∈ extendVertex 𝓖 T, edgeSize e = 2 :=
    fun e he => edgeSize_extendVertex h2 hn1 he
  have hmaxEq : hypergraphMaxDegree (extendVertex 𝓖 T) = Δ := by
    rw [hΔ]
    exact hypergraphMaxDegree_extendVertex h2 hn1 hTmem hTcard_le
  have hev : Even (n + 1) := by obtain ⟨k, hk⟩ := hodd; exact ⟨k + 1, by omega⟩
  have hcardLR : ((n : ℝ) + 1) ≤ (1 + (1 / 2) * ε) * (n : ℝ) := by
    nlinarith [hεn2, hnR]
  have hlrExt : SelfLowerRegular (extendVertex 𝓖 T) Set.univ (p / 4) (2 * ε) :=
    selfLowerRegular_extendVertex hn1 hε hlr hcardLR
  have hdegExt : ∀ v : Fin (n + 1),
      ((hypergraphMaxDegree (extendVertex 𝓖 T) : ℝ) - (degAt (extendVertex 𝓖 T) v : ℝ))
        ≤ 3 * η * ((n : ℝ) + 1) := by
    intro v
    rw [hmaxEq]
    rcases lt_or_ge v.val n with hv | hv
    · have hvcast : Fin.castSucc (⟨v.val, hv⟩ : Fin n) = v := by ext; simp [Fin.castSucc]
      rw [← hvcast, degAt_extendVertex_castSucc 𝓖 T _ hn1]
      have hd := hdeg (⟨v.val, hv⟩ : Fin n)
      by_cases huT : (⟨v.val, hv⟩ : Fin n) ∈ T
      · rw [if_pos huT]
        have hcast : (((degAt 𝓖 (⟨v.val, hv⟩ : Fin n) + 1 : ℕ)) : ℝ)
            = (degAt 𝓖 (⟨v.val, hv⟩ : Fin n) : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        nlinarith [hd, hε, hη, hnR]
      · rw [if_neg huT]
        have hcast : (((degAt 𝓖 (⟨v.val, hv⟩ : Fin n) + 0 : ℕ)) : ℝ)
            = (degAt 𝓖 (⟨v.val, hv⟩ : Fin n) : ℝ) := by push_cast; ring
        rw [hcast]
        nlinarith [hd, hη, hnR]
    · have hvlast : v = Fin.last n := by
        ext; simp only [Fin.val_last]; omega
      rw [hvlast, degAt_extendVertex_last 𝓖 T hn1, hTcard_eq]
      have h3 : (Δ : ℝ) - (t : ℝ) < 2 * η * (n : ℝ) + 1 := by
        have := Nat.sub_one_lt_floor ((Δ : ℝ) - 2 * η * (n : ℝ))
        rw [ht]
        linarith
      nlinarith [h3, hηn1, hη]
  have hmin : ∀ v : Fin (n + 1),
      degAt (extendVertex 𝓖 T) (Fin.last n) ≤ degAt (extendVertex 𝓖 T) v := by
    intro v
    rw [degAt_extendVertex_last 𝓖 T hn1]
    rcases lt_or_ge v.val n with hv | hv
    · have hvcast : Fin.castSucc (⟨v.val, hv⟩ : Fin n) = v := by ext; simp [Fin.castSucc]
      rw [← hvcast, degAt_extendVertex_castSucc 𝓖 T _ hn1]
      have hd := hdeg (⟨v.val, hv⟩ : Fin n)
      have hle : (t : ℝ) ≤ (degAt 𝓖 (⟨v.val, hv⟩ : Fin n) : ℝ) := by
        have h1 : η * (n : ℝ) ≤ 2 * η * (n : ℝ) := by nlinarith [hη, hnR]
        rw [ht] at ht2
        nlinarith [ht2, hd, h1]
      have hnat : t ≤ degAt 𝓖 (⟨v.val, hv⟩ : Fin n) := by exact_mod_cast hle
      have hnat' : T.card ≤ degAt 𝓖 (⟨v.val, hv⟩ : Fin n)
          + (if (⟨v.val, hv⟩ : Fin n) ∈ T then 1 else 0) := by
        rw [hTcard_eq]
        exact le_trans hnat (Nat.le_add_right _ _)
      exact hnat'
    · have hvlast : v = Fin.last n := by
        ext; simp only [Fin.val_last]; omega
      rw [hvlast, degAt_extendVertex_last 𝓖 T hn1]
  have hkey : (Δ : ℝ) - (t : ℝ) ≤
      ∑ u ∈ (Finset.univ : Finset (Fin n)),
        ((Δ : ℝ) - (degAt (extendVertex 𝓖 T) (Fin.castSucc u) : ℝ)) := by
    set F : Finset (Fin n) := Finset.univ.filter
      (fun u => degAt (extendVertex 𝓖 T) (Fin.castSucc u) < Δ) with hF
    have hFle : (F.card : ℝ) ≤ ∑ u ∈ (Finset.univ : Finset (Fin n)),
        ((Δ : ℝ) - (degAt (extendVertex 𝓖 T) (Fin.castSucc u) : ℝ)) := by
      have h1 : (F.card : ℝ) ≤ ∑ u ∈ F,
          ((Δ : ℝ) - (degAt (extendVertex 𝓖 T) (Fin.castSucc u) : ℝ)) := by
        have hc : (F.card : ℝ) = ∑ _u ∈ F, (1 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [hc]
        refine Finset.sum_le_sum (fun u hu => ?_)
        have hu' : degAt (extendVertex 𝓖 T) (Fin.castSucc u) < Δ :=
          (Finset.mem_filter.mp hu).2
        have h2' : (degAt (extendVertex 𝓖 T) (Fin.castSucc u) : ℝ) + 1 ≤ (Δ : ℝ) := by
          exact_mod_cast hu'
        linarith
      refine le_trans h1 (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)
      intro u _ _
      have h := degAt_extendVertex_le_max h2 hn1 hTmem hTcard_le (Fin.castSucc u)
      have h' : (degAt (extendVertex 𝓖 T) (Fin.castSucc u) : ℝ) ≤ (Δ : ℝ) := by
        rw [hΔ]; exact_mod_cast h
      linarith
    have hFcard : (Δ : ℝ) - (t : ℝ) ≤ (F.card : ℝ) := by
      have hsub : S.filter (fun u => u ∉ T) ⊆ F := by
        intro u hu
        rw [Finset.mem_filter] at hu
        obtain ⟨huS, huT⟩ := hu
        have h1 : degAt 𝓖 u < Δ := by
          have := huS
          rw [hS, Finset.mem_filter] at this
          exact this.2
        rw [hF, Finset.mem_filter]
        exact ⟨Finset.mem_univ u, by
          rw [degAt_extendVertex_castSucc 𝓖 T u hn1, if_neg huT]; exact h1⟩
      have hcardF : (S.filter (fun u => u ∉ T)).card = S.card - T.card := by
        have hsum := Finset.card_filter_add_card_filter_not (s := S) (fun u => u ∈ T)
        have hfil : S.filter (fun u => u ∈ T) = T := by
          ext u
          rw [Finset.mem_filter]
          exact ⟨fun h => h.2, fun h => ⟨hTsub h, h⟩⟩
        rw [hfil] at hsum
        omega
      have h1 : Δ - t ≤ (S.filter (fun u => u ∉ T)).card := by
        rw [hcardF]
        omega
      have h2' : (S.filter (fun u => u ∉ T)).card ≤ F.card := Finset.card_le_card hsub
      have h3 : Δ - t ≤ F.card := le_trans h1 h2'
      have hcast : ((Δ - t : ℕ) : ℝ) = (Δ : ℝ) - (t : ℝ) := Nat.cast_sub htleΔ
      rw [← hcast]
      exact_mod_cast h3
    linarith
  have hsum : 2 * ((hypergraphMaxDegree (extendVertex 𝓖 T) : ℝ)
        - (degAt (extendVertex 𝓖 T) (Fin.last n) : ℝ)) ≤
      ∑ v ∈ (Finset.univ : Finset (Fin (n + 1))),
        ((hypergraphMaxDegree (extendVertex 𝓖 T) : ℝ) - (degAt (extendVertex 𝓖 T) v : ℝ)) := by
    rw [hmaxEq, degAt_extendVertex_last 𝓖 T hn1, hTcard_eq]
    rw [Fin.sum_univ_castSucc]
    rw [degAt_extendVertex_last 𝓖 T hn1, hTcard_eq]
    linarith [hkey]
  have hdegExt' : ∀ v : Fin (n + 1),
      ((hypergraphMaxDegree (extendVertex 𝓖 T) : ℝ) - (degAt (extendVertex 𝓖 T) v : ℝ))
        ≤ 3 * η * ((n + 1 : ℕ) : ℝ) := by
    intro v
    have h := hdegExt v
    have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hc]
    exact h
  have hsum' : ((hypergraphMaxDegree (extendVertex 𝓖 T) : ℝ) -
        (degAt (extendVertex 𝓖 T) (Fin.last n) : ℝ)) ≤
      ∑ v ∈ (Finset.univ.erase (Fin.last n)),
        ((hypergraphMaxDegree (extendVertex 𝓖 T) : ℝ) - (degAt (extendVertex 𝓖 T) v : ℝ)) := by
    have hsplit : (∑ v ∈ (Finset.univ : Finset (Fin (n + 1))),
          ((hypergraphMaxDegree (extendVertex 𝓖 T) : ℝ) - (degAt (extendVertex 𝓖 T) v : ℝ))) =
        ((hypergraphMaxDegree (extendVertex 𝓖 T) : ℝ) -
            (degAt (extendVertex 𝓖 T) (Fin.last n) : ℝ)) +
          ∑ v ∈ (Finset.univ.erase (Fin.last n)),
            ((hypergraphMaxDegree (extendVertex 𝓖 T) : ℝ) - (degAt (extendVertex 𝓖 T) v : ℝ)) := by
      have hse := Finset.sum_erase_add (Finset.univ : Finset (Fin (n + 1)))
        (fun v => ((hypergraphMaxDegree (extendVertex 𝓖 T) : ℝ) -
          (degAt (extendVertex 𝓖 T) v : ℝ))) (Finset.mem_univ (Fin.last n))
      linarith
    linarith [hsum, hsplit]
  have hres := hNc (n + 1) (by omega) (extendVertex 𝓖 T) h2ext hlrExt hdegExt' hev
    ⟨Fin.last n, hmin, hsum'⟩
  rw [hmaxEq] at hres
  exact colorable_famImage (Fin.castSucc_injective n) 𝓖 Δ
    (ErdosFaberLovaszConjecture.Hypergraph.Colorable.restrict (fun e he => Or.inl he) hres)


/-- **Corollary 10.13 (`cor:optcol`) from `GKOStatementFixed`, both parities.**  This is the
statement a consumer of the faithful Theorem 10.8 should use; it packages
`Work.Deep.GKO.corollary_10_13_even` (even case) and
`Work.Deep.GKO.corollary_10_13_odd_from_fixed` (odd case) behind a single parity-free
threshold. -/
theorem corollary_10_13_from_fixed (hGKO : GKOStatementFixed) :
    ∀ p : ℝ, 0 < p → p < 1 → ∃ η₀ ε₀ : ℝ, 0 < η₀ ∧ 0 < ε₀ ∧ ε₀ ≤ p ∧
      (∀ η ε : ℝ, 0 < η → η ≤ η₀ → 0 < ε → ε ≤ ε₀ → ∃ N₀ : ℕ,
        ∀ n ≥ N₀, ∀ 𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin n),
        (∀ e ∈ 𝓖, edgeSize e = 2) →
        SelfLowerRegular 𝓖 Set.univ p ε →
        (∀ v : Fin n, ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) ≤ η * (n : ℝ)) →
        (({v : Fin n | degAt 𝓖 v < hypergraphMaxDegree 𝓖}.ncard : ℝ) ≥
          (hypergraphMaxDegree 𝓖 : ℝ)) →
        𝓖.Colorable (hypergraphMaxDegree 𝓖)) := by
  intro p hp0 hp1
  obtain ⟨ν₁, ε₁, hν₁, hε₁, hε₁p, hmain₁⟩ := corollary_10_13_even hGKO p hp0 hp1
  obtain ⟨η₂, ε₂, hη₂, hε₂, hε₂p, hmain₂⟩ :=
    corollary_10_13_odd_from_fixed hGKO p hp0 hp1
  refine ⟨min ν₁ η₂, min ε₁ ε₂, lt_min hν₁ hη₂, lt_min hε₁ hε₂, ?_, ?_⟩
  · exact le_trans (min_le_left _ _) hε₁p
  · intro η ε hη hη₀ hε hε₀
    have hην₁ : η ≤ ν₁ := le_trans hη₀ (min_le_left _ _)
    have hηη₂ : η ≤ η₂ := le_trans hη₀ (min_le_right _ _)
    have hεε₁ : ε ≤ ε₁ := le_trans hε₀ (min_le_left _ _)
    have hεε₂ : ε ≤ ε₂ := le_trans hε₀ (min_le_right _ _)
    obtain ⟨N₁, hN₁⟩ := hmain₁ η ε hη hην₁ hε hεε₁
    obtain ⟨N₂, hN₂⟩ := hmain₂ η ε hη hηη₂ hε hεε₂
    refine ⟨max N₁ N₂, ?_⟩
    intro n hn 𝓖 h2 hlr hdeg hlow
    by_cases hev : Even n
    · exact hN₁ n (le_trans (le_max_left _ _) hn) hev 𝓖 h2 hlr hdeg hlow
    · exact hN₂ n (le_trans (le_max_right _ _) hn) (Nat.not_even_iff_odd.mp hev) 𝓖
        h2 hlr hdeg hlow

end

end Work.Deep.GKO
