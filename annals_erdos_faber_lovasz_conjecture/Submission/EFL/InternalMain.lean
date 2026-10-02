import Submission.EFL.InternalStepB

/-!
# §7.2: the internal absorption lemma (`internal-absorption-lemma`)

This module assembles the two cases of §7.2 into the paper's Lemma 7.2:
given a family `N_1, …, N_k` (`k ≤ κn`) of edge-disjoint matchings that are
absorbable by pseudorandomness (with respect to `𝓕(R) ∪ {U,S}`), one can
extend them by edges of `R` so that they are edge-disjoint and

* if `|U| ≤ (1-2ε)n`: they have perfect coverage of `U`;
* otherwise (`|U| > (1-2ε)n`, where `|S| ≥ γn`): they have nearly-perfect
  coverage of `U` with defects in `S`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-- **Lemma `internal-absorption-lemma`** (Lemma 7.2 of the paper). -/
theorem internal_absorption {𝓗 R : Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {U S : Set (Fin n)} {ρ ε γ κ ξ : ℝ} {B : ℕ}
    (hm : InternalMargins n ρ ε γ κ ξ)
    (hmatch : InternalMatchingInput n B)
    (hUlow : (n : ℝ) / 100 ≤ (U.ncard : ℝ))
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (habs : IsAbsorber (incidentTwo 𝓗 U) R 𝓥 ρ (10 * γ) ξ) (hU𝓥 : U ∈ 𝓥)
    (hR2 : ∀ e ∈ R, edgeSize e = 2)
    (hB : (B : ℝ) ≤ ρ ^ 2 * (γ * (n : ℝ)) / 400)
    (hS : γ * (n : ℝ) ≤ (S.ncard : ℝ)) (hSsub : S ⊆ U)
    {k : ℕ} (N : Fin k → Set 𝓗)
    (hPseudo : ∀ i, PseudoRandom (N i) (absorberFam R U ∪ {U, S}) γ κ)
    (hNR : ∀ i, ∀ e ∈ N i, (e : Set (Fin n)) ∉ R)
    (hNmat : ∀ i, IsMatching 𝓗 (N i))
    (hNdisj : ∀ i j, i ≠ j → Disjoint (N i) (N j))
    (hk : (k : ℝ) ≤ κ * (n : ℝ)) :
    ∃ N' : Fin k → Set 𝓗,
      (∀ i, N i ⊆ N' i) ∧
      (∀ i, ∀ e ∈ N' i, e ∉ N i → (e : Set (Fin n)) ∈ R) ∧
      (∀ i, IsMatching 𝓗 (N' i)) ∧
      (∀ i j, i ≠ j → Disjoint (N' i) (N' j)) ∧
      (((U.ncard : ℝ) ≤ (1 - 2 * ε) * (n : ℝ)) → PerfectCoverage N' U) ∧
      (((1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ)) → NearlyPerfectCoverage N' U S) := by
  classical
  by_cases hUA : (U.ncard : ℝ) ≤ (1 - 2 * ε) * (n : ℝ)
  · -- Case A: `|U| ≤ (1-2ε)n`, the absorption matchings cover `U i = U ∖ V(N i)`
    obtain ⟨Nabs, u, hmat, hdisj, hRN, hdisjN, hcov, hUmem, hNmem, hinj, hExtra⟩ :=
      internal_iter (Extra := fun _ N Nabs => Covers Nabs (U \ matchVert N))
        (fun N used P hdeg hP hps => by
          obtain ⟨uu, huU, huN, huP, Nabss, hmat', hR', hdisj', hcov'⟩ :=
            internal_step_A2 hm hmatch hUlow hUdeg habs hU𝓥 hps hdeg hR2 hB hUA hP
          exact ⟨uu, huU, huN, huP, Nabss, hmat', hR', hdisj', fun x hx => hcov' hx.1, hcov'⟩)
        k N hPseudo hk
    set N' : Fin k → Set 𝓗 := fun i => N i ∪ Nabs i with hN'def
    have hsub1 : ∀ i, N i ⊆ N' i := fun i e he => by
      simp only [hN'def, Set.mem_union]; exact Or.inl he
    have hsub2 : ∀ i, Nabs i ⊆ N' i := fun i e he => by
      simp only [hN'def, Set.mem_union]; exact Or.inr he
    refine ⟨N', hsub1, ?_, ?_, ?_, ?_, ?_⟩
    · intro i e he hne
      have h2 : e ∈ N i ∨ e ∈ Nabs i := by simpa only [hN'def, Set.mem_union] using he
      rcases h2 with h2 | h2
      · exact absurd h2 hne
      · exact hRN i h2
    · intro i
      simp only [hN'def]
      exact isMatching_union (hNmat i) (hmat i) (hdisjN i).symm
    · intro i j hij
      rw [Set.disjoint_left]
      intro e hei hej
      have hi : e ∈ N i ∨ e ∈ Nabs i := by simpa only [hN'def, Set.mem_union] using hei
      have hj : e ∈ N j ∨ e ∈ Nabs j := by simpa only [hN'def, Set.mem_union] using hej
      rcases hi with hi | hi <;> rcases hj with hj | hj
      · exact (Set.disjoint_left.mp (hNdisj i j hij)) hi hj
      · exact (hNR i e hi) (hRN j hj)
      · exact (hNR j e hj) (hRN i hi)
      · exact (Set.disjoint_left.mp (hdisj i j hij)) hi hj
    · intro _ i x hx
      by_cases hxi : x ∈ matchVert (N i)
      · exact matchVert_mono (hsub1 i) hxi
      · exact matchVert_mono (hsub2 i) (hExtra i ⟨hx, hxi⟩)
    · intro hc
      exact absurd hc (not_lt.mpr hUA)
  · -- Case B: `|U| > (1-2ε)n`, the defects lie in `S` and are distinct
    obtain ⟨Nabs, u, hmat, hdisj, hRN, hdisjN, hcov, hUmem, hNmem, hinj, hExtra⟩ :=
      internal_iter (Extra := fun u _ _ => u ∈ S)
        (fun N used P hdeg hP hps => by
          obtain ⟨uu, huS, huN, huP, Nabss, hmat', hR', hdisj', hcov'⟩ :=
            internal_step_B2 hm hmatch hUlow hUdeg habs hU𝓥 hps hdeg hR2 hB hS hSsub hP
          exact ⟨uu, hSsub huS, huN, huP, Nabss, hmat', hR', hdisj', hcov', huS⟩)
        k N hPseudo hk
    set N' : Fin k → Set 𝓗 := fun i => N i ∪ Nabs i with hN'def
    have hsub1 : ∀ i, N i ⊆ N' i := fun i e he => by
      simp only [hN'def, Set.mem_union]; exact Or.inl he
    have hsub2 : ∀ i, Nabs i ⊆ N' i := fun i e he => by
      simp only [hN'def, Set.mem_union]; exact Or.inr he
    have hmiss : ∀ i, ∀ x ∈ U, x ∉ matchVert (N' i) → x = u i := by
      intro i x hxU hxnot
      by_cases hxi : x = u i
      · exact hxi
      · exfalso
        have h3 : x ∉ matchVert (N i ∪ Nabs i) := by simpa only [hN'def] using hxnot
        rw [matchVert_union] at h3
        exact (fun h => h3 (Or.inr h)) (hcov i ⟨⟨hxU, fun h => h3 (Or.inl h)⟩, hxi⟩)
    refine ⟨N', hsub1, ?_, ?_, ?_, (fun hc => absurd hc hUA), ?_⟩
    · intro i e he hne
      have h2 : e ∈ N i ∨ e ∈ Nabs i := by simpa only [hN'def, Set.mem_union] using he
      rcases h2 with h2 | h2
      · exact absurd h2 hne
      · exact hRN i h2
    · intro i
      simp only [hN'def]
      exact isMatching_union (hNmat i) (hmat i) (hdisjN i).symm
    · intro i j hij
      rw [Set.disjoint_left]
      intro e hei hej
      have hi : e ∈ N i ∨ e ∈ Nabs i := by simpa only [hN'def, Set.mem_union] using hei
      have hj : e ∈ N j ∨ e ∈ Nabs j := by simpa only [hN'def, Set.mem_union] using hej
      rcases hi with hi | hi <;> rcases hj with hj | hj
      · exact (Set.disjoint_left.mp (hNdisj i j hij)) hi hj
      · exact (hNR i e hi) (hRN j hj)
      · exact (hNR j e hj) (hRN i hi)
      · exact (Set.disjoint_left.mp (hdisj i j hij)) hi hj
    · intro _
      refine ⟨?_, fun i x hx => (hmiss i x hx.1 hx.2).symm ▸ hExtra i, ?_⟩
      intro uU huU
      have hbad : (({i : Fin k | uU ∉ matchVert (N' i)} : Set (Fin k))).ncard ≤ 1 :=
        (Set.ncard_le_one (s := {i : Fin k | uU ∉ matchVert (N' i)}) (Set.toFinite _)).mpr
          (fun i hi j hj => hinj ((hmiss i uU huU hi).symm.trans (hmiss j uU huU hj)))
      have hsum : (({i : Fin k | uU ∈ matchVert (N' i)} : Set (Fin k))).ncard
          + (({i : Fin k | uU ∉ matchVert (N' i)} : Set (Fin k))).ncard = k := by
        have hdisj : Disjoint ({i : Fin k | uU ∈ matchVert (N' i)} : Set (Fin k))
            {i : Fin k | uU ∉ matchVert (N' i)} :=
          Set.disjoint_left.mpr (fun i h1 h2 => h2 h1)
        have hun : ({i : Fin k | uU ∈ matchVert (N' i)} : Set (Fin k))
            ∪ {i : Fin k | uU ∉ matchVert (N' i)} = Set.univ := by
          ext i; by_cases h : uU ∈ matchVert (N' i) <;> simp [h]
        have h := Set.ncard_union_eq hdisj
        rw [hun, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h
        exact h.symm
      have hsumR : ((({i : Fin k | uU ∈ matchVert (N' i)} : Set (Fin k))).ncard : ℝ)
          = (k : ℝ) - ((({i : Fin k | uU ∉ matchVert (N' i)} : Set (Fin k))).ncard : ℝ) := by
        have h := congrArg (Nat.cast : ℕ → ℝ) hsum
        push_cast at h
        linarith
      have hbadR : ((({i : Fin k | uU ∉ matchVert (N' i)} : Set (Fin k))).ncard : ℝ) ≤ 1 := by
        exact_mod_cast hbad
      simp only [Fintype.card_fin]
      linarith
      · intro i
        rw [Set.ncard_le_one (s := U \ matchVert (N' i)) (Set.toFinite _)]
        intro x hx y hy
        exact (hmiss i x hx.1 hx.2).trans (hmiss i y hy.1 hy.2).symm

end

end ErdosFaberLovaszConjecture
