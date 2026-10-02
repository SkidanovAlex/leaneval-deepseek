import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.MultiAbsorbAux

/-!
# The §7 absorption lemmas in multi-hypergraph language

The cone's absorption lemmas (`crossing_absorption`, `internal_absorption`)
extend a batch of matchings by edges of the absorber `R`.  The §7 assembly of
`lem:nibble2` needs them for *multi-hypergraph* matchings, i.e. plain families
`N : Set (Set (Fin n))` whose non-singleton parts are pairwise disjoint.
This module proves those two statements, by running the cone's iteration
engines (`crossing_iter`, `internal_iter`, which only ask for the
pseudorandomness of the input) with ambient hypergraph `𝓜.edgeSet` and
re-assembling the output.
-/

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- The edges of `ofAbs M` that are edges of `R`, for `M` a family of
`R`-edges. -/
theorem ofAbs_subset_R {𝓜 : MultiHypergraph n} {R : Hypergraph (Fin n)}
    {M : Set ↥(MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n))}
    (hM : M ⊆ {e : ↥(MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n)) |
      (e : Set (Fin n)) ∈ R}) :
    ofAbs M ⊆ R := by
  rintro e ⟨x, hx, rfl⟩
  exact hM hx

/-- **Assembly of an absorbing family.**  Given multi-hypergraph matchings `N i`
avoiding `R` and a family `M i` of `R`-matchings, each vertex-disjoint from the
corresponding `N i`, the families `N i ∪ M i` are again multi-hypergraph
matchings, pairwise edge-disjoint, extend `N i`, and every edge added to `N i`
lies in `R`. -/
theorem absorbAssemble {𝓜 : MultiHypergraph n} {R : Hypergraph (Fin n)} {k : ℕ}
    (N : Fin k → Set (Set (Fin n)))
    (hNsub : ∀ i, N i ⊆ MultiHypergraph.edgeSet 𝓜)
    (hNmat : ∀ i, MultiHypergraph.IsMatching 𝓜 (N i))
    (hNdisj : ∀ i j, i ≠ j → EdgeDisjointFam (N i) (N j))
    (hNR : ∀ i, ∀ e ∈ N i, e ∉ R)
    (M : Fin k → Set ↥(MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n)))
    (hMmat : ∀ i, (M i).Pairwise fun a b => Disjoint (a : Set (Fin n)) (b : Set (Fin n)))
    (hMdisj : ∀ i j, i ≠ j → Disjoint (M i) (M j))
    (hMR : ∀ i, M i ⊆ {e : ↥(MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n)) |
      (e : Set (Fin n)) ∈ R})
    (hMdisjN : ∀ i, Disjoint (matchVert (M i)) (matchVert (toAbs (N i) (hNsub i)))) :
    (∀ i, N i ⊆ N i ∪ ofAbs (M i)) ∧
    (∀ i, ∀ e ∈ N i ∪ ofAbs (M i), e ∉ N i → e ∈ R) ∧
    (∀ i, MultiHypergraph.IsMatching 𝓜 (N i ∪ ofAbs (M i))) ∧
    (∀ i j, i ≠ j → EdgeDisjointFam (N i ∪ ofAbs (M i)) (N j ∪ ofAbs (M j))) := by
  classical
  refine ⟨fun i => Set.subset_union_left, ?_, ?_, ?_⟩
  · intro i e he hne
    rw [Set.mem_union] at he
    rcases he with h | h
    · exact absurd h hne
    · exact ofAbs_subset_R (hMR i) h
  · intro i
    refine ⟨?_, ?_⟩
    · intro e he
      rw [Set.mem_union] at he
      rcases he with h | h
      · exact hNsub i h
      · exact ofAbs_subset 𝓜 (M i) h
    · intro e1 he1 e2 he2 hne
      rw [Set.mem_union] at he1 he2
      rcases he1 with h1 | h1 <;> rcases he2 with h2 | h2
      · exact (hNmat i).2 h1 h2 hne
      · obtain ⟨hE2, hm2⟩ := mem_ofAbs.mp h2
        refine Set.disjoint_left.mpr fun x hx1 hx2 => ?_
        have hx1' : x ∈ matchVert (toAbs (N i) (hNsub i)) := by
          rw [matchVert_toAbs]; exact mem_famVert.mpr ⟨e1, h1, hx1⟩
        have hx2' : x ∈ matchVert (M i) := mem_matchVert.mpr ⟨⟨e2, hE2⟩, hm2, hx2⟩
        exact (Set.disjoint_left.mp (hMdisjN i)) hx2' hx1'
      · obtain ⟨hE1, hm1⟩ := mem_ofAbs.mp h1
        refine Set.disjoint_left.mpr fun x hx1 hx2 => ?_
        have hx2' : x ∈ matchVert (toAbs (N i) (hNsub i)) := by
          rw [matchVert_toAbs]; exact mem_famVert.mpr ⟨e2, h2, hx2⟩
        have hx1' : x ∈ matchVert (M i) := mem_matchVert.mpr ⟨⟨e1, hE1⟩, hm1, hx1⟩
        exact (Set.disjoint_left.mp (hMdisjN i)) hx1' hx2'
      · obtain ⟨hE1, hm1⟩ := mem_ofAbs.mp h1
        obtain ⟨hE2, hm2⟩ := mem_ofAbs.mp h2
        exact (hMmat i) hm1 hm2 (fun h => hne (congrArg Subtype.val h))
  · intro i j hij
    rw [EdgeDisjointFam, Set.disjoint_left]
    rintro e ⟨he1, h2e⟩ ⟨he2, -⟩
    rw [Set.mem_union] at he1 he2
    rcases he1 with h1 | h1 <;> rcases he2 with h2 | h2
    · exact (Set.disjoint_left.mp (hNdisj i j hij)) ⟨h1, h2e⟩ ⟨h2, h2e⟩
    · exact hNR i e h1 (ofAbs_subset_R (hMR j) h2)
    · exact hNR j e h2 (ofAbs_subset_R (hMR i) h1)
    · obtain ⟨hE1, hm1⟩ := mem_ofAbs.mp h1
      obtain ⟨hE2, hm2⟩ := mem_ofAbs.mp h2
      exact (Set.disjoint_left.mp (hMdisj i j hij)) hm1
        (show (⟨e, hE1⟩ : ↥(MultiHypergraph.edgeSet 𝓜)) ∈ M j from by
          rw [show (⟨e, hE1⟩ : ↥(MultiHypergraph.edgeSet 𝓜)) = ⟨e, hE2⟩ from Subtype.ext rfl]
          exact hm2)

/-- **Counting for nearly-perfect coverage.**  If each matching of a family
`N : Fin k → Set (Set (Fin n))` misses at most the point `u0 i` of `U`, and the
points `u0 i` are distinct, then every vertex of `U` is covered by all but at
most one matching. -/
theorem nearlyPerfect_count {k : ℕ} {N : Fin k → Set (Set (Fin n))} {U : Set (Fin n)}
    {u0 : Fin k → Fin n} (hinj : Function.Injective u0)
    (hmiss : ∀ i, ∀ x ∈ U, x ∉ famVert (N i) → x = u0 i) :
    ∀ u ∈ U, (({i : Fin k | u ∈ famVert (N i)} : Set (Fin k)).ncard : ℝ) + 1 ≥ (k : ℝ) := by
  intro u hu
  have hsub : (({i : Fin k | u ∈ famVert (N i)} : Set (Fin k)))ᶜ ⊆ {i : Fin k | u = u0 i} := by
    intro i hi
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hi ⊢
    exact hmiss i u hu hi
  have hb : ({i : Fin k | u = u0 i} : Set (Fin k)).ncard ≤ 1 := by
    rw [Set.ncard_le_one]
    intro a ha b hb
    simp only [Set.mem_setOf_eq] at ha hb
    exact hinj (ha.symm.trans hb)
  have hb1 : (({i : Fin k | u ∈ famVert (N i)} : Set (Fin k)))ᶜ.ncard ≤ 1 :=
    le_trans (Set.ncard_le_ncard hsub) hb
  have hsum := Set.ncard_add_ncard_compl ({i : Fin k | u ∈ famVert (N i)} : Set (Fin k))
  rw [Nat.card_fin] at hsum
  have hsumR : (({i : Fin k | u ∈ famVert (N i)} : Set (Fin k)).ncard : ℝ)
      + ((({i : Fin k | u ∈ famVert (N i)} : Set (Fin k)))ᶜ.ncard : ℝ) = (k : ℝ) := by
    have hc := congrArg (Nat.cast : ℕ → ℝ) hsum
    push_cast at hc
    exact hc
  have hb1R : ((({i : Fin k | u ∈ famVert (N i)} : Set (Fin k)))ᶜ.ncard : ℝ) ≤ 1 := by
    exact_mod_cast hb1
  linarith

/-- **The crossing absorption in multi-hypergraph language.** -/
theorem crossing_absorption_multi {𝓜 : MultiHypergraph n} {R : Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {U : Set (Fin n)} {ρ ε γ κ ξ : ℝ} {k : ℕ}
    (hm : CrossingMargins n ρ ε γ κ ξ)
    (hUcard : (U.ncard : ℝ) ≤ (n : ℝ) / 100)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤
      (degAt (incidentTwo (MultiHypergraph.pow2 𝓜) U) u : ℝ))
    (habs : IsAbsorber (incidentTwo (MultiHypergraph.pow2 𝓜) U) R 𝓥 ρ (10 * γ) ξ)
    (hU𝓥 : U ∈ 𝓥)
    (N : Fin k → Set (Set (Fin n)))
    (hNmat : ∀ i, MultiHypergraph.IsMatching 𝓜 (N i))
    (hNdisj : ∀ i j, i ≠ j → EdgeDisjointFam (N i) (N j))
    (hNR : ∀ i, ∀ e ∈ N i, e ∉ R)
    (hpseudo : ∀ i, PseudoRandomFam (N i) (absorberFam R U ∪ {U, ∅}) γ κ)
    (hk : (k : ℝ) ≤ κ * (n : ℝ)) :
    ∃ N' : Fin k → Set (Set (Fin n)),
      (∀ i, N i ⊆ N' i) ∧
      (∀ i, ∀ e ∈ N' i, e ∉ N i → e ∈ R) ∧
      (∀ i, MultiHypergraph.IsMatching 𝓜 (N' i)) ∧
      (∀ i j, i ≠ j → EdgeDisjointFam (N' i) (N' j)) ∧
      (∀ i, CoversFamMulti (N' i) U) := by
  classical
  have hsub : ∀ i, N i ⊆ MultiHypergraph.edgeSet 𝓜 := fun i => (hNmat i).1
  have hI := incidentTwo_edgeSet 𝓜 U
  obtain ⟨M, hMmat, hMdisj, hMR, hcov, hMdisjN⟩ :=
    crossing_iter (𝓗 := (MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n)))
      (R := R) (𝓥 := 𝓥) (U := U) hm hUcard (by rw [hI]; exact hUdeg)
      (by rw [hI]; exact habs) hU𝓥 k (fun i => toAbs (N i) (hsub i))
      (fun i => (pseudoRandom_toAbs_iff (hsub i) (absorberFam R U ∪ {U, ∅}) γ κ).mpr
        (hpseudo i)) hk
  obtain ⟨hsub', hadd, hmat', hdisj'⟩ :=
    absorbAssemble N hsub hNmat hNdisj hNR M hMmat hMdisj hMR hMdisjN
  refine ⟨fun i => N i ∪ ofAbs (M i), hsub', hadd, hmat', hdisj', ?_⟩
  intro i u hu
  by_cases h : u ∈ famVert (N i)
  · exact famVert_mono Set.subset_union_left h
  · have hu' : u ∈ U \ matchVert (toAbs (N i) (hsub i)) := by
      refine ⟨hu, ?_⟩
      rw [matchVert_toAbs]
      exact h
    obtain ⟨e, he, hue⟩ := mem_matchVert.mp (hcov i hu')
    exact famVert_mono Set.subset_union_right
      (mem_famVert.mpr ⟨(e : Set (Fin n)), ⟨e, he, rfl⟩, hue⟩)

/-- **The internal absorption in multi-hypergraph language.** -/
theorem internal_absorption_multi {𝓜 : MultiHypergraph n} {R : Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {U S : Set (Fin n)} {ρ ε γ κ ξ : ℝ} {B k : ℕ}
    (hm : InternalMargins n ρ ε γ κ ξ)
    (hmatch : InternalMatchingInput n B)
    (hUlow : (n : ℝ) / 100 ≤ (U.ncard : ℝ))
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤
      (degAt (incidentTwo (MultiHypergraph.pow2 𝓜) U) u : ℝ))
    (habs : IsAbsorber (incidentTwo (MultiHypergraph.pow2 𝓜) U) R 𝓥 ρ (10 * γ) ξ)
    (hU𝓥 : U ∈ 𝓥)
    (hR2 : ∀ e ∈ R, edgeSize e = 2)
    (hB : (B : ℝ) ≤ ρ ^ 2 * (γ * (n : ℝ)) / 400)
    (hS : γ * (n : ℝ) ≤ (S.ncard : ℝ)) (hSsub : S ⊆ U)
    (N : Fin k → Set (Set (Fin n)))
    (hNmat : ∀ i, MultiHypergraph.IsMatching 𝓜 (N i))
    (hNdisj : ∀ i j, i ≠ j → EdgeDisjointFam (N i) (N j))
    (hNR : ∀ i, ∀ e ∈ N i, e ∉ R)
    (hpseudo : ∀ i, PseudoRandomFam (N i) (absorberFam R U ∪ {U, S}) γ κ)
    (hk : (k : ℝ) ≤ κ * (n : ℝ)) :
    ∃ N' : Fin k → Set (Set (Fin n)),
      (∀ i, N i ⊆ N' i) ∧
      (∀ i, ∀ e ∈ N' i, e ∉ N i → e ∈ R) ∧
      (∀ i, MultiHypergraph.IsMatching 𝓜 (N' i)) ∧
      (∀ i j, i ≠ j → EdgeDisjointFam (N' i) (N' j)) ∧
      (((U.ncard : ℝ) ≤ (1 - 2 * ε) * (n : ℝ)) → ∀ i, CoversFamMulti (N' i) U) ∧
      (((1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ)) → NearlyPerfectCoverageFam N' U S) := by
  classical
  have hsub : ∀ i, N i ⊆ MultiHypergraph.edgeSet 𝓜 := fun i => (hNmat i).1
  have hI := incidentTwo_edgeSet 𝓜 U
  have hUdeg' : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤
      (degAt (incidentTwo (MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n)) U) u : ℝ) := by
    intro u hu; rw [hI]; exact hUdeg u hu
  have habs' : IsAbsorber (incidentTwo (MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n)) U) R
      𝓥 ρ (10 * γ) ξ := by rw [hI]; exact habs
  have hpseudo' : ∀ i, PseudoRandom (toAbs (N i) (hsub i)) (absorberFam R U ∪ {U, S}) γ κ :=
    fun i => (pseudoRandom_toAbs_iff (hsub i) (absorberFam R U ∪ {U, S}) γ κ).mpr (hpseudo i)
  by_cases hUA : (U.ncard : ℝ) ≤ (1 - 2 * ε) * (n : ℝ)
  · obtain ⟨M, u0, hMmat, hMdisj, hMR, hMdisjN, hcov, huU, huN, hinj, hExtra⟩ :=
      internal_iter (𝓗 := (MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n)))
        (R := R) (U := U) (S := S) (γ := γ) (κ := κ)
        (Extra := fun _ N M => Covers M (U \ matchVert N))
        (fun Nk used P hused hP hps => by
          obtain ⟨uu, huU, huN, huP, Ms, hmat', hR', hdisj', hcov'⟩ :=
            internal_step_A2 (𝓗 := (MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n)))
              hm hmatch hUlow hUdeg' habs' hU𝓥 hps hused hR2 hB hUA hP
          exact ⟨uu, huU, huN, huP, Ms, hmat', hR', hdisj', fun x hx => hcov' hx.1, hcov'⟩)
        k (fun i => toAbs (N i) (hsub i)) hpseudo' hk
    obtain ⟨hsub', hadd, hmat', hdisj'⟩ :=
      absorbAssemble N hsub hNmat hNdisj hNR M hMmat hMdisj hMR hMdisjN
    refine ⟨fun i => N i ∪ ofAbs (M i), hsub', hadd, hmat', hdisj', ?_, ?_⟩
    · intro _ i u hu
      by_cases h : u ∈ famVert (N i)
      · exact famVert_mono Set.subset_union_left h
      · have hu' : u ∈ U \ matchVert (toAbs (N i) (hsub i)) := by
          refine ⟨hu, ?_⟩
          rw [matchVert_toAbs]
          exact h
        obtain ⟨e, he, hue⟩ := mem_matchVert.mp (hExtra i hu')
        exact famVert_mono Set.subset_union_right
          (mem_famVert.mpr ⟨(e : Set (Fin n)), ⟨e, he, rfl⟩, hue⟩)
    · intro hc
      exact absurd hc (not_lt.mpr hUA)
  · have hgt : (1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ) := not_le.mp hUA
    obtain ⟨M, u0, hMmat, hMdisj, hMR, hMdisjN, hcov, huU, huN, hinj, hExtra⟩ :=
      internal_iter (𝓗 := (MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n)))
        (R := R) (U := U) (S := S) (γ := γ) (κ := κ)
        (Extra := fun u _ _ => u ∈ S)
        (fun Nk used P hused hP hps => by
          obtain ⟨uu, huS, huN, huP, Ms, hmat', hR', hdisj', hcov'⟩ :=
            internal_step_B2 (𝓗 := (MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n)))
              hm hmatch hUlow hUdeg' habs' hU𝓥 hps hused hR2 hB hS hSsub hP
          exact ⟨uu, hSsub huS, huN, huP, Ms, hmat', hR', hdisj', hcov', huS⟩)
        k (fun i => toAbs (N i) (hsub i)) hpseudo' hk
    obtain ⟨hsub', hadd, hmat', hdisj'⟩ :=
      absorbAssemble N hsub hNmat hNdisj hNR M hMmat hMdisj hMR hMdisjN
    -- every vertex of `U` not covered by `N i ∪ M i` is the defect `u0 i`
    have hmiss : ∀ i, ∀ x ∈ U, x ∉ famVert (N i ∪ ofAbs (M i)) → x = u0 i := by
      intro i x hxU hx
      have hxN : x ∉ famVert (N i) := fun h => hx (famVert_mono Set.subset_union_left h)
      have hxM : x ∉ matchVert (M i) := fun h =>
        hx (famVert_mono Set.subset_union_right (by rw [famVert_ofAbs]; exact h))
      have hmA : x ∈ U \ matchVert (toAbs (N i) (hsub i)) := by
        refine ⟨hxU, ?_⟩
        rw [matchVert_toAbs]
        exact hxN
      by_contra hne
      exact hxM (hcov i ⟨hmA, by simpa [Set.mem_singleton_iff] using hne⟩)
    refine ⟨fun i => N i ∪ ofAbs (M i), hsub', hadd, hmat', hdisj', ?_, ?_⟩
    · intro hc
      exact absurd hc (not_le_of_gt hgt)
    · intro _
      refine ⟨?_, ?_, ?_⟩
      · intro u hu
        have hc := nearlyPerfect_count (N := fun i => N i ∪ ofAbs (M i)) hinj hmiss u hu
        simpa [Fintype.card_fin] using hc
      · intro i x hx
        have hxu : x = u0 i := hmiss i x hx.1 hx.2
        rw [hxu]
        exact hExtra i
      · intro i
        have hsub1 : U \ famVert (N i ∪ ofAbs (M i)) ⊆ ({u0 i} : Set (Fin n)) := by
          intro x hx
          rw [Set.mem_singleton_iff]
          exact hmiss i x hx.1 hx.2
        exact le_trans (Set.ncard_le_ncard hsub1) (le_of_eq (Set.ncard_singleton _))

end

end ErdosFaberLovaszConjecture
