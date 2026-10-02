import Submission.EFL.InternalStep

/-!
# §7.2, part 2: the case `|U| > (1-2ε)n` and the iteration

This module completes the proof of the paper's `internal-absorption-lemma`
(Lemma 7.2) begun in `InternalStep.lean`:

* `internal_matching_of` — the perfect matching on a set `W` with
  `(U ∖ V(N)) ∖ {ul} ⊆ W ⊆ U ∖ V(N)` and `W` even (the shared core of both
  cases of the one-step lemma, extracted from `internal_step_A`);
* `internal_pick_A` / `internal_pick_B` — the choice of a *new* defect vertex
  `u ∈ (U ∖ V(N)) ∖ P` (in case B additionally `u ∈ S`), where `P` is the set
  of defects already chosen;
* `internal_step_A2` / `internal_step_B2` — the one-step lemma in the two
  cases `|U| ≤ (1-2ε)n` and `|U| > (1-2ε)n`, in the form used by the
  iteration (they also return the defect vertex `u` and avoid `P`);
* `internal_iter_A` / `internal_iter_B` — the iterations, with the
  accumulated `used` (the union of the previous absorption matchings) and the
  accumulated defect set `P`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-! ## The perfect matching of `restr (R ∖ used) W` -/

/-- **The matching on `W`.**  If `(U ∖ V(N)) ∖ {ul} ⊆ W ⊆ U ∖ V(N)`, `W` has
an even number of vertices and `|W| ≥ γn/400`, then the available edges of `R`
inside `W` contain a matching covering `W` (Proposition `internal-matching-prop`
plus `internal_degree_chain` and the upper-regularity of `R`). -/
theorem internal_matching_of {𝓗 R used : Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {U S : Set (Fin n)} {N : Set 𝓗} {ρ ε γ κ ξ : ℝ} {B : ℕ}
    (hm : InternalMargins n ρ ε γ κ ξ)
    (hmatch : InternalMatchingInput n B)
    (hUlow : (n : ℝ) / 100 ≤ (U.ncard : ℝ))
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (habs : IsAbsorber (incidentTwo 𝓗 U) R 𝓥 ρ (10 * γ) ξ) (hU𝓥 : U ∈ 𝓥)
    (hpseudo : PseudoRandom N (absorberFam R U ∪ {U, S}) γ κ)
    (hused : ∀ v : Fin n, ((nbrs used v).ncard : ℝ) ≤ κ * (n : ℝ))
    (hR2 : ∀ e ∈ R, edgeSize e = 2)
    (hB : (B : ℝ) ≤ ρ ^ 2 * (γ * (n : ℝ)) / 400)
    {W : Set (Fin n)} {ul : Fin n}
    (hWle : W ⊆ U \ matchVert N) (hWeven : Even W.ncard)
    (hWlow : γ * (n : ℝ) / 400 ≤ (W.ncard : ℝ))
    (hWge : (U \ matchVert N) \ {ul} ⊆ W) :
    ∃ M : Set 𝓗, IsMatching 𝓗 M ∧
      (∀ e ∈ M, (e : Set (Fin n)) ∈ R ∧ (e : Set (Fin n)) ∉ used) ∧
      (∀ e ∈ M, (e : Set (Fin n)) ⊆ W) ∧
      Disjoint (matchVert M) (matchVert N) ∧
      (∀ w ∈ W, ∃ e ∈ M, w ∈ (e : Set (Fin n))) := by
  classical
  have hRsub : R ⊆ incidentTwo 𝓗 U := habs.1
  have hdeg : ∀ w ∈ W, 3 * ρ * (W.ncard : ℝ) / 4
      ≤ (degIn (restr (R \ used) W) W w : ℝ) := by
    intro w hw
    rw [degIn_restr hw]
    exact internal_degree_chain hm hUlow hUdeg habs hU𝓥 hpseudo hused hWle hWge hw
  have hξ0 : (0 : ℝ) ≤ 400 * ξ / γ :=
    div_nonneg (mul_nonneg (by norm_num) (le_of_lt hm.hξ)) (le_of_lt hm.hγ)
  have hξρ : 10 * (400 * ξ / γ) ≤ ρ := by
    have h2 : 10 * (400 * ξ / γ) = 4000 * ξ / γ := by ring
    rw [h2, div_le_iff₀ hm.hγ]
    have h3 : 4000 * ξ ≤ ρ * γ := by rw [mul_comm ρ γ]; exact hm.hξγρ
    exact h3
  have hB' : (B : ℝ) ≤ ρ ^ 2 * (W.ncard : ℝ) := by
    have h := hB
    have h2 : ρ ^ 2 * (γ * (n : ℝ)) / 400 ≤ ρ ^ 2 * (W.ncard : ℝ) := by
      have h3 : (0 : ℝ) ≤ ρ ^ 2 := sq_nonneg ρ
      nlinarith [hWlow, h3]
    linarith [h, h2]
  have hsub : ∀ e ∈ restr (R \ used) W, e ⊆ W := fun e he => he.2
  have h2' : ∀ e ∈ restr (R \ used) W, edgeSize e = 2 :=
    restr_edgeSize (fun e he => hR2 e he.1)
  have hRsub' : restr (R \ used) W ⊆ 𝓗 :=
    fun e he => incidentTwo_subset_self (hRsub (he.1).1)
  have hreg : ∀ S T : Finset (Fin n), S ⊆ sfin W → T ⊆ sfin W → Disjoint S T →
      (400 * ξ / γ) * (W.ncard : ℝ) ≤ (S.card : ℝ) →
      (400 * ξ / γ) * (W.ncard : ℝ) ≤ (T.card : ℝ) →
      (edgeCount (restr (R \ used) W) S T : ℝ) ≤
        (ρ + 400 * ξ / γ) * (S.card : ℝ) * (T.card : ℝ) := by
    intro S T hS hT hdisj hSc hTc
    have haux : ξ * (n : ℝ) ≤ (400 * ξ / γ) * (W.ncard : ℝ) := by
      have h2 : (400 * ξ / γ) * (γ * (n : ℝ) / 400) = ξ * (n : ℝ) := by
        field_simp [ne_of_gt hm.hγ]
      rw [← h2]
      exact mul_le_mul_of_nonneg_left hWlow hξ0
    have hξn : ξ * (n : ℝ) ≤ (S.card : ℝ) := le_trans haux hSc
    have hξn' : ξ * (n : ℝ) ≤ (T.card : ℝ) := le_trans haux hTc
    have hmono : (edgeCount (restr (R \ used) W) S T : ℝ) ≤ (edgeCount R S T : ℝ) := by
      exact_mod_cast edgeCount_mono (fun (e : Set (Fin n)) (he : e ∈ restr (R \ used) W) =>
        he.1.1) S T
    have hmain := habs.2.2 S T hdisj hξn hξn'
    have hcard : (edgeCount (incidentTwo 𝓗 U) S T : ℝ) ≤ (S.card : ℝ) * (T.card : ℝ) := by
      have h := edgeCount_le_card_mul (incidentTwo 𝓗 U) S T
      exact_mod_cast h
    have hξξ' : ξ ≤ 400 * ξ / γ := by
      rw [le_div_iff₀ hm.hγ]
      nlinarith [hm.hξ, hm.hγhalf, le_of_lt hm.hξ]
    nlinarith [hmono, hmain, hcard, le_of_lt hm.hρ, hξξ']
  obtain ⟨M, hMm, hMR, hMcov⟩ := internal_matching_step hm.hρ hm.hρ1 hξ0 hξρ hB' hmatch
    hWeven hRsub' hsub h2' hdeg hreg
  refine ⟨M, hMm, ?_, ?_, ?_, ?_⟩
  · intro e he
    have h := hMR e he
    exact ⟨h.1.1, h.1.2⟩
  · intro e he
    exact (hMR e he).2
  · rw [Set.disjoint_left]
    intro x hx hxN
    rw [mem_matchVert] at hx
    obtain ⟨e, he, hxe⟩ := hx
    exact (hWle ((hMR e he).2 hxe)).2 hxN
  · intro w hw
    exact hMcov w hw

end

variable {n : ℕ}

/-- A family that `∃`-covers `W` covers it in the sense of `Covers`. -/
theorem covers_of_exists {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} {W : Set (Fin n)}
    (h : ∀ w ∈ W, ∃ e ∈ M, w ∈ (e : Set (Fin n))) : Covers M W :=
  fun w hw => by rw [mem_matchVert]; exact h w hw

/-! ## A lower bound for `γn` -/

/-- From the paper's `ρ ≪ 1` and `1/n ≪ γ` (here `2000 ≤ γρn`, `ρ ≤ 1`) we get
`γn ≥ 2000`. -/
theorem gamma_mul_n_ge {γ ρ : ℝ} (hγ : 0 ≤ γ) (hρ1 : ρ ≤ 1)
    (hn0 : 0 ≤ (n : ℝ)) (hnbig : 2000 ≤ γ * ρ * (n : ℝ)) :
    (2000 : ℝ) ≤ γ * (n : ℝ) := by
  have h1 : ρ * (n : ℝ) ≤ (n : ℝ) := by simpa using mul_le_mul_of_nonneg_right hρ1 hn0
  have h2 : γ * (ρ * (n : ℝ)) ≤ γ * (n : ℝ) := mul_le_mul_of_nonneg_left h1 hγ
  linarith [hnbig, h2]

/-! ## Choosing a fresh defect vertex -/

/-- **The choice of the defect vertex in the case `|U| ≤ (1-2ε)n`.**  There is a
vertex `u ∈ (U ∖ V(N)) ∖ P` (the defect is arbitrary there; it only has to be
new). -/
theorem internal_pick_A {𝓗 R used : Hypergraph (Fin n)}
    {U S : Set (Fin n)} {N : Set 𝓗} {P : Finset (Fin n)} {ρ ε γ κ ξ : ℝ}
    (hm : InternalMargins n ρ ε γ κ ξ)
    (hUlow : (n : ℝ) / 100 ≤ (U.ncard : ℝ))
    (hpseudo : PseudoRandom N (absorberFam R U ∪ {U, S}) γ κ)
    (hP : (P.card : ℝ) ≤ κ * (n : ℝ)) :
    ∃ u : Fin n, u ∈ U ∧ u ∉ matchVert N ∧ u ∉ P := by
  classical
  have hAlow := internal_A_lower (used := used) hm hUlow hpseudo
  have hγ0 : (0 : ℝ) ≤ γ := le_of_lt hm.hγ
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hκγ : 400 * κ ≤ γ := by linarith [hm.hκγ]
  have hgn : (2000 : ℝ) ≤ γ * (n : ℝ) := gamma_mul_n_ge hγ0 hm.hρ1 hn0 hm.hnbig
  have h1 : ((U \ matchVert N).ncard : ℝ) - ((P : Set (Fin n)).ncard : ℝ)
      ≤ (((U \ matchVert N) \ (P : Set (Fin n))).ncard : ℝ) := ncard_sdiff_ge _ _
  have hPn : ((P : Set (Fin n)).ncard : ℝ) = (P.card : ℝ) := by simp
  have h2 : κ * (n : ℝ) ≤ γ * (n : ℝ) / 400 := by
    have h := mul_le_mul_of_nonneg_right hκγ hn0
    nlinarith [h]
  have hgt : (0 : ℝ) < (((U \ matchVert N) \ (P : Set (Fin n))).ncard : ℝ) := by
    linarith [h1, hAlow, h2, hP, hPn, hgn]
  have hpos : 0 < ((U \ matchVert N) \ (P : Set (Fin n))).ncard := by exact_mod_cast hgt
  obtain ⟨u, hu⟩ := (Set.ncard_pos).mp hpos
  rw [Set.mem_sdiff] at hu
  exact ⟨u, hu.1.1, hu.1.2, hu.2⟩

/-- **The choice of the defect vertex in the case `|U| > (1-2ε)n`.**  There is a
vertex `u ∈ (S ∖ V(N)) ∖ P`: the defect must lie in `S`, and the paper's
`κ ≪ γ` (here `100κ ≤ γ²` and `4 ≤ γ²n`) makes `|S ∖ V(N)| ≥ γ²n - κn` much
larger than `|P| ≤ κn`. -/
theorem internal_pick_B {𝓗 R used : Hypergraph (Fin n)}
    {U S : Set (Fin n)} {N : Set 𝓗} {P : Finset (Fin n)} {ρ ε γ κ ξ : ℝ}
    (hm : InternalMargins n ρ ε γ κ ξ)
    (hpseudo : PseudoRandom N (absorberFam R U ∪ {U, S}) γ κ)
    (hP : (P.card : ℝ) ≤ κ * (n : ℝ))
    (hS : γ * (n : ℝ) ≤ (S.ncard : ℝ)) :
    ∃ u : Fin n, u ∈ S ∧ u ∉ matchVert N ∧ u ∉ P := by
  classical
  have hγ0 : (0 : ℝ) ≤ γ := le_of_lt hm.hγ
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hκ2 : 100 * κ * (n : ℝ) ≤ γ ^ 2 * (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hm.hκγ2 hn0
    nlinarith [h]
  have hmemS : S ∈ absorberFam R U ∪ {U, S} := by
    refine Set.mem_union_right _ ?_
    exact Set.mem_insert_iff.mpr (Or.inr rfl)
  have hps := (abs_le.mp (hpseudo S hmemS)).1
  have hSge : γ * (γ * (n : ℝ)) - κ * (n : ℝ) ≤ ((S \ matchVert N).ncard : ℝ) := by
    have h2 : γ * (γ * (n : ℝ)) ≤ γ * (S.ncard : ℝ) := mul_le_mul_of_nonneg_left hS hγ0
    linarith [hps, h2]
  have h1 : ((S \ matchVert N).ncard : ℝ) - ((P : Set (Fin n)).ncard : ℝ)
      ≤ (((S \ matchVert N) \ (P : Set (Fin n))).ncard : ℝ) := ncard_sdiff_ge _ _
  have hPn : ((P : Set (Fin n)).ncard : ℝ) = (P.card : ℝ) := by simp
  have hgt : (0 : ℝ) < (((S \ matchVert N) \ (P : Set (Fin n))).ncard : ℝ) := by
    linarith [h1, hSge, hP, hPn, hκ2, hm.hγn]
  have hpos : 0 < ((S \ matchVert N) \ (P : Set (Fin n))).ncard := by exact_mod_cast hgt
  obtain ⟨u, hu⟩ := (Set.ncard_pos).mp hpos
  rw [Set.mem_sdiff] at hu
  exact ⟨u, hu.1.1, hu.1.2, hu.2⟩

/-! ## The one-step lemma in the two cases -/

/-- **§7.2, case `|U| ≤ (1-2ε)n`.**  There is a new defect vertex `u` (not in
the already chosen set `P`) and a matching of available `R`-edges covering all
of `U ∖ V(N)`. -/
theorem internal_step_A2 {𝓗 R used : Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {U S : Set (Fin n)} {N : Set 𝓗} {P : Finset (Fin n)}
    {ρ ε γ κ ξ : ℝ} {B : ℕ}
    (hm : InternalMargins n ρ ε γ κ ξ)
    (hmatch : InternalMatchingInput n B)
    (hUlow : (n : ℝ) / 100 ≤ (U.ncard : ℝ))
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (habs : IsAbsorber (incidentTwo 𝓗 U) R 𝓥 ρ (10 * γ) ξ) (hU𝓥 : U ∈ 𝓥)
    (hpseudo : PseudoRandom N (absorberFam R U ∪ {U, S}) γ κ)
    (hused : ∀ v : Fin n, ((nbrs used v).ncard : ℝ) ≤ κ * (n : ℝ))
    (hR2 : ∀ e ∈ R, edgeSize e = 2)
    (hB : (B : ℝ) ≤ ρ ^ 2 * (γ * (n : ℝ)) / 400)
    (hUA : (U.ncard : ℝ) ≤ (1 - 2 * ε) * (n : ℝ))
    (hP : (P.card : ℝ) ≤ κ * (n : ℝ)) :
    ∃ u : Fin n, u ∈ U ∧ u ∉ matchVert N ∧ u ∉ P ∧
      ∃ Nabs : Set 𝓗, IsMatching 𝓗 Nabs ∧
        (∀ e ∈ Nabs, (e : Set (Fin n)) ∈ R ∧ (e : Set (Fin n)) ∉ used) ∧
        Disjoint (matchVert Nabs) (matchVert N) ∧
        Covers Nabs (U \ matchVert N) := by
  classical
  have hRsub : R ⊆ incidentTwo 𝓗 U := habs.1
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hγ0 : (0 : ℝ) ≤ γ := le_of_lt hm.hγ
  have hγn0 : (0 : ℝ) ≤ γ * (n : ℝ) := mul_nonneg hγ0 hn0
  have hAlow : γ * (n : ℝ) / 200 ≤ ((U \ matchVert N).ncard : ℝ) :=
    internal_A_lower (used := used) hm hUlow hpseudo
  have hgn : (2000 : ℝ) ≤ γ * (n : ℝ) := gamma_mul_n_ge hγ0 hm.hρ1 hn0 hm.hnbig
  have h1 : (1 : ℝ) ≤ γ * (n : ℝ) / 400 := by linarith [hgn]
  obtain ⟨u, huU, huN, huP⟩ := internal_pick_A (used := used) hm hUlow hpseudo hP
  have huA : u ∈ U \ matchVert N := ⟨huU, huN⟩
  by_cases hpar : Even (U \ matchVert N).ncard
  · obtain ⟨M, hMm, hMR, -, hMdisj, hMcov⟩ :=
      internal_matching_of hm hmatch hUlow hUdeg habs hU𝓥 hpseudo hused hR2 hB
        (W := U \ matchVert N) (ul := u) (fun _ hx => hx) hpar
        (by linarith [hAlow, hγn0]) (fun _ hx => hx.1)
    exact ⟨u, huU, huN, huP, M, hMm, hMR, hMdisj, covers_of_exists hMcov⟩
  · have hAncard : 0 < (U \ matchVert N).ncard := by
      have h2 : (0 : ℝ) < γ * (n : ℝ) / 200 := by linarith [hgn]
      exact_mod_cast lt_of_lt_of_le h2 hAlow
    have hstep : ((U \ matchVert N) \ {u}).ncard + 1 = (U \ matchVert N).ncard := by
      rw [Set.ncard_sdiff_singleton_of_mem huA]
      omega
    have hWeven : Even ((U \ matchVert N) \ {u}).ncard := by
      rw [← hstep] at hpar
      rcases Nat.even_or_odd ((U \ matchVert N) \ {u}).ncard with he | ho
      · exact he
      · obtain ⟨m, hm'⟩ := ho
        exact absurd ⟨m + 1, by omega⟩ hpar
    have hWlow : γ * (n : ℝ) / 400 ≤ (((U \ matchVert N) \ {u}).ncard : ℝ) := by
      have h2 : (((U \ matchVert N) \ {u}).ncard : ℝ) = ((U \ matchVert N).ncard : ℝ) - 1 := by
        have h3 : (((U \ matchVert N) \ {u}).ncard : ℝ) + 1 = ((U \ matchVert N).ncard : ℝ) := by
          exact_mod_cast hstep
        linarith
      linarith [h2, hAlow, h1]
    obtain ⟨v, hv1, hv2, hv3, hv4⟩ :=
      internal_pair hm hUlow hUdeg habs hU𝓥 hpseudo hused hUA huU huN
    obtain ⟨M, hMm, hMR, hMW, hMdisj, hMcov⟩ :=
      internal_matching_of hm hmatch hUlow hUdeg habs hU𝓥 hpseudo hused hR2 hB
        (W := (U \ matchVert N) \ {u}) (ul := u) (fun _ hx => hx.1) hWeven hWlow
        (fun _ hx => hx)
    set e0 : 𝓗 := ⟨({u, v} : Set (Fin n)), incidentTwo_subset_self (hRsub hv1)⟩ with he0def
    have hsing : IsMatching 𝓗 ({e0} : Set 𝓗) := isMatching_singleton 𝓗 e0
    have hdis : Disjoint (matchVert M) (matchVert ({e0} : Set 𝓗)) := by
      rw [Set.disjoint_left]
      intro x hx hxe
      rw [mem_matchVert] at hx hxe
      obtain ⟨e, he, hxe'⟩ := hx
      obtain ⟨e', he', hxe''⟩ := hxe
      rw [Set.mem_singleton_iff] at he'
      subst he'
      have heW : (e : Set (Fin n)) ⊆ (U \ matchVert N) \ {u} := hMW e he
      have hxW := heW hxe'
      rw [he0def] at hxe''
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxe''
      rcases hxe'' with rfl | rfl
      · exact hxW.2 rfl
      · exact hv2 hxW.1.1
    refine ⟨u, huU, huN, huP, M ∪ {e0}, isMatching_union hMm hsing hdis, ?_, ?_, ?_⟩
    · intro e he
      rw [Set.mem_union] at he
      rcases he with he | he
      · exact hMR e he
      · rw [Set.mem_singleton_iff] at he
        refine ⟨?_, ?_⟩
        · rw [he, he0def]; exact hv1
        · intro hc
          rw [he] at hc
          rw [he0def] at hc
          exact hv4 hc
    · rw [Set.disjoint_left]
      intro x hx hxN
      rw [matchVert_union] at hx
      rw [Set.mem_union] at hx
      rcases hx with hx | hx
      · exact (Set.disjoint_left.mp hMdisj) hx hxN
      · rw [mem_matchVert] at hx
        obtain ⟨e, he, hxe⟩ := hx
        rw [Set.mem_singleton_iff] at he
        subst he
        rw [he0def] at hxe
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxe
        rcases hxe with h | h
        · exact huN (h ▸ hxN)
        · exact hv3 (h ▸ hxN)
    · intro x hx
      by_cases hxu : x = u
      · rw [matchVert_union]
        refine Or.inr ?_
        rw [mem_matchVert]
        refine ⟨e0, by rw [Set.mem_singleton_iff], ?_⟩
        rw [he0def, hxu]
        simp
      · rw [matchVert_union]
        refine Or.inl ?_
        rw [mem_matchVert]
        exact hMcov x ⟨hx, hxu⟩

/-- **§7.2, case `|U| > (1-2ε)n`.**  There is a new defect vertex
`u ∈ S ∖ (V(N) ∪ P)` and a matching of available `R`-edges covering
`(U ∖ V(N)) ∖ {u}`. -/
theorem internal_step_B2 {𝓗 R used : Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {U S : Set (Fin n)} {N : Set 𝓗} {P : Finset (Fin n)}
    {ρ ε γ κ ξ : ℝ} {B : ℕ}
    (hm : InternalMargins n ρ ε γ κ ξ)
    (hmatch : InternalMatchingInput n B)
    (hUlow : (n : ℝ) / 100 ≤ (U.ncard : ℝ))
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (habs : IsAbsorber (incidentTwo 𝓗 U) R 𝓥 ρ (10 * γ) ξ) (hU𝓥 : U ∈ 𝓥)
    (hpseudo : PseudoRandom N (absorberFam R U ∪ {U, S}) γ κ)
    (hused : ∀ v : Fin n, ((nbrs used v).ncard : ℝ) ≤ κ * (n : ℝ))
    (hR2 : ∀ e ∈ R, edgeSize e = 2)
    (hB : (B : ℝ) ≤ ρ ^ 2 * (γ * (n : ℝ)) / 400)
    (hS : γ * (n : ℝ) ≤ (S.ncard : ℝ)) (hSsub : S ⊆ U)
    (hP : (P.card : ℝ) ≤ κ * (n : ℝ)) :
    ∃ u : Fin n, u ∈ S ∧ u ∉ matchVert N ∧ u ∉ P ∧
      ∃ Nabs : Set 𝓗, IsMatching 𝓗 Nabs ∧
        (∀ e ∈ Nabs, (e : Set (Fin n)) ∈ R ∧ (e : Set (Fin n)) ∉ used) ∧
        Disjoint (matchVert Nabs) (matchVert N) ∧
        Covers Nabs ((U \ matchVert N) \ {u}) := by
  classical
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hγ0 : (0 : ℝ) ≤ γ := le_of_lt hm.hγ
  have hγn0 : (0 : ℝ) ≤ γ * (n : ℝ) := mul_nonneg hγ0 hn0
  have hAlow : γ * (n : ℝ) / 200 ≤ ((U \ matchVert N).ncard : ℝ) :=
    internal_A_lower (used := used) hm hUlow hpseudo
  have hgn : (2000 : ℝ) ≤ γ * (n : ℝ) := gamma_mul_n_ge hγ0 hm.hρ1 hn0 hm.hnbig
  have h1 : (1 : ℝ) ≤ γ * (n : ℝ) / 400 := by linarith [hgn]
  obtain ⟨u, huS, huN, huP⟩ := internal_pick_B (used := used) hm hpseudo hP hS
  have huU : u ∈ U := hSsub huS
  have huA : u ∈ U \ matchVert N := ⟨huU, huN⟩
  by_cases hpar : Even (U \ matchVert N).ncard
  · obtain ⟨M, hMm, hMR, hMW, hMdisj, hMcov⟩ :=
      internal_matching_of hm hmatch hUlow hUdeg habs hU𝓥 hpseudo hused hR2 hB
        (W := U \ matchVert N) (ul := u) (fun _ hx => hx) hpar
        (by linarith [hAlow, hγn0]) (fun _ hx => hx.1)
    exact ⟨u, huS, huN, huP, M, hMm, hMR, hMdisj,
      Covers.mono (subset_refl M) (Set.sdiff_subset) (covers_of_exists hMcov)⟩
  · have hAncard : 0 < (U \ matchVert N).ncard := by
      have h2 : (0 : ℝ) < γ * (n : ℝ) / 200 := by linarith [hgn]
      exact_mod_cast lt_of_lt_of_le h2 hAlow
    have hstep : ((U \ matchVert N) \ {u}).ncard + 1 = (U \ matchVert N).ncard := by
      rw [Set.ncard_sdiff_singleton_of_mem huA]
      omega
    have hWeven : Even ((U \ matchVert N) \ {u}).ncard := by
      rw [← hstep] at hpar
      rcases Nat.even_or_odd ((U \ matchVert N) \ {u}).ncard with he | ho
      · exact he
      · obtain ⟨m, hm'⟩ := ho
        exact absurd ⟨m + 1, by omega⟩ hpar
    have hWlow : γ * (n : ℝ) / 400 ≤ (((U \ matchVert N) \ {u}).ncard : ℝ) := by
      have h2 : (((U \ matchVert N) \ {u}).ncard : ℝ) = ((U \ matchVert N).ncard : ℝ) - 1 := by
        have h3 : (((U \ matchVert N) \ {u}).ncard : ℝ) + 1 = ((U \ matchVert N).ncard : ℝ) := by
          exact_mod_cast hstep
        linarith
      linarith [h2, hAlow, h1]
    obtain ⟨M, hMm, hMR, hMW, hMdisj, hMcov⟩ :=
      internal_matching_of hm hmatch hUlow hUdeg habs hU𝓥 hpseudo hused hR2 hB
        (W := (U \ matchVert N) \ {u}) (ul := u) (fun _ hx => hx.1) hWeven hWlow
        (fun _ hx => hx)
    exact ⟨u, huS, huN, huP, M, hMm, hMR, hMdisj, covers_of_exists hMcov⟩

/-! ## The iteration -/

/-- **The iteration of the one-step internal absorption.**  Given a one-step
lemma `hstep` (which uses the accumulated edge set `used` and the accumulated
defect set `P` and produces one matching and one new defect vertex, avoiding
`P`), we iterate it over `i : Fin k`, accumulating `used` as the union of the
previous matchings and `P` as the set of the previous defect vertices.  The
extra conclusion `Extra` is whatever the one-step lemma guarantees for the
pair `(N, Nabs)` / vertex `u`. -/
theorem internal_iter {𝓗 R : Hypergraph (Fin n)}
    {U S : Set (Fin n)} {γ κ : ℝ}
    (Extra : Fin n → Set 𝓗 → Set 𝓗 → Prop)
    (hstep : ∀ (N : Set 𝓗) (used : Hypergraph (Fin n)) (P : Finset (Fin n)),
      (∀ v : Fin n, ((nbrs used v).ncard : ℝ) ≤ κ * (n : ℝ)) →
      (P.card : ℝ) ≤ κ * (n : ℝ) →
      PseudoRandom N (absorberFam R U ∪ {U, S}) γ κ →
      ∃ u : Fin n, u ∈ U ∧ u ∉ matchVert N ∧ u ∉ P ∧
        ∃ Nabs : Set 𝓗, IsMatching 𝓗 Nabs ∧
          (∀ e ∈ Nabs, (e : Set (Fin n)) ∈ R ∧ (e : Set (Fin n)) ∉ used) ∧
          Disjoint (matchVert Nabs) (matchVert N) ∧
          Covers Nabs ((U \ matchVert N) \ {u}) ∧ Extra u N Nabs) :
    ∀ (k : ℕ) (N : Fin k → Set 𝓗),
      (∀ i, PseudoRandom (N i) (absorberFam R U ∪ {U, S}) γ κ) →
      (k : ℝ) ≤ κ * (n : ℝ) →
      ∃ (Nabs : Fin k → Set 𝓗) (u : Fin k → Fin n),
        (∀ i, IsMatching 𝓗 (Nabs i)) ∧
        (∀ i j, i ≠ j → Disjoint (Nabs i) (Nabs j)) ∧
        (∀ i, Nabs i ⊆ {e : 𝓗 | (e : Set (Fin n)) ∈ R}) ∧
        (∀ i, Disjoint (matchVert (Nabs i)) (matchVert (N i))) ∧
        (∀ i, Covers (Nabs i) ((U \ matchVert (N i)) \ {u i})) ∧
        (∀ i, u i ∈ U) ∧ (∀ i, u i ∉ matchVert (N i)) ∧
        Function.Injective u ∧ (∀ i, Extra (u i) (N i) (Nabs i)) := by
  classical
  intro k
  induction k with
  | zero =>
      intro N _ _
      exact ⟨Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
        fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
        fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
        fun i => Fin.elim0 i⟩
  | succ k ih =>
      intro N hpseudo hk
      let N0 : Fin k → Set 𝓗 := fun i => N i.castSucc
      have hpseudo0 : ∀ i, PseudoRandom (N0 i) (absorberFam R U ∪ {U, S}) γ κ :=
        fun i => hpseudo i.castSucc
      have hk0 : (k : ℝ) ≤ κ * (n : ℝ) := by
        have h : ((k : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
        linarith [hk, h]
      obtain ⟨Nabs0, u0, hmat0, hdisj0, hR0, hdisjN0, hcov0, hU0, hN0, hinj0, hExtra0⟩ :=
        ih N0 hpseudo0 hk0
      set used : Hypergraph (Fin n) := famUnionIdx Nabs0 with huseddef
      have huseddeg : ∀ v : Fin n, ((nbrs used v).ncard : ℝ) ≤ κ * (n : ℝ) := by
        intro v
        have h1 : (nbrs used v).ncard ≤ k := by
          rw [huseddef]
          exact ncard_nbrs_famUnionIdx_le hmat0 v
        have h2 : ((nbrs used v).ncard : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
        linarith [h2, hk0]
      set P : Finset (Fin n) := Finset.image u0 Finset.univ with hPdef
      have hPcard : (P.card : ℝ) ≤ κ * (n : ℝ) := by
        have h1 : P.card ≤ k := by
          rw [hPdef]
          calc (Finset.image u0 Finset.univ).card ≤ Finset.univ.card := Finset.card_image_le
            _ = k := by simp
        have h2 : (P.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
        linarith [h2, hk0]
      obtain ⟨uL, huLU, huLN, huLP, NabsL, hmatL, hRL, hdisjNL, hcovL, hExtraL⟩ :=
        hstep (N (Fin.last k)) used P huseddeg hPcard (hpseudo (Fin.last k))
      have hPmem : ∀ a : Fin k, u0 a ∈ P := by
        intro a
        rw [hPdef]
        exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
      refine ⟨Fin.snoc Nabs0 NabsL, Fin.snoc u0 uL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · simp only [Fin.snoc_castSucc]; exact hmat0 j
        · simp only [Fin.snoc_last]; exact hmatL
      · intro i j hij
        rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl <;>
          rcases Fin.eq_castSucc_or_eq_last j with ⟨b, rfl⟩ | rfl
        · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hdisj0 a b (fun h => hij (congrArg Fin.castSucc h))
        · rw [Fin.snoc_castSucc, Fin.snoc_last, Set.disjoint_left]
          intro e he1 he2
          rw [huseddef] at hRL
          exact (hRL e he2).2 (famOf_subset_famUnionIdx (mem_famOf_of_mem he1))
        · rw [Fin.snoc_last, Fin.snoc_castSucc, Set.disjoint_left]
          intro e he1 he2
          rw [huseddef] at hRL
          exact (hRL e he1).2 (famOf_subset_famUnionIdx (mem_famOf_of_mem he2))
        · exact absurd rfl hij
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · simp only [Fin.snoc_castSucc]; exact hR0 j
        · simp only [Fin.snoc_last]; exact fun e he => (hRL e he).1
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · simp only [Fin.snoc_castSucc]; exact hdisjN0 j
        · simp only [Fin.snoc_last]; exact hdisjNL
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · simp only [Fin.snoc_castSucc]; exact hcov0 j
        · simp only [Fin.snoc_last]; exact hcovL
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · simp only [Fin.snoc_castSucc]; exact hU0 j
        · simp only [Fin.snoc_last]; exact huLU
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · simp only [Fin.snoc_castSucc]; exact hN0 j
        · simp only [Fin.snoc_last]; exact huLN
      · intro i j hij
        rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl <;>
          rcases Fin.eq_castSucc_or_eq_last j with ⟨b, rfl⟩ | rfl
        · simp only [Fin.snoc_castSucc] at hij
          exact congrArg Fin.castSucc (hinj0 hij)
        · simp only [Fin.snoc_castSucc, Fin.snoc_last] at hij
          exact absurd (hij.symm ▸ hPmem a) huLP
        · simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
          exact absurd (hij ▸ hPmem b) huLP
        · rfl
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · simp only [Fin.snoc_castSucc]; exact hExtra0 j
        · simp only [Fin.snoc_last]; exact hExtraL

end ErdosFaberLovaszConjecture
