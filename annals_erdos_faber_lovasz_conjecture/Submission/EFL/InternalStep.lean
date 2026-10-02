import Submission.EFL.InternalAbsorption

/-!
# The one-step internal absorption (§7.2 of the paper)

This module contains the ingredients of the one-step internal absorption:

* `restr R W` — the subfamily of `R` consisting of the edges inside `W`, with
  `degIn_restr` (the degree inside `W` is unchanged by restricting to `W`);
* `internal_pair` — the choice of the vertex `u ∈ U \ V(N)` and its partner
  `v ∉ U ∪ V(N)` (the `{u_i v_i}` edge) in the case `|U| ≤ (1-2ε)n`;
* `internal_step_A` — the case `|U| ≤ (1-2ε)n` of the one-step internal
  absorption: a matching of available edges of `R` covering all of
  `U \ V(N)`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-! ## Restricting a family of edges to a vertex set -/

/-- `R` restricted to the edges lying inside the vertex set `W`. -/
def restr (R : Hypergraph (Fin n)) (W : Set (Fin n)) : Hypergraph (Fin n) :=
  {e | e ∈ R ∧ e ⊆ W}

theorem mem_restr {R : Hypergraph (Fin n)} {W : Set (Fin n)} {e : Set (Fin n)} :
    e ∈ restr R W ↔ e ∈ R ∧ e ⊆ W := Iff.rfl

theorem restr_subset (R : Hypergraph (Fin n)) (W : Set (Fin n)) : restr R W ⊆ R :=
  fun _ he => he.1

theorem restr_subset_of {R G : Hypergraph (Fin n)} (h : R ⊆ G) (W : Set (Fin n)) :
    restr R W ⊆ G := fun _ he => h he.1

theorem restr_edgeSize {R : Hypergraph (Fin n)} {W : Set (Fin n)}
    (h2 : ∀ e ∈ R, edgeSize e = 2) : ∀ e ∈ restr R W, edgeSize e = 2 :=
  fun e he => h2 e he.1

/-- Restricting the family to `W` does not change the degree inside `W`. -/
theorem degIn_restr {R : Hypergraph (Fin n)} {W : Set (Fin n)} {w : Fin n} (hw : w ∈ W) :
    degIn (restr R W) W w = degIn R W w := by
  rw [degIn_eq_ncard, degIn_eq_ncard]
  congr 1
  ext y
  constructor
  · rintro ⟨hyW, hyR, -⟩
    exact ⟨hyW, hyR⟩
  · rintro ⟨hyW, hyR⟩
    refine ⟨hyW, hyR, ?_⟩
    rintro z (hz : z ∈ ({w, y} : Set (Fin n)))
    rcases (Set.mem_insert_iff.mp hz) with rfl | rfl
    · exact hw
    · exact hyW

/-! ## The choice of the pair `{u, v}` -/

/-- **The pair of §7.2 (case `|U| ≤ (1-2ε)n`).**  Every `u ∈ U \ V(N)` has a
`R`-neighbour `v` outside `U ∪ V(N)` whose edge is not yet used. -/
theorem internal_pair {𝓗 : Hypergraph (Fin n)} {R used : Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {U S : Set (Fin n)} {N : Set 𝓗} {ρ ε γ κ ξ : ℝ}
    (hm : InternalMargins n ρ ε γ κ ξ)
    (hUlow : (n : ℝ) / 100 ≤ (U.ncard : ℝ))
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (habs : IsAbsorber (incidentTwo 𝓗 U) R 𝓥 ρ (10 * γ) ξ) (hU𝓥 : U ∈ 𝓥)
    (hpseudo : PseudoRandom N (absorberFam R U ∪ {U, S}) γ κ)
    (hused : ∀ v : Fin n, ((nbrs used v).ncard : ℝ) ≤ κ * (n : ℝ))
    (hUA : (U.ncard : ℝ) ≤ (1 - 2 * ε) * (n : ℝ))
    {u : Fin n} (huU : u ∈ U) (huN : u ∉ matchVert N) :
    ∃ v : Fin n, v ∈ nbrs R u ∧ v ∉ U ∧ v ∉ matchVert N
      ∧ ({u, v} : Set (Fin n)) ∉ used := by
  classical
  have htyp := habs.2.1
  have hγ0 : (0 : ℝ) ≤ γ := le_of_lt hm.hγ
  have hρ0 : (0 : ℝ) ≤ ρ := le_of_lt hm.hρ
  have hε0 : (0 : ℝ) ≤ ε := le_of_lt hm.hε
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hεn : (0 : ℝ) ≤ ε * (n : ℝ) := mul_nonneg hε0 hn0
  -- (1) `u` has at least `εn` `G'`-neighbours outside `U`
  have hdegU : (1 - ε) * (n : ℝ) ≤ ((nbrs (incidentTwo 𝓗 U) u).ncard : ℝ) := by
    have h := hUdeg u huU
    rwa [degAt] at h
  have hcompl : (ε * (n : ℝ)) ≤ (((nbrs (incidentTwo 𝓗 U) u) \ U).ncard : ℝ) := by
    have h1 : ((nbrs (incidentTwo 𝓗 U) u).ncard : ℝ)
        ≤ (((nbrs (incidentTwo 𝓗 U) u) \ U).ncard : ℝ) + (U.ncard : ℝ) := by
      have h2 := ncard_sdiff_ge (nbrs (incidentTwo 𝓗 U) u) U
      have h3 : ((nbrs (incidentTwo 𝓗 U) u).ncard : ℝ)
          ≤ ((nbrs (incidentTwo 𝓗 U) u).ncard : ℝ) := le_refl _
      linarith [h2]
    linarith [h1, hdegU, hUA]
  -- (2) typicality
  have htyp' := (htyp U hU𝓥 u).2
  have hcomp : (Uᶜ ∩ nbrs (incidentTwo 𝓗 U) u).ncard
      = ((nbrs (incidentTwo 𝓗 U) u) \ U).ncard := by
    congr 1
    ext w
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
    tauto
  have hcomp2 : (Uᶜ ∩ nbrs R u).ncard = ((nbrs R u) \ U).ncard := by
    congr 1
    ext w
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
    tauto
  rw [hcomp, hcomp2] at htyp'
  have hNRU : ρ * (ε * (n : ℝ)) - 10 * γ * (n : ℝ) ≤ (((nbrs R u) \ U).ncard : ℝ) := by
    have h := (abs_le.mp htyp').1
    have h2 := mul_le_mul_of_nonneg_left hcompl hρ0
    linarith [h, h2]
  -- (3) pseudorandomness
  have hmem : (nbrs R u) \ U ∈ absorberFam R U ∪ {U, S} := by
    refine Set.mem_union_left _ ?_
    exact Or.inr ⟨u, rfl⟩
  have hpseudo' := hpseudo ((nbrs R u) \ U) hmem
  have hS : γ * (ρ * (ε * (n : ℝ)) - 10 * γ * (n : ℝ)) - 2 * κ * (n : ℝ)
      ≤ ((((nbrs R u) \ U) \ matchVert N) \ nbrs used u).ncard := by
    have h1 := (abs_le.mp hpseudo').1
    have h2 : γ * ((((nbrs R u) \ U).ncard : ℝ)) - κ * (n : ℝ)
        ≤ ((((nbrs R u) \ U) \ matchVert N).ncard : ℝ) := by
      linarith [h1]
    have h3 : (((((nbrs R u) \ U) \ matchVert N) \ nbrs used u).ncard : ℝ)
        ≥ ((((nbrs R u) \ U) \ matchVert N).ncard : ℝ) - (nbrs used u).ncard := by
      have h := ncard_sdiff_ge (((nbrs R u) \ U) \ matchVert N) (nbrs used u)
      linarith [h]
    have h4 := hused u
    have h5 : γ * (ρ * (ε * (n : ℝ)) - 10 * γ * (n : ℝ))
        ≤ γ * ((((nbrs R u) \ U).ncard : ℝ)) := mul_le_mul_of_nonneg_left hNRU hγ0
    linarith [h2, h3, h4, h5]
  -- (4) the set is nonempty
  have hpos : 0 < ((((nbrs R u) \ U) \ matchVert N) \ nbrs used u).ncard := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      by_contra hc
      have hc2 : (n : ℝ) = 0 := le_antisymm (not_lt.mp hc) hn0
      have hzero : γ * ρ * (n : ℝ) = 0 := by rw [hc2]; ring
      linarith [hm.hnbig, hzero]
    have hγn0 : (0 : ℝ) ≤ γ * (n : ℝ) := mul_nonneg hγ0 hn0
    have hγρεn : (0 : ℝ) ≤ γ * (ρ * (ε * (n : ℝ))) :=
      mul_nonneg hγ0 (mul_nonneg (le_of_lt hm.hρ) hεn)
    have h1 : (0 : ℝ) < γ * (ρ * (ε * (n : ℝ))) :=
      mul_pos hm.hγ (mul_pos hm.hρ (mul_pos hm.hε hnpos))
    have h2 : 10 * γ * γ * (n : ℝ) ≤ (γ * (ρ * (ε * (n : ℝ)))) / 4 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
      have h := mul_le_mul_of_nonneg_right hm.hγε hγn0
      nlinarith [h]
    have h3 : 2 * κ * (n : ℝ) ≤ (γ * (ρ * (ε * (n : ℝ)))) / 4 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
      have h := mul_le_mul_of_nonneg_right hm.hκγε hn0
      nlinarith [h, hγρεn]
    have h4 : (0 : ℝ) < ((((nbrs R u) \ U) \ matchVert N) \ nbrs used u).ncard := by
      have h := hS
      linarith [h2, h3, h1]
    exact_mod_cast h4
  have hpos' : 0 < (sfin ((((nbrs R u) \ U) \ matchVert N) \ nbrs used u)).card := by
    rw [card_sfin]
    exact_mod_cast hpos
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos'
  rw [mem_sfin] at hv
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · exact hv.1.1.1
  · exact hv.1.1.2
  · exact hv.1.2
  · exact hv.2

/-! ## The case `|U| ≤ (1-2ε)n` of the one-step internal absorption -/

theorem internal_step_A {𝓗 : Hypergraph (Fin n)} {R used : Hypergraph (Fin n)}
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
    (hUA : (U.ncard : ℝ) ≤ (1 - 2 * ε) * (n : ℝ)) :
    ∃ Nabs : Set 𝓗, IsMatching 𝓗 Nabs ∧
      (∀ e ∈ Nabs, (e : Set (Fin n)) ∈ R ∧ (e : Set (Fin n)) ∉ used) ∧
      Disjoint (matchVert Nabs) (matchVert N) ∧
      Covers Nabs (U \ matchVert N) := by
  classical
  have hRsub : R ⊆ incidentTwo 𝓗 U := habs.1
  have hup : UpperRegular (incidentTwo 𝓗 U) R ρ ξ := habs.2.2
  have hγ0 : (0 : ℝ) ≤ γ := le_of_lt hm.hγ
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hAlow : γ * (n : ℝ) / 200 ≤ ((U \ matchVert N).ncard : ℝ) :=
    internal_A_lower (used := used) hm hUlow hpseudo
  -- the matching on a set `W` with `(U \ V(N)) \ {ul} ⊆ W ⊆ U \ V(N)`
  have matching_of : ∀ (W : Set (Fin n)) (ul : Fin n),
      W ⊆ U \ matchVert N → Even W.ncard → γ * (n : ℝ) / 400 ≤ (W.ncard : ℝ) →
      (U \ matchVert N) \ {ul} ⊆ W →
      ∃ M : Set 𝓗, IsMatching 𝓗 M ∧
        (∀ e ∈ M, (e : Set (Fin n)) ∈ R ∧ (e : Set (Fin n)) ∉ used) ∧
        (∀ e ∈ M, (e : Set (Fin n)) ⊆ W) ∧
        Disjoint (matchVert M) (matchVert N) ∧
        (∀ w ∈ W, ∃ e ∈ M, w ∈ (e : Set (Fin n))) := by
    intro W ul hWle hWeven hWlow hWge
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
      have hmain := hup S T hdisj hξn hξn'
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
  have hn1 : 1 ≤ n := by
    by_contra hc
    push_neg at hc
    have hc2 : n = 0 := by omega
    subst hc2
    have hb := hm.hnbig
    simp only [Nat.cast_zero, mul_zero] at hb
    linarith [hb]
  haveI : NeZero n := ⟨by omega⟩
  by_cases hpar : Even (U \ matchVert N).ncard
  · -- even case
    obtain ⟨M, hMm, hMR, hMW, hMdisj, hMcov⟩ :=
      matching_of (U \ matchVert N) 0 (fun _ hx => hx) hpar (by linarith [hAlow]) (fun _ hx => hx.1)
    refine ⟨M, hMm, hMR, hMdisj, ?_⟩
    intro w hw
    rw [mem_matchVert]
    exact hMcov w hw
  · -- odd case: pick `u ∈ A` and its partner `v`
    have hposA : 0 < (sfin (U \ matchVert N)).card := by
      rw [card_sfin]
      have h1 : (0 : ℝ) < γ * (n : ℝ) / 200 := by
        have h2 : 0 < γ * (n : ℝ) := by
          by_contra hc
          have hc2 : (n : ℝ) = 0 := by
            have h3 : ¬ (0:ℝ) < (n:ℝ) := fun hlt => hc (mul_pos hm.hγ hlt)
            exact le_antisymm (not_lt.mp h3) hn0
          have hzero : γ * ρ * (n : ℝ) = 0 := by rw [hc2]; ring
          linarith [hm.hnbig, hzero]
        linarith [h2]
      exact_mod_cast lt_of_lt_of_le h1 hAlow
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hposA
    rw [mem_sfin] at hu
    have hAncard : 0 < (U \ matchVert N).ncard := by
      rw [card_sfin] at hposA
      exact hposA
    have hstep : ((U \ matchVert N) \ {u}).ncard + 1 = (U \ matchVert N).ncard := by
      rw [Set.ncard_sdiff_singleton_of_mem hu]
      omega
    have hWeven : Even ((U \ matchVert N) \ {u}).ncard := by
      rw [← hstep] at hpar
      rcases Nat.even_or_odd ((U \ matchVert N) \ {u}).ncard with he | ho
      · exact he
      · obtain ⟨m, hm⟩ := ho
        exact absurd ⟨m + 1, by omega⟩ hpar
    have hWlow : γ * (n : ℝ) / 400 ≤ (((U \ matchVert N) \ {u}).ncard : ℝ) := by
      have h2 : (((U \ matchVert N) \ {u}).ncard : ℝ) = ((U \ matchVert N).ncard : ℝ) - 1 := by
        have h3 : (((U \ matchVert N) \ {u}).ncard : ℝ) + 1
            = ((U \ matchVert N).ncard : ℝ) := by exact_mod_cast hstep
        linarith
      have h4 : (1 : ℝ) ≤ γ * (n : ℝ) / 400 := by
        have h5 : (0 : ℝ) < γ * (n : ℝ) := by
          by_contra hc
          have hc2 : (n : ℝ) = 0 := by
            have h3 : ¬ (0:ℝ) < (n:ℝ) := fun hlt => hc (mul_pos hm.hγ hlt)
            exact le_antisymm (not_lt.mp h3) hn0
          have hzero : γ * ρ * (n : ℝ) = 0 := by rw [hc2]; ring
          linarith [hm.hnbig, hzero]
        have h6 : γ * ρ * (n : ℝ) ≤ γ * (n : ℝ) := by
          have h := mul_le_mul_of_nonneg_right hm.hρ1 hn0
          nlinarith [h, h5, le_of_lt hm.hγ]
        linarith [hm.hnbig, h6]
      linarith [h2, hAlow, h4]
    obtain ⟨v, hv1, hv2, hv3, hv4⟩ :=
      internal_pair hm hUlow hUdeg habs hU𝓥 hpseudo hused hUA hu.1 hu.2
    obtain ⟨M, hMm, hMR, hMW, hMdisj, hMcov⟩ :=
      matching_of ((U \ matchVert N) \ {u}) u (fun _ hx => hx.1)
        hWeven hWlow (fun _ hx => hx)
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
    refine ⟨M ∪ {e0}, isMatching_union hMm hsing hdis, ?_, ?_, ?_⟩
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
        · exact hu.2 (h ▸ hxN)
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

end

end ErdosFaberLovaszConjecture