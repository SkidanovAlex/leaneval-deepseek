import Submission.EFL.CrossingAbsorption
import Submission.EFL.GFactor

/-!
# Internal absorption (§7.2 of the paper)

This module formalises the second absorption lemma of §7
(`internal-absorption-lemma`): when `|U| ≥ n/100` the matchings are extended
by *perfect* matchings of the graph induced on `U ∖ V(N_i)`, using the
perfect-matching criterion `internal-matching-prop` (an upper-regular graph of
minimum degree `≥ 3ρm/4` on an even number of vertices has a perfect
matching).

The matching criterion is recorded as the input `InternalMatchingInput`; the
remaining content of the lemma is counting, collected in
`internal_degree_chain` (the degree estimate `d ≥ 3ρ|W|/4`) and in the
one-step/iteration lemmas below.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-! ## Degrees inside a vertex set, and matching families -/

/-- `degIn` (from `GFactor.lean`) as a `Set.ncard`. -/
theorem degIn_eq_ncard (R : Hypergraph (Fin n)) (W : Set (Fin n)) (w : Fin n) :
    degIn R W w = ({y : Fin n | y ∈ W ∧ ({w, y} : Set (Fin n)) ∈ R} : Set (Fin n)).ncard :=
  rfl

/-- A subfamily of `R` whose edges are pairwise disjoint. -/
def IsMatchingFam {R : Hypergraph (Fin n)} (M : Set R) : Prop :=
  M.Pairwise fun e₁ e₂ => Disjoint (e₁ : Set (Fin n)) (e₂ : Set (Fin n))

/-- A subfamily of `R` covering a vertex set `W`. -/
def CoversFam {R : Hypergraph (Fin n)} (M : Set R) (W : Set (Fin n)) : Prop :=
  ∀ w ∈ W, ∃ e ∈ M, w ∈ (e : Set (Fin n))

/-- The perfect-matching input of §7.2 (Proposition `internal-matching-prop`):
there is `B` such that whenever `W` has an even number of vertices and the
2-edge family `R` (all of whose edges lie inside `W`) has minimum degree at
least `3ρ|W|/4` and is upper `(ρ,ξ)`-regular with respect to `W`, then `R`
contains a matching covering `W`. -/
def InternalMatchingInput (n : ℕ) (B : ℕ) : Prop :=
  ∀ (W : Set (Fin n)) (R : Hypergraph (Fin n)) (ρ ξ : ℝ),
    Even W.ncard → 0 < ρ → 0 ≤ ξ → 10 * ξ ≤ ρ → ρ ≤ 1 →
    (B : ℝ) ≤ ρ ^ 2 * (W.ncard : ℝ) →
    (∀ e ∈ R, e ⊆ W) → (∀ e ∈ R, edgeSize e = 2) →
    (∀ w ∈ W, 3 * ρ * (W.ncard : ℝ) / 4 ≤ (degIn R W w : ℝ)) →
    (∀ S T : Finset (Fin n), S ⊆ sfin W → T ⊆ sfin W → Disjoint S T →
      ξ * (W.ncard : ℝ) ≤ (S.card : ℝ) → ξ * (W.ncard : ℝ) ≤ (T.card : ℝ) →
      (edgeCount R S T : ℝ) ≤ (ρ + ξ) * (S.card : ℝ) * (T.card : ℝ)) →
    ∃ M : Set R, IsMatchingFam M ∧ CoversFam M W

/-! ## Numeric margins of §7.2 -/

/-- The numeric margins of §7.2 in the concrete form needed below
(`0 < 1/n ≪ ξ ≪ κ ≪ γ ≪ ρ,ε ≪ 1`). -/
structure InternalMargins (n : ℕ) (ρ ε γ κ ξ : ℝ) : Prop where
  hρ : 0 < ρ
  hρ1 : ρ ≤ 1
  hε : 0 < ε
  hγ : 0 < γ
  hκ : 0 < κ
  hξ : 0 < ξ
  hε4 : 4000 * ε ≤ 1
  hγρ : 20000 * γ ≤ ρ
  hκγ : 1500 * κ ≤ γ
  hκγρ : 4000 * κ ≤ γ * ρ
  hnbig : 2000 ≤ γ * ρ * (n : ℝ)
  -- margins used by the one-step lemmas of §7.2 (`InternalStep.lean`)
  hξγρ : 4000 * ξ ≤ γ * ρ
  hγε : 40 * γ ≤ ρ * ε
  hκγε : 8 * κ ≤ γ * ρ * ε
  hκγ2 : 100 * κ ≤ γ ^ 2
  hεhalf : 2 * ε ≤ 1 / 8
  hγhalf : 2 * γ ≤ 1
  -- a lower bound on `γ²n` (the paper's `γ ≫ 1/n`), used to choose the
  -- defect vertices `u_i` of the case `|U| > (1-2ε)n` of §7.2
  hγn : 4 ≤ γ ^ 2 * (n : ℝ)

/-- `|U ∖ V(N)| ≥ γn/200` under pseudorandomness. -/
theorem internal_A_lower {𝓗 : Hypergraph (Fin n)} {R used : Hypergraph (Fin n)}
    {U S : Set (Fin n)} {N : Set 𝓗} {ρ ε γ κ ξ : ℝ} (hm : InternalMargins n ρ ε γ κ ξ)
    (hUlow : (n : ℝ) / 100 ≤ (U.ncard : ℝ))
    (hpseudo : PseudoRandom N (absorberFam R U ∪ {U, S}) γ κ) :
    γ * (n : ℝ) / 200 ≤ ((U \ matchVert N).ncard : ℝ) := by
  have hmemU : U ∈ absorberFam R U ∪ {U, S} := by
    refine Set.mem_union_right _ ?_
    exact Set.mem_insert_iff.mpr (Or.inl rfl)
  have h := (abs_le.mp (hpseudo U hmemU)).1
  have hγ0 : (0 : ℝ) ≤ γ := le_of_lt hm.hγ
  have hκγ : 200 * κ ≤ γ := by linarith [hm.hκγ]
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [h, hUlow, hγ0, hκγ, hn0]

/-- The final numeric assembly of `internal_degree_chain`, with all products
pre-multiplied so that only linear arithmetic is needed. -/
theorem internal_arith_core {ρ ε γ κ : ℝ} {n U W : ℕ}
    (hA : 3 * ρ * (W : ℝ) / 4 ≤ 0.75 * (γ * ρ * (U : ℝ)) + 0.75 * (ρ * κ * (n : ℝ)))
    (hE : 0.75 * ρ * κ * (n : ℝ) ≤ 0.0005 * (γ * ρ * (n : ℝ)))
    (hB : γ * ρ * (ε * (n : ℝ)) ≤ 0.00025 * (γ * ρ * (n : ℝ)))
    (hC : 10 * γ * γ * (n : ℝ) ≤ 0.0005 * (γ * ρ * (n : ℝ)))
    (hD : 2 * κ * (n : ℝ) ≤ 0.0005 * (γ * ρ * (n : ℝ)))
    (hF : 1 ≤ 0.0005 * (γ * ρ * (n : ℝ)))
    (hG : 0.0025 * (γ * ρ * (n : ℝ)) ≤ 0.25 * (γ * ρ * (U : ℝ))) :
    3 * ρ * (W : ℝ) / 4
      ≤ γ * (ρ * ((U : ℝ) - ε * (n : ℝ)) - 10 * γ * (n : ℝ)) - 2 * κ * (n : ℝ) - 1 := by
  have h1 : γ * ρ * (ε * (n : ℝ)) + 10 * γ * γ * (n : ℝ) + 2 * κ * (n : ℝ) + 1
      ≤ 0.00175 * (γ * ρ * (n : ℝ)) := by linarith [hB, hC, hD, hF]
  have h2 : 0.0005 * (γ * ρ * (n : ℝ)) + 0.00175 * (γ * ρ * (n : ℝ))
      ≤ 0.25 * (γ * ρ * (U : ℝ)) := by linarith [hG]
  nlinarith [hA, hE, h1, h2]

set_option maxHeartbeats 1000000 in
/-- **The degree estimate of §7.2.**  Every `u ∈ W` has at least `3ρ|W|/4`
neighbours in `W` inside the available edges `R ∖ used`, where `W` is
`U ∖ V(N)` with at most one vertex deleted. -/
theorem internal_degree_chain {𝓗 : Hypergraph (Fin n)} {R used : Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {U S W : Set (Fin n)} {N : Set 𝓗} {ρ ε γ κ ξ : ℝ}
    (hm : InternalMargins n ρ ε γ κ ξ)
    (hUlow : (n : ℝ) / 100 ≤ (U.ncard : ℝ))
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (habs : IsAbsorber (incidentTwo 𝓗 U) R 𝓥 ρ (10 * γ) ξ) (hU𝓥 : U ∈ 𝓥)
    (hpseudo : PseudoRandom N (absorberFam R U ∪ {U, S}) γ κ)
    (hused : ∀ v : Fin n, ((nbrs used v).ncard : ℝ) ≤ κ * (n : ℝ))
    {ul : Fin n} (hWle : W ⊆ U \ matchVert N) (hWge : (U \ matchVert N) \ {ul} ⊆ W)
    {u : Fin n} (hu : u ∈ W) :
    3 * ρ * (W.ncard : ℝ) / 4 ≤ ((degIn (R \ used) W u : ℕ) : ℝ) := by
  classical
  have htyp := habs.2.1
  have hγ0 : (0 : ℝ) ≤ γ := le_of_lt hm.hγ
  have hκ0 : (0 : ℝ) ≤ κ := le_of_lt hm.hκ
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have huU : u ∈ U := hWle hu |>.1
  -- (1) the degree of `u` inside `G'`
  have hdegU : (1 - ε) * (n : ℝ) ≤ ((nbrs (incidentTwo 𝓗 U) u).ncard : ℝ) := by
    have h := hUdeg u huU
    rwa [degAt] at h
  have hGU : (U.ncard : ℝ) - ε * (n : ℝ) ≤ ((U ∩ nbrs (incidentTwo 𝓗 U) u).ncard : ℝ) := by
    have hsd : ((U ∩ nbrs (incidentTwo 𝓗 U) u).ncard : ℝ)
        ≥ ((nbrs (incidentTwo 𝓗 U) u).ncard : ℝ) - (Uᶜ.ncard : ℝ) := by
      have h1 : (nbrs (incidentTwo 𝓗 U) u).ncard
          ≤ (U ∩ nbrs (incidentTwo 𝓗 U) u).ncard + (Uᶜ).ncard := by
        have hsub : nbrs (incidentTwo 𝓗 U) u ⊆
            (U ∩ nbrs (incidentTwo 𝓗 U) u) ∪ Uᶜ := by
          intro x hx
          by_cases h : x ∈ U
          · exact Or.inl ⟨h, hx⟩
          · exact Or.inr h
        have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
        have h3 := Set.ncard_union_le (U ∩ nbrs (incidentTwo 𝓗 U) u) Uᶜ
        exact le_trans h2 h3
      have h4 : ((nbrs (incidentTwo 𝓗 U) u).ncard : ℝ)
          ≤ ((U ∩ nbrs (incidentTwo 𝓗 U) u).ncard : ℝ) + ((Uᶜ).ncard : ℝ) := by
        exact_mod_cast h1
      linarith
    have hcompl : ((Uᶜ).ncard : ℝ) ≤ (n : ℝ) - (U.ncard : ℝ) := by
      have h3 : (Uᶜ ∪ U).ncard = (Uᶜ).ncard + U.ncard :=
        Set.ncard_union_eq (Set.disjoint_left.mpr fun x hx1 hx2 => hx1 hx2)
      have h4 : ((Uᶜ ∪ U).ncard : ℝ) = (n : ℝ) := by
        rw [Set.compl_union_self U, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
      have h5 : ((Uᶜ).ncard : ℝ) + (U.ncard : ℝ) = (n : ℝ) := by
        rw [← Nat.cast_add, ← h3]
        exact h4
      linarith [h5]
    linarith [hsd, hcompl, hdegU]
  -- (2) typicality
  have htyp' := (htyp U hU𝓥 u).1
  have hcomp : (U ∩ nbrs R u).ncard = (U ∩ nbrs R u).ncard := rfl
  have hNRU : ρ * ((U ∩ nbrs (incidentTwo 𝓗 U) u).ncard : ℝ) - 10 * γ * (n : ℝ)
      ≤ ((U ∩ nbrs R u).ncard : ℝ) := by
    have h := (abs_le.mp htyp').1
    linarith [h]
  -- (3) pseudorandomness at `S₀ = N_R(u) ∩ U`
  have hmem : U ∩ nbrs R u ∈ absorberFam R U ∪ {U, S} := by
    refine Set.mem_union_left _ ?_
    exact Or.inl ⟨u, (Set.inter_comm (nbrs R u) U).symm⟩
  have hpseudo' := hpseudo (U ∩ nbrs R u) hmem
  have hS0 : γ * ((U ∩ nbrs R u).ncard : ℝ) - κ * (n : ℝ)
      ≤ (((U ∩ nbrs R u) \ matchVert N).ncard : ℝ) := by
    have h := (abs_le.mp hpseudo').1
    linarith [h]
  -- (4) removing `{ul}` and the used neighbours
  have hY : γ * ((U ∩ nbrs R u).ncard : ℝ) - 2 * κ * (n : ℝ) - 1
      ≤ (((((U ∩ nbrs R u) \ matchVert N) \ {ul}) \ nbrs used u).ncard : ℝ) := by
    have h1 : ((((U ∩ nbrs R u) \ matchVert N) \ {ul}).ncard : ℝ)
        ≥ (((U ∩ nbrs R u) \ matchVert N).ncard : ℝ) - 1 := by
      have h := ncard_sdiff_ge ((U ∩ nbrs R u) \ matchVert N) ({ul} : Set (Fin n))
      have h2 : (({ul} : Set (Fin n)).ncard : ℝ) ≤ 1 := by
        rw [Set.ncard_singleton]; norm_num
      linarith
    have h2 : (((((U ∩ nbrs R u) \ matchVert N) \ {ul}) \ nbrs used u).ncard : ℝ)
        ≥ ((((U ∩ nbrs R u) \ matchVert N) \ {ul}).ncard : ℝ) - (nbrs used u).ncard := by
      have h := ncard_sdiff_ge (((U ∩ nbrs R u) \ matchVert N) \ {ul}) (nbrs used u)
      linarith
    have h3 := hused u
    linarith
  -- (5) the counted set lies in `W` and contributes to `degIn`
  have hsub : (((U ∩ nbrs R u) \ matchVert N) \ {ul}) \ nbrs used u ⊆
      {y : Fin n | y ∈ W ∧ ({u, y} : Set (Fin n)) ∈ R \ used} := by
    rintro y ⟨⟨⟨⟨hyU, hyR⟩, hyN⟩, hyul⟩, hyused⟩
    refine ⟨?_, ?_, ?_⟩
    · exact hWge ⟨⟨hyU, hyN⟩, by simpa using hyul⟩
    · exact hyR
    · intro hc
      exact hyused hc
  have hdegIn : (((((U ∩ nbrs R u) \ matchVert N) \ {ul}) \ nbrs used u).ncard : ℝ)
      ≤ (degIn (R \ used) W u : ℝ) := by
    rw [degIn_eq_ncard]
    have h := Set.ncard_le_ncard hsub (Set.toFinite _)
    exact_mod_cast h
  -- (6) the size of `W` is at most `γ|U| + κn`
  have hWsize : ((W.ncard : ℕ) : ℝ) ≤ γ * (U.ncard : ℝ) + κ * (n : ℝ) := by
    have hsubW : W ⊆ U \ matchVert N := hWle
    have h1 : (W.ncard : ℝ) ≤ (((U \ matchVert N).ncard : ℝ)) := by
      have := Set.ncard_le_ncard hsubW (Set.toFinite _)
      exact_mod_cast this
    have hmemU : U ∈ absorberFam R U ∪ {U, S} := by
      refine Set.mem_union_right _ ?_
      exact Set.mem_insert_iff.mpr (Or.inl rfl)
    have h2 := (abs_le.mp (hpseudo U hmemU)).2
    linarith [h1, h2]
  -- (7) assembly
  have hchain : γ * (ρ * ((U.ncard : ℝ) - ε * (n : ℝ)) - 10 * γ * (n : ℝ)) - 2 * κ * (n : ℝ) - 1
      ≤ (degIn (R \ used) W u : ℝ) := by
    have hmono : ρ * ((U.ncard : ℝ) - ε * (n : ℝ)) - 10 * γ * (n : ℝ)
        ≤ ((U ∩ nbrs R u).ncard : ℝ) := by
      have hρ0 : (0 : ℝ) ≤ ρ := le_of_lt hm.hρ
      have h := mul_le_mul_of_nonneg_left hGU hρ0
      linarith [h, hNRU]
    have hmono2 : γ * (ρ * ((U.ncard : ℝ) - ε * (n : ℝ)) - 10 * γ * (n : ℝ)) - 2 * κ * (n : ℝ) - 1
        ≤ γ * ((U ∩ nbrs R u).ncard : ℝ) - 2 * κ * (n : ℝ) - 1 := by
      have := mul_le_mul_of_nonneg_left hmono hγ0
      linarith
    linarith [hmono2, hY, hdegIn]
  have hρnn : (0 : ℝ) ≤ ρ * (n : ℝ) := mul_nonneg (le_of_lt hm.hρ) hn0
  have hγnn : (0 : ℝ) ≤ γ * (n : ℝ) := mul_nonneg (le_of_lt hm.hγ) hn0
  have hγρ0 : (0 : ℝ) ≤ γ * ρ := mul_nonneg hγ0 (le_of_lt hm.hρ)
  have hA : 3 * ρ * (W.ncard : ℝ) / 4
      ≤ 0.75 * (γ * ρ * (U.ncard : ℝ)) + 0.75 * (ρ * κ * (n : ℝ)) := by
    nlinarith [hWsize, hm.hρ]
  have hεn : ε * (n : ℝ) ≤ (n : ℝ) / 4000 := by nlinarith [hm.hε4, hn0]
  have hB : γ * ρ * (ε * (n : ℝ)) ≤ 0.00025 * (γ * ρ * (n : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left hεn hγρ0
    nlinarith [h]
  have hC : 10 * γ * γ * (n : ℝ) ≤ 0.0005 * (γ * ρ * (n : ℝ)) := by
    have h := mul_le_mul_of_nonneg_right hm.hγρ hγnn
    nlinarith [h]
  have hD : 2 * κ * (n : ℝ) ≤ 0.0005 * (γ * ρ * (n : ℝ)) := by
    have h := mul_le_mul_of_nonneg_right hm.hκγρ hn0
    nlinarith [h]
  have hE : 0.75 * ρ * κ * (n : ℝ) ≤ 0.0005 * (γ * ρ * (n : ℝ)) := by
    have h := mul_le_mul_of_nonneg_right hm.hκγ hρnn
    nlinarith [h]
  have hF : 1 ≤ 0.0005 * (γ * ρ * (n : ℝ)) := by nlinarith [hm.hnbig]
  have hG : 0.0025 * (γ * ρ * (n : ℝ)) ≤ 0.25 * (γ * ρ * (U.ncard : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left hUlow hγρ0
    linarith [h]
  exact le_trans (internal_arith_core hA hE hB hC hD hF hG) hchain

/-! ## Turning a matching family into a family of edges of `𝓗` -/

/-- A subfamily of `R` regarded as a family of edges of `𝓗`. -/
def famToSet {𝓗 R : Hypergraph (Fin n)} (h : R ⊆ 𝓗) (M : Set R) : Set 𝓗 :=
  {e : 𝓗 | ∃ e' : R, e' ∈ M ∧ (e' : Set (Fin n)) = (e : Set (Fin n))}

theorem famToSet_mem {𝓗 R : Hypergraph (Fin n)} {h : R ⊆ 𝓗} {M : Set R} {e : 𝓗} :
    e ∈ famToSet h M ↔ ∃ e' : R, e' ∈ M ∧ (e' : Set (Fin n)) = (e : Set (Fin n)) :=
  Iff.rfl

theorem famToSet_subset {𝓗 R : Hypergraph (Fin n)} {h : R ⊆ 𝓗} {M : Set R} :
    ∀ e ∈ famToSet h M, (e : Set (Fin n)) ∈ R := by
  rintro e ⟨e', _, heq⟩
  rw [← heq]
  exact e'.2

theorem famToSet_isMatching {𝓗 R : Hypergraph (Fin n)} {h : R ⊆ 𝓗} {M : Set R}
    (hM : IsMatchingFam M) : IsMatching 𝓗 (famToSet h M) := by
  intro e₁ he₁ e₂ he₂ hne
  obtain ⟨e₁', h1, hr1⟩ := he₁
  obtain ⟨e₂', h2, hr2⟩ := he₂
  refine Set.disjoint_left.mpr (fun x hx₁ hx₂ => ?_)
  have hx₁' : x ∈ (e₁' : Set (Fin n)) := by rw [hr1]; exact hx₁
  have hx₂' : x ∈ (e₂' : Set (Fin n)) := by rw [hr2]; exact hx₂
  have hne' : e₁' ≠ e₂' := fun hc => hne (Subtype.ext (by rw [← hr1, ← hr2, hc]))
  exact (Set.disjoint_left.mp (hM h1 h2 hne')) hx₁' hx₂'

theorem famToSet_covers {𝓗 R : Hypergraph (Fin n)} {h : R ⊆ 𝓗} {M : Set R} {W : Set (Fin n)}
    (hM : CoversFam M W) : ∀ w ∈ W, ∃ e ∈ famToSet h M, w ∈ (e : Set (Fin n)) := by
  intro w hw
  obtain ⟨e', he', hwe'⟩ := hM w hw
  exact ⟨⟨(e' : Set (Fin n)), h e'.2⟩, ⟨e', he', rfl⟩, hwe'⟩

/-- **The perfect-matching step of §7.2.**  An even vertex set `W` on which the
2-edge family `R` has minimum degree `≥ 3ρ|W|/4` and which is upper
`(ρ,ξ')`-regular w.r.t. `R` contains a matching covering `W`. -/
theorem internal_matching_step {𝓗 R : Hypergraph (Fin n)} {W : Set (Fin n)} {ρ ξ : ℝ} {B : ℕ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hξ : 0 ≤ ξ) (hξρ : 10 * ξ ≤ ρ)
    (hB : (B : ℝ) ≤ ρ ^ 2 * (W.ncard : ℝ)) (hmatch : InternalMatchingInput n B)
    (hWeven : Even W.ncard) (hRsub : R ⊆ 𝓗)
    (hsub : ∀ e ∈ R, e ⊆ W) (h2 : ∀ e ∈ R, edgeSize e = 2)
    (hdeg : ∀ w ∈ W, 3 * ρ * (W.ncard : ℝ) / 4 ≤ (degIn R W w : ℝ))
    (hreg : ∀ S T : Finset (Fin n), S ⊆ sfin W → T ⊆ sfin W → Disjoint S T →
      ξ * (W.ncard : ℝ) ≤ (S.card : ℝ) → ξ * (W.ncard : ℝ) ≤ (T.card : ℝ) →
      (edgeCount R S T : ℝ) ≤ (ρ + ξ) * (S.card : ℝ) * (T.card : ℝ)) :
    ∃ M : Set 𝓗, IsMatching 𝓗 M ∧ (∀ e ∈ M, (e : Set (Fin n)) ∈ R) ∧
      ∀ w ∈ W, ∃ e ∈ M, w ∈ (e : Set (Fin n)) := by
  obtain ⟨M, hMmatch, hMcov⟩ := hmatch W R ρ ξ hWeven hρ hξ hξρ hρ1 hB hsub h2 hdeg hreg
  exact ⟨famToSet hRsub M, famToSet_isMatching hMmatch, famToSet_subset, famToSet_covers hMcov⟩

end

end ErdosFaberLovaszConjecture