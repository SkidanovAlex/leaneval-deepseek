import Submission.EFL.HugeAbsorption
import Submission.EFL.InternalStepB
import Submission.Commons.Combinatorics.EFLArith.crossing_arith_a
import Submission.Commons.Combinatorics.EFLArith.crossing_arith_b
import Submission.Commons.Combinatorics.EFLArith.sixth_arith
import Submission.Commons.Combinatorics.EFLArith.internal_arith

/-!
# §7.3: the absorption lemma for huge and medium matchings

This module formalises the paper's Lemma `huge-edge-absorption-lemma`
(Lemma 7.3): matchings that are absorbable either by *smallness* (their
vertex set has at most `γn` vertices) or by *typicality* (and are not
*difficult*) can be extended by edges of `R` so as to have perfect or
nearly-perfect coverage of `U`.

The proof has four ingredients:

* the *crossing* part (`huge_crossing_step`): for a matching `N` with
  `|U ∖ V(N)| ≤ n/100`, a matching of `R`-edges joining `U ∖ V(N)` to
  `(V∖U) ∖ V(N)` covering `U ∖ V(N)`;
* the *internal* part (`huge_internal_step`): for `|U ∖ V(N)| > n/100`, a
  matching covering all but at most one vertex of `U ∖ V(N)` inside
  `U ∖ V(N)`, together with the choice of the defect vertex;
* two iterations (`huge_iter_cov`, `huge_iter_defect`) over the matchings;
* the assembly (`huge_edge_absorption`).
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}
variable {ρ ε γ κ ξ : ℝ}

/-! ## The numeric margins of §7.3 -/

/-- The numeric margin hierarchy of §7.3, in the concrete form needed by the
estimates: `0 < 1/n ≪ ξ ≪ κ ≪ γ ≪ ρ, ε ≪ 1`. -/
structure HugeMargins (n : ℕ) (ρ ε γ κ ξ : ℝ) : Prop where
  hρ : 0 < ρ
  hρ1 : ρ ≤ 1
  hε : 0 < ε
  hγ : 0 < γ
  hκ : 0 < κ
  hξ : 0 < ξ
  /-- `ε` is small: `1000ε ≤ 1`. -/
  hεsmall : 1000 * ε ≤ 1
  /-- `γ ≪ ρε`. -/
  hγε : 1000 * γ ≤ ρ * ε
  /-- `1/n ≪ γρ`. -/
  hnbig : 2000 ≤ γ * ρ * (n : ℝ)
  /-- `ξ ≪ γρ`. -/
  hξγρ : 4000 * ξ ≤ γ * ρ

/-! ## Elementary cardinality lemmas -/

/-- `|A| ≤ |A ∩ B| + |Bᶜ|`. -/
theorem ncard_le_ncard_inter_add (A B : Set (Fin n)) :
    (A.ncard : ℝ) ≤ ((A ∩ B).ncard : ℝ) + (Bᶜ).ncard := by
  have h : A ⊆ (A ∩ B) ∪ Bᶜ := fun x hx => by
    by_cases hb : x ∈ B
    · exact Or.inl ⟨hx, hb⟩
    · exact Or.inr hb
  have h1 : A.ncard ≤ ((A ∩ B) ∪ Bᶜ).ncard := Set.ncard_le_ncard h (Set.toFinite _)
  have h2 : ((A ∩ B) ∪ Bᶜ).ncard ≤ (A ∩ B).ncard + (Bᶜ).ncard := Set.ncard_union_le _ _
  have h3 : (A.ncard : ℝ) ≤ (((A ∩ B) ∪ Bᶜ).ncard : ℝ) := by exact_mod_cast h1
  have h4 : (((A ∩ B) ∪ Bᶜ).ncard : ℝ) ≤ ((A ∩ B).ncard : ℝ) + (Bᶜ).ncard := by
    exact_mod_cast h2
  linarith

/-- `|Bᶜ| ≤ n - |B|` is an equality on `Fin n`. -/
theorem ncard_compl_eq (B : Set (Fin n)) : (Bᶜ).ncard = n - B.ncard := by
  have h := Set.ncard_compl_add_ncard B (Set.toFinite _)
  have h2 : Nat.card (Fin n) = n := by simp [Nat.card_eq_fintype_card]
  rw [h2] at h
  omega

/-- Monotonicity of `Set.ncard` in `ℝ`. -/
theorem ncard_le_ncard_real {A B : Set (Fin n)} (h : A ⊆ B) :
    (A.ncard : ℝ) ≤ (B.ncard : ℝ) := by
  have := Set.ncard_le_ncard h (Set.toFinite _)
  exact_mod_cast this

/-- From `2000 ≤ γρn`, `ρ ≤ 1` and `1000γ ≤ ρε ≤ ρ` we get `ρn ≥ 2000000`. -/
theorem rho_mul_n_ge (hm : HugeMargins n ρ ε γ κ ξ) : (2000000 : ℝ) ≤ ρ * (n : ℝ) := by
  have hρ0 : (0 : ℝ) < ρ := hm.hρ
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hε1 : ε ≤ 1 := by linarith [hm.hεsmall]
  have hγρ : 1000 * γ ≤ ρ := by
    have h := hm.hγε
    nlinarith [h, hρ0, hε1]
  have h1 : γ * ρ * (n : ℝ) ≤ (ρ * (n : ℝ)) * ρ / 1000 := by
    have h2 : γ ≤ ρ / 1000 := by linarith
    have h3 : γ * ρ * (n : ℝ) ≤ (ρ / 1000) * ρ * (n : ℝ) := by
      have := mul_le_mul_of_nonneg_right h2 (mul_nonneg (le_of_lt hρ0) hn0)
      nlinarith [this]
    nlinarith [h3]
  have h4 : (2000 : ℝ) ≤ (ρ * (n : ℝ)) * ρ / 1000 := le_trans hm.hnbig h1
  nlinarith [h4, hρ0, hm.hρ1]

/-- Cast of `ncard_compl_eq`. -/
theorem ncard_compl_cast (B : Set (Fin n)) : ((Bᶜ).ncard : ℝ) = (n : ℝ) - (B.ncard : ℝ) := by
  have hle : B.ncard ≤ n := by
    have h := Set.ncard_le_ncard (Set.subset_univ B) (Set.toFinite _)
    simpa [Nat.card_eq_fintype_card] using h
  rw [ncard_compl_eq B, Nat.cast_sub hle]

/-- `γ ≤ 1/1000` from `1000γ ≤ ρε ≤ ρ ≤ 1`. -/
theorem gamma_le_thousandth (hm : HugeMargins n ρ ε γ κ ξ) : γ ≤ 1 / 1000 := by
  have hε1 : ε ≤ 1 := by linarith [hm.hεsmall]
  have h1 : ρ * ε ≤ ρ * 1 := mul_le_mul_of_nonneg_left hε1 (le_of_lt hm.hρ)
  have h2 : 1000 * γ ≤ ρ := le_trans hm.hγε (by simpa using h1)
  have h3 : ρ ≤ 1 := hm.hρ1
  linarith

/-- Subtracting the already used edges from a neighbourhood loses at most `K`
vertices. -/
theorem ncard_inter_nbrs_sdiff_ge (R used : Hypergraph (Fin n)) (A : Set (Fin n))
    (u : Fin n) {K : ℕ} (hused : (nbrs used u).ncard ≤ K) :
    ((A ∩ nbrs R u).ncard : ℝ) - (K : ℝ) ≤ ((A ∩ nbrs (R \ used) u).ncard : ℝ) := by
  have hset : A ∩ nbrs (R \ used) u = (A ∩ nbrs R u) \ nbrs used u := by
    rw [nbrs_sdiff]
    ext w
    simp only [Set.mem_inter_iff, Set.mem_sdiff]
    tauto
  rw [hset]
  have h := ncard_sdiff_ge (A ∩ nbrs R u) (nbrs used u)
  have h2 : ((nbrs used u).ncard : ℝ) ≤ (K : ℝ) := by exact_mod_cast hused
  linarith

/-! ## The crossing degree bound -/

/-- **Case (b) of the crossing degree bound**: `N` absorbable by typicality and
not difficult. -/
theorem huge_cross_degree_b {𝓗 R used : Hypergraph (Fin n)} {𝓥 : Set (Set (Fin n))}
    {U : Set (Fin n)} {N : Set 𝓗} {K : ℕ} {u : Fin n}
    (hm : HugeMargins n ρ ε γ κ ξ)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (htyp : Typical (incidentTwo 𝓗 U) R ρ (10 * γ) 𝓥)
    (hX𝓥 : U ∪ matchVert N ∈ 𝓥)
    (hVN : ((matchVert N).ncard : ℝ) ≤ ((3 : ℝ) / 4 + ε) * (n : ℝ))
    (hused : ∀ v : Fin n, (nbrs used v).ncard ≤ K)
    (hK : (K : ℝ) ≤ γ * (n : ℝ))
    (hUle : ((U \ matchVert N).ncard : ℝ) ≤ (n : ℝ) / 100)
    (hu : u ∈ U \ matchVert N) :
    ρ * (n : ℝ) / 7 ≤ ((nbrs (R \ used) u ∩ ((U ∪ matchVert N)ᶜ : Set (Fin n))).ncard : ℝ) := by
  classical
  set X : Set (Fin n) := U ∪ matchVert N with hXdef
  have huU : u ∈ U := hu.1
  have hXn : (X.ncard : ℝ) ≤ ((U \ matchVert N).ncard : ℝ) + ((matchVert N).ncard : ℝ) := by
    have h1 : X ⊆ (U \ matchVert N) ∪ matchVert N := by
      rintro x (hx | hx)
      · by_cases hxN : x ∈ matchVert N
        · exact Or.inr hxN
        · exact Or.inl ⟨hx, hxN⟩
      · exact Or.inr hx
    have h2 := ncard_le_ncard_real h1
    have h3 := Set.ncard_union_le (U \ matchVert N) (matchVert N)
    have h4 : (((U \ matchVert N) ∪ matchVert N).ncard : ℝ)
        ≤ ((U \ matchVert N).ncard : ℝ) + ((matchVert N).ncard : ℝ) := by
      exact_mod_cast h3
    linarith
  have hXc : (n : ℝ) / 6 ≤ ((Xᶜ).ncard : ℝ) := by
    rw [ncard_compl_cast X]
    have hε1 : ε ≤ 1 / 1000 := by linarith [hm.hεsmall]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [hε1, hn0]
  -- the `G'`-degree of `u`
  have hG'deg : (1 - ε) * (n : ℝ) ≤ ((nbrs (incidentTwo 𝓗 U) u).ncard : ℝ) := by
    have h := hUdeg u huU
    rwa [degAt] at h
  have hcomplG' : (((nbrs (incidentTwo 𝓗 U) u)ᶜ).ncard : ℝ) ≤ ε * (n : ℝ) := by
    rw [ncard_compl_cast (nbrs (incidentTwo 𝓗 U) u)]
    linarith
  have hG'X : ((Xᶜ).ncard : ℝ) - ε * (n : ℝ)
      ≤ ((Xᶜ ∩ nbrs (incidentTwo 𝓗 U) u).ncard : ℝ) := by
    have h := ncard_le_ncard_inter_add (Xᶜ) (nbrs (incidentTwo 𝓗 U) u)
    linarith
  have hRlow : ρ * ((Xᶜ ∩ nbrs (incidentTwo 𝓗 U) u).ncard : ℝ) - 10 * γ * (n : ℝ)
      ≤ ((Xᶜ ∩ nbrs R u).ncard : ℝ) := by
    have hX𝓥' : X ∈ 𝓥 := hX𝓥
    have h := (abs_le.mp ((htyp X hX𝓥') u).2).1
    linarith
  have hstep : ρ * ((Xᶜ).ncard : ℝ) - ρ * ε * (n : ℝ) - 10 * γ * (n : ℝ)
      ≤ ((Xᶜ ∩ nbrs R u).ncard : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hG'X (le_of_lt hm.hρ)
    have h2 : ρ * (((Xᶜ).ncard : ℝ) - ε * (n : ℝ))
        = ρ * ((Xᶜ).ncard : ℝ) - ρ * ε * (n : ℝ) := by ring
    linarith [h, hRlow, h2]
  have hsub := ncard_inter_nbrs_sdiff_ge R used (Xᶜ) u (hused u)
  have harith := Commons.Combinatorics.EFLArith.crossing_arith_b (n := n) hm.hρ hm.hγ hm.hγε hm.hεsmall
  have hcastK : (K : ℝ) ≤ γ * (n : ℝ) := hK
  have hgoal : ρ * (n : ℝ) / 7
      ≤ ((Xᶜ ∩ nbrs (R \ used) u).ncard : ℝ) := by
    have hρ6 : ρ * ((n : ℝ) / 6) - ρ * ε * (n : ℝ) - 11 * γ * (n : ℝ)
        ≤ ((Xᶜ ∩ nbrs (R \ used) u).ncard : ℝ) := by
      linarith [hstep, hsub, hcastK, hXc, mul_le_mul_of_nonneg_left hXc (le_of_lt hm.hρ)]
    have h1 : ρ * ((n : ℝ) / 6 - ε * (n : ℝ)) - 11 * γ * (n : ℝ)
        = ρ * ((n : ℝ) / 6) - ρ * ε * (n : ℝ) - 11 * γ * (n : ℝ) := by ring
    linarith [harith, hρ6, h1]
  have hset : Xᶜ ∩ nbrs (R \ used) u = nbrs (R \ used) u ∩ Xᶜ := Set.inter_comm _ _
  rwa [hset] at hgoal

/-- `|A| - |B| - |C| ≤ |A \ (B ∪ C)|`. -/
theorem ncard_sdiff_union_ge (A B C : Set (Fin n)) :
    (A.ncard : ℝ) - (B.ncard : ℝ) - (C.ncard : ℝ) ≤ ((A \ (B ∪ C)).ncard : ℝ) := by
  have h1 : A ⊆ (A \ (B ∪ C)) ∪ (B ∪ C) := fun x hx => by
    by_cases h : x ∈ B ∪ C
    · exact Or.inr h
    · exact Or.inl ⟨hx, h⟩
  have h2 : A.ncard ≤ ((A \ (B ∪ C)) ∪ (B ∪ C)).ncard := Set.ncard_le_ncard h1 (Set.toFinite _)
  have h3 : ((A \ (B ∪ C)) ∪ (B ∪ C)).ncard ≤ (A \ (B ∪ C)).ncard + (B ∪ C).ncard :=
    Set.ncard_union_le _ _
  have h4 : (B ∪ C).ncard ≤ B.ncard + C.ncard := Set.ncard_union_le _ _
  have h5 : (A.ncard : ℝ) ≤ ((A \ (B ∪ C)).ncard : ℝ) + ((B ∪ C).ncard : ℝ) := by
    exact_mod_cast le_trans h2 h3
  have h6 : (((B ∪ C).ncard : ℕ) : ℝ) ≤ (B.ncard : ℝ) + (C.ncard : ℝ) := by exact_mod_cast h4
  linarith

/-- **Case (a) of the crossing degree bound**: `N` absorbable by smallness. -/
theorem huge_cross_degree_a {𝓗 R used : Hypergraph (Fin n)} {𝓥 : Set (Set (Fin n))}
    {U : Set (Fin n)} {N : Set 𝓗} {K : ℕ} {u : Fin n}
    (hm : HugeMargins n ρ ε γ κ ξ)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (htyp : Typical (incidentTwo 𝓗 U) R ρ (10 * γ) 𝓥)
    (hU𝓥 : U ∈ 𝓥)
    (hVN : ((matchVert N).ncard : ℝ) ≤ γ * (n : ℝ))
    (hused : ∀ v : Fin n, (nbrs used v).ncard ≤ K)
    (hK : (K : ℝ) ≤ γ * (n : ℝ))
    (hUle : ((U \ matchVert N).ncard : ℝ) ≤ (n : ℝ) / 100)
    (hu : u ∈ U \ matchVert N) :
    ρ * (n : ℝ) / 7 ≤ ((nbrs (R \ used) u ∩ ((U ∪ matchVert N)ᶜ : Set (Fin n))).ncard : ℝ) := by
  classical
  have huU : u ∈ U := hu.1
  -- `|U| ≤ n/50`
  have hU50 : ((U : Set (Fin n)).ncard : ℝ) ≤ (n : ℝ) / 50 := by
    have h1 : U ⊆ (U \ matchVert N) ∪ matchVert N := fun x hx => by
      by_cases h : x ∈ matchVert N
      · exact Or.inr h
      · exact Or.inl ⟨hx, h⟩
    have h2 := ncard_le_ncard_real h1
    have h3 := Set.ncard_union_le (U \ matchVert N) (matchVert N)
    have h4 : (((U \ matchVert N) ∪ matchVert N).ncard : ℝ)
        ≤ ((U \ matchVert N).ncard : ℝ) + ((matchVert N).ncard : ℝ) := by exact_mod_cast h3
    have hγ1 : γ ≤ 1 / 1000 := gamma_le_thousandth (n := n) (ρ := ρ) (ε := ε) (γ := γ) (κ := κ) (ξ := ξ) hm
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h5 : γ * (n : ℝ) ≤ (n : ℝ) / 1000 := by nlinarith [hγ1, hn0]
    linarith
  -- `|N_{G'}(u) \ U| ≥ (49/50 - ε)n`
  have hG'deg : (1 - ε) * (n : ℝ) ≤ ((nbrs (incidentTwo 𝓗 U) u).ncard : ℝ) := by
    have h := hUdeg u huU
    rwa [degAt] at h
  have hout : ((49 : ℝ) / 50 - ε) * (n : ℝ)
      ≤ (((nbrs (incidentTwo 𝓗 U) u) \ U).ncard : ℝ) := by
    have h1 : (nbrs (incidentTwo 𝓗 U) u) ⊆
        ((nbrs (incidentTwo 𝓗 U) u) ∩ U) ∪ ((nbrs (incidentTwo 𝓗 U) u) \ U) := fun x hx => by
      by_cases h : x ∈ U
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    have h2 := ncard_le_ncard_real h1
    have h3 := Set.ncard_union_le ((nbrs (incidentTwo 𝓗 U) u) ∩ U)
      ((nbrs (incidentTwo 𝓗 U) u) \ U)
    have h4 : ((((nbrs (incidentTwo 𝓗 U) u) ∩ U) ∪ ((nbrs (incidentTwo 𝓗 U) u) \ U)).ncard : ℝ)
        ≤ (((nbrs (incidentTwo 𝓗 U) u) ∩ U).ncard : ℝ)
          + (((nbrs (incidentTwo 𝓗 U) u) \ U).ncard : ℝ) := by exact_mod_cast h3
    have h5 : (((nbrs (incidentTwo 𝓗 U) u) ∩ U).ncard : ℝ) ≤ ((U : Set (Fin n)).ncard : ℝ) :=
      ncard_le_ncard_real Set.inter_subset_right
    linarith
  have hUcG' : (Uᶜ ∩ nbrs (incidentTwo 𝓗 U) u) = ((nbrs (incidentTwo 𝓗 U) u) \ U) := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
    tauto
  have hRlow : ρ * ((49 : ℝ) / 50 - ε) * (n : ℝ) - 10 * γ * (n : ℝ)
      ≤ ((Uᶜ ∩ nbrs R u).ncard : ℝ) := by
    have h := (abs_le.mp ((htyp U hU𝓥) u).2).1
    rw [hUcG'] at h
    have h2 := mul_le_mul_of_nonneg_left hout (le_of_lt hm.hρ)
    linarith
  -- subtract `V(N)` and `used`
  have hUn : (Uᶜ ∩ nbrs R u) \ (matchVert N ∪ nbrs used u)
      ⊆ nbrs (R \ used) u ∩ (U ∪ matchVert N)ᶜ := by
    intro w hw
    rw [Set.mem_sdiff] at hw
    obtain ⟨hw1, hw2⟩ := hw
    rw [Set.mem_inter_iff] at hw1
    rw [Set.mem_union, not_or] at hw2
    refine ⟨?_, ?_⟩
    · rw [nbrs_sdiff, Set.mem_sdiff]
      exact ⟨hw1.2, hw2.2⟩
    · rw [Set.mem_compl_iff, Set.mem_union, not_or]
      exact ⟨hw1.1, hw2.1⟩
  have hsub : ((Uᶜ ∩ nbrs R u).ncard : ℝ) - ((matchVert N).ncard : ℝ) - (K : ℝ)
      ≤ ((nbrs (R \ used) u ∩ (U ∪ matchVert N)ᶜ).ncard : ℝ) := by
    have h1 : (((Uᶜ ∩ nbrs R u) \ (matchVert N ∪ nbrs used u)).ncard : ℝ)
        ≤ ((nbrs (R \ used) u ∩ (U ∪ matchVert N)ᶜ).ncard : ℝ) := ncard_le_ncard_real hUn
    have h2 := ncard_sdiff_union_ge (Uᶜ ∩ nbrs R u) (matchVert N) (nbrs used u)
    have h3 : ((nbrs used u).ncard : ℝ) ≤ (K : ℝ) := by exact_mod_cast hused u
    linarith
  have harith := Commons.Combinatorics.EFLArith.crossing_arith_a (n := n) hm.hρ hm.hγ hm.hγε hm.hεsmall
  linarith [harith, hRlow, hsub, hK, hVN]

/-! ## The crossing step of Lemma 7.3 -/

/-- **The crossing degree bound of Lemma 7.3** (both alternatives). -/
theorem huge_cross_degree {𝓗 R used : Hypergraph (Fin n)} {U S : Set (Fin n)}
    {N : Set 𝓗} {K : ℕ} {u : Fin n}
    (hm : HugeMargins n ρ ε γ κ ξ)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (habs : AbsorbableBySmall 𝓗 N R U S ρ ε γ κ ξ ∨
      (AbsorbableByTypical 𝓗 N R U S ρ ε γ κ ξ ∧ ¬ IsDifficult U N))
    (hn : 4 ≤ n)
    (hused : ∀ v : Fin n, (nbrs used v).ncard ≤ K)
    (hK : (K : ℝ) ≤ γ * (n : ℝ))
    (hUle : ((U \ matchVert N).ncard : ℝ) ≤ (n : ℝ) / 100)
    (hu : u ∈ U \ matchVert N) :
    ρ * (n : ℝ) / 7 ≤ ((nbrs (R \ used) u ∩ (U ∪ matchVert N)ᶜ).ncard : ℝ) := by
  rcases habs with ⟨⟨𝓥, hU𝓥, -, habsor⟩, -, hsmall⟩ | habsT
  · exact huge_cross_degree_a (N := N) (K := K) (u := u) (𝓥 := 𝓥) hm hUdeg habsor.2.1
      hU𝓥 hsmall hused hK hUle hu
  · obtain ⟨hAbT, hnd⟩ := habsT
    have hVNle : ((matchVert N).ncard : ℝ) ≤ ((3 : ℝ) / 4 + ε) * (n : ℝ) :=
      card_matchVert_le_of_not_difficult hAbT hnd hn
    obtain ⟨𝓥, hU𝓥, -, hX𝓥, -, habsor, hnotR, hVNU⟩ := hAbT
    exact huge_cross_degree_b (N := N) (K := K) (u := u) (𝓥 := 𝓥) hm hUdeg habsor.2.1
      hX𝓥 hVNle hused hK hUle hu

/-- The degree bound in the crossing step implies the filter-cardinality bound
required by the matching propositions. -/
theorem card_filter_cross_ge {𝓗 : Hypergraph (Fin n)} {R' : Hypergraph (Fin n)}
    {U : Set (Fin n)} {N : Set 𝓗} {A VN : Finset (Fin n)} {a : Fin n}
    (hA : ∀ x : Fin n, x ∈ A ↔ x ∈ U ∧ x ∉ matchVert N)
    (hVN : ∀ x : Fin n, x ∈ VN ↔ x ∈ matchVert N) :
    (nbrs R' a ∩ (U ∪ matchVert N)ᶜ).ncard ≤
      (((Finset.univ \ A).filter
        (fun b => ({a, b} : Set (Fin n)) ∈ R' ∧ b ∉ VN))).card := by
  classical
  rw [← card_sfin]
  refine Finset.card_le_card (fun b hb => ?_)
  rw [mem_sfin] at hb
  obtain ⟨hbR, hbU⟩ := hb
  rw [Set.mem_compl_iff, Set.mem_union, not_or] at hbU
  rw [Finset.mem_filter]
  refine ⟨?_, hbR, ?_⟩
  · rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ b, fun h => hbU.1 ((hA b).mp h).1⟩
  · rw [hVN]
    exact hbU.2

/-- **The crossing step of Lemma 7.3.**  If `|U ∖ V(N)| ≤ n/100` then there is
a matching of `R`-edges avoiding `used` that covers `U ∖ V(N)`. -/
theorem huge_cross_step {𝓗 R R' used : Hypergraph (Fin n)} {U S : Set (Fin n)}
    {N : Set 𝓗} {K B : ℕ}
    (hR' : R' = R \ used)
    (hm : HugeMargins n ρ ε γ κ ξ) (hmatch : InternalMatchingInput n B)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (habs : AbsorbableBySmall 𝓗 N R U S ρ ε γ κ ξ ∨
      (AbsorbableByTypical 𝓗 N R U S ρ ε γ κ ξ ∧ ¬ IsDifficult U N))
    (hn : 4 ≤ n)
    (hused : ∀ v : Fin n, (nbrs used v).ncard ≤ K)
    (hK : (K : ℝ) ≤ γ * (n : ℝ))
    (hUle : ((U \ matchVert N).ncard : ℝ) ≤ (n : ℝ) / 100) :
    ∃ Nabs : Set 𝓗, IsMatching 𝓗 Nabs ∧
      (∀ e ∈ Nabs, (e : Set (Fin n)) ∈ R ∧ (e : Set (Fin n)) ∉ used) ∧
      Disjoint (matchVert Nabs) (matchVert N) ∧
      Covers Nabs (U \ matchVert N) := by
  classical
  have habsorOf : R ⊆ incidentTwo 𝓗 U := by
    rcases habs with ⟨⟨𝓥, -, -, habsor⟩, -, -⟩ | ⟨⟨𝓥, -, -, -, -, habsor, -, -⟩, -⟩
    · exact habsor.1
    · exact habsor.1
  have hdeg7 : ∀ a ∈ U \ matchVert N, ρ * (n : ℝ) / 7 ≤
      ((nbrs R' a ∩ (U ∪ matchVert N)ᶜ).ncard : ℝ) := by
    intro a ha
    have h := huge_cross_degree (N := N) (K := K) (u := a) (used := used) hm hUdeg habs
      hn hused hK hUle ha
    rwa [← hR'] at h
  set Af : Finset (Fin n) := sfin (U \ matchVert N) with hAfdef
  set VN : Finset (Fin n) := sfin (matchVert N) with hVNdef
  have hmemAf : ∀ x : Fin n, x ∈ Af ↔ x ∈ U ∧ x ∉ matchVert N := by
    intro x
    rw [hAfdef, mem_sfin, Set.mem_sdiff]
  have hmemVN : ∀ x : Fin n, x ∈ VN ↔ x ∈ matchVert N := by
    intro x
    rw [hVNdef, mem_sfin]
  have hcardAf : (Af.card : ℝ) = ((U \ matchVert N).ncard : ℝ) := by
    rw [hAfdef, card_sfin]
  have hR'sub : R' ⊆ R := fun e he => by rw [hR'] at he; exact he.1
  have hR'notmem : ∀ e : Set (Fin n), e ∈ R' → e ∉ used := fun e he => by
    rw [hR'] at he
    exact he.2
  -- the filter-form degree bound
  have hdeg : ∀ a ∈ Af, 2 * ρ * (Af.card : ℝ) ≤
      ((((Finset.univ \ Af) : Finset (Fin n)).filter
        (fun b => ({a, b} : Set (Fin n)) ∈ R' ∧ b ∉ VN)).card : ℝ) := by
    intro a ha
    have ha' : a ∈ U \ matchVert N := by
      rw [Set.mem_sdiff]
      exact (hmemAf a).mp ha
    have h1 := hdeg7 a ha'
    have h2 : (((nbrs R' a ∩ (U ∪ matchVert N)ᶜ).ncard : ℝ))
        ≤ (((Finset.univ \ Af).filter
            (fun b => ({a, b} : Set (Fin n)) ∈ R' ∧ b ∉ VN)).card : ℝ) := by
      have hh := card_filter_cross_ge (R' := R') (U := U) (N := N) (A := Af) (VN := VN)
        (a := a) hmemAf hmemVN
      exact_mod_cast hh
    have h3 : 2 * ρ * (Af.card : ℝ) ≤ 2 * ρ * ((n : ℝ) / 100) := by
      rw [hcardAf]
      exact mul_le_mul_of_nonneg_left hUle (by linarith [hm.hρ])
    have h4 : 2 * ((n : ℝ) / 100) ≤ (n : ℝ) / 7 := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have h5 : 2 * ρ * ((n : ℝ) / 100) ≤ ρ * (n : ℝ) / 7 := by
      have := mul_le_mul_of_nonneg_left h4 (le_of_lt hm.hρ)
      linarith
    linarith
  -- upper regularity of `R'`
  have hreg : ∀ S T : Finset (Fin n), Disjoint S T →
      ξ * (n : ℝ) ≤ (S.card : ℝ) → ξ * (n : ℝ) ≤ (T.card : ℝ) →
      (edgeCount R' S T : ℝ) ≤ (ρ + ξ) * (S.card : ℝ) * (T.card : ℝ) := by
    intro S T hdisj hS hT
    have h1 : (edgeCount R' S T : ℝ) ≤ (edgeCount R S T : ℝ) := by
      exact_mod_cast edgeCount_mono hR'sub S T
    have hup : UpperRegular (incidentTwo 𝓗 U) R ρ ξ := by
      rcases habs with ⟨⟨𝓥, -, -, habsor⟩, -, -⟩ | ⟨⟨𝓥, -, -, -, -, habsor, -, -⟩, -⟩
      · exact habsor.2.2
      · exact habsor.2.2
    have h2 := hup S T hdisj hS hT
    have h3 : (edgeCount (incidentTwo 𝓗 U) S T : ℝ) ≤ (S.card : ℝ) * (T.card : ℝ) := by
      have := edgeCount_le_card_mul (incidentTwo 𝓗 U) S T
      exact_mod_cast this
    have hρ0 : (0 : ℝ) ≤ ρ := le_of_lt hm.hρ
    nlinarith [h1, h2, h3]
  -- the construction of the absorbing matching
  have build : ∀ (Bf : Finset (Fin n))
      (f : {a : Fin n // a ∈ Af} → {b : Fin n // b ∈ Bf})
      (hdisj : Disjoint Af Bf)
      (hfv : ∀ a : {a : Fin n // a ∈ Af}, (f a).1 ∉ matchVert N)
      (hfinj : Function.Injective f)
      (hfm : ∀ a : {a : Fin n // a ∈ Af}, ({a.1, (f a).1} : Set (Fin n)) ∈ R'),
      ∃ Nabs : Set 𝓗, IsMatching 𝓗 Nabs ∧
        (∀ e ∈ Nabs, (e : Set (Fin n)) ∈ R ∧ (e : Set (Fin n)) ∉ used) ∧
        Disjoint (matchVert Nabs) (matchVert N) ∧ Covers Nabs (U \ matchVert N) := by
    intro Bf f hdisj hfv hfinj hfm
    set Nabs : Set 𝓗 := {e : 𝓗 | ∃ a : {a : Fin n // a ∈ Af},
      (e : Set (Fin n)) = ({a.1, (f a).1} : Set (Fin n))} with hNabsdef
    have hmem𝓗 : ∀ a : {a : Fin n // a ∈ Af}, ({a.1, (f a).1} : Set (Fin n)) ∈ 𝓗 :=
      fun a => incidentTwo_subset_self (habsorOf (hR'sub (hfm a)))
    refine ⟨Nabs, ?_, ?_, ?_, ?_⟩
    · rw [hNabsdef]
      exact isMatching_pairImage hdisj f hfinj hmem𝓗
    · intro e he
      rw [hNabsdef] at he
      obtain ⟨a, ha⟩ := he
      rw [ha]
      exact ⟨hR'sub (hfm a), hR'notmem _ (hfm a)⟩
    · rw [Set.disjoint_left]
      intro x hx hxN
      rw [hNabsdef, matchVert_pairImage f hmem𝓗] at hx
      rcases hx with ⟨a, ha⟩ | ⟨a, ha⟩
      · rw [ha] at hxN
        exact ((hmemAf a.1).mp a.2).2 hxN
      · rw [ha] at hxN
        exact hfv a hxN
    · intro x hx
      have hxAf : x ∈ Af := (hmemAf x).mpr hx
      rw [mem_matchVert]
      refine ⟨⟨({x, (f ⟨x, hxAf⟩).1} : Set (Fin n)), hmem𝓗 ⟨x, hxAf⟩⟩,
        ⟨⟨x, hxAf⟩, rfl⟩, ?_⟩
      simp
  by_cases hbig : ξ * (n : ℝ) ≤ ρ * (Af.card : ℝ)
  · obtain ⟨f, hfinj, hf⟩ := exists_matching_covering_of_upperRegular (R := R')
      (A := Af) (VN := VN) hm.hρ (le_of_lt hm.hξ) (by
        have hγρ : γ ≤ ρ := by
          have h := hm.hγε
          have hε1 : ε ≤ 1 := by linarith [hm.hεsmall]
          nlinarith [h, le_of_lt hm.hρ, hε1]
        nlinarith [hm.hξγρ, hγρ, hm.hρ, hm.hρ1]) hdeg hbig hreg
    have hfv : ∀ a : {a : Fin n // a ∈ Af}, (f a).1 ∉ matchVert N := by
      intro a
      exact fun hV => (hf a).2 ((hmemVN _).mpr hV)
    have hdisj : Disjoint Af (Finset.univ \ Af) := Finset.disjoint_sdiff
    exact build (Finset.univ \ Af) f hdisj hfv hfinj (fun a => (hf a).1)
  · -- the greedy case
    have hξρ2 : 7 * ξ ≤ ρ ^ 2 := by
      have h2 : 4000 * ξ ≤ γ * ρ := hm.hξγρ
      have h3 : γ * ρ ≤ ρ ^ 2 := by
        have hγρ1 : γ ≤ ρ := by
          have h := hm.hγε
          have hε1 : ε ≤ 1 := by linarith [hm.hεsmall]
          nlinarith [h, le_of_lt hm.hρ, hε1]
        nlinarith [hγρ1, le_of_lt hm.hρ, hm.hρ1]
      nlinarith [h2, h3]
    set Bg : Finset (Fin n) := Finset.univ \ (Af ∪ VN) with hBgdef
    have hmemBg : ∀ x : Fin n, x ∈ Bg ↔ x ∉ U ∧ x ∉ matchVert N := by
      intro x
      simp only [hBgdef, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
        not_or, hmemAf, hmemVN]
      constructor
      · rintro ⟨h1, h2⟩
        rw [not_and_or] at h1
        rcases h1 with h1 | h1
        · exact ⟨h1, h2⟩
        · exact absurd h2 h1
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [not_and_or]; exact Or.inl h1, h2⟩
    have hgreedy : ∀ a ∈ Af, Af.card <
        (Bg.filter (fun b => ({a, b} : Set (Fin n)) ∈ R')).card := by
      intro a ha
      have ha' : a ∈ U \ matchVert N := by
        rw [Set.mem_sdiff]
        exact (hmemAf a).mp ha
      have h1 := hdeg7 a ha'
      have h2 : ((nbrs R' a ∩ (U ∪ matchVert N)ᶜ).ncard : ℝ) ≤
          ((Bg.filter (fun b => ({a, b} : Set (Fin n)) ∈ R')).card : ℝ) := by
        rw [← card_sfin]
        have hle : (sfin (nbrs R' a ∩ (U ∪ matchVert N)ᶜ)).card ≤
            (Bg.filter (fun b => ({a, b} : Set (Fin n)) ∈ R')).card := by
          refine Finset.card_le_card (fun b hb => ?_)
          rw [mem_sfin] at hb
          obtain ⟨hbR, hbU⟩ := hb
          rw [Set.mem_compl_iff, Set.mem_union, not_or] at hbU
          rw [Finset.mem_filter]
          exact ⟨(hmemBg b).mpr ⟨hbU.1, hbU.2⟩, hbR⟩
        exact_mod_cast hle
      have h3 : (Af.card : ℝ) < ξ * (n : ℝ) / ρ := by
        rw [not_le] at hbig
        rw [lt_div_iff₀ hm.hρ]
        linarith [hbig]
      have h4 : ξ * (n : ℝ) / ρ ≤ ρ * (n : ℝ) / 7 := by
        rw [div_le_iff₀ hm.hρ]
        nlinarith [hξρ2, show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n]
      have h5 : (Af.card : ℝ) < ((Bg.filter
            (fun b => ({a, b} : Set (Fin n)) ∈ R')).card : ℝ) := by linarith
      exact_mod_cast h5
    obtain ⟨f, hfinj, hf⟩ := exists_matching_covering_of_greedy (R := R')
      (A := Af) (B := Bg) hgreedy
    have hdisj : Disjoint Af Bg := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      have h := (hmemBg x).mp hx'
      exact h.1 ((hmemAf x).mp hx).1
    have hfv : ∀ a : {a : Fin n // a ∈ Af}, (f a).1 ∉ matchVert N :=
      fun a => ((hmemBg (f a).1).mp (f a).2).2
    exact build Bg f hdisj hfv hfinj (fun a => hf a)

/-! ## The internal degree bound of Lemma 7.3 -/

/-- `degIn` is the `ncard` of the intersection with the neighbourhood. -/
theorem degIn_eq_inter_nbrs (R : Hypergraph (Fin n)) (W : Set (Fin n)) (u : Fin n) :
    degIn R W u = (W ∩ nbrs R u).ncard := by
  rw [degIn_eq_ncard]
  rfl

/-- **The internal degree bound of Lemma 7.3.**  For `w ∈ W` with
`W ⊆ U ∖ V(N)` and `(U ∖ V(N)) ⊆ W ∪ {u}` (the removed vertex `u`), and
`|W| ≥ n/200 - 1`, the degree of `w` in `restr (R ∖ used) W` is at least
`3ρ|W|/4`. -/
theorem huge_internal_degree {𝓗 R used : Hypergraph (Fin n)}
    {U S : Set (Fin n)} {N : Set 𝓗} {K : ℕ} {u w : Fin n} {W : Set (Fin n)}
    (hm : HugeMargins n ρ ε γ κ ξ)
    (hR2 : R ⊆ 𝓗.pow2)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (habs : AbsorbableBySmall 𝓗 N R U S ρ ε γ κ ξ ∨
      (AbsorbableByTypical 𝓗 N R U S ρ ε γ κ ξ ∧ ¬ IsDifficult U N))
    (hused : ∀ v : Fin n, (nbrs used v).ncard ≤ K)
    (hK : (K : ℝ) ≤ γ * (n : ℝ))
    (hwW : w ∈ W)
    (hWle : W ⊆ U \ matchVert N)
    (hYsub : U \ matchVert N ⊆ W ∪ {u})
    (hWlow : (n : ℝ) / 200 - 1 ≤ (W.ncard : ℝ))
    (hWup : (W.ncard : ℝ) ≤ (n : ℝ)) :
    3 * ρ * (W.ncard : ℝ) / 4
      ≤ (degIn (restr (R \ used) W) W w : ℝ) := by
  classical
  have hw : w ∈ U \ matchVert N := hWle hwW
  have hwU : w ∈ U := hw.1
  -- the neighbourhoods inside `Y` and inside `W` differ by at most the vertex `u`
  have hkey : (U \ matchVert N) ∩ nbrs (R \ used) w ⊆ (W ∩ nbrs (R \ used) w) ∪ {u} := by
    intro x hx
    obtain ⟨hxY, hxn⟩ := hx
    have hxu : x ∈ W ∪ ({u} : Set (Fin n)) := hYsub hxY
    rw [Set.mem_union] at hxu
    rcases hxu with hxW | hxu
    · exact Or.inl ⟨hxW, hxn⟩
    · exact Or.inr hxu
  have hdegWK : ((U \ matchVert N) ∩ nbrs (R \ used) w).ncard
      ≤ (W ∩ nbrs (R \ used) w).ncard + 1 := by
    have h1 := Set.ncard_le_ncard hkey (Set.toFinite _)
    have h2 := Set.ncard_union_le (W ∩ nbrs (R \ used) w) ({u} : Set (Fin n))
    have h3 : (({u} : Set (Fin n)).ncard : ℕ) = 1 := Set.ncard_singleton u
    have h4 : (((W ∩ nbrs (R \ used) w) ∪ ({u} : Set (Fin n))).ncard : ℕ)
        ≤ (W ∩ nbrs (R \ used) w).ncard + 1 := by
      rw [← h3]
      exact h2
    exact le_trans h1 h4
  have hYcard : ((W.ncard : ℝ)) ≤ (((U \ matchVert N).ncard : ℝ)) :=
    ncard_le_ncard_real hWle
  -- the lower bound on the `R`-degree inside `Y = U ∖ V(N)`
  have hcase : ρ * (((U \ matchVert N).ncard : ℝ) - ε * (n : ℝ)) - 12 * γ * (n : ℝ)
      ≤ (((U \ matchVert N) ∩ nbrs (R \ used) w).ncard : ℝ) := by
    have hG'deg : (1 - ε) * (n : ℝ) ≤ ((nbrs (incidentTwo 𝓗 U) w).ncard : ℝ) := by
      have h := hUdeg w hwU
      rwa [degAt] at h
    have hcomplG' : (((nbrs (incidentTwo 𝓗 U) w)ᶜ).ncard : ℝ) ≤ ε * (n : ℝ) := by
      rw [ncard_compl_cast (nbrs (incidentTwo 𝓗 U) w)]
      linarith
    rcases habs with ⟨⟨𝓥, hU𝓥, -, habsor⟩, -, hsmall⟩ | habsT
    · -- case (a): typicality at `U`, smallness of `N`
      have hGU : ((U : Set (Fin n)).ncard : ℝ) - ε * (n : ℝ)
          ≤ ((U ∩ nbrs (incidentTwo 𝓗 U) w).ncard : ℝ) := by
        have h := ncard_le_ncard_inter_add U (nbrs (incidentTwo 𝓗 U) w)
        linarith
      have hRlow : ρ * ((U ∩ nbrs (incidentTwo 𝓗 U) w).ncard : ℝ) - 10 * γ * (n : ℝ)
          ≤ ((U ∩ nbrs R w).ncard : ℝ) := by
        have h := (abs_le.mp ((habsor.2.1 U hU𝓥) w).1).1
        linarith
      have hstep : ρ * ((U : Set (Fin n)).ncard : ℝ) - ρ * ε * (n : ℝ) - 10 * γ * (n : ℝ)
          ≤ ((U ∩ nbrs R w).ncard : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hGU (le_of_lt hm.hρ)
        have h2 : ρ * (((U : Set (Fin n)).ncard : ℝ) - ε * (n : ℝ))
            = ρ * ((U : Set (Fin n)).ncard : ℝ) - ρ * ε * (n : ℝ) := by ring
        linarith [h, hRlow, h2]
      -- remove `V(N)` and the used edges
      have hsub1 : U ∩ nbrs R w ⊆ ((U \ matchVert N) ∩ nbrs R w) ∪ matchVert N := by
        intro x hx
        obtain ⟨hxU, hxn⟩ := hx
        by_cases hxN : x ∈ matchVert N
        · exact Or.inr hxN
        · exact Or.inl ⟨⟨hxU, hxN⟩, hxn⟩
      have h1 : ((U ∩ nbrs R w).ncard : ℝ)
          ≤ (((U \ matchVert N) ∩ nbrs R w).ncard : ℝ) + ((matchVert N).ncard : ℝ) := by
        have h2 := ncard_le_ncard_real hsub1
        have h3 := Set.ncard_union_le ((U \ matchVert N) ∩ nbrs R w) (matchVert N)
        have h4 : ((((U \ matchVert N) ∩ nbrs R w) ∪ matchVert N).ncard : ℝ)
            ≤ (((U \ matchVert N) ∩ nbrs R w).ncard : ℝ) + ((matchVert N).ncard : ℝ) := by
          exact_mod_cast h3
        linarith
      have h2 := ncard_inter_nbrs_sdiff_ge R used ((U \ matchVert N)) w (hused w)
      have h3 : (K : ℝ) ≤ γ * (n : ℝ) := hK
      have hYU : (((U \ matchVert N) : Set (Fin n)).ncard : ℝ) ≤ ((U : Set (Fin n)).ncard : ℝ) :=
        ncard_le_ncard_real Set.sdiff_subset
      have hYU' : ρ * (((U \ matchVert N) : Set (Fin n)).ncard : ℝ)
          ≤ ρ * ((U : Set (Fin n)).ncard : ℝ) :=
        mul_le_mul_of_nonneg_left hYU (le_of_lt hm.hρ)
      have hring : ρ * (((U \ matchVert N) : Set (Fin n)).ncard : ℝ) - ρ * ε * (n : ℝ)
            - 12 * γ * (n : ℝ)
          = ρ * ((((U \ matchVert N) : Set (Fin n)).ncard : ℝ) - ε * (n : ℝ))
            - 12 * γ * (n : ℝ) := by ring
      linarith [hstep, h1, h2, h3, hsmall, hYU', hring]
    · -- case (b): typicality at `U ∖ V(N)`
      obtain ⟨hAbT, hnd⟩ := habsT
      obtain ⟨𝓥, hU𝓥, -, hX𝓥, hY𝓥, habsor, hnotR, hVNU⟩ := hAbT
      have hGY : (((U \ matchVert N) : Set (Fin n)).ncard : ℝ) - ε * (n : ℝ)
          ≤ (((U \ matchVert N) ∩ nbrs (incidentTwo 𝓗 U) w).ncard : ℝ) := by
        have h := ncard_le_ncard_inter_add (U \ matchVert N) (nbrs (incidentTwo 𝓗 U) w)
        linarith
      have hRlow : ρ * (((U \ matchVert N) ∩ nbrs (incidentTwo 𝓗 U) w).ncard : ℝ)
          - 10 * γ * (n : ℝ) ≤ (((U \ matchVert N) ∩ nbrs R w).ncard : ℝ) := by
        have h := (abs_le.mp ((habsor.2.1 (U \ matchVert N) hY𝓥) w).1).1
        linarith
      have hstep : ρ * (((U \ matchVert N) : Set (Fin n)).ncard : ℝ) - ρ * ε * (n : ℝ)
          - 10 * γ * (n : ℝ) ≤ (((U \ matchVert N) ∩ nbrs R w).ncard : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hGY (le_of_lt hm.hρ)
        have h2 : ρ * ((((U \ matchVert N) : Set (Fin n)).ncard : ℝ) - ε * (n : ℝ))
            = ρ * (((U \ matchVert N) : Set (Fin n)).ncard : ℝ) - ρ * ε * (n : ℝ) := by ring
        linarith [h, hRlow, h2]
      have h2 := ncard_inter_nbrs_sdiff_ge R used ((U \ matchVert N)) w (hused w)
      have h3 : (K : ℝ) ≤ γ * (n : ℝ) := hK
      have hring : ρ * (((U \ matchVert N) : Set (Fin n)).ncard : ℝ) - ρ * ε * (n : ℝ)
            - 12 * γ * (n : ℝ)
          = ρ * ((((U \ matchVert N) : Set (Fin n)).ncard : ℝ) - ε * (n : ℝ))
            - 12 * γ * (n : ℝ) := by ring
      linarith [hstep, h2, h3, hring]
  -- the arithmetic
  have hρn : (20000 : ℝ) ≤ ρ * (n : ℝ) := by
    have h := rho_mul_n_ge (n := n) (ρ := ρ) (ε := ε) (γ := γ) (κ := κ) (ξ := ξ) hm
    linarith
  have harith := Commons.Combinatorics.EFLArith.internal_arith (n := n) (m := (W.ncard : ℝ))
    hm.hρ hm.hρ1 hm.hγ hm.hγε hm.hεsmall hWlow hWup hρn
  have hrestr : degIn (restr (R \ used) W) W w = (W ∩ nbrs (R \ used) w).ncard := by
    rw [degIn_restr hwW, degIn_eq_inter_nbrs]
  rw [hrestr]
  -- `|Y ∩ N| ≤ |W ∩ N| + 1` and `ρ(m - εn) ≥ ρ(|Y| - εn)`
  have hYge : ρ * (((W.ncard : ℝ)) - ε * (n : ℝ)) - 12 * γ * (n : ℝ)
      ≤ (((U \ matchVert N) ∩ nbrs (R \ used) w).ncard : ℝ) := by
    have h := mul_le_mul_of_nonneg_left
      (show ((W.ncard : ℝ)) - ε * (n : ℝ) ≤ (((U \ matchVert N).ncard : ℝ)) - ε * (n : ℝ)
        by linarith [hYcard]) (le_of_lt hm.hρ)
    linarith [hcase, h]
  have h1 : (((U \ matchVert N) ∩ nbrs (R \ used) w).ncard : ℝ)
      ≤ ((W ∩ nbrs (R \ used) w).ncard : ℝ) + 1 := by exact_mod_cast hdegWK
  have hb : ρ * ((W.ncard : ℝ) - ε * (n : ℝ)) - 13 * γ * (n : ℝ) - 1
      ≤ ρ * ((W.ncard : ℝ) - ε * (n : ℝ)) - 12 * γ * (n : ℝ) := by
    have hγn : (0 : ℝ) ≤ γ * (n : ℝ) :=
      mul_nonneg (le_of_lt hm.hγ) (Nat.cast_nonneg n)
    linarith
  linarith [harith, hYge, h1, hb]

/-! ## The internal matching and the internal step of Lemma 7.3 -/

/-- **The internal matching.**  If `|U ∖ V(N)| > n/100`, `W` has an even number
of vertices and `(U ∖ V(N)) ⊆ W ∪ {u}` with `W ⊆ U ∖ V(N)`, then the edges of
`R ∖ used` inside `W` contain a matching covering `W`. -/
theorem huge_internal_matching {𝓗 R used : Hypergraph (Fin n)} {U S : Set (Fin n)}
    {N : Set 𝓗} {K B : ℕ} {u : Fin n} {W : Set (Fin n)}
    (hm : HugeMargins n ρ ε γ κ ξ) (hmatch : InternalMatchingInput n B)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (habs : AbsorbableBySmall 𝓗 N R U S ρ ε γ κ ξ ∨
      (AbsorbableByTypical 𝓗 N R U S ρ ε γ κ ξ ∧ ¬ IsDifficult U N))
    (hused : ∀ v : Fin n, (nbrs used v).ncard ≤ K)
    (hK : (K : ℝ) ≤ γ * (n : ℝ))
    (hB : (B : ℝ) ≤ ρ ^ 2 * (γ * (n : ℝ)) / 400)
    (hRsub2 : R ⊆ 𝓗.pow2)
    (hUbig : (n : ℝ) / 100 < (((U \ matchVert N) : Set (Fin n)).ncard : ℝ))
    (hWeven : Even W.ncard)
    (hWle : W ⊆ U \ matchVert N)
    (hYsub : U \ matchVert N ⊆ W ∪ {u}) :
    ∃ M : Set 𝓗, IsMatching 𝓗 M ∧
      (∀ e ∈ M, (e : Set (Fin n)) ∈ R ∧ (e : Set (Fin n)) ∉ used) ∧
      (∀ e ∈ M, (e : Set (Fin n)) ⊆ W) ∧
      Disjoint (matchVert M) (matchVert N) ∧ Covers M W := by
  classical
  set Y : Set (Fin n) := U \ matchVert N with hYdef
  have hYU : Y ⊆ U := Set.sdiff_subset
  -- `|Y| ≤ |W| + 1` and hence the two lower bounds on `|W|`
  have hYcard : (Y.ncard : ℝ) ≤ (W.ncard : ℝ) + 1 := by
    have h1 : Y ⊆ W ∪ ({u} : Set (Fin n)) := hYsub
    have h2 := ncard_le_ncard_real h1
    have h3 : (W ∪ ({u} : Set (Fin n))).ncard ≤ W.ncard + 1 := by
      have h4 := Set.ncard_union_le W ({u} : Set (Fin n))
      rw [Set.ncard_singleton] at h4
      exact h4
    have h5 : ((W ∪ ({u} : Set (Fin n))).ncard : ℝ) ≤ (W.ncard : ℝ) + 1 := by
      exact_mod_cast h3
    linarith
  have hWlow : (n : ℝ) / 200 - 1 ≤ (W.ncard : ℝ) := by
    have h1 : (n : ℝ) / 200 - 1 ≤ (Y.ncard : ℝ) - 1 := by
      have h2 : (n : ℝ) / 200 + 1 ≤ (n : ℝ) / 100 := by
        have hn : (200 : ℝ) ≤ (n : ℝ) := by
          have hb := hm.hnbig
          have hρn : (2000000 : ℝ) ≤ ρ * (n : ℝ) :=
            rho_mul_n_ge (n := n) (ρ := ρ) (ε := ε) (γ := γ) (κ := κ) (ξ := ξ) hm
          have hρ1 : ρ ≤ 1 := hm.hρ1
          have hnn : (2000000 : ℝ) ≤ (n : ℝ) := by
            have := mul_le_mul_of_nonneg_right hρ1 (Nat.cast_nonneg n)
            linarith
          linarith
        linarith
      linarith [hUbig]
    linarith [hYcard]
  have hWup : (W.ncard : ℝ) ≤ (n : ℝ) := by
    have h := ncard_le_ncard_real (Set.subset_univ W) (B := Set.univ)
    simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using h
  have hnbig2000 : (400 : ℝ) ≤ (n : ℝ) := by
    have hρn : (2000000 : ℝ) ≤ ρ * (n : ℝ) :=
      rho_mul_n_ge (n := n) (ρ := ρ) (ε := ε) (γ := γ) (κ := κ) (ξ := ξ) hm
    have := mul_le_mul_of_nonneg_right hm.hρ1 (Nat.cast_nonneg n)
    linarith
  have hWlow2 : γ * (n : ℝ) / 400 ≤ (W.ncard : ℝ) := by
    have hγ1 : γ ≤ 1 / 1000 := gamma_le_thousandth (n := n) (ρ := ρ) (ε := ε) (γ := γ)
      (κ := κ) (ξ := ξ) hm
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h1 : γ * (n : ℝ) / 400 ≤ (n : ℝ) / 400000 := by nlinarith [hγ1, hn0]
    have h3 : (n : ℝ) / 200 - 1 ≥ (n : ℝ) / 400 := by linarith [hnbig2000]
    have h2 : (n : ℝ) / 400 ≤ (W.ncard : ℝ) := by linarith [hWlow, h3]
    linarith
  have hdeg : ∀ w ∈ W, 3 * ρ * (W.ncard : ℝ) / 4
      ≤ (degIn (restr (R \ used) W) W w : ℝ) := by
    intro w hw
    exact huge_internal_degree (W := W) (u := u) (N := N) (K := K) hm hRsub2 hUdeg habs
      hused hK hw (by rw [← hYdef]; exact hWle) (by rw [← hYdef]; exact hYsub) hWlow hWup
  -- the upper regularity of `restr (R \ used) W`
  have hξ0 : (0 : ℝ) ≤ 400 * ξ / γ :=
    div_nonneg (mul_nonneg (by norm_num) (le_of_lt hm.hξ)) (le_of_lt hm.hγ)
  have hξρ : 10 * (400 * ξ / γ) ≤ ρ := by
    have h2 : 10 * (400 * ξ / γ) = 4000 * ξ / γ := by ring
    rw [h2, div_le_iff₀ hm.hγ]
    have h3 : 4000 * ξ ≤ ρ * γ := by rw [mul_comm ρ γ]; exact hm.hξγρ
    exact h3
  have hB' : (B : ℝ) ≤ ρ ^ 2 * (W.ncard : ℝ) := by
    have h2 : ρ ^ 2 * (γ * (n : ℝ)) / 400 ≤ ρ ^ 2 * (W.ncard : ℝ) := by
      have h3 : (0 : ℝ) ≤ ρ ^ 2 := sq_nonneg ρ
      nlinarith [hWlow2, h3]
    linarith [hB, h2]
  have hup : UpperRegular (incidentTwo 𝓗 U) R ρ ξ := by
    rcases habs with ⟨⟨𝓥, -, -, habsor⟩, -, -⟩ | ⟨⟨𝓥, -, -, -, -, habsor, -, -⟩, -⟩
    · exact habsor.2.2
    · exact habsor.2.2
  have hRsub : R ⊆ incidentTwo 𝓗 U := by
    rcases habs with ⟨⟨𝓥, -, -, habsor⟩, -, -⟩ | ⟨⟨𝓥, -, -, -, -, habsor, -, -⟩, -⟩
    · exact habsor.1
    · exact habsor.1
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
      exact mul_le_mul_of_nonneg_left hWlow2 hξ0
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
      have hγ400 : γ ≤ 400 := by
        linarith [gamma_le_thousandth (n := n) (ρ := ρ) (ε := ε) (γ := γ) (κ := κ)
          (ξ := ξ) hm]
      nlinarith [hm.hξ, hγ400]
    have hγ1 : γ ≤ 1 := by
      linarith [gamma_le_thousandth (n := n) (ρ := ρ) (ε := ε) (γ := γ) (κ := κ) (ξ := ξ) hm]
    nlinarith [hmono, hmain, hcard, le_of_lt hm.hρ, hξξ']
  have hsub : ∀ e ∈ restr (R \ used) W, e ⊆ W := fun e he => he.2
  have h2' : ∀ e ∈ restr (R \ used) W, edgeSize e = 2 :=
    fun e he => (mem_pow2.mp (hRsub2 he.1.1)).2
  have hRsub' : restr (R \ used) W ⊆ 𝓗 := fun e he => (mem_pow2.mp (hRsub2 he.1.1)).1
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
    rw [mem_matchVert]
    exact hMcov w hw

end

end ErdosFaberLovaszConjecture
