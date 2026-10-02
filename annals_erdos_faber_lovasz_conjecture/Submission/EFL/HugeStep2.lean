import Submission.EFL.HugeStep

/-!
# §7.3, part 2: the partner choice, the internal steps and the iterations

This module completes the proof of the paper's Lemma `huge-edge-absorption-lemma`
(Lemma 7.3).  `HugeStep.lean` proved the crossing part, the internal degree
bound and the internal matching; here we add

* the numeric margins used by the partner choice (`pair_arith_a`, `pair_arith_b`)
  and the fact `εn ≥ 2·10⁶` implied by the margin hierarchy;
* the *partner choice* `huge_pair` (a vertex `v ∉ U ∪ V(N)` with
  `{u,v} ∈ R ∖ used`);
* the *internal step* in the case `|U| ≤ (1-10ε)n` (`huge_internal_step_small`),
  which covers all of `U ∖ V(N)`;
* the *defect choice* `huge_pick_S` and the internal step in the case
  `|U| > (1-10ε)n` (`huge_internal_step_large`);
* the two uniform one-step lemmas (`huge_step_cov`, `huge_step_defect`);
* the two iterations (`huge_iter_cov`, `huge_iter_defect`);
* the assembly `huge_edge_absorption`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}
variable {ρ ε γ κ ξ : ℝ}

/-! ## Numeric margins -/

/-- From the margin hierarchy, `εn ≥ 2·10⁶` (in particular `εn ≥ 2`). -/
theorem eps_mul_n_ge_big (hm : HugeMargins n ρ ε γ κ ξ) :
    (2000000 : ℝ) ≤ ε * (n : ℝ) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : 1000 * γ * (ρ * (n : ℝ)) ≤ ρ ^ 2 * ε * (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hm.hγε (mul_nonneg (le_of_lt hm.hρ) hn0)
    nlinarith [h]
  have h2 : (2000000 : ℝ) ≤ 1000 * γ * (ρ * (n : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left hm.hnbig (by norm_num : (0 : ℝ) ≤ 1000)
    nlinarith [h]
  have h3 : ρ ^ 2 * ε * (n : ℝ) ≤ ε * (n : ℝ) := by
    have hρ2 : ρ ^ 2 ≤ ρ := by nlinarith [hm.hρ, hm.hρ1]
    have h4 : ρ ^ 2 * ε ≤ ρ * ε := mul_le_mul_of_nonneg_right hρ2 (le_of_lt hm.hε)
    have h5 : ρ ^ 2 * ε * (n : ℝ) ≤ ρ * ε * (n : ℝ) :=
      mul_le_mul_of_nonneg_right h4 hn0
    have h6 : ρ * ε * (n : ℝ) ≤ ε * (n : ℝ) := by
      have h7 : ρ * ε ≤ ε := by nlinarith [hm.hρ, hm.hρ1, hm.hε]
      exact mul_le_mul_of_nonneg_right h7 hn0
    linarith
  linarith

/-- `γ ≤ ε` (from `1000γ ≤ ρε ≤ ε`). -/
theorem gamma_le_eps (hm : HugeMargins n ρ ε γ κ ξ) : γ ≤ ε := by
  nlinarith [hm.hγε, hm.hρ, hm.hρ1, hm.hε]

/-- `ρ * (3/2·εn) - 11·γn > 0`. -/
theorem pair_arith_b (hm : HugeMargins n ρ ε γ κ ξ) (hn : 1 ≤ n) :
    0 < ρ * (3 / 2 * ε * (n : ℝ)) - 11 * γ * (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hγe : 11 * γ ≤ ρ * ε * (11 / 1000) := by nlinarith [hm.hγε]
  have h1 : 11 * γ * (n : ℝ) ≤ ρ * ε * (11 / 1000) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hγe (le_of_lt hn0)
  have hpos : 0 < ρ * ε * (n : ℝ) := mul_pos (mul_pos hm.hρ hm.hε) hn0
  have hc : (0 : ℝ) < 3 / 2 - 11 / 1000 := by norm_num
  have h2 := mul_pos hc hpos
  nlinarith [h1, hpos, h2]

/-- `ρ * (8·εn) - 12·γn > 0`. -/
theorem pair_arith_a (hm : HugeMargins n ρ ε γ κ ξ) (hn : 1 ≤ n) :
    0 < ρ * (8 * ε * (n : ℝ)) - 12 * γ * (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hγe : 12 * γ ≤ ρ * ε * (12 / 1000) := by nlinarith [hm.hγε]
  have h1 : 12 * γ * (n : ℝ) ≤ ρ * ε * (12 / 1000) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hγe (le_of_lt hn0)
  have hpos : 0 < ρ * ε * (n : ℝ) := mul_pos (mul_pos hm.hρ hm.hε) hn0
  have hc : (0 : ℝ) < 8 - 12 / 1000 := by norm_num
  have h2 := mul_pos hc hpos
  nlinarith [h1, hpos, h2]

/-! ## The partner choice -/

/-- **The partner choice of Lemma 7.3.**  If `|U| ≤ (1-10ε)n` and `u ∈ U ∖ V(N)`
then there is `v ∉ U ∪ V(N)` with `{u,v} ∈ R ∖ used`. -/
theorem huge_pair {𝓗 R used : Hypergraph (Fin n)} {U S : Set (Fin n)} {N : Set 𝓗}
    {K : ℕ} {u : Fin n}
    (hm : HugeMargins n ρ ε γ κ ξ)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (habs : AbsorbableBySmall 𝓗 N R U S ρ ε γ κ ξ ∨
      (AbsorbableByTypical 𝓗 N R U S ρ ε γ κ ξ ∧ ¬ IsDifficult U N))
    (hn : 4 ≤ n)
    (hused : ∀ v : Fin n, (nbrs used v).ncard ≤ K)
    (hK : (K : ℝ) ≤ γ * (n : ℝ))
    (hUle : ((U : Set (Fin n)).ncard : ℝ) ≤ (1 - 10 * ε) * (n : ℝ))
    (huU : u ∈ U) (huN : u ∉ matchVert N) :
    ∃ v : Fin n, v ∉ U ∪ matchVert N ∧ ({u, v} : Set (Fin n)) ∈ R ∧
      ({u, v} : Set (Fin n)) ∉ used := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hρ0 : (0 : ℝ) ≤ ρ := le_of_lt hm.hρ
  set X : Set (Fin n) := U ∪ matchVert N with hXdef
  have hXeq : (Xᶜ : Set (Fin n)) = Uᶜ \ matchVert N := by
    rw [hXdef]
    ext x
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_sdiff, not_or]
  -- `Uᶜ` is large
  have hUc : 10 * ε * (n : ℝ) ≤ ((Uᶜ).ncard : ℝ) := by
    rw [ncard_compl_cast U]
    linarith
  -- the `G'`-degree of `u`
  have hG'deg : (1 - ε) * (n : ℝ) ≤ ((nbrs (incidentTwo 𝓗 U) u).ncard : ℝ) := by
    have h := hUdeg u huU
    rwa [degAt] at h
  have hcomplG' : (((nbrs (incidentTwo 𝓗 U) u)ᶜ).ncard : ℝ) ≤ ε * (n : ℝ) := by
    rw [ncard_compl_cast (nbrs (incidentTwo 𝓗 U) u)]
    linarith
  have hG'U : ((Uᶜ).ncard : ℝ) - ε * (n : ℝ)
      ≤ ((Uᶜ ∩ nbrs (incidentTwo 𝓗 U) u).ncard : ℝ) := by
    have h := ncard_le_ncard_inter_add (Uᶜ) (nbrs (incidentTwo 𝓗 U) u)
    linarith
  have hG'X : ((Xᶜ).ncard : ℝ) - ε * (n : ℝ)
      ≤ ((Xᶜ ∩ nbrs (incidentTwo 𝓗 U) u).ncard : ℝ) := by
    have h := ncard_le_ncard_inter_add (Xᶜ) (nbrs (incidentTwo 𝓗 U) u)
    linarith
  have hmain : 0 < ((Xᶜ ∩ nbrs (R \ used) u).ncard : ℝ) := by
    rcases habs with ⟨⟨𝓥, hU𝓥, -, habsor⟩, -, hsmall⟩ | ⟨hAbT, hnd⟩
    · -- case (a): absorbable by smallness
      have hVN : ((matchVert N).ncard : ℝ) ≤ γ * (n : ℝ) := hsmall
      have hγn : γ * (n : ℝ) ≤ ε * (n : ℝ) :=
        mul_le_mul_of_nonneg_right (gamma_le_eps hm) hn0
      have hXc : 9 * ε * (n : ℝ) ≤ ((Xᶜ).ncard : ℝ) := by
        rw [hXeq]
        have h1 := ncard_sdiff_ge (Uᶜ) (matchVert N)
        linarith
      -- typicality at `U`
      have hUt : ρ * ((Uᶜ).ncard : ℝ) - ρ * ε * (n : ℝ) - 10 * γ * (n : ℝ)
          ≤ ((Uᶜ ∩ nbrs R u).ncard : ℝ) := by
        have h := (abs_le.mp ((habsor.2.1 U hU𝓥 u).2)).1
        have h2 := mul_le_mul_of_nonneg_left hG'U hρ0
        have h3 : ρ * (((Uᶜ).ncard : ℝ) - ε * (n : ℝ))
            = ρ * ((Uᶜ).ncard : ℝ) - ρ * ε * (n : ℝ) := by ring
        linarith [h, h2, h3]
      -- pass from `Uᶜ` to `Xᶜ`
      have hXR : ((Uᶜ ∩ nbrs R u).ncard : ℝ) - ((matchVert N).ncard : ℝ)
          ≤ ((Xᶜ ∩ nbrs R u).ncard : ℝ) := by
        have hset : (Uᶜ ∩ nbrs R u) \ matchVert N = Xᶜ ∩ nbrs R u := by
          rw [hXeq]
          ext x
          simp only [Set.mem_sdiff, Set.mem_inter_iff]
          tauto
        rw [← hset]
        exact ncard_sdiff_ge _ _
      have hsub := ncard_inter_nbrs_sdiff_ge R used (Xᶜ) u (hused u)
      have hρn : (0 : ℝ) ≤ ρ * ε * (n : ℝ) :=
        mul_nonneg (mul_nonneg hρ0 (le_of_lt hm.hε)) hn0
      have hmm : ρ * (8 * ε * (n : ℝ)) - 12 * γ * (n : ℝ)
          ≤ ((Xᶜ ∩ nbrs (R \ used) u).ncard : ℝ) := by
        have hρUc : ρ * (10 * ε * (n : ℝ)) ≤ ρ * ((Uᶜ).ncard : ℝ) :=
          mul_le_mul_of_nonneg_left hUc hρ0
        linarith [hUt, hXR, hsub, hK, hVN, hρUc, hρn]
      linarith [hmm, pair_arith_a hm hn1]
    · -- case (b): absorbable by typicality and not difficult
      obtain ⟨𝓥, hU𝓥, -, hX𝓥, -, habsor, -, -⟩ := hAbT
      -- `|Uᶜ| ≥ 2`
      have hUc2 : 2 ≤ (Uᶜ).ncard := by
        have hbig := eps_mul_n_ge_big (n := n) (ρ := ρ) (ε := ε) (γ := γ) (κ := κ)
          (ξ := ξ) hm
        have h2 : (2 : ℝ) ≤ 10 * ε * (n : ℝ) := by linarith
        have h3 : (2 : ℝ) ≤ ((Uᶜ).ncard : ℝ) := le_trans h2 hUc
        exact_mod_cast h3
      -- `N` is not difficult and `|Uᶜ| ≥ 2`
      have hnd' : 4 * (matchVert N ∩ Uᶜ).ncard < 3 * (Uᶜ).ncard := by
        rw [IsDifficult, not_and_or] at hnd
        rcases hnd with h | h
        · exact absurd hUc2 (by omega)
        · exact not_le.mp h
      -- `|Xᶜ| ≥ 5/2 ε n`
      have hXc : 5 * ε * (n : ℝ) / 2 ≤ ((Xᶜ).ncard : ℝ) := by
        rw [hXeq]
        have h1 : ((Uᶜ).ncard : ℝ) - (((matchVert N) ∩ Uᶜ).ncard : ℝ)
            ≤ ((Uᶜ \ matchVert N).ncard : ℝ) := by
          have h := ncard_sdiff_ge (Uᶜ) ((matchVert N) ∩ Uᶜ)
          have hset : (Uᶜ \ ((matchVert N) ∩ Uᶜ)) = Uᶜ \ matchVert N := by
            ext x
            simp only [Set.mem_sdiff, Set.mem_inter_iff]
            tauto
          rwa [hset] at h
        have h2 : 4 * (((matchVert N) ∩ Uᶜ).ncard : ℝ) < 3 * ((Uᶜ).ncard : ℝ) := by
          exact_mod_cast hnd'
        linarith
      -- typicality at `U ∪ V(N)`
      have hXt : ρ * ((Xᶜ).ncard : ℝ) - ρ * ε * (n : ℝ) - 10 * γ * (n : ℝ)
          ≤ ((Xᶜ ∩ nbrs R u).ncard : ℝ) := by
        have h := (abs_le.mp ((habsor.2.1 X hX𝓥 u).2)).1
        have h2 := mul_le_mul_of_nonneg_left hG'X hρ0
        have h3 : ρ * (((Xᶜ).ncard : ℝ) - ε * (n : ℝ))
            = ρ * ((Xᶜ).ncard : ℝ) - ρ * ε * (n : ℝ) := by ring
        linarith [h, h2, h3]
      have hsub := ncard_inter_nbrs_sdiff_ge R used (Xᶜ) u (hused u)
      have hρn : (0 : ℝ) ≤ ρ * ε * (n : ℝ) :=
        mul_nonneg (mul_nonneg hρ0 (le_of_lt hm.hε)) hn0
      have hmm : ρ * (3 / 2 * ε * (n : ℝ)) - 11 * γ * (n : ℝ)
          ≤ ((Xᶜ ∩ nbrs (R \ used) u).ncard : ℝ) := by
        have hρXc : ρ * (5 * ε * (n : ℝ) / 2) ≤ ρ * ((Xᶜ).ncard : ℝ) :=
          mul_le_mul_of_nonneg_left hXc hρ0
        linarith [hXt, hsub, hK, hρXc]
      linarith [hmm, pair_arith_b hm hn1]
  have hpos : 0 < (Xᶜ ∩ nbrs (R \ used) u).ncard := by exact_mod_cast hmain
  obtain ⟨v, hv⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
  obtain ⟨hvX, hvnbrs⟩ := hv
  rw [Set.mem_compl_iff, hXdef] at hvX
  rw [mem_nbrs, Set.mem_sdiff] at hvnbrs
  exact ⟨v, hvX, hvnbrs.1, hvnbrs.2⟩


/-! ## The internal step in the case `|U| ≤ (1-10ε)n` -/

/-- **The internal step of Lemma 7.3 in the case `|U| ≤ (1-10ε)n`.**  If
`|U ∖ V(N)| > n/100` there is a matching of available `R`-edges, disjoint from
`V(N)`, covering all of `U ∖ V(N)`. -/
theorem huge_internal_step_small {𝓗 R used : Hypergraph (Fin n)} {U S : Set (Fin n)}
    {N : Set 𝓗} {K B : ℕ}
    (hm : HugeMargins n ρ ε γ κ ξ) (hmatch : InternalMatchingInput n B)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (habs : AbsorbableBySmall 𝓗 N R U S ρ ε γ κ ξ ∨
      (AbsorbableByTypical 𝓗 N R U S ρ ε γ κ ξ ∧ ¬ IsDifficult U N))
    (hn : 4 ≤ n)
    (hused : ∀ v : Fin n, (nbrs used v).ncard ≤ K)
    (hK : (K : ℝ) ≤ γ * (n : ℝ))
    (hB : (B : ℝ) ≤ ρ ^ 2 * (γ * (n : ℝ)) / 400)
    (hRsub2 : R ⊆ 𝓗.pow2)
    (hUle : ((U : Set (Fin n)).ncard : ℝ) ≤ (1 - 10 * ε) * (n : ℝ))
    (hUbig : (n : ℝ) / 100 < (((U \ matchVert N) : Set (Fin n)).ncard : ℝ)) :
    ∃ Nabs : Set 𝓗, IsMatching 𝓗 Nabs ∧
      (∀ e ∈ Nabs, (e : Set (Fin n)) ∈ R ∧ (e : Set (Fin n)) ∉ used) ∧
      Disjoint (matchVert Nabs) (matchVert N) ∧ Covers Nabs (U \ matchVert N) := by
  classical
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hYpos : 0 < ((U \ matchVert N) : Set (Fin n)).ncard := by
    have h : (0 : ℝ) < (((U \ matchVert N) : Set (Fin n)).ncard : ℝ) := by linarith
    exact_mod_cast h
  obtain ⟨u, huA⟩ := (Set.ncard_pos (Set.toFinite _)).mp hYpos
  have huU : u ∈ U := huA.1
  have huN : u ∉ matchVert N := huA.2
  by_cases hpar : Even ((U \ matchVert N) : Set (Fin n)).ncard
  · obtain ⟨M, hMm, hMR, -, hMdisj, hMcov⟩ :=
      huge_internal_matching (W := U \ matchVert N) (u := u) (N := N) (K := K)
        hm hmatch hUdeg habs hused hK hB hRsub2 hUbig hpar
        (fun _ hx => hx) (fun _ hx => Or.inl hx)
    exact ⟨M, hMm, hMR, hMdisj, hMcov⟩
  · have hstep : (((U \ matchVert N) \ {u}) : Set (Fin n)).ncard + 1
        = ((U \ matchVert N) : Set (Fin n)).ncard := by
      rw [Set.ncard_sdiff_singleton_of_mem huA]
      exact Nat.succ_pred_eq_of_pos hYpos
    have hWeven : Even (((U \ matchVert N) \ {u}) : Set (Fin n)).ncard := by
      rw [← hstep] at hpar
      rcases Nat.even_or_odd (((U \ matchVert N) \ {u}) : Set (Fin n)).ncard with he | ho
      · exact he
      · obtain ⟨m, hm'⟩ := ho
        exact absurd ⟨m + 1, by omega⟩ hpar
    obtain ⟨M, hMm, hMR, hMW, hMdisj, hMcov⟩ :=
      huge_internal_matching (W := (U \ matchVert N) \ {u}) (u := u) (N := N) (K := K)
        hm hmatch hUdeg habs hused hK hB hRsub2 hUbig hWeven
        (fun _ hx => hx.1) (fun x hx => by
          by_cases hxu : x = u
          · exact Or.inr (by rw [hxu]; simp)
          · exact Or.inl ⟨hx, hxu⟩)
    obtain ⟨v, hv1, hv2, hv3⟩ :=
      huge_pair (N := N) (K := K) (u := u) hm hUdeg habs hn hused hK hUle huU huN
    have hmem : ({u, v} : Set (Fin n)) ∈ 𝓗 := (mem_pow2.mp (hRsub2 hv2)).1
    set e0 : 𝓗 := ⟨({u, v} : Set (Fin n)), hmem⟩ with he0def
    have hsing : IsMatching 𝓗 ({e0} : Set 𝓗) := isMatching_singleton 𝓗 e0
    have hdis : Disjoint (matchVert M) (matchVert ({e0} : Set 𝓗)) := by
      rw [Set.disjoint_left]
      intro x hx hxe
      rw [mem_matchVert] at hx hxe
      obtain ⟨e, he, hxe'⟩ := hx
      obtain ⟨e', he', hxe''⟩ := hxe
      rw [Set.mem_singleton_iff] at he'
      subst he'
      have hxW := hMW e he hxe'
      rw [he0def] at hxe''
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxe''
      rcases hxe'' with h | h
      · exact hxW.2 h
      · subst h
        exact hv1 (Or.inl hxW.1.1)
    refine ⟨M ∪ {e0}, isMatching_union hMm hsing hdis, ?_, ?_, ?_⟩
    · intro e he
      rw [Set.mem_union, Set.mem_singleton_iff] at he
      rcases he with he | rfl
      · exact hMR e he
      · rw [he0def]
        exact ⟨hv2, hv3⟩
    · rw [Set.disjoint_left]
      intro x hx hxN
      rw [matchVert_union, Set.mem_union] at hx
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
        · subst h
          exact hv1 (Or.inr hxN)
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
        exact hMcov ⟨hx, hxu⟩

/-! ## The defect choice -/

/-- **The choice of the defect vertex in the case `|U| > (1-10ε)n`.**  There is
a vertex `u ∈ (S ∖ V(N)) ∖ P`. -/
theorem huge_pick_S {𝓗 R : Hypergraph (Fin n)} {U S : Set (Fin n)} {N : Set 𝓗}
    {P : Finset (Fin n)}
    (hm : HugeMargins n ρ ε γ κ ξ)
    (habs : AbsorbableBySmall 𝓗 N R U S ρ ε γ κ ξ ∨
      (AbsorbableByTypical 𝓗 N R U S ρ ε γ κ ξ ∧ ¬ IsDifficult U N))
    (hSsub : S ⊆ U)
    (hS : (γ + ε) * (n : ℝ) < (S.ncard : ℝ))
    (hP : (P.card : ℝ) ≤ γ * (n : ℝ)) :
    ∃ u : Fin n, u ∈ S ∧ u ∉ matchVert N ∧ u ∉ P := by
  classical
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  -- `|V(N) ∩ U| ≤ εn`
  have hVNU : (((matchVert N) ∩ U).ncard : ℝ) ≤ ε * (n : ℝ) := by
    rcases habs with ⟨⟨𝓥, -, -, habsor⟩, -, hsmall⟩ | ⟨hAbT, -⟩
    · have hγn : γ * (n : ℝ) ≤ ε * (n : ℝ) :=
        mul_le_mul_of_nonneg_right (gamma_le_eps hm) hn0
      have h1 : ((matchVert N).ncard : ℝ) ≤ γ * (n : ℝ) := hsmall
      have h2 : (((matchVert N) ∩ U).ncard : ℝ) ≤ ((matchVert N).ncard : ℝ) :=
        ncard_le_ncard_real Set.inter_subset_left
      linarith
    · obtain ⟨𝓥, -, -, -, -, -, -, hcard⟩ := hAbT
      exact hcard
  -- `|S ∖ V(N)| > γn`
  have hSge : γ * (n : ℝ) < (((S \ matchVert N) : Set (Fin n)).ncard : ℝ) := by
    have h1 : ((S ∩ matchVert N).ncard : ℝ) ≤ (((matchVert N) ∩ U).ncard : ℝ) := by
      apply ncard_le_ncard_real
      intro x hx
      exact ⟨hx.2, hSsub hx.1⟩
    have hset : (S \ matchVert N : Set (Fin n)) = S \ (S ∩ matchVert N) := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_inter_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun h => h2 h.2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun h => h2 ⟨h1, h⟩⟩
    have h2 := ncard_sdiff_ge S (S ∩ matchVert N)
    rw [← hset] at h2
    linarith
  have h1 : ((((S \ matchVert N) \ (P : Set (Fin n))) : Set (Fin n)).ncard : ℝ)
      ≥ (((S \ matchVert N) : Set (Fin n)).ncard : ℝ) - (P.card : ℝ) := by
    have h := ncard_sdiff_ge (S \ matchVert N) (P : Set (Fin n))
    simpa using h
  have hpos : (0 : ℝ) < ((((S \ matchVert N) \ (P : Set (Fin n))) : Set (Fin n)).ncard : ℝ) := by
    linarith
  have hpos' : 0 < ((((S \ matchVert N) \ (P : Set (Fin n))) : Set (Fin n)).ncard) := by
    exact_mod_cast hpos
  obtain ⟨u, hu⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos'
  rw [Set.mem_sdiff, Set.mem_sdiff] at hu
  exact ⟨u, hu.1.1, hu.1.2, hu.2⟩

/-! ## The internal step in the case `|U| > (1-10ε)n` -/

/-- **The internal step of Lemma 7.3 in the case `|U| > (1-10ε)n`.**  If
`|U ∖ V(N)| > n/100` there is a new defect vertex `u ∈ (S ∖ V(N)) ∖ P` and a
matching of available `R`-edges covering `(U ∖ V(N)) ∖ {u}`. -/
theorem huge_internal_step_large {𝓗 R used : Hypergraph (Fin n)} {U S : Set (Fin n)}
    {N : Set 𝓗} {P : Finset (Fin n)} {K B : ℕ}
    (hm : HugeMargins n ρ ε γ κ ξ) (hmatch : InternalMatchingInput n B)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (habs : AbsorbableBySmall 𝓗 N R U S ρ ε γ κ ξ ∨
      (AbsorbableByTypical 𝓗 N R U S ρ ε γ κ ξ ∧ ¬ IsDifficult U N))
    (hn : 4 ≤ n)
    (hused : ∀ v : Fin n, (nbrs used v).ncard ≤ K)
    (hK : (K : ℝ) ≤ γ * (n : ℝ))
    (hB : (B : ℝ) ≤ ρ ^ 2 * (γ * (n : ℝ)) / 400)
    (hRsub2 : R ⊆ 𝓗.pow2)
    (hSsub : S ⊆ U) (hS : (γ + ε) * (n : ℝ) < (S.ncard : ℝ))
    (hP : (P.card : ℝ) ≤ γ * (n : ℝ))
    (hUbig : (n : ℝ) / 100 < (((U \ matchVert N) : Set (Fin n)).ncard : ℝ)) :
    ∃ u : Fin n, u ∈ S ∧ u ∉ matchVert N ∧ u ∉ P ∧
      ∃ Nabs : Set 𝓗, IsMatching 𝓗 Nabs ∧
        (∀ e ∈ Nabs, (e : Set (Fin n)) ∈ R ∧ (e : Set (Fin n)) ∉ used) ∧
        Disjoint (matchVert Nabs) (matchVert N) ∧
        Covers Nabs ((U \ matchVert N) \ {u}) := by
  classical
  obtain ⟨u, huS, huN, huP⟩ := huge_pick_S (N := N) (P := P) hm habs hSsub hS hP
  have huU : u ∈ U := hSsub huS
  have huA : u ∈ U \ matchVert N := ⟨huU, huN⟩
  by_cases hpar : Even ((U \ matchVert N) : Set (Fin n)).ncard
  · obtain ⟨M, hMm, hMR, -, hMdisj, hMcov⟩ :=
      huge_internal_matching (W := U \ matchVert N) (u := u) (N := N) (K := K)
        hm hmatch hUdeg habs hused hK hB hRsub2 hUbig hpar
        (fun _ hx => hx) (fun _ hx => Or.inl hx)
    exact ⟨u, huS, huN, huP, M, hMm, hMR, hMdisj,
      Covers.mono (subset_refl M) Set.sdiff_subset hMcov⟩
  · have hstep : (((U \ matchVert N) \ {u}) : Set (Fin n)).ncard + 1
        = ((U \ matchVert N) : Set (Fin n)).ncard := by
      have hYpos : 0 < ((U \ matchVert N) : Set (Fin n)).ncard :=
        (Set.ncard_pos (Set.toFinite _)).mpr ⟨u, huA⟩
      rw [Set.ncard_sdiff_singleton_of_mem huA]
      exact Nat.succ_pred_eq_of_pos hYpos
    have hWeven : Even (((U \ matchVert N) \ {u}) : Set (Fin n)).ncard := by
      rw [← hstep] at hpar
      rcases Nat.even_or_odd (((U \ matchVert N) \ {u}) : Set (Fin n)).ncard with he | ho
      · exact he
      · obtain ⟨m, hm'⟩ := ho
        exact absurd ⟨m + 1, by omega⟩ hpar
    obtain ⟨M, hMm, hMR, -, hMdisj, hMcov⟩ :=
      huge_internal_matching (W := (U \ matchVert N) \ {u}) (u := u) (N := N) (K := K)
        hm hmatch hUdeg habs hused hK hB hRsub2 hUbig hWeven
        (fun _ hx => hx.1) (fun x hx => by
          by_cases hxu : x = u
          · exact Or.inr (by rw [hxu]; simp)
          · exact Or.inl ⟨hx, hxu⟩)
    exact ⟨u, huS, huN, huP, M, hMm, hMR, hMdisj, hMcov⟩

/-! ## The uniform one-step lemmas -/

/-- **The perfect-coverage one-step lemma.** -/
theorem huge_step_cov {𝓗 R used : Hypergraph (Fin n)} {U S : Set (Fin n)} {N : Set 𝓗}
    {K B : ℕ}
    (hm : HugeMargins n ρ ε γ κ ξ) (hmatch : InternalMatchingInput n B)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (hn : 4 ≤ n)
    (hused : ∀ v : Fin n, (nbrs used v).ncard ≤ K)
    (hK : (K : ℝ) ≤ γ * (n : ℝ))
    (hB : (B : ℝ) ≤ ρ ^ 2 * (γ * (n : ℝ)) / 400)
    (hRsub2 : R ⊆ 𝓗.pow2)
    (hUle : ((U : Set (Fin n)).ncard : ℝ) ≤ (1 - 10 * ε) * (n : ℝ))
    (habs : AbsorbableBySmall 𝓗 N R U S ρ ε γ κ ξ ∨
      (AbsorbableByTypical 𝓗 N R U S ρ ε γ κ ξ ∧ ¬ IsDifficult U N)) :
    ∃ Nabs : Set 𝓗, IsMatching 𝓗 Nabs ∧
      (∀ e ∈ Nabs, (e : Set (Fin n)) ∈ R ∧ (e : Set (Fin n)) ∉ used) ∧
      Disjoint (matchVert Nabs) (matchVert N) ∧ Covers Nabs (U \ matchVert N) := by
  by_cases hY : (((U \ matchVert N) : Set (Fin n)).ncard : ℝ) ≤ (n : ℝ) / 100
  · exact huge_cross_step (R' := R \ used) rfl hm hmatch hUdeg habs hn hused hK hY
  · exact huge_internal_step_small (N := N) (K := K) hm hmatch hUdeg habs hn hused hK
      hB hRsub2 hUle (not_le.mp hY)

/-- **The defect one-step lemma.** -/
theorem huge_step_defect {𝓗 R used : Hypergraph (Fin n)} {U S : Set (Fin n)}
    {N : Set 𝓗} {P : Finset (Fin n)} {K B : ℕ}
    (hm : HugeMargins n ρ ε γ κ ξ) (hmatch : InternalMatchingInput n B)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (hn : 4 ≤ n)
    (hused : ∀ v : Fin n, (nbrs used v).ncard ≤ K)
    (hK : (K : ℝ) ≤ γ * (n : ℝ))
    (hB : (B : ℝ) ≤ ρ ^ 2 * (γ * (n : ℝ)) / 400)
    (hRsub2 : R ⊆ 𝓗.pow2)
    (hSsub : S ⊆ U) (hS : (γ + ε) * (n : ℝ) < (S.ncard : ℝ))
    (hP : (P.card : ℝ) ≤ γ * (n : ℝ))
    (habs : AbsorbableBySmall 𝓗 N R U S ρ ε γ κ ξ ∨
      (AbsorbableByTypical 𝓗 N R U S ρ ε γ κ ξ ∧ ¬ IsDifficult U N)) :
    ∃ u : Fin n, u ∈ S ∧ u ∉ matchVert N ∧ u ∉ P ∧
      ∃ Nabs : Set 𝓗, IsMatching 𝓗 Nabs ∧
        (∀ e ∈ Nabs, (e : Set (Fin n)) ∈ R ∧ (e : Set (Fin n)) ∉ used) ∧
        Disjoint (matchVert Nabs) (matchVert N) ∧
        Covers Nabs ((U \ matchVert N) \ {u}) := by
  by_cases hY : (((U \ matchVert N) : Set (Fin n)).ncard : ℝ) ≤ (n : ℝ) / 100
  · obtain ⟨u, huS, huN, huP⟩ := huge_pick_S (N := N) (P := P) hm habs hSsub hS hP
    obtain ⟨Nabs, h1, h2, h3, h4⟩ :=
      huge_cross_step (R' := R \ used) rfl hm hmatch hUdeg habs hn hused hK hY
    exact ⟨u, huS, huN, huP, Nabs, h1, h2, h3,
      Covers.mono (subset_refl Nabs) Set.sdiff_subset h4⟩
  · exact huge_internal_step_large (N := N) (P := P) (K := K) hm hmatch hUdeg habs hn
      hused hK hB hRsub2 hSsub hS hP (not_le.mp hY)

/-! ## The iterations -/

/-- **Iteration of the perfect-coverage step.** -/
theorem huge_iter_cov {𝓗 R : Hypergraph (Fin n)} {U S : Set (Fin n)} {B : ℕ}
    (hm : HugeMargins n ρ ε γ κ ξ) (hmatch : InternalMatchingInput n B)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (hn : 4 ≤ n) (hB : (B : ℝ) ≤ ρ ^ 2 * (γ * (n : ℝ)) / 400)
    (hRsub2 : R ⊆ 𝓗.pow2)
    (hUle : ((U : Set (Fin n)).ncard : ℝ) ≤ (1 - 10 * ε) * (n : ℝ)) :
    ∀ (k K : ℕ) (N : Fin k → Set 𝓗), k ≤ K → (K : ℝ) ≤ γ * (n : ℝ) →
      (∀ i, AbsorbableBySmall 𝓗 (N i) R U S ρ ε γ κ ξ ∨
        (AbsorbableByTypical 𝓗 (N i) R U S ρ ε γ κ ξ ∧ ¬ IsDifficult U (N i))) →
      ∃ Nabs : Fin k → Set 𝓗,
        (∀ i, IsMatching 𝓗 (Nabs i)) ∧
        (∀ i j, i ≠ j → Disjoint (Nabs i) (Nabs j)) ∧
        (∀ i, ∀ e ∈ Nabs i, (e : Set (Fin n)) ∈ R) ∧
        (∀ i, Disjoint (matchVert (Nabs i)) (matchVert (N i))) ∧
        (∀ i, Covers (Nabs i) (U \ matchVert (N i))) := by
  intro k
  induction k with
  | zero =>
      intro K N hk hKR habs
      exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
        fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ k ih =>
      intro K N hk hKR habs
      let N0 : Fin k → Set 𝓗 := fun i => N i.castSucc
      have hk0 : k ≤ K := by omega
      have habs0 : ∀ i, AbsorbableBySmall 𝓗 (N0 i) R U S ρ ε γ κ ξ ∨
          (AbsorbableByTypical 𝓗 (N0 i) R U S ρ ε γ κ ξ ∧ ¬ IsDifficult U (N0 i)) :=
        fun i => habs i.castSucc
      obtain ⟨Nabs0, hmat0, hdisj0, hR0, hdisjN0, hcov0⟩ := ih K N0 hk0 hKR habs0
      set used : Hypergraph (Fin n) := famUnionIdx Nabs0 with huseddef
      have huseddeg : ∀ v : Fin n, (nbrs used v).ncard ≤ K := by
        intro v
        have h1 : (nbrs used v).ncard ≤ k := by
          rw [huseddef]
          exact ncard_nbrs_famUnionIdx_le hmat0 v
        omega
      obtain ⟨NabsL, hmatL, hRL, hdisjNL, hcovL⟩ :=
        huge_step_cov (N := N (Fin.last k)) (K := K) hm hmatch hUdeg hn huseddeg hKR hB
          hRsub2 hUle (habs (Fin.last k))
      rw [huseddef] at hRL
      refine ⟨Fin.snoc Nabs0 NabsL, ?_, ?_, ?_, ?_, ?_⟩
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
          exact (hRL e he2).2 (famOf_subset_famUnionIdx (mem_famOf_of_mem he1))
        · rw [Fin.snoc_last, Fin.snoc_castSucc, Set.disjoint_left]
          intro e he1 he2
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

/-- **Iteration of the defect step.** -/
theorem huge_iter_defect {𝓗 R : Hypergraph (Fin n)} {U S : Set (Fin n)} {B : ℕ}
    (hm : HugeMargins n ρ ε γ κ ξ) (hmatch : InternalMatchingInput n B)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (hn : 4 ≤ n) (hB : (B : ℝ) ≤ ρ ^ 2 * (γ * (n : ℝ)) / 400)
    (hRsub2 : R ⊆ 𝓗.pow2) (hSsub : S ⊆ U) :
    ∀ (k K : ℕ) (N : Fin k → Set 𝓗), k ≤ K → (K : ℝ) ≤ γ * (n : ℝ) →
      (γ + ε) * (n : ℝ) < (S.ncard : ℝ) →
      (∀ i, AbsorbableBySmall 𝓗 (N i) R U S ρ ε γ κ ξ ∨
        (AbsorbableByTypical 𝓗 (N i) R U S ρ ε γ κ ξ ∧ ¬ IsDifficult U (N i))) →
      ∃ (Nabs : Fin k → Set 𝓗) (u : Fin k → Fin n),
        (∀ i, IsMatching 𝓗 (Nabs i)) ∧
        (∀ i j, i ≠ j → Disjoint (Nabs i) (Nabs j)) ∧
        (∀ i, ∀ e ∈ Nabs i, (e : Set (Fin n)) ∈ R) ∧
        (∀ i, Disjoint (matchVert (Nabs i)) (matchVert (N i))) ∧
        (∀ i, Covers (Nabs i) ((U \ matchVert (N i)) \ {u i})) ∧
        (∀ i, u i ∈ S) ∧ Function.Injective u := by
  intro k
  induction k with
  | zero =>
      intro K N hk hKR hS habs
      exact ⟨Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
        fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
        fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ k ih =>
      intro K N hk hKR hS habs
      let N0 : Fin k → Set 𝓗 := fun i => N i.castSucc
      have hk0 : k ≤ K := by omega
      have habs0 : ∀ i, AbsorbableBySmall 𝓗 (N0 i) R U S ρ ε γ κ ξ ∨
          (AbsorbableByTypical 𝓗 (N0 i) R U S ρ ε γ κ ξ ∧ ¬ IsDifficult U (N0 i)) :=
        fun i => habs i.castSucc
      obtain ⟨Nabs0, u0, hmat0, hdisj0, hR0, hdisjN0, hcov0, huS0, hinj0⟩ :=
        ih K N0 hk0 hKR hS habs0
      set used : Hypergraph (Fin n) := famUnionIdx Nabs0 with huseddef
      have huseddeg : ∀ v : Fin n, (nbrs used v).ncard ≤ K := by
        intro v
        have h1 : (nbrs used v).ncard ≤ k := by
          rw [huseddef]
          exact ncard_nbrs_famUnionIdx_le hmat0 v
        omega
      set P : Finset (Fin n) := Finset.image u0 Finset.univ with hPdef
      have hPcard : (P.card : ℝ) ≤ γ * (n : ℝ) := by
        have h1 : P.card ≤ k := by
          rw [hPdef]
          calc (Finset.image u0 Finset.univ).card ≤ Finset.univ.card := Finset.card_image_le
            _ = k := by simp
        have h2 : (P.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
        have h3 : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast hk0
        linarith
      obtain ⟨uL, huS, huN, huP, NabsL, hmatL, hRL, hdisjNL, hcovL⟩ :=
        huge_step_defect (N := N (Fin.last k)) (P := P) (K := K) hm hmatch hUdeg hn
          huseddeg hKR hB hRsub2 hSsub hS hPcard (habs (Fin.last k))
      rw [huseddef] at hRL
      have hPmem : ∀ a : Fin k, u0 a ∈ P := by
        intro a
        rw [hPdef]
        exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
      refine ⟨Fin.snoc Nabs0 NabsL, Fin.snoc u0 uL, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
          exact (hRL e he2).2 (famOf_subset_famUnionIdx (mem_famOf_of_mem he1))
        · rw [Fin.snoc_last, Fin.snoc_castSucc, Set.disjoint_left]
          intro e he1 he2
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
        · simp only [Fin.snoc_castSucc]; exact huS0 j
        · simp only [Fin.snoc_last]; exact huS
      · intro i j hij
        rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl <;>
          rcases Fin.eq_castSucc_or_eq_last j with ⟨b, rfl⟩ | rfl
        · simp only [Fin.snoc_castSucc] at hij
          exact congrArg Fin.castSucc (hinj0 hij)
        · simp only [Fin.snoc_castSucc, Fin.snoc_last] at hij
          exact absurd (hij.symm ▸ hPmem a) huP
        · simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
          exact absurd (hij ▸ hPmem b) huP
        · rfl

/-! ## The assembly -/

/-- **Lemma `huge-edge-absorption-lemma`** (Lemma 7.3 of the paper). -/
theorem huge_edge_absorption {𝓗 R : Hypergraph (Fin n)} {U S : Set (Fin n)} {B : ℕ}
    (hm : HugeMargins n ρ ε γ κ ξ) (hmatch : InternalMatchingInput n B)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (hn : 4 ≤ n) (hB : (B : ℝ) ≤ ρ ^ 2 * (γ * (n : ℝ)) / 400)
    (hRsub2 : R ⊆ 𝓗.pow2) (hSsub : S ⊆ U)
    (hSbig : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      (γ + ε) * (n : ℝ) < (S.ncard : ℝ))
    {k : ℕ} (N : Fin k → Set 𝓗)
    (habs : ∀ i, AbsorbableBySmall 𝓗 (N i) R U S ρ ε γ κ ξ ∨
      (AbsorbableByTypical 𝓗 (N i) R U S ρ ε γ κ ξ ∧ ¬ IsDifficult U (N i)))
    (hNR : ∀ i, ∀ e ∈ N i, (e : Set (Fin n)) ∉ R)
    (hNmat : ∀ i, IsMatching 𝓗 (N i))
    (hNdisj : ∀ i j, i ≠ j → Disjoint (N i) (N j))
    (hk : (k : ℝ) ≤ γ * (n : ℝ)) :
    ∃ N' : Fin k → Set 𝓗,
      (∀ i, N i ⊆ N' i) ∧
      (∀ i, ∀ e ∈ N' i, e ∉ N i → (e : Set (Fin n)) ∈ R) ∧
      (∀ i, IsMatching 𝓗 (N' i)) ∧
      (∀ i j, i ≠ j → Disjoint (N' i) (N' j)) ∧
      (((U.ncard : ℝ) ≤ (1 - 10 * ε) * (n : ℝ)) → PerfectCoverage N' U) ∧
      (((1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ)) → NearlyPerfectCoverage N' U S) := by
  classical
  by_cases hUA : (U.ncard : ℝ) ≤ (1 - 10 * ε) * (n : ℝ)
  · -- perfect coverage
    obtain ⟨Nabs, hmat, hdisj, hRN, hdisjN, hcov⟩ :=
      huge_iter_cov (𝓗 := 𝓗) (R := R) (U := U) (S := S) (B := B) hm hmatch hUdeg hn hB
        hRsub2 hUA k k N le_rfl hk habs
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
      · exact hRN i e h2
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
      · exact (hNR i e hi) (hRN j e hj)
      · exact (hNR j e hj) (hRN i e hi)
      · exact (Set.disjoint_left.mp (hdisj i j hij)) hi hj
    · intro _ i x hx
      by_cases hxi : x ∈ matchVert (N i)
      · exact matchVert_mono (hsub1 i) hxi
      · exact matchVert_mono (hsub2 i) (hcov i ⟨hx, hxi⟩)
    · intro hc
      exact absurd hc (not_lt.mpr hUA)
  · -- nearly-perfect coverage, defects in `S`
    obtain ⟨Nabs, u, hmat, hdisj, hRN, hdisjN, hcov, huS, hinj⟩ :=
      huge_iter_defect (𝓗 := 𝓗) (R := R) (U := U) (S := S) (B := B) hm hmatch hUdeg hn
        hB hRsub2 hSsub k k N le_rfl hk (hSbig (not_le.mp hUA)) habs
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
      · exact hRN i e h2
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
      · exact (hNR i e hi) (hRN j e hj)
      · exact (hNR j e hj) (hRN i e hi)
      · exact (Set.disjoint_left.mp (hdisj i j hij)) hi hj
    · intro _
      refine ⟨?_, fun i x hx => (hmiss i x hx.1 hx.2).symm ▸ huS i, ?_⟩
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
