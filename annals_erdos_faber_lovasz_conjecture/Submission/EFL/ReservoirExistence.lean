import Submission.EFL.Pow2Edges
import Submission.Commons.Combinatorics.FiniteSampling.exists_finset_sum_close
import Submission.Commons.Analysis.Real.reservoir_union_bound

set_option autoImplicit false
open scoped BigOperators
namespace ErdosFaberLovaszConjecture
noncomputable section
variable {n : ℕ}

/-! ## The three families of events of the random reservoir -/

theorem card_canonFinset_filter {G : Hypergraph (Fin n)} (P : Set (Fin n) → Prop) [DecidablePred P] :
    ((canonFinset G).filter P).card = Nat.card {e : G // P (e.1 : Set (Fin n))} := by
  classical
  have h : Nat.card {e : Set (Fin n) // e ∈ G ∧ P e} = ((canonFinset G).filter P).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨heG, hP⟩
      exact ⟨by simpa [canonFinset] using heG, hP⟩
    · rintro ⟨he, hP⟩
      exact ⟨by simpa [canonFinset] using he, hP⟩
  rw [← h]
  exact (Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun e : Set (Fin n) => e ∈ G) P)).symm

/-- The `G`-edges through `v`. -/
noncomputable def starEv (G : Hypergraph (Fin n)) (v : Fin n) : Finset (Set (Fin n)) := by
  classical
  exact (canonFinset G).filter (fun e => v ∈ e)

/-- The `G`-edges through `v` whose other endpoint lies in `X`. -/
noncomputable def pairEv (G : Hypergraph (Fin n)) (X : Set (Fin n)) (v : Fin n) :
    Finset (Set (Fin n)) := by
  classical
  exact (canonFinset G).filter (fun e => v ∈ e ∧ (e \ {v}) ⊆ X)

/-- The `G`-edges meeting both `S` and `T`. -/
noncomputable def crossEv (G : Hypergraph (Fin n)) (S T : Finset (Fin n)) :
    Finset (Set (Fin n)) := by
  classical
  exact (canonFinset G).filter
    (fun e => (∃ s ∈ e, s ∈ (S : Set (Fin n))) ∧ (∃ t ∈ e, t ∈ (T : Set (Fin n))))

/-- The number of `G`-edges through `v` is the `G`-degree of `v`. -/
theorem card_starEv {G : Hypergraph (Fin n)} (h2 : ∀ e ∈ G, edgeSize e = 2) (v : Fin n) :
    (starEv G v).card = (nbrs G v).ncard := by
  classical
  rw [starEv, card_canonFinset_filter (G := G) (fun e => v ∈ e)]
  exact (ncard_nbrs_eq_hypergraphDegree h2 v).symm

/-- The number of `G`-edges through `v` with other endpoint in `X` is the
number of `G`-neighbours of `v` inside `X`. -/
theorem card_pairEv {G : Hypergraph (Fin n)} (h2 : ∀ e ∈ G, edgeSize e = 2)
    (X : Set (Fin n)) (v : Fin n) :
    (pairEv G X v).card = (X ∩ nbrs G v).ncard := by
  classical
  rw [pairEv, card_canonFinset_filter (G := G) (fun e => v ∈ e ∧ (e \ {v}) ⊆ X)]
  exact (ncard_inter_nbrs_eq h2 X v).symm

/-- The number of `G`-edges between two disjoint vertex sets is `edgeCount`. -/
theorem card_crossEv {G : Hypergraph (Fin n)} (h2 : ∀ e ∈ G, edgeSize e = 2)
    {S T : Finset (Fin n)} (hd : Disjoint S T) :
    (crossEv G S T).card = edgeCount G S T := by
  classical
  have h1 : (crossEv G S T).card = Nat.card {e : G //
      (∃ s ∈ (e.1 : Set (Fin n)), s ∈ (S : Set (Fin n))) ∧
      (∃ t ∈ (e.1 : Set (Fin n)), t ∈ (T : Set (Fin n)))} := by
    rw [crossEv, card_canonFinset_filter]
  have h2' : (edgesBetween G S T).card = Nat.card {e : G //
      (∃ s ∈ (e.1 : Set (Fin n)), s ∈ (S : Set (Fin n))) ∧
      (∃ t ∈ (e.1 : Set (Fin n)), t ∈ (T : Set (Fin n)))} := by
    unfold edgesBetween
    rw [card_canonFinset_filter]
  rw [h1, ← h2', ← edgeCount_eq_edgesBetween h2 hd]


/-! ## The index type of the random reservoir and its events -/

/-- The index type of the conditions imposed on the random reservoir:
the vertex degrees, the two typicality conditions for each `X ∈ 𝓥`, and the
regularity conditions for every pair of disjoint sets of size `≥ ξn`. -/
abbrev ResIdx (ξ : ℝ) (𝓥 : Finset (Set (Fin n))) : Type :=
  (Fin n) ⊕ ((Fin n × 𝓥) ⊕ ((Fin n × 𝓥) ⊕ ({p : Finset (Fin n) × Finset (Fin n) //
    Disjoint p.1 p.2 ∧ ξ * (n : ℝ) ≤ (p.1.card : ℝ) ∧ ξ * (n : ℝ) ≤ (p.2.card : ℝ)})))

/-- The event whose sampling count is constrained at each index. -/
noncomputable def resEv (𝓗 G' : Hypergraph (Fin n)) (ξ : ℝ) (𝓥 : Finset (Set (Fin n))) :
    ResIdx ξ 𝓥 → Finset (Set (Fin n)) := by
  classical
  exact fun i =>
    match i with
    | Sum.inl v => starEv 𝓗.pow2 v
    | Sum.inr (Sum.inl (v, X)) => pairEv G' (X : Set (Fin n)) v
    | Sum.inr (Sum.inr (Sum.inl (v, X))) => pairEv G' ((X : Set (Fin n)))ᶜ v
    | Sum.inr (Sum.inr (Sum.inr p)) => crossEv G' p.1.1 p.1.2

/-- The tolerance at each index. -/
noncomputable def resTol (ξ : ℝ) (𝓥 : Finset (Set (Fin n))) : ResIdx ξ 𝓥 → ℝ :=
  fun i =>
    match i with
    | Sum.inl _ => ξ * (n : ℝ)
    | Sum.inr (Sum.inl _) => ξ * (n : ℝ)
    | Sum.inr (Sum.inr (Sum.inl _)) => ξ * (n : ℝ)
    | Sum.inr (Sum.inr (Sum.inr p)) => ξ * (p.1.1.card : ℝ) * (p.1.2.card : ℝ) / 2

theorem resTol_nonneg (ξ : ℝ) (𝓥 : Finset (Set (Fin n))) (hξ : 0 ≤ ξ) (i : ResIdx ξ 𝓥) :
    0 ≤ resTol ξ 𝓥 i := by
  match i with
  | Sum.inl v => exact mul_nonneg hξ (Nat.cast_nonneg n)
  | Sum.inr (Sum.inl p) => exact mul_nonneg hξ (Nat.cast_nonneg n)
  | Sum.inr (Sum.inr (Sum.inl p)) => exact mul_nonneg hξ (Nat.cast_nonneg n)
  | Sum.inr (Sum.inr (Sum.inr p)) =>
      exact div_nonneg (mul_nonneg (mul_nonneg hξ (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
        (by norm_num)

theorem resEv_subset_canon (𝓗 G' : Hypergraph (Fin n)) (ξ : ℝ) (𝓥 : Finset (Set (Fin n)))
    (hG' : G' ⊆ 𝓗.pow2) (i : ResIdx ξ 𝓥) :
    ↑(resEv 𝓗 G' ξ 𝓥 i) ⊆ canonFinset 𝓗.pow2 := by
  classical
  match i with
  | Sum.inl v =>
      intro e he
      simp only [Finset.mem_coe, resEv, starEv, canonFinset, Finset.mem_filter,
        Finset.mem_univ, true_and] at he ⊢
      exact he.1
  | Sum.inr (Sum.inl p) =>
      intro e he
      simp only [Finset.mem_coe, resEv, pairEv, canonFinset, Finset.mem_filter,
        Finset.mem_univ, true_and] at he ⊢
      exact hG' he.1
  | Sum.inr (Sum.inr (Sum.inl p)) =>
      intro e he
      simp only [Finset.mem_coe, resEv, pairEv, canonFinset, Finset.mem_filter,
        Finset.mem_univ, true_and] at he ⊢
      exact hG' he.1
  | Sum.inr (Sum.inr (Sum.inr p)) =>
      intro e he
      simp only [Finset.mem_coe, resEv, crossEv, canonFinset, Finset.mem_filter,
        Finset.mem_univ, true_and] at he ⊢
      exact hG' he.1


/-! ## Proposition 11.1: the pseudorandom reservoir exists -/

/-- **Proposition 11.1 (`prop:pseudo_reservoir`), core form.**  If the union
bound for the `n` degree conditions, the `2n|𝓥|` typicality conditions and the
`4ⁿ` regularity conditions holds, then there is a set `R ⊆ E(G)` of 2-edges
satisfying all of them. -/
theorem exists_reservoir_core (𝓗 : Hypergraph (Fin n)) (hlin : 𝓗.IsLinear)
    {G' : Hypergraph (Fin n)} (hG' : G' ⊆ 𝓗.pow2)
    (𝓥 : Finset (Set (Fin n))) {ρ ξ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hξ0 : 0 < ξ)
    (hbound : (Finset.univ.sum fun i : ResIdx ξ 𝓥 =>
        2 * Real.exp (-((resTol ξ 𝓥 i) ^ 2) /
          (2 * (ρ * ((resEv 𝓗 G' ξ 𝓥 i).card : ℝ) + resTol ξ 𝓥 i / 3)))) < 1) :
    ∃ R : Hypergraph (Fin n), R ⊆ 𝓗.pow2 ∧
      (∀ v : Fin n, |((degAt R v : ℝ) - ρ * (degAt 𝓗.pow2 v : ℝ))| ≤ ξ * (n : ℝ)) ∧
      Typical G' (R ∩ G') ρ ξ (𝓥 : Set (Set (Fin n))) ∧
      UpperRegular G' (R ∩ G') ρ ξ ∧
      LowerRegular G' (R ∩ G') ρ ξ := by
  classical
  obtain ⟨R0, hR0⟩ := Commons.Combinatorics.FiniteSampling.exists_finset_sum_close (E := Set (Fin n)) hρ0.le hρ1
    (fun i => resTol_nonneg ξ 𝓥 hξ0.le i) hbound
  set Rf : Finset (Set (Fin n)) := R0 ∩ canonFinset 𝓗.pow2 with hRf
  have hRfsub : ↑Rf ⊆ 𝓗.pow2 := by
    intro e he
    have h1 : e ∈ canonFinset 𝓗.pow2 := (Finset.mem_inter.mp he).2
    simpa [canonFinset] using h1
  have h2Rf : ∀ e ∈ Rf, edgeSize e = 2 := fun e he => (mem_pow2).mp (hRfsub he) |>.2
  have hdev : ∀ i : ResIdx ξ 𝓥,
      |(((Rf ∩ resEv 𝓗 G' ξ 𝓥 i).card : ℝ)) - ρ * ((resEv 𝓗 G' ξ 𝓥 i).card : ℝ)|
        ≤ resTol ξ 𝓥 i := by
    intro i
    have h := hR0 i
    have heq : R0 ∩ resEv 𝓗 G' ξ 𝓥 i = Rf ∩ resEv 𝓗 G' ξ 𝓥 i := by
      rw [hRf, Finset.inter_assoc,
        Finset.inter_eq_right.mpr (resEv_subset_canon 𝓗 G' ξ 𝓥 hG' i)]
    rwa [heq] at h
  set Rs : Hypergraph (Fin n) := {e : Set (Fin n) | e ∈ Rf} with hRs
  have hRssub : Rs ⊆ 𝓗.pow2 := by
    intro e he
    exact hRfsub he
  have h2Rs : ∀ e ∈ Rs, edgeSize e = 2 := fun e he => h2Rf e he
  refine ⟨Rs, hRssub, ?_, ?_, ?_, ?_⟩
  · -- (P1) the degrees
    intro v
    have hcard : (Rf ∩ starEv 𝓗.pow2 v).card = (starEv Rs v).card := by
      congr 1
      ext e
      simp only [Finset.mem_inter, starEv, canonFinset, Finset.mem_filter, Finset.mem_univ,
        true_and, hRs, Set.mem_setOf_eq]
      constructor
      · rintro ⟨heR, _, hv⟩; exact ⟨heR, hv⟩
      · rintro ⟨heR, hv⟩; exact ⟨heR, hRfsub heR, hv⟩
    have hstarP : (starEv Rs v).card = (nbrs Rs v).ncard := card_starEv h2Rs v
    have hstarG : (starEv 𝓗.pow2 v).card = (nbrs 𝓗.pow2 v).ncard :=
      card_starEv (fun e he => (mem_pow2).mp he |>.2) v
    have := hdev (Sum.inl v)
    simp only [resTol, resEv] at this
    rw [hcard, hstarP, hstarG] at this
    simpa [degAt] using this
  · -- typicality
    intro X hX v
    have hXmem : X ∈ (𝓥 : Set (Set (Fin n))) := by simpa using hX
    have hX' : ∃ Y ∈ 𝓥, (Y : Set (Fin n)) = X := ⟨X, by simpa using hX, rfl⟩
    constructor
    · obtain ⟨Y, hY, hYX⟩ := hX'
      have hmem : |(((Rf ∩ pairEv G' (Y : Set (Fin n)) v).card : ℝ)) -
            ρ * ((pairEv G' (Y : Set (Fin n)) v).card : ℝ)| ≤ ξ * (n : ℝ) := by
        have h := hdev (Sum.inr (Sum.inl (v, ⟨Y, hY⟩)))
        simpa [resTol, resEv] using h
      have hcard1 : (Rf ∩ pairEv G' (Y : Set (Fin n)) v).card
          = (pairEv (Rs ∩ G') (Y : Set (Fin n)) v).card := by
        congr 1
        ext e
        simp only [Finset.mem_inter, pairEv, canonFinset, Finset.mem_filter, Finset.mem_univ,
          true_and, hRs, Set.mem_setOf_eq, Set.mem_inter_iff]
        constructor
        · rintro ⟨heR, hG'e, hv, hsub⟩
          exact ⟨⟨heR, hG'e⟩, hv, hsub⟩
        · rintro ⟨⟨heR, hG'e⟩, hv, hsub⟩
          exact ⟨heR, hG'e, hv, hsub⟩
      have hcard2 : (pairEv G' (Y : Set (Fin n)) v).card
          = ((Y : Set (Fin n)) ∩ nbrs G' v).ncard := by
        rw [pairEv, card_canonFinset_filter (G := G')
          (fun e => v ∈ e ∧ (e \ {v}) ⊆ (Y : Set (Fin n)))]
        exact (ncard_inter_nbrs_eq (fun e he => (mem_pow2).mp (hG' he) |>.2) _ v).symm
      have hcard3 : (pairEv (Rs ∩ G') (Y : Set (Fin n)) v).card
          = ((Y : Set (Fin n)) ∩ nbrs (Rs ∩ G') v).ncard := by
        rw [pairEv, card_canonFinset_filter (G := Rs ∩ G')
          (fun e => v ∈ e ∧ (e \ {v}) ⊆ (Y : Set (Fin n)))]
        exact (ncard_inter_nbrs_eq
          (fun e he => h2Rs e (Set.mem_of_mem_inter_left (by exact he))) _ v).symm
      rw [hcard1, hcard3, hcard2, hYX] at hmem
      exact hmem
    · obtain ⟨Y, hY, hYX⟩ := hX'
      have hYc : Y ∈ 𝓥 := hY
      have hmem : |(((Rf ∩ pairEv G' ((Y : Set (Fin n)))ᶜ v).card : ℝ)) -
            ρ * ((pairEv G' ((Y : Set (Fin n)))ᶜ v).card : ℝ)| ≤ ξ * (n : ℝ) := by
        have h := hdev (Sum.inr (Sum.inr (Sum.inl (v, ⟨Y, hY⟩))))
        simpa [resTol, resEv] using h
      have hcard1 : (Rf ∩ pairEv G' ((Y : Set (Fin n)))ᶜ v).card
          = (pairEv (Rs ∩ G') ((Y : Set (Fin n)))ᶜ v).card := by
        congr 1
        ext e
        simp only [Finset.mem_inter, pairEv, canonFinset, Finset.mem_filter, Finset.mem_univ,
          true_and, hRs, Set.mem_setOf_eq, Set.mem_inter_iff]
        constructor
        · rintro ⟨heR, hG'e, hv, hsub⟩
          exact ⟨⟨heR, hG'e⟩, hv, hsub⟩
        · rintro ⟨⟨heR, hG'e⟩, hv, hsub⟩
          exact ⟨heR, hG'e, hv, hsub⟩
      have hcard2 : (pairEv G' ((Y : Set (Fin n)))ᶜ v).card
          = (((Y : Set (Fin n)))ᶜ ∩ nbrs G' v).ncard := by
        rw [pairEv, card_canonFinset_filter (G := G')
          (fun e => v ∈ e ∧ (e \ {v}) ⊆ ((Y : Set (Fin n)))ᶜ)]
        exact (ncard_inter_nbrs_eq (fun e he => (mem_pow2).mp (hG' he) |>.2) _ v).symm
      have hcard3 : (pairEv (Rs ∩ G') ((Y : Set (Fin n)))ᶜ v).card
          = (((Y : Set (Fin n)))ᶜ ∩ nbrs (Rs ∩ G') v).ncard := by
        rw [pairEv, card_canonFinset_filter (G := Rs ∩ G')
          (fun e => v ∈ e ∧ (e \ {v}) ⊆ ((Y : Set (Fin n)))ᶜ)]
        exact (ncard_inter_nbrs_eq
          (fun e he => h2Rs e (Set.mem_of_mem_inter_left (by exact he))) _ v).symm
      rw [hcard1, hcard3, hcard2, hYX] at hmem
      exact hmem
  · -- upper regularity
    intro S T hd hS hT
    have hpair : (⟨(S, T), hd, hS, hT⟩ : {p : Finset (Fin n) × Finset (Fin n) //
        Disjoint p.1 p.2 ∧ ξ * (n : ℝ) ≤ (p.1.card : ℝ) ∧ ξ * (n : ℝ) ≤ (p.2.card : ℝ)}) ∈
        Finset.univ := Finset.mem_univ _
    have hmem : |(((Rf ∩ crossEv G' S T).card : ℝ)) -
        ρ * ((crossEv G' S T).card : ℝ)| ≤ ξ * (S.card : ℝ) * (T.card : ℝ) / 2 := by
      have h := hdev (Sum.inr (Sum.inr (Sum.inr ⟨(S, T), hd, hS, hT⟩)))
      simpa [resTol, resEv] using h
    have hcard1 : (Rf ∩ crossEv G' S T).card = (crossEv (Rs ∩ G') S T).card := by
      congr 1
      ext e
      simp only [Finset.mem_inter, crossEv, canonFinset, Finset.mem_filter, Finset.mem_univ,
        true_and, hRs, Set.mem_setOf_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨heR, hG'e, h1, h2⟩; exact ⟨⟨heR, hG'e⟩, h1, h2⟩
      · rintro ⟨⟨heR, hG'e⟩, h1, h2⟩; exact ⟨heR, hG'e, h1, h2⟩
    have hcard2 : (crossEv G' S T).card = edgeCount G' S T :=
      card_crossEv (fun e he => (mem_pow2).mp (hG' he) |>.2) hd
    have hcard3 : (crossEv (Rs ∩ G') S T).card = edgeCount (Rs ∩ G') S T :=
      card_crossEv (fun e he => h2Rs e (Set.mem_of_mem_inter_left (by exact he))) hd
    rw [hcard1, hcard3, hcard2] at hmem
    have h1 := (abs_le.mp hmem).2
    have h2 : ξ * (S.card : ℝ) * (T.card : ℝ) / 2 ≤ ξ * (S.card : ℝ) * (T.card : ℝ) := by
      have := mul_nonneg (mul_nonneg hξ0.le (Nat.cast_nonneg (α := ℝ) S.card))
        (Nat.cast_nonneg (α := ℝ) T.card)
      linarith
    linarith [h1, h2]
  · -- lower regularity
    intro S T hd hS hT
    have hmem : |(((Rf ∩ crossEv G' S T).card : ℝ)) -
        ρ * ((crossEv G' S T).card : ℝ)| ≤ ξ * (S.card : ℝ) * (T.card : ℝ) / 2 := by
      have h := hdev (Sum.inr (Sum.inr (Sum.inr ⟨(S, T), hd, hS, hT⟩)))
      simpa [resTol, resEv] using h
    have hcard1 : (Rf ∩ crossEv G' S T).card = (crossEv (Rs ∩ G') S T).card := by
      congr 1
      ext e
      simp only [Finset.mem_inter, crossEv, canonFinset, Finset.mem_filter, Finset.mem_univ,
        true_and, hRs, Set.mem_setOf_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨heR, hG'e, h1, h2⟩; exact ⟨⟨heR, hG'e⟩, h1, h2⟩
      · rintro ⟨⟨heR, hG'e⟩, h1, h2⟩; exact ⟨heR, hG'e, h1, h2⟩
    have hcard2 : (crossEv G' S T).card = edgeCount G' S T :=
      card_crossEv (fun e he => (mem_pow2).mp (hG' he) |>.2) hd
    have hcard3 : (crossEv (Rs ∩ G') S T).card = edgeCount (Rs ∩ G') S T :=
      card_crossEv (fun e he => h2Rs e (Set.mem_of_mem_inter_left (by exact he))) hd
    rw [hcard1, hcard3, hcard2] at hmem
    have h1 := (abs_le.mp hmem).1
    have h2 : ξ * (S.card : ℝ) * (T.card : ℝ) / 2 ≤ ξ * (S.card : ℝ) * (T.card : ℝ) := by
      have := mul_nonneg (mul_nonneg hξ0.le (Nat.cast_nonneg (α := ℝ) S.card))
        (Nat.cast_nonneg (α := ℝ) T.card)
      linarith
    linarith [h1, h2]

theorem card_pairs_le (n : ℕ) : Fintype.card (Finset (Fin n) × Finset (Fin n)) = 4 ^ n := by
  rw [Fintype.card_prod, Fintype.card_finset, Fintype.card_fin, ← mul_pow]
  norm_num

/-- The Chernoff exponent for the degree/typicality events: the tolerance is
`ξn` and the event has size at most `M ≤ m`. -/
theorem exp_bound_linear {ρ ξ M : ℝ} {m : ℕ} (hρ : 0 < ρ) (hξ : 0 < ξ) (hM0 : 0 ≤ M)
    (hM : M ≤ (m : ℝ)) (hm : 1 ≤ m) {c : ℝ} (hc : c ≤ ξ ^ 2 / (2 * (ρ + ξ / 3))) :
    c * (m : ℝ) ≤ (ξ * (m : ℝ)) ^ 2 / (2 * (ρ * M + ξ * (m : ℝ) / 3)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hD1 : (0 : ℝ) < 2 * (ρ * M + ξ * (m : ℝ) / 3) := by nlinarith [hρ, hξ, hM0, hmR]
  have hD2 : (0 : ℝ) < 2 * (ρ * (m : ℝ) + ξ * (m : ℝ) / 3) := by nlinarith [hρ, hξ, hmR]
  have hstep1 : (ξ * (m : ℝ)) ^ 2 / (2 * (ρ * (m : ℝ) + ξ * (m : ℝ) / 3))
      ≤ (ξ * (m : ℝ)) ^ 2 / (2 * (ρ * M + ξ * (m : ℝ) / 3)) := by
    rw [div_le_div_iff₀ hD2 hD1]
    have h1 : ρ * M ≤ ρ * (m : ℝ) := mul_le_mul_of_nonneg_left hM hρ.le
    nlinarith [h1, hξ, hmR]
  have hstep2 : (ξ * (m : ℝ)) ^ 2 / (2 * (ρ * (m : ℝ) + ξ * (m : ℝ) / 3))
      = ξ ^ 2 / (2 * (ρ + ξ / 3)) * (m : ℝ) := by
    field_simp
  rw [hstep2] at hstep1
  calc c * (m : ℝ) ≤ (ξ ^ 2 / (2 * (ρ + ξ / 3))) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg m)
    _ = ξ ^ 2 / (2 * (ρ + ξ / 3)) * (m : ℝ) := rfl
    _ ≤ _ := hstep1


/-- The Chernoff exponent for the regularity events. -/
theorem exp_bound_quadratic {ρ ξ S T A : ℝ} {m : ℕ} (hρ : 0 < ρ) (hξ : 0 < ξ) (hm : 1 ≤ m)
    (hS : ξ * (m : ℝ) ≤ S) (hT : ξ * (m : ℝ) ≤ T) (hA : 0 ≤ A) (hAST : A ≤ S * T)
    {c : ℝ} (hc : c ≤ ξ ^ 4 / (4 * (2 * ρ + ξ / 3))) :
    c * (m : ℝ) ^ 2 ≤ (ξ * S * T / 2) ^ 2 / (2 * (ρ * A + ξ * S * T / 6)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hξm : 0 < ξ * (m : ℝ) := mul_pos hξ hmR
  have hS0 : 0 < S := lt_of_lt_of_le hξm hS
  have hT0 : 0 < T := lt_of_lt_of_le hξm hT
  have hP0 : 0 < S * T := mul_pos hS0 hT0
  have hD1 : (0 : ℝ) < 2 * (ρ * A + ξ * S * T / 6) := by nlinarith [hρ, hξ, hA, hP0]
  have hD2 : (0 : ℝ) < 2 * (ρ * (S * T) + ξ * S * T / 6) := by nlinarith [hρ, hξ, hP0]
  have hstep1 : (ξ * S * T / 2) ^ 2 / (2 * (ρ * (S * T) + ξ * S * T / 6))
      ≤ (ξ * S * T / 2) ^ 2 / (2 * (ρ * A + ξ * S * T / 6)) := by
    rw [div_le_div_iff₀ hD2 hD1]
    have h1 : ρ * A ≤ ρ * (S * T) := mul_le_mul_of_nonneg_left hAST hρ.le
    nlinarith [h1, hξ, hP0]
  have hstep2 : (ξ * S * T / 2) ^ 2 / (2 * (ρ * (S * T) + ξ * S * T / 6))
      = ξ ^ 2 * (S * T) / (8 * ρ + 4 * ξ / 3) := by
    field_simp
    ring
  have hstep3 : ξ ^ 4 / (4 * (2 * ρ + ξ / 3)) * (m : ℝ) ^ 2
      ≤ ξ ^ 2 * (S * T) / (8 * ρ + 4 * ξ / 3) := by
    have hD3 : (0 : ℝ) < 4 * (2 * ρ + ξ / 3) := by nlinarith [hρ, hξ]
    have hD4 : (0 : ℝ) < 8 * ρ + 4 * ξ / 3 := by nlinarith [hρ, hξ]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hD3 hD4]
    have hST : ξ ^ 2 * (m : ℝ) ^ 2 ≤ S * T := by
      calc ξ ^ 2 * (m : ℝ) ^ 2 = (ξ * (m : ℝ)) * (ξ * (m : ℝ)) := by ring
        _ ≤ S * T := mul_le_mul hS hT hξm.le (le_trans hξm.le hS)
    have h2 : ξ ^ 4 * (m : ℝ) ^ 2 * (4 * (2 * ρ + ξ / 3))
        ≤ ξ ^ 2 * (S * T) * (4 * (2 * ρ + ξ / 3)) := by
      have hfac : (0 : ℝ) ≤ ξ ^ 2 * (4 * (2 * ρ + ξ / 3)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hST hfac]
    nlinarith [h2]
  calc c * (m : ℝ) ^ 2 ≤ ξ ^ 4 / (4 * (2 * ρ + ξ / 3)) * (m : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ ξ ^ 2 * (S * T) / (8 * ρ + 4 * ξ / 3) := hstep3
    _ = (ξ * S * T / 2) ^ 2 / (2 * (ρ * (S * T) + ξ * S * T / 6)) := hstep2.symm
    _ ≤ (ξ * S * T / 2) ^ 2 / (2 * (ρ * A + ξ * S * T / 6)) := hstep1


/-- **The union bound of Proposition 11.1.**  The sum of the Chernoff failure
probabilities of all the events of the reservoir is `< 1`. -/
theorem reservoir_sum_bound (𝓗 : Hypergraph (Fin n)) {G' : Hypergraph (Fin n)}
    (hG' : G' ⊆ 𝓗.pow2)
    (𝓥 : Finset (Set (Fin n))) {ρ ξ : ℝ} (hρ0 : 0 < ρ) (hξ0 : 0 < ξ)
    (hn : 1 ≤ n)
    (hnum : (2 * (n : ℝ) + 4 * (n : ℝ) * (𝓥.card : ℝ)) *
          Real.exp (-(ξ ^ 2 / (2 * (ρ + ξ / 3)) * (n : ℝ))) +
        2 * ((4 : ℝ) ^ n) * Real.exp (-(ξ ^ 4 / (4 * (2 * ρ + ξ / 3)) * (n : ℝ) ^ 2)) < 1) :
    (∑ i : ResIdx ξ 𝓥, 2 * Real.exp (-((resTol ξ 𝓥 i) ^ 2) /
          (2 * (ρ * ((resEv 𝓗 G' ξ 𝓥 i).card : ℝ) + resTol ξ 𝓥 i / 3)))) < 1 := by
  classical
  set B1 : ℝ := 2 * Real.exp (-(ξ ^ 2 / (2 * (ρ + ξ / 3)) * (n : ℝ))) with hB1
  set B2 : ℝ := 2 * Real.exp (-(ξ ^ 4 / (4 * (2 * ρ + ξ / 3)) * (n : ℝ) ^ 2)) with hB2
  have hcard_le : ∀ A : Finset (Set (Fin n)), (A.card : ℝ) ≤ (n : ℝ) ∨ True := fun _ => Or.inr trivial
  -- The four groups of indices
  have hstar : ∀ v : Fin n,
      2 * Real.exp (-((resTol ξ 𝓥 (Sum.inl v)) ^ 2) /
        (2 * (ρ * ((resEv 𝓗 G' ξ 𝓥 (Sum.inl v)).card : ℝ) + resTol ξ 𝓥 (Sum.inl v) / 3)))
      ≤ B1 := by
    intro v
    have hEv : resEv 𝓗 G' ξ 𝓥 (Sum.inl v) = starEv 𝓗.pow2 v := by simp [resEv]
    have hcardN : ((resEv 𝓗 G' ξ 𝓥 (Sum.inl v)).card : ℝ) ≤ (n : ℝ) := by
      rw [hEv, card_starEv (fun e he => (mem_pow2).mp he |>.2) v]
      calc ((nbrs 𝓗.pow2 v).ncard : ℝ) ≤ ((Set.univ : Set (Fin n)).ncard : ℝ) :=
            Nat.cast_le.mpr (Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _))
        _ = (n : ℝ) := by
            rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    have htol : resTol ξ 𝓥 (Sum.inl v) = ξ * (n : ℝ) := by simp [resTol]
    have hexp := exp_bound_linear (m := n) hρ0 hξ0 (Nat.cast_nonneg _) hcardN hn (le_refl _)
    rw [hB1, htol]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hexp))
      (by norm_num : (0 : ℝ) ≤ 2)
  have hpair : ∀ p : Fin n × 𝓥,
      2 * Real.exp (-((resTol ξ 𝓥 (Sum.inr (Sum.inl p))) ^ 2) /
        (2 * (ρ * ((resEv 𝓗 G' ξ 𝓥 (Sum.inr (Sum.inl p))).card : ℝ)
          + resTol ξ 𝓥 (Sum.inr (Sum.inl p)) / 3))) ≤ B1 := by
    intro p
    obtain ⟨v, X⟩ := p
    have hEv : resEv 𝓗 G' ξ 𝓥 (Sum.inr (Sum.inl (v, X))) = pairEv G' (X : Set (Fin n)) v := by
      simp [resEv]
    have hcardN : ((resEv 𝓗 G' ξ 𝓥 (Sum.inr (Sum.inl (v, X)))).card : ℝ) ≤ (n : ℝ) := by
      rw [hEv, card_pairEv (fun e he => (mem_pow2).mp (hG' he) |>.2) (X : Set (Fin n)) v]
      calc (((X : Set (Fin n)) ∩ nbrs G' v).ncard : ℝ) ≤ ((Set.univ : Set (Fin n)).ncard : ℝ) :=
            Nat.cast_le.mpr (Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _))
        _ = (n : ℝ) := by
            rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    have htol : resTol ξ 𝓥 (Sum.inr (Sum.inl (v, X))) = ξ * (n : ℝ) := by simp [resTol]
    have hexp := exp_bound_linear (m := n) hρ0 hξ0 (Nat.cast_nonneg _) hcardN hn (le_refl _)
    rw [hB1, htol]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hexp))
      (by norm_num : (0 : ℝ) ≤ 2)
  have hpair2 : ∀ p : Fin n × 𝓥,
      2 * Real.exp (-((resTol ξ 𝓥 (Sum.inr (Sum.inr (Sum.inl p)))) ^ 2) /
        (2 * (ρ * ((resEv 𝓗 G' ξ 𝓥 (Sum.inr (Sum.inr (Sum.inl p)))).card : ℝ)
          + resTol ξ 𝓥 (Sum.inr (Sum.inr (Sum.inl p))) / 3))) ≤ B1 := by
    intro p
    obtain ⟨v, X⟩ := p
    have hEv : resEv 𝓗 G' ξ 𝓥 (Sum.inr (Sum.inr (Sum.inl (v, X)))) =
        pairEv G' ((X : Set (Fin n)))ᶜ v := by simp [resEv]
    have hcardN : ((resEv 𝓗 G' ξ 𝓥 (Sum.inr (Sum.inr (Sum.inl (v, X))))).card : ℝ) ≤ (n : ℝ) := by
      rw [hEv, card_pairEv (fun e he => (mem_pow2).mp (hG' he) |>.2) ((X : Set (Fin n)))ᶜ v]
      calc ((((X : Set (Fin n)))ᶜ ∩ nbrs G' v).ncard : ℝ) ≤ ((Set.univ : Set (Fin n)).ncard : ℝ) :=
            Nat.cast_le.mpr (Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _))
        _ = (n : ℝ) := by
            rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    have htol : resTol ξ 𝓥 (Sum.inr (Sum.inr (Sum.inl (v, X)))) = ξ * (n : ℝ) := by simp [resTol]
    have hexp := exp_bound_linear (m := n) hρ0 hξ0 (Nat.cast_nonneg _) hcardN hn (le_refl _)
    rw [hB1, htol]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hexp))
      (by norm_num : (0 : ℝ) ≤ 2)
  have hcross : ∀ p : {p : Finset (Fin n) × Finset (Fin n) //
        Disjoint p.1 p.2 ∧ ξ * (n : ℝ) ≤ (p.1.card : ℝ) ∧ ξ * (n : ℝ) ≤ (p.2.card : ℝ)},
      2 * Real.exp (-((resTol ξ 𝓥 (Sum.inr (Sum.inr (Sum.inr p)))) ^ 2) /
        (2 * (ρ * ((resEv 𝓗 G' ξ 𝓥 (Sum.inr (Sum.inr (Sum.inr p)))).card : ℝ)
          + resTol ξ 𝓥 (Sum.inr (Sum.inr (Sum.inr p))) / 3))) ≤ B2 := by
    intro p
    obtain ⟨⟨S, T⟩, hd, hS, hT⟩ := p
    have hEv : resEv 𝓗 G' ξ 𝓥 (Sum.inr (Sum.inr (Sum.inr ⟨(S, T), hd, hS, hT⟩))) =
        crossEv G' S T := by simp [resEv]
    have hcardN : ((resEv 𝓗 G' ξ 𝓥
        (Sum.inr (Sum.inr (Sum.inr ⟨(S, T), hd, hS, hT⟩)))).card : ℝ) ≤ (S.card : ℝ) * (T.card : ℝ) := by
      rw [hEv, card_crossEv (fun e he => (mem_pow2).mp (hG' he) |>.2) hd]
      calc (edgeCount G' S T : ℝ) ≤ ((S ×ˢ T).card : ℝ) := by
            rw [edgeCount]
            exact_mod_cast Finset.card_filter_le _ _
        _ = (S.card : ℝ) * (T.card : ℝ) := by
            rw [Finset.card_product, Nat.cast_mul]
    have htol : resTol ξ 𝓥 (Sum.inr (Sum.inr (Sum.inr ⟨(S, T), hd, hS, hT⟩))) =
        ξ * (S.card : ℝ) * (T.card : ℝ) / 2 := by simp [resTol]
    have hexp := exp_bound_quadratic (m := n) hρ0 hξ0 hn hS hT
      (Nat.cast_nonneg (α := ℝ) (resEv 𝓗 G' ξ 𝓥 (Sum.inr (Sum.inr (Sum.inr ⟨(S, T), hd, hS, hT⟩)))).card)
      hcardN (le_refl _)
    rw [hB2, htol]
    have hdiv : ξ * (S.card : ℝ) * (T.card : ℝ) / 2 / 3 = ξ * (S.card : ℝ) * (T.card : ℝ) / 6 := by
      ring
    rw [hdiv]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hexp))
      (by norm_num : (0 : ℝ) ≤ 2)
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : (∑ v : Fin n, 2 * Real.exp (-((resTol ξ 𝓥 (Sum.inl v)) ^ 2) /
        (2 * (ρ * ((resEv 𝓗 G' ξ 𝓥 (Sum.inl v)).card : ℝ) + resTol ξ 𝓥 (Sum.inl v) / 3))))
      ≤ (n : ℝ) * B1 := by
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin n))
      (fun v => 2 * Real.exp (-((resTol ξ 𝓥 (Sum.inl v)) ^ 2) /
        (2 * (ρ * ((resEv 𝓗 G' ξ 𝓥 (Sum.inl v)).card : ℝ) + resTol ξ 𝓥 (Sum.inl v) / 3))))
      B1 (fun v _ => hstar v)
    simpa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  have h2 : (∑ p : Fin n × 𝓥, 2 * Real.exp (-((resTol ξ 𝓥 (Sum.inr (Sum.inl p))) ^ 2) /
        (2 * (ρ * ((resEv 𝓗 G' ξ 𝓥 (Sum.inr (Sum.inl p))).card : ℝ)
          + resTol ξ 𝓥 (Sum.inr (Sum.inl p)) / 3)))) ≤ ((n : ℝ) * (𝓥.card : ℝ)) * B1 := by
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin n × 𝓥))
      (fun p => 2 * Real.exp (-((resTol ξ 𝓥 (Sum.inr (Sum.inl p))) ^ 2) /
        (2 * (ρ * ((resEv 𝓗 G' ξ 𝓥 (Sum.inr (Sum.inl p))).card : ℝ)
          + resTol ξ 𝓥 (Sum.inr (Sum.inl p)) / 3)))) B1 (fun p _ => hpair p)
    simpa [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, nsmul_eq_mul]
      using this
  have h3 : (∑ p : Fin n × 𝓥, 2 * Real.exp (-((resTol ξ 𝓥 (Sum.inr (Sum.inr (Sum.inl p)))) ^ 2) /
        (2 * (ρ * ((resEv 𝓗 G' ξ 𝓥 (Sum.inr (Sum.inr (Sum.inl p)))).card : ℝ)
          + resTol ξ 𝓥 (Sum.inr (Sum.inr (Sum.inl p))) / 3)))) ≤ ((n : ℝ) * (𝓥.card : ℝ)) * B1 := by
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin n × 𝓥))
      (fun p => 2 * Real.exp (-((resTol ξ 𝓥 (Sum.inr (Sum.inr (Sum.inl p)))) ^ 2) /
        (2 * (ρ * ((resEv 𝓗 G' ξ 𝓥 (Sum.inr (Sum.inr (Sum.inl p)))).card : ℝ)
          + resTol ξ 𝓥 (Sum.inr (Sum.inr (Sum.inl p))) / 3)))) B1 (fun p _ => hpair2 p)
    simpa [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, nsmul_eq_mul]
      using this
  have h4 : (∑ p : {p : Finset (Fin n) × Finset (Fin n) //
        Disjoint p.1 p.2 ∧ ξ * (n : ℝ) ≤ (p.1.card : ℝ) ∧ ξ * (n : ℝ) ≤ (p.2.card : ℝ)},
      2 * Real.exp (-((resTol ξ 𝓥 (Sum.inr (Sum.inr (Sum.inr p)))) ^ 2) /
        (2 * (ρ * ((resEv 𝓗 G' ξ 𝓥 (Sum.inr (Sum.inr (Sum.inr p)))).card : ℝ)
          + resTol ξ 𝓥 (Sum.inr (Sum.inr (Sum.inr p))) / 3))))
      ≤ ((4 : ℝ) ^ n) * B2 := by
    have hle : (Fintype.card {p : Finset (Fin n) × Finset (Fin n) //
          Disjoint p.1 p.2 ∧ ξ * (n : ℝ) ≤ (p.1.card : ℝ) ∧ ξ * (n : ℝ) ≤ (p.2.card : ℝ)} : ℝ)
        ≤ (4 : ℝ) ^ n := by
      have h1 := Fintype.card_subtype_le (fun p : Finset (Fin n) × Finset (Fin n) =>
        Disjoint p.1 p.2 ∧ ξ * (n : ℝ) ≤ (p.1.card : ℝ) ∧ ξ * (n : ℝ) ≤ (p.2.card : ℝ))
      rw [card_pairs_le] at h1
      exact_mod_cast h1
    have := Finset.sum_le_card_nsmul
      (Finset.univ : Finset {p : Finset (Fin n) × Finset (Fin n) //
          Disjoint p.1 p.2 ∧ ξ * (n : ℝ) ≤ (p.1.card : ℝ) ∧ ξ * (n : ℝ) ≤ (p.2.card : ℝ)})
      (fun p => 2 * Real.exp (-((resTol ξ 𝓥 (Sum.inr (Sum.inr (Sum.inr p)))) ^ 2) /
        (2 * (ρ * ((resEv 𝓗 G' ξ 𝓥 (Sum.inr (Sum.inr (Sum.inr p)))).card : ℝ)
          + resTol ξ 𝓥 (Sum.inr (Sum.inr (Sum.inr p))) / 3)))) B2 (fun p _ => hcross p)
    have h2' : (Fintype.card {p : Finset (Fin n) × Finset (Fin n) //
          Disjoint p.1 p.2 ∧ ξ * (n : ℝ) ≤ (p.1.card : ℝ) ∧ ξ * (n : ℝ) ≤ (p.2.card : ℝ)} : ℝ) * B2
        ≤ ((4 : ℝ) ^ n) * B2 := mul_le_mul_of_nonneg_right hle (by positivity)
    simp only [Finset.card_univ, nsmul_eq_mul] at this
    linarith [this, h2']
  linarith [h1, h2, h3, h4, hnum]

/-- **Proposition 11.1 (`prop:pseudo_reservoir`), structural form.**  Given the
union-bound inequality, the random reservoir exists: a set `R ⊆ E(G)` of
2-edges whose degree sequence is `ρ d_G ± ξn`, and whose restriction to `G'`
is a `(ρ,ξ,ξ,ε)`-absorber for `𝓥` (i.e. `(ρ,ξ,G')`-typical and upper
`(ρ,ξ,G')`-regular), and additionally lower `(ρ,ξ,G')`-regular. -/
theorem exists_pseudoReservoir (𝓗 : Hypergraph (Fin n)) (hlin : 𝓗.IsLinear)
    {G' : Hypergraph (Fin n)} (hG' : G' ⊆ 𝓗.pow2)
    (𝓥 : Finset (Set (Fin n))) {ρ ξ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hξ0 : 0 < ξ)
    (hn : 1 ≤ n)
    (hnum : (2 * (n : ℝ) + 4 * (n : ℝ) * (𝓥.card : ℝ)) *
          Real.exp (-(ξ ^ 2 / (2 * (ρ + ξ / 3)) * (n : ℝ))) +
        2 * ((4 : ℝ) ^ n) * Real.exp (-(ξ ^ 4 / (4 * (2 * ρ + ξ / 3)) * (n : ℝ) ^ 2)) < 1) :
    ∃ R : Hypergraph (Fin n), R ⊆ 𝓗.pow2 ∧
      IsAbsorber G' (R ∩ G') (𝓥 : Set (Set (Fin n))) ρ ξ ξ ∧
      LowerRegular G' (R ∩ G') ρ ξ ∧
      (∀ v : Fin n, |((degAt R v : ℝ) - ρ * (degAt 𝓗.pow2 v : ℝ))| ≤ ξ * (n : ℝ)) := by
  obtain ⟨R, hRsub, hdeg, htyp, hup, hlow⟩ :=
    exists_reservoir_core 𝓗 hlin hG' 𝓥 hρ0 hρ1 hξ0
      (reservoir_sum_bound 𝓗 hG' 𝓥 hρ0 hξ0 hn hnum)
  exact ⟨R, hRsub, ⟨fun _ he => he.2, htyp, hup⟩, hlow, hdeg⟩

/-- **Proposition 11.1 (`prop:pseudo_reservoir`).**  For `0 < 1/n₀ ≪ ξ, ε, ρ < 1`
and `n ≥ n₀`, and a family `𝓥` of at most `n^{log n}` subsets of the vertex set,
there is a set `R ⊆ E(G)` of 2-edges with `(ρ,ξ,ε,𝓥)`-pseudorandom reservoir
properties: `d_R(v) = ρ d_G(v) ± ξn` for every vertex, and `R ∩ E(G')` is a
`(ρ,ξ,ξ,ε)`-absorber for `𝓥` that is also lower `(ρ,ξ,G')`-regular. -/
theorem exists_pseudoReservoir_eventually {ρ ξ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hξ0 : 0 < ξ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 ≤ n → ∀ (𝓗 : Hypergraph (Fin n)), 𝓗.IsLinear →
      ∀ (G' : Hypergraph (Fin n)), G' ⊆ 𝓗.pow2 → ∀ (𝓥 : Finset (Set (Fin n))),
        (𝓥.card : ℝ) ≤ (n : ℝ) ^ Real.log n →
        ∃ R : Hypergraph (Fin n), R ⊆ 𝓗.pow2 ∧
          IsAbsorber G' (R ∩ G') (𝓥 : Set (Set (Fin n))) ρ ξ ξ ∧
          LowerRegular G' (R ∩ G') ρ ξ ∧
          (∀ v : Fin n, |((degAt R v : ℝ) - ρ * (degAt 𝓗.pow2 v : ℝ))| ≤ ξ * (n : ℝ)) := by
  obtain ⟨N, hN⟩ := Commons.Analysis.Real.reservoir_union_bound
    (ξ ^ 2 / (2 * (ρ + ξ / 3))) (ξ ^ 4 / (4 * (2 * ρ + ξ / 3)))
    (by positivity) (by positivity)
  exact ⟨N, fun n hn hn1 𝓗 hlin G' hG' 𝓥 hV =>
    exists_pseudoReservoir 𝓗 hlin hG' 𝓥 hρ0 hρ1 hξ0 hn1
      (hN n hn (𝓥.card : ℝ) (Nat.cast_nonneg _) hV)⟩

end
end ErdosFaberLovaszConjecture
