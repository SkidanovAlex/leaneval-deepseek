import Submission.Work.ConeSwitch.MathlibNoHG

namespace Work.Deep.Kahn

open scoped BigOperators

/-- A sub-finset of prescribed cardinality: for `t ≤ #Q` there is `T ⊆ Q` with `#T = t`. -/
private theorem exists_subset_card {α : Type*} [DecidableEq α] (Q : Finset α) :
    ∀ t : ℕ, t ≤ Q.card → ∃ T : Finset α, T ⊆ Q ∧ T.card = t := by
  induction Q using Finset.induction_on with
  | empty =>
      intro t ht
      rw [Finset.card_empty] at ht
      exact ⟨∅, Finset.empty_subset _, by rw [Finset.card_empty]; omega⟩
  | insert a s ha ih =>
      intro t ht
      rw [Finset.card_insert_of_notMem ha] at ht
      rcases Nat.lt_or_ge t (s.card + 1) with hlt | hge
      · obtain ⟨T, hT, hTc⟩ := ih t (Nat.lt_succ_iff.mp hlt)
        exact ⟨T, fun x hx => Finset.mem_insert_of_mem (hT hx), hTc⟩
      · obtain ⟨T, hT, hTc⟩ := ih s.card le_rfl
        refine ⟨insert a T, ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.mp hx with hx' | hx'
          · exact Finset.mem_insert.mpr (Or.inl hx')
          · exact Finset.mem_insert_of_mem (hT hx')
        · rw [Finset.card_insert_of_notMem (fun hmem : a ∈ T => ha (hT hmem)), hTc]
          omega

/-- A finset sandwiched between `S ⊆ P`, of prescribed cardinality. -/
private theorem exists_between {α : Type*} [DecidableEq α] {S P : Finset α} (hSP : S ⊆ P)
    {n : ℕ} (h1 : S.card ≤ n) (h2 : n ≤ P.card) :
    ∃ G : Finset α, S ⊆ G ∧ G ⊆ P ∧ G.card = n := by
  have hcard : n - S.card ≤ (P \ S).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hSP]
    omega
  obtain ⟨T, hTsub, hTcard⟩ := exists_subset_card (P \ S) (n - S.card) hcard
  refine ⟨S ∪ T, Finset.subset_union_left, ?_, ?_⟩
  · exact Finset.union_subset hSP (hTsub.trans Finset.sdiff_subset)
  · have hd : Disjoint S T := Finset.disjoint_of_subset_right hTsub Finset.disjoint_sdiff
    rw [Finset.card_union_of_disjoint hd, hTcard]
    omega

/-- The inductive engine: the multiplicity statement phrased with sums. -/
private theorem decomp (m : ℕ) : ∀ (c Λ : ℕ) (δ : Fin c → ℕ),
    (∑ γ : Fin c, δ γ) = Λ * m → (∀ γ : Fin c, δ γ ≤ m) →
    ∃ Γ : Fin m → Finset (Fin c),
      (∀ k : Fin m, (Γ k).card = Λ) ∧
      (∀ γ : Fin c, ∑ k : Fin m, (if γ ∈ Γ k then 1 else 0) = δ γ) := by
  induction m with
  | zero =>
      intro c Λ δ hsum _hmax
      have hsum0 : ∑ γ : Fin c, δ γ = 0 := by rw [hsum, Nat.mul_zero]
      have hδ0 : ∀ γ : Fin c, δ γ = 0 := fun γ =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le (δ i))).mp hsum0 γ
          (Finset.mem_univ γ)
      refine ⟨fun _ => ∅, fun k => Fin.elim0 k, fun γ => ?_⟩
      rw [Fin.sum_univ_zero]
      exact (hδ0 γ).symm
  | succ m ih =>
      intro c Λ δ hsum hmax
      have hmpos : 0 < m + 1 := Nat.succ_pos m
      have hScard : (Finset.univ.filter (fun γ : Fin c => δ γ = m + 1)).card ≤ Λ := by
        have h1 : ∑ γ ∈ Finset.univ.filter (fun γ : Fin c => δ γ = m + 1), δ γ
            = (Finset.univ.filter (fun γ : Fin c => δ γ = m + 1)).card * (m + 1) := by
          calc ∑ γ ∈ Finset.univ.filter (fun γ : Fin c => δ γ = m + 1), δ γ
              = ∑ γ ∈ Finset.univ.filter (fun γ : Fin c => δ γ = m + 1), (m + 1) :=
                Finset.sum_congr rfl (fun γ hγ => (Finset.mem_filter.mp hγ).2)
            _ = (Finset.univ.filter (fun γ : Fin c => δ γ = m + 1)).card * (m + 1) := by
                simp [Finset.sum_const]
        have h2 : ∑ γ ∈ Finset.univ.filter (fun γ : Fin c => δ γ = m + 1), δ γ
            ≤ Λ * (m + 1) := by
          rw [← hsum]
          exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        rw [h1] at h2
        exact Nat.le_of_mul_le_mul_right h2 hmpos
      have hPcard : Λ ≤ (Finset.univ.filter (fun γ : Fin c => 0 < δ γ)).card := by
        have hsplit : ∑ γ : Fin c, δ γ
            = ∑ γ ∈ Finset.univ.filter (fun γ : Fin c => 0 < δ γ), δ γ := by
          have hzero : ∑ γ ∈ Finset.univ.filter (fun γ : Fin c => ¬ 0 < δ γ), δ γ = 0 :=
            Finset.sum_eq_zero (fun γ hγ => by
              have := (Finset.mem_filter.mp hγ).2
              omega)
          calc ∑ γ : Fin c, δ γ
              = ∑ γ ∈ Finset.univ.filter (fun γ : Fin c => 0 < δ γ), δ γ
                + ∑ γ ∈ Finset.univ.filter (fun γ : Fin c => ¬ 0 < δ γ), δ γ :=
                (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
                  (p := fun γ : Fin c => 0 < δ γ) (f := fun γ : Fin c => δ γ)).symm
            _ = ∑ γ ∈ Finset.univ.filter (fun γ : Fin c => 0 < δ γ), δ γ := by
                rw [hzero, add_zero]
        have hle : ∑ γ ∈ Finset.univ.filter (fun γ : Fin c => 0 < δ γ), δ γ
            ≤ ∑ γ ∈ Finset.univ.filter (fun γ : Fin c => 0 < δ γ), (m + 1) :=
          Finset.sum_le_sum (fun γ _ => hmax γ)
        have h3 : Λ * (m + 1) ≤ (Finset.univ.filter (fun γ : Fin c => 0 < δ γ)).card * (m + 1) := by
          calc Λ * (m + 1) = ∑ γ : Fin c, δ γ := hsum.symm
            _ = ∑ γ ∈ Finset.univ.filter (fun γ : Fin c => 0 < δ γ), δ γ := hsplit
            _ ≤ ∑ γ ∈ Finset.univ.filter (fun γ : Fin c => 0 < δ γ), (m + 1) := hle
            _ = (Finset.univ.filter (fun γ : Fin c => 0 < δ γ)).card * (m + 1) := by
                simp [Finset.sum_const]
        exact Nat.le_of_mul_le_mul_right h3 hmpos
      have hSP : Finset.univ.filter (fun γ : Fin c => δ γ = m + 1)
          ⊆ Finset.univ.filter (fun γ : Fin c => 0 < δ γ) := by
        intro γ hγ
        obtain ⟨-, hγ⟩ := Finset.mem_filter.mp hγ
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ γ, by omega⟩
      obtain ⟨Γ0, hSΓ0, hΓ0P, hΓ0card⟩ := exists_between hSP hScard hPcard
      have hwsum : ∑ γ : Fin c, (if γ ∈ Γ0 then 1 else 0) = Λ := by
        have hfil : Finset.univ.filter (fun γ : Fin c => γ ∈ Γ0) = Γ0 :=
          Finset.ext (fun γ => by simp)
        rw [← Finset.sum_filter, hfil, ← Finset.card_eq_sum_ones]
        exact hΓ0card
      have hδw : ∀ γ : Fin c,
          (δ γ - (if γ ∈ Γ0 then 1 else 0)) + (if γ ∈ Γ0 then 1 else 0) = δ γ := by
        intro γ
        by_cases hγ : γ ∈ Γ0
        · have hpos : 0 < δ γ := (Finset.mem_filter.mp (hΓ0P hγ)).2
          rw [if_pos hγ]
          omega
        · rw [if_neg hγ]
          omega
      have hsum' : ∑ γ : Fin c, (δ γ - (if γ ∈ Γ0 then 1 else 0)) = Λ * m := by
        have h1 : (∑ γ : Fin c, (δ γ - (if γ ∈ Γ0 then 1 else 0)))
            + ∑ γ : Fin c, (if γ ∈ Γ0 then 1 else 0) = ∑ γ : Fin c, δ γ := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun γ _ => hδw γ)
        rw [hwsum, hsum] at h1
        rw [show Λ * (m + 1) = Λ * m + Λ by rw [Nat.mul_succ]] at h1
        omega
      have hmax' : ∀ γ : Fin c, δ γ - (if γ ∈ Γ0 then 1 else 0) ≤ m := by
        intro γ
        by_cases hγ : γ ∈ Γ0
        · have hpos : 0 < δ γ := (Finset.mem_filter.mp (hΓ0P hγ)).2
          rw [if_pos hγ]
          have := hmax γ
          omega
        · have hne : δ γ ≠ m + 1 := by
            intro hcon
            exact hγ (hSΓ0 (Finset.mem_filter.mpr ⟨Finset.mem_univ γ, hcon⟩))
          rw [if_neg hγ]
          have := hmax γ
          omega
      obtain ⟨Γ', hΓ'card, hΓ'mult⟩ :=
        ih c Λ (fun γ => δ γ - (if γ ∈ Γ0 then 1 else 0)) hsum' hmax'
      refine ⟨Fin.cons (α := fun _ => Finset (Fin c)) Γ0 Γ', ?_, ?_⟩
      · intro k
        rcases Fin.eq_zero_or_eq_succ k with hk | ⟨j, hk⟩
        · rw [hk, Fin.cons_zero]
          exact hΓ0card
        · rw [hk, Fin.cons_succ]
          exact hΓ'card j
      · intro γ
        have hsplit : (∑ k : Fin (m + 1),
              (if γ ∈ Fin.cons (α := fun _ => Finset (Fin c)) Γ0 Γ' k then 1 else 0))
            = (if γ ∈ Γ0 then 1 else 0) + ∑ k : Fin m, (if γ ∈ Γ' k then 1 else 0) := by
          rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hsplit, hΓ'mult γ, add_comm]
        exact hδw γ

/-- **Multiset decomposition into `Λ`-sets.**  A function `δ : Fin c → ℕ` with total
`Λ * m` and pointwise bound `δ γ ≤ m` can be written as the multiplicity function of a
family of `m` sets of size `Λ`: there are `Γ k ⊆ Fin c` with `#(Γ k) = Λ` for every `k`,
and every colour `γ` lies in exactly `δ γ` of the `Γ k`. -/
theorem listDecomp (c Λ m : ℕ) (δ : Fin c → ℕ)
    (hsum : ∑ γ : Fin c, δ γ = Λ * m) (hmax : ∀ γ : Fin c, δ γ ≤ m) :
    ∃ Γ : Fin m → Finset (Fin c),
      (∀ k : Fin m, (Γ k).card = Λ) ∧
      (∀ γ : Fin c, (Finset.univ.filter (fun k : Fin m => γ ∈ Γ k)).card = δ γ) := by
  obtain ⟨Γ, h1, h2⟩ := decomp m c Λ δ hsum hmax
  refine ⟨Γ, h1, fun γ => ?_⟩
  have hfil : (Finset.univ.filter (fun k : Fin m => γ ∈ Γ k)).card
      = ∑ k : Fin m, (if γ ∈ Γ k then 1 else 0) := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hfil]
  exact h2 γ

end Work.Deep.Kahn
