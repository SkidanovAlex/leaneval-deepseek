import Mathlib
import Submission.Work.EQ.FanTri.fan_split_defs

/-!
# Counting the blocks of a gap/trip decomposition

A word `u` decomposed into gap lengths `a` and trips `σ` (`DecSpec u a σ`) satisfies
`σ.length ≤ VisU u` and `∑ |σᵢ| ≤ 2 * VisU u`.

The walk of `u` never leaves `0` along the gaps `true^{aᵢ}` and stays non-zero strictly inside
each trip `σᵢ`; hence every trip contributes at least one position, and all but its last
position, to the non-zero positions counted by `VisU u`.
-/

namespace Work.EQ.FanTri

open Work.EQ

/-- `VisU`, written as a count over `Finset.range` (positions `j + 1` for `j < |u|`). -/
lemma VisU_eq_range (u : List Bool) :
    VisU u = ((Finset.range u.length).filter (fun j => wstate u (j + 1) ≠ 0)).card := by
  unfold VisU
  rw [show Finset.Icc 1 u.length = (Finset.range u.length).image Nat.succ from by
    ext t; rw [Finset.mem_Icc, Finset.mem_image]; simp only [Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨t - 1, by omega, by omega⟩
    · rintro ⟨j, hj, hjt⟩; subst hjt; omega]
  rw [Finset.filter_image, Finset.card_image_of_injective _ Nat.succ_injective]

/-- Inside a prefix `p` of `p ++ q` the walk states agree. -/
lemma wstate_append_le (p q : List Bool) {t : ℕ} (h : t ≤ p.length) :
    wstate (p ++ q) t = wstate p t := by
  unfold wstate
  rw [List.take_append_of_le_length h]

/-- Past a prefix `p` that returns to `0`, the walk of `p ++ q` is the walk of `q`. -/
lemma wstate_append_shift (p q : List Bool) (h0 : stAux p 0 = 0) (s : ℕ) :
    wstate (p ++ q) (p.length + s) = wstate q s := by
  rw [wstate_append, h0]; rfl

/-- If `p` returns to `0`, then `VisU` is additive over `p ++ q`. -/
lemma VisU_append (p q : List Bool) (h0 : stAux p 0 = 0) :
    VisU (p ++ q) = VisU p + VisU q := by
  rw [VisU_eq_range (p ++ q), VisU_eq_range p, VisU_eq_range q, List.length_append,
      Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [wstate_append_le p q (by omega)]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [show p.length + j + 1 = p.length + (j + 1) from by omega,
        wstate_append_shift p q h0 (j + 1)]

/-- `VisU` is monotone under appending a suffix. -/
lemma VisU_le_append_left (p q : List Bool) : VisU p ≤ VisU (p ++ q) := by
  rw [VisU_eq_range p, VisU_eq_range (p ++ q)]
  apply Finset.card_le_card
  intro j hj
  rw [Finset.mem_filter] at hj ⊢
  obtain ⟨hj1, hj2⟩ := hj
  rw [Finset.mem_range] at hj1 ⊢
  refine ⟨by simp only [List.length_append]; omega, ?_⟩
  rw [wstate_append_le p q (by omega)]
  exact hj2

/-- **Lower bound for `asm`.** If the gaps and trips are assembled with every non-final trip
returning to `0`, then `VisU` of the assembled word dominates the sum of the `VisU` of its
trips (the gaps contribute nothing). -/
lemma VisU_asm_ge (a : List ℕ) (σ : List (List Bool))
    (hlen : a.length = σ.length + 1)
    (hclosed : ∀ (i : ℕ) (τ : List Bool), σ[i]? = some τ → i + 1 < σ.length →
        stAux τ 0 = 0) :
    (σ.map VisU).sum ≤ VisU (asm a σ) := by
  induction σ generalizing a with
  | nil =>
      rcases a with _ | ⟨g, gs⟩
      · simp only [List.length_nil] at hlen; omega
      · have hgs : gs = [] := by
          have h : gs.length = 0 := by
            simp only [List.length_cons, List.length_nil, Nat.zero_add] at hlen
            omega
          exact List.length_eq_zero_iff.mp h
        subst hgs
        simp [asm, VisU_replicate_true]
  | cons τ ts ih =>
      rcases a with _ | ⟨g, gs⟩
      · simp only [List.length_cons, List.length_nil] at hlen; omega
      · have hlen_gs : gs.length = ts.length + 1 := by
          simp only [List.length_cons] at hlen; omega
        by_cases hts : ts = []
        · subst hts
          have hgs_len : gs.length = 1 := by
            simp only [List.length_nil, Nat.zero_add] at hlen_gs; omega
          rcases gs with _ | ⟨g', gs'⟩
          · simp only [List.length_nil] at hgs_len; omega
          · have hgs' : gs' = [] := by
              have h : gs'.length = 0 := by
                simp only [List.length_cons] at hgs_len
                omega
              exact List.length_eq_zero_iff.mp h
            subst hgs'
            have h0 : stAux (List.replicate g true) 0 = 0 := by
              rw [stAux_replicate_true]; omega
            calc ((τ :: []).map VisU).sum
                = VisU τ := by simp
              _ ≤ VisU (τ ++ List.replicate g' true) := VisU_le_append_left τ _
              _ ≤ VisU (List.replicate g true ++ (τ ++ List.replicate g' true)) := by
                    rw [VisU_append _ _ h0, VisU_replicate_true, zero_add]
              _ = VisU (asm (g :: g' :: []) (τ :: [])) := by simp [asm]
        · have hτ0 : stAux τ 0 = 0 := by
            apply hclosed 0 τ
            · simp
            · have : 0 < ts.length := List.length_pos_iff.mpr hts
              simp only [List.length_cons]; omega
          have hclosed_ts : ∀ (i : ℕ) (τ' : List Bool), ts[i]? = some τ' →
              i + 1 < ts.length → stAux τ' 0 = 0 := by
            intro i τ' hi hi'
            apply hclosed (i + 1) τ'
            · rw [List.getElem?_cons_succ]; exact hi
            · simp only [List.length_cons]; omega
          have key := ih gs hlen_gs hclosed_ts
          have h0 : stAux (List.replicate g true) 0 = 0 := by
            rw [stAux_replicate_true]; omega
          calc ((τ :: ts).map VisU).sum
              = VisU τ + (ts.map VisU).sum := by simp
            _ ≤ VisU τ + VisU (asm gs ts) := Nat.add_le_add_left key (VisU τ)
            _ = VisU (τ ++ asm gs ts) := by rw [VisU_append τ (asm gs ts) hτ0]
            _ ≤ VisU (List.replicate g true ++ (τ ++ asm gs ts)) := by
                  rw [VisU_append _ _ h0, VisU_replicate_true, zero_add]
            _ = VisU (asm (g :: gs) (τ :: ts)) := by
                  rw [show asm (g :: gs) (τ :: ts)
                        = List.replicate g true ++ (τ ++ asm gs ts) from by
                        simp [asm, List.append_assoc]]

/-- A trip that leaves `0` at its first step contributes at least one non-zero position. -/
lemma VisU_trip_ge_one {τ : List Bool} (h : wstate τ 1 ≠ 0) : 1 ≤ VisU τ := by
  rw [VisU_eq_range]
  have hne : τ ≠ [] := by rintro rfl; simp [wstate] at h
  have hmem : 0 ∈ (Finset.range τ.length).filter (fun j => wstate τ (j + 1) ≠ 0) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨List.length_pos_iff.mpr hne, by simpa using h⟩
  exact Finset.card_pos.mpr ⟨0, hmem⟩

/-- A trip that is non-zero at every strictly interior position contributes all of them. -/
lemma VisU_trip_ge_pred {τ : List Bool}
    (h : ∀ t : ℕ, 1 ≤ t → t < τ.length → wstate τ t ≠ 0) :
    τ.length - 1 ≤ VisU τ := by
  rw [VisU_eq_range, ← Finset.card_range (τ.length - 1)]
  apply Finset.card_le_card
  intro j hj
  rw [Finset.mem_range] at hj
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, h (j + 1) (by omega) (by omega)⟩

/-- **Counts of a gap/trip decomposition.** A word `u` with decomposition `DecSpec u a σ` has
at most `VisU u` trips, and the total length of the trips is at most `2 * VisU u`. -/
theorem dec_counts (u : List Bool) (a : List ℕ) (σ : List (List Bool))
    (h : Work.EQ.FanTri.DecSpec u a σ) :
    σ.length ≤ Work.EQ.FanTri.VisU u ∧
      (σ.map List.length).sum ≤ 2 * Work.EQ.FanTri.VisU u := by
  obtain ⟨hlen, hu, hA, hB, hC, hD⟩ := h
  have hclosed : ∀ (i : ℕ) (τ : List Bool), σ[i]? = some τ → i + 1 < σ.length →
      stAux τ 0 = 0 := by
    intro i τ hi hi'
    have hh := hC i τ hi hi'
    rwa [wstate_of_le (u := τ) (t := τ.length) le_rfl] at hh
  have hsum : (σ.map VisU).sum ≤ VisU u := by
    have hh := VisU_asm_ge a σ hlen hclosed
    rwa [← hu] at hh
  have hone : ∀ τ ∈ σ, 1 ≤ VisU τ := by
    intro τ hτ
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hτ
    exact VisU_trip_ge_one (hA i τ hi)
  have hpred : ∀ τ ∈ σ, τ.length - 1 ≤ VisU τ := by
    intro τ hτ
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hτ
    exact VisU_trip_ge_pred (fun t h1 h2 => hB i τ hi t h1 h2)
  have hlen1 : ∀ τ ∈ σ, 1 ≤ τ.length := by
    intro τ hτ
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hτ
    have hne : τ ≠ [] := by
      rintro rfl
      exact hA i [] hi (by simp [wstate])
    exact List.length_pos_iff.mpr hne
  refine ⟨?_, ?_⟩
  · calc σ.length = (σ.map (fun _ => 1)).sum := by simp
      _ ≤ (σ.map VisU).sum := List.sum_le_sum hone
      _ ≤ VisU u := hsum
  · have hone' : σ.length ≤ (σ.map VisU).sum := by
      simpa using (List.sum_le_sum hone : (σ.map (fun _ => (1:ℕ))).sum ≤ (σ.map VisU).sum)
    have hA1 : (σ.map List.length).sum
        = (σ.map (fun τ => τ.length - 1)).sum + σ.length := by
      have hmap : σ.map List.length = σ.map (fun τ => (τ.length - 1) + 1) :=
        List.map_congr_left (fun τ hτ => (Nat.sub_add_cancel (hlen1 τ hτ)).symm)
      rw [hmap, List.sum_map_add]
      simp
    rw [hA1]
    calc (σ.map (fun τ => τ.length - 1)).sum + σ.length
        ≤ (σ.map VisU).sum + (σ.map VisU).sum :=
          Nat.add_le_add (List.sum_le_sum hpred) hone'
      _ ≤ VisU u + VisU u := Nat.add_le_add hsum hsum
      _ = 2 * VisU u := by ring

end Work.EQ.FanTri
