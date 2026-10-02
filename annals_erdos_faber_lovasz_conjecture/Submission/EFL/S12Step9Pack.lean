import Submission.EFL.S12Inst5

/-!
# §12, Step 9, packaged: the `m(w)`-bounds for `𝓜_prev`

`Submission/EFL/S12Step9.lean` contains the paper's Step 9 in the form of the
lemmas `s12_mbound` (the `m(w)`-bounds `(eqn:mbound_1)`--`(eqn:mbound_3)`) and
`s12_uc` (the degree bounds UC2--UC4), stated for an arbitrary family
`M : ι → Set (Set (Fin n))` of families of vertex sets.

Here we instantiate `s12_mbound` with the actual `𝓜_prev^*` of §12
(`prevFam` of `S12Mprev.lean`), extended by the whole vertex set outside
`C_prev` so that it is indexed by all of `Fin n`: for `c ∉ C_prev` nothing is
missed, so the counting sets `{i : w ∉ famVert (𝓜_prev^*_i)}` are supported on
`C_prev` and can be compared with the `Finset.filter` counts of
`S12Mprev.lean` (`sdiff_famVert_prevFam_subset_S1`, `ncard_miss_le_one`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-! ## `𝓜_prev^*` extended to all colours -/

/-- `𝓜_prev^*` of §12, extended by the whole vertex set outside
`C_prev = C_med ∪ C_diff ∪ C_huge ∪ C_main ∪ C_buff`, so that it is a family
indexed by all of `Fin n` which misses nothing outside `C_prev`. -/
def prevFamFull {𝓗 : Hypergraph (Fin n)} (MD HM MM MB : Fin n → Set 𝓗)
    (Cmed Cdiff Chuge Cmain Cbuff : Finset (Fin n)) (c : Fin n) : Set (Set (Fin n)) :=
  if c ∈ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff then
    prevFam MD HM MM MB Cdiff Cmain Cbuff c
  else Set.univ

/-- The set of colours of `𝓜_prev` whose matching misses `w`. -/
def prevMiss {𝓗 : Hypergraph (Fin n)} (MD HM MM MB : Fin n → Set 𝓗)
    (Cmed Cdiff Chuge Cmain Cbuff : Finset (Fin n)) (w : Fin n) : Set (Fin n) :=
  {i | w ∉ famVert (prevFamFull MD HM MM MB Cmed Cdiff Chuge Cmain Cbuff i)}

theorem prevFamFull_of_mem {𝓗 : Hypergraph (Fin n)} {MD HM MM MB : Fin n → Set 𝓗}
    {Cmed Cdiff Chuge Cmain Cbuff : Finset (Fin n)} {c : Fin n}
    (hc : c ∈ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff) :
    prevFamFull MD HM MM MB Cmed Cdiff Chuge Cmain Cbuff c
      = prevFam MD HM MM MB Cdiff Cmain Cbuff c := by
  rw [prevFamFull, if_pos hc]

theorem prevFamFull_of_notMem {𝓗 : Hypergraph (Fin n)} {MD HM MM MB : Fin n → Set 𝓗}
    {Cmed Cdiff Chuge Cmain Cbuff : Finset (Fin n)} {c : Fin n}
    (hc : c ∉ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff) :
    prevFamFull MD HM MM MB Cmed Cdiff Chuge Cmain Cbuff c = Set.univ := by
  rw [prevFamFull, if_neg hc]

theorem famVert_prevFamFull_of_notMem {𝓗 : Hypergraph (Fin n)} {MD HM MM MB : Fin n → Set 𝓗}
    {Cmed Cdiff Chuge Cmain Cbuff : Finset (Fin n)} {c : Fin n}
    (hc : c ∉ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff) :
    famVert (prevFamFull MD HM MM MB Cmed Cdiff Chuge Cmain Cbuff c) =
      (Set.univ : Set (Fin n)) := by
  rw [prevFamFull_of_notMem hc]
  ext v
  rw [famVert, Set.mem_sUnion]
  simp only [Set.mem_univ, true_and]
  exact ⟨fun _ => trivial, fun _ => ⟨Set.univ, trivial⟩⟩

theorem mem_famVert_prevFamFull_of_notMem {𝓗 : Hypergraph (Fin n)}
    {MD HM MM MB : Fin n → Set 𝓗} {Cmed Cdiff Chuge Cmain Cbuff : Finset (Fin n)}
    {c : Fin n} (hc : c ∉ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff) (w : Fin n) :
    w ∈ famVert (prevFamFull MD HM MM MB Cmed Cdiff Chuge Cmain Cbuff c) := by
  rw [famVert_prevFamFull_of_notMem hc]
  trivial

/-! ## Membership lemmas for the five colour sets -/

/-- A colour of `C_prev` which is not in `C_diff` lies in one of the four other
classes. -/
theorem mem_of_mem_prev_notMem_Cdiff {Cmed Cdiff Chuge Cmain Cbuff : Finset (Fin n)}
    {c : Fin n} (hc : c ∈ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff) (hd : c ∉ Cdiff) :
    c ∈ Cmed ∪ Chuge ∪ Cmain ∪ Cbuff := by
  rcases Finset.mem_union.mp hc with h1 | h1
  · rcases Finset.mem_union.mp h1 with h2 | h2
    · -- `(Cmed ∪ Cdiff) ∪ Chuge`
      rcases Finset.mem_union.mp h2 with h3 | h3
      · -- `Cmed ∪ Cdiff`
        rcases Finset.mem_union.mp h3 with h4 | h4
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ h4))
        · exact absurd h4 hd
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ h3))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ h2)
  · exact Finset.mem_union_right _ h1

/-- A colour of `C_prev ∖ (C_diff ∪ C_main ∪ C_buff)` lies in
`C_med ∪ C_huge`. -/
theorem mem_med_huge_of_mem_prev {Cmed Cdiff Chuge Cmain Cbuff : Finset (Fin n)}
    {c : Fin n} (hc : c ∈ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff)
    (hd : c ∉ Cdiff) (hm : c ∉ Cmain) (hb : c ∉ Cbuff) :
    c ∈ Cmed ∪ Chuge := by
  have h := mem_of_mem_prev_notMem_Cdiff hc hd
  rcases Finset.mem_union.mp h with h1 | h1
  · rcases Finset.mem_union.mp h1 with h2 | h2
    · -- `Cmed ∪ Chuge`
      rcases Finset.mem_union.mp h2 with h3 | h3
      · exact Finset.mem_union_left _ h3
      · exact Finset.mem_union_right _ h3
    · exact absurd h2 hm
  · exact absurd h1 hb

/-- Membership of a colour class in `C_prev = C_med ∪ C_diff ∪ C_huge ∪
C_main ∪ C_buff`. -/
theorem mem_prev_of_mem_Cmed {Cmed Cdiff Chuge Cmain Cbuff : Finset (Fin n)} {c : Fin n}
    (hc : c ∈ Cmed) : c ∈ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff :=
  Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_union_left _ hc)))

theorem mem_prev_of_mem_Cdiff {Cmed Cdiff Chuge Cmain Cbuff : Finset (Fin n)} {c : Fin n}
    (hc : c ∈ Cdiff) : c ∈ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff :=
  Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_union_right _ hc)))

theorem mem_prev_of_mem_Chuge {Cmed Cdiff Chuge Cmain Cbuff : Finset (Fin n)} {c : Fin n}
    (hc : c ∈ Chuge) : c ∈ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff :=
  Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_union_right _ hc))

theorem mem_prev_of_mem_Cmain {Cmed Cdiff Chuge Cmain Cbuff : Finset (Fin n)} {c : Fin n}
    (hc : c ∈ Cmain) : c ∈ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff :=
  Finset.mem_union_left _ (Finset.mem_union_right _ hc)

theorem mem_prev_of_mem_Cbuff {Cmed Cdiff Chuge Cmain Cbuff : Finset (Fin n)} {c : Fin n}
    (hc : c ∈ Cbuff) : c ∈ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff :=
  Finset.mem_union_right _ hc

/-- The `famVert` of `prevFam` in each of the four branches. -/
theorem famVert_prevFam_eq_Cdiff {𝓗 : Hypergraph (Fin n)} {MD HM MM MB : Fin n → Set 𝓗}
    {Cdiff Cmain Cbuff : Finset (Fin n)} {c : Fin n} (hc : c ∈ Cdiff) :
    famVert (prevFam MD HM MM MB Cdiff Cmain Cbuff c) = matchVert (MD c) := by
  rw [prevFam_of_mem_Cdiff hc, famVert_famOf]

theorem famVert_prevFam_eq_Cmain {𝓗 : Hypergraph (Fin n)} {MD HM MM MB : Fin n → Set 𝓗}
    {Cdiff Cmain Cbuff : Finset (Fin n)} {c : Fin n} (hd : c ∉ Cdiff) (hc : c ∈ Cmain) :
    famVert (prevFam MD HM MM MB Cdiff Cmain Cbuff c) = matchVert (MM c) := by
  rw [prevFam_of_mem_Cmain hd hc, famVert_famOf]

theorem famVert_prevFam_eq_Cbuff {𝓗 : Hypergraph (Fin n)} {MD HM MM MB : Fin n → Set 𝓗}
    {Cdiff Cmain Cbuff : Finset (Fin n)} {c : Fin n} (hd : c ∉ Cdiff) (hm : c ∉ Cmain)
    (hc : c ∈ Cbuff) :
    famVert (prevFam MD HM MM MB Cdiff Cmain Cbuff c) = matchVert (MB c) := by
  rw [prevFam_of_mem_Cbuff hd hm hc, famVert_famOf]

theorem famVert_prevFam_eq_HM {𝓗 : Hypergraph (Fin n)} {MD HM MM MB : Fin n → Set 𝓗}
    {Cdiff Cmain Cbuff : Finset (Fin n)} {c : Fin n} (hd : c ∉ Cdiff) (hm : c ∉ Cmain)
    (hb : c ∉ Cbuff) :
    famVert (prevFam MD HM MM MB Cdiff Cmain Cbuff c) = matchVert (HM c) := by
  rw [prevFam_of_notMem hd hm hb, famVert_famOf]


/-! ## The `m(w)`-bounds for `𝓜_prev` -/

/-- **§12 Step 9, instantiated: the `m(w)`-bounds `(eqn:mbound_1)`--`(eqn:mbound_3)`
for `𝓜_prev`.**  The family `𝓜_prev^*` is `prevFam` of `S12Mprev.lean`, indexed
by all of `Fin n` through `prevFamFull`. -/
theorem s12_step9_mbound {𝓗 : Hypergraph (Fin n)} {U S₁ S₂ S₃ : Set (Fin n)} {ε : ℝ}
    {MD HM MM MB : Fin n → Set 𝓗} {Cmed Cdiff Chuge Cmain Cbuff : Finset (Fin n)}
    {Vn1 Vn2 : Set (Fin n)}
    (hS₂ : S₂ = S2def U S₁ HM (Cmed ∪ Chuge))
    (hS₃ : S₃ = S3def U S₂ MM Cmain)
    (hdiff1 : Cdiff.card ≤ 1)
    (hdiffVn1 : ∀ c ∈ Cdiff, Vn1 ⊆ matchVert (MD c))
    (hdiffVn2 : ∀ c ∈ Cdiff, Vn2 ∩ S₁ ⊆ matchVert (MD c))
    (hhm : ∀ c ∈ Cmed ∪ Chuge, U \ matchVert (HM c) ⊆ S₁)
    (hmain : ∀ c ∈ Cmain, U \ matchVert (MM c) ⊆ S₂)
    (hbuff : ∀ c ∈ Cbuff, U \ matchVert (MB c) ⊆ S₃)
    (h21 : S₂ ⊆ S₁) (h32 : S₃ ⊆ S₂)
    (hnp : ∀ u ∈ U, ((Cmed ∪ Chuge).filter (fun c => u ∉ matchVert (HM c))).card ≤ 1)
    (hnp' : ∀ u ∈ U, (Cmain.filter (fun c => u ∉ matchVert (MM c))).card ≤ 1)
    (hnp'' : ∀ u ∈ U, (Cbuff.filter (fun c => u ∉ matchVert (MB c))).card ≤ 1)
    (hperf : (U.ncard : ℝ) ≤ (1 - 10 * ε) * (n : ℝ) →
      (∀ c ∈ Cmed ∪ Chuge, U ⊆ matchVert (HM c)) ∧
      (∀ c ∈ Cmain, U ⊆ matchVert (MM c)) ∧
      (∀ c ∈ Cbuff, U ⊆ matchVert (MB c)))
    (hVn1Vn2 : Vn1 ⊆ Vn2) (hVn2U : Vn2 ⊆ U) :
    (∀ u ∈ U \ S₁, (prevMiss MD HM MM MB Cmed Cdiff Chuge Cmain Cbuff u).ncard ≤ 1) ∧
    (∀ v ∈ Vn1 \ S₁, (prevMiss MD HM MM MB Cmed Cdiff Chuge Cmain Cbuff v).ncard = 0) ∧
    (∀ u ∈ U \ Vn2, (prevMiss MD HM MM MB Cmed Cdiff Chuge Cmain Cbuff u).ncard ≤ 2) ∧
    (∀ v ∈ Vn2, (prevMiss MD HM MM MB Cmed Cdiff Chuge Cmain Cbuff v).ncard ≤ 1) ∧
    (((U.ncard : ℝ) ≤ (1 - 10 * ε) * (n : ℝ)) →
      (∀ u ∈ U \ Vn1, (prevMiss MD HM MM MB Cmed Cdiff Chuge Cmain Cbuff u).ncard ≤ 1) ∧
      (∀ v ∈ Vn1, (prevMiss MD HM MM MB Cmed Cdiff Chuge Cmain Cbuff v).ncard = 0)) := by
  classical
  -- the `Finset`-level miss count of `S12Mprev.lean`
  have hcount : ∀ u ∈ U,
      ((Cmed ∪ Chuge).filter (fun c => u ∉ matchVert (HM c))).card +
        (Cmain.filter (fun c => u ∉ matchVert (MM c))).card +
        (Cbuff.filter (fun c => u ∉ matchVert (MB c))).card ≤ 1 := by
    intro u hu
    exact ncard_miss_le_one hu hS₂ hS₃ hmain hbuff (hnp u hu) (hnp' u hu) (hnp'' u hu)
  -- the miss set (off `C_diff`) is contained in the union of the three filters
  have hmiss_sub : ∀ u : Fin n,
      {i : Fin n | i ∉ (Cdiff : Set (Fin n)) ∧
        u ∉ famVert (prevFamFull MD HM MM MB Cmed Cdiff Chuge Cmain Cbuff i)} ⊆
      ↑((Cmed ∪ Chuge).filter (fun c => u ∉ matchVert (HM c)) ∪
        (Cmain.filter (fun c => u ∉ matchVert (MM c)) ∪
        Cbuff.filter (fun c => u ∉ matchVert (MB c))) : Finset (Fin n)) := by
    rintro u i ⟨hid, hi⟩
    by_cases hmem : i ∈ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff
    · rw [prevFamFull_of_mem hmem] at hi
      by_cases hm : i ∈ Cmain
      · rw [famVert_prevFam_eq_Cmain hid hm] at hi
        exact Finset.mem_union_right _
          (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hm, hi⟩))
      · by_cases hb : i ∈ Cbuff
        · rw [famVert_prevFam_eq_Cbuff hid hm hb] at hi
          exact Finset.mem_union_right _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hb, hi⟩))
        · rw [famVert_prevFam_eq_HM hid hm hb] at hi
          exact Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨mem_med_huge_of_mem_prev hmem hid hm hb, hi⟩)
    · rw [famVert_prevFamFull_of_notMem hmem] at hi
      exact (hi trivial).elim
  -- the resulting cardinality bound
  have hmiss_bound : ∀ u : Fin n,
      ({i : Fin n | i ∉ (Cdiff : Set (Fin n)) ∧
        u ∉ famVert (prevFamFull MD HM MM MB Cmed Cdiff Chuge Cmain Cbuff i)} :
          Set (Fin n)).ncard ≤
        ((Cmed ∪ Chuge).filter (fun c => u ∉ matchVert (HM c))).card +
          (Cmain.filter (fun c => u ∉ matchVert (MM c))).card +
          (Cbuff.filter (fun c => u ∉ matchVert (MB c))).card := by
    intro u
    have h1 : ({i : Fin n | i ∉ (Cdiff : Set (Fin n)) ∧
        u ∉ famVert (prevFamFull MD HM MM MB Cmed Cdiff Chuge Cmain Cbuff i)} :
          Set (Fin n)).ncard ≤
        ((((Cmed ∪ Chuge).filter (fun c => u ∉ matchVert (HM c)) ∪
          (Cmain.filter (fun c => u ∉ matchVert (MM c)) ∪
          Cbuff.filter (fun c => u ∉ matchVert (MB c))) : Finset (Fin n))) :
            Set (Fin n)).ncard :=
      Set.ncard_le_ncard (hmiss_sub u) (Set.toFinite _)
    rw [Set.ncard_coe_finset] at h1
    have h2 := Finset.card_union_le ((Cmed ∪ Chuge).filter (fun c => u ∉ matchVert (HM c)))
      (Cmain.filter (fun c => u ∉ matchVert (MM c)) ∪
        Cbuff.filter (fun c => u ∉ matchVert (MB c)))
    have h3 := Finset.card_union_le (Cmain.filter (fun c => u ∉ matchVert (MM c)))
      (Cbuff.filter (fun c => u ∉ matchVert (MB c)))
    omega
  refine s12_mbound (ι := Fin n) (M := prevFamFull MD HM MM MB Cmed Cdiff Chuge Cmain Cbuff)
    (U := U) (S₁ := S₁) (ε := ε) (ιdiff := (Cdiff : Set (Fin n))) (Vn1 := Vn1) (Vn2 := Vn2)
    (hdiff1 := ?_) (hdiffVn1 := ?_) (hdiffVn2 := ?_) (hrestcov := ?_) (hnp := ?_)
    (hperf := ?_) (hVn1Vn2 := hVn1Vn2) (hVn2U := hVn2U)
  · rw [Set.ncard_coe_finset]; exact hdiff1
  · intro i hi
    rw [prevFamFull_of_mem (mem_prev_of_mem_Cdiff hi), famVert_prevFam_eq_Cdiff hi]
    exact hdiffVn1 i hi
  · intro i hi
    rw [prevFamFull_of_mem (mem_prev_of_mem_Cdiff hi), famVert_prevFam_eq_Cdiff hi]
    exact hdiffVn2 i hi
  · intro i hi
    by_cases hmem : i ∈ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff
    · rw [prevFamFull_of_mem hmem]
      refine sdiff_famVert_prevFam_subset i (fun h => absurd h hi) ?_ ?_ ?_
      · intro _ h2
        exact (hmain i h2).trans h21
      · intro _ _ h3
        exact (hbuff i h3).trans (h32.trans h21)
      · intro hd hm hb
        exact hhm i (mem_med_huge_of_mem_prev hmem hd hm hb)
    · rw [famVert_prevFamFull_of_notMem hmem]
      intro v hv
      exact (hv.2 trivial).elim
  · intro u hu
    exact le_trans (hmiss_bound u) (hcount u hu)
  · intro hUc i hi
    rcases hperf hUc with ⟨h1, h2, h3⟩
    by_cases hmem : i ∈ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff
    · rw [prevFamFull_of_mem hmem]
      by_cases hm : i ∈ Cmain
      · rw [famVert_prevFam_eq_Cmain hi hm]; exact h2 i hm
      · by_cases hb : i ∈ Cbuff
        · rw [famVert_prevFam_eq_Cbuff hi hm hb]; exact h3 i hb
        · rw [famVert_prevFam_eq_HM hi hm hb]
          exact h1 i (mem_med_huge_of_mem_prev hmem hi hm hb)
    · rw [famVert_prevFamFull_of_notMem hmem]
      exact Set.subset_univ U

end

end ErdosFaberLovaszConjecture
