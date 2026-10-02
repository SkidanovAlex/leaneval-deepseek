import Submission.EFL.S12Step4
import Submission.EFL.S12Step5
import Submission.EFL.S12Step6
import Submission.EFL.S12Step7
import Submission.EFL.S12Step8r
import Submission.EFL.S12Step9
import Submission.EFL.ReservoirExistence
import Submission.EFL.GFactorDischarge
import Submission.EFL.S12Numeric

/-!
# §12: the assembly of `𝓜_prev` (the family of matchings of Steps 4--7)

The proof of Theorem 1.1 builds a family `𝓜_prev = {M_c : c ∈ C_prev}` of
pairwise edge-disjoint matchings, where
`C_prev = C_med ∪ C_diff ∪ C_huge ∪ C_main ∪ C_buff`:

* `c ∈ C_diff`     — the (at most one) matching of Step 4 (`𝓜_diff`);
* `c ∈ C_main`     — the matchings of Step 6 (`𝓜_main`);
* `c ∈ C_buff`     — the matchings of Step 7 (`𝓜_buff`);
* otherwise (`c ∈ C_med ∪ C_huge`) — the matchings of Step 5 (`𝓜_hm`).

Since the five colour sets are pairwise disjoint, the corresponding matchings of
a given colour are the *unique* nonempty one, and `𝓜_prev` is well defined.

This module records the assembly and its structural properties: the family is
supported on `C_prev`, each member is a matching of `𝓗` (equivalently of
`𝓗_reg`), distinct members are edge-disjoint, and the coverage properties of
the individual steps transfer to the union.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-! ## Elementary glue -/

/-- Two disjoint families of vertex sets are edge-disjoint. -/
theorem edgeDisjointFam_of_disjoint {A B : Set (Set (Fin n))} (h : Disjoint A B) :
    EdgeDisjointFam A B := by
  rw [EdgeDisjointFam]
  exact Set.disjoint_of_subset_left (fun e he => he.1)
    (Set.disjoint_of_subset_right (fun e he => he.1) h)

/-- The `famOf`-image of a union of four families. -/
theorem famOf_union_four {𝓗 : Hypergraph (Fin n)} (A B C D : Set 𝓗) :
    famOf (A ∪ B ∪ C ∪ D) = famOf A ∪ famOf B ∪ famOf C ∪ famOf D := by
  rw [famOf_union, famOf_union, famOf_union]

/-! ## The family `𝓜_prev^*` -/

/-- **The family `𝓜_prev^*` of §12**, as a family of vertex sets: the colour `c`
carries the matching of the step whose colour set contains `c`.  The colour
sets are pairwise disjoint, so the definition is well posed (the branch taken
is irrelevant for colours outside the corresponding set, where the matching is
empty). -/
def prevFam {𝓗 : Hypergraph (Fin n)} (MD HM MM MB : Fin n → Set 𝓗)
    (Cdiff Cmain Cbuff : Finset (Fin n)) (c : Fin n) : Set (Set (Fin n)) :=
  if c ∈ Cdiff then famOf (MD c)
  else if c ∈ Cmain then famOf (MM c)
  else if c ∈ Cbuff then famOf (MB c)
  else famOf (HM c)

theorem prevFam_of_mem_Cdiff {𝓗 : Hypergraph (Fin n)} {MD HM MM MB : Fin n → Set 𝓗}
    {Cdiff Cmain Cbuff : Finset (Fin n)} {c : Fin n} (hc : c ∈ Cdiff) :
    prevFam MD HM MM MB Cdiff Cmain Cbuff c = famOf (MD c) := if_pos hc

theorem prevFam_of_mem_Cmain {𝓗 : Hypergraph (Fin n)} {MD HM MM MB : Fin n → Set 𝓗}
    {Cdiff Cmain Cbuff : Finset (Fin n)} {c : Fin n} (hc : c ∉ Cdiff) (hc' : c ∈ Cmain) :
    prevFam MD HM MM MB Cdiff Cmain Cbuff c = famOf (MM c) := by
  rw [prevFam, if_neg hc, if_pos hc']

theorem prevFam_of_mem_Cbuff {𝓗 : Hypergraph (Fin n)} {MD HM MM MB : Fin n → Set 𝓗}
    {Cdiff Cmain Cbuff : Finset (Fin n)} {c : Fin n} (hc : c ∉ Cdiff) (hc' : c ∉ Cmain)
    (hc'' : c ∈ Cbuff) :
    prevFam MD HM MM MB Cdiff Cmain Cbuff c = famOf (MB c) := by
  rw [prevFam, if_neg hc, if_neg hc', if_pos hc'']

theorem prevFam_of_notMem {𝓗 : Hypergraph (Fin n)} {MD HM MM MB : Fin n → Set 𝓗}
    {Cdiff Cmain Cbuff : Finset (Fin n)} {c : Fin n} (hc : c ∉ Cdiff) (hc' : c ∉ Cmain)
    (hc'' : c ∉ Cbuff) :
    prevFam MD HM MM MB Cdiff Cmain Cbuff c = famOf (HM c) := by
  rw [prevFam, if_neg hc, if_neg hc', if_neg hc'']

/-- A colour outside `C_prev = C_med ∪ C_diff ∪ C_huge ∪ C_main ∪ C_buff` carries
nothing. -/
theorem prevFam_eq_empty {𝓗 : Hypergraph (Fin n)} {MD HM MM MB : Fin n → Set 𝓗}
    {Cmed Cdiff Chuge Cmain Cbuff : Finset (Fin n)} {c : Fin n}
    (hD : ∀ c ∉ Cdiff, MD c = ∅) (hH : ∀ c ∉ Cmed ∪ Chuge, HM c = ∅)
    (hM : ∀ c ∉ Cmain, MM c = ∅) (hB : ∀ c ∉ Cbuff, MB c = ∅)
    (hc : c ∉ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff) :
    prevFam MD HM MM MB Cdiff Cmain Cbuff c = ∅ := by
  have h1 : c ∉ Cdiff := fun h => hc (Finset.mem_union_left Cbuff (Finset.mem_union_left Cmain
    (Finset.mem_union_left Chuge (Finset.mem_union_right Cmed h))))
  have h2 : c ∉ Cmain := fun h => hc (Finset.mem_union_left Cbuff
    (Finset.mem_union_right (Cmed ∪ Cdiff ∪ Chuge) h))
  have h3 : c ∉ Cbuff := fun h => hc (Finset.mem_union_right (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain) h)
  have h4 : c ∉ Cmed ∪ Chuge := by
    intro h
    refine hc (Finset.mem_union_left Cbuff (Finset.mem_union_left Cmain ?_))
    rcases Finset.mem_union.mp h with h' | h'
    · exact Finset.mem_union_left Chuge (Finset.mem_union_left Cdiff h')
    · exact Finset.mem_union_right (Cmed ∪ Cdiff) h'
  rw [prevFam_of_notMem h1 h2 h3, hH c h4]
  ext e
  simp [famOf]

/-- `𝓜_prev^*` at `c` is contained in the union of the four families at `c`. -/
theorem prevFam_subset_union {𝓗 : Hypergraph (Fin n)} (MD HM MM MB : Fin n → Set 𝓗)
    (Cdiff Cmain Cbuff : Finset (Fin n)) (c : Fin n) :
    prevFam MD HM MM MB Cdiff Cmain Cbuff c ⊆ famOf (MD c ∪ HM c ∪ MM c ∪ MB c) := by
  rw [famOf_union_four]
  by_cases h1 : c ∈ Cdiff
  · rw [prevFam_of_mem_Cdiff h1]
    intro e he
    exact Or.inl (Or.inl (Or.inl he))
  · by_cases h2 : c ∈ Cmain
    · rw [prevFam_of_mem_Cmain h1 h2]
      intro e he
      exact Or.inl (Or.inr he)
    · by_cases h3 : c ∈ Cbuff
      · rw [prevFam_of_mem_Cbuff h1 h2 h3]
        intro e he
        exact Or.inr he
      · rw [prevFam_of_notMem h1 h2 h3]
        intro e he
        exact Or.inl (Or.inl (Or.inr he))

/-- The vertex set of `𝓜_prev^*` at `c`, in terms of the branch taken. -/
theorem famVert_prevFam {𝓗 : Hypergraph (Fin n)} (MD HM MM MB : Fin n → Set 𝓗)
    (Cdiff Cmain Cbuff : Finset (Fin n)) (c : Fin n) :
    (c ∈ Cdiff → famVert (prevFam MD HM MM MB Cdiff Cmain Cbuff c) = matchVert (MD c)) ∧
    (c ∉ Cdiff → c ∈ Cmain →
      famVert (prevFam MD HM MM MB Cdiff Cmain Cbuff c) = matchVert (MM c)) ∧
    (c ∉ Cdiff → c ∉ Cmain → c ∈ Cbuff →
      famVert (prevFam MD HM MM MB Cdiff Cmain Cbuff c) = matchVert (MB c)) ∧
    (c ∉ Cdiff → c ∉ Cmain → c ∉ Cbuff →
      famVert (prevFam MD HM MM MB Cdiff Cmain Cbuff c) = matchVert (HM c)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; rw [prevFam_of_mem_Cdiff h, famVert_famOf]
  · intro h h'; rw [prevFam_of_mem_Cmain h h', famVert_famOf]
  · intro h h' h''; rw [prevFam_of_mem_Cbuff h h' h'', famVert_famOf]
  · intro h h' h''; rw [prevFam_of_notMem h h' h'', famVert_famOf]


/-! ## `𝓜_prev` is a family of matchings -/

/-- Each member of `𝓜_prev^*` is a matching of `𝓗_reg`. -/
theorem isMatching_prevFam {𝓗 : Hypergraph (Fin n)} {MD HM MM MB : Fin n → Set 𝓗}
    {Cdiff Cmain Cbuff : Finset (Fin n)}
    (hD : ∀ c, IsMatching 𝓗 (MD c)) (hH : ∀ c, IsMatching 𝓗 (HM c))
    (hM : ∀ c, IsMatching 𝓗 (MM c)) (hB : ∀ c, IsMatching 𝓗 (MB c)) (c : Fin n) :
    MultiHypergraph.IsMatching (MultiHypergraph.regHypergraph 𝓗)
      (prevFam MD HM MM MB Cdiff Cmain Cbuff c) := by
  by_cases h1 : c ∈ Cdiff
  · rw [prevFam_of_mem_Cdiff h1]; exact isMatching_famOf_reg (hD c)
  · by_cases h2 : c ∈ Cmain
    · rw [prevFam_of_mem_Cmain h1 h2]; exact isMatching_famOf_reg (hM c)
    · by_cases h3 : c ∈ Cbuff
      · rw [prevFam_of_mem_Cbuff h1 h2 h3]; exact isMatching_famOf_reg (hB c)
      · rw [prevFam_of_notMem h1 h2 h3]; exact isMatching_famOf_reg (hH c)

/-- Deleting the singletons from `𝓜_prev^*` gives a matching of `𝓗`. -/
theorem isMatching_prevFam_toFam {𝓗 : Hypergraph (Fin n)} {MD HM MM MB : Fin n → Set 𝓗}
    {Cdiff Cmain Cbuff : Finset (Fin n)}
    (hD : ∀ c, IsMatching 𝓗 (MD c)) (hH : ∀ c, IsMatching 𝓗 (HM c))
    (hM : ∀ c, IsMatching 𝓗 (MM c)) (hB : ∀ c, IsMatching 𝓗 (MB c)) (c : Fin n) :
    IsMatching 𝓗 (toFam (prevFam MD HM MM MB Cdiff Cmain Cbuff c)) :=
  MultiHypergraph.IsMatching.toFam (isMatching_prevFam hD hH hM hB c) (fun _ he => he)

/-- **The coverage at `c` transfers from a single branch.**  If the vertices of
`U` missed by the matching of the branch containing `c` lie in `S`, then so do
the vertices of `U` missed by `𝓜_prev^*` at `c`. -/
theorem sdiff_famVert_prevFam_subset {𝓗 : Hypergraph (Fin n)} {MD HM MM MB : Fin n → Set 𝓗}
    {Cdiff Cmain Cbuff : Finset (Fin n)} {U S : Set (Fin n)} (c : Fin n)
    (hD : c ∈ Cdiff → U \ matchVert (MD c) ⊆ S)
    (hM : c ∉ Cdiff → c ∈ Cmain → U \ matchVert (MM c) ⊆ S)
    (hB : c ∉ Cdiff → c ∉ Cmain → c ∈ Cbuff → U \ matchVert (MB c) ⊆ S)
    (hH : c ∉ Cdiff → c ∉ Cmain → c ∉ Cbuff → U \ matchVert (HM c) ⊆ S) :
    U \ famVert (prevFam MD HM MM MB Cdiff Cmain Cbuff c) ⊆ S := by
  have hmain := (famVert_prevFam MD HM MM MB Cdiff Cmain Cbuff c)
  by_cases h1 : c ∈ Cdiff
  · rw [hmain.1 h1]
    exact hD h1
  · by_cases h2 : c ∈ Cmain
    · rw [hmain.2.1 h1 h2]
      exact hM h1 h2
    · by_cases h3 : c ∈ Cbuff
      · rw [hmain.2.2.1 h1 h2 h3]
        exact hB h1 h2 h3
      · rw [hmain.2.2.2 h1 h2 h3]
        exact hH h1 h2 h3

/-! ## The singleton bookkeeping of `𝓗_reg` at the vertices of `U` -/

/-- **No matching of a sub-multi-hypergraph of `𝓗_reg` covers a vertex of `U`
by a singleton edge.**  Consequently "covered" has the same meaning in `𝓜` and
in `𝓗` for the vertices of `U`, which is what lets the coverage statements of
Steps 5--7 (phrased with `famVert`) be used for the matchings of `𝓗`
(phrased with `matchVert`). -/
theorem matchVert_toFam_of_mem_famVert {𝓗 : Hypergraph (Fin n)} {𝓜 : MultiHypergraph n}
    (hbig : ∀ e ∈ 𝓗, 2 ≤ e.ncard) (h𝓜 : 𝓜 ≤ MultiHypergraph.regHypergraph 𝓗)
    {G : Set (Set (Fin n))} (hG : MultiHypergraph.IsMatching 𝓜 G)
    {U : Set (Fin n)} {ε : ℝ} (hU : U ⊆ Vplus 𝓗 (1 - ε)) (hεn : ε * (n : ℝ) ≤ 3)
    {u : Fin n} (hu : u ∈ U) (h : u ∈ famVert G) :
    u ∈ matchVert (toFam (𝓗 := 𝓗) G) := by
  rw [mem_famVert] at h
  obtain ⟨e, he, hue⟩ := h
  have hedges : e ∈ 𝓜.edgeSet := hG.1 he
  rw [MultiHypergraph.mem_edgeSet] at hedges
  rcases hedges with h1 | ⟨v, rfl, hv⟩
  · have he𝓗 : e ∈ 𝓗 := h𝓜.1 h1
    exact mem_matchVert.mpr ⟨⟨e, he𝓗⟩, mem_toFam_iff.mpr ⟨he, hbig e he𝓗⟩, hue⟩
  · exfalso
    have hvu : v = u := (Set.mem_singleton_iff.mp hue).symm
    have h0 : (MultiHypergraph.regHypergraph 𝓗).singles u = 0 :=
      singles_regHypergraph_eq_zero_of_mem_Vplus 𝓗 hεn (hU hu)
    have hle : 𝓜.singles u ≤ 0 := by
      rw [← h0]
      exact h𝓜.2 u
    rw [hvu] at hv
    omega


/-! ## The defect sets `S₂` and `S₃` and the global coverage of `𝓜_prev ∖ 𝓜_diff` -/

/-- The defect set `S₂` of Step 6: `S₁` minus the vertices of `U` missed by one
of the matchings of `𝓜_hm`. -/
def S2def (U S₁ : Set (Fin n)) {𝓗 : Hypergraph (Fin n)} (Mhm : Fin n → Set 𝓗)
    (C : Finset (Fin n)) : Set (Fin n) :=
  S₁ \ ⋃ c ∈ (C : Set (Fin n)), (U \ matchVert (Mhm c))

/-- The defect set `S₃` of Step 7: `S₂` minus the vertices of `U` missed by one
of the matchings of `𝓜_main`. -/
def S3def (U S₂ : Set (Fin n)) {𝓗 : Hypergraph (Fin n)} (Mmain : Fin n → Set 𝓗)
    (C : Finset (Fin n)) : Set (Fin n) :=
  S₂ \ ⋃ c ∈ (C : Set (Fin n)), (U \ matchVert (Mmain c))

theorem S2def_subset (U S₁ : Set (Fin n)) {𝓗 : Hypergraph (Fin n)} (Mhm : Fin n → Set 𝓗)
    (C : Finset (Fin n)) : S2def U S₁ Mhm C ⊆ S₁ := Set.sdiff_subset

theorem S3def_subset (U S₂ : Set (Fin n)) {𝓗 : Hypergraph (Fin n)} (Mmain : Fin n → Set 𝓗)
    (C : Finset (Fin n)) : S3def U S₂ Mmain C ⊆ S₂ := Set.sdiff_subset

/-- A vertex of `S₂` (which lies in `U`) is covered by *every* matching of
`𝓜_hm`. -/
theorem mem_matchVert_of_mem_S2def {𝓗 : Hypergraph (Fin n)} {U S₁ : Set (Fin n)}
    {Mhm : Fin n → Set 𝓗} {C : Finset (Fin n)} {u : Fin n} (h : u ∈ S2def U S₁ Mhm C)
    (hu : u ∈ U) {c : Fin n} (hc : c ∈ C) : u ∈ matchVert (Mhm c) := by
  by_contra hmem
  have h1 : u ∈ ⋃ c ∈ (C : Set (Fin n)), (U \ matchVert (Mhm c)) := by
    simp only [Set.mem_iUnion]
    exact ⟨c, hc, hu, hmem⟩
  rw [S2def, Set.mem_sdiff] at h
  exact h.2 h1

/-- A vertex of `S₃` (which lies in `U`) is covered by *every* matching of
`𝓜_main`. -/
theorem mem_matchVert_of_mem_S3def {𝓗 : Hypergraph (Fin n)} {U S₂ : Set (Fin n)}
    {Mmain : Fin n → Set 𝓗} {C : Finset (Fin n)} {u : Fin n} (h : u ∈ S3def U S₂ Mmain C)
    (hu : u ∈ U) {c : Fin n} (hc : c ∈ C) : u ∈ matchVert (Mmain c) := by
  by_contra hmem
  have h1 : u ∈ ⋃ c ∈ (C : Set (Fin n)), (U \ matchVert (Mmain c)) := by
    simp only [Set.mem_iUnion]
    exact ⟨c, hc, hu, hmem⟩
  rw [S3def, Set.mem_sdiff] at h
  exact h.2 h1

/-- **The global coverage of `𝓜_hm ∪ 𝓜_main ∪ 𝓜_buff`.**  If the defects of the
coverage of `U` by the three families lie in `S₁`, `S₂`, `S₃` (with
`S₂ = S₁ ∖ ⋃_{𝓜_hm}(U ∖ V(M))` and `S₃ = S₂ ∖ ⋃_{𝓜_main}(U ∖ V(M))`) and each
family misses a given `u ∈ U` at most once, then so does their union: at most
one of the three families misses `u` at all. -/
theorem ncard_miss_le_one {𝓗 : Hypergraph (Fin n)} {U S₁ S₂ S₃ : Set (Fin n)}
    {Mhm Mmain Mbuff : Fin n → Set 𝓗} {Cmed Chuge Cmain Cbuff : Finset (Fin n)} {u : Fin n}
    (hu : u ∈ U)
    (hS₂ : S₂ = S2def U S₁ Mhm (Cmed ∪ Chuge))
    (hS₃ : S₃ = S3def U S₂ Mmain Cmain)
    (hmain : ∀ c ∈ Cmain, U \ matchVert (Mmain c) ⊆ S₂)
    (hbuff : ∀ c ∈ Cbuff, U \ matchVert (Mbuff c) ⊆ S₃)
    (hnp_hm : ((Cmed ∪ Chuge).filter (fun c => u ∉ matchVert (Mhm c))).card ≤ 1)
    (hnp_main : (Cmain.filter (fun c => u ∉ matchVert (Mmain c))).card ≤ 1)
    (hnp_buff : (Cbuff.filter (fun c => u ∉ matchVert (Mbuff c))).card ≤ 1) :
    ((Cmed ∪ Chuge).filter (fun c => u ∉ matchVert (Mhm c))).card +
      (Cmain.filter (fun c => u ∉ matchVert (Mmain c))).card +
      (Cbuff.filter (fun c => u ∉ matchVert (Mbuff c))).card ≤ 1 := by
  classical
  -- a vertex of `S₂` is covered by all of `𝓜_hm`
  have hS₂cov : ∀ c ∈ Cmed ∪ Chuge, u ∈ S₂ → u ∈ matchVert (Mhm c) := by
    intro c hc hmem
    rw [hS₂] at hmem
    exact mem_matchVert_of_mem_S2def hmem hu hc
  -- a vertex of `S₃` is covered by all of `𝓜_main`
  have hS₃cov : ∀ c ∈ Cmain, u ∈ S₃ → u ∈ matchVert (Mmain c) := by
    intro c hc hmem
    rw [hS₃] at hmem
    exact mem_matchVert_of_mem_S3def hmem hu hc
  -- `𝓜_main` missing `u` forces all of `𝓜_hm` to cover `u`
  have hmain_hm : 0 < (Cmain.filter (fun c => u ∉ matchVert (Mmain c))).card →
      (Cmed ∪ Chuge).filter (fun c => u ∉ matchVert (Mhm c)) = ∅ := by
    intro hpos
    obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hc
    have hS₂u : u ∈ S₂ := hmain c hc.1 ⟨hu, hc.2⟩
    refine Finset.eq_empty_iff_forall_notMem.mpr (fun c' hc' => ?_)
    rw [Finset.mem_filter] at hc'
    exact hc'.2 (hS₂cov c' hc'.1 hS₂u)
  -- `𝓜_buff` missing `u` forces all of `𝓜_hm` and `𝓜_main` to cover `u`
  have hbuff_hm : 0 < (Cbuff.filter (fun c => u ∉ matchVert (Mbuff c))).card →
      (Cmed ∪ Chuge).filter (fun c => u ∉ matchVert (Mhm c)) = ∅ := by
    intro hpos
    obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hc
    have hS₃u : u ∈ S₃ := hbuff c hc.1 ⟨hu, hc.2⟩
    have hS₂u : u ∈ S₂ := by rw [hS₃] at hS₃u; exact S3def_subset U S₂ Mmain Cmain hS₃u
    refine Finset.eq_empty_iff_forall_notMem.mpr (fun c' hc' => ?_)
    rw [Finset.mem_filter] at hc'
    exact hc'.2 (hS₂cov c' hc'.1 hS₂u)
  have hbuff_main : 0 < (Cbuff.filter (fun c => u ∉ matchVert (Mbuff c))).card →
      Cmain.filter (fun c => u ∉ matchVert (Mmain c)) = ∅ := by
    intro hpos
    obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hc
    have hS₃u : u ∈ S₃ := hbuff c hc.1 ⟨hu, hc.2⟩
    refine Finset.eq_empty_iff_forall_notMem.mpr (fun c' hc' => ?_)
    rw [Finset.mem_filter] at hc'
    exact hc'.2 (hS₃cov c' hc'.1 hS₃u)
  -- at most one of the three families misses `u`
  by_cases hmain0 : (Cmain.filter (fun c => u ∉ matchVert (Mmain c))).card = 0
  · by_cases hbuff0 : (Cbuff.filter (fun c => u ∉ matchVert (Mbuff c))).card = 0
    · rw [hmain0, hbuff0]
      omega
    · have h1 := hbuff_hm (Nat.pos_of_ne_zero hbuff0)
      rw [h1, Finset.card_empty, hmain0]
      omega
  · have h1 := hmain_hm (Nat.pos_of_ne_zero hmain0)
    have habuff0 : (Cbuff.filter (fun c => u ∉ matchVert (Mbuff c))).card = 0 := by
      by_contra hb
      have h2 := hbuff_main (Nat.pos_of_ne_zero hb)
      rw [h2, Finset.card_empty] at hmain0
      omega
    rw [h1, Finset.card_empty, habuff0]
    omega


/-! ## The defect set `S₁` and the coverage hypotheses of `s12_mbound` -/

/-- The defect set `S₁` of Step 4: `S` minus the vertices of `V^{(n-2)}(𝓗)`
missed by one of the matchings of `𝓜_diff`. -/
def S1def (Vn2 S : Set (Fin n)) {𝓗 : Hypergraph (Fin n)} (Mdiff : Fin n → Set 𝓗)
    (C : Finset (Fin n)) : Set (Fin n) :=
  S \ ⋃ c ∈ (C : Set (Fin n)), (Vn2 \ matchVert (Mdiff c))

theorem S1def_subset (Vn2 S : Set (Fin n)) {𝓗 : Hypergraph (Fin n)} (Mdiff : Fin n → Set 𝓗)
    (C : Finset (Fin n)) : S1def Vn2 S Mdiff C ⊆ S := Set.sdiff_subset

/-- **`(def:r1s1)`.**  Every vertex of `V^{(n-2)}(𝓗) ∩ S₁` is covered by every
matching of `𝓜_diff` (this is `hdiffVn2` of `s12_mbound`). -/
theorem vn2_inter_S1_subset_matchVert {𝓗 : Hypergraph (Fin n)} {Vn2 S S₁ : Set (Fin n)}
    {Mdiff : Fin n → Set 𝓗} {C : Finset (Fin n)} {c : Fin n} (hc : c ∈ C)
    (hS₁ : S₁ = S1def Vn2 S Mdiff C) : Vn2 ∩ S₁ ⊆ matchVert (Mdiff c) := by
  rintro v ⟨hv2, hv1⟩
  by_contra hmem
  have h1 : v ∈ ⋃ c ∈ (C : Set (Fin n)), (Vn2 \ matchVert (Mdiff c)) := by
    simp only [Set.mem_iUnion]
    exact ⟨c, hc, hv2, hmem⟩
  rw [hS₁, S1def, Set.mem_sdiff] at hv1
  exact hv1.2 h1

/-- **The coverage hypothesis `hrestcov` of `s12_mbound`.**  For a colour
outside `C_diff`, the vertices of `U` missed by `𝓜_prev^*` lie in `S₁`: this is
the combination of the coverage of `𝓜_hm` (defects in `S₁`), of `𝓜_main`
(defects in `S₂ ⊆ S₁`) and of `𝓜_buff` (defects in `S₃ ⊆ S₂ ⊆ S₁`). -/
theorem sdiff_famVert_prevFam_subset_S1 {𝓗 : Hypergraph (Fin n)}
    {MD HM MM MB : Fin n → Set 𝓗} {U S₁ S₂ S₃ : Set (Fin n)}
    {Cmed Cdiff Chuge Cmain Cbuff : Finset (Fin n)}
    (h21 : S₂ ⊆ S₁) (h32 : S₃ ⊆ S₂)
    (hDC : Disjoint Cdiff (Cmed ∪ Chuge ∪ Cmain ∪ Cbuff))
    (hMC : Disjoint Cmain (Cmed ∪ Chuge ∪ Cbuff))
    (hBC : Disjoint Cbuff (Cmed ∪ Chuge ∪ Cmain))
    (hhm : ∀ c ∈ Cmed ∪ Chuge, U \ matchVert (HM c) ⊆ S₁)
    (hmain : ∀ c ∈ Cmain, U \ matchVert (MM c) ⊆ S₂)
    (hbuff : ∀ c ∈ Cbuff, U \ matchVert (MB c) ⊆ S₃) :
    ∀ c ∈ Cmed ∪ Chuge ∪ Cmain ∪ Cbuff,
      U \ famVert (prevFam MD HM MM MB Cdiff Cmain Cbuff c) ⊆ S₁ := by
  intro c hc
  rcases Finset.mem_union.mp hc with h1 | h1
  · rcases Finset.mem_union.mp h1 with h2 | h2
    · -- `c ∈ Cmed ∪ Chuge`
      have hd : c ∉ Cdiff := fun hh => Finset.disjoint_left.mp hDC hh
        (Finset.mem_union_left Cbuff (Finset.mem_union_left Cmain h2))
      have hm : c ∉ Cmain := fun hh => Finset.disjoint_left.mp hMC hh
        (Finset.mem_union_left Cbuff h2)
      have hb : c ∉ Cbuff := fun hh => Finset.disjoint_left.mp hBC hh
        (Finset.mem_union_left Cmain h2)
      rw [prevFam_of_notMem hd hm hb, famVert_famOf]
      exact hhm c h2
    · -- `c ∈ Cmain`
      have hd : c ∉ Cdiff := fun hh => Finset.disjoint_left.mp hDC hh
        (Finset.mem_union_left Cbuff (Finset.mem_union_right (Cmed ∪ Chuge) h2))
      have hb : c ∉ Cbuff := fun hh => Finset.disjoint_left.mp hBC hh
        (Finset.mem_union_right (Cmed ∪ Chuge) h2)
      rw [prevFam_of_mem_Cmain hd h2, famVert_famOf]
      exact fun v hv => h21 (hmain c h2 hv)
  · -- `c ∈ Cbuff`
    have hd : c ∉ Cdiff := fun hh => Finset.disjoint_left.mp hDC hh
      (Finset.mem_union_right (Cmed ∪ Chuge ∪ Cmain) h1)
    have hm : c ∉ Cmain := fun hh => Finset.disjoint_left.mp hMC hh
      (Finset.mem_union_right (Cmed ∪ Chuge) h1)
    rw [prevFam_of_mem_Cbuff hd hm h1, famVert_famOf]
    exact fun v hv => h21 (h32 (hbuff c h1 hv))


/-! ## `𝓜_prev` consists of edges of `𝓗`, so the `hsingle` bookkeeping is vacuous -/

/-- Every element of `𝓜_prev^*` is an edge of `𝓗` (all four steps produce
matchings of `𝓗`, not of the multi-hypergraph `𝓗_reg`). -/
theorem prevFam_subset_hyp {𝓗 : Hypergraph (Fin n)} (MD HM MM MB : Fin n → Set 𝓗)
    (Cdiff Cmain Cbuff : Finset (Fin n)) (c : Fin n) :
    prevFam MD HM MM MB Cdiff Cmain Cbuff c ⊆ 𝓗 := by
  by_cases h1 : c ∈ Cdiff
  · rw [prevFam_of_mem_Cdiff h1]
    rintro e ⟨e', he', rfl⟩
    exact e'.2
  · by_cases h2 : c ∈ Cmain
    · rw [prevFam_of_mem_Cmain h1 h2]
      rintro e ⟨e', he', rfl⟩
      exact e'.2
    · by_cases h3 : c ∈ Cbuff
      · rw [prevFam_of_mem_Cbuff h1 h2 h3]
        rintro e ⟨e', he', rfl⟩
        exact e'.2
      · rw [prevFam_of_notMem h1 h2 h3]
        rintro e ⟨e', he', rfl⟩
        exact e'.2

/-- **The `hsingle` bookkeeping of `s12_deg_h_final` is vacuous** when every
matching consists of edges of `𝓗`: no matching covers `w` only by edges outside
`𝓗`, so the count is `0 ≤ n - 3 - d_𝓗(w)`. -/
theorem ncard_single_miss_eq_zero {𝓗 : Hypergraph (Fin n)} {ι : Type*}
    {M : ι → Set (Set (Fin n))} (hsub : ∀ i, M i ⊆ 𝓗) (w : Fin n) :
    (({i | w ∈ famVert (M i) ∧ ¬ ∃ e ∈ M i, w ∈ e ∧ e ∈ 𝓗} : Set ι)).ncard = 0 := by
  have hempty : ({i | w ∈ famVert (M i) ∧ ¬ ∃ e ∈ M i, w ∈ e ∧ e ∈ 𝓗} : Set ι) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨i, hi⟩
    obtain ⟨e, he, hwe⟩ := mem_famVert.mp hi.1
    exact hi.2 ⟨e, he, hwe, hsub i he⟩
  rw [hempty, Set.ncard_empty]

/-- The `hsingle` hypothesis of `s12_deg_h_final` for `𝓜_prev`. -/
theorem prevFam_single_bound {𝓗 : Hypergraph (Fin n)} (MD HM MM MB : Fin n → Set 𝓗)
    (Cdiff Cmain Cbuff : Finset (Fin n)) (w : Fin n) :
    (({i | w ∈ famVert (prevFam MD HM MM MB Cdiff Cmain Cbuff i) ∧
        ¬ ∃ e ∈ prevFam MD HM MM MB Cdiff Cmain Cbuff i, w ∈ e ∧ e ∈ 𝓗} :
        Set (Fin n))).ncard ≤ n - 3 - MultiHypergraph.hdeg 𝓗 w := by
  rw [ncard_single_miss_eq_zero (fun i => prevFam_subset_hyp MD HM MM MB Cdiff Cmain Cbuff i) w]
  exact Nat.zero_le _

/-! ## `𝓗_final` -/

/-- **`𝓗_final = 𝓗 ∖ ⋃𝓜_prev`** (equation `(eqn:h_final)`), phrased with the
index type `↥C_prev` used by the degree estimates of Step 9. -/
def hfinOf {𝓗 : Hypergraph (Fin n)} (MD HM MM MB : Fin n → Set 𝓗) (Cprev : Finset (Fin n))
    (Cdiff Cmain Cbuff : Finset (Fin n)) : Hypergraph (Fin n) :=
  {e ∈ 𝓗 | ∀ c : ↥Cprev, e ∉ prevFam MD HM MM MB Cdiff Cmain Cbuff c.1}

theorem mem_hfinOf {𝓗 : Hypergraph (Fin n)} {MD HM MM MB : Fin n → Set 𝓗}
    {Cprev Cdiff Cmain Cbuff : Finset (Fin n)} {e : Set (Fin n)} :
    e ∈ hfinOf MD HM MM MB Cprev Cdiff Cmain Cbuff ↔
      e ∈ 𝓗 ∧ ∀ c : ↥Cprev, e ∉ prevFam MD HM MM MB Cdiff Cmain Cbuff c.1 := Iff.rfl


/-- The index type `↥C_prev` has `n - |C_final|` elements (this is the
hypothesis `hcard` of `s12_deg_h_final`). -/
theorem card_Cprev_sub {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} {r₀ β γ ρ : ℝ}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (h : IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal) :
    (Fintype.card ↥(Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff) : ℝ) =
      (n : ℝ) - (Cfinal.card : ℝ) := by
  rw [Fintype.card_coe]
  exact h.card_Cprev_real


/-! ## The vertex sets `V^{(n-1)}(𝓗)` and `V_+^{(n-2)}(𝓗)` of the instantiation -/

/-- The degree of a vertex of a linear hypergraph without singletons is at most
`n-1` (the other endpoints of the edges through a vertex are distinct). -/
theorem hdeg_le_pred {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (hbig : ∀ e ∈ 𝓗, 2 ≤ edgeSize e) (v : Fin n) :
    MultiHypergraph.hdeg 𝓗 v ≤ n - 1 := by
  have h := degree_mul_le (𝓗 := 𝓗) (r := 2) hlin hbig v
  rw [hdeg_eq_hypergraphDegree]
  simpa using h

/-- **The paper's `eqn:non-graph-degree`.**  `2 d_𝓗(v) ≤ (n-1) + d_G(v)`, i.e.
at least `2d - (n-1)` edges through `v` are `2`-edges. -/
theorem two_mul_hdeg_sub_le_degAt {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (hbig : ∀ e ∈ 𝓗, 2 ≤ edgeSize e) (hn1 : 1 ≤ n) (v : Fin n) :
    2 * MultiHypergraph.hdeg 𝓗 v ≤ (n - 1) + degAt 𝓗.pow2 v := by
  have h1 := hdeg_sdiff_pow2_le 𝓗 hlin hbig v
  have h2 : MultiHypergraph.hdeg (𝓗 \ 𝓗.pow2) v + MultiHypergraph.hdeg 𝓗.pow2 v =
      MultiHypergraph.hdeg 𝓗 v :=
    MultiHypergraph.hdeg_sdiff_add (𝓜 := MultiHypergraph.ofHypergraph 𝓗)
      (powFam_subset 𝓗 2) v
  have h3 : MultiHypergraph.hdeg 𝓗.pow2 v = degAt 𝓗.pow2 v := hdeg_pow2_eq_degAt 𝓗 v
  have h4 : (MultiHypergraph.hdeg 𝓗 v : ℝ) ≤
      ((n : ℝ) - 1 + (degAt 𝓗.pow2 v : ℝ)) / 2 := by
    rw [← h2, Nat.cast_add, h3]
    linarith [h1]
  have h5 : 2 * (MultiHypergraph.hdeg 𝓗 v : ℝ) ≤ (n : ℝ) - 1 + (degAt 𝓗.pow2 v : ℝ) := by
    linarith
  have h6 : ((2 * MultiHypergraph.hdeg 𝓗 v : ℕ) : ℝ) ≤
      (((n - 1) + degAt 𝓗.pow2 v : ℕ) : ℝ) := by
    have h7 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn1, Nat.cast_one]
    push_cast
    rw [h7]
    linarith
  exact_mod_cast h6

/-- **`V^{(n-1)}(𝓗) ⊆ U = V_+^{(1-ε)}(G)`**: a vertex in `n-1` edges has at
least `n-1 ≥ (1-ε)n` `2`-edges (`εn ≥ 1`). -/
theorem Vdeg_pred_subset_Vplus {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (hbig : ∀ e ∈ 𝓗, 2 ≤ edgeSize e) (hn1 : 1 ≤ n) {ε : ℝ}
    (hεn : 1 ≤ ε * (n : ℝ)) {v : Fin n} (hv : v ∈ Vdeg 𝓗 (n - 1)) :
    v ∈ Vplus 𝓗 (1 - ε) := by
  have h2 := two_mul_hdeg_sub_le_degAt hlin hbig hn1 v
  have hdv : MultiHypergraph.hdeg 𝓗 v = n - 1 := by simpa [Vdeg, MultiHypergraph.hdeg] using hv
  have h2' : (2 * (n - 1) : ℕ) ≤ (n - 1) + degAt 𝓗.pow2 v := by
    have h := h2
    rwa [hdv] at h
  have h4 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn1, Nat.cast_one]
  have h3 : (2 : ℝ) * ((n - 1 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) + (degAt 𝓗.pow2 v : ℝ) := by
    exact_mod_cast h2'
  rw [h4] at h3
  show (1 - ε) * (n : ℝ) ≤ (degAt 𝓗.pow2 v : ℝ)
  nlinarith

/-- **`V^{(n-2)}(𝓗) ⊆ U = V_+^{(1-ε)}(G)`**: a vertex in `n-2` edges has at
least `n-3 ≥ (1-ε)n` `2`-edges (`εn ≥ 3`). -/
theorem Vdeg_pred2_subset_Vplus {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (hbig : ∀ e ∈ 𝓗, 2 ≤ edgeSize e) (hn2 : 2 ≤ n) {ε : ℝ}
    (hεn : 3 ≤ ε * (n : ℝ)) {v : Fin n} (hv : v ∈ Vdeg 𝓗 (n - 2)) :
    v ∈ Vplus 𝓗 (1 - ε) := by
  have hn1 : 1 ≤ n := by omega
  have h2 := two_mul_hdeg_sub_le_degAt hlin hbig hn1 v
  have hdv : MultiHypergraph.hdeg 𝓗 v = n - 2 := by simpa [Vdeg, MultiHypergraph.hdeg] using hv
  have h2' : (2 * (n - 2) : ℕ) ≤ (n - 1) + degAt 𝓗.pow2 v := by
    have h := h2
    rwa [hdv] at h
  have h4 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn1, Nat.cast_one]
  have h5 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by rw [Nat.cast_sub hn2, Nat.cast_ofNat]
  have h3 : (2 : ℝ) * ((n - 2 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) + (degAt 𝓗.pow2 v : ℝ) := by
    exact_mod_cast h2'
  rw [h4, h5] at h3
  show (1 - ε) * (n : ℝ) ≤ (degAt 𝓗.pow2 v : ℝ)
  nlinarith

/-- **`V_+^{(n-2)}(𝓗) ⊆ U`**, i.e. the hypothesis `hVn2U` of `s12_mbound`. -/
theorem Vdeg_plus_subset_Vplus {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (hbig : ∀ e ∈ 𝓗, 2 ≤ edgeSize e) (hn2 : 2 ≤ n) {ε : ℝ}
    (hεn : 3 ≤ ε * (n : ℝ)) :
    Vdeg 𝓗 (n - 1) ∪ Vdeg 𝓗 (n - 2) ⊆ Vplus 𝓗 (1 - ε) := by
  intro v hv
  rw [Set.mem_union] at hv
  rcases hv with h | h
  · exact Vdeg_pred_subset_Vplus hlin hbig (by omega) (by linarith) h
  · exact Vdeg_pred2_subset_Vplus hlin hbig hn2 hεn h

/-- Membership in `V^{(d)}(𝓗)` is `d_𝓗(v) = d`. -/
theorem mem_Vdeg_iff {𝓗 : Hypergraph (Fin n)} {d : ℕ} {v : Fin n} :
    v ∈ Vdeg 𝓗 d ↔ MultiHypergraph.hdeg 𝓗 v = d := by
  simp only [Vdeg, MultiHypergraph.hdeg, Set.mem_ofPred_eq]

/-- `V^{(n-1)}(𝓗) = {v : (n-1 : ℝ) ≤ d_𝓗(v)}` (the degrees are at most `n-1`). -/
theorem mem_Vdeg_pred_iff {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (hbig : ∀ e ∈ 𝓗, 2 ≤ edgeSize e) (hn1 : 1 ≤ n) {v : Fin n} :
    v ∈ Vdeg 𝓗 (n - 1) ↔ ((n : ℝ) - 1 ≤ (MultiHypergraph.hdeg 𝓗 v : ℝ)) := by
  rw [mem_Vdeg_iff]
  constructor
  · intro h
    rw [h]
    have h4 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn1, Nat.cast_one]
    rw [h4]
  · intro h
    have hle : MultiHypergraph.hdeg 𝓗 v ≤ n - 1 := hdeg_le_pred hlin hbig v
    have hle' : (MultiHypergraph.hdeg 𝓗 v : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hle
    have h4 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn1, Nat.cast_one]
    have h5 : ((n - 1 : ℕ) : ℝ) ≤ (MultiHypergraph.hdeg 𝓗 v : ℝ) := by linarith
    have h6 : n - 1 ≤ MultiHypergraph.hdeg 𝓗 v := by exact_mod_cast h5
    omega

/-- `V_+^{(n-2)}(𝓗) = V^{(n-1)}(𝓗) ∪ V^{(n-2)}(𝓗) = {v : (n-2 : ℝ) ≤ d_𝓗(v)}`. -/
theorem mem_Vdeg_plus_iff {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (hbig : ∀ e ∈ 𝓗, 2 ≤ edgeSize e) (hn2 : 2 ≤ n) {v : Fin n} :
    v ∈ Vdeg 𝓗 (n - 1) ∪ Vdeg 𝓗 (n - 2) ↔
      ((n : ℝ) - 2 ≤ (MultiHypergraph.hdeg 𝓗 v : ℝ)) := by
  rw [Set.mem_union, mem_Vdeg_iff, mem_Vdeg_iff]
  constructor
  · rintro (h | h) <;> rw [h]
    · have h4 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      rw [h4]; linarith
    · have h4 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
        rw [Nat.cast_sub hn2, Nat.cast_ofNat]
      rw [h4]
  · intro h
    have hle : MultiHypergraph.hdeg 𝓗 v ≤ n - 1 := hdeg_le_pred hlin hbig v
    have hge : n - 2 ≤ MultiHypergraph.hdeg 𝓗 v := by
      have h6 : ((n - 2 : ℕ) : ℝ) ≤ (MultiHypergraph.hdeg 𝓗 v : ℝ) := by
        have h7 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
          rw [Nat.cast_sub hn2, Nat.cast_ofNat]
        rw [h7]; exact h
      exact_mod_cast h6
    rcases Nat.eq_or_lt_of_le hge with h' | h'
    · exact Or.inr h'.symm
    · exact Or.inl (by omega)


/-- `V^{(n-1)}(𝓗)`, the set `Vn1` of `s12_mbound`/`s12_uc`/`s12_uc3_count`. -/
abbrev Vn1set (𝓗 : Hypergraph (Fin n)) : Set (Fin n) := Vdeg 𝓗 (n - 1)

/-- `V_+^{(n-2)}(𝓗)`, the set `Vn2` of `s12_mbound`/`s12_uc`/`s12_uc3_count`. -/
abbrev Vn2set (𝓗 : Hypergraph (Fin n)) : Set (Fin n) := Vdeg 𝓗 (n - 1) ∪ Vdeg 𝓗 (n - 2)

/-- `V^{(n-1)}(𝓗) ⊆ V_+^{(n-2)}(𝓗)` (the hypothesis `hVn1Vn2` of `s12_mbound`). -/
theorem Vn1set_subset_Vn2set (𝓗 : Hypergraph (Fin n)) : Vn1set 𝓗 ⊆ Vn2set 𝓗 :=
  Set.subset_union_left


/-! ## The instantiation: Steps 1--3 of §12 -/

/-- **§12, Steps 1--3 (Type A).**  From a Type A colouring `φ` of the medium and
large edges of `𝓗` and the numerical part of the parameter hierarchy, build the
seven colour sets of Step 3, together with the ambient facts of Steps 1--2 used
later: `φ` has singleton colour classes on huge edges (needed for Steps 4--6),
and the vertex sets `V^{(n-1)}(𝓗)` and `V_+^{(n-2)}(𝓗)` are contained in
`U = V_+^{(1-ε)}(G)` (the hypotheses `hVn1Vn2`/`hVn2U` of `s12_mbound`). -/
theorem s12_step3_typeA {n : ℕ} {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (hbig : ∀ e ∈ 𝓗, 2 ≤ edgeSize e) {r₁ r₀ σ γ₁ β γ ρ ε : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)}
    (hA : IsTypeA σ γ₁ β r₁ r₀ 𝓗 φ) (hγ : γ₁ ≤ γ)
    (hβ0 : 0 < β) (hβn : 8 ≤ β * (n : ℝ)) (hn2 : 2 ≤ n)
    (hr1 : r₁ < β * (n : ℝ) / 4)
    (hεn : 3 ≤ ε * (n : ℝ)) (hU : U = Vplus 𝓗 (1 - ε))
    (hnum : (Dparam n ρ : ℝ) + (D'param (Dparam n ρ) γ : ℝ) +
      (2 * γ * (n : ℝ) + 32 / β ^ 2) ≤ (n : ℝ))
    (hDlb : (1 - σ) * (n : ℝ) ≤ (Dparam n ρ : ℝ)) :
    ∃ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n),
      IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal ∧
      φ.SingletonClassesForHuge β ∧
      Vn2set 𝓗 ⊆ U ∧
      (∀ v : Fin n, v ∈ Vn1set 𝓗 ↔ ((n : ℝ) - 1 ≤ (MultiHypergraph.hdeg 𝓗 v : ℝ))) ∧
      (∀ v : Fin n, v ∈ Vn2set 𝓗 ↔ ((n : ℝ) - 2 ≤ (MultiHypergraph.hdeg 𝓗 v : ℝ))) ∧
      (∀ c : Fin n, c ∉ Cmed → ¬ φ.AssignedToHuge β c →
        (φ.classVertexCount c : ℝ) ≤ β * (n : ℝ)) ∧
      (((Cmed ∪ Cdiff ∪ Chuge).card : ℝ) ≤ γ * (n : ℝ) + 32 / β ^ 2) ∧
      Clarge.card ≤ Dparam n ρ := by
  have hn1 : 1 ≤ n := by omega
  have hA' := hA
  obtain ⟨C₁, Cmed, -, -, -, -, -, -, hsing, -⟩ := hA'
  obtain ⟨Cmed', Cdiff, Chuge, Clarge, Cmain, Cbuff, Cfinal, hS12, hvert, h3R, hCl⟩ :=
    exists_S12Colours_typeA 𝓗 hlin φ U hA hγ hβ0 hβn hn1 hr1 hnum
  refine ⟨Cmed', Cdiff, Chuge, Clarge, Cmain, Cbuff, Cfinal, hS12, hsing, ?_, ?_, ?_,
    hvert, h3R, hCl hDlb⟩
  · rw [hU]
    exact Vdeg_plus_subset_Vplus hlin hbig hn2 hεn
  · intro v
    exact mem_Vdeg_pred_iff hlin hbig hn1
  · intro v
    exact mem_Vdeg_plus_iff hlin hbig hn2

/-- **§12, Steps 1--3 (Type B).**  The Type B case: here `U` *is*
`V_+^{(1-ε)}(G)`, the huge colour classes cover at most `δn` vertices (the
extremal bound `(6.7:b)`, used by Step 5), and the same vertex-set facts
hold. -/
theorem s12_step3_typeB {n : ℕ} {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (hbig : ∀ e ∈ 𝓗, 2 ≤ edgeSize e) {r₁ r₀ δ γ₂ γ₁ β γ ρ ε : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)}
    (hB : IsTypeB δ γ₂ γ₁ β r₁ r₀ 𝓗 φ) (hγ₂ : γ₂ ≤ γ) (hγ₁ : γ₁ ≤ γ)
    (hβ0 : 0 < β) (hβn : 8 ≤ β * (n : ℝ)) (hn2 : 2 ≤ n)
    (hr1 : r₁ < β * (n : ℝ) / 4)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (h3 : 3 ≤ (1 - δ) * Real.sqrt (n : ℝ)) (hδ3 : δ < 3 / 10)
    (hγδ : γ₁ ≤ δ) (hβδ : β ≤ δ) (hεn : 3 ≤ ε * (n : ℝ))
    (hnum : (Dparam n ρ : ℝ) + (D'param (Dparam n ρ) γ : ℝ) +
      (2 * γ * (n : ℝ) + 32 / β ^ 2) ≤ (n : ℝ)) :
    ∃ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n),
      IsS12Colours n 𝓗 r₁ φ (Vplus 𝓗 (1 - ε)) r₀ β γ ρ
        Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal ∧
      (∀ c : Fin n, φ.AssignedToHuge β c →
        (φ.classVertexCount c : ℝ) ≤ δ * (n : ℝ)) ∧
      Vn2set 𝓗 ⊆ Vplus 𝓗 (1 - ε) ∧
      (∀ v : Fin n, v ∈ Vn1set 𝓗 ↔ ((n : ℝ) - 1 ≤ (MultiHypergraph.hdeg 𝓗 v : ℝ))) ∧
      (∀ v : Fin n, v ∈ Vn2set 𝓗 ↔ ((n : ℝ) - 2 ≤ (MultiHypergraph.hdeg 𝓗 v : ℝ))) ∧
      (∀ c : Fin n, c ∉ Cmed → ¬ φ.AssignedToHuge β c →
        (φ.classVertexCount c : ℝ) ≤ β * (n : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hB' := hB
  obtain ⟨-, Cmed, -, -, -, hassigned, -⟩ := hB'
  obtain ⟨Cmed', Cdiff, Chuge, Clarge, Cmain, Cbuff, Cfinal, hS12, hvert⟩ :=
    exists_S12Colours_typeB 𝓗 hlin φ hB hγ₂ hγ₁ hβ0 hβn hn1 hr1 hδ0 hδ1 hε0 hε1 h3 hδ3
      hγδ hβδ hnum
  refine ⟨Cmed', Cdiff, Chuge, Clarge, Cmain, Cbuff, Cfinal, hS12, hassigned, ?_, ?_, ?_,
    ?_⟩
  · exact Vdeg_plus_subset_Vplus hlin hbig hn2 hεn
  · intro v
    exact mem_Vdeg_pred_iff hlin hbig hn1
  · intro v
    exact mem_Vdeg_plus_iff hlin hbig hn2
  · exact hvert


/-! ## §12, Step 2: the family `𝓥` of `(def:cv)` -/

/-- **`(def:cv)`.**  The family of vertex sets with respect to which the
reservoir and the absorber of §12 are typical:
`{U, V(𝓗)} ∪ {U ∪ V(φ⁻¹(c)), U ∖ V(φ⁻¹(c)) : c ∈ [n]}`. -/
def cvFinset {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ} (φ : (medLarge 𝓗 r₁).Coloring (Fin n))
    (U : Set (Fin n)) : Finset (Set (Fin n)) :=
  ({U, (Set.univ : Set (Fin n))} ∪
      (Finset.univ : Finset (Fin n)).image (fun c => U ∪ φ.classVertices c)) ∪
    (Finset.univ : Finset (Fin n)).image (fun c => U \ φ.classVertices c)

theorem mem_cvFinset {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} {X : Set (Fin n)} :
    X ∈ cvFinset φ U ↔
      X = U ∨ X = (Set.univ : Set (Fin n)) ∨
        (∃ c : Fin n, X = U ∪ φ.classVertices c) ∨
        ∃ c : Fin n, X = U \ φ.classVertices c := by
  classical
  simp only [cvFinset, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image, Finset.mem_univ, true_and]
  tauto

theorem mem_cvFinset_U {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} : U ∈ cvFinset φ U := by
  rw [mem_cvFinset]; exact Or.inl rfl

theorem mem_cvFinset_univ {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} :
    (Set.univ : Set (Fin n)) ∈ cvFinset φ U := by
  rw [mem_cvFinset]; exact Or.inr (Or.inl rfl)

theorem mem_cvFinset_union {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} (c : Fin n) :
    U ∪ φ.classVertices c ∈ cvFinset φ U := by
  rw [mem_cvFinset]; exact Or.inr (Or.inr (Or.inl ⟨c, rfl⟩))

theorem mem_cvFinset_sdiff {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} (c : Fin n) :
    U \ φ.classVertices c ∈ cvFinset φ U := by
  rw [mem_cvFinset]; exact Or.inr (Or.inr (Or.inr ⟨c, rfl⟩))

/-- `|𝓥| ≤ 2n + 2` (the paper's `|𝓥| ≤ 2n+2`, as needed by Property 11.1). -/
theorem cvFinset_card_le {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) (U : Set (Fin n)) :
    (cvFinset φ U).card ≤ 2 * n + 2 := by
  classical
  have h1 : ({U, (Set.univ : Set (Fin n))} : Finset (Set (Fin n))).card ≤ 2 := by
    have := Finset.card_insert_le U ({Set.univ} : Finset (Set (Fin n)))
    simp only [Finset.card_singleton] at this
    omega
  have h2 : ((Finset.univ : Finset (Fin n)).image (fun c => U ∪ φ.classVertices c)).card ≤ n :=
    calc ((Finset.univ : Finset (Fin n)).image (fun c => U ∪ φ.classVertices c)).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by rw [Finset.card_univ, Fintype.card_fin]
  have h3 : ((Finset.univ : Finset (Fin n)).image (fun c => U \ φ.classVertices c)).card ≤ n :=
    calc ((Finset.univ : Finset (Fin n)).image (fun c => U \ φ.classVertices c)).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by rw [Finset.card_univ, Fintype.card_fin]
  have h4 := Finset.card_union_le ({U, (Set.univ : Set (Fin n))} ∪
    (Finset.univ : Finset (Fin n)).image (fun c => U ∪ φ.classVertices c))
    ((Finset.univ : Finset (Fin n)).image (fun c => U \ φ.classVertices c))
  have h5 := Finset.card_union_le ({U, (Set.univ : Set (Fin n))} : Finset (Set (Fin n)))
    ((Finset.univ : Finset (Fin n)).image (fun c => U ∪ φ.classVertices c))
  simp only [cvFinset]
  omega

/-! ## §12, Step 4: the output package and its instantiation -/

/-- **The output of §12 Step 4** (`step:diff`): the matchings `𝓜_diff` extending
the (at most one) difficult colour class, the truncated absorber
`R₁ = R_abs ∖ ⋃𝓜_diff` and the defect set `S₁`, with D1, `(eq:R1abs)` and
`(eq:boundS1)`. -/
structure IsS12Step4 {n : ℕ} (𝓗 : Hypergraph (Fin n)) {r₁ : ℝ}
    (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) (U S : Set (Fin n)) (Cdiff : Finset (Fin n))
    (R_abs R₁ : Hypergraph (Fin n)) (S₁ : Set (Fin n)) (Mdiff : Fin n → Set 𝓗)
    (𝓥 : Set (Set (Fin n))) (ρ_abs γ ξ : ℝ) : Prop where
  /-- the matchings are supported on `C_diff`. -/
  hMdiff_supp : ∀ c ∉ Cdiff, Mdiff c = ∅
  /-- `M_c ⊇ φ⁻¹(c)`. -/
  hMdiff_ext : ∀ c ∈ Cdiff, subFam (𝓖 := medLarge 𝓗 r₁) (φ.colorClass c) ⊆ Mdiff c
  /-- the added edges are edges of `G`. -/
  hMdiff_add : ∀ c ∈ Cdiff, ∀ e ∈ Mdiff c,
      e ∉ subFam (𝓖 := medLarge 𝓗 r₁) (φ.colorClass c) → (e : Set (Fin n)) ∈ 𝓗.pow2
  /-- every `M_c` is a matching. -/
  hMdiff_mat : ∀ c, IsMatching 𝓗 (Mdiff c)
  /-- D1: every vertex of `V^{(n-1)}(𝓗)` is covered. -/
  hMdiff_cov : ∀ c ∈ Cdiff, Covers (Mdiff c) (Vdeg 𝓗 (n - 1))
  /-- D1: all but five vertices of `V^{(n-2)}(𝓗)` are covered. -/
  hMdiff_five : ∀ c ∈ Cdiff, (Vdeg 𝓗 (n - 2) \ matchVert (Mdiff c)).ncard ≤ 5
  /-- `(def:r1s1)`: `R₁ = R_abs ∖ ⋃𝓜_diff`. -/
  hR₁_eq : R₁ = R_abs \ famUnionIdx Mdiff
  /-- `(def:r1s1)`: `S₁ = S ∖ ⋃_c (V^{(n-2)}(𝓗) ∖ V(M_c))`. -/
  hS₁_eq : S₁ = S \ (⋃ c ∈ (Cdiff : Set (Fin n)),
    (Vdeg 𝓗 (n - 2) \ matchVert (Mdiff c)))
  /-- `S₁ ⊆ S`. -/
  hS₁_sub : S₁ ⊆ S
  /-- `(eq:R1abs)`: `R₁` is a `(ρ_abs, 3γ/2, ξ)`-absorber. -/
  hR₁_abs : IsAbsorber (incidentTwo 𝓗 U) R₁ 𝓥 ρ_abs (3 * γ / 2) ξ
  /-- `(eq:boundS1)`: `S₁` loses at most five vertices. -/
  hS₁_big : (S.ncard : ℝ) - 5 ≤ (S₁.ncard : ℝ)

/-- **§12, Step 4, instantiated.**  From the Step-3 colour sets (Type A), the
difficult-edge absorption margins `DiffMargins n β`, the absorber `R_abs` of
§11 and the numerical condition `10ξ + 1/n ≤ 3γ/2`, either `χ'(𝓗) ≤ n` or the
Step-4 package `IsS12Step4` is produced. -/
theorem s12_step4_inst {n : ℕ} {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (hbig : ∀ f ∈ 𝓗, 2 ≤ f.ncard) {r₁ r₀ σ γ₁ β γ ρ ρ_abs ξ ε : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U S : Set (Fin n)}
    (hU : U = Vplus 𝓗 (1 - ε))
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (hS12 : IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal)
    (hA : IsTypeA σ γ₁ β r₁ r₀ 𝓗 φ) (hm : DiffMargins n β)
    (hn : 1 ≤ n) (hξγ : 10 * ξ + 1 / (n : ℝ) ≤ 3 * γ / 2)
    {R_abs : Hypergraph (Fin n)} {𝓥 : Set (Set (Fin n))}
    (hRabs : IsAbsorber (incidentTwo 𝓗 U) R_abs 𝓥 ρ_abs (10 * ξ) ξ) :
    𝓗.chromaticIndex ≤ n ∨
      ∃ (Mdiff : Fin n → Set 𝓗) (R₁ : Hypergraph (Fin n)) (S₁ : Set (Fin n)),
        IsS12Step4 𝓗 φ U S Cdiff R_abs R₁ S₁ Mdiff 𝓥 ρ_abs γ ξ := by
  rcases s12_step4 (ε := ε) hlin hbig hm hS12 hA hRabs hξγ hn with h | ⟨Mdiff, R₁, S₁, h1, h2, h3,
    h4, h5, h6, h7, h8, h9, h10, h11⟩
  · exact Or.inl h
  · exact Or.inr ⟨Mdiff, R₁, S₁, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-! ## §12, Step 2: the reservoir and the absorber (Property 11.1, Lemma 11.2) -/

/-- **§12, Step 2 (Type A₁).**  Property 11.1
(`exists_pseudoReservoir_eventually`) produces a pseudorandom reservoir
`R_res ⊆ E(G)` with the absorber `R_abs = R_res ∩ G'` for the family `𝓥` of
`(def:cv)`. -/
theorem s12_step2_typeA1 {ρ ξ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hξ0 : 0 < ξ) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (𝓗 : Hypergraph (Fin n)), 𝓗.IsLinear →
      ∀ {r₁ : ℝ} (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) (U : Set (Fin n)) {ε : ℝ},
        U = Vplus 𝓗 (1 - ε) → 1 ≤ n →
        ((cvFinset φ U).card : ℝ) ≤ (n : ℝ) ^ Real.log n →
        ∃ R_res R_abs : Hypergraph (Fin n),
          IsReservoirTypeA1 𝓗 R_res (cvFinset φ U : Set (Set (Fin n))) ρ ξ ε ∧
          IsAbsorber (incidentTwo 𝓗 U) R_abs (cvFinset φ U : Set (Set (Fin n))) ρ ξ ξ ∧
          R_abs ⊆ R_res ∧ R_abs ⊆ 𝓗.pow2 := by
  obtain ⟨N, hN⟩ := exists_pseudoReservoir_eventually hρ0 hρ1 hξ0
  refine ⟨N, ?_⟩
  intro n hnle 𝓗 hlin r₁ φ U ε hU hn hVcard
  obtain ⟨R, hRpow, habs, -, hdeg⟩ := hN n hnle hn 𝓗 hlin (incidentTwo 𝓗 U)
    (incidentTwo_subset_pow2 𝓗 U) (cvFinset φ U) hVcard
  have hA1 : IsReservoirTypeA1 𝓗 R (cvFinset φ U : Set (Set (Fin n))) ρ ξ ε := by
    refine ⟨hRpow, ?_⟩
    rw [← hU]
    exact ⟨hdeg, habs⟩
  exact ⟨R, R ∩ incidentTwo 𝓗 U, hA1, habs, Set.inter_subset_left,
    Set.inter_subset_left.trans hRpow⟩

/-- **§12, Step 2 (Type A₂).**  Property 11.1 gives a `(ρ/2, ξ, ξ)`-absorber
`R_abs` that is lower `(ρ/2, ξ, G')`-regular, and Lemma 11.2
(`exists_regularising_reservoir`) augments it with a regularising part `R_reg`. -/
theorem s12_step2_typeA2 {ρ ξ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hξ0 : 0 < ξ) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (𝓗 : Hypergraph (Fin n)), 𝓗.IsLinear →
      ∀ {r₁ : ℝ} (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) (U : Set (Fin n)) {ε : ℝ},
        U = Vplus 𝓗 (1 - ε) → 1 ≤ n → 0 < ε → IsFull 𝓗 ρ ε →
        ((cvFinset φ U).card : ℝ) ≤ (n : ℝ) ^ Real.log n →
        (Set.univ : Set (Fin n)) ∈ (cvFinset φ U : Set (Set (Fin n))) →
        1 ≤ ε * n → 1 ≤ 5 * ε * n → ρ ≤ 1 / 100 → 25 ≤ ρ * n →
        20 * ε ≤ ρ ^ 2 → 20 * ε + ξ ≤ ρ / 2 → ξ ≤ ρ / 2 → 2 ≤ ξ * n →
        ∃ R_res R_abs : Hypergraph (Fin n),
          IsReservoirTypeA2 𝓗 R_res (cvFinset φ U : Set (Set (Fin n))) ρ ξ ε ∧
          IsAbsorber (incidentTwo 𝓗 U) R_abs (cvFinset φ U : Set (Set (Fin n))) (ρ / 2) ξ ξ ∧
          R_abs ⊆ R_res ∧ R_abs ⊆ 𝓗.pow2 := by
  obtain ⟨N, hN⟩ := exists_pseudoReservoir_eventually (ρ := ρ / 2) (ξ := ξ)
    (by linarith) (by linarith) hξ0
  refine ⟨N, ?_⟩
  intro n hnle 𝓗 hlin r₁ φ U ε hU hn hε0 hfull hVcard hVuniv hεn h5εn hρ100 hρn hερ h20 hξε
    hξn
  obtain ⟨R, hRpow, habs, hlow, -⟩ := hN n hnle hn 𝓗 hlin (incidentTwo 𝓗 U)
    (incidentTwo_subset_pow2 𝓗 U) (cvFinset φ U) hVcard
  have habs' : IsAbsorber (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) (R ∩ incidentTwo 𝓗 U)
      (cvFinset φ U : Set (Set (Fin n))) (ρ / 2) ξ ξ := by
    rw [← hU]; exact habs
  have hlow' : LowerRegular (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) (R ∩ incidentTwo 𝓗 U)
      (ρ / 2) ξ := by
    rw [← hU]; exact hlow
  have hpow' : R ∩ incidentTwo 𝓗 U ⊆ 𝓗.pow2 := Set.inter_subset_left.trans hRpow
  obtain ⟨Rreg, hRregpow, hdisj, hreg⟩ :=
    exists_regularising_reservoir gfactorStatement 𝓗 (R ∩ incidentTwo 𝓗 U)
      (cvFinset φ U : Set (Set (Fin n))) hVuniv hε0 (by linarith) hξ0
      hfull habs' hn hεn h5εn hρ100 hρn hερ h20 hξε hξn
  have hA2 : IsReservoirTypeA2 𝓗 ((R ∩ incidentTwo 𝓗 U) ∪ Rreg)
      (cvFinset φ U : Set (Set (Fin n))) ρ ξ ε :=
    ⟨Set.union_subset hpow' hRregpow, R ∩ incidentTwo 𝓗 U, Rreg, rfl, habs', hlow', hreg⟩
  exact ⟨(R ∩ incidentTwo 𝓗 U) ∪ Rreg, R ∩ incidentTwo 𝓗 U, hA2, habs,
    Set.subset_union_left, hpow'⟩

/-- **§12, Step 2 (Type B).**  Property 11.1 produces the absorber `R_res` of
Type B (note that in the paper `R_res = R_abs` in this case). -/
theorem s12_step2_typeB {ρ ξ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hξ0 : 0 < ξ) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (𝓗 : Hypergraph (Fin n)), 𝓗.IsLinear →
      ∀ {r₁ : ℝ} (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) (U : Set (Fin n)) {ε : ℝ},
        U = Vplus 𝓗 (1 - ε) → 1 ≤ n →
        ((cvFinset φ U).card : ℝ) ≤ (n : ℝ) ^ Real.log n →
        ∃ R_res R_abs : Hypergraph (Fin n),
          IsReservoirTypeB 𝓗 R_res (cvFinset φ U : Set (Set (Fin n))) ρ ξ ε ∧
          IsAbsorber (incidentTwo 𝓗 U) R_abs (cvFinset φ U : Set (Set (Fin n))) ρ ξ ξ ∧
          R_abs ⊆ R_res ∧ R_abs ⊆ 𝓗.pow2 := by
  obtain ⟨N, hN⟩ := exists_pseudoReservoir_eventually hρ0 hρ1 hξ0
  refine ⟨N, ?_⟩
  intro n hnle 𝓗 hlin r₁ φ U ε hU hn hVcard
  obtain ⟨R, hRpow, habs, -, -⟩ := hN n hnle hn 𝓗 hlin (incidentTwo 𝓗 U)
    (incidentTwo_subset_pow2 𝓗 U) (cvFinset φ U) hVcard
  have hB : IsReservoirTypeB 𝓗 (R ∩ incidentTwo 𝓗 U)
      (cvFinset φ U : Set (Set (Fin n))) ρ ξ ε := by
    rw [IsReservoirTypeB, ← hU]; exact habs
  exact ⟨R ∩ incidentTwo 𝓗 U, R ∩ incidentTwo 𝓗 U, hB, habs, subset_rfl,
    Set.inter_subset_left.trans hRpow⟩

end

end ErdosFaberLovaszConjecture
