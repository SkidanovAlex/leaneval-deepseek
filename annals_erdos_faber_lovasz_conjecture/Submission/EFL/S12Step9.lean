import Submission.EFL.S12Step6
import Submission.EFL.S12Step7
import Submission.EFL.S12Step8

/-!
# §12, Step 9 (`step:step9`): the bounds on the degrees in `𝓗_final`

This module formalises the counting part of **Step 9** of the proof of
Theorem 1.1.

Let `𝓜_prev^* = {M_c : c ∈ C_prev}` be the family of matchings of `𝓗_reg`
assembled from Steps 4--7, split as `𝓜_diff ∪ 𝓜_rest`, and let

`m(w) = |{c : w ∉ V(M_c)}|`

be the number of matchings of `𝓜_prev^*` that do *not* cover `w`.  From the
covering properties of the matchings -- `𝓜_diff` covers `V^{(n-1)}(𝓗)` (D1),
the remaining matchings have nearly-perfect coverage of `U` with defects in
`S₁` and perfect coverage of `U` when `|U| ≤ (1-10ε)n` -- the paper derives

* **mbound 1** (`(eqn:mbound_1)`)  `m(u) ≤ 1` for `u ∈ U ∖ S₁` and
  `m(v) = 0` for `v ∈ V^{(n-1)}(𝓗) ∖ S₁`;
* **mbound 2** (`(eqn:mbound_2)`)  `m(u) ≤ 2` for `u ∈ U ∖ V^{(n-2)}(𝓗)` and
  `m(v) ≤ 1` for `v ∈ V^{(n-2)}(𝓗)`;
* **mbound 3** (`(eqn:mbound_3)`)  if `|U| ≤ (1-10ε)n` then `m(u) ≤ 1` for
  `u ∈ U ∖ V^{(n-1)}(𝓗)` and `m(v) = 0` for `v ∈ V^{(n-1)}(𝓗)`.

Together with the degree identity `(eqn:deg_h_final)`
(`s12_deg_h_final` in `S12Step8.lean`) these give the degree bounds
UC1--UC4 of the final step.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- **§12, Step 9, the `m(w)`-bounds.**  Let `M : ι → Set (Set (Fin n))` be the
family of matchings `𝓜_prev^*`, let `ιdiff` index the subfamily `𝓜_diff`, and
suppose that

* `𝓜_diff` covers `V^{(n-1)}(𝓗)` (and, together with the definition of `S₁`,
  covers `V^{(n-2)}(𝓗) ∩ S₁`);
* apart from `𝓜_diff`, the defects of the coverage of `U` lie in `S₁`, and
  every vertex of `U` is missed by at most one matching of `𝓜_rest`;
* when `|U| ≤ (1-10ε)n` the matchings of `𝓜_rest` cover `U` perfectly.

Then the three bounds `(eqn:mbound_1)`--`(eqn:mbound_3)` hold. -/
theorem s12_mbound {ι : Type*} [Fintype ι] {M : ι → Set (Set (Fin n))}
    {U S₁ : Set (Fin n)} {ε : ℝ} (ιdiff : Set ι) (Vn1 Vn2 : Set (Fin n))
    (hdiff1 : ιdiff.ncard ≤ 1)
    (hdiffVn1 : ∀ i ∈ ιdiff, Vn1 ⊆ famVert (M i))
    (hdiffVn2 : ∀ i ∈ ιdiff, Vn2 ∩ S₁ ⊆ famVert (M i))
    (hrestcov : ∀ i ∉ ιdiff, U \ famVert (M i) ⊆ S₁)
    (hnp : ∀ u ∈ U, (({i | i ∉ ιdiff ∧ u ∉ famVert (M i)} : Set ι)).ncard ≤ 1)
    (hperf : (U.ncard : ℝ) ≤ (1 - 10 * ε) * (n : ℝ) → ∀ i ∉ ιdiff, U ⊆ famVert (M i))
    (hVn1Vn2 : Vn1 ⊆ Vn2) (hVn2U : Vn2 ⊆ U) :
    (∀ u ∈ U \ S₁, (({i | u ∉ famVert (M i)} : Set ι)).ncard ≤ 1) ∧
    (∀ v ∈ Vn1 \ S₁, (({i | v ∉ famVert (M i)} : Set ι)).ncard = 0) ∧
    (∀ u ∈ U \ Vn2, (({i | u ∉ famVert (M i)} : Set ι)).ncard ≤ 2) ∧
    (∀ v ∈ Vn2, (({i | v ∉ famVert (M i)} : Set ι)).ncard ≤ 1) ∧
    (((U.ncard : ℝ) ≤ (1 - 10 * ε) * (n : ℝ)) →
      (∀ u ∈ U \ Vn1, (({i | u ∉ famVert (M i)} : Set ι)).ncard ≤ 1) ∧
      (∀ v ∈ Vn1, (({i | v ∉ famVert (M i)} : Set ι)).ncard = 0)) := by
  have hVn1U : Vn1 ⊆ U := hVn1Vn2.trans hVn2U
  -- (mbound 1, first part)
  have h1 : ∀ u ∈ U \ S₁, (({i | u ∉ famVert (M i)} : Set ι)).ncard ≤ 1 := by
    intro u hu
    have hsub : ({i | u ∉ famVert (M i)} : Set ι) ⊆ ιdiff := by
      intro i hi
      by_contra hid
      exact hu.2 (hrestcov i hid ⟨hu.1, hi⟩)
    exact le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) hdiff1
  -- (mbound 1, second part)
  have h2 : ∀ v ∈ Vn1 \ S₁, (({i | v ∉ famVert (M i)} : Set ι)).ncard = 0 := by
    intro v hv
    have hempty : ({i | v ∉ famVert (M i)} : Set ι) = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨i, hi⟩
      by_cases hid : i ∈ ιdiff
      · exact hi (hdiffVn1 i hid hv.1)
      · exact hv.2 (hrestcov i hid ⟨hVn1U hv.1, hi⟩)
    rw [hempty, Set.ncard_empty]
  -- (mbound 2, first part)
  have h3 : ∀ u ∈ U \ Vn2, (({i | u ∉ famVert (M i)} : Set ι)).ncard ≤ 2 := by
    intro u hu
    have hsub : ({i | u ∉ famVert (M i)} : Set ι) ⊆
        ιdiff ∪ {i | i ∉ ιdiff ∧ u ∉ famVert (M i)} := by
      intro i hi
      by_cases hid : i ∈ ιdiff
      · exact Or.inl hid
      · exact Or.inr ⟨hid, hi⟩
    calc (({i | u ∉ famVert (M i)} : Set ι)).ncard
        ≤ (ιdiff ∪ {i | i ∉ ιdiff ∧ u ∉ famVert (M i)} : Set ι).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ιdiff.ncard + (({i | i ∉ ιdiff ∧ u ∉ famVert (M i)} : Set ι)).ncard :=
          Set.ncard_union_le _ _
      _ ≤ 1 + 1 := Nat.add_le_add hdiff1 (hnp u hu.1)
      _ = 2 := rfl
  -- (mbound 2, second part)
  have h4 : ∀ v ∈ Vn2, (({i | v ∉ famVert (M i)} : Set ι)).ncard ≤ 1 := by
    intro v hv
    by_cases hvS : v ∈ S₁
    · -- the `𝓜_diff`-matchings cover `v`; at most one of the rest misses it
      have hsub : ({i | v ∉ famVert (M i)} : Set ι) ⊆
          {i | i ∉ ιdiff ∧ v ∉ famVert (M i)} := by
        intro i hi
        refine ⟨?_, hi⟩
        by_contra hid
        exact hi (hdiffVn2 i hid ⟨hv, hvS⟩)
      exact le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) (hnp v (hVn2U hv))
    · -- no matching of the rest misses `v`; at most one of `𝓜_diff` does
      have hsub : ({i | v ∉ famVert (M i)} : Set ι) ⊆ ιdiff := by
        intro i hi
        by_contra hid
        exact hvS (hrestcov i hid ⟨hVn2U hv, hi⟩)
      exact le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) hdiff1
  -- (mbound 3)
  have h5 : ((U.ncard : ℝ) ≤ (1 - 10 * ε) * (n : ℝ)) →
      (∀ u ∈ U \ Vn1, (({i | u ∉ famVert (M i)} : Set ι)).ncard ≤ 1) ∧
      (∀ v ∈ Vn1, (({i | v ∉ famVert (M i)} : Set ι)).ncard = 0) := by
    intro hUc
    constructor
    · intro u hu
      have hsub : ({i | u ∉ famVert (M i)} : Set ι) ⊆ ιdiff := by
        intro i hi
        by_contra hid
        exact hi (hperf hUc i hid hu.1)
      exact le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) hdiff1
    · intro v hv
      have hempty : ({i | v ∉ famVert (M i)} : Set ι) = ∅ := by
        rw [← Set.not_nonempty_iff_eq_empty]
        rintro ⟨i, hi⟩
        by_cases hid : i ∈ ιdiff
        · exact hi (hdiffVn1 i hid hv)
        · exact hi (hperf hUc i hid (hVn1U hv))
      rw [hempty, Set.ncard_empty]
  exact ⟨h1, h2, h3, h4, h5⟩


/-- **§12, Step 9, UC2--UC4.**  The degree bounds for `𝓗_final` on `U`, obtained
by combining the identity `(eqn:deg_h_final)` with the `m(w)`-bounds
`(eqn:mbound_1)`--`(eqn:mbound_3)`.

`Vn1`/`Vn2` are `V^{(n-1)}(𝓗)`/`V^{(n-2)}(𝓗)`, characterised by the degree
hypotheses `hVn1`/`hVn2`; `hdg_le` is the fact that the degree of a vertex of a
linear hypergraph is at most `n-1`. -/
theorem s12_uc {ι : Type*} [Fintype ι] {M : ι → Set (Set (Fin n))}
    {𝓗 𝓗fin : Hypergraph (Fin n)} {U : Set (Fin n)} (Cfinal : Finset (Fin n))
    (Vn1 Vn2 : Set (Fin n))
    (hdeg : ∀ w : Fin n, (MultiHypergraph.hdeg 𝓗fin w : ℝ) ≤
      (Cfinal.card : ℝ) + (({i | w ∉ famVert (M i)} : Set ι)).ncard -
        min ((n : ℝ) - (MultiHypergraph.hdeg 𝓗 w : ℝ)) 3)
    (hVn1 : ∀ w : Fin n, w ∈ Vn1 ↔ (n : ℝ) - 1 ≤ (MultiHypergraph.hdeg 𝓗 w : ℝ))
    (hVn2 : ∀ w : Fin n, w ∈ Vn2 ↔ (n : ℝ) - 2 ≤ (MultiHypergraph.hdeg 𝓗 w : ℝ))
    (hdg_le : ∀ w : Fin n, (MultiHypergraph.hdeg 𝓗 w : ℝ) ≤ (n : ℝ) - 1)
    (hm2 : ∀ u ∈ U \ Vn2, (({i | u ∉ famVert (M i)} : Set ι)).ncard ≤ 2)
    (hm2' : ∀ v ∈ Vn2, (({i | v ∉ famVert (M i)} : Set ι)).ncard ≤ 1) :
    (∀ w ∈ U, w ∉ Vn1 → (MultiHypergraph.hdeg 𝓗fin w : ℝ) ≤ (Cfinal.card : ℝ) - 1) ∧
    (∀ w ∈ Vn1, (MultiHypergraph.hdeg 𝓗fin w : ℝ) ≤ (Cfinal.card : ℝ)) ∧
    ((∀ v ∈ Vn1, (({i | v ∉ famVert (M i)} : Set ι)).ncard = 0) →
      ∀ w ∈ Vn1, (MultiHypergraph.hdeg 𝓗fin w : ℝ) ≤ (Cfinal.card : ℝ) - 1) := by
  -- integrality: `¬(n-1 ≤ d)` for a natural `d` means `d ≤ n-2`
  have hint1 : ∀ w : Fin n, w ∉ Vn1 → (MultiHypergraph.hdeg 𝓗 w : ℝ) ≤ (n : ℝ) - 2 := by
    intro w hw
    have h1 : ¬ ((n : ℝ) - 1 ≤ (MultiHypergraph.hdeg 𝓗 w : ℝ)) :=
      fun h => hw ((hVn1 w).mpr h)
    have h2 : MultiHypergraph.hdeg 𝓗 w + 1 < n := by
      have : (MultiHypergraph.hdeg 𝓗 w : ℝ) + 1 < (n : ℝ) := by linarith
      exact_mod_cast this
    have h3 : MultiHypergraph.hdeg 𝓗 w ≤ n - 2 := by omega
    have h4 : ((MultiHypergraph.hdeg 𝓗 w : ℕ) : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := by
      exact_mod_cast h3
    have h5 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
      rw [Nat.cast_sub (show 2 ≤ n by omega)]
      norm_num
    linarith
  have hint2 : ∀ w : Fin n, w ∉ Vn2 → (MultiHypergraph.hdeg 𝓗 w : ℝ) ≤ (n : ℝ) - 3 := by
    intro w hw
    have h1 : ¬ ((n : ℝ) - 2 ≤ (MultiHypergraph.hdeg 𝓗 w : ℝ)) :=
      fun h => hw ((hVn2 w).mpr h)
    have h2 : MultiHypergraph.hdeg 𝓗 w + 2 < n := by
      have : (MultiHypergraph.hdeg 𝓗 w : ℝ) + 2 < (n : ℝ) := by linarith
      exact_mod_cast this
    have h3 : MultiHypergraph.hdeg 𝓗 w ≤ n - 3 := by omega
    have h4 : ((MultiHypergraph.hdeg 𝓗 w : ℕ) : ℝ) ≤ ((n - 3 : ℕ) : ℝ) := by
      exact_mod_cast h3
    have h5 : ((n - 3 : ℕ) : ℝ) = (n : ℝ) - 3 := by
      rw [Nat.cast_sub (show 3 ≤ n by omega)]
      norm_num
    linarith
  have hVn1Vn2 : Vn1 ⊆ Vn2 := by
    intro w hw
    exact (hVn2 w).mpr (by have := (hVn1 w).mp hw; linarith)
  constructor
  · -- UC2
    intro w hwU hwV1
    have h := hdeg w
    by_cases hwV2 : w ∈ Vn2
    · have hm : (({i | w ∉ famVert (M i)} : Set ι)).ncard ≤ 1 := hm2' w hwV2
      have hm' : ((({i | w ∉ famVert (M i)} : Set ι)).ncard : ℝ) ≤ 1 := by exact_mod_cast hm
      have hle := hint1 w hwV1
      have hmin : (2 : ℝ) ≤
          min ((n : ℝ) - (MultiHypergraph.hdeg 𝓗 w : ℝ)) 3 := le_min (by linarith) (by norm_num)
      linarith
    · have hm := hm2 w (by exact ⟨hwU, hwV2⟩)
      have hm' : ((({i | w ∉ famVert (M i)} : Set ι)).ncard : ℝ) ≤ 2 := by exact_mod_cast hm
      have hle := hint2 w hwV2
      have hmin : (3 : ℝ) ≤
          min ((n : ℝ) - (MultiHypergraph.hdeg 𝓗 w : ℝ)) 3 := le_min (by linarith) le_rfl
      linarith
  constructor
  · -- UC3 (first part)
    intro w hw
    have hm := hm2' w (hVn1Vn2 hw)
    have hm' : ((({i | w ∉ famVert (M i)} : Set ι)).ncard : ℝ) ≤ 1 := by exact_mod_cast hm
    have hmin : (1 : ℝ) ≤
        min ((n : ℝ) - (MultiHypergraph.hdeg 𝓗 w : ℝ)) 3 := by
      refine le_min ?_ (by norm_num)
      have := hdg_le w
      linarith
    have := hdeg w
    linarith
  · -- UC4 (given that no vertex of `Vn1` is missed)
    intro hm0 w hw
    have hm := hm0 w hw
    have hm' : ((({i | w ∉ famVert (M i)} : Set ι)).ncard : ℝ) = 0 := by exact_mod_cast hm
    have hmin : (1 : ℝ) ≤
        min ((n : ℝ) - (MultiHypergraph.hdeg 𝓗 w : ℝ)) 3 := by
      refine le_min ?_ (by norm_num)
      have := hdg_le w
      linarith
    have := hdeg w
    linarith


/-! ## No singleton edges of `𝓗_reg` at a vertex of `U` -/

/-- For `u ∈ U = V_+^{(1-ε)}(G)` the multi-hypergraph `𝓗_reg` has no singleton
edge at `u`: its degree `d_𝓗(u) ≥ d_G(u) ≥ (1-ε)n ≥ n - 3`.  Consequently no
edge of a matching of `𝓗_reg` covering `u` is a singleton. -/
theorem singles_regHypergraph_eq_zero_of_mem_Vplus (𝓗 : Hypergraph (Fin n)) {ε : ℝ}
    (hεn : ε * (n : ℝ) ≤ 3) {u : Fin n} (hu : u ∈ Vplus 𝓗 (1 - ε)) :
    (MultiHypergraph.regHypergraph 𝓗).singles u = 0 := by
  rw [MultiHypergraph.singles_regHypergraph]
  have h1 : (1 - ε) * (n : ℝ) ≤ (degAt 𝓗.pow2 u : ℝ) := hu
  have h2 : (degAt 𝓗.pow2 u : ℝ) ≤ (MultiHypergraph.hdeg 𝓗 u : ℝ) := by
    have := degAt_le_hdeg 𝓗.pow2 u
    have h3 := hdeg_mono (powFam_subset 𝓗 2) u
    have h4 : (degAt 𝓗.pow2 u : ℝ) ≤ (MultiHypergraph.hdeg 𝓗.pow2 u : ℝ) := by
      exact_mod_cast this
    have h5 : (MultiHypergraph.hdeg 𝓗.pow2 u : ℝ) ≤ (MultiHypergraph.hdeg 𝓗 u : ℝ) := by
      exact_mod_cast h3
    linarith
  have h6 : (n : ℝ) - 3 ≤ (MultiHypergraph.hdeg 𝓗 u : ℝ) := by linarith
  by_cases hn : n ≤ 3
  · have hz : n - 3 = 0 := by omega
    rw [hz, Nat.zero_sub]
  · rw [not_le] at hn
    have hcast : ((n - 3 : ℕ) : ℝ) ≤ ((MultiHypergraph.hdeg 𝓗 u : ℕ) : ℝ) := by
      have hcs : ((n - 3 : ℕ) : ℝ) = (n : ℝ) - 3 := by
        rw [Nat.cast_sub (show 3 ≤ n by omega)]
        norm_num
      linarith
    have h7 : n - 3 ≤ MultiHypergraph.hdeg 𝓗 u := by exact_mod_cast hcast
    exact Nat.sub_eq_zero_of_le h7

/-- For `u ∈ U`, the singleton `{u}` is not an edge of `𝓗_reg`. -/
theorem singleton_notMem_edgeSet_regHypergraph (𝓗 : Hypergraph (Fin n)) {ε : ℝ}
    (hbig : ∀ f ∈ 𝓗, 2 ≤ edgeSize f)
    (hεn : ε * (n : ℝ) ≤ 3) {u : Fin n} (hu : u ∈ Vplus 𝓗 (1 - ε)) :
    ({u} : Set (Fin n)) ∉ (MultiHypergraph.regHypergraph 𝓗).edgeSet := by
  intro hmem
  rw [MultiHypergraph.mem_edgeSet] at hmem
  rcases hmem with h1 | ⟨v, hv, hv'⟩
  · have h2 := hbig {u} h1
    rw [edgeSize_eq_ncard, Set.ncard_singleton] at h2
    omega
  · have hvu : v = u := Set.singleton_eq_singleton_iff.mp hv.symm
    rw [hvu, singles_regHypergraph_eq_zero_of_mem_Vplus 𝓗 hεn hu] at hv'
    exact absurd hv' (by norm_num)


/-! ## Glue lemmas for assembling `𝓜_prev` from the matchings of Steps 4--7 -/

theorem famOf_union {𝓗 : Hypergraph (Fin n)} (M M' : Set 𝓗) :
    famOf (M ∪ M') = famOf M ∪ famOf M' := by
  ext e
  simp only [mem_famOf, Set.mem_union]
  constructor
  · rintro ⟨e', he' | he', heq⟩
    · exact Or.inl ⟨e', he', heq⟩
    · exact Or.inr ⟨e', he', heq⟩
  · rintro (⟨e', he', heq⟩ | ⟨e', he', heq⟩)
    · exact ⟨e', Or.inl he', heq⟩
    · exact ⟨e', Or.inr he', heq⟩

/-- The union of two matchings with pairwise disjoint edges is a matching. -/
theorem IsMatching.union {𝓗 : Hypergraph (Fin n)} {M M' : Set 𝓗}
    (hM : IsMatching 𝓗 M) (hM' : IsMatching 𝓗 M')
    (h : ∀ e ∈ M, ∀ e' ∈ M', Disjoint (e : Set (Fin n)) (e' : Set (Fin n))) :
    IsMatching 𝓗 (M ∪ M') := by
  rw [IsMatching] at hM hM' ⊢
  intro e₁ he₁ e₂ he₂ hne
  rw [Set.mem_union] at he₁ he₂
  rcases he₁ with h1 | h1 <;> rcases he₂ with h2 | h2
  · exact hM h1 h2 hne
  · exact h e₁ h1 e₂ h2
  · exact (h e₂ h2 e₁ h1).symm
  · exact hM' h1 h2 hne

/-- Two disjoint families of edges of `𝓗` are edge-disjoint as families of
vertex sets. -/
theorem edgeDisjointFam_famOf_of_disjoint {𝓗 : Hypergraph (Fin n)} {M M' : Set 𝓗}
    (h : Disjoint M M') : EdgeDisjointFam (famOf M) (famOf M') := by
  rw [EdgeDisjointFam]
  exact Set.disjoint_of_subset_left (fun e he => he.1)
    (Set.disjoint_of_subset_right (fun e he => he.1) (disjoint_famOf h))


/-! ## UC1: the reservoir degree bound outside `U` -/

/-- **§12, Step 9 (UC1), reservoir estimate.**  If `w ∉ U = V_+^{(1-ε)}(G)`
then the degree of `w` in the reservoir `R_res` is at most
`ρ(1-ε)n + ξn`: for a reservoir of Type A₁ this is the pseudorandomness of
`R_res`, for Type A₂ it is the second half of the regularising property, and
for Type B it is the typicality of `R_res` together with the fact that the
`G'`-neighbourhood of `w` is contained in its `G`-neighbourhood when
`w ∉ U`. -/
theorem degAt_Rres_le_of_notMem_Vplus {𝓗 R_res : Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {ρ ξ ε : ℝ} (hρ0 : 0 ≤ ρ) (hn : 0 < n)
    (hres : IsReservoirTypeA1 𝓗 R_res 𝓥 ρ ξ ε ∨ IsReservoirTypeA2 𝓗 R_res 𝓥 ρ ξ ε ∨
      (IsReservoirTypeB 𝓗 R_res 𝓥 ρ ξ ε ∧ 2 * ρ * ((n : ℝ) - 1) + 1 ≤ ε * (n : ℝ)))
    (hV : (Set.univ : Set (Fin n)) ∈ 𝓥)
    {w : Fin n} (hw : w ∉ Vplus 𝓗 (1 - ε)) :
    (degAt R_res w : ℝ) ≤ ρ * (1 - ε) * (n : ℝ) + ξ * (n : ℝ) := by
  have hw' : (degAt 𝓗.pow2 w : ℝ) < (1 - ε) * (n : ℝ) := by
    have h1 : ¬ ((1 - ε) * (n : ℝ) ≤ (degAt 𝓗.pow2 w : ℝ)) := hw
    exact not_le.mp h1
  rcases hres with h | h | h
  · -- Type A₁
    obtain ⟨-, hps, -⟩ := h
    have h2 := hps w
    rw [abs_le] at h2
    have h3 : (degAt R_res w : ℝ) ≤ ρ * (degAt 𝓗.pow2 w : ℝ) + ξ * (n : ℝ) := by linarith
    have h4 : ρ * (degAt 𝓗.pow2 w : ℝ) ≤ ρ * ((1 - ε) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (le_of_lt hw') hρ0
    linarith
  · -- Type A₂
    obtain ⟨-, Rabs, Rreg, hEq, -, -, hreg⟩ := h
    have h2 := (hreg.2 w hw).2
    rw [hEq]
    linarith
  · -- Type B
    obtain ⟨-, htyp, -⟩ := h.1
    have h2 := (htyp Set.univ hV w).1
    simp only [Set.univ_inter] at h2
    rw [abs_le] at h2
    show ((nbrs R_res w).ncard : ℝ) ≤ ρ * (1 - ε) * (n : ℝ) + ξ * (n : ℝ)
    have h3 : ((nbrs R_res w).ncard : ℝ) ≤ ρ * ((nbrs (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w).ncard : ℝ)
        + ξ * (n : ℝ) := by linarith
    have h4 : nbrs (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w ⊆ nbrs 𝓗.pow2 w := by
      intro x hx
      exact (mem_incidentTwo.mp hx).1
    have h5 : ((nbrs (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w).ncard : ℝ) ≤
        ((nbrs 𝓗.pow2 w).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard h4 (Set.toFinite _)
    have h6 : ρ * ((nbrs (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w).ncard : ℝ) ≤
        ρ * ((1 - ε) * (n : ℝ)) := by
      have := mul_le_mul_of_nonneg_left (le_trans h5 (le_of_lt hw')) hρ0
      linarith
    linarith


/-! ## UC1 -/

/-- **§12, Step 9 (UC1).**  The degree bound for vertices outside `U`: if
`𝓗_final` is covered by `R_final` (where `R_final ⊆ R_res`) and by the large
edges (at most `2n/r₀` through any vertex), and if the reservoir degrees
outside `U` are at most `ρ(1-ε)n + ξn`, then

`d_{𝓗_final}(w) ≤ |C_final| - ρεn/4`. -/
theorem s12_uc1 {U : Set (Fin n)} {𝓗fin R_res R_final : Hypergraph (Fin n)}
    (Cfinal : Finset (Fin n)) {ρ ξ ε : ℝ} {r₀ : ℕ}
    (hRfin : R_final ⊆ R_res)
    (hdecomp : ∀ w : Fin n, (MultiHypergraph.hdeg 𝓗fin w : ℝ) ≤
      (degAt R_final w : ℝ) + 2 * (n : ℝ) / (r₀ : ℝ))
    (hres : ∀ w : Fin n, w ∉ U →
      (degAt R_res w : ℝ) ≤ ρ * (1 - ε) * (n : ℝ) + ξ * (n : ℝ))
    (hnum1 : ρ * (1 - ε) * (n : ℝ) + ξ * (n : ℝ) ≤
      (Cfinal.card : ℝ) - ρ * ε * (n : ℝ) / 2)
    (hnum2 : 2 * (n : ℝ) / (r₀ : ℝ) ≤ ρ * ε * (n : ℝ) / 4) :
    ∀ w ∈ (Set.univ : Set (Fin n)) \ U,
      (MultiHypergraph.hdeg 𝓗fin w : ℝ) ≤ (Cfinal.card : ℝ) - ρ * ε * (n : ℝ) / 4 := by
  intro w hw
  have h1 : (degAt R_final w : ℝ) ≤ (degAt R_res w : ℝ) := by
    exact_mod_cast degAt_mono hRfin w
  have h2 := hdecomp w
  have h3 := hres w hw.2
  linarith


/-- **§12, Step 9 (UC3, second part).**  There are at least `|C_final|` vertices
of degree less than `|C_final|` in `𝓗_final`.

The vertices of `V^{(n-1)}(𝓗)` that are missed by no matching of `𝓜_prev^*`
have degree `< |C_final|` (by `(eqn:deg_h_final)`), and at most
`|𝓜_prev| = n - |C_final|` vertices of `V^{(n-1)}(𝓗)` are missed by some
matching (each matching misses at most one vertex of `U`).  Together with UC1
(vertices outside `U`) and UC2 (vertices of `U ∖ V^{(n-1)}`) this gives
`|C_final|` vertices of degree `< |C_final|`. -/
theorem s12_uc3_count {ι : Type*} [Fintype ι] {M : ι → Set (Set (Fin n))}
    {U Vn1 : Set (Fin n)} {𝓗fin : Hypergraph (Fin n)} (Cfinal : Finset (Fin n))
    (hVn1U : Vn1 ⊆ U)
    (hcardM : (Fintype.card ι : ℝ) = (n : ℝ) - (Cfinal.card : ℝ))
    (hmiss : ∀ i, (Vn1 \ famVert (M i)).ncard ≤ 1)
    (hdegVn1 : ∀ v ∈ Vn1, (({i | v ∉ famVert (M i)} : Set ι)).ncard = 0 →
      (MultiHypergraph.hdeg 𝓗fin v : ℝ) < (Cfinal.card : ℝ))
    (hUC1 : ∀ w : Fin n, w ∉ U → (MultiHypergraph.hdeg 𝓗fin w : ℝ) < (Cfinal.card : ℝ))
    (hUC2 : ∀ w : Fin n, w ∈ U → w ∉ Vn1 →
      (MultiHypergraph.hdeg 𝓗fin w : ℝ) < (Cfinal.card : ℝ)) :
    (Cfinal.card : ℝ) ≤
      (({v : Fin n | (MultiHypergraph.hdeg 𝓗fin v : ℝ) < (Cfinal.card : ℝ)}) :
        Set (Fin n)).ncard := by
  classical
  set T : Set (Fin n) := {v | (MultiHypergraph.hdeg 𝓗fin v : ℝ) < (Cfinal.card : ℝ)} with hT
  set A : Set (Fin n) := {v ∈ Vn1 | (({i | v ∉ famVert (M i)} : Set ι)).ncard = 0} with hA
  set D : Set (Fin n) := {v ∈ Vn1 | 0 < (({i | v ∉ famVert (M i)} : Set ι)).ncard} with hD
  set B : Set (Fin n) := U \ Vn1 with hB
  set Cc : Set (Fin n) := Uᶜ with hC
  -- the vertices of `Vn1` missed by some matching
  have hDcover : D ⊆ ⋃ i : ι, (Vn1 ∩ {v | v ∉ famVert (M i)}) := by
    rintro v ⟨hvVn1, hvpos⟩
    rw [Set.mem_iUnion]
    obtain ⟨i, hi⟩ := (Set.ncard_pos (Set.toFinite _)).mp hvpos
    exact ⟨i, hvVn1, hi⟩
  have hDle : D.ncard ≤ Fintype.card ι := by
    refine le_trans (Set.ncard_le_ncard hDcover (Set.toFinite _)) ?_
    refine le_trans (Set.ncard_iUnion_le_of_fintype _) ?_
    have h1 : ∀ i : ι, (Vn1 ∩ {v | v ∉ famVert (M i)}).ncard ≤ 1 := by
      intro i
      refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) (hmiss i)
      rintro v ⟨hv1, hv⟩
      exact ⟨hv1, hv⟩
    calc ∑ i : ι, (Vn1 ∩ {v | v ∉ famVert (M i)}).ncard ≤ ∑ _i : ι, 1 :=
          Finset.sum_le_sum (fun i _ => h1 i)
      _ = Fintype.card ι := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
          norm_num
  -- `A ∪ D = Vn1` and they are disjoint
  have hAD : A ∪ D = Vn1 := by
    ext v
    rw [hA, hD, Set.mem_union]
    constructor
    · rintro (⟨h1, -⟩ | ⟨h1, -⟩) <;> exact h1
    · intro hv
      by_cases h : (({i | v ∉ famVert (M i)} : Set ι)).ncard = 0
      · exact Or.inl ⟨hv, h⟩
      · exact Or.inr ⟨hv, Nat.pos_of_ne_zero h⟩
  have hAdisj : Disjoint A D := by
    rw [Set.disjoint_left]
    rintro v ⟨-, h1⟩ ⟨-, h2⟩
    omega
  have hAsum : A.ncard + D.ncard = Vn1.ncard := by
    rw [← Set.ncard_union_eq hAdisj (Set.toFinite _) (Set.toFinite _), hAD]
  -- the three pieces lie in `T`
  have hAT : A ⊆ T := by
    rintro v ⟨hv1, hv0⟩
    exact hdegVn1 v hv1 hv0
  have hBT : B ⊆ T := by
    rintro v ⟨hvU, hv1⟩
    exact hUC2 v hvU hv1
  have hCT : Cc ⊆ T := by
    rintro v hv
    exact hUC1 v hv
  -- disjointness of the pieces
  have hdisjAB : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro v ⟨hv1, -⟩ ⟨-, hv1'⟩
    exact hv1' hv1
  have hdisjU : Disjoint (A ∪ B) Cc := by
    rw [Set.disjoint_left]
    rintro v (⟨hv1, -⟩ | ⟨hvU, -⟩) hv
    · exact hv (hVn1U hv1)
    · exact hv hvU
  -- the lower bound on `|A ∪ B ∪ Cc|`
  have hcardSum : (A ∪ B ∪ Cc).ncard = A.ncard + B.ncard + Cc.ncard := by
    rw [Set.ncard_union_eq hdisjU (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq hdisjAB (Set.toFinite _) (Set.toFinite _)]
  -- the cardinalities of the pieces
  have hBcard : B.ncard + Vn1.ncard = U.ncard := by
    rw [hB]
    exact Set.ncard_sdiff_add_ncard_of_subset hVn1U
  have hCcard : Cc.ncard + U.ncard = n := by
    rw [hC, Set.ncard_compl_add_ncard U, Nat.card_eq_fintype_card, Fintype.card_fin]
  -- the main arithmetic
  have hAle : (A.ncard : ℝ) = (Vn1.ncard : ℝ) - (D.ncard : ℝ) := by
    have h1 : A.ncard ≤ Vn1.ncard := by
      rw [← hAsum]; exact Nat.le_add_right _ _
    have := congrArg (Nat.cast : ℕ → ℝ) hAsum
    push_cast at this
    linarith
  have hcardι : (Fintype.card ι : ℝ) = (n : ℝ) - (Cfinal.card : ℝ) := hcardM
  have hTge : (A.ncard : ℝ) + B.ncard + Cc.ncard ≤ (T.ncard : ℝ) := by
    have h1 : (A ∪ B ∪ Cc).ncard ≤ T.ncard :=
      Set.ncard_le_ncard (fun v hv => by
        rcases hv with (hv | hv) | hv
        · exact hAT hv
        · exact hBT hv
        · exact hCT hv) (Set.toFinite _)
    rw [hcardSum] at h1
    exact_mod_cast h1
  have hBc : (B.ncard : ℝ) = (U.ncard : ℝ) - (Vn1.ncard : ℝ) := by
    have h1 := congrArg (Nat.cast : ℕ → ℝ) hBcard
    push_cast at h1
    have h2 : (Vn1.ncard : ℝ) ≤ (U.ncard : ℝ) := by
      have := Set.ncard_le_ncard hVn1U (Set.toFinite _)
      exact_mod_cast this
    linarith
  have hCc : (Cc.ncard : ℝ) = (n : ℝ) - (U.ncard : ℝ) := by
    have h1 := congrArg (Nat.cast : ℕ → ℝ) hCcard
    push_cast at h1
    have h2 : (U.ncard : ℝ) ≤ (n : ℝ) := by
      have := Set.ncard_le_ncard (Set.subset_univ U) (Set.toFinite _)
      simpa using (show ((U.ncard : ℕ) : ℝ) ≤ ((Set.univ : Set (Fin n)).ncard : ℝ) from by
        exact_mod_cast this)
    linarith
  have hDle' : (D.ncard : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hDle
  have hDcard : (D.ncard : ℝ) ≤ (Vn1.ncard : ℝ) := by
    have := Set.ncard_le_ncard (show D ⊆ Vn1 by intro v hv; exact hv.1) (Set.toFinite _)
    exact_mod_cast this
  linarith [hTge, hAle, hBc, hCc, hDle', hcardι]

end

end ErdosFaberLovaszConjecture
