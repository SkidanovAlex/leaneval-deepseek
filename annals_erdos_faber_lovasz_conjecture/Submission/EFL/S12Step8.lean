import Submission.EFL.S12Step5
import Submission.EFL.Nibble

/-!
# §12, Step 8 (`step:step8`): the decomposition `𝓗_final = 𝓗 ∖ ⋃𝓜_prev`

This module formalises the two structural parts of **Step 8** of the proof of
Theorem 1.1 that do not depend on the deep nibble/leftover inputs:

* **`s12_h_final_decomposition`** (`eqn:h_final`): if the previous matchings
  `𝓜_prev = {M_c : c ∈ C_prev}` contain all the colour classes outside
  `C_final`, only add edges of `𝓗_small` on top of them, and cover all small
  edges outside the reservoir, then every edge of `𝓗` is either in a matching
  of `𝓜_prev`, in `R_final = R_res ∖ ⋃𝓜_prev`, or in a colour class of
  `C_final`.

* **`s12_deg_h_final`** (`eqn:deg_h_final`): the degree bound
  `d_{𝓗_final}(w) ≤ |C_final| + m(w) - min(n - d_𝓗(w), 3)`, where `m(w)` is
  the number of matchings of `𝓜_prev` (in the regularised multi-hypergraph)
  that do not cover `w`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## The decomposition of `𝓗` -/

/-- **§12, Step 8, `(eqn:h_final)`.**  If the family `𝓜_prev` of matchings
contains every colour class of `C_prev`, only uses small edges outside the
colour classes, and covers every small edge outside the reservoir `R_res`,
then `𝓗` is covered by `𝓜_prev`, the final reservoir `R_final` and the colour
classes of `C_final`. -/
theorem s12_h_final_decomposition {n : ℕ} {𝓗 : Hypergraph (Fin n)} {r₁ r₀ β γ ρ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (hS12 : IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal)
    {Cprev : Finset (Fin n)} (hCprev : Cprev = Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff)
    {Mprev : Fin n → Set 𝓗} {R_res R_final : Hypergraph (Fin n)}
    (hRfinal : R_final = R_res \ famUnionIdx Mprev)
    (hsub : ∀ c ∈ Cprev, colourFam φ c ⊆ Mprev c)
    (hoff : ∀ c ∉ Cprev, Mprev c = ∅)
    (hexc : ∀ c ∈ Cprev, ∀ e ∈ Mprev c,
      e ∉ colourFam φ c → edgeSize (e : Set (Fin n)) ≤ r₁)
    (hcover : ∀ e : 𝓗, edgeSize (e : Set (Fin n)) ≤ r₁ →
      (e : Set (Fin n)) ∈ R_res ∨ ∃ c ∈ Cprev, e ∈ Mprev c) :
    ∀ e : 𝓗, (∃ c ∈ Cprev, e ∈ Mprev c) ∨ (e : Set (Fin n)) ∈ R_final ∨
      ∃ c ∈ Cfinal, e ∈ colourFam φ c := by
  classical
  intro e
  by_cases hsmall : edgeSize (e : Set (Fin n)) ≤ r₁
  · rcases hcover e hsmall with hR | ⟨c, hc, hmem⟩
    · by_cases hfam : (e : Set (Fin n)) ∈ famUnionIdx Mprev
      · rw [mem_famUnionIdx] at hfam
        obtain ⟨i, hi⟩ := hfam
        rw [mem_famOf] at hi
        obtain ⟨e', he', hval⟩ := hi
        refine Or.inl ⟨i, ?_, ?_⟩
        · by_contra hiC
          rw [hoff i hiC] at he'
          exact he'
        · exact Subtype.ext hval ▸ he'
      · refine Or.inr (Or.inl ?_)
        rw [hRfinal]
        exact ⟨hR, hfam⟩
    · exact Or.inl ⟨c, hc, hmem⟩
  · have hmed : (e : Set (Fin n)) ∈ medLarge 𝓗 r₁ := ⟨e.2, lt_of_not_ge hsmall⟩
    set e' : ↥(medLarge 𝓗 r₁) := ⟨(e : Set (Fin n)), hmed⟩ with he'
    have hmem : e ∈ colourFam φ (φ.labels e') := by
      rw [mem_colourFam]
      refine ⟨hmed, ?_⟩
      rw [mem_colorClass]
    by_cases hc : φ.labels e' ∈ Cprev
    · exact Or.inl ⟨φ.labels e', hc, hsub _ hc hmem⟩
    · refine Or.inr (Or.inr ⟨φ.labels e', ?_, hmem⟩)
      rw [hS12.hCfinal_eq]
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      exact hCprev ▸ hc

/-! ## The degree bound `(eqn:deg_h_final)` -/

/-- **§12, Step 8, `(eqn:deg_h_final)`.**  If `𝓗_final = 𝓗 ∖ ⋃_{i} M_i` and the
families `M_i` are `|ι| = n - |C_final|` edge-disjoint matchings of the
regularised multi-hypergraph (so that at most `n - 3 - d_𝓗(w)` of them cover
`w` only by a singleton edge), then

`d_{𝓗_final}(w) ≤ |C_final| + m(w) - min(n - d_𝓗(w), 3)`,

where `m(w)` is the number of the `M_i` not covering `w`. -/
theorem s12_deg_h_final {n : ℕ} {𝓗 𝓗fin : Hypergraph (Fin n)} {Cfin : ℕ}
    {ι : Type*} [Fintype ι] {M : ι → Set (Set (Fin n))}
    (hbig : ∀ e ∈ 𝓗, 2 ≤ e.ncard)
    (hfin : ∀ e : Set (Fin n), e ∈ 𝓗fin ↔ e ∈ 𝓗 ∧ ∀ i, e ∉ M i)
    (hcard : (Fintype.card ι : ℝ) = (n : ℝ) - (Cfin : ℝ))
    (hdisj : ∀ i j, i ≠ j → EdgeDisjointFam (M i) (M j))
    (hsingle : ∀ w : Fin n,
      (({i | w ∈ famVert (M i) ∧ ¬ ∃ e ∈ M i, w ∈ e ∧ e ∈ 𝓗} : Set ι)).ncard ≤
        n - 3 - MultiHypergraph.hdeg 𝓗 w) :
    ∀ w : Fin n, (MultiHypergraph.hdeg 𝓗fin w : ℝ) ≤
      (Cfin : ℝ) + (({i | w ∉ famVert (M i)} : Set ι).ncard : ℝ) -
        min ((n : ℝ) - (MultiHypergraph.hdeg 𝓗 w : ℝ)) 3 := by
  classical
  intro w
  set S : Set ι := {i | ∃ e ∈ M i, w ∈ e ∧ e ∈ 𝓗} with hSdef
  set Rm : Set (Set (Fin n)) := {e | e ∈ 𝓗 ∧ w ∈ e ∧ ∃ i, e ∈ M i} with hRmdef
  set A : Set (Set (Fin n)) := {e | e ∈ 𝓗 ∧ w ∈ e} with hAdef
  set m : ℕ := ({i | w ∉ famVert (M i)} : Set ι).ncard with hmdef
  set k : ℕ := n - 3 - MultiHypergraph.hdeg 𝓗 w with hkdef
  -- (1) `S.ncard ≤ Rm.ncard`
  have hSmem : ∀ i ∈ S, ∃ e ∈ M i, w ∈ e ∧ e ∈ 𝓗 := fun i hi => hi
  let g : ι → Set (Fin n) := fun i => if h : i ∈ S then Classical.choose h else ∅
  have hgi : ∀ i (hi : i ∈ S), g i = Classical.choose (hSmem i hi) := fun i hi => dif_pos hi
  have hgS : ∀ i : ι, i ∈ S → g i ∈ Rm := by
    intro i hi
    have hspec := Classical.choose_spec (hSmem i hi)
    rw [hgi i hi, hRmdef]
    exact ⟨hspec.2.2, hspec.2.1, i, hspec.1⟩
  have hg_inj : Set.InjOn g S := by
    intro i hi j hj hij
    by_contra hne
    have hspec_i := Classical.choose_spec (hSmem i hi)
    have hspec_j := Classical.choose_spec (hSmem j hj)
    have heq : Classical.choose (hSmem i hi) = Classical.choose (hSmem j hj) := by
      rw [← hgi i hi, ← hgi j hj]; exact hij
    have h1 : Classical.choose (hSmem i hi) ∈ nonsing (M i) :=
      ⟨hspec_i.1, hbig _ hspec_i.2.2⟩
    have h2 : Classical.choose (hSmem j hj) ∈ nonsing (M j) :=
      ⟨hspec_j.1, hbig _ hspec_j.2.2⟩
    have h3 : Classical.choose (hSmem i hi) ∈ nonsing (M j) := heq ▸ h2
    exact (Set.disjoint_left.mp (hdisj i j hne) h1) h3
  have hSRm : S.ncard ≤ Rm.ncard := by
    have h1 : (g '' S).ncard = S.ncard := (Set.ncard_image_iff (s := S)).mpr hg_inj
    calc S.ncard = (g '' S).ncard := h1.symm
      _ ≤ Rm.ncard := Set.ncard_le_ncard (fun e he => by
          obtain ⟨i, hi, rfl⟩ := he
          exact hgS i hi) (Set.toFinite _)
  -- (2) `Sᶜ.ncard ≤ m + k`
  have hcompl : Sᶜ ⊆ {i | w ∉ famVert (M i)} ∪
      {i | w ∈ famVert (M i) ∧ ¬ ∃ e ∈ M i, w ∈ e ∧ e ∈ 𝓗} := by
    intro i hi
    by_cases hw : w ∈ famVert (M i)
    · exact Or.inr ⟨hw, hi⟩
    · exact Or.inl hw
  have hSc : (Sᶜ).ncard ≤ m + k := by
    refine le_trans (Set.ncard_le_ncard hcompl (Set.toFinite _)) ?_
    refine le_trans (Set.ncard_union_le _ _) ?_
    have h1 : ({i | w ∉ famVert (M i)} : Set ι).ncard = m := rfl
    have h2 : ({i | w ∈ famVert (M i) ∧ ¬ ∃ e ∈ M i, w ∈ e ∧ e ∈ 𝓗} : Set ι).ncard ≤ k := by
      rw [hkdef]; exact hsingle w
    rw [h1]
    exact Nat.add_le_add_left h2 m
  -- (3) `card ι ≤ S.ncard + m + k`
  have hcardS : (Fintype.card ι : ℝ) ≤ (S.ncard : ℝ) + (m : ℝ) + (k : ℝ) := by
    have hsum : (Sᶜ).ncard + S.ncard = Nat.card ι := Set.ncard_compl_add_ncard S
    have hsum2 : (Fintype.card ι : ℝ) = ((Sᶜ).ncard : ℝ) + (S.ncard : ℝ) := by
      rw [← Nat.card_eq_fintype_card, ← hsum, Nat.cast_add]
    have h2 : ((Sᶜ).ncard : ℝ) ≤ (m : ℝ) + (k : ℝ) := by exact_mod_cast hSc
    linarith
  -- (4) `hdeg 𝓗fin w = (A \ Rm).ncard`
  have hAsub : Rm ⊆ A := by
    intro e he
    rw [hRmdef] at he
    rw [hAdef]; exact ⟨he.1, he.2.1⟩
  have hAeq : A.ncard = MultiHypergraph.hdeg 𝓗 w := rfl
  have hfin_eq : ({e ∈ 𝓗fin | w ∈ e} : Set (Set (Fin n))) = A \ Rm := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
    rw [hAdef, hRmdef]
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨he, hwe⟩
      have h1 := (hfin e).mp he
      exact ⟨⟨h1.1, hwe⟩, by rintro ⟨-, -, i, hi⟩; exact h1.2 i hi⟩
    · rintro ⟨⟨he𝓗, hwe⟩, hnot⟩
      exact ⟨(hfin e).mpr ⟨he𝓗, fun i hi => absurd ⟨he𝓗, hwe, i, hi⟩ hnot⟩, hwe⟩
  have hAdecomp : (A \ Rm).ncard + Rm.ncard = A.ncard :=
    Set.ncard_sdiff_add_ncard_of_subset hAsub
  -- (5) arithmetic
  have h1 : (MultiHypergraph.hdeg 𝓗fin w : ℝ) =
      (A.ncard : ℝ) - (Rm.ncard : ℝ) := by
    have h : MultiHypergraph.hdeg 𝓗fin w = (A \ Rm).ncard := by
      rw [MultiHypergraph.hdeg, ← hfin_eq]
    rw [h]
    have hc := congrArg (Nat.cast : ℕ → ℝ) hAdecomp
    push_cast at hc
    linarith
  have h2 : (S.ncard : ℝ) ≤ (Rm.ncard : ℝ) := by exact_mod_cast hSRm
  have hkval : (k : ℝ) = max 0 ((n : ℝ) - 3 - (MultiHypergraph.hdeg 𝓗 w : ℝ)) := by
    rw [hkdef]
    have hsub : n - 3 - MultiHypergraph.hdeg 𝓗 w =
        n - (3 + MultiHypergraph.hdeg 𝓗 w) := by omega
    rw [hsub]
    by_cases h : 3 + MultiHypergraph.hdeg 𝓗 w ≤ n
    · have h' : (3 : ℝ) + (MultiHypergraph.hdeg 𝓗 w : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      rw [Nat.cast_sub h, Nat.cast_add]
      push_cast
      rw [max_eq_right (by linarith)]
      ring
    · have hzero : n - (3 + MultiHypergraph.hdeg 𝓗 w) = 0 := by omega
      rw [hzero, Nat.cast_zero, max_eq_left]
      have h' : n < 3 + MultiHypergraph.hdeg 𝓗 w := Nat.lt_of_not_le h
      have h'' : (n : ℝ) < 3 + (MultiHypergraph.hdeg 𝓗 w : ℝ) := by exact_mod_cast h'
      linarith
  have hk_le : ((k : ℝ)) ≤ (n : ℝ) - (MultiHypergraph.hdeg 𝓗 w : ℝ) -
      min ((n : ℝ) - (MultiHypergraph.hdeg 𝓗 w : ℝ)) 3 := by
    set a : ℝ := (MultiHypergraph.hdeg 𝓗 w : ℝ) with hadef
    have hkval' : (k : ℝ) = max 0 ((n : ℝ) - 3 - a) := by rw [hkval, hadef]
    rw [hkval']
    by_cases h : (3 : ℝ) + a ≤ (n : ℝ)
    · rw [max_eq_right (by linarith), min_eq_right (by linarith)]
      linarith
    · rw [max_eq_left (by push_neg at h; linarith), min_eq_left (by push_neg at h; linarith)]
      linarith
  have hAeq' : (A.ncard : ℝ) = (MultiHypergraph.hdeg 𝓗 w : ℝ) := by rw [hAeq]
  have hgoal : (MultiHypergraph.hdeg 𝓗fin w : ℝ) ≤
      (Cfin : ℝ) + (m : ℝ) -
        min ((n : ℝ) - (MultiHypergraph.hdeg 𝓗 w : ℝ)) 3 := by
    have h3 := hcardS
    have h4 := h2
    have h5 := hk_le
    have h6 := hcard
    linarith
  simpa only [hmdef] using hgoal


/-! ## From a matching decomposition to `χ'(𝓗) ≤ n` -/

/-- If `𝓗` is the disjoint union of `n` pairwise edge-disjoint matchings, then
`χ'(𝓗) ≤ n`.  (This is the final packaging step of §12 Step 10.) -/
theorem chromaticIndex_le_of_matchingDecomposition {n : ℕ} {𝓗 : Hypergraph (Fin n)}
    {M : Fin n → Set 𝓗} (hmat : ∀ c, IsMatching 𝓗 (M c))
    (hcov : ∀ e : 𝓗, ∃ c, e ∈ M c) : 𝓗.chromaticIndex ≤ n :=
  Hypergraph.chromaticIndex_le_of_colorable 𝓗 ⟨matchingDecompositionColoring hmat hcov⟩

/-! ## `(eqn:bound_prev_colours)` -/

/-- The colour sets `C_med ∪ C_diff ∪ C_huge ∪ C_main ∪ C_buff` and `C_final`
partition `[n]`, so `|C_prev| = n - |C_final|` (the counting identity
`(eqn:bound_prev_colours)`). -/
theorem IsS12Colours.card_Cprev {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} {r₀ β γ ρ : ℝ}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (h : IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal) :
    (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff).card + Cfinal.card = n := by
  have hd1 : Disjoint (Cmed ∪ Cdiff ∪ Chuge) Cmain := by
    rw [Finset.disjoint_left]
    intro x hx hxc
    exact (Finset.mem_compl.mp (h.hCmain_sub hxc)) hx
  have hd2 : Disjoint (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain) Cbuff := by
    rw [Finset.disjoint_left]
    intro x hx hxc
    exact (Finset.mem_compl.mp (h.hCbuff_sub hxc)) hx
  have hunion : (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff) ∪ Cfinal = Finset.univ := by
    rw [h.hCfinal_eq]
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  have hdisj : Disjoint (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff) Cfinal := by
    rw [Finset.disjoint_left]
    intro x hx hxc
    rw [h.hCfinal_eq, Finset.mem_sdiff] at hxc
    exact hxc.2 hx
  have hcu := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_univ, Fintype.card_fin] at hcu
  exact hcu.symm

/-- `(eqn:bound_prev_colours)`, `|C_prev| = n - |C_final|` (as a real number). -/
theorem IsS12Colours.card_Cprev_real {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} {r₀ β γ ρ : ℝ}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (h : IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal) :
    ((Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff).card : ℝ) = (n : ℝ) - (Cfinal.card : ℝ) := by
  have h1 := h.card_Cprev
  have h4 : ((Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff).card : ℝ) + (Cfinal.card : ℝ) =
      (n : ℝ) := by
    rw [← Nat.cast_add, h1]
  linarith

end

end ErdosFaberLovaszConjecture
