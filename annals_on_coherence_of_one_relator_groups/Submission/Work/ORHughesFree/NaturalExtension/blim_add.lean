import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension.blim_lower_approx
import Submission.Work.ORHughesFree.NaturalExtension.blim_upper_approx

namespace Work.ORHughesFree.NaturalExtension

/-- Two sets belonging to an ultrafilter have nonempty intersection. -/
private lemma inter_nonempty_of_mem {ω : Ultrafilter ℕ} {s t : Set ℕ}
    (hs : s ∈ ω) (ht : t ∈ ω) : (s ∩ t).Nonempty :=
  Filter.nonempty_of_mem (Filter.inter_mem hs ht)

/-- The ultralimit is additive: `blim ω (f + g) = blim ω f + blim ω g` for bounded `f`, `g`.

The proof squeezes the two reals against each other.  Writing `S = {r | {i | r ≤ f i} ∈ ω}` so
that `blim ω f = sSup S`, the defining ultrafilter `ω` contains, for every `ε > 0`, both
`{i | blim ω f - ε ≤ f i}` and `{i | f i ≤ blim ω f + ε}` (the two approximations
`blim_lower_approx` and `blim_upper_approx`).  Intersecting the corresponding sets for `f` and
`g` and using the fact that an ultrafilter is closed under intersections (so the intersection is
nonempty, hence witnesses the pointwise inequality somewhere), one gets
`blim ω (f + g) ≥ blim ω f + blim ω g - 2ε` and `blim ω (f + g) ≤ blim ω f + blim ω g + 2ε`
for every `ε > 0`; letting `ε → 0` gives the result. -/
theorem blim_add (ω : Ultrafilter ℕ) {f g : ℕ → ℝ} {M : ℝ}
    (hf : ∀ i, |f i| ≤ M) (hg : ∀ i, |g i| ≤ M) :
    blim ω (f + g) = blim ω f + blim ω g := by
  -- The sum of two `M`-bounded sequences is `2M`-bounded.
  have hfg : ∀ i, |(f + g) i| ≤ 2 * M := by
    intro i
    have h1 : |f i + g i| ≤ |f i| + |g i| := abs_add_le (f i) (g i)
    have h2 := hf i
    have h3 := hg i
    simp only [Pi.add_apply]
    linarith
  -- `S = {r | {i | r ≤ (f + g) i} ∈ ω}` is nonempty (`-2M ∈ S`).
  have hne : ({r : ℝ | {i : ℕ | r ≤ (f + g) i} ∈ ω}).Nonempty := by
    refine ⟨-2 * M, ?_⟩
    rw [Set.mem_ofPred_eq]
    have h : ∀ i, -2 * M ≤ (f + g) i := by
      intro i
      have h' := hfg i
      have h'' := neg_abs_le ((f + g) i)
      linarith
    rw [show {i : ℕ | -2 * M ≤ (f + g) i} = Set.univ from Set.eq_univ_iff_forall.mpr h]
    exact Filter.univ_mem
  -- Upper bound: `blim ω (f + g) ≤ blim ω f + blim ω g`.
  have hle : blim ω (f + g) ≤ blim ω f + blim ω g := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    have hε' : 0 < ε / 2 := by linarith
    have hA := blim_upper_approx ω hf hε'
    have hB := blim_upper_approx ω hg hε'
    -- On `A ∩ B` (an `ω`-set) the sum is at most `blim ω f + blim ω g + ε`.
    have hAB : {i : ℕ | f i ≤ blim ω f + ε / 2} ∩ {i : ℕ | g i ≤ blim ω g + ε / 2} ∈ ω :=
      Filter.inter_mem hA hB
    have hD : {i : ℕ | (f + g) i ≤ blim ω f + blim ω g + ε} ∈ ω := by
      refine Filter.mem_of_superset hAB ?_
      rintro i ⟨hi1, hi2⟩
      simp only [Set.mem_ofPred_eq] at hi1 hi2 ⊢
      simp only [Pi.add_apply]
      linarith
    -- Hence `blim ω f + blim ω g + ε` is an upper bound for `S`; so is the supremum.
    have hbound : ∀ r ∈ {r : ℝ | {i : ℕ | r ≤ (f + g) i} ∈ ω},
        r ≤ blim ω f + blim ω g + ε := by
      intro r hr
      by_contra h
      have hlt : blim ω f + blim ω g + ε < r := not_le.mp h
      obtain ⟨i, hi1, hi2⟩ := inter_nonempty_of_mem hr hD
      simp only [Set.mem_ofPred_eq] at hi1 hi2
      linarith
    calc blim ω (f + g) = sSup {r : ℝ | {i : ℕ | r ≤ (f + g) i} ∈ ω} := rfl
      _ ≤ blim ω f + blim ω g + ε := csSup_le hne hbound
  -- Lower bound: `blim ω f + blim ω g ≤ blim ω (f + g)`.
  have hge : blim ω f + blim ω g ≤ blim ω (f + g) := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    have hε' : 0 < ε / 2 := by linarith
    have hA := blim_lower_approx ω hf hε'
    have hB := blim_lower_approx ω hg hε'
    -- On `A ∩ B` (an `ω`-set) the sum is at least `blim ω f + blim ω g - ε`.
    have hAB : {i : ℕ | blim ω f - ε / 2 ≤ f i} ∩ {i : ℕ | blim ω g - ε / 2 ≤ g i} ∈ ω :=
      Filter.inter_mem hA hB
    have hE : {i : ℕ | blim ω f + blim ω g - ε ≤ (f + g) i} ∈ ω := by
      refine Filter.mem_of_superset hAB ?_
      rintro i ⟨hi1, hi2⟩
      simp only [Set.mem_ofPred_eq] at hi1 hi2 ⊢
      simp only [Pi.add_apply]
      linarith
    -- So `blim ω f + blim ω g - ε ∈ S`, and `S` is bounded above by `2M`.
    have hbdd : BddAbove {r : ℝ | {i : ℕ | r ≤ (f + g) i} ∈ ω} := by
      refine ⟨2 * M, ?_⟩
      intro r hr
      by_contra h
      have hlt : 2 * M < r := not_le.mp h
      have hr' : {i : ℕ | r ≤ (f + g) i} ∈ ω := hr
      have hempty : {i : ℕ | r ≤ (f + g) i} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro i hri
        simp only [Set.mem_ofPred_eq] at hri
        have h' := hfg i
        have h'' := le_abs_self ((f + g) i)
        linarith
      rw [hempty] at hr'
      exact Filter.empty_notMem (ω : Filter ℕ) hr'
    have hmain : blim ω f + blim ω g - ε ≤ sSup {r : ℝ | {i : ℕ | r ≤ (f + g) i} ∈ ω} :=
      le_csSup hbdd hE
    have hEq : sSup {r : ℝ | {i : ℕ | r ≤ (f + g) i} ∈ ω} = blim ω (f + g) := rfl
    linarith
  exact le_antisymm hle hge

end Work.ORHughesFree.NaturalExtension
