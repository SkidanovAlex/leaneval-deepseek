import Mathlib

/-! Telescoping bound for sums of variations of a monotone function over a
pairwise-non-overlapping finite family of intervals inside `[A,B]`.

If `[lo i, hi i]` (i ∈ s) are pairwise non-overlapping subintervals of
`[A,B]` and `h` is monotone on `[A,B]`, then the intervals can be chained and

    Σ_{i ∈ s} |h(hi i) − h(lo i)| ≤ |h B − h A| .

Prove by induction on the finite set `s`, removing an element where `lo` is
minimal (`Finset.exists_min_image`); all other intervals lie to its right by
non-overlap, and the rest is a telescoping chain.  Provide both the
`MonotoneOn` and the `AntitoneOn` variants. -/

noncomputable section
open scoped BigOperators

set_option autoImplicit false

namespace Submission
namespace S5Tele

/-- monotone telescoping bound over a finite family of non-overlapping
intervals inside `[A,B]`. -/
theorem sum_var_le_mono {ι : Type*} [DecidableEq ι] (s : Finset ι) (lo hi : ι → ℝ)
    (A B : ℝ) (hAB : A ≤ B)
    (hA : ∀ i ∈ s, A ≤ lo i) (hB : ∀ i ∈ s, hi i ≤ B)
    (hle : ∀ i ∈ s, lo i ≤ hi i)
    (hsep : ∀ ⦃i j : ι⦄, i ∈ s → j ∈ s → i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (h : ℝ → ℝ) (hmono : MonotoneOn h (Set.Icc A B)) :
    (∑ i ∈ s, |h (hi i) - h (lo i)|) ≤ |h B - h A| := by
  classical
  let P : Finset ι → Prop := fun u =>
    ∀ (A B : ℝ), A ≤ B →
      (∀ i ∈ u, A ≤ lo i) → (∀ i ∈ u, hi i ≤ B) →
      (∀ i ∈ u, lo i ≤ hi i) →
      (∀ ⦃i j : ι⦄, i ∈ u → j ∈ u → i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i) →
      MonotoneOn h (Set.Icc A B) →
      (∑ i ∈ u, |h (hi i) - h (lo i)|) ≤ |h B - h A|
  have hPs : P s := by
    refine Finset.strongInductionOn s ?_
    intro u ih A B hAB hA hB hle hsep hmono
    by_cases hu : u = ∅
    · subst u
      simp
    · have hu_ne : u.Nonempty := Finset.nonempty_iff_ne_empty.mpr hu
      obtain ⟨i0, hi0u, hmin⟩ := Finset.exists_min_image u lo hu_ne
      let t := u.erase i0
      let w := t.filter (fun j => hi i0 ≤ lo j)
      -- basic membership facts ---------------------------------------------
      have hwu : w ⊆ u := by
        intro j hjw
        exact (Finset.mem_erase.mp (Finset.mem_filter.mp hjw).1).2
      have hi0w : i0 ∉ w := by
        intro h
        exact (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
      have hwu_proper : w ⊂ u := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hwu, ?_⟩
        intro hweq
        exact hi0w (by simpa [hweq] using hi0u)
      have hsub_ins : insert i0 w ⊆ u := by
        intro j hj
        rcases Finset.mem_insert.mp hj with hjeq | hjw
        · subst j
          exact hi0u
        · exact hwu hjw
      -- elements of u outside (insert i0 w) give zero contribution ---------
      have hd_zero : ∀ x ∈ u, x ∉ insert i0 w →
          |h (hi x) - h (lo x)| = 0 := by
        intro x hxu hxnot
        have hxne : x ≠ i0 := by
          intro hxeq
          apply hxnot
          rw [hxeq]
          exact Finset.mem_insert.mpr (Or.inl rfl)
        have hxt : x ∈ t := by
          exact Finset.mem_erase.mpr ⟨hxne, hxu⟩
        have hxw : ¬ hi i0 ≤ lo x := by
          intro hxge
          apply hxnot
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hxt, hxge⟩))
        have hsepx : hi i0 ≤ lo x ∨ hi x ≤ lo i0 := hsep hi0u hxu (Ne.symm hxne)
        have hxhi_le : hi x ≤ lo i0 := by
          rcases hsepx with h1 | h2
          · exact False.elim (hxw h1)
          · exact h2
        have hminx : lo i0 ≤ lo x := hmin x hxu
        have hxx : lo x ≤ hi x := hle x hxu
        have hx_lo : lo x = lo i0 := le_antisymm (le_trans hxx hxhi_le) hminx
        have hx_hi : hi x = lo i0 := le_antisymm hxhi_le (le_trans hminx hxx)
        rw [hx_hi, hx_lo]
        simp
      -- sum over u splits into i0 plus w ------------------------------------
      have hsum : (∑ x ∈ u, |h (hi x) - h (lo x)|) =
          |h (hi i0) - h (lo i0)| + (∑ x ∈ w, |h (hi x) - h (lo x)|) := by
        rw [← Finset.sum_subset hsub_ins hd_zero, Finset.sum_insert hi0w]
      -- induction hypotheses for w, shifted to [hi i0, B] --------------------
      have hAB' : hi i0 ≤ B := hB i0 hi0u
      have hA' : ∀ i ∈ w, hi i0 ≤ lo i := by
        intro i hiw
        exact (Finset.mem_filter.mp hiw).2
      have hB' : ∀ i ∈ w, hi i ≤ B := by
        intro i hiw
        exact hB i (hwu hiw)
      have hle' : ∀ i ∈ w, lo i ≤ hi i := by
        intro i hiw
        exact hle i (hwu hiw)
      have hsep' : ∀ ⦃i j : ι⦄, i ∈ w → j ∈ w → i ≠ j →
          hi i ≤ lo j ∨ hi j ≤ lo i := by
        intro i j hiw hjw hij
        exact hsep (hwu hiw) (hwu hjw) hij
      have hmono' : MonotoneOn h (Set.Icc (hi i0) B) := by
        refine MonotoneOn.mono hmono ?_
        intro x hx
        rcases Set.mem_Icc.mp hx with ⟨h1, h2⟩
        exact Set.mem_Icc.mpr ⟨le_trans (le_trans (hA i0 hi0u) (hle i0 hi0u)) h1, h2⟩
      have hw_le : (∑ i ∈ w, |h (hi i) - h (lo i)|) ≤ |h B - h (hi i0)| :=
        ih w hwu_proper (hi i0) B hAB' hA' hB' hle' hsep' hmono'
      -- monotone increments ------------------------------------------------
      have hle0 : lo i0 ≤ hi i0 := hle i0 hi0u
      have hA0B : A ≤ lo i0 := hA i0 hi0u
      have h0B : hi i0 ≤ B := hB i0 hi0u
      have hlo0_mem : lo i0 ∈ Set.Icc A B :=
        Set.mem_Icc.mpr ⟨hA0B, le_trans hle0 h0B⟩
      have hhi0_mem : hi i0 ∈ Set.Icc A B :=
        Set.mem_Icc.mpr ⟨le_trans hA0B hle0, h0B⟩
      have hmon_lo_hi0 : h (lo i0) ≤ h (hi i0) := hmono hlo0_mem hhi0_mem hle0
      have habs_i0 : |h (hi i0) - h (lo i0)| = h (hi i0) - h (lo i0) :=
        abs_of_nonneg (sub_nonneg.mpr hmon_lo_hi0)
      have hmon_hi0_B : h (hi i0) ≤ h B := hmono hhi0_mem (Set.mem_Icc.mpr ⟨hAB, le_rfl⟩) h0B
      have habs_hiB : |h B - h (hi i0)| = h B - h (hi i0) :=
        abs_of_nonneg (sub_nonneg.mpr hmon_hi0_B)
      have hmon_A_lo0 : h A ≤ h (lo i0) :=
        hmono (Set.mem_Icc.mpr ⟨le_rfl, hAB⟩) hlo0_mem hA0B
      have hmon_A_B : h A ≤ h B :=
        hmono (Set.mem_Icc.mpr ⟨le_rfl, hAB⟩) (Set.mem_Icc.mpr ⟨hAB, le_rfl⟩) hAB
      -- telescoping chain ---------------------------------------------------
      calc
        (∑ x ∈ u, |h (hi x) - h (lo x)|)
            = |h (hi i0) - h (lo i0)| + (∑ x ∈ w, |h (hi x) - h (lo x)|) := hsum
        _ = (h (hi i0) - h (lo i0)) + (∑ x ∈ w, |h (hi x) - h (lo x)|) := by
          rw [habs_i0]
        _ ≤ (h (hi i0) - h (lo i0)) + |h B - h (hi i0)| := by
          exact add_le_add_right hw_le (h (hi i0) - h (lo i0))
        _ = (h (hi i0) - h (lo i0)) + (h B - h (hi i0)) := by
          rw [habs_hiB]
        _ = h B - h (lo i0) := by
          ring
        _ ≤ h B - h A := by
          exact sub_le_sub_left hmon_A_lo0 (h B)
        _ = |h B - h A| := by
          rw [abs_of_nonneg (sub_nonneg.mpr hmon_A_B)]
  exact hPs A B hAB hA hB hle hsep hmono

/-- antitone telescoping bound over a finite family of non-overlapping
intervals inside `[A,B]`. -/
theorem sum_var_le_anti {ι : Type*} [DecidableEq ι] (s : Finset ι) (lo hi : ι → ℝ)
    (A B : ℝ) (hAB : A ≤ B)
    (hA : ∀ i ∈ s, A ≤ lo i) (hB : ∀ i ∈ s, hi i ≤ B)
    (hle : ∀ i ∈ s, lo i ≤ hi i)
    (hsep : ∀ ⦃i j : ι⦄, i ∈ s → j ∈ s → i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (h : ℝ → ℝ) (hanti : AntitoneOn h (Set.Icc A B)) :
    (∑ i ∈ s, |h (hi i) - h (lo i)|) ≤ |h B - h A| := by
  classical
  let g : ℝ → ℝ := fun x => -(h x)
  have hgm : MonotoneOn g (Set.Icc A B) := by
    intro x hx y hy hxy
    dsimp [g]
    exact neg_le_neg (hanti hx hy hxy)
  have hbound := sum_var_le_mono s lo hi A B hAB hA hB hle hsep g hgm
  calc
    (∑ i ∈ s, |h (hi i) - h (lo i)|) = ∑ i ∈ s, |g (hi i) - g (lo i)| := by
      refine Finset.sum_congr rfl ?_
      intro i his
      dsimp [g]
      rw [neg_sub_neg, abs_sub_comm]
    _ ≤ |g B - g A| := hbound
    _ = |h B - h A| := by
      dsimp [g]
      rw [neg_sub_neg, abs_sub_comm]

end S5Tele
end Submission
