/-
# The truncation facets of `Q̄` are pairwise disjoint

This file proves `Work.RTOwed.cuspCert.facet_disjoint`: two *distinct* ideal vertices `w ≠ w'` of
the 24-cell `Q` cannot both be tight at a common point `y ∈ Q̄`, i.e. no point of `Q̄` lies on two
truncation facets at once.  Equivalently, the 24 facets cut off by the truncation planes
`p_w · y = 1 - δ_K = 4/5` have pairwise disjoint (relative) interiors in `Q̄`.

## The mathematics

`truncSlack w y = 4/5 - p_w · y` and `y ∈ Q̄` means that the 24 side constraints
`|y_i| + |y_k| ≤ 1` (`i ≠ k`) and the 24 truncation constraints hold.  Writing `δ_K = 1/5`, the
scaled normals `truncNormal2 w = 2 p_w` are

* `truncNormal2 w = 2 s e_i`, `s = ±1`, for the 8 *coordinate* vertices `w = 16, …, 23`
  (`w = 16 + 2i` gives `+e_i`, `w = 17 + 2i` gives `-e_i`), and
* `truncNormal2 w ∈ {±1}^4` for the 16 *diagonal* vertices `w = 0, …, 15`.

The two ingredients are therefore

* **the coordinate bound** `|y_i| ≤ 4/5` (truncation at `±e_i`), which combined with
  `|y_i| + |y_k| ≤ 1` gives `|y_k| ≤ 1/5` for `k ≠ i` as soon as `y` is tight at `±e_i`;
* **the three-term bound** `|y_a| + |y_b| + |y_c| ≤ 3/2 < 8/5 = 4·(2/5)` for three distinct
  coordinates, obtained by adding the three pairwise constraints.

Case analysis on the pair `(w, w')`:

* two coordinate vertices with the same axis are equal (the sign is determined) — contradicting
  `w ≠ w'` — and with different axes give `|y_i| + |y_k| = 8/5 > 1`;
* a coordinate vertex `±e_i` and a diagonal vertex give
  `8/5 = |Σ_r (2p_w)_r y_r| ≤ 4/5 + 3·(1/5) = 7/5`;
* two diagonal vertices have scaled normals `p ≠ p'` in `{±1}^4`: writing `C` for the set of
  coordinates where they agree and `D` for its (nonempty) complement, subtracting the two
  tightness equations gives `Σ_{r∈D} p_r y_r = 0` and hence `Σ_{r∈C} p_r y_r = 8/5`; but `C` is a
  proper subset of the four coordinates, so `Σ_{r∈C} p_r y_r ≤ Σ_{r∈C} |y_r| ≤ 3/2 < 8/5`.
-/
import Mathlib
import Submission.Work.RTOwed.cuspCert.cusp_disjoint

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed.cuspCert

open Work.FoldInst

/-! ## Auxiliary bounds on `Q̄` -/

/-- **The three-term bound.**  If `r0` is a coordinate outside a set `S` of coordinates, then
`Σ_{r ∈ S} |y_r| ≤ 3/2` for `y ∈ Q̄`: the three coordinates different from `r0` satisfy
`|y_a| + |y_b| + |y_c| ≤ 3/2` (sum the three pairwise constraints `|y_i| + |y_k| ≤ 1`). -/
lemma facet_sum_abs_le {y : E4} (hy : y ∈ Qbar) {r0 : Fin 4} {S : Finset (Fin 4)}
    (hr0 : r0 ∉ S) : ∑ r ∈ S, |y r| ≤ 3 / 2 := by
  have hmain : ∑ r ∈ Finset.univ.erase r0, |y r| ≤ 3 / 2 := by
    fin_cases r0
    · show ∑ r ∈ Finset.univ.erase (0 : Fin 4), |y r| ≤ 3 / 2
      have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 4))) (f := fun r => |y r|)
        (a := (0 : Fin 4)) (Finset.mem_univ _)
      rw [Fin.sum_univ_four] at h
      have h12 := abs_add_le_one y hy (show (1 : Fin 4) ≠ 2 by decide)
      have h13 := abs_add_le_one y hy (show (1 : Fin 4) ≠ 3 by decide)
      have h23 := abs_add_le_one y hy (show (2 : Fin 4) ≠ 3 by decide)
      linarith
    · show ∑ r ∈ Finset.univ.erase (1 : Fin 4), |y r| ≤ 3 / 2
      have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 4))) (f := fun r => |y r|)
        (a := (1 : Fin 4)) (Finset.mem_univ _)
      rw [Fin.sum_univ_four] at h
      have h02 := abs_add_le_one y hy (show (0 : Fin 4) ≠ 2 by decide)
      have h03 := abs_add_le_one y hy (show (0 : Fin 4) ≠ 3 by decide)
      have h23 := abs_add_le_one y hy (show (2 : Fin 4) ≠ 3 by decide)
      linarith
    · show ∑ r ∈ Finset.univ.erase (2 : Fin 4), |y r| ≤ 3 / 2
      have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 4))) (f := fun r => |y r|)
        (a := (2 : Fin 4)) (Finset.mem_univ _)
      rw [Fin.sum_univ_four] at h
      have h01 := abs_add_le_one y hy (show (0 : Fin 4) ≠ 1 by decide)
      have h03 := abs_add_le_one y hy (show (0 : Fin 4) ≠ 3 by decide)
      have h13 := abs_add_le_one y hy (show (1 : Fin 4) ≠ 3 by decide)
      linarith
    · show ∑ r ∈ Finset.univ.erase (3 : Fin 4), |y r| ≤ 3 / 2
      have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 4))) (f := fun r => |y r|)
        (a := (3 : Fin 4)) (Finset.mem_univ _)
      rw [Fin.sum_univ_four] at h
      have h01 := abs_add_le_one y hy (show (0 : Fin 4) ≠ 1 by decide)
      have h02 := abs_add_le_one y hy (show (0 : Fin 4) ≠ 2 by decide)
      have h12 := abs_add_le_one y hy (show (1 : Fin 4) ≠ 2 by decide)
      linarith
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hmain
  · intro r hr
    exact Finset.mem_erase.mpr ⟨fun hh => hr0 (hh ▸ hr), Finset.mem_univ r⟩
  · intro r hr hrs
    exact abs_nonneg _

/-- **The tightness data at a coordinate vertex**: if `w ≥ 16` is tight at `y`, then the coordinate
of `w` is `±4/5` in `y` and the sign of `w` is the sign of that coordinate. -/
lemma facet_coord_tight {y : E4} {w : Fin 24} (hw : truncSlack w y = 0) (h16 : 16 ≤ (w : ℕ)) :
    (axisSign w : ℝ) * y (axisIdx w) = 4 / 5 ∧ |y (axisIdx w)| = 4 / 5 := by
  have hform := axis_n2_form w h16
  have h := axis_slack_eq y w hform
  rw [hw] at h
  have hs : (axisSign w : ℝ) * y (axisIdx w) = 4 / 5 := by linarith
  refine ⟨hs, ?_⟩
  have habs : |(axisSign w : ℝ)| = 1 := by
    rcases axisSign_pm w with h1 | h1 <;> rw [h1] <;> norm_num
  calc |y (axisIdx w)| = |(axisSign w : ℝ) * y (axisIdx w)| := by rw [abs_mul, habs, one_mul]
    _ = |(4 : ℝ) / 5| := by rw [hs]
    _ = 4 / 5 := by norm_num

/-! ## The three cases of the case analysis -/

/-- **Two coordinate vertices** cannot both be tight at a point of `Q̄`. -/
lemma facet_coord_pair_false {y : E4} (hy : y ∈ Qbar) {w w' : Fin 24}
    (h16 : 16 ≤ (w : ℕ)) (h16' : 16 ≤ (w' : ℕ))
    (hw : truncSlack w y = 0) (hw' : truncSlack w' y = 0) (hne : w ≠ w') : False := by
  obtain ⟨h1, h1abs⟩ := facet_coord_tight (y := y) (w := w) hw h16
  obtain ⟨h2, h2abs⟩ := facet_coord_tight (y := y) (w := w') hw' h16'
  by_cases hik : axisIdx w = axisIdx w'
  · have hss : axisSign w = axisSign w' := by
      have hyi : y (axisIdx w) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at h1; norm_num at h1
      have hsub : ((axisSign w : ℝ) - (axisSign w' : ℝ)) * y (axisIdx w) = 0 := by
        rw [sub_mul]
        have h2' := h2
        rw [← hik] at h2'
        rw [h1, h2']
        ring
      rcases mul_eq_zero.mp hsub with hsub' | hzero
      · exact Int.cast_injective (sub_eq_zero.mp hsub')
      · exact absurd hzero hyi
    have hform := axis_n2_form w h16
    have hform' := axis_n2_form w' h16'
    exact hne (truncNormal2_injective (by rw [hform, hform', hik, hss]))
  · have hp := abs_add_le_one y hy hik
    rw [h1abs, h2abs] at hp
    norm_num at hp

/-- **A coordinate vertex and a diagonal vertex** cannot both be tight at a point of `Q̄`:
`8/5 = |Σ_r (2p_w)_r y_r| ≤ 4/5 + 3·(1/5) = 7/5`. -/
lemma facet_coord_diag_false {y : E4} (hy : y ∈ Qbar) {w w' : Fin 24}
    (h16 : 16 ≤ (w : ℕ)) (hlt' : (w' : ℕ) < 16)
    (hw : truncSlack w y = 0) (hw' : truncSlack w' y = 0) : False := by
  obtain ⟨h1, h1abs⟩ := facet_coord_tight (y := y) (w := w) hw h16
  have hsum := half_sum_eq hw'
  have hentry : ∀ r, truncNormal2 w' r = 1 ∨ truncNormal2 w' r = -1 :=
    fun r => half_entry_z w' hlt' r
  have hsmall : ∀ r : Fin 4, r ≠ axisIdx w → |y r| ≤ 1 / 5 := by
    intro r hr
    have hp := abs_add_le_one y hy (Ne.symm hr)
    rw [h1abs] at hp
    linarith
  have hErase : ∑ r ∈ Finset.univ.erase (axisIdx w), |y r| ≤ 3 / 5 := by
    calc ∑ r ∈ Finset.univ.erase (axisIdx w), |y r|
        ≤ ∑ r ∈ Finset.univ.erase (axisIdx w), (1 / 5 : ℝ) :=
          Finset.sum_le_sum fun r hr => hsmall r (Finset.mem_erase.mp hr).1
      _ = 3 / 5 := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ (axisIdx w))]
        simp only [Finset.card_univ, Fintype.card_fin]
        norm_num
  have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 4))) (f := fun r => |y r|)
      (a := axisIdx w) (Finset.mem_univ _)
  have hsumabs : ∑ r, (truncNormal2 w' r : ℝ) * y r ≤ 7 / 5 := by
    calc ∑ r, (truncNormal2 w' r : ℝ) * y r
        ≤ ∑ r, |(truncNormal2 w' r : ℝ) * y r| := Finset.sum_le_sum fun r _ => le_abs_self _
      _ = ∑ r, |y r| := Finset.sum_congr rfl fun r _ => by
            rw [abs_mul]
            rcases hentry r with hh | hh <;> rw [hh] <;> norm_num
      _ = ∑ r ∈ Finset.univ.erase (axisIdx w), |y r| + |y (axisIdx w)| := hsplit.symm
      _ ≤ 3 / 5 + 4 / 5 := add_le_add hErase (le_of_eq h1abs)
      _ = 7 / 5 := by norm_num
  linarith

/-- **Two diagonal vertices** cannot both be tight at a point of `Q̄`.  The scaled normals
`p ≠ p'` lie in `{±1}^4`; on the (nonempty) set `D` where they differ they are opposite, so the
difference of the two tightness equations gives `Σ_{r∈D} p_r y_r = 0` and hence
`Σ_{r∈C} p_r y_r = 8/5` on the complementary set `C`.  But `C` omits a coordinate, so
`Σ_{r∈C} p_r y_r ≤ Σ_{r∈C} |y_r| ≤ 3/2 < 8/5`. -/
lemma facet_diag_pair_false {y : E4} (hy : y ∈ Qbar) {p p' : Fin 4 → ℤ}
    (hne : p ≠ p') (hp : ∀ r, p r = 1 ∨ p r = -1) (hp' : ∀ r, p' r = 1 ∨ p' r = -1)
    (h1 : ∑ r, (p r : ℝ) * y r = 8 / 5) (h2 : ∑ r, (p' r : ℝ) * y r = 8 / 5) : False := by
  obtain ⟨r0, hr0⟩ : ∃ r, p r ≠ p' r := by
    by_contra h
    push Not at h
    exact hne (funext h)
  set C : Finset (Fin 4) := Finset.univ.filter (fun r => p r = p' r) with hC
  set D : Finset (Fin 4) := Finset.univ.filter (fun r => ¬ (p r = p' r)) with hD
  -- split both tightness equations according to `C` and `D`
  have hsplit1 : (∑ r ∈ C, (p r : ℝ) * y r) + (∑ r ∈ D, (p r : ℝ) * y r) = 8 / 5 := by
    rw [hC, hD]
    rw [Finset.sum_filter_add_sum_filter_not]
    exact h1
  have hsplit2 : (∑ r ∈ C, (p' r : ℝ) * y r) + (∑ r ∈ D, (p' r : ℝ) * y r) = 8 / 5 := by
    rw [hC, hD]
    rw [Finset.sum_filter_add_sum_filter_not]
    exact h2
  have hCeq : (∑ r ∈ C, (p r : ℝ) * y r) = (∑ r ∈ C, (p' r : ℝ) * y r) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' : p r = p' r := by
      rw [hC] at hr
      exact (Finset.mem_filter.mp hr).2
    rw [hr']
  -- on `D` the two normals are opposite
  have hDneg : (∑ r ∈ D, (p' r : ℝ) * y r) = - (∑ r ∈ D, (p r : ℝ) * y r) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' : p r ≠ p' r := by
      rw [hD] at hr
      exact (Finset.mem_filter.mp hr).2
    rcases hp r with hh | hh <;> rcases hp' r with hh' | hh'
    · exact absurd (by rw [hh, hh']) hr'
    · rw [hh, hh']; push_cast; ring
    · rw [hh, hh']; push_cast; ring
    · exact absurd (by rw [hh, hh']) hr'
  have hDzero : (∑ r ∈ D, (p r : ℝ) * y r) = 0 := by linarith
  have hCval : (∑ r ∈ C, (p r : ℝ) * y r) = 8 / 5 := by linarith
  -- the sum over `C` is bounded by `3/2`
  have hCr0 : r0 ∉ C := by
    rw [hC]
    exact fun hh => hr0 (Finset.mem_filter.mp hh).2
  have hstep1 : (∑ r ∈ C, (p r : ℝ) * y r) ≤ ∑ r ∈ C, |y r| := by
    refine Finset.sum_le_sum fun r hr => ?_
    calc (p r : ℝ) * y r ≤ |(p r : ℝ) * y r| := le_abs_self _
      _ = |y r| := by
          rw [abs_mul]
          rcases hp r with hh | hh <;> rw [hh] <;> norm_num
  have hstep2 : ∑ r ∈ C, |y r| ≤ 3 / 2 := facet_sum_abs_le hy hCr0
  linarith

/-! ## The disjointness of the truncation facets -/

theorem facet_disjoint : ∀ (w w' : Fin 24), w ≠ w' → ∀ {y : Work.FoldInst.E4},
    y ∈ Work.FoldInst.Qbar → Work.FoldInst.truncSlack w y = 0 → Work.FoldInst.truncSlack w' y = 0 → False := by
  intro w w' hne y hy hw hw'
  by_cases h16 : (w : ℕ) < 16
  · by_cases h16' : (w' : ℕ) < 16
    · -- both vertices are diagonal
      exact facet_diag_pair_false hy (p := truncNormal2 w) (p' := truncNormal2 w')
        (fun h => hne (truncNormal2_injective h))
        (fun r => half_entry_z w h16 r) (fun r => half_entry_z w' h16' r)
        (half_sum_eq hw) (half_sum_eq hw')
    · -- `w` diagonal, `w'` coordinate
      exact facet_coord_diag_false hy (by omega) h16 hw' hw
  · have h16le : 16 ≤ (w : ℕ) := by omega
    by_cases h16' : (w' : ℕ) < 16
    · -- `w` coordinate, `w'` diagonal
      exact facet_coord_diag_false hy h16le h16' hw hw'
    · -- both vertices are coordinate
      exact facet_coord_pair_false hy h16le (by omega) hw hw' hne

end Work.RTOwed.cuspCert
