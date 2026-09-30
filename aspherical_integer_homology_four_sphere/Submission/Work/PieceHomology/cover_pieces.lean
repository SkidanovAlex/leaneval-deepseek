import Mathlib
import Submission.Work.PieceHomology.CircCover

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PieceHomology

/-!
# The two-piece cover of the circle: the point-set facts

This file proves the point-set statement about the cover of `Circ = ℝ/ℤ` by the two open sets

* `cU = ℝ/ℤ ∖ {π(-1/2)}`,
* `cV = ℝ/ℤ ∖ {π(-1/4)}`,

whose intersection is the disjoint union of the two open arcs `cA1 = π '' (-1/4, 1/2)` and
`cA2 = π '' (1/2, 3/4)`:

`cU ∩ cV = cA1 ∪ cA2`, the two arcs are disjoint, and both are open.

The key point is the fundamental-domain statement: every class in `ℝ/ℤ` has a *unique*
representative in `Ioc (-1/4) (3/4)` (`AddCircle.equivIoc`), and modulo this normalization the
condition `x ∉ {π(-1/4), π(-1/2)}` is exactly `x ∈ K1 ∪ K2`.
-/

/-- `π t = π t'` as soon as `t - t'` is an integer. -/
theorem coe_eq_of_sub_eq_int (t t' : ℝ) (k : ℤ) (h : (k : ℝ) = t - t') :
    ((t : ℝ) : Circ) = ((t' : ℝ) : Circ) := (coe_eq_iff t t').mpr ⟨k, h⟩

/-- `π(1/2) = π(-1/2)`. -/
theorem coe_half : (((1/2 : ℝ)) : Circ) = (((-1/2 : ℝ)) : Circ) :=
  coe_eq_of_sub_eq_int (1/2) (-1/2) 1 (by norm_num)

/-- `π(3/4) = π(-1/4)`. -/
theorem coe_three_quarter : (((3/4 : ℝ)) : Circ) = (((-1/4 : ℝ)) : Circ) :=
  coe_eq_of_sub_eq_int (3/4) (-1/4) 1 (by norm_num)

/-- If `t - t'` lies strictly between `0` and `1`, then `π t ≠ π t'`. -/
theorem coe_ne_of_sub_mem_Ioo_unit (t t' : ℝ) (h1 : 0 < t - t') (h2 : t - t' < 1) :
    ((t : ℝ) : Circ) ≠ ((t' : ℝ) : Circ) := by
  intro hc
  obtain ⟨k, hk⟩ := (coe_eq_iff t t').mp hc
  have hk0 : (0 : ℤ) < k := by
    rw [← Int.cast_lt (R := ℝ), Int.cast_zero, hk]; exact h1
  have hk1 : k < (1 : ℤ) := by
    rw [← Int.cast_lt (R := ℝ), Int.cast_one, hk]; exact h2
  omega

/-- The two arcs are contained in `U ∩ V`. -/
theorem image_K1_union_K2_subset_cU_inter_cV :
    ((↑) : ℝ → Circ) '' (K1 ∪ K2) ⊆ cU ∩ cV := by
  rintro y ⟨t, ht, rfl⟩
  rw [Set.mem_union] at ht
  have htI : t ∈ Set.Ioo (-1/4 : ℝ) (3/4) := by
    rcases ht with ht | ht
    · change t ∈ Set.Ioo (-1/4 : ℝ) (1/2) at ht
      rw [Set.mem_Ioo] at ht ⊢
      exact ⟨ht.1, by linarith [ht.2]⟩
    · change t ∈ Set.Ioo (1/2 : ℝ) (3/4) at ht
      rw [Set.mem_Ioo] at ht ⊢
      exact ⟨by linarith [ht.1], ht.2⟩
  have hne_half : t ≠ 1/2 := by
    rcases ht with ht | ht
    · change t ∈ Set.Ioo (-1/4 : ℝ) (1/2) at ht
      rw [Set.mem_Ioo] at ht; linarith [ht.2]
    · change t ∈ Set.Ioo (1/2 : ℝ) (3/4) at ht
      rw [Set.mem_Ioo] at ht; linarith [ht.1]
  constructor
  · intro hc
    exact coe_ne_of_sub_mem_Ioo t (1/2)
      (by rw [Set.mem_Ioo]; exact ⟨by linarith [htI.1], by linarith [htI.2]⟩) hne_half
      (hc.trans coe_half.symm)
  · intro hc
    exact coe_ne_of_sub_mem_Ioo_unit t (-1/4) (by linarith [htI.1]) (by linarith [htI.2]) hc

/-- Every point of `U ∩ V` lies on one of the two arcs: the complement of `{π(-1/4), π(1/2)}`
inside the fundamental domain `Ioc (-1/4) (3/4)` is `K1 ∪ K2`. -/
theorem cU_inter_cV_subset :
    cU ∩ cV ⊆ ((↑) : ℝ → Circ) '' (K1 ∪ K2) := by
  intro x hx
  obtain ⟨hxU, hxV⟩ := hx
  obtain ⟨t, htIoc, hxt⟩ : ∃ t : ℝ, t ∈ Set.Ioc (-1/4 : ℝ) (-1/4 + 1) ∧ ((t : ℝ) : Circ) = x :=
    ⟨((AddCircle.equivIoc (1:ℝ) (-1/4 : ℝ) x : Set.Ioc (-1/4 : ℝ) (-1/4 + 1)) : ℝ),
      (AddCircle.equivIoc (1:ℝ) (-1/4 : ℝ) x).2, AddCircle.coe_equivIoc⟩
  have ht34 : t ≤ 3/4 := by linarith [htIoc.2]
  have ht_gt : -1/4 < t := htIoc.1
  have ht_ne_34 : t ≠ 3/4 := by
    rintro rfl
    exact hxV (hxt.symm.trans coe_three_quarter)
  have ht_ne_12 : t ≠ 1/2 := by
    rintro rfl
    exact hxU (hxt.symm.trans coe_half)
  refine ⟨t, ?_, hxt⟩
  rw [Set.mem_union, K1, K2, Set.mem_Ioo, Set.mem_Ioo]
  rcases lt_trichotomy t (1/2) with h | h | h
  · exact Or.inl ⟨ht_gt, h⟩
  · exact absurd h ht_ne_12
  · exact Or.inr ⟨h, lt_of_le_of_ne ht34 ht_ne_34⟩

theorem cover_pieces :
    (Work.PieceHomology.cU ∩ Work.PieceHomology.cV = Work.PieceHomology.cA1 ∪ Work.PieceHomology.cA2)
    ∧ Disjoint Work.PieceHomology.cA1 Work.PieceHomology.cA2
    ∧ IsOpen Work.PieceHomology.cA1 ∧ IsOpen Work.PieceHomology.cA2 := by
  have himg : ((↑) : ℝ → Circ) '' (K1 ∪ K2) = cA1 ∪ cA2 := by
    rw [Set.image_union, cA1, cA2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← himg]
    exact Set.Subset.antisymm cU_inter_cV_subset image_K1_union_K2_subset_cU_inter_cV
  · rw [Set.disjoint_left]
    rintro x hx1 hx2
    obtain ⟨t1, ht1, h1⟩ := hx1
    obtain ⟨t2, ht2, h2⟩ := hx2
    change t1 ∈ Set.Ioo (-1/4 : ℝ) (1/2) at ht1
    change t2 ∈ Set.Ioo (1/2 : ℝ) (3/4) at ht2
    rw [Set.mem_Ioo] at ht1 ht2
    refine coe_ne_of_sub_mem_Ioo t1 t2 (by rw [Set.mem_Ioo]; constructor <;>
      linarith [ht1.1, ht1.2, ht2.1, ht2.2]) ?_ (by rw [h1, h2])
    intro h
    rw [h] at ht1
    linarith [ht1.2, ht2.1]
  · simpa [cA1] using isOpenMap_coe K1 isOpen_Ioo
  · simpa [cA2] using isOpenMap_coe K2 isOpen_Ioo

end Work.PieceHomology
