import Mathlib

namespace Work.FIArea3.JointCount

open MeasureTheory Set
open scoped ENNReal Pointwise

/-- For `a < b`, adding the unit interval `[0,1]` to the open interval `(a,b)` yields the open
interval `(a, b+1)`. -/
lemma Ioo_add_Icc_one (a b : ℝ) (hab : a < b) :
    Ioo a b + Icc (0:ℝ) 1 = Ioo a (b + 1) := by
  ext x
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨by linarith [hs.1, ht.1], by linarith [hs.2, ht.2]⟩
  · intro hx
    have h1 : max 0 (x - b) < 1 := max_lt (by norm_num) (by linarith [hx.2])
    have h2 : max 0 (x - b) < x - a := max_lt (by linarith [hx.1]) (by linarith)
    obtain ⟨t, ht1, ht2⟩ := exists_between (lt_min h1 h2)
    refine ⟨x - t, ⟨?_, ?_⟩, t, ⟨?_, ?_⟩, by ring⟩
    · linarith [lt_of_lt_of_le ht2 (min_le_right 1 (x - a))]
    · linarith [lt_of_le_of_lt (le_max_right 0 (x - b)) ht1]
    · exact le_of_lt (lt_of_le_of_lt (le_max_left 0 (x - b)) ht1)
    · exact le_of_lt (lt_of_lt_of_le ht2 (min_le_left 1 (x - a)))

/-- **Volume of a convex set thickened by the unit interval.**  If `S ⊆ ℝ` is convex and bounded,
then the volume of its Minkowski sum `S + [0,1]` equals the volume of `S` plus `1` (the latter
contribution being absent when `S` is empty). -/
theorem convex_volume_add_Icc_one (S : Set ℝ) (hS : Convex ℝ S) (hb : Bornology.IsBounded S) :
    MeasureTheory.volume (Set.image2 (· + ·) S (Set.Icc (0:ℝ) 1)) =
      MeasureTheory.volume S + (if S = ∅ then 0 else 1) := by
  rw [Set.image2_add]
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hSord : S.OrdConnected := hS.ordConnected
    have hbddBelow : BddBelow S := hb.bddBelow
    have hbddAbove : BddAbove S := hb.bddAbove
    have hab : sInf S ≤ sSup S := csInf_le_csSup hne hbddBelow hbddAbove
    have hSIcc : S ⊆ Icc (sInf S) (sSup S) := subset_Icc_csInf_csSup hbddBelow hbddAbove
    -- the open interval between the infimum and the supremum is contained in `S`
    have hIoo_sub : Ioo (sInf S) (sSup S) ⊆ S := by
      intro x hx
      obtain ⟨s1, hs1, hs1x⟩ := exists_lt_of_csInf_lt hne hx.1
      obtain ⟨s2, hs2, hxs2⟩ := exists_lt_of_lt_csSup hne hx.2
      exact hSord.out hs1 hs2 ⟨le_of_lt hs1x, le_of_lt hxs2⟩
    -- volume of `S` via the sandwich `(sInf S, sSup S) ⊆ S ⊆ [sInf S, sSup S]`
    have hvolS : volume S = ENNReal.ofReal (sSup S - sInf S) := by
      apply le_antisymm
      · calc volume S ≤ volume (Icc (sInf S) (sSup S)) := measure_mono hSIcc
          _ = ENNReal.ofReal (sSup S - sInf S) := Real.volume_Icc
      · calc ENNReal.ofReal (sSup S - sInf S) = volume (Ioo (sInf S) (sSup S)) :=
              Real.volume_Ioo.symm
          _ ≤ volume S := measure_mono hIoo_sub
    -- upper bound for the volume of `S + [0,1]`
    have hT_upper : S + Icc (0:ℝ) 1 ⊆ Icc (sInf S) (sSup S + 1) := by
      rintro x ⟨s, hs, t, ht, rfl⟩
      exact ⟨by linarith [(hSIcc hs).1, ht.1], by linarith [(hSIcc hs).2, ht.2]⟩
    have hvolT_le : volume (S + Icc (0:ℝ) 1) ≤ ENNReal.ofReal (sSup S + 1 - sInf S) := by
      calc volume (S + Icc (0:ℝ) 1) ≤ volume (Icc (sInf S) (sSup S + 1)) := measure_mono hT_upper
        _ = ENNReal.ofReal (sSup S + 1 - sInf S) := Real.volume_Icc
    -- lower bound for the volume of `S + [0,1]`
    have hvolT_ge : ENNReal.ofReal (sSup S + 1 - sInf S) ≤ volume (S + Icc (0:ℝ) 1) := by
      rcases lt_or_eq_of_le hab with hlt | heq
      · -- the set is non-degenerate: it contains the open interval `(sInf S, sSup S)`
        have h_eq : Ioo (sInf S) (sSup S) + Icc (0:ℝ) 1 = Ioo (sInf S) (sSup S + 1) :=
          Ioo_add_Icc_one _ _ hlt
        calc ENNReal.ofReal (sSup S + 1 - sInf S)
            = volume (Ioo (sInf S) (sSup S + 1)) :=
              (Real.volume_Ioo (a := sInf S) (b := sSup S + 1)).symm
          _ = volume (Ioo (sInf S) (sSup S) + Icc (0:ℝ) 1) := by rw [h_eq]
          _ ≤ volume (S + Icc (0:ℝ) 1) := by
              apply measure_mono
              rintro x ⟨s, hs, t, ht, rfl⟩
              exact ⟨s, hIoo_sub hs, t, ht, rfl⟩
      · -- the degenerate case: `S` is a single point
        have hsInf_mem : sInf S ∈ S := by
          obtain ⟨y, hy⟩ := hne
          have h1 : sInf S ≤ y := (hSIcc hy).1
          have h2 : y ≤ sInf S := heq.symm ▸ (hSIcc hy).2
          exact (le_antisymm h2 h1) ▸ hy
        have hS_eq : S = Icc (sInf S) (sSup S) := by
          refine Subset.antisymm hSIcc ?_
          intro x hx
          have hx' : x = sInf S := le_antisymm (heq.symm ▸ hx.2) hx.1
          rw [hx']
          exact hsInf_mem
        have h_eq : S + Icc (0:ℝ) 1 = Icc (sInf S) (sSup S + 1) := by
          conv_lhs => rw [hS_eq]
          rw [Set.Icc_add_Icc hab (by norm_num : (0:ℝ) ≤ 1)]
          simp
        rw [h_eq]
        exact le_of_eq (Real.volume_Icc (a := sInf S) (b := sSup S + 1)).symm
    have hvolT : volume (S + Icc (0:ℝ) 1) = ENNReal.ofReal (sSup S + 1 - sInf S) :=
      le_antisymm hvolT_le hvolT_ge
    have hfin : ENNReal.ofReal (sSup S + 1 - sInf S) =
        ENNReal.ofReal (sSup S - sInf S) + 1 := by
      rw [show sSup S + 1 - sInf S = (sSup S - sInf S) + 1 by ring,
        ENNReal.ofReal_add (by linarith) (by norm_num : (0:ℝ) ≤ 1), ENNReal.ofReal_one]
    rw [hvolT, hvolS, if_neg hne.ne_empty]
    exact hfin

end Work.FIArea3.JointCount
