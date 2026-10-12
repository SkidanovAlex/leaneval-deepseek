import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

theorem LintegralTailLimit {g : ℝ → ENNReal} {R C : ℝ} (hR : 0 < R)
    (hg : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (h : ∀ r : ℝ, 0 < r → r < R → (∫⁻ s in Set.Ioi r, g s) ≤ ENNReal.ofReal C) :
    (∫⁻ s in Set.Ioi (0 : ℝ), g s) ≤ ENNReal.ofReal C := by
  -- the approximating sequence `r n = R / (n + 2) ↓ 0`, with `0 < r n < R` for all `n`
  set r : ℕ → ℝ := fun n => R / ((n : ℝ) + 2) with hrdef
  have hg0 : (0 : ℝ → ENNReal) ≤ g := fun _ => zero_le
  have hrpos : ∀ n, 0 < r n := by
    intro n; change 0 < R / ((n : ℝ) + 2); positivity
  have hrR : ∀ n, r n < R := by
    intro n
    change R / ((n : ℝ) + 2) < R
    rw [div_lt_iff₀ (show (0 : ℝ) < (n : ℝ) + 2 by positivity)]
    have h1 : (1 : ℝ) < (n : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    simpa using mul_lt_mul_of_pos_left h1 hR
  have hanti : Antitone r := by
    intro n m hnm
    change R / ((m : ℝ) + 2) ≤ R / ((n : ℝ) + 2)
    refine div_le_div_of_nonneg_left (G₀ := ℝ) (a := R) (b := (m : ℝ) + 2)
      (c := (n : ℝ) + 2) hR.le (show (0 : ℝ) < (n : ℝ) + 2 by positivity) ?_
    have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    linarith
  have hgA : AEMeasurable g (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := hg.aemeasurable
  have hmeas : ∀ n, AEMeasurable ((Set.Ioi (r n)).indicator g) MeasureTheory.volume := fun n =>
    (aemeasurable_indicator_iff measurableSet_Ioi).mpr
      (AEMeasurable.mono_set (Set.Ioi_subset_Ioi (hrpos n).le) hgA)
  -- the indicators increase pointwise to the indicator of `Ioi 0`
  have hsup : ∀ x, (⨆ n, (Set.Ioi (r n)).indicator g x) = (Set.Ioi (0 : ℝ)).indicator g x := by
    intro x
    by_cases hx : (0 : ℝ) < x
    · obtain ⟨n, hn⟩ := exists_nat_gt (R / x)
      have hn' : R / x < (n : ℝ) + 2 := lt_of_lt_of_le hn (by linarith)
      have hRlt : R < ((n : ℝ) + 2) * x := (div_lt_iff₀ hx).mp hn'
      have hrx : r n < x := by
        change R / ((n : ℝ) + 2) < x
        rw [div_lt_iff₀ (show (0 : ℝ) < (n : ℝ) + 2 by positivity)]
        exact lt_of_lt_of_eq hRlt (mul_comm ((n : ℝ) + 2) x)
      exact le_antisymm
        (iSup_le fun m =>
          Set.indicator_le_indicator_of_subset (Set.Ioi_subset_Ioi (hrpos m).le) hg0 x)
        (by
          rw [Set.indicator_of_mem (show x ∈ Set.Ioi (0 : ℝ) from hx) g]
          calc g x = (Set.Ioi (r n)).indicator g x :=
                (Set.indicator_of_mem (show x ∈ Set.Ioi (r n) from hrx) g).symm
            _ ≤ ⨆ m, (Set.Ioi (r m)).indicator g x :=
                le_iSup (fun m => (Set.Ioi (r m)).indicator g x) n)
    · have hzeroL : (Set.Ioi (0 : ℝ)).indicator g x = 0 :=
        Set.indicator_of_notMem (show x ∉ Set.Ioi (0 : ℝ) from hx) g
      have hzeroR : (⨆ n, (Set.Ioi (r n)).indicator g x) = 0 := by
        rw [ENNReal.iSup_eq_zero]
        intro n
        exact Set.indicator_of_notMem (show x ∉ Set.Ioi (r n) from by
          simp only [Set.mem_Ioi]; linarith [hrpos n, not_lt.mp hx]) g
      rw [hzeroR, hzeroL]
  have hmono : ∀ x, Monotone fun n => (Set.Ioi (r n)).indicator g x := fun x n m hnm =>
    Set.indicator_le_indicator_of_subset (Set.Ioi_subset_Ioi (hanti hnm)) hg0 x
  calc (∫⁻ s in Set.Ioi (0 : ℝ), g s)
      = ∫⁻ s, (Set.Ioi (0 : ℝ)).indicator g s :=
        (MeasureTheory.lintegral_indicator measurableSet_Ioi g).symm
    _ = ∫⁻ s, (⨆ n, (Set.Ioi (r n)).indicator g s) :=
        MeasureTheory.lintegral_congr fun x => (hsup x).symm
    _ = ⨆ n, ∫⁻ s, (Set.Ioi (r n)).indicator g s :=
        MeasureTheory.lintegral_iSup' hmeas (Filter.Eventually.of_forall hmono)
    _ = ⨆ n, ∫⁻ s in Set.Ioi (r n), g s := by
        simp only [MeasureTheory.lintegral_indicator measurableSet_Ioi]
    _ ≤ ENNReal.ofReal C := iSup_le fun n => h (r n) (hrpos n) (hrR n)

end Work.BoseFixR.LatGreen
