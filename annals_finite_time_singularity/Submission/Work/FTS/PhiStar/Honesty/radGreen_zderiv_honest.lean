import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.Honesty.radGreenCPCore

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllExist

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ### the two primitive difference formulas -/

/-- `rgA` is the primitive of `rgF1`: `rgA y - rgA z = ∫_z^y rgF1` for `1 ≤ y`, `1 ≤ z`,
oriented interval integral. -/
lemma rgMeas_A_diff {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hA1 : IntegrableOn (rgF1 α m c) (Set.Ioc 0 1))
    (hA2 : ∀ w : ℝ, 1 ≤ w → IntegrableOn (rgF1 α m c) (Set.Ioc 1 w))
    {z y : ℝ} (hz1 : 1 ≤ z) (hy1 : 1 ≤ y) :
    rgA α m c y - rgA α m c z = ∫ t in z..y, rgF1 α m c t := by
  have h0 : ∀ w : ℝ, 0 ≤ w → rgA α m c w = ∫ t in Set.Ioc (0:ℝ) w, rgF1 α m c t :=
    fun w hw => intervalIntegral.integral_of_le hw
  have hsplit : ∀ w : ℝ, 1 ≤ w → (∫ t in Set.Ioc (0:ℝ) w, rgF1 α m c t)
      = (∫ t in Set.Ioc (0:ℝ) 1, rgF1 α m c t)
        + (∫ t in Set.Ioc (1:ℝ) w, rgF1 α m c t) := by
    intro w hw
    have hdisj : Disjoint (Set.Ioc (0:ℝ) 1) (Set.Ioc (1:ℝ) w) := by
      rw [Set.disjoint_left]
      intro t ht1 ht2
      exact absurd ht1.2 (not_le.mpr ht2.1)
    rw [← MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hA1 (hA2 w hw),
      Set.Ioc_union_Ioc_eq_Ioc (by norm_num : (0:ℝ) ≤ 1) hw]
  have hsplit2 : ∀ w : ℝ, 1 ≤ w → z ≤ w → (∫ t in Set.Ioc (1:ℝ) w, rgF1 α m c t)
      = (∫ t in Set.Ioc (1:ℝ) z, rgF1 α m c t)
        + (∫ t in Set.Ioc z w, rgF1 α m c t) := by
    intro w hw1 hw
    have hdisj : Disjoint (Set.Ioc (1:ℝ) z) (Set.Ioc z w) := by
      rw [Set.disjoint_left]
      intro t ht1 ht2
      exact absurd ht1.2 (not_le.mpr ht2.1)
    rw [← MeasureTheory.setIntegral_union hdisj measurableSet_Ioc (hA2 z hz1)
        ((hA2 w hw1).mono_set (fun t ht => ⟨by linarith [ht.1], ht.2⟩)),
      Set.Ioc_union_Ioc_eq_Ioc hz1 hw]
  have hsplit3 : ∀ w : ℝ, 1 ≤ w → w ≤ z → (∫ t in Set.Ioc (1:ℝ) z, rgF1 α m c t)
      = (∫ t in Set.Ioc (1:ℝ) w, rgF1 α m c t)
        + (∫ t in Set.Ioc w z, rgF1 α m c t) := by
    intro w hw1 hw
    have hdisj : Disjoint (Set.Ioc (1:ℝ) w) (Set.Ioc w z) := by
      rw [Set.disjoint_left]
      intro t ht1 ht2
      exact absurd ht1.2 (not_le.mpr ht2.1)
    rw [← MeasureTheory.setIntegral_union hdisj measurableSet_Ioc (hA2 w hw1)
        ((hA2 z hz1).mono_set (fun t ht => ⟨by linarith [ht.1], ht.2⟩)),
      Set.Ioc_union_Ioc_eq_Ioc hw1 hw]
  rcases le_total z y with h | h
  · rw [h0 y (by linarith), h0 z (by linarith), hsplit y hy1, hsplit z hz1,
      hsplit2 y hy1 h, hsplit2 z hz1 le_rfl, Set.Ioc_self, MeasureTheory.setIntegral_empty,
      add_zero, intervalIntegral.integral_of_le h]
    ring
  · rw [h0 y (by linarith), h0 z (by linarith), hsplit y hy1, hsplit z hz1,
      hsplit2 z hz1 le_rfl, Set.Ioc_self, MeasureTheory.setIntegral_empty, add_zero,
      hsplit3 y hy1 h, intervalIntegral.integral_of_ge h]
    ring

/-- `rgB` is (minus) the primitive of `rgF2`: `rgB y - rgB z = -∫_z^y rgF2` for `1 ≤ y`, `1 ≤ z`,
oriented interval integral. -/
lemma rgMeas_B_diff {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hB : ∀ w : ℝ, 1 ≤ w → IntegrableOn (rgF2 α m c) (Set.Ioi w))
    {z y : ℝ} (hz1 : 1 ≤ z) (hy1 : 1 ≤ y) :
    rgB α m c y - rgB α m c z = -∫ t in z..y, rgF2 α m c t := by
  have hI1 : IntegrableOn (rgF2 α m c) (Set.Ioi (1:ℝ)) := hB 1 le_rfl
  rcases le_total z y with h | h
  · have hdisj : Disjoint (Set.Ioc z y) (Set.Ioi y) := by
      rw [Set.disjoint_left]
      intro t ht1 ht2
      exact absurd ht1.2 (not_le.mpr ht2)
    have hmem : Set.Ioc z y ⊆ Set.Ioi (1:ℝ) := fun t ht => lt_of_le_of_lt hz1 ht.1
    have hunion : Set.Ioc z y ∪ Set.Ioi y = Set.Ioi z := by
      ext t
      simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · rintro (⟨h1, h2⟩ | h2)
        · exact h1
        · exact lt_of_le_of_lt h h2
      · intro ht
        by_cases hty : t ≤ y
        · exact Or.inl ⟨ht, hty⟩
        · exact Or.inr (lt_of_not_ge hty)
    have hun : (∫ t in Set.Ioc z y, rgF2 α m c t) + rgB α m c y = rgB α m c z := by
      simp only [rgB]
      rw [← MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
        (hI1.mono_set hmem) (hB y hy1), hunion]
    rw [intervalIntegral.integral_of_le h]
    linarith
  · have hdisj : Disjoint (Set.Ioc y z) (Set.Ioi z) := by
      rw [Set.disjoint_left]
      intro t ht1 ht2
      exact absurd ht1.2 (not_le.mpr ht2)
    have hmem : Set.Ioc y z ⊆ Set.Ioi (1:ℝ) := fun t ht => lt_of_le_of_lt hy1 ht.1
    have hunion : Set.Ioc y z ∪ Set.Ioi z = Set.Ioi y := by
      ext t
      simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · rintro (⟨h1, h2⟩ | h2)
        · exact h1
        · exact lt_of_le_of_lt h h2
      · intro ht
        by_cases htz : t ≤ z
        · exact Or.inl ⟨ht, htz⟩
        · exact Or.inr (lt_of_not_ge htz)
    have hun : (∫ t in Set.Ioc y z, rgF2 α m c t) + rgB α m c z = rgB α m c y := by
      simp only [rgB]
      rw [← MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
        (hI1.mono_set hmem) (hB z hz1), hunion]
    rw [intervalIntegral.integral_of_ge h]
    linarith



/-! ### the derivative identity -/

theorem radGreen_zderiv_honest {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hfar : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1))
    (hA1 : IntegrableOn (rgF1 α m c) (Set.Ioc 0 1))
    (hA2 : ∀ w : ℝ, 1 ≤ w → IntegrableOn (rgF1 α m c) (Set.Ioc 1 w))
    (hB : ∀ w : ℝ, 1 ≤ w → IntegrableOn (rgF2 α m c) (Set.Ioi w)) :
    ∀ z : ℝ, 2 ≤ z → z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
      = rgK α m * (rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z) := by
  intro z hz
  have hz1 : 1 ≤ z := by linarith
  have hz0 : (0 : ℝ) < z := by linarith
  have hqge : 2 ≤ rgQ α m := by have := rgQ_ge hα hα4 hm; linarith
  have hpnn : 0 ≤ rgP α m := rgP_nonneg hα m
  -- the crux estimate
  have hCP : Filter.Tendsto (fun y : ℝ =>
      (∫ t in z..y, (y ^ (-(rgQ α m)) * rgF1 α m c t - y ^ (rgP α m) * rgF2 α m c t))
        / (y - z)) (nhdsWithin z {z}ᶜ) (nhds 0) :=
    rgMeas_CP_tendsto hqge hpnn hz (hA2 z hz1) (hB z hz1)
  -- the two power difference quotients
  have hpow1 : Filter.Tendsto
      (fun y : ℝ => (y ^ (-(rgQ α m)) - z ^ (-(rgQ α m))) / (y - z))
      (nhdsWithin z {z}ᶜ) (nhds (-(rgQ α m) * z ^ (-(rgQ α m) - 1))) := by
    have h := (Real.hasDerivAt_rpow_const (x := z) (p := -(rgQ α m))
      (Or.inl (ne_of_gt hz0))).tendsto_slope
    refine Filter.Tendsto.congr' (f₁ := slope (fun y : ℝ => y ^ (-(rgQ α m))) z)
      (f₂ := fun y : ℝ => (y ^ (-(rgQ α m)) - z ^ (-(rgQ α m))) / (y - z)) ?_ h
    filter_upwards with y
    rw [slope_def_field]
  have hpow2 : Filter.Tendsto
      (fun y : ℝ => (y ^ (rgP α m) - z ^ (rgP α m)) / (y - z))
      (nhdsWithin z {z}ᶜ) (nhds (rgP α m * z ^ (rgP α m - 1))) := by
    have h := (Real.hasDerivAt_rpow_const (x := z) (p := rgP α m)
      (Or.inl (ne_of_gt hz0))).tendsto_slope
    refine Filter.Tendsto.congr' (f₁ := slope (fun y : ℝ => y ^ (rgP α m)) z)
      (f₂ := fun y : ℝ => (y ^ (rgP α m) - z ^ (rgP α m)) / (y - z)) ?_ h
    filter_upwards with y
    rw [slope_def_field]
  -- the eventual decomposition of the slope
  have hdec : (fun y : ℝ => slope (Work.FTS.PhiStar.Radial.radGreen α m c) z y)
      =ᶠ[nhdsWithin z {z}ᶜ]
      (fun y : ℝ => rgK α m *
        ((∫ t in z..y, (y ^ (-(rgQ α m)) * rgF1 α m c t - y ^ (rgP α m) * rgF2 α m c t))
            / (y - z)
          + ((y ^ (-(rgQ α m)) - z ^ (-(rgQ α m))) / (y - z)) * rgA α m c z
          + ((y ^ (rgP α m) - z ^ (rgP α m)) / (y - z)) * rgB α m c z)) := by
    have hmem : Set.Ioi (1 : ℝ) ∈ nhdsWithin z {z}ᶜ :=
      nhdsWithin_le_nhds (show Set.Ioi (1 : ℝ) ∈ nhds z from
        isOpen_Ioi.mem_nhds (show (1 : ℝ) < z by linarith))
    filter_upwards [hmem, self_mem_nhdsWithin] with y hy hyne
    have hy1 : 1 ≤ y := hy.le
    have hAy := rgMeas_A_diff hA1 hA2 hz1 hy1
    have hBy : rgB α m c y - rgB α m c z = -∫ t in z..y, rgF2 α m c t :=
      rgMeas_B_diff hB hz1 hy1
    have hBy' : rgB α m c z - rgB α m c y = ∫ t in z..y, rgF2 α m c t := by
      rw [show rgB α m c z - rgB α m c y = -(rgB α m c y - rgB α m c z) from by ring,
        hBy, neg_neg]
    have hintA : IntervalIntegrable (rgF1 α m c) volume z y :=
      ⟨(hA2 y hy1).mono_set (fun t ht => ⟨lt_of_le_of_lt hz1 ht.1, ht.2⟩),
       (hA2 z hz1).mono_set (fun t ht => ⟨lt_of_le_of_lt hy1 ht.1, ht.2⟩)⟩
    have hintB : IntervalIntegrable (rgF2 α m c) volume z y :=
      ⟨(hB z hz1).mono_set (fun t ht => ht.1),
       (hB y hy1).mono_set (fun t ht => ht.1)⟩
    have hintfull : (∫ t in z..y,
          (y ^ (-(rgQ α m)) * rgF1 α m c t - y ^ (rgP α m) * rgF2 α m c t))
        = y ^ (-(rgQ α m)) * (∫ t in z..y, rgF1 α m c t)
          - y ^ (rgP α m) * (∫ t in z..y, rgF2 α m c t) := by
      rw [intervalIntegral.integral_sub (hintA.const_mul _) (hintB.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hkey : Work.FTS.PhiStar.Radial.radGreen α m c y
        - Work.FTS.PhiStar.Radial.radGreen α m c z
        = rgK α m * (y ^ (-(rgQ α m)) * (rgA α m c y - rgA α m c z)
            - y ^ (rgP α m) * (rgB α m c z - rgB α m c y)
            + (y ^ (-(rgQ α m)) - z ^ (-(rgQ α m))) * rgA α m c z
            + (y ^ (rgP α m) - z ^ (rgP α m)) * rgB α m c z) := by
      rw [radGreen_eq α m c y, radGreen_eq α m c z]
      ring
    rw [slope_def_field, hkey, hAy, hBy', ← hintfull]
    ring
  -- the limit of the decomposition
  have hlim : Filter.Tendsto (fun y : ℝ => rgK α m *
        ((∫ t in z..y, (y ^ (-(rgQ α m)) * rgF1 α m c t - y ^ (rgP α m) * rgF2 α m c t))
            / (y - z)
          + ((y ^ (-(rgQ α m)) - z ^ (-(rgQ α m))) / (y - z)) * rgA α m c z
          + ((y ^ (rgP α m) - z ^ (rgP α m)) / (y - z)) * rgB α m c z))
      (nhdsWithin z {z}ᶜ)
      (nhds (rgK α m * (rgP α m * z ^ (rgP α m - 1) * rgB α m c z
        - rgQ α m * z ^ (-(rgQ α m) - 1) * rgA α m c z))) := by
    have h1 : Filter.Tendsto (fun y : ℝ =>
        (∫ t in z..y, (y ^ (-(rgQ α m)) * rgF1 α m c t - y ^ (rgP α m) * rgF2 α m c t))
            / (y - z)
          + ((y ^ (-(rgQ α m)) - z ^ (-(rgQ α m))) / (y - z)) * rgA α m c z
          + ((y ^ (rgP α m) - z ^ (rgP α m)) / (y - z)) * rgB α m c z)
        (nhdsWithin z {z}ᶜ)
        (nhds (0 + (-(rgQ α m) * z ^ (-(rgQ α m) - 1)) * rgA α m c z
          + (rgP α m * z ^ (rgP α m - 1)) * rgB α m c z)) :=
      (hCP.add (hpow1.mul tendsto_const_nhds)).add (hpow2.mul tendsto_const_nhds)
    have h2 : rgK α m * (0 + (-(rgQ α m) * z ^ (-(rgQ α m) - 1)) * rgA α m c z
          + (rgP α m * z ^ (rgP α m - 1)) * rgB α m c z)
        = rgK α m * (rgP α m * z ^ (rgP α m - 1) * rgB α m c z
          - rgQ α m * z ^ (-(rgQ α m) - 1) * rgA α m c z) := by ring
    have := h1.const_mul (rgK α m)
    simpa only [h2, mul_zero] using this
  have hslope : Filter.Tendsto (slope (Work.FTS.PhiStar.Radial.radGreen α m c) z)
      (nhdsWithin z {z}ᶜ)
      (nhds (rgK α m * (rgP α m * z ^ (rgP α m - 1) * rgB α m c z
        - rgQ α m * z ^ (-(rgQ α m) - 1) * rgA α m c z))) :=
    Filter.Tendsto.congr' hdec.symm hlim
  have hd : HasDerivAt (Work.FTS.PhiStar.Radial.radGreen α m c)
      (rgK α m * (rgP α m * z ^ (rgP α m - 1) * rgB α m c z
        - rgQ α m * z ^ (-(rgQ α m) - 1) * rgA α m c z)) z :=
    hasDerivAt_iff_tendsto_slope.mpr hslope
  rw [hd.deriv]
  have e1 : z * z ^ (rgP α m - 1) = z ^ (rgP α m) := by
    rw [mul_comm, ← Real.rpow_add_one (ne_of_gt hz0),
      show rgP α m - 1 + 1 = rgP α m by ring]
  have e2 : z * z ^ (-(rgQ α m) - 1) = z ^ (-(rgQ α m)) := by
    rw [mul_comm, ← Real.rpow_add_one (ne_of_gt hz0),
      show -(rgQ α m) - 1 + 1 = -(rgQ α m) by ring]
  rw [show z * (rgK α m * (rgP α m * z ^ (rgP α m - 1) * rgB α m c z
        - rgQ α m * z ^ (-(rgQ α m) - 1) * rgA α m c z))
      = rgK α m * (rgP α m * (z * z ^ (rgP α m - 1)) * rgB α m c z
        - rgQ α m * (z * z ^ (-(rgQ α m) - 1)) * rgA α m c z) from by ring,
    e1, e2, rgG2, rgG1]
  ring

end Work.FTS.PhiStar.Honesty
