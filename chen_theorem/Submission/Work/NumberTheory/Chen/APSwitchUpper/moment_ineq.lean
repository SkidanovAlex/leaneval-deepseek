import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiLevelCore

namespace Work.NumberTheory.Chen.APSwitchUpper

open MeasureTheory Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## A triangular Fubini (first-moment) identity -/

theorem integral_tail_eq (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) :
    (∫ x in a..b, ∫ y in x..b, f y) = ∫ x in a..b, (x - a) * f x := by
  have hFac : AbsolutelyContinuousOnInterval (fun x => ∫ y in a..x, f y) a b :=
    hf.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp [Set.uIcc, hab])
  have hidac : AbsolutelyContinuousOnInterval (fun x : ℝ => x) a b :=
    ContDiffOn.absolutelyContinuousOnInterval (by fun_prop)
  have hibp := AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul hFac hidac
  simp only [deriv_id'', mul_one, intervalIntegral.integral_same] at hibp
  have hder : (∫ x in a..b, deriv (fun x => ∫ y in a..x, f y) x * x)
      = ∫ x in a..b, x * f x := by
    have h1 : (∫ x in a..b, deriv (fun x => ∫ y in a..x, f y) x * x)
        = ∫ x in a..b, f x * x := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hf.ae_hasDerivAt_integral] with x hx hxmem
      have hxu : x ∈ Set.uIcc a b := Set.uIoc_subset_uIcc hxmem
      rw [(hx hxu a (by simp [Set.uIcc, hab])).deriv]
    rw [h1]
    exact intervalIntegral.integral_congr (fun x _ => by ring)
  have hpt : ∀ x ∈ Set.Icc a b,
      (∫ y in x..b, f y) = (∫ y in a..b, f y) - ∫ y in a..x, f y := by
    intro x hx
    obtain ⟨hax, hxb⟩ := hx
    have h1 : IntervalIntegrable f volume a x :=
      hf.mono_set (by rw [Set.uIcc_of_le hax, Set.uIcc_of_le hab]; exact Set.Icc_subset_Icc_right hxb)
    have h2 : IntervalIntegrable f volume x b :=
      hf.mono_set (by rw [Set.uIcc_of_le hxb, Set.uIcc_of_le hab]; exact Set.Icc_subset_Icc_left hax)
    have hadj := intervalIntegral.integral_add_adjacent_intervals h1 h2
    linarith
  have hcongr : (∫ x in a..b, ∫ y in x..b, f y)
      = ∫ x in a..b, ((∫ y in a..b, f y) - ∫ y in a..x, f y) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with x hx
    have hx' : x ∈ Set.Icc a b := by
      have := Set.uIoc_subset_uIcc hx
      rwa [Set.uIcc_of_le hab] at this
    exact hpt x hx'
  rw [hcongr]
  have hFint : IntervalIntegrable (fun x => ∫ y in a..x, f y) volume a b :=
    hFac.continuousOn.intervalIntegrable
  rw [intervalIntegral.integral_sub intervalIntegrable_const hFint,
    intervalIntegral.integral_const]
  rw [hibp, hder]
  have hxif : IntervalIntegrable (fun x => x * f x) volume a b := hf.continuousOn_mul (by fun_prop)
  have haf : IntervalIntegrable (fun x => a * f x) volume a b := hf.const_mul a
  rw [show (∫ x in a..b, (x - a) * f x) = ∫ x in a..b, (x * f x - a * f x) from
    intervalIntegral.integral_congr (fun x _ => by ring)]
  rw [intervalIntegral.integral_sub hxif haf, intervalIntegral.integral_const_mul]
  ring

/-! ## The level constants -/

/-- The right end of the level-`j` support: `Mv j = 2j+3`. -/
abbrev Mv (j : ℕ) : ℝ := ((2 * j + 3 : ℕ) : ℝ)

lemma Mv_cast (j : ℕ) : Mv j = 2 * (j : ℝ) + 3 := by
  simp only [Mv]; push_cast; ring

lemma Mv_succ (j : ℕ) : Mv (j + 1) = Mv j + 2 := by
  simp only [Mv]; push_cast; ring

lemma Mv_succ' (j : ℕ) : ((2 * j + 4 : ℕ) : ℝ) = Mv j + 1 := by
  simp only [Mv]; push_cast; ring

lemma three_le_Mv (j : ℕ) : (3 : ℝ) ≤ Mv j := by
  simp only [Mv]; push_cast; exact_mod_cast (by omega : 3 ≤ 2 * j + 3)

lemma one_le_Mv (j : ℕ) : (1 : ℝ) ≤ Mv j := by linarith [three_le_Mv j]

lemma Cv_eq (j : ℕ) : Cv j = ∫ u in (2 : ℝ)..(Mv j + 1), oddSum j u := by
  rw [Cv, Mv_succ']

lemma Tv_eq (j : ℕ) : Tv j = ∫ u in (3 : ℝ)..(Mv j), evenSum j u := rfl

lemma oddSum_mul_id_int (j : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun s => s * oddSum j s) volume a b :=
  (oddSum_intervalIntegrable j a b).continuousOn_mul continuous_id.continuousOn

lemma evenSum_mul_id_int (j : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun s => s * evenSum j s) volume a b :=
  (evenSum_intervalIntegrable j a b).continuousOn_mul continuous_id.continuousOn

lemma oddSum_sub_mul_int (j : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun s => (s - 2) * oddSum j s) volume a b :=
  (oddSum_intervalIntegrable j a b).continuousOn_mul (by fun_prop)

/-! ## `Dv` and `Gv` -/

/-- The first moment of the level-`j` odd profile. -/
def Dv (j : ℕ) : ℝ := ∫ s in (2 : ℝ)..((2 * j + 4 : ℕ) : ℝ), s * oddSum j s

/-- The centered first moment. -/
def Gv (j : ℕ) : ℝ := Dv j - 2 * Cv j

lemma Dv_eq' (j : ℕ) : Dv j = ∫ s in (2 : ℝ)..(Mv j + 1), s * oddSum j s := by
  rw [Dv, Mv_succ']

lemma Gv_eq (j : ℕ) :
    Gv j = ∫ s in (2 : ℝ)..(Mv j + 1), (s - 2) * oddSum j s := by
  rw [Gv, Dv_eq', Cv_eq]
  rw [show (∫ s in (2 : ℝ)..(Mv j + 1), (s - 2) * oddSum j s)
      = ∫ s in (2 : ℝ)..(Mv j + 1), (s * oddSum j s - 2 * oddSum j s) from
    intervalIntegral.integral_congr (fun x _ => by ring)]
  rw [intervalIntegral.integral_sub (oddSum_mul_id_int j 2 (Mv j + 1))
      ((oddSum_intervalIntegrable j 2 (Mv j + 1)).const_mul 2),
    intervalIntegral.integral_const_mul]

lemma Dv_eq_Phi (j : ℕ) :
    Dv j = ∫ x in (1 : ℝ)..(Mv j), (∫ v in x..(Mv j), evenSum j v) := by
  rw [Dv_eq', show (2 : ℝ) = 1 + 1 from by norm_num,
    ← intervalIntegral.integral_comp_add_right (fun s => s * oddSum j s) 1]
  refine intervalIntegral.integral_congr (fun x hx => ?_)
  have hx1 : (1 : ℝ) ≤ x := by
    rw [Set.uIcc_of_le (one_le_Mv j)] at hx; exact hx.1
  have h := oddSum_mul_integral j (s := x + 1) (by linarith)
  rw [show x + 1 - 1 = x from by ring] at h
  exact h

lemma Dv_eq (j : ℕ) :
    Dv j = ∫ x in (1 : ℝ)..(Mv j), (x - 1) * evenSum j x := by
  rw [Dv_eq_Phi]
  exact integral_tail_eq (evenSum j) (one_le_Mv j) (evenSum_intervalIntegrable j 1 (Mv j))

/-! ## The `[1,3]` pieces -/

lemma evenSum_one_three (k : ℕ) :
    ∫ x in (1 : ℝ)..3, evenSum (k + 1) x = (3 + Cv k) * Real.log 3 - 2 := by
  have hc : ContinuousOn (fun x : ℝ => (1 : ℝ) / x) (Set.uIcc (1:ℝ) 3) :=
    continuousOn_const.div continuous_id.continuousOn (by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)] at hx
      exact ne_of_gt (by linarith [hx.1] : (0:ℝ) < x))
  have hdiv : IntervalIntegrable (fun x : ℝ => (1:ℝ) / x) volume 1 3 := hc.intervalIntegrable
  have h1 : ∫ x in (1 : ℝ)..3, evenSum (k + 1) x
      = ∫ x in (1 : ℝ)..3, ((3 + Cv k) * (1 / x) - 1) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    rw [evenSum_formula k hx.1 hx.2]
    field_simp
    ring
  rw [h1, intervalIntegral.integral_sub (hdiv.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul,
    integral_one_div (by
      rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)]
      intro h
      exact absurd h.1 (by norm_num)),
    intervalIntegral.integral_const]
  norm_num

lemma mu_eq (k : ℕ) :
    ∫ x in (1 : ℝ)..(Mv (k + 1)), evenSum (k + 1) x
      = (3 + Cv k) * Real.log 3 - 2 + Tv (k + 1) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (evenSum_intervalIntegrable (k + 1) 1 3)
      (evenSum_intervalIntegrable (k + 1) 3 (Mv (k + 1)))]
  rw [evenSum_one_three k, ← Tv_eq]

/-! ## The clamped part -/

/-- The clamped part of the truncated line. -/
def cut (x : ℝ) : ℝ := max (3 - x) 0

lemma cut_eq_if (x : ℝ) : (if x ≤ 3 then 3 - x else 0) = cut x := by
  rcases le_or_gt x 3 with h | h
  · rw [if_pos h, cut, max_eq_left (by linarith)]
  · rw [if_neg (by linarith), cut, max_eq_right (by linarith)]

lemma cut_cont : Continuous cut :=
  (continuous_const.sub continuous_id).max continuous_const

lemma integral_cut_one (M : ℝ) (h3M : (3:ℝ) ≤ M) :
    ∫ x in (1 : ℝ)..M, cut x = 2 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (cut_cont.intervalIntegrable 1 3) (cut_cont.intervalIntegrable 3 M)]
  have h0 : ∫ x in (3 : ℝ)..M, cut x = 0 := by
    have hpt : Set.EqOn cut (fun _ => (0:ℝ)) (Set.uIcc (3:ℝ) M) := by
      intro x hx
      rw [Set.uIcc_of_le h3M, Set.mem_Icc] at hx
      exact max_eq_right (by linarith [hx.1])
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_zero]
  have hid : IntervalIntegrable (fun x : ℝ => x) volume 1 3 :=
    continuous_id.intervalIntegrable 1 3
  have h1 : ∫ x in (1 : ℝ)..3, cut x = 2 := by
    have hpt : Set.EqOn cut (fun x : ℝ => 3 - x) (Set.uIcc (1:ℝ) 3) := by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)] at hx
      exact max_eq_left (by linarith [hx.2])
    rw [intervalIntegral.integral_congr hpt,
      intervalIntegral.integral_sub (f := fun _ => (3:ℝ)) (g := fun x : ℝ => x)
        (continuous_const.intervalIntegrable 1 3) hid,
      intervalIntegral.integral_const, integral_id]
    norm_num
  rw [h1, h0, add_zero]

/-! ## The centred first moment -/

/-- The moving-window integral of the level-`k` odd profile. -/
def Psi (k : ℕ) (x : ℝ) : ℝ := ∫ v in (max (x - 1) 2)..(Mv k + 1), oddSum k v

/-- The auxiliary function whose `[1,3]` values are `Cv k`. -/
def Psi' (k : ℕ) (x : ℝ) : ℝ := x * evenSum (k + 1) x - cut x

lemma Psi_eq_Psi' (k : ℕ) {x : ℝ} (hx : 1 ≤ x) : Psi k x = Psi' k x := by
  have h := evenSum_succ_mul k (s := x) hx
  rw [cut_eq_if, Mv_succ'] at h
  simp only [Psi, Psi']
  linarith [h]

lemma Psi'_int (k : ℕ) (a b : ℝ) : IntervalIntegrable (Psi' k) volume a b :=
  (evenSum_mul_id_int (k + 1) a b).sub (cut_cont.intervalIntegrable a b)

lemma Psi_int (k : ℕ) {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    IntervalIntegrable (Psi k) volume a b := by
  refine (Psi'_int k a b).congr (fun x hx => ?_)
  have hx1 : (1:ℝ) ≤ x := le_trans (le_min ha hb) (Set.uIoc_subset_uIcc hx).1
  exact (Psi_eq_Psi' k hx1).symm

lemma Psi'_one_three (k : ℕ) : ∫ x in (1 : ℝ)..3, Psi' k x = 2 * Cv k := by
  have hpt : Set.EqOn (Psi' k) (fun _ => Cv k) (Set.uIcc (1:ℝ) 3) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 3), Set.mem_Icc] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have h := evenSum_formula k hx.1 hx.2
    simp only [Psi']
    rw [h, cut, max_eq_left (by linarith [hx.2])]
    field_simp
    ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const]
  norm_num

lemma Psi_three (k : ℕ) :
    ∫ x in (3 : ℝ)..(Mv (k + 1)), Psi k x = Gv k := by
  have hM3 : (3:ℝ) ≤ Mv (k+1) := three_le_Mv (k+1)
  have h2 : ∫ x in (3 : ℝ)..(Mv (k + 1)), Psi k x
      = ∫ x in (3 : ℝ)..(Mv (k + 1)), (∫ v in (x - 1)..(Mv k + 1), oddSum k v) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le hM3, Set.mem_Icc] at hx
    simp only [Psi]
    rw [max_eq_left (by linarith [hx.1])]
  rw [h2, intervalIntegral.integral_comp_sub_right
      (fun z => ∫ v in z..(Mv k + 1), oddSum k v) 1]
  rw [show (3:ℝ) - 1 = 2 from by norm_num,
    show Mv (k + 1) - 1 = Mv k + 1 from by rw [Mv_succ]; ring]
  rw [integral_tail_eq (oddSum k) (by linarith [one_le_Mv k])
      (oddSum_intervalIntegrable k 2 (Mv k + 1))]
  rw [Gv_eq]

lemma Psi_one_Mv (k : ℕ) : ∫ x in (1 : ℝ)..(Mv (k + 1)), Psi k x = Dv k := by
  have hM3 : (3:ℝ) ≤ Mv (k+1) := three_le_Mv (k+1)
  have hI : IntervalIntegrable (Psi k) volume 1 (Mv (k+1)) :=
    Psi_int k (by norm_num) (one_le_Mv (k+1))
  have hsub1 : Set.uIcc (1:ℝ) 3 ⊆ Set.uIcc (1:ℝ) (Mv (k+1)) := by
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 3), Set.uIcc_of_le (one_le_Mv (k+1))]
    exact Set.Icc_subset_Icc_right hM3
  have hsub2 : Set.uIcc (3:ℝ) (Mv (k+1)) ⊆ Set.uIcc (1:ℝ) (Mv (k+1)) := by
    rw [Set.uIcc_of_le hM3, Set.uIcc_of_le (one_le_Mv (k+1))]
    exact Set.Icc_subset_Icc_left (by norm_num : (1:ℝ) ≤ 3)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hI.mono_set hsub1) (hI.mono_set hsub2)
  rw [← hsplit]
  have e1 : ∫ x in (1 : ℝ)..3, Psi k x = 2 * Cv k := by
    have hpt : Set.EqOn (Psi k) (Psi' k) (Set.uIcc (1:ℝ) 3) := by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 3), Set.mem_Icc] at hx
      exact Psi_eq_Psi' k (by linarith [hx.1])
    rw [intervalIntegral.integral_congr hpt, Psi'_one_three k]
  rw [e1, Psi_three k, Gv]
  ring

lemma mom_eq (k : ℕ) :
    ∫ x in (1 : ℝ)..(Mv (k + 1)), x * evenSum (k + 1) x = 2 + Dv k := by
  have hcongr : ∫ x in (1 : ℝ)..(Mv (k + 1)), x * evenSum (k + 1) x
      = ∫ x in (1 : ℝ)..(Mv (k + 1)), (cut x + Psi k x) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le (one_le_Mv (k+1)), Set.mem_Icc] at hx
    have h := Psi_eq_Psi' k hx.1
    simp only [Psi'] at h ⊢
    linarith [h]
  rw [hcongr, intervalIntegral.integral_add (cut_cont.intervalIntegrable _ _)
      (Psi_int k (by norm_num) (one_le_Mv (k+1))),
    integral_cut_one (Mv (k + 1)) (three_le_Mv (k+1)), Psi_one_Mv k]

lemma Dv_diff (k : ℕ) :
    Dv (k + 1) - Dv k = 4 - 3 * Real.log 3 - Cv k * Real.log 3 - Tv (k + 1) := by
  have hJ : Dv (k+1) = ∫ x in (1:ℝ)..(Mv (k+1)), (x - 1) * evenSum (k + 1) x := Dv_eq (k+1)
  have hsplit : ∫ x in (1:ℝ)..(Mv (k+1)), (x - 1) * evenSum (k + 1) x
      = (∫ x in (1:ℝ)..(Mv (k+1)), x * evenSum (k + 1) x)
        - ∫ x in (1:ℝ)..(Mv (k+1)), evenSum (k + 1) x := by
    rw [show (∫ x in (1:ℝ)..(Mv (k+1)), (x - 1) * evenSum (k + 1) x)
        = ∫ x in (1:ℝ)..(Mv (k+1)),
            (x * evenSum (k + 1) x - evenSum (k + 1) x) from
      intervalIntegral.integral_congr (fun x _ => by ring)]
    rw [intervalIntegral.integral_sub (evenSum_mul_id_int (k+1) 1 (Mv (k+1)))
      (evenSum_intervalIntegrable (k+1) 1 (Mv (k+1)))]
  linarith [hJ, hsplit, mom_eq k, mu_eq k]

lemma Gv_mono (k : ℕ) : Gv k ≤ Gv (k + 1) := by
  have hk3 : (3:ℝ) ≤ Mv k := three_le_Mv k
  rw [Gv_eq k, Gv_eq (k + 1), show Mv (k + 1) + 1 = Mv k + 3 from by rw [Mv_succ]; ring]
  have h1M : Mv k + 1 ≤ Mv k + 3 := by linarith
  have hsupp : ∫ s in (Mv k + 1)..(Mv k + 3), (s - 2) * oddSum k s = 0 := by
    have hpt : Set.EqOn (fun s => (s - 2) * oddSum k s) (fun _ => (0:ℝ))
        (Set.uIcc (Mv k + 1) (Mv k + 3)) := by
      intro x hx
      rw [Set.uIcc_of_le h1M, Set.mem_Icc] at hx
      have hz : oddSum k x = 0 := oddSum_eq_zero_of_le k (by rw [Mv_succ' k]; exact hx.1)
      change (x - 2) * oddSum k x = 0
      rw [hz, mul_zero]
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_zero]
  have e1 : ∫ s in (2:ℝ)..(Mv k + 1), (s - 2) * oddSum k s
      = ∫ s in (2:ℝ)..(Mv k + 3), (s - 2) * oddSum k s := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
        (oddSum_sub_mul_int k 2 (Mv k + 1)) (oddSum_sub_mul_int k (Mv k + 1) (Mv k + 3)),
      hsupp, add_zero]
  rw [e1]
  refine intervalIntegral.integral_mono_on (by linarith) (oddSum_sub_mul_int k 2 (Mv k + 3))
    (oddSum_sub_mul_int (k + 1) 2 (Mv k + 3)) (fun x hx => ?_)
  have hx2 : (2:ℝ) ≤ x := hx.1
  have h2 : oddSum k x ≤ oddSum (k + 1) x := oddSum_mono (by omega) x
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x - 2) (sub_nonneg.mpr h2)]

theorem moment_ineq (n : ℕ) :
    2 * Cv (n + 1) ≤ (4 - 3 * Real.log 3) + Cv n * (2 - Real.log 3) - Tv (n + 1) := by
  have h := Dv_diff n
  have hg := Gv_mono n
  have hdef : (4 - 3 * Real.log 3) + Cv n * (2 - Real.log 3) - Tv (n + 1) - 2 * Cv (n + 1)
      = Gv (n + 1) - Gv n := by
    rw [Gv, Gv]
    linarith [h]
  linarith [hdef, hg]

end
end Work.NumberTheory.Chen.APSwitchUpper
