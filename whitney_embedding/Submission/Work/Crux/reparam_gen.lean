import Mathlib
import Submission.Work.Noncompact.CompressionTube.immersedArcWithGerm

/-!
# The reparametrisation with a *prescribed* start of the affine range

`Work.Noncompact.CompressionTube.exists_smooth_reparam_gen` is the copy of
`exists_smooth_reparam` (immersedArcWithGerm.lean) in which the start of the affine range is a
parameter `h` instead of the constant `1/2`.  It exists because the germ-extent of
`immersedArcWithGerm` is bounded by `min (1/2) (min e_h ρv) / 2` — the `1/2` being exactly this
affine-range start — while the base-piece lemma needs a germ of prescribed extent `e ≤ 1`.

Edits relative to the source: `he₀h : e₀ < 1/2` becomes `he₀h : e₀ < h`; the bound
`(1/2 - e₀)/16` of the density's parameter becomes `(h - e₀)/16`; `hme : e₀ + m < 1/2` becomes
`e₀ + m < h`; and the affine clause `Icc (1/2 : ℝ) 1` becomes `Icc h 1`.  The internal constants
`1/2` of the density (`Lf t = (1/2) * exp ((t + m)/m)`, `hIntG`, ...) are the ramp values and are
untouched.
-/

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff Topology MeasureTheory
open Set Metric Filter MeasureTheory

theorem exists_smooth_reparam_gen (a b e₀ h : ℝ) (ha : a < 0) (he₀ : 0 < e₀) (he₀h : e₀ < h) (hh1 : h ≤ 1)
    (he₀b : e₀ < b) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧
      (∀ t : ℝ, 0 < deriv φ t) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) e₀ → φ t = t) ∧
      Set.range φ ⊆ Set.Ioo a b ∧
      φ 1 ∈ Set.Ioo e₀ b ∧
      (∃ μ : ℝ, ∀ t : ℝ, t ∈ Set.Icc h 1 → φ t = φ 1 + μ * (t - 1)) := by
  classical
  have hm_pos : 0 < min 1 (min ((h - e₀)/16) (min ((b - e₀)/16) ((-a)/16))) :=
    lt_min one_pos (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  obtain ⟨m, hmpos, hm1, hm2, hm3, hm4⟩ : ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ m ≤ (h - e₀)/16 ∧
      m ≤ (b - e₀)/16 ∧ m ≤ (-a)/16 :=
    ⟨_, hm_pos, min_le_left _ _, le_trans (min_le_right _ _) (min_le_left _ _),
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)),
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  have hme : e₀ + m < h := by
    have h : e₀ + (h - e₀)/16 < h := by linarith
    linarith
  set G : ℝ → ℝ := fun t => m * (1 - Real.smoothTransition (t - 1)) +
      Real.smoothTransition (t - 1) * (m * Real.exp (1 - t)) with hG
  set Lf : ℝ → ℝ := fun t => (1/2) * Real.exp ((t + m)/m) with hLf
  set F : ℝ → ℝ := fun t => (Real.smoothTransition ((t - e₀)/m) * G t +
      (1 - Real.smoothTransition ((t - e₀)/m))) *
      (Real.smoothTransition ((-t - m)/m) * Lf t +
      (1 - Real.smoothTransition ((-t - m)/m))) with hF
  have hFcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := by rw [hF]; fun_prop
  obtain ⟨hφcd, hφderiv⟩ := Work.Whitney.contDiff_primitive hFcd
  have hcont : Continuous F := hFcd.continuous
  -- pointwise bounds
  have hGle : ∀ t : ℝ, G t ≤ m := by
    intro t
    show m * (1 - Real.smoothTransition (t - 1)) +
      Real.smoothTransition (t - 1) * (m * Real.exp (1 - t)) ≤ m
    by_cases h : t ≤ 1
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith : t - 1 ≤ 0)]; simp
    · push Not at h
      have hexp : Real.exp (1 - t) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
      have h1 : Real.smoothTransition (t - 1) * (m * Real.exp (1 - t)) ≤
          Real.smoothTransition (t - 1) * m :=
        mul_le_mul_of_nonneg_left (by nlinarith [hexp, hmpos]) (Real.smoothTransition.nonneg _)
      nlinarith [h1]
  have hG0 : ∀ t : ℝ, t ≤ 1 → G t = m := by
    intro t ht
    show m * (1 - Real.smoothTransition (t - 1)) +
      Real.smoothTransition (t - 1) * (m * Real.exp (1 - t)) = m
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : t - 1 ≤ 0)]; ring
  have hGdec : ∀ t : ℝ, 2 ≤ t → G t = m * Real.exp (1 - t) := by
    intro t ht
    show m * (1 - Real.smoothTransition (t - 1)) +
      Real.smoothTransition (t - 1) * (m * Real.exp (1 - t)) = m * Real.exp (1 - t)
    rw [Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ t - 1)]; ring
  have hGpos : ∀ t : ℝ, 0 < G t := by
    intro t
    show 0 < m * (1 - Real.smoothTransition (t - 1)) +
      Real.smoothTransition (t - 1) * (m * Real.exp (1 - t))
    by_cases h : t ≤ 1
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith : t - 1 ≤ 0)]; simpa using hmpos
    · push Not at h
      have hs := Real.smoothTransition.le_one (t - 1)
      have h0 := Real.smoothTransition.nonneg (t - 1)
      have hpos : 0 < Real.exp (1 - t) := Real.exp_pos _
      rcases lt_or_eq_of_le hs with h' | h'
      · have h2 : 0 ≤ Real.smoothTransition (t - 1) * (m * Real.exp (1 - t)) :=
          mul_nonneg (Real.smoothTransition.nonneg _) (mul_nonneg hmpos.le (Real.exp_nonneg _))
        nlinarith [h2, h', hmpos, h0]
      · rw [h']; nlinarith [hpos, hmpos]
  have hLfle : ∀ t : ℝ, t ≤ -2*m → Lf t ≤ 1/2 := by
    intro t ht
    show (1/2) * Real.exp ((t + m)/m) ≤ 1/2
    have h2 : Real.exp ((t + m)/m) ≤ 1 := by
      rw [Real.exp_le_one_iff, div_le_iff₀ hmpos]; linarith
    nlinarith
  have hLfpos : ∀ t : ℝ, 0 < Lf t := by
    intro t; show 0 < (1/2) * Real.exp ((t + m)/m); positivity
  have hFpos : ∀ t : ℝ, 0 < F t := by
    intro t
    show 0 < (Real.smoothTransition ((t - e₀)/m) * G t +
      (1 - Real.smoothTransition ((t - e₀)/m))) *
      (Real.smoothTransition ((-t - m)/m) * Lf t +
      (1 - Real.smoothTransition ((-t - m)/m)))
    have hs1 := Real.smoothTransition.le_one ((t - e₀)/m)
    have h01 := Real.smoothTransition.nonneg ((t - e₀)/m)
    have hs2 := Real.smoothTransition.le_one ((-t - m)/m)
    have h02 := Real.smoothTransition.nonneg ((-t - m)/m)
    have hA : 0 < Real.smoothTransition ((t - e₀)/m) * G t +
        (1 - Real.smoothTransition ((t - e₀)/m)) := by
      rcases lt_or_eq_of_le hs1 with h | h
      · nlinarith [h01, hGpos t]
      · rw [h]; simpa using hGpos t
    have hB : 0 < Real.smoothTransition ((-t - m)/m) * Lf t +
        (1 - Real.smoothTransition ((-t - m)/m)) := by
      rcases lt_or_eq_of_le hs2 with h | h
      · nlinarith [h02, hLfpos t]
      · rw [h]; simpa using hLfpos t
    exact mul_pos hA hB
  have hFle : ∀ t : ℝ, F t ≤ 1 := by
    intro t
    show (Real.smoothTransition ((t - e₀)/m) * G t +
      (1 - Real.smoothTransition ((t - e₀)/m))) *
      (Real.smoothTransition ((-t - m)/m) * Lf t +
      (1 - Real.smoothTransition ((-t - m)/m))) ≤ 1
    have hs1 := Real.smoothTransition.le_one ((t - e₀)/m)
    have h01 := Real.smoothTransition.nonneg ((t - e₀)/m)
    have hs2 := Real.smoothTransition.le_one ((-t - m)/m)
    have h02 := Real.smoothTransition.nonneg ((-t - m)/m)
    have hA : Real.smoothTransition ((t - e₀)/m) * G t +
        (1 - Real.smoothTransition ((t - e₀)/m)) ≤ 1 := by
      nlinarith [h01, hs1, hGle t, (hGpos t).le]
    have hB : Real.smoothTransition ((-t - m)/m) * Lf t +
        (1 - Real.smoothTransition ((-t - m)/m)) ≤ 1 := by
      by_cases h : -m ≤ t
      · have h2 : Real.smoothTransition ((-t - m)/m) = 0 :=
          Real.smoothTransition.zero_of_nonpos (by rw [div_nonpos_iff]; right; exact ⟨by linarith, hmpos.le⟩)
        rw [h2]; norm_num
      · push Not at h
        have hL2 : Lf t ≤ 1 := by
          show (1/2) * Real.exp ((t + m)/m) ≤ 1
          have h3 : Real.exp ((t + m)/m) ≤ 1 := by
            rw [Real.exp_le_one_iff, div_le_iff₀ hmpos]; linarith
          linarith
        nlinarith [h02, hs2, hL2]
    have hBpos : 0 ≤ Real.smoothTransition ((-t - m)/m) * Lf t +
        (1 - Real.smoothTransition ((-t - m)/m)) := by
      rcases lt_or_eq_of_le hs2 with hh | hh
      · nlinarith [h02, (hLfpos t).le]
      · rw [hh]; simpa using (hLfpos t).le
    calc _ ≤ 1 * 1 := mul_le_mul hA hB hBpos (by norm_num)
      _ = 1 := by norm_num
  have hFid : ∀ t : ℝ, 0 ≤ t → t ≤ e₀ → F t = 1 := by
    intro t ht0 ht1
    show (Real.smoothTransition ((t - e₀)/m) * G t +
      (1 - Real.smoothTransition ((t - e₀)/m))) *
      (Real.smoothTransition ((-t - m)/m) * Lf t +
      (1 - Real.smoothTransition ((-t - m)/m))) = 1
    have h1 : Real.smoothTransition ((t - e₀)/m) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by rw [div_nonpos_iff]; right; exact ⟨by linarith, hmpos.le⟩)
    have h2 : Real.smoothTransition ((-t - m)/m) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by rw [div_nonpos_iff]; right; exact ⟨by linarith, hmpos.le⟩)
    rw [h1, h2, hG0 t (by linarith)]; ring
  have hFaff : ∀ t : ℝ, e₀ + m ≤ t → t ≤ 1 → F t = m := by
    intro t ht0 ht1
    show (Real.smoothTransition ((t - e₀)/m) * G t +
      (1 - Real.smoothTransition ((t - e₀)/m))) *
      (Real.smoothTransition ((-t - m)/m) * Lf t +
      (1 - Real.smoothTransition ((-t - m)/m))) = m
    have h1 : Real.smoothTransition ((t - e₀)/m) = 1 :=
      Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hmpos]; linarith)
    have h2 : Real.smoothTransition ((-t - m)/m) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by rw [div_nonpos_iff]; right; exact ⟨by linarith, hmpos.le⟩)
    rw [h1, h2, hG0 t ht1]; ring
  have hFmid : ∀ t : ℝ, 1 ≤ t → F t = G t := by
    intro t ht0
    show (Real.smoothTransition ((t - e₀)/m) * G t +
      (1 - Real.smoothTransition ((t - e₀)/m))) *
      (Real.smoothTransition ((-t - m)/m) * Lf t +
      (1 - Real.smoothTransition ((-t - m)/m))) = G t
    have h1 : Real.smoothTransition ((t - e₀)/m) = 1 :=
      Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hmpos]; linarith)
    have h2 : Real.smoothTransition ((-t - m)/m) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by rw [div_nonpos_iff]; right; exact ⟨by linarith, hmpos.le⟩)
    rw [h1, h2]; ring
  have hFlow : ∀ t : ℝ, t ≤ -2*m → F t = Lf t := by
    intro t ht
    show (Real.smoothTransition ((t - e₀)/m) * G t +
      (1 - Real.smoothTransition ((t - e₀)/m))) *
      (Real.smoothTransition ((-t - m)/m) * Lf t +
      (1 - Real.smoothTransition ((-t - m)/m))) = Lf t
    have h1 : Real.smoothTransition ((-t - m)/m) = 1 :=
      Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hmpos]; linarith)
    have h2 : Real.smoothTransition ((t - e₀)/m) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by rw [div_nonpos_iff]; right; exact ⟨by linarith, hmpos.le⟩)
    rw [h1, h2]; ring
  -- integral estimates
  have hAB : ∀ a b : ℝ, IntervalIntegrable F volume a b := fun a b => hcont.intervalIntegrable _ _
  have hIntA : ∫ x in (-m)..(0:ℝ), F x ≤ m := by
    have h := intervalIntegral.integral_mono_on (f := F) (g := fun _ : ℝ => (1:ℝ))
      (by linarith : (-m:ℝ) ≤ 0) (hAB _ _) intervalIntegrable_const (fun x _ => hFle x)
    have h2 : ∫ x in (-m)..(0:ℝ), (1:ℝ) = m := by
      rw [intervalIntegral.integral_const]; simp
    linarith [h, h2.le]
  have hIntB : ∫ x in (0:ℝ)..e₀, F x = e₀ := by
    rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (1:ℝ)) (fun x hx => by
      rw [Set.uIcc_of_le he₀.le] at hx
      exact hFid x hx.1 hx.2)]
    rw [intervalIntegral.integral_const]; simp
  have hIntC : ∫ x in e₀..(e₀ + m), F x ≤ m := by
    have h := intervalIntegral.integral_mono_on (f := F) (g := fun _ : ℝ => (1:ℝ))
      (by linarith : e₀ ≤ e₀ + m) (hAB _ _) intervalIntegrable_const (fun x _ => hFle x)
    have h2 : ∫ x in e₀..(e₀ + m), (1:ℝ) = m := by
      rw [intervalIntegral.integral_const]; simp
    linarith [h, h2.le]
  have hIntD : ∫ x in (e₀ + m)..(1:ℝ), F x = m * (1 - e₀ - m) := by
    rw [intervalIntegral.integral_congr (g := fun _ : ℝ => m) (fun x hx => by
      rw [Set.uIcc_of_le (by linarith : e₀ + m ≤ (1:ℝ))] at hx
      exact hFaff x hx.1 hx.2)]
    rw [intervalIntegral.integral_const]; simp; ring
  have hIntE : ∫ x in (1:ℝ)..2, F x ≤ m := by
    have h := intervalIntegral.integral_mono_on (f := F) (g := fun _ : ℝ => m)
      (by norm_num : (1:ℝ) ≤ 2) (hAB _ _) intervalIntegrable_const (fun x hx => by
        rw [hFmid x hx.1]; exact hGle x)
    have h2 : ∫ x in (1:ℝ)..2, m = m := by
      rw [intervalIntegral.integral_const]; norm_num
    linarith [h, h2.le]
  have hIntF : ∀ t : ℝ, 2 ≤ t → ∫ x in (2:ℝ)..t, F x ≤ m := by
    intro t ht
    have hpt : Set.EqOn F (fun x => m * Real.exp (1 - x)) (Set.uIcc (2:ℝ) t) := by
      intro x hx
      rw [Set.uIcc_of_le ht] at hx
      rw [hFmid x (by linarith [hx.1]), hGdec x hx.1]
    rw [intervalIntegral.integral_congr hpt]
    have hderiv : ∀ x ∈ Set.uIcc (2:ℝ) t, HasDerivAt (fun y : ℝ => -m * Real.exp (1 - y))
        (m * Real.exp (1 - x)) x := by
      intro x hx
      have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub 1
      have h2 : HasDerivAt (fun y : ℝ => Real.exp (1 - y)) (Real.exp (1 - x) * (-1)) x := h1.exp
      have h3 : HasDerivAt (fun y : ℝ => -m * Real.exp (1 - y))
          (-m * (Real.exp (1 - x) * (-1))) x := h2.const_mul (-m)
      have h4 : -m * (Real.exp (1 - x) * (-1)) = m * Real.exp (1 - x) := by ring
      rw [h4] at h3
      exact h3
    have hint : IntervalIntegrable (fun x : ℝ => m * Real.exp (1 - x)) volume 2 t :=
      ((by fun_prop : Continuous fun x : ℝ => m * Real.exp (1 - x))).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have h2 : Real.exp (1 - 2) = Real.exp (-1) := by norm_num
    rw [h2]
    have h3 : Real.exp (-1) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    have h4 : Real.exp (1 - t) ≥ 0 := Real.exp_nonneg _
    nlinarith [h3, h4, hmpos]
  have hIntG : ∀ t : ℝ, t ≤ -2*m → ∫ x in t..(-2*m), F x ≤ (1/2) * m := by
    intro t ht
    have hpt : Set.EqOn F (fun x => (1/2) * Real.exp ((x + m)/m)) (Set.uIcc t (-2*m)) := by
      intro x hx
      rw [Set.uIcc_of_le ht] at hx
      rw [hFlow x hx.2, hLf]
    rw [intervalIntegral.integral_congr hpt]
    have hderiv : ∀ x ∈ Set.uIcc t (-2*m),
        HasDerivAt (fun y : ℝ => (1/2) * m * Real.exp ((y + m)/m))
          ((1/2) * Real.exp ((x + m)/m)) x := by
      intro x hx
      have h1 : HasDerivAt (fun y : ℝ => (y + m)/m) (1/m) x := by
        simpa using ((hasDerivAt_id x).add_const m).div_const m
      have h2 : HasDerivAt (fun y : ℝ => Real.exp ((y + m)/m))
          (Real.exp ((x + m)/m) * (1/m)) x := h1.exp
      have h3 : HasDerivAt (fun y : ℝ => (1/2) * m * Real.exp ((y + m)/m))
          ((1/2) * m * (Real.exp ((x + m)/m) * (1/m))) x := h2.const_mul ((1/2) * m)
      have h4 : (1/2) * m * (Real.exp ((x + m)/m) * (1/m)) = (1/2) * Real.exp ((x + m)/m) := by
        field_simp
      rw [h4] at h3
      exact h3
    have hint : IntervalIntegrable (fun x : ℝ => (1/2) * Real.exp ((x + m)/m)) volume t (-2*m) :=
      ((by fun_prop : Continuous fun x : ℝ => (1/2) * Real.exp ((x + m)/m))).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have h2 : Real.exp ((-2*m + m)/m) = Real.exp (-1) := by
      have h5 : (-2*m + m)/m = -1 := by field_simp; ring
      rw [h5]
    rw [h2]
    have h3 : Real.exp ((t + m)/m) ≥ 0 := Real.exp_nonneg _
    have h4 : Real.exp (-1) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    nlinarith [h3, h4, hmpos]
  -- assembled bounds
  have hφ_mono : StrictMono (fun t : ℝ => ∫ x in (0:ℝ)..t, F x) :=
    strictMono_of_deriv_pos (fun t => by rw [(hφderiv t).deriv]; exact hFpos t)
  have h1φ : (∫ x in (0:ℝ)..(1:ℝ), F x) ≤ e₀ + 2*m := by
    have h1 : ∫ x in (0:ℝ)..(1:ℝ), F x
        = (∫ x in (0:ℝ)..e₀, F x) + ∫ x in e₀..(1:ℝ), F x :=
      (intervalIntegral.integral_add_adjacent_intervals (hAB _ _) (hAB _ _)).symm
    have h2 : ∫ x in e₀..(1:ℝ), F x
        = (∫ x in e₀..(e₀+m), F x) + ∫ x in (e₀+m)..(1:ℝ), F x :=
      (intervalIntegral.integral_add_adjacent_intervals (hAB _ _) (hAB _ _)).symm
    have h4 : ∫ x in (e₀ + m)..(1:ℝ), F x ≤ m := by
      have h5 : m * (1 - e₀ - m) ≤ m := by nlinarith [hmpos, hme]
      linarith [hIntD, h5]
    rw [h1, h2, hIntB]
    linarith [hIntC, h4]
  have htail : ∀ t : ℝ, 1 ≤ t → ∫ x in (1:ℝ)..t, F x ≤ 2*m := by
    intro t ht
    by_cases h2 : t ≤ 2
    · have hsplit : ∫ x in (1:ℝ)..(2:ℝ), F x = (∫ x in (1:ℝ)..t, F x) + ∫ x in t..(2:ℝ), F x :=
        (intervalIntegral.integral_add_adjacent_intervals (hAB _ _) (hAB _ _)).symm
      have h2' : 0 ≤ ∫ x in t..(2:ℝ), F x :=
        intervalIntegral.integral_nonneg_of_forall h2 (fun x => (hFpos x).le)
      linarith [hIntE, h2', hsplit]
    · push Not at h2
      have hsplit : ∫ x in (1:ℝ)..t, F x = (∫ x in (1:ℝ)..(2:ℝ), F x) + ∫ x in (2:ℝ)..t, F x :=
        (intervalIntegral.integral_add_adjacent_intervals (hAB _ _) (hAB _ _)).symm
      linarith [hIntE, hIntF t h2.le, hsplit]
  have hneg : ∀ t : ℝ, t ≤ 0 → ∫ x in t..(0:ℝ), F x ≤ (5/2)*m := by
    intro t ht
    have hlow : ∫ x in (-2*m)..(-m), F x ≤ m := by
      have h := intervalIntegral.integral_mono_on (f := F) (g := fun _ : ℝ => (1:ℝ))
        (by linarith : (-2*m:ℝ) ≤ -m) (hAB _ _) intervalIntegrable_const (fun x _ => hFle x)
      have h3 : ∫ x in (-2*m)..(-m), (1:ℝ) = m := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      linarith [h, h3.le]
    have hsplit2 : ∫ x in (-2*m)..(0:ℝ), F x =
        (∫ x in (-2*m)..(-m), F x) + ∫ x in (-m)..(0:ℝ), F x :=
      (intervalIntegral.integral_add_adjacent_intervals (hAB _ _) (hAB _ _)).symm
    by_cases h2 : t ≤ -2*m
    · have hsplit1 : ∫ x in t..(0:ℝ), F x =
          (∫ x in t..(-2*m), F x) + ∫ x in (-2*m)..(0:ℝ), F x :=
        (intervalIntegral.integral_add_adjacent_intervals (hAB _ _) (hAB _ _)).symm
      have hg := hIntG t h2
      linarith [hg, hlow, hIntA, hsplit1, hsplit2]
    · push Not at h2
      have hsplit1 : ∫ x in (-2*m)..(0:ℝ), F x =
          (∫ x in (-2*m)..t, F x) + ∫ x in t..(0:ℝ), F x :=
        (intervalIntegral.integral_add_adjacent_intervals (hAB _ _) (hAB _ _)).symm
      have h3 : 0 ≤ ∫ x in (-2*m)..t, F x :=
        intervalIntegral.integral_nonneg_of_forall (by linarith : (-2*m:ℝ) ≤ t)
          (fun x => (hFpos x).le)
      linarith [hlow, hIntA, hsplit1, hsplit2, h3]
  have hrange : Set.range (fun t : ℝ => ∫ x in (0:ℝ)..t, F x) ⊆ Set.Ioo a b := by
    rintro y ⟨t, rfl⟩
    change a < (∫ x in (0:ℝ)..t, F x) ∧ (∫ x in (0:ℝ)..t, F x) < b
    have hb0 : 0 < b := lt_trans he₀ he₀b
    constructor
    · by_cases ht : t ≤ 0
      · have hsymm : ∫ x in (0:ℝ)..t, F x = -∫ x in t..(0:ℝ), F x :=
          intervalIntegral.integral_symm t 0
        rw [hsymm]
        have hb2 : (5/2)*m < -a := by nlinarith [hm4, ha, hmpos]
        linarith [hneg t ht, hb2]
      · push Not at ht
        have h2 : 0 ≤ ∫ x in (0:ℝ)..t, F x :=
          intervalIntegral.integral_nonneg_of_forall ht.le (fun x => (hFpos x).le)
        linarith [ha, h2]
    · by_cases ht : t ≤ 0
      · have hsymm : ∫ x in (0:ℝ)..t, F x = -∫ x in t..(0:ℝ), F x :=
          intervalIntegral.integral_symm t 0
        rw [hsymm]
        have h2 : 0 ≤ ∫ x in t..(0:ℝ), F x :=
          intervalIntegral.integral_nonneg_of_forall ht (fun x => (hFpos x).le)
        linarith [h2, hb0]
      · push Not at ht
        by_cases ht1 : t ≤ 1
        · have hsplit : ∫ x in (0:ℝ)..(1:ℝ), F x = (∫ x in (0:ℝ)..t, F x) + ∫ x in t..(1:ℝ), F x :=
            (intervalIntegral.integral_add_adjacent_intervals (hAB _ _) (hAB _ _)).symm
          have h2 : 0 ≤ ∫ x in t..(1:ℝ), F x :=
            intervalIntegral.integral_nonneg_of_forall ht1 (fun x => (hFpos x).le)
          have hb' : e₀ + 2*m < b := by nlinarith [hm3, he₀b]
          linarith [h1φ, h2, hsplit, hb']
        · push Not at ht1
          have hsplit : ∫ x in (0:ℝ)..t, F x = (∫ x in (0:ℝ)..(1:ℝ), F x) + ∫ x in (1:ℝ)..t, F x :=
            (intervalIntegral.integral_add_adjacent_intervals (hAB _ _) (hAB _ _)).symm
          have hb' : e₀ + 4*m < b := by nlinarith [hm3, he₀b]
          linarith [h1φ, htail t ht1.le, hsplit, hb']
  have hmono : (∫ x in (0:ℝ)..e₀, F x) < ∫ x in (0:ℝ)..(1:ℝ), F x :=
    hφ_mono (by linarith : e₀ < 1)
  refine ⟨fun t => ∫ x in (0:ℝ)..t, F x, hφcd, ?_, ?_, hrange, ?_, ?_⟩
  · intro t
    rw [(hφderiv t).deriv]
    exact hFpos t
  · intro t ht
    rw [Set.mem_Icc] at ht
    change ∫ x in (0:ℝ)..t, F x = t
    have hcc : ∫ x in (0:ℝ)..t, F x = ∫ x in (0:ℝ)..t, (1:ℝ) :=
      intervalIntegral.integral_congr (fun x hx => by
        rw [Set.uIcc_of_le ht.1] at hx
        exact hFid x hx.1 (by linarith [hx.2, ht.2]))
    rw [hcc, intervalIntegral.integral_const]
    simp
  · show e₀ < (∫ x in (0:ℝ)..(1:ℝ), F x) ∧ (∫ x in (0:ℝ)..(1:ℝ), F x) < b
    have hb' : e₀ + 2*m < b := by nlinarith [hm3, he₀b]
    constructor
    · linarith [hmono, hIntB]
    · linarith [h1φ, hb']
  · refine ⟨m, fun t ht => ?_⟩
    rw [Set.mem_Icc] at ht
    have htle : t ≤ 1 := ht.2
    have hsplit : ∫ x in (0:ℝ)..(1:ℝ), F x = (∫ x in (0:ℝ)..t, F x) + ∫ x in t..(1:ℝ), F x :=
      (intervalIntegral.integral_add_adjacent_intervals (hAB _ _) (hAB _ _)).symm
    have hmid : ∫ x in t..(1:ℝ), F x = ∫ x in t..(1:ℝ), m :=
      intervalIntegral.integral_congr (fun x hx => by
        rw [Set.uIcc_of_le htle] at hx
        exact hFaff x (by linarith [ht.1, hme, hx.1]) hx.2)
    rw [hmid, intervalIntegral.integral_const] at hsplit
    have hconst : ((1:ℝ) - t) • m = m * (1 - t) := by ring
    rw [hconst] at hsplit
    linarith [hsplit]


end Work.Noncompact.CompressionTube
