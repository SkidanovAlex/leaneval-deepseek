import Mathlib
import Submission.Work.EQ.FatouDefs
import Submission.Work.EQ.Fatou.integral_pk_eq
import Submission.Work.EQ.Fatou.eventually_pk_lt
import Submission.Work.EQ.Fatou.pk_mixture

/-!
# Basic integral facts about the angle Poisson kernel `pk`

This module collects the elementary integral identities for
`Work.EQ.pk r ψ = (1 - r²)/(1 - 2 r cos ψ + r²)` that are used in the a.e. radial-limit
development:

* `pk_periodic` — `ψ ↦ pk r ψ` has period `2π`;
* `integral_pk_zero_two_pi` — the mass of the kernel over a period is `2π`;
* `integral_pk_shift` — the shifted version `∫₀^{2π} pk r (θ - φ) dφ = 2π`;
* `pk_antitone_on`, `pk_far_bound` — the kernel is small uniformly away from the singular
  direction (i.e. on `[δ, 2π - δ]`);
* `pk_shift_intervalIntegral` — the change of variables that symmetrizes the integral over
  `(θ-δ, θ+δ)`;
* `pk_far_piece_le` — the two far pieces of the period integral are bounded by `C` times the
  full mass of the weight.
-/

namespace Work.EQ.Fatou

open MeasureTheory Set intervalIntegral Filter

lemma pk_periodic (r : ℝ) : Function.Periodic (fun ψ : ℝ => Work.EQ.pk r ψ) (2 * Real.pi) := by
  intro ψ
  simp only [Work.EQ.pk, Real.cos_add, Real.cos_two_pi, Real.sin_two_pi]
  ring_nf

/-- The Poisson kernel has mass `2π` on a period. -/
theorem integral_pk_zero_two_pi (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    ∫ ψ in (0 : ℝ)..2 * Real.pi, Work.EQ.pk r ψ = 2 * Real.pi := by
  have hper := (pk_periodic r).intervalIntegral_add_eq (-Real.pi) 0
  have hpi : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [hpi, zero_add] at hper
  rw [← hper]
  exact integral_pk_eq r hr hr1

/-- The shifted Poisson kernel has mass `2π` on a period. -/
lemma integral_pk_shift (r θ : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    ∫ φ in (0:ℝ)..2 * Real.pi, Work.EQ.pk r (θ - φ) = 2 * Real.pi := by
  rw [integral_comp_sub_left (fun ψ : ℝ => Work.EQ.pk r ψ) θ]
  have h0 : θ - 0 = θ := by ring
  rw [h0]
  have hper := (pk_periodic r).intervalIntegral_add_eq (θ - 2 * Real.pi) 0
  have h1 : θ - 2 * Real.pi + 2 * Real.pi = θ := by ring
  rw [h1, zero_add] at hper
  rw [hper]
  exact integral_pk_zero_two_pi r hr hr1

/-- On `[0, π]` the Poisson kernel is antitone in the angle. -/
lemma pk_antitone_on (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) {δ ψ : ℝ} (hδ : 0 < δ)
    (hδψ : δ ≤ ψ) (hψπ : ψ ≤ Real.pi) : Work.EQ.pk r ψ ≤ Work.EQ.pk r δ := by
  have hcos : Real.cos ψ ≤ Real.cos δ :=
    Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt hδ) hψπ hδψ
  have hnum : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hDδ : 0 < 1 - 2 * r * Real.cos δ + r ^ 2 := by
    have hc : Real.cos δ ≤ 1 := Real.cos_le_one δ
    nlinarith [sq_nonneg (1 - r)]
  have hle : 1 - 2 * r * Real.cos δ + r ^ 2 ≤ 1 - 2 * r * Real.cos ψ + r ^ 2 := by
    nlinarith [hcos, hr0]
  simp only [Work.EQ.pk]
  exact div_le_div_of_nonneg_left hnum hDδ hle

/-- **The Poisson kernel is uniformly small away from the singular direction.**
For every `δ ∈ (0, π)` and `C > 0` the kernel is eventually `≤ C` on `[δ, 2π - δ]`. -/
theorem pk_far_bound (δ C : ℝ) (hδ : 0 < δ) (hδπ : δ < Real.pi) (hC : 0 < C) :
    ∀ᶠ r in nhdsWithin (1:ℝ) (Set.Iio 1),
      ∀ ψ ∈ Set.Icc δ (2 * Real.pi - δ), Work.EQ.pk r ψ ≤ C := by
  have h01 : ∀ᶠ r in nhdsWithin (1:ℝ) (Set.Iio 1), (0:ℝ) < r ∧ r < 1 := by
    have hlt : ∀ᶠ r in nhdsWithin (1:ℝ) (Set.Iio 1), r < 1 := self_mem_nhdsWithin
    have hgt : ∀ᶠ r in nhdsWithin (1:ℝ) (Set.Iio 1), (0:ℝ) < r := by
      filter_upwards [nhdsWithin_le_nhds
        (Ioi_mem_nhds (show (0:ℝ) < 1 by norm_num))] with r hr
      exact hr
    filter_upwards [hlt, hgt] with r h1 h2
    exact ⟨h2, h1⟩
  filter_upwards [h01, eventually_pk_lt δ C hδ hC] with r hr hlt
  intro ψ hψ
  have hδC : Work.EQ.pk r δ < C := hlt δ ⟨le_rfl, le_of_lt hδπ⟩
  rcases lt_or_ge ψ Real.pi with hψπ | hψπ
  · have hmono : Work.EQ.pk r ψ ≤ Work.EQ.pk r δ :=
      pk_antitone_on r hr.1.le hr.2 (δ := δ) (ψ := ψ) hδ hψ.1 (le_of_lt hψπ)
    linarith
  · have hmem : 2 * Real.pi - ψ ∈ Set.Icc δ Real.pi := by
      constructor
      · linarith [hψ.2]
      · linarith
    have hkey : Work.EQ.pk r ψ = Work.EQ.pk r (2 * Real.pi - ψ) := by
      simp only [Work.EQ.pk, Real.cos_two_pi_sub]
    rw [hkey]
    have hmono : Work.EQ.pk r (2 * Real.pi - ψ) ≤ Work.EQ.pk r δ :=
      pk_antitone_on r hr.1.le hr.2 (δ := δ) (ψ := 2 * Real.pi - ψ) hδ hmem.1 hmem.2
    linarith

/-- **Symmetrization of the near integral.**  The integral of `pk r (θ - ·)` against `h` over the
interval `(θ-δ, θ+δ)` equals the integral over a half period of `pk r ·` against the symmetrized
weight `h (θ + ·) + h (θ - ·)`. -/
theorem pk_shift_intervalIntegral (r θ δ : ℝ) (h : ℝ → ℝ) (hδ : 0 ≤ δ)
    (h1 : IntervalIntegrable (fun φ => Work.EQ.pk r (θ-φ) * h φ) volume (θ-δ) (θ+δ)) :
    ∫ φ in (θ-δ)..(θ+δ), Work.EQ.pk r (θ-φ) * h φ
      = ∫ ψ in (0:ℝ)..δ, Work.EQ.pk r ψ * (h (θ+ψ) + h (θ-ψ)) := by
  have hA : θ - (θ - δ) = δ := by ring
  have hB : θ - (θ + δ) = -δ := by ring
  have hI' : IntervalIntegrable (fun y : ℝ => Work.EQ.pk r y * h (θ - y)) volume δ (-δ) := by
    have hh := h1.comp_sub_left θ (by exact enorm_ne_top)
    rw [hA, hB] at hh
    exact hh.congr (fun y _ => by rw [show θ - (θ - y) = y by ring])
  have hI : IntervalIntegrable (fun y : ℝ => Work.EQ.pk r y * h (θ - y)) volume (-δ) δ := hI'.symm
  have hcongr : (∫ φ in (θ-δ)..(θ+δ), Work.EQ.pk r (θ-φ) * h φ)
      = ∫ φ in (θ-δ)..(θ+δ), (fun y : ℝ => Work.EQ.pk r y * h (θ - y)) (θ - φ) := by
    apply intervalIntegral.integral_congr
    intro φ _
    show Work.EQ.pk r (θ-φ) * h φ = Work.EQ.pk r (θ-φ) * h (θ - (θ-φ))
    rw [show θ - (θ - φ) = φ by ring]
  rw [hcongr, intervalIntegral.integral_comp_sub_left
    (fun y : ℝ => Work.EQ.pk r y * h (θ - y)) θ, hB, hA]
  have hIneg : IntervalIntegrable (fun y : ℝ => Work.EQ.pk r y * h (θ - y)) volume (-δ) 0 := by
    refine hI.mono_set ?_
    rw [uIcc_of_le (show -δ ≤ 0 by linarith), uIcc_of_le (show -δ ≤ δ by linarith)]
    exact Icc_subset_Icc le_rfl hδ
  have hIpos : IntervalIntegrable (fun y : ℝ => Work.EQ.pk r y * h (θ - y)) volume (0:ℝ) δ := by
    refine hI.mono_set ?_
    rw [uIcc_of_le (show (0:ℝ) ≤ δ by linarith), uIcc_of_le (show -δ ≤ δ by linarith)]
    exact Icc_subset_Icc (by linarith) le_rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals hIneg hIpos]
  have hpk_even : ∀ y : ℝ, Work.EQ.pk r (-y) = Work.EQ.pk r y := fun y => by
    simp only [Work.EQ.pk, Real.cos_neg]
  have hneg : (∫ y in (-δ)..0, Work.EQ.pk r y * h (θ - y))
      = ∫ y in (0:ℝ)..δ, Work.EQ.pk r y * h (θ + y) := by
    have hcomp : (∫ y in (-δ)..0, Work.EQ.pk r y * h (θ - y))
        = ∫ y in (0:ℝ)..δ, Work.EQ.pk r (-y) * h (θ - -y) := by
      simpa only [neg_zero] using (intervalIntegral.integral_comp_neg
        (f := fun y : ℝ => Work.EQ.pk r y * h (θ - y)) (a := (0:ℝ)) (b := δ)).symm
    rw [hcomp]
    apply intervalIntegral.integral_congr
    intro y _
    show Work.EQ.pk r (-y) * h (θ - -y) = Work.EQ.pk r y * h (θ + y)
    rw [show θ - -y = θ + y by ring, hpk_even y]
  rw [hneg]
  have hIg2 : IntervalIntegrable (fun y : ℝ => Work.EQ.pk r y * h (θ + y)) volume (-δ) δ := by
    have hh := h1.comp_add_right θ (by exact enorm_ne_top)
    rw [show (θ - δ) - θ = -δ by ring, show (θ + δ) - θ = δ by ring] at hh
    refine hh.congr (fun y _ => ?_)
    show Work.EQ.pk r (θ - (y + θ)) * h (y + θ) = Work.EQ.pk r y * h (θ + y)
    rw [show θ - (y + θ) = -y by ring, hpk_even y, show y + θ = θ + y by ring]
  have hIg2' : IntervalIntegrable (fun y : ℝ => Work.EQ.pk r y * h (θ + y)) volume (0:ℝ) δ := by
    refine hIg2.mono_set ?_
    rw [uIcc_of_le (show (0:ℝ) ≤ δ by linarith), uIcc_of_le (show -δ ≤ δ by linarith)]
    exact Icc_subset_Icc (by linarith) le_rfl
  rw [← intervalIntegral.integral_add hIg2' hIpos]
  apply intervalIntegral.integral_congr
  intro y _
  ring

/-- **The far pieces of the period integral.**  If the kernel is bounded by `C` on the far range
`[δ, 2π-δ]` and `h ≥ 0`, then the two pieces of `∫₀^{2π} pk r (θ-φ) h φ dφ` lying outside
`(θ-δ, θ+δ)` are together at most `C` times the total mass of `h`. -/
theorem pk_far_piece_le (r C θ δ : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (hC : 0 ≤ C)
    (hδ0 : 0 < δ) (hδθ : δ < θ) (hθ2π : θ < 2 * Real.pi) (hδ2π : δ < 2 * Real.pi - θ)
    (h : ℝ → ℝ) (hh : ∀ x, 0 ≤ h x)
    (hint : IntervalIntegrable h volume (0:ℝ) (2 * Real.pi))
    (hbound : ∀ ψ ∈ Set.Icc δ (2 * Real.pi - δ), Work.EQ.pk r ψ ≤ C) :
    (∫ φ in (0:ℝ)..(θ-δ), Work.EQ.pk r (θ-φ) * h φ)
      + (∫ φ in (θ+δ)..(2 * Real.pi), Work.EQ.pk r (θ-φ) * h φ)
      ≤ C * (∫ φ in (0:ℝ)..(2 * Real.pi), h φ) := by
  have hθδ : 0 < θ - δ := by linarith
  have hθδ2 : θ + δ < 2 * Real.pi := by linarith
  have hcont : Continuous (fun φ : ℝ => Work.EQ.pk r (θ - φ)) :=
    (continuous_pk r hr0 hr1).comp (by fun_prop)
  have hpk_abs : ∀ φ : ℝ, Work.EQ.pk r (θ - φ) = Work.EQ.pk r |θ - φ| := by
    intro φ
    rcases lt_or_ge (θ - φ) 0 with h | h
    · rw [abs_of_neg h]
      simp only [Work.EQ.pk, Real.cos_neg]
    · rw [abs_of_nonneg h]
  have hint0 : IntervalIntegrable h volume (0:ℝ) (θ - δ) := by
    refine hint.mono_set ?_
    rw [uIcc_of_le (show (0:ℝ) ≤ θ - δ by linarith),
      uIcc_of_le (show (0:ℝ) ≤ 2 * Real.pi by positivity)]
    exact Icc_subset_Icc le_rfl (by linarith)
  have hint1 : IntervalIntegrable h volume (θ + δ) (2 * Real.pi) := by
    refine hint.mono_set ?_
    rw [uIcc_of_le (show θ + δ ≤ 2 * Real.pi by linarith),
      uIcc_of_le (show (0:ℝ) ≤ 2 * Real.pi by positivity)]
    exact Icc_subset_Icc (by linarith) le_rfl
  have hI0 : IntervalIntegrable (fun φ : ℝ => Work.EQ.pk r (θ-φ) * h φ)
      volume (0:ℝ) (θ - δ) :=
    (hint0.mul_continuousOn hcont.continuousOn).congr (fun x _ => by ring)
  have hI1 : IntervalIntegrable (fun φ : ℝ => Work.EQ.pk r (θ-φ) * h φ)
      volume (θ + δ) (2 * Real.pi) :=
    (hint1.mul_continuousOn hcont.continuousOn).congr (fun x _ => by ring)
  have hpiece0 : ∀ φ ∈ Set.Icc (0:ℝ) (θ - δ),
      Work.EQ.pk r (θ-φ) * h φ ≤ C * h φ := by
    intro φ hφ
    have hmem : |θ - φ| ∈ Set.Icc δ (2 * Real.pi - δ) := by
      rw [abs_of_pos (by linarith [hφ.2])]
      constructor <;> linarith [hφ.1, hφ.2]
    rw [hpk_abs φ]
    exact mul_le_mul_of_nonneg_right (hbound _ hmem) (hh φ)
  have hpiece1 : ∀ φ ∈ Set.Icc (θ + δ) (2 * Real.pi),
      Work.EQ.pk r (θ-φ) * h φ ≤ C * h φ := by
    intro φ hφ
    have hmem : |θ - φ| ∈ Set.Icc δ (2 * Real.pi - δ) := by
      rw [abs_of_neg (by linarith [hφ.1])]
      constructor <;> linarith [hφ.1, hφ.2]
    rw [hpk_abs φ]
    exact mul_le_mul_of_nonneg_right (hbound _ hmem) (hh φ)
  have hb0 : ∫ φ in (0:ℝ)..(θ-δ), Work.EQ.pk r (θ-φ) * h φ
      ≤ C * ∫ φ in (0:ℝ)..(θ-δ), h φ := by
    rw [← intervalIntegral.integral_const_mul]
    exact integral_mono_on (le_of_lt hθδ) hI0 (hint0.const_mul C) hpiece0
  have hb1 : ∫ φ in (θ+δ)..(2*Real.pi), Work.EQ.pk r (θ-φ) * h φ
      ≤ C * ∫ φ in (θ+δ)..(2*Real.pi), h φ := by
    rw [← intervalIntegral.integral_const_mul]
    exact integral_mono_on (le_of_lt hθδ2) hI1 (hint1.const_mul C) hpiece1
  have hintm : IntervalIntegrable h volume (θ - δ) (θ + δ) := by
    refine hint.mono_set ?_
    rw [uIcc_of_le (show θ - δ ≤ θ + δ by linarith),
      uIcc_of_le (show (0:ℝ) ≤ 2 * Real.pi by positivity)]
    exact Icc_subset_Icc (by linarith) (by linarith)
  have hsum : (∫ φ in (0:ℝ)..(θ-δ), h φ) + (∫ φ in (θ+δ)..(2 * Real.pi), h φ)
      ≤ ∫ φ in (0:ℝ)..(2 * Real.pi), h φ := by
    have hs1 := intervalIntegral.integral_add_adjacent_intervals hint0 hintm
    have hs2 := intervalIntegral.integral_add_adjacent_intervals (hint0.trans hintm) hint1
    have hmid : 0 ≤ ∫ φ in (θ-δ)..(θ+δ), h φ :=
      intervalIntegral.integral_nonneg (by linarith) (fun x hx => hh x)
    linarith [hs1, hs2, hmid]
  calc (∫ φ in (0:ℝ)..(θ-δ), Work.EQ.pk r (θ-φ) * h φ)
        + (∫ φ in (θ+δ)..(2 * Real.pi), Work.EQ.pk r (θ-φ) * h φ)
      ≤ C * (∫ φ in (0:ℝ)..(θ-δ), h φ) + C * (∫ φ in (θ+δ)..(2 * Real.pi), h φ) :=
        add_le_add hb0 hb1
    _ = C * ((∫ φ in (0:ℝ)..(θ-δ), h φ) + (∫ φ in (θ+δ)..(2 * Real.pi), h φ)) := by ring
    _ ≤ C * (∫ φ in (0:ℝ)..(2 * Real.pi), h φ) := mul_le_mul_of_nonneg_left hsum hC

end Work.EQ.Fatou
