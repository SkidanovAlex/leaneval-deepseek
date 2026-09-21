import Mathlib
import Submission.Work.Geometry.Ulam.odd_cap_centroid_moment_hasDerivAt_aux_general
import Submission.Work.Geometry.Ulam.odd_cap_centroid_moment_at_zero_general
import Submission.Commons.Geometry.Ulam.body_of_revolution_cap_volume_half_of_interval
import Submission.Commons.Geometry.Ulam.concaveOn_Icc_bounded
import Submission.Work.Geometry.Ulam.profile_measurable_smooth_general_inf
import Submission.Work.OddCurve.CapsGen.moment_hasDerivAt_gen_smooth
import Submission.Work.OddCurve.CapsGen.moment_deriv_eq_zero_gen_smooth

/-!
# The odd cap centroid moment identity (general interval, smooth regularity)

Copy of `Commons.Geometry.Ulam.odd_profile_cap_centroid_moment_eq_general` with the analytic
regularity hypotheses on `f` and `h` replaced by the smooth ones.  The two analytic ingredients
are replaced by the copies proved in this directory:
`moment_hasDerivAt_gen_smooth` and `moment_deriv_eq_zero_gen_smooth`; the auxiliary
`profile_measurable_smooth_general` by `profile_measurable_smooth_general_inf`.
-/

namespace Work.OddCurve.CapsGen

open Commons.Geometry.Ulam
open MeasureTheory Set Filter
open scoped Topology Interval ContDiff RealInnerProductSpace BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

lemma odd_profile_cap_centroid_moment_eq_general_smooth {n : ℕ} (hn : 1 ≤ n) {C : ℝ}
    {A B : ℝ} (hAB : A < B) {h x y f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc A B)
    (hf_cont : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Ioo A B))
    (hf_conc : ConcaveOn ℝ (Set.Icc A B) f)
    (hf_left : f A = 0) (hf_right : f B = 0)
    (hf_pos : ∀ t ∈ Set.Ioo A B, 0 < f t)
    (hh_cont : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h Set.univ)
    (h0 : h 0 = 0)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hxy_inside : ∀ s : ℝ, 0 < s → -x s ∈ Set.Ioo A B ∧ y s ∈ Set.Ioo A B)
    (h_moment : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) =
        C / Real.sqrt (1 + s ^ 2))
    (h_center : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) *
          (t + deriv h s)) = 0) :
    ∀ s : ℝ, 0 < s →
      (∫ t in A..B,
          ∫ z in (-f t)..(max (-f t) (min (f t) (s * t + h s))),
            (t + s * z) * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2))) =
        (1 / 2 : ℝ) * ∫ t in A..B,
          ∫ z in (-f t)..(f t), t * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)) := by
  classical
  let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)
  let Afun : ℝ → ℝ := fun r =>
    ∫ t in A..B,
      ∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))), (t + r * z) * W t z
  have hf_nonneg : ∀ t ∈ Set.Icc A B, 0 ≤ f t :=
    profile_nonneg_Icc_general (a := A) (b := B) hAB.le hf_conc hf_left hf_right
  have hf_meas : Measurable f :=
    profile_measurable_smooth_general_inf (a := A) (b := B) hAB.le hf_support hf_cont hf_left hf_right
  have hf_bdd : Bornology.IsBounded (f '' Set.Icc A B) :=
    concaveOn_Icc_bounded hAB.le hf_conc
  have hcont : ContinuousOn Afun (Set.Ici 0) := by
    intro r hr
    exact (odd_cap_centroid_moment_hasDerivAt_general_smooth (n := n) (f := f) (h := h) (A := A) (B := B) hAB
      hn hf_nonneg hf_meas hf_bdd hh_cont r).continuousAt.continuousWithinAt
  have hderiv : ∀ r > 0, HasDerivAt Afun 0 r := by
    intro r hr
    have hd := odd_cap_centroid_moment_hasDerivAt_general_smooth (n := n) (f := f) (h := h) (A := A) (B := B) hAB
      hn hf_nonneg hf_meas hf_bdd hh_cont r
    have hz := odd_cap_centroid_moment_deriv_eq_zero_general_smooth (n := n) hn (C := C) (A := A) (B := B) hAB
      hf_support hf_cont hf_conc hf_left hf_right hf_pos hh_cont h0 hxy hxy_inside h_moment h_center r hr
    simpa [Afun, W] using hd.congr_deriv hz
  have hconst : ∀ r > 0, Afun r = Afun 0 := const_on_Ioi_of_deriv_zero hderiv hcont
  have hA0 : Afun 0 = ∫ t in A..B, ∫ z in (-f t)..0, t * W t z := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc A B := by
      simpa [Set.uIcc_of_le hAB.le] using ht
    have hf_nonneg_t : 0 ≤ f t := hf_nonneg t htIcc
    have hup : max (-f t) (min (f t) (0 * t + h 0)) = 0 := by
      rw [h0]
      simp [hf_nonneg_t]
    change (∫ z in (-f t)..(max (-f t) (min (f t) (0 * t + h 0))),
        (t + 0 * z) * W t z) = ∫ z in (-f t)..0, t * W t z
    rw [hup]
    apply intervalIntegral.integral_congr
    intro z hz
    ring
  have hhalf := odd_cap_centroid_moment_at_zero_general (n := n) (f := f) (A := A) (B := B) hAB hf_nonneg
  intro s hs
  calc
    (∫ t in A..B,
        ∫ z in (-f t)..(max (-f t) (min (f t) (s * t + h s))),
          (t + s * z) * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)))
        = Afun s := by simp [Afun, W]
    _ = Afun 0 := hconst s hs
    _ = ∫ t in A..B, ∫ z in (-f t)..0, t * W t z := hA0
    _ = (1 / 2 : ℝ) * ∫ t in A..B,
        ∫ z in (-f t)..(f t), t * W t z := hhalf
    _ = (1 / 2 : ℝ) * ∫ t in A..B,
        ∫ z in (-f t)..(f t), t * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)) := by
        simp [W]

end Work.OddCurve.CapsGen
