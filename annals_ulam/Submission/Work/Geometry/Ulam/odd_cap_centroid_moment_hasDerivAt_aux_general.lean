import Mathlib
import Submission.Commons.Geometry.Ulam.moment_h_bounds
import Submission.Commons.Geometry.Ulam.ball_cap_first_moment_eq
import Submission.Commons.Geometry.Ulam.odd_moment_integral_hasDerivAt
import Submission.Commons.Geometry.Ulam.body_of_revolution_cap_volume_half_of_interval
import Submission.Work.Geometry.Ulam.norm_odd_cap_centroid_slice_integral_le_general
import Submission.Work.Geometry.Ulam.odd_cap_centroid_hlin_hderiv_general

namespace Commons.Geometry.Ulam

open MeasureTheory Set Filter
open scoped Topology Interval ContDiff RealInnerProductSpace BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- General `A < B` version of `odd_cap_centroid_moment_hasDerivAt_aux`.
The support-size factor is `T = max |A| |B|`; it is threaded through
`hL_bound`, `Kline`, `Bint`, and `B`. -/
lemma cap_slice_hasDerivAt_of_cont {F s t dh : ℝ} {h : ℝ → ℝ}
    {g : ℝ → ℝ} (hg_cont : Continuous g)
    (hg_zero_left : g (-F) = 0) (hg_zero_right : g F = 0)
    (hF : 0 ≤ F) (hh : HasDerivAt h dh s) :
    HasDerivAt
      (fun r : ℝ =>
        ∫ z in (-F)..(max (-F) (min F (r * t + h r))), g z)
      (if -F < s * t + h s ∧ s * t + h s < F then
          g (s * t + h s) * (t + dh)
        else 0) s := by
  let a : ℝ := -F
  let b : ℝ := F
  let x : ℝ → ℝ := fun r => r * t + h r
  let u : ℝ → ℝ := fun r => max a (min b (x r))
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith
  have hx : HasDerivAt x (t + dh) s := by
    have h1 : HasDerivAt (fun r : ℝ => r * t) t s := by
      simpa using (hasDerivAt_id s).mul_const t
    exact h1.add hh
  have hx_cont : ContinuousAt x s := hx.continuousAt
  have hxO : (fun r : ℝ => x r - x s) =O[𝓝 s] (fun r : ℝ => r - s) :=
    hx.isBigO_sub
  have hu_cont : ContinuousAt u s := by
    dsimp [u, a, b]
    have hmin : ContinuousAt (fun r : ℝ => min F (x r)) s :=
      continuous_min.continuousAt.comp₂ continuousAt_const hx_cont
    have hmax : ContinuousAt (fun r : ℝ => max (-F) (min F (x r))) s :=
      continuous_max.continuousAt.comp₂ continuousAt_const hmin
    simpa using hmax
  have huO : (fun r : ℝ => u r - u s) =O[𝓝 s] (fun r : ℝ => r - s) := by
    dsimp [u, a, b]
    exact isBigO_clamp_sub hxO
  have hP_left : HasDerivAt (fun y : ℝ => ∫ z in a..y, g z) 0 a := by
    have h := (hg_cont.integral_hasStrictDerivAt a a).hasDerivAt
    simpa [a, hg_zero_left] using h
  have hP_right : HasDerivAt (fun y : ℝ => ∫ z in a..y, g z) 0 b := by
    have h := (hg_cont.integral_hasStrictDerivAt a b).hasDerivAt
    simpa [b, hg_zero_right] using h
  by_cases hcond : -F < s * t + h s ∧ s * t + h s < F
  · have hxs_lower : a < x s := by
      dsimp [x, a]
      simpa using hcond.1
    have hxs_upper : x s < b := by
      dsimp [x, b]
      simpa using hcond.2
    have h_event_lower : ∀ᶠ r in 𝓝 s, a < x r := by
      have hmem : {r : ℝ | a < x r} ∈ 𝓝 s :=
        hx_cont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hxs_lower)
      exact Filter.eventually_iff.mpr hmem
    have h_event_upper : ∀ᶠ r in 𝓝 s, x r < b := by
      have hmem : {r : ℝ | x r < b} ∈ 𝓝 s :=
        hx_cont.preimage_mem_nhds (isOpen_Iio.mem_nhds hxs_upper)
      exact Filter.eventually_iff.mpr hmem
    have h_event_u : ∀ᶠ r in 𝓝 s, u r = x r := by
      filter_upwards [h_event_lower, h_event_upper] with r hr_lower hr_upper
      dsimp [u, a, b]
      rw [min_eq_right hr_upper.le, max_eq_right hr_lower.le]
    have hP_deriv : HasDerivAt (fun y : ℝ => ∫ z in a..y, g z) (g (x s)) (x s) :=
      (hg_cont.integral_hasStrictDerivAt a (x s)).hasDerivAt
    have hcomp : HasDerivAt ((fun y : ℝ => ∫ z in a..y, g z) ∘ x)
        (g (x s) * (t + dh)) s := by
      simpa [Function.comp_def] using hP_deriv.comp s hx
    have h_event : (fun r : ℝ => ∫ z in (-F)..(max (-F) (min F (r * t + h r))), g z) =ᶠ[𝓝 s]
        ((fun y : ℝ => ∫ z in a..y, g z) ∘ x) := by
      filter_upwards [h_event_u] with r hr
      have hr' : max (-F) (min F (r * t + h r)) = r * t + h r := by
        simpa [u, x, a, b] using hr
      simp [a, x, hr']
    have hmain : HasDerivAt
        (fun r : ℝ => ∫ z in (-F)..(max (-F) (min F (r * t + h r))), g z)
        (g (x s) * (t + dh)) s :=
      HasDerivAt.congr_of_eventuallyEq hcomp h_event
    simpa [x, hcond] using hmain
  · have hcond_false : ¬ (-F < s * t + h s ∧ s * t + h s < F) := hcond
    by_cases hle_lower : s * t + h s ≤ -F
    · have hxs_lower : x s ≤ a := by
        dsimp [x, a]
        simpa using hle_lower
      have hqs : u s = a := by
        dsimp [u, a, b]
        rw [min_eq_right (le_trans hxs_lower hab)]
        rw [max_eq_left hxs_lower]
      have hqO : (fun r : ℝ => u r - a) =O[𝓝 s] (fun r : ℝ => r - s) := by
        simpa [hqs] using huO
      have hderiv0 : HasDerivAt (fun r : ℝ => ∫ z in a..(u r), g z) 0 s := by
        simpa using hasDerivAt_comp_of_deriv_zero_of_isBigO_sub
          (P := fun y : ℝ => ∫ z in a..y, g z) (q := u) (s := s) (b := a)
          hP_left hu_cont hqs hqO
      have hmain : HasDerivAt
          (fun r : ℝ => ∫ z in (-F)..(max (-F) (min F (r * t + h r))), g z) 0 s := by
        simpa [u, a, b] using hderiv0
      simpa [hcond_false] using hmain
    · have h_upper : F ≤ s * t + h s := by
        have h_not_lower : -F < s * t + h s := lt_of_not_ge hle_lower
        have h_not_upper : ¬ s * t + h s < F := by
          intro hup
          exact hcond_false ⟨h_not_lower, hup⟩
        exact le_of_not_gt h_not_upper
      have hxs_upper : b ≤ x s := by
        dsimp [x, b]
        simpa using h_upper
      have hqs : u s = b := by
        dsimp [u, a, b]
        rw [min_eq_left hxs_upper]
        rw [max_eq_right hab]
      have hqO : (fun r : ℝ => u r - b) =O[𝓝 s] (fun r : ℝ => r - s) := by
        simpa [hqs] using huO
      have hderiv0 : HasDerivAt (fun r : ℝ => ∫ z in a..(u r), g z) 0 s := by
        simpa using hasDerivAt_comp_of_deriv_zero_of_isBigO_sub
          (P := fun y : ℝ => ∫ z in a..y, g z) (q := u) (s := s) (b := b)
          hP_right hu_cont hqs hqO
      have hmain : HasDerivAt
          (fun r : ℝ => ∫ z in (-F)..(max (-F) (min F (r * t + h r))), g z) 0 s := by
        simpa [u, a, b] using hderiv0
      simpa [hcond_false] using hmain


lemma odd_cap_centroid_slice_hasDerivAt_general {n : ℕ} {F s t dh : ℝ} {h : ℝ → ℝ}
    (hn : 1 ≤ n) (hF : 0 ≤ F) (hh : HasDerivAt h dh s) :
    HasDerivAt
      (fun r : ℝ =>
        ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
          (t + r * z) * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)))
      (if -F < s * t + h s ∧ s * t + h s < F then
          (t + s * (s * t + h s)) * ((F ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
            Real.sqrt (F ^ 2 - (s * t + h s) ^ 2)) * (t + dh) -
          ((F ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (F ^ 2 - (s * t + h s) ^ 2)) /
            (2 * (n : ℝ) + 1)
        else 0) s := by
  let W : ℝ → ℝ := fun z => (F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)
  let g1 : ℝ → ℝ := W
  let g2 : ℝ → ℝ := fun z => z * W z
  have hg1_cont : Continuous g1 := by
    dsimp [g1, W]
    continuity
  have hg2_cont : Continuous g2 := by
    dsimp [g2, W]
    continuity
  have hW_left : W (-F) = 0 := by
    dsimp [W]
    ring_nf
    simp
  have hW_right : W F = 0 := by
    dsimp [W]
    ring_nf
    simp
  have hg1_left : g1 (-F) = 0 := by simpa [g1] using hW_left
  have hg1_right : g1 F = 0 := by simpa [g1] using hW_right
  have hg2_left : g2 (-F) = 0 := by
    dsimp [g2]
    rw [hW_left]
    simp
  have hg2_right : g2 F = 0 := by
    dsimp [g2]
    rw [hW_right]
    simp
  have hG1 := cap_slice_hasDerivAt_of_cont (F := F) (s := s) (t := t) (dh := dh) (h := h)
    (g := g1) hg1_cont hg1_left hg1_right hF hh
  have hG2 := cap_slice_hasDerivAt_of_cont (F := F) (s := s) (t := t) (dh := dh) (h := h)
    (g := g2) hg2_cont hg2_left hg2_right hF hh
  let G1 : ℝ → ℝ := fun r =>
    ∫ z in (-F)..(max (-F) (min F (r * t + h r))), g1 z
  let G2 : ℝ → ℝ := fun r =>
    ∫ z in (-F)..(max (-F) (min F (r * t + h r))), g2 z
  have hfun : (fun r : ℝ =>
        ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
          (t + r * z) * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2))) =
      fun r : ℝ => t * G1 r + r * G2 r := by
    funext r
    dsimp [G1, G2, g1, g2, W]
    have hpoint : (fun z : ℝ => (t + r * z) * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2))) =
        fun z : ℝ => t * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)) +
          r * (z * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2))) := by
      funext z
      ring
    calc
      (∫ z in (-F)..(max (-F) (min F (r * t + h r))),
          (t + r * z) * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)))
          = ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
              (t * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)) +
                r * (z * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)))) := by
              rw [hpoint]
      _ = (∫ z in (-F)..(max (-F) (min F (r * t + h r))),
              t * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2))) +
            ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
              r * (z * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2))) := by
              rw [intervalIntegral.integral_add]
              · exact (by continuity : Continuous (fun z : ℝ => t * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)))).intervalIntegrable _ _
              · exact (by continuity : Continuous (fun z : ℝ => r * (z * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2))))).intervalIntegrable _ _
      _ = t * (∫ z in (-F)..(max (-F) (min F (r * t + h r))),
                ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2))) +
            r * (∫ z in (-F)..(max (-F) (min F (r * t + h r))),
                z * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2))) := by
              rw [intervalIntegral.integral_const_mul]
              rw [intervalIntegral.integral_const_mul]
  have hderiv_aux : HasDerivAt (fun r : ℝ => t * G1 r + r * G2 r)
      (t * (if -F < s * t + h s ∧ s * t + h s < F then
          g1 (s * t + h s) * (t + dh) else 0) +
        (G2 s + s * (if -F < s * t + h s ∧ s * t + h s < F then
          g2 (s * t + h s) * (t + dh) else 0))) s := by
    have hprod : HasDerivAt (fun r : ℝ => r * G2 r) (G2 s + s * (if -F < s * t + h s ∧ s * t + h s < F then
        g2 (s * t + h s) * (t + dh) else 0)) s := by
      simpa [G2, Pi.mul_def] using (hasDerivAt_id s).mul hG2
    have hconst := hG1.const_mul t
    have hsum := hconst.add hprod
    simpa [G1, G2, Pi.add_def, Pi.mul_def, mul_comm, mul_left_comm, mul_assoc] using hsum
  have hmain : HasDerivAt
      (fun r : ℝ =>
        ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
          (t + r * z) * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)))
      (t * (if -F < s * t + h s ∧ s * t + h s < F then
          g1 (s * t + h s) * (t + dh) else 0) +
        (G2 s + s * (if -F < s * t + h s ∧ s * t + h s < F then
          g2 (s * t + h s) * (t + dh) else 0))) s := by
    rw [hfun]
    exact hderiv_aux
  by_cases hcond : -F < s * t + h s ∧ s * t + h s < F
  · have hL_lower : -F ≤ s * t + h s := le_of_lt hcond.1
    have hL_upper : s * t + h s ≤ F := le_of_lt hcond.2
    have hup : max (-F) (min F (s * t + h s)) = s * t + h s := by
      rw [min_eq_right hL_upper, max_eq_right hL_lower]
    have hG2_val : G2 s = - ((F ^ 2 - (s * t + h s) ^ 2) ^ n *
        Real.sqrt (F ^ 2 - (s * t + h s) ^ 2)) / (2 * (n : ℝ) + 1) := by
      dsimp [G2, g2, W]
      rw [hup]
      have hball := ball_cap_first_moment_eq (n := n) (r := F) (L := s * t + h s) hn hF hL_lower hL_upper
      simpa [mul_assoc] using hball
    have hderiv_eq : t * (g1 (s * t + h s) * (t + dh)) +
        (G2 s + s * (g2 (s * t + h s) * (t + dh))) =
        (t + s * (s * t + h s)) * ((F ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
          Real.sqrt (F ^ 2 - (s * t + h s) ^ 2)) * (t + dh) -
        ((F ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (F ^ 2 - (s * t + h s) ^ 2)) /
          (2 * (n : ℝ) + 1) := by
      have hg1val : g1 (s * t + h s) =
          (F ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - (s * t + h s) ^ 2) := by
        dsimp [g1, W]
      have hg2val : g2 (s * t + h s) =
          (s * t + h s) * ((F ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
            Real.sqrt (F ^ 2 - (s * t + h s) ^ 2)) := by
        dsimp [g2, W]
      rw [hg1val, hg2val, hG2_val]
      ring
    simpa [hcond, hderiv_eq] using hmain
  · have hmain' : HasDerivAt
      (fun r : ℝ =>
        ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
          (t + r * z) * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2)))
      (t * 0 + (G2 s + s * 0)) s := by
      simpa [hcond] using hmain
    have hG2_zero : G2 s = 0 := by
      by_cases hle_lower : s * t + h s ≤ -F
      · have hup : max (-F) (min F (s * t + h s)) = -F := by
          have hmin : min F (s * t + h s) = s * t + h s := min_eq_right (le_trans hle_lower (by linarith [hF]))
          rw [hmin]
          exact max_eq_left hle_lower
        dsimp [G2, g2, W]
        rw [hup]
        simp
      · have h_upper : F ≤ s * t + h s := by
          have h_not_lower : -F < s * t + h s := lt_of_not_ge hle_lower
          have h_not_upper : ¬ s * t + h s < F := by
            intro hup
            exact hcond ⟨h_not_lower, hup⟩
          exact le_of_not_gt h_not_upper
        have hup : max (-F) (min F (s * t + h s)) = F := by
          have hmin : min F (s * t + h s) = F := min_eq_left h_upper
          rw [hmin]
          exact max_eq_right (by linarith [hF])
        have h_int := ball_cap_first_moment_eq (n := n) (r := F) (L := F) hn hF (by linarith) (by rfl)
        have hzero : F ^ 2 - F ^ 2 = 0 := by ring
        dsimp [G2, g2, W]
        rw [hup]
        have h_int' : (∫ z in (-F)..F, z * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2))) =
            -((F ^ 2 - F ^ 2) ^ n * Real.sqrt (F ^ 2 - F ^ 2)) / (2 * (n : ℝ) + 1) := by
          simpa [mul_assoc] using h_int
        rw [h_int']
        simp [hzero]
    have hderiv_zero : t * 0 + (G2 s + s * 0) = 0 := by
      rw [hG2_zero]
      ring
    have hmain_zero : HasDerivAt
        (fun r : ℝ =>
          ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
            (t + r * z) * ((F ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (F ^ 2 - z ^ 2))) 0 s := by
      simpa [hG2_zero] using hmain'
    simpa [hcond] using hmain_zero



lemma odd_cap_centroid_moment_hasDerivAt_aux_general {n : ℕ} {f h : ℝ → ℝ}
    {A B : ℝ} (hAB : A < B) (hn : 1 ≤ n)
    (hf_nonneg : ∀ t ∈ Set.Icc A B, 0 ≤ f t)
    (hf_meas : Measurable f)
    (hf_bdd : Bornology.IsBounded (f '' Set.Icc A B))
    (hh_cont : ContDiffOn ℝ (⊤ : WithTop ℕ∞) h Set.univ)
    (s : ℝ) :
    HasDerivAt
      (fun r : ℝ =>
        ∫ t in A..B,
          ∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
            (t + r * z) * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)))
      (∫ t in A..B,
        if -f t < s * t + h s ∧ s * t + h s < f t then
          (t + s * (s * t + h s)) * ((f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
            Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) * (t + deriv h s) -
          ((f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) /
            (2 * (n : ℝ) + 1)
        else 0) s := by
  classical
  let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)
  let U : ℝ → ℝ → ℝ := fun r t => max (-f t) (min (f t) (r * t + h r))
  let F : ℝ → ℝ → ℝ := fun r t =>
    ∫ z in (-f t)..(U r t), (t + r * z) * W t z
  let F' : ℝ → ℝ → ℝ := fun r t =>
    if -f t < r * t + h r ∧ r * t + h r < f t then
      (t + r * (r * t + h r)) * ((f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) *
        Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) * (t + deriv h r) -
      ((f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) /
        (2 * (n : ℝ) + 1)
    else 0
  rcases hf_bdd.exists_pos_norm_le with ⟨M, hMpos, hM⟩
  have hf_abs_le : ∀ t ∈ Set.Icc A B, |f t| ≤ M := by
    intro t ht
    exact hM (f t) ⟨t, ht, rfl⟩
  have hf_le_M : ∀ t ∈ Set.Icc A B, f t ≤ M := by
    intro t ht
    have hnonneg : 0 ≤ f t := hf_nonneg t ht
    simpa [abs_of_nonneg hnonneg] using hf_abs_le t ht
  have hM_nonneg : 0 ≤ M := le_of_lt hMpos
  have h_deriv_cont_on_univ : ContinuousOn (deriv h) Set.univ := by
    exact hh_cont.continuousOn_deriv_of_isOpen isOpen_univ (by simp)
  have h_deriv_cont : Continuous (deriv h) := by
    rwa [continuousOn_univ] at h_deriv_cont_on_univ
  have h_cont_on_univ : ContinuousOn h Set.univ := hh_cont.continuousOn
  have h_cont : Continuous h := by
    rwa [continuousOn_univ] at h_cont_on_univ
  have hh_meas : Measurable h := h_cont.measurable
  have hderiv_meas : Measurable (deriv h) := h_deriv_cont.measurable
  let S : Set ℝ := Set.Icc (s - 1) (s + 1)
  have hS_mem : S ∈ 𝓝 s := by
    dsimp [S]
    rw [Metric.mem_nhds_iff]
    refine ⟨1, by norm_num, ?_⟩
    intro r hr
    have hdist : dist r s < 1 := by simpa [Metric.mem_ball] using hr
    rw [Real.dist_eq] at hdist
    have habs := abs_lt.mp hdist
    constructor <;> linarith
  have h_deriv_cont_on_S : ContinuousOn (deriv h) S := h_deriv_cont.continuousOn
  obtain ⟨Ch, hCh⟩ := (isCompact_Icc : IsCompact (Set.Icc (s - 1) (s + 1))).exists_bound_of_continuousOn
    h_deriv_cont_on_S
  let C : ℝ := max Ch 1
  have hC_nonneg : 0 ≤ C := by dsimp [C]; positivity
  have hderiv_bound : ∀ r ∈ S, |deriv h r| ≤ C := by
    intro r hr
    have := hCh r hr
    exact le_trans this (le_max_left _ _)
  have h_cont_on_S : ContinuousOn h S := h_cont.continuousOn
  obtain ⟨Hh, hHh⟩ := (isCompact_Icc : IsCompact (Set.Icc (s - 1) (s + 1))).exists_bound_of_continuousOn
    h_cont_on_S
  let H : ℝ := max |Hh| 1
  have hH_nonneg : 0 ≤ H := by dsimp [H]; positivity
  have h_bound : ∀ r ∈ S, |h r| ≤ H := by
    intro r hr
    have hle := hHh r hr
    have hle' : |h r| ≤ |Hh| := by
      simpa [Real.norm_eq_abs] using le_trans hle (le_abs_self Hh)
    exact le_trans hle' (le_max_left _ _)
  let R : ℝ := |s| + 1
  have hR_nonneg : 0 ≤ R := by dsimp [R]; positivity
  have hR_mem : ∀ r ∈ S, |r| ≤ R := by
    intro r hr
    have hdist : |r - s| ≤ 1 := by
      rcases hr with ⟨h1, h2⟩
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hle : |r| ≤ |s| + |r - s| := by
      calc |r| = |s + (r - s)| := by ring_nf
        _ ≤ |s| + |r - s| := abs_add_le _ _
    dsimp [R]
    nlinarith
  let T : ℝ := max |A| |B|
  have hT_nonneg : 0 ≤ T := by dsimp [T]; positivity
  let Kline : ℝ := T + R * (R * T + H)
  let Wbase : ℝ := (M ^ 2) ^ (n - 1) * M
  have hKline_nonneg : 0 ≤ Kline := by dsimp [Kline]; positivity
  have hWbase_nonneg : 0 ≤ Wbase := by dsimp [Wbase]; positivity
  let Bint : ℝ := (T + |s| * M) * (2 * M) * Wbase
  have hBint_nonneg : 0 ≤ Bint := by dsimp [Bint]; positivity
  let Bbound : ℝ := Kline * Wbase * (T + C) + (M ^ 2) ^ n * M / (2 * (n : ℝ) + 1)
  have hBbound_nonneg : 0 ≤ Bbound := by
    dsimp [Bbound]
    positivity
  have hL_bound : ∀ r ∈ S, ∀ t ∈ Set.Icc A B, |r * t + h r| ≤ R * T + H := by
    intro r hr t ht
    have ht_abs : |t| ≤ T := by
      rw [abs_le]
      constructor
      · have hA_le : A ≤ t := ht.1
        have hnegT_le_A : -T ≤ A := by
          dsimp [T]
          have h1 : -max |A| |B| ≤ -|A| := neg_le_neg (le_max_left |A| |B|)
          have h2 : -|A| ≤ A := neg_abs_le A
          linarith
        linarith
      · have htB : t ≤ B := ht.2
        have hB_le_T : B ≤ T := by
          dsimp [T]
          exact le_trans (le_abs_self B) (le_max_right |A| |B|)
        linarith
    calc
      |r * t + h r| ≤ |r * t| + |h r| := abs_add_le _ _
      _ = |r| * |t| + |h r| := by rw [abs_mul]
      _ ≤ R * T + H := by
        exact add_le_add (mul_le_mul (hR_mem r hr) ht_abs (abs_nonneg t) hR_nonneg) (h_bound r hr)
      _ = R * T + H := by ring
  have hF_meas : ∀ᶠ r in 𝓝 s, AEStronglyMeasurable (F r) (volume.restrict (Set.uIoc A B)) := by
    filter_upwards [hS_mem] with r hr
    have hLm : Measurable (fun t : ℝ => -f t) := by fun_prop
    have hUm : Measurable (fun t : ℝ => max (-f t) (min (f t) (r * t + h r))) := by fun_prop
    have hg : Measurable (Function.uncurry (fun t z : ℝ => (t + r * z) * W t z)) := by fun_prop
    exact (aeStronglyMeasurable_intervalIntegral_param hLm hUm hg).restrict
  have hF_int : IntervalIntegrable (F s) volume A B := by
    rw [intervalIntegrable_iff]
    have hmeas : AEStronglyMeasurable (F s) (volume.restrict (Set.uIoc A B)) := by
      exact hF_meas.self_of_nhds
    have hbnd' := norm_odd_cap_centroid_slice_integral_le_general (n := n) (f := f) (h := h) (M := M) (A := A) (B := B) hAB
      hf_le_M hf_nonneg hM_nonneg s
    have hbnd : ∀ᵐ t ∂volume.restrict (Set.uIoc A B), ‖F s t‖ ≤ Bint := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hbnd'] with t ht
      intro htIoc
      have htIoc' : t ∈ Set.Ioc A B := by
        simpa [Set.uIoc_of_le (hAB.le)] using htIoc
      have htcc : t ∈ Set.Icc A B := Set.Ioc_subset_Icc_self htIoc'
      have ht_abs : |t| ≤ T := by
        rw [abs_le]
        constructor
        · have hA_le : A ≤ t := htcc.1
          have hnegT_le_A : -T ≤ A := by
            dsimp [T]
            have h1 : -max |A| |B| ≤ -|A| := neg_le_neg (le_max_left |A| |B|)
            have h2 : -|A| ≤ A := neg_abs_le A
            linarith
          linarith
        · have htB : t ≤ B := htcc.2
          have hB_le_T : B ≤ T := by
            dsimp [T]
            exact le_trans (le_abs_self B) (le_max_right |A| |B|)
          linarith
      have hle : |t| + |s| * M ≤ T + |s| * M := by nlinarith [ht_abs]
      have hbound_t := ht htIoc
      calc
        ‖F s t‖ ≤ (|t| + |s| * M) * (2 * M) * Wbase := by
          simpa [F, U, W, Wbase] using hbound_t
        _ ≤ (T + |s| * M) * (2 * M) * Wbase := by
          nlinarith [hle, (by positivity : 0 ≤ (2 * M) * Wbase)]
        _ = Bint := by dsimp [Bint]
    exact IntegrableOn.of_bound (by
        rw [Set.uIoc_of_le (hAB.le)]
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top) hmeas _ hbnd
  have hF'_meas : AEStronglyMeasurable (F' s) (volume.restrict (Set.uIoc A B)) := by
    have h_cond_meas : MeasurableSet {t : ℝ | -f t < s * t + h s ∧ s * t + h s < f t} := by
      apply MeasurableSet.inter
      · exact measurableSet_lt hf_meas.neg (by fun_prop)
      · exact measurableSet_lt (by fun_prop) hf_meas
    have h_then_meas : Measurable (fun t : ℝ =>
        (t + s * (s * t + h s)) * ((f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
          Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) * (t + deriv h s) -
        ((f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) /
          (2 * (n : ℝ) + 1)) := by
      fun_prop
    exact (Measurable.ite h_cond_meas h_then_meas measurable_const).aestronglyMeasurable.restrict
  have h_bound' : ∀ᵐ t ∂volume, t ∈ Set.uIoc A B → ∀ r ∈ S, ‖F' r t‖ ≤ Bbound := by
    filter_upwards [] with t ht r hr
    have htIoc : t ∈ Set.Ioc A B := by
      simpa [Set.uIoc_of_le (hAB.le)] using ht
    have htcc : t ∈ Set.Icc A B := Set.Ioc_subset_Icc_self htIoc
    have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
    have hft_le : f t ≤ M := hf_le_M t htcc
    by_cases hcond : -f t < r * t + h r ∧ r * t + h r < f t
    · have hL_abs : |r * t + h r| ≤ R * T + H := hL_bound r hr t htcc
      have hG_nonneg : 0 ≤ f t ^ 2 - (r * t + h r) ^ 2 := by
        have hL_abs_lt : |r * t + h r| < f t := by
          rw [abs_lt]
          exact ⟨hcond.1, hcond.2⟩
        nlinarith
      have hG_le : f t ^ 2 - (r * t + h r) ^ 2 ≤ M ^ 2 := by
        have hftsq : f t ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hft_nonneg hft_le 2
        nlinarith [sq_nonneg (r * t + h r)]
      have hWbase_le : |((f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) *
          Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2))| ≤ Wbase := by
        have hpow : |(f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1)| ≤ (M ^ 2) ^ (n - 1) := by
          rw [abs_pow, abs_of_nonneg hG_nonneg]
          exact pow_le_pow_left₀ hG_nonneg hG_le (n - 1)
        have hsqrt : |Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)| ≤ M := by
          rw [abs_of_nonneg (Real.sqrt_nonneg _)]
          exact (Real.sqrt_le_left hM_nonneg).2 hG_le
        dsimp [Wbase]
        simpa [abs_mul] using mul_le_mul hpow hsqrt (abs_nonneg _) (by positivity)
      have hWn_le : |((f t ^ 2 - (r * t + h r) ^ 2) ^ n *
          Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2))| ≤ (M ^ 2) ^ n * M := by
        have hpow : |(f t ^ 2 - (r * t + h r) ^ 2) ^ n| ≤ (M ^ 2) ^ n := by
          rw [abs_pow, abs_of_nonneg hG_nonneg]
          exact pow_le_pow_left₀ hG_nonneg hG_le n
        have hsqrt : |Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)| ≤ M := by
          rw [abs_of_nonneg (Real.sqrt_nonneg _)]
          exact (Real.sqrt_le_left hM_nonneg).2 hG_le
        simpa [abs_mul] using mul_le_mul hpow hsqrt (abs_nonneg _) (by positivity)
      have ht_abs : |t| ≤ T := by
        rw [abs_le]
        constructor
        · have hA_le : A ≤ t := htcc.1
          have hnegT_le_A : -T ≤ A := by
            dsimp [T]
            have h1 : -max |A| |B| ≤ -|A| := neg_le_neg (le_max_left |A| |B|)
            have h2 : -|A| ≤ A := neg_abs_le A
            linarith
          linarith
        · have htB : t ≤ B := htcc.2
          have hB_le_T : B ≤ T := by
            dsimp [T]
            exact le_trans (le_abs_self B) (le_max_right |A| |B|)
          linarith
      have hlin : |t + r * (r * t + h r)| ≤ Kline := by
        have := abs_t_add_r_line_le_general (h := h) (t := t) (r := r) (T := T) (R := R) (H := H) ht_abs (hR_mem r hr) hL_abs
        simpa [Kline] using this
      have hderiv_le : |t + deriv h r| ≤ T + C := by
        exact abs_t_add_deriv_le_general (h := h) (t := t) (r := r) (T := T) (C := C) ht_abs (hderiv_bound r hr)
      have hfirst : |(t + r * (r * t + h r)) * ((f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) *
          Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) * (t + deriv h r)| ≤
          Kline * Wbase * (T + C) := by
        have hprod1 : |(t + r * (r * t + h r)) * ((f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) *
            Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2))| ≤ Kline * Wbase := by
          simpa [abs_mul] using mul_le_mul hlin hWbase_le (abs_nonneg _) hKline_nonneg
        have hprod2 : |(t + r * (r * t + h r)) * ((f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) *
            Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) * (t + deriv h r)| ≤
            (Kline * Wbase) * (T + C) := by
          simpa [abs_mul] using mul_le_mul hprod1 hderiv_le (abs_nonneg _) (by positivity)
        simpa [mul_assoc] using hprod2
      have hsecond : |((f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) /
          (2 * (n : ℝ) + 1)| ≤ (M ^ 2) ^ n * M / (2 * (n : ℝ) + 1) := by
        have hden_nonneg : 0 ≤ 2 * (n : ℝ) + 1 := by positivity
        rw [abs_div, abs_of_nonneg hden_nonneg]
        exact div_le_div_of_nonneg_right hWn_le hden_nonneg
      have hsum_le : |(t + r * (r * t + h r)) * ((f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) *
          Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) * (t + deriv h r) -
        ((f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) /
          (2 * (n : ℝ) + 1)| ≤ Bbound := by
        have htri := abs_sub_le ((t + r * (r * t + h r)) *
            ((f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) *
            (t + deriv h r)) 0
            (((f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) /
              (2 * (n : ℝ) + 1))
        have htri' : |(t + r * (r * t + h r)) * ((f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) *
            Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) * (t + deriv h r) -
          ((f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) /
            (2 * (n : ℝ) + 1)| ≤
            |(t + r * (r * t + h r)) * ((f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) *
              Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) * (t + deriv h r)| +
            |((f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) /
              (2 * (n : ℝ) + 1)| := by
          simpa [sub_zero, zero_sub] using htri
        dsimp [Bbound]
        nlinarith [htri', hfirst, hsecond]
      dsimp [F']
      rw [if_pos hcond]
      exact hsum_le
    · dsimp [F']
      rw [if_neg hcond, abs_zero]
      exact hBbound_nonneg
  have h_bound_int : IntervalIntegrable (fun _ : ℝ => Bbound) volume A B := by
    exact intervalIntegrable_const
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc A B → ∀ r ∈ S,
      HasDerivAt (fun r => F r t) (F' r t) r := by
    filter_upwards [] with t ht r hr
    have htIoc : t ∈ Set.Ioc A B := by
      simpa [Set.uIoc_of_le (hAB.le)] using ht
    have htcc : t ∈ Set.Icc A B := Set.Ioc_subset_Icc_self htIoc
    have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
    have hh_deriv : HasDerivAt h (deriv h r) r := by
      have hd : DifferentiableAt ℝ h r := by
        exact (hh_cont.contDiffAt (by simp)).differentiableAt (by simp)
      exact hd.hasDerivAt
    have hslice := odd_cap_centroid_slice_hasDerivAt_general (n := n) (F := f t) (s := r) (t := t)
      (dh := deriv h r) (h := h) hn hft_nonneg hh_deriv
    simpa [F, F', U, W] using hslice
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (F := F) (F' := F') (x₀ := s) (s := S) (μ := volume) (a := A) (b := B)
    hS_mem hF_meas hF_int hF'_meas h_bound' h_bound_int h_diff).2
lemma odd_cap_centroid_moment_hasDerivAt_general {n : ℕ} {f h : ℝ → ℝ}
    {A B : ℝ} (hAB : A < B) (hn : 1 ≤ n)
    (hf_nonneg : ∀ t ∈ Set.Icc A B, 0 ≤ f t)
    (hf_meas : Measurable f)
    (hf_bdd : Bornology.IsBounded (f '' Set.Icc A B))
    (hh_cont : ContDiffOn ℝ (⊤ : WithTop ℕ∞) h Set.univ)
    (s : ℝ) :
    HasDerivAt
      (fun r : ℝ =>
        ∫ t in A..B,
          ∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
            (t + r * z) * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)))
      (∫ t in A..B,
        if -f t < s * t + h s ∧ s * t + h s < f t then
          (t + s * (s * t + h s)) * ((f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
            Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) * (t + deriv h s) -
          ((f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) /
            (2 * (n : ℝ) + 1)
        else 0) s := by
  exact odd_cap_centroid_moment_hasDerivAt_aux_general hAB hn hf_nonneg hf_meas hf_bdd hh_cont s

end Commons.Geometry.Ulam
