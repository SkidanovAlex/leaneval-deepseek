import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Submission.Commons.Geometry.Ulam.cap_slice_hasDerivAt
import Submission.Commons.Geometry.Ulam.cap_volume_continuousOn_Ici_zero

namespace Commons.Geometry.Ulam

open Set Filter MeasureTheory
open scoped Topology Interval ContDiff

private lemma cap_slice_hasDerivAt_of_cont {F s t dh : ℝ} {h : ℝ → ℝ}
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

-- Antiderivative of `z * (F^2 - z^2)^(n-1)`.

private lemma integral_z_mul_pow_sub {n : ℕ} (hn : 1 ≤ n) {F L : ℝ}
    (hL_lower : -F ≤ L) :
    (∫ z in (-F)..L, z * (F ^ 2 - z ^ 2) ^ (n - 1)) =
      - (F ^ 2 - L ^ 2) ^ n / (2 * (n : ℝ)) := by
  let P : ℝ → ℝ := fun z => - (F ^ 2 - z ^ 2) ^ n / (2 * (n : ℝ))
  let f' : ℝ → ℝ := fun z => z * (F ^ 2 - z ^ 2) ^ (n - 1)
  have hcontP : ContinuousOn P (Set.Icc (-F) L) := by
    have hcont : Continuous P := by
      dsimp [P]
      continuity
    exact hcont.continuousOn
  have hderiv : ∀ z ∈ Set.Ioo (-F) L, HasDerivAt P (f' z) z := by
    intro z hz
    have h1 : HasDerivAt (fun u : ℝ => F ^ 2 - u ^ 2) (0 - 2 * z) z := by
      have hu : HasDerivAt (fun u : ℝ => u ^ 2) (2 * z) z := by
        simpa using (hasDerivAt_pow 2 (z : ℝ))
      exact (hasDerivAt_const z (F ^ 2)).sub hu
    have h1' : HasDerivAt (fun u : ℝ => F ^ 2 - u ^ 2) (-(2 * z)) z := by
      exact h1.congr_deriv (by ring)
    have hpow : HasDerivAt (fun u : ℝ => (F ^ 2 - u ^ 2) ^ n)
        ((n : ℝ) * (F ^ 2 - z ^ 2) ^ (n - 1) * (-(2 * z))) z := h1'.pow n
    have hmain : HasDerivAt (fun u : ℝ => (F ^ 2 - u ^ 2) ^ n)
        (-(2 * (n : ℝ)) * z * (F ^ 2 - z ^ 2) ^ (n - 1)) z := by
      exact hpow.congr_deriv (by ring)
    have hc : HasDerivAt P (f' z) z := by
      have hn0 : (2 * (n : ℝ)) ≠ 0 := by
        have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hn)
        positivity
      have hneg := hmain.neg
      have hdiv := hneg.div_const (2 * (n : ℝ))
      have hfun : P =ᶠ[𝓝 z]
          (fun u : ℝ => (-(F ^ 2 - u ^ 2) ^ n) / (2 * (n : ℝ))) := by
        filter_upwards [] with u
        rfl
      have hder_eq : f' z = -(-(2 * (n : ℝ)) * z * (F ^ 2 - z ^ 2) ^ (n - 1)) /
          (2 * (n : ℝ)) := by
        dsimp [f']
        field_simp [hn0]
      exact (hdiv.congr_deriv hder_eq.symm).congr_of_eventuallyEq hfun
    simpa [P, f'] using hc
  have hint : IntervalIntegrable f' volume (-F) L := by
    have hcont : Continuous f' := by
      dsimp [f']
      continuity
    exact hcont.intervalIntegrable _ _
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := -F) (b := L)
    (f := P) (f' := f') hL_lower hcontP hderiv hint
  have hPL : P L = - (F ^ 2 - L ^ 2) ^ n / (2 * (n : ℝ)) := by
    dsimp [P]
  have hPmF : P (-F) = 0 := by
    dsimp [P]
    have hzero : F ^ 2 - (-F) ^ 2 = 0 := by ring
    have hn0 : n ≠ 0 := by omega
    simp [hzero, zero_pow hn0]
  calc
    (∫ z in (-F)..L, f' z) = P L - P (-F) := by simpa [f'] using hmain
    _ = - (F ^ 2 - L ^ 2) ^ n / (2 * (n : ℝ)) := by rw [hPL, hPmF, sub_zero]

-- Slice derivative for the centroid moment integrand.

private lemma cap_centroid_slice_hasDerivAt {n : ℕ} {F s t dh : ℝ} {h : ℝ → ℝ}
    (hn : 2 ≤ n) (hF : 0 ≤ F) (hh : HasDerivAt h dh s) :
    HasDerivAt
      (fun r : ℝ =>
        ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
          (t + r * z) * (F ^ 2 - z ^ 2) ^ (n - 1))
      (if -F < s * t + h s ∧ s * t + h s < F then
          (t + s * (s * t + h s)) * (F ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
            (t + dh) -
          (F ^ 2 - (s * t + h s) ^ 2) ^ n / (2 * (n : ℝ))
        else 0) s := by
  let W : ℝ → ℝ := fun z => (F ^ 2 - z ^ 2) ^ (n - 1)
  let g1 : ℝ → ℝ := W
  let g2 : ℝ → ℝ := fun z => z * W z
  have hg1_cont : Continuous g1 := by
    dsimp [g1, W]
    continuity
  have hg2_cont : Continuous g2 := by
    dsimp [g2, W]
    continuity
  have hnz : n - 1 ≠ 0 := by omega
  have hW_left : W (-F) = 0 := by
    dsimp [W]
    simp [zero_pow hnz]
  have hW_right : W F = 0 := by
    dsimp [W]
    simp [zero_pow hnz]
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
          (t + r * z) * (F ^ 2 - z ^ 2) ^ (n - 1)) =
      fun r : ℝ => t * G1 r + r * G2 r := by
    funext r
    dsimp [G1, G2, g1, g2, W]
    have hpoint : (fun z : ℝ => (t + r * z) * (F ^ 2 - z ^ 2) ^ (n - 1)) =
        fun z : ℝ => t * (F ^ 2 - z ^ 2) ^ (n - 1) + r * (z * (F ^ 2 - z ^ 2) ^ (n - 1)) := by
      funext z
      ring
    calc
      (∫ z in (-F)..(max (-F) (min F (r * t + h r))),
          (t + r * z) * (F ^ 2 - z ^ 2) ^ (n - 1))
          = ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
              (t * (F ^ 2 - z ^ 2) ^ (n - 1) + r * (z * (F ^ 2 - z ^ 2) ^ (n - 1))) := by
              rw [hpoint]
      _ = (∫ z in (-F)..(max (-F) (min F (r * t + h r))),
              t * (F ^ 2 - z ^ 2) ^ (n - 1)) +
            ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
              r * (z * (F ^ 2 - z ^ 2) ^ (n - 1)) := by
              rw [intervalIntegral.integral_add]
              · exact (by continuity : Continuous (fun z : ℝ => t * (F ^ 2 - z ^ 2) ^ (n - 1))).intervalIntegrable _ _
              · exact (by continuity : Continuous (fun z : ℝ => r * (z * (F ^ 2 - z ^ 2) ^ (n - 1)))).intervalIntegrable _ _
      _ = t * (∫ z in (-F)..(max (-F) (min F (r * t + h r))),
                (F ^ 2 - z ^ 2) ^ (n - 1)) +
            r * (∫ z in (-F)..(max (-F) (min F (r * t + h r))),
                z * (F ^ 2 - z ^ 2) ^ (n - 1)) := by
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
          (t + r * z) * (F ^ 2 - z ^ 2) ^ (n - 1))
      (t * (if -F < s * t + h s ∧ s * t + h s < F then
          g1 (s * t + h s) * (t + dh) else 0) +
        (G2 s + s * (if -F < s * t + h s ∧ s * t + h s < F then
          g2 (s * t + h s) * (t + dh) else 0))) s := by
    rw [hfun]
    exact hderiv_aux
  by_cases hcond : -F < s * t + h s ∧ s * t + h s < F
  · have hL_lower : -F ≤ s * t + h s := le_of_lt hcond.1
    have hG2_val : G2 s = - (F ^ 2 - (s * t + h s) ^ 2) ^ n / (2 * (n : ℝ)) := by
      have hup : max (-F) (min F (s * t + h s)) = s * t + h s := by
        rw [min_eq_right hcond.2.le, max_eq_right hcond.1.le]
      dsimp [G2, g2, W]
      rw [hup]
      simpa using integral_z_mul_pow_sub (n := n) (by omega) (F := F) (L := s * t + h s) hL_lower
    have hderiv_eq : t * (g1 (s * t + h s) * (t + dh)) +
        (G2 s + s * (g2 (s * t + h s) * (t + dh))) =
        (t + s * (s * t + h s)) * (F ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
          (t + dh) -
        (F ^ 2 - (s * t + h s) ^ 2) ^ n / (2 * (n : ℝ)) := by
      have hg1val : g1 (s * t + h s) = (F ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) := by
        dsimp [g1, W]
      have hg2val : g2 (s * t + h s) =
          (s * t + h s) * (F ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) := by
        dsimp [g2, W]
      rw [hg1val, hg2val, hG2_val]
      ring
    simpa [hcond, hderiv_eq] using hmain
  · have hmain' : HasDerivAt
      (fun r : ℝ =>
        ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
          (t + r * z) * (F ^ 2 - z ^ 2) ^ (n - 1))
      (t * 0 + (G2 s + s * 0)) s := by
      simpa [hcond] using hmain
    have hG2_zero : G2 s = 0 := by
      by_cases hle_lower : s * t + h s ≤ -F
      · have hup : max (-F) (min F (s * t + h s)) = -F := by
          have hmin : min F (s * t + h s) = s * t + h s := min_eq_right (le_trans hle_lower (by linarith [hF]))
          rw [hmin]
          exact max_eq_left hle_lower
        simp [G2, g2, W, hup]
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
        have h_int := integral_z_mul_pow_sub (n := n) (by omega) (F := F) (L := F) (by linarith [hF])
        have hzero : F ^ 2 - F ^ 2 = 0 := by ring
        simp [G2, g2, W, hup, h_int, hzero, zero_pow (by omega : n ≠ 0)]
    have hderiv_zero : t * 0 + (G2 s + s * 0) = 0 := by
      rw [hG2_zero]
      ring
    have hmain_zero : HasDerivAt
        (fun r : ℝ =>
          ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
            (t + r * z) * (F ^ 2 - z ^ 2) ^ (n - 1)) 0 s := by
      simpa [hG2_zero] using hmain'
    simpa [hcond] using hmain_zero


private lemma norm_cap_centroid_slice_integral_le {n : ℕ} {f h : ℝ → ℝ} {M : ℝ}
    (hf_le_M : ∀ t ∈ Set.Icc (-1 : ℝ) 1, f t ≤ M)
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t)
    (hM_nonneg : 0 ≤ M) :
    ∀ r : ℝ, ∀ᵐ t ∂volume, t ∈ Ι (-1 : ℝ) 1 →
      ‖(∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
          (t + r * z) * (f t ^ 2 - z ^ 2) ^ (n - 1))‖ ≤
        (|t| + |r| * M) * (2 * M) * (2 * M ^ 2) ^ (n - 1) := by
  intro r
  filter_upwards [] with t ht
  have htIoc : t ∈ Ioc (-1 : ℝ) 1 := by
    simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
  have htcc : t ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioc_subset_Icc_self htIoc
  have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
  have hft_le : f t ≤ M := hf_le_M t htcc
  let a : ℝ := -f t
  let b : ℝ := f t
  let U : ℝ := max a (min b (r * t + h r))
  let g : ℝ → ℝ := fun z => (t + r * z) * (f t ^ 2 - z ^ 2) ^ (n - 1)
  have ha_le_b : a ≤ b := by dsimp [a, b]; linarith
  have hU_mem : U ∈ Set.Icc a b := by
    dsimp [U]
    rw [Set.mem_Icc]
    constructor
    · exact le_max_left _ _
    · exact max_le ha_le_b (min_le_left _ _)
  have hUa : a ≤ U := hU_mem.1
  have hUb : U ≤ b := hU_mem.2
  have hg_bound : ∀ z ∈ Ι a U, ‖g z‖ ≤ (|t| + |r| * M) * (2 * M ^ 2) ^ (n - 1) := by
    intro z hz
    have hzIoc : z ∈ Ioc a U := by
      simpa [Set.uIoc_of_le hUa] using hz
    have hz_lower : -M ≤ z := by
      have ha_lower : -M ≤ a := by dsimp [a]; linarith
      exact le_trans ha_lower (le_of_lt hzIoc.1)
    have hz_upper : z ≤ M := by
      have hb_upper : b ≤ M := by dsimp [b]; linarith
      exact le_trans (le_trans hzIoc.2 hUb) hb_upper
    have hz_abs : |z| ≤ M := abs_le.mpr ⟨hz_lower, hz_upper⟩
    have hsq_le : |f t ^ 2 - z ^ 2| ≤ 2 * M ^ 2 := by
      have h1 : |f t ^ 2 - z ^ 2| ≤ f t ^ 2 + z ^ 2 := by
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg (f t), sq_nonneg z]
      have hftsq : f t ^ 2 ≤ M ^ 2 := by
        exact pow_le_pow_left₀ hft_nonneg hft_le 2
      have hzsq : z ^ 2 ≤ M ^ 2 := by
        calc z ^ 2 = |z| ^ 2 := by simp [sq_abs]
          _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg z) hz_abs 2
      have hsum : f t ^ 2 + z ^ 2 ≤ 2 * M ^ 2 := by nlinarith
      exact le_trans h1 hsum
    have hpow : |(f t ^ 2 - z ^ 2) ^ (n - 1)| ≤ (2 * M ^ 2) ^ (n - 1) := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hsq_le (n - 1)
    have hlin : |t + r * z| ≤ |t| + |r| * M := by
      calc
        |t + r * z| ≤ |t| + |r * z| := abs_add_le _ _
        _ = |t| + |r| * |z| := by rw [abs_mul]
        _ ≤ |t| + |r| * M := by
          nlinarith [mul_le_mul_of_nonneg_left hz_abs (abs_nonneg r)]
    dsimp [g]
    simpa [abs_mul] using mul_le_mul hlin hpow (abs_nonneg _) (by positivity)
  have hlen : |U - a| ≤ 2 * M := by
    rw [abs_of_nonneg (sub_nonneg.mpr hUa)]
    calc U - a ≤ b - a := sub_le_sub hUb le_rfl
      _ = 2 * f t := by dsimp [a, b]; ring
      _ ≤ 2 * M := mul_le_mul_of_nonneg_left hft_le (by norm_num)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := U)
      (C := (|t| + |r| * M) * (2 * M ^ 2) ^ (n - 1)) (f := g) hg_bound
  calc
    ‖∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
        (t + r * z) * (f t ^ 2 - z ^ 2) ^ (n - 1)‖
        = ‖∫ z in a..U, g z‖ := by simp [a, b, U, g]
    _ ≤ ((|t| + |r| * M) * (2 * M ^ 2) ^ (n - 1)) * |U - a| := hnorm
    _ ≤ ((|t| + |r| * M) * (2 * M ^ 2) ^ (n - 1)) * (2 * M) := by
        exact mul_le_mul_of_nonneg_left hlen (by positivity)
    _ = (|t| + |r| * M) * (2 * M) * (2 * M ^ 2) ^ (n - 1) := by ring

private lemma cap_centroid_moment_hasDerivAt_aux {n : ℕ} {f h : ℝ → ℝ}
    (hn : 2 ≤ n)
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t)
    (hf_meas : Measurable f)
    (hf_bdd : Bornology.IsBounded (f '' Set.Icc (-1 : ℝ) 1))
    (hh_cont : ContDiffOn ℝ (WithTop.some (⊤ : ℕ∞)) h Set.univ)
    (s : ℝ) :
    HasDerivAt
      (fun r : ℝ =>
        ∫ t in (-1 : ℝ)..1,
          ∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
            (t + r * z) * (f t ^ 2 - z ^ 2) ^ (n - 1))
      (∫ t in (-1 : ℝ)..1,
        if -f t < s * t + h s ∧ s * t + h s < f t then
          (t + s * (s * t + h s)) * (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
            (t + deriv h s) -
          (f t ^ 2 - (s * t + h s) ^ 2) ^ n / (2 * (n : ℝ))
        else 0) s := by
  classical
  let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1)
  let U : ℝ → ℝ → ℝ := fun r t => max (-f t) (min (f t) (r * t + h r))
  let F : ℝ → ℝ → ℝ := fun r t =>
    ∫ z in (-f t)..(U r t), (t + r * z) * W t z
  let F' : ℝ → ℝ → ℝ := fun r t =>
    if -f t < r * t + h r ∧ r * t + h r < f t then
      (t + r * (r * t + h r)) * (f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) *
        (t + deriv h r) -
      (f t ^ 2 - (r * t + h r) ^ 2) ^ n / (2 * (n : ℝ))
    else 0
  rcases hf_bdd.exists_pos_norm_le with ⟨M, hMpos, hM⟩
  have hf_abs_le : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |f t| ≤ M := by
    intro t ht
    exact hM (f t) ⟨t, ht, rfl⟩
  have hf_le_M : ∀ t ∈ Set.Icc (-1 : ℝ) 1, f t ≤ M := by
    intro t ht
    have hnonneg : 0 ≤ f t := hf_nonneg t ht
    simpa [abs_of_nonneg hnonneg] using hf_abs_le t ht
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
  let Kline : ℝ := 1 + R * (R + H)
  let Bq : ℝ := M ^ 2 + (R + H) ^ 2
  have hKline_nonneg : 0 ≤ Kline := by dsimp [Kline]; positivity
  have hBq_nonneg : 0 ≤ Bq := by dsimp [Bq]; positivity
  have hWbound_nonneg : 0 ≤ Bq ^ (n - 1) := by positivity
  let B : ℝ := Kline * Bq ^ (n - 1) * (1 + C) + Bq ^ n / (2 * (n : ℝ))
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hL_bound : ∀ r ∈ S, ∀ t ∈ Set.Icc (-1 : ℝ) 1, |r * t + h r| ≤ R + H := by
    intro r hr t ht
    have ht_abs : |t| ≤ 1 := by
      exact abs_le.mpr ⟨ht.1, by norm_num at ht ⊢; exact ht.2⟩
    calc
      |r * t + h r| ≤ |r * t| + |h r| := abs_add_le _ _
      _ = |r| * |t| + |h r| := by rw [abs_mul]
      _ ≤ R * 1 + H := by
        exact add_le_add (mul_le_mul (hR_mem r hr) ht_abs (abs_nonneg t) hR_nonneg) (h_bound r hr)
      _ = R + H := by ring
  have hF_meas : ∀ᶠ r in 𝓝 s, AEStronglyMeasurable (F r) (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    filter_upwards [hS_mem] with r hr
    have hLm : Measurable (fun t : ℝ => -f t) := by fun_prop
    have hUm : Measurable (fun t : ℝ => max (-f t) (min (f t) (r * t + h r))) := by fun_prop
    have hg : Measurable (Function.uncurry (fun t z : ℝ => (t + r * z) * W t z)) := by fun_prop
    exact (aeStronglyMeasurable_intervalIntegral_param hLm hUm hg).restrict
  have hF_int : IntervalIntegrable (F s) volume (-1 : ℝ) 1 := by
    rw [intervalIntegrable_iff]
    have hmeas : AEStronglyMeasurable (F s) (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
      exact hF_meas.self_of_nhds
    let Bint : ℝ := (1 + |s| * M) * (2 * M) * (2 * M ^ 2) ^ (n - 1)
    have hBint_nonneg : 0 ≤ Bint := by dsimp [Bint]; positivity
    have hbnd' := norm_cap_centroid_slice_integral_le (n := n) (f := f) (h := h) (M := M)
      hf_le_M hf_nonneg (le_of_lt hMpos) s
    have hbnd : ∀ᵐ t ∂volume.restrict (Set.uIoc (-1 : ℝ) 1), ‖F s t‖ ≤ Bint := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hbnd'] with t ht
      intro htIoc
      have htIoc' : t ∈ Set.Ioc (-1 : ℝ) 1 := by
        simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using htIoc
      have htcc : t ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioc_subset_Icc_self htIoc'
      have ht_abs : |t| ≤ 1 := by
        exact abs_le.mpr ⟨htcc.1, by norm_num at htcc ⊢; exact htcc.2⟩
      have hle : |t| + |s| * M ≤ 1 + |s| * M := by nlinarith [ht_abs]
      have hbound_t := ht htIoc
      calc
        ‖F s t‖ ≤ (|t| + |s| * M) * (2 * M) * (2 * M ^ 2) ^ (n - 1) := by
          simpa [F, U, W] using hbound_t
        _ ≤ (1 + |s| * M) * (2 * M) * (2 * M ^ 2) ^ (n - 1) := by
          nlinarith [hle, (by positivity : 0 ≤ (2 * M) * (2 * M ^ 2) ^ (n - 1))]
        _ = Bint := by dsimp [Bint]
    exact IntegrableOn.of_bound (by
        rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top) hmeas _ hbnd
  have hF'_meas : AEStronglyMeasurable (F' s) (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    have h_cond_meas : MeasurableSet {t : ℝ | -f t < s * t + h s ∧ s * t + h s < f t} := by
      apply MeasurableSet.inter
      · exact measurableSet_lt hf_meas.neg (by fun_prop)
      · exact measurableSet_lt (by fun_prop) hf_meas
    have h_then_meas : Measurable (fun t : ℝ =>
        (t + s * (s * t + h s)) * (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
          (t + deriv h s) -
        (f t ^ 2 - (s * t + h s) ^ 2) ^ n / (2 * (n : ℝ))) := by
      fun_prop
    exact (Measurable.ite h_cond_meas h_then_meas measurable_const).aestronglyMeasurable.restrict
  have h_bound' : ∀ᵐ t ∂volume, t ∈ Set.uIoc (-1 : ℝ) 1 → ∀ r ∈ S, ‖F' r t‖ ≤ B := by
    filter_upwards [] with t ht r hr
    have htIoc : t ∈ Set.Ioc (-1 : ℝ) 1 := by
      simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    have htcc : t ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioc_subset_Icc_self htIoc
    have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
    have hft_le : f t ≤ M := hf_le_M t htcc
    by_cases hcond : -f t < r * t + h r ∧ r * t + h r < f t
    · have hL_abs : |r * t + h r| ≤ R + H := hL_bound r hr t htcc
      have hq_abs : |f t ^ 2 - (r * t + h r) ^ 2| ≤ Bq := by
        have h1 : |f t ^ 2 - (r * t + h r) ^ 2| ≤ f t ^ 2 + (r * t + h r) ^ 2 := by
          rw [abs_le]
          constructor <;> nlinarith [sq_nonneg (f t), sq_nonneg (r * t + h r)]
        have hftsq : f t ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hft_nonneg hft_le 2
        have hLsq : (r * t + h r) ^ 2 ≤ (R + H) ^ 2 := by
          rw [sq_le_sq]
          simpa [abs_of_nonneg (by positivity : 0 ≤ R + H)] using hL_abs
        have hsum : f t ^ 2 + (r * t + h r) ^ 2 ≤ M ^ 2 + (R + H) ^ 2 := by nlinarith
        exact le_trans h1 hsum
      have hq_pow : |(f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1)| ≤ Bq ^ (n - 1) := by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) hq_abs (n - 1)
      have hq_pow_n : |(f t ^ 2 - (r * t + h r) ^ 2) ^ n| ≤ Bq ^ n := by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) hq_abs n
      have ht_abs : |t| ≤ 1 := by
        exact abs_le.mpr ⟨htcc.1, by norm_num at htcc ⊢; exact htcc.2⟩
      have hlin : |t + r * (r * t + h r)| ≤ Kline := by
        calc
          |t + r * (r * t + h r)| ≤ |t| + |r * (r * t + h r)| := abs_add_le _ _
          _ = |t| + |r| * |r * t + h r| := by rw [abs_mul]
          _ ≤ 1 + R * (R + H) := by
            exact add_le_add ht_abs (mul_le_mul (hR_mem r hr) hL_abs (abs_nonneg (r * t + h r)) hR_nonneg)
          _ = Kline := by dsimp [Kline]
      have hderiv_le : |t + deriv h r| ≤ 1 + C := by
        calc
          |t + deriv h r| ≤ |t| + |deriv h r| := abs_add_le _ _
          _ ≤ 1 + C := by exact add_le_add ht_abs (hderiv_bound r hr)
      have hfirst : |(t + r * (r * t + h r)) * (f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) *
          (t + deriv h r)| ≤ Kline * Bq ^ (n - 1) * (1 + C) := by
        have hprod1 : |(t + r * (r * t + h r)) * (f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1)| ≤
            Kline * Bq ^ (n - 1) := by
          simpa [abs_mul] using mul_le_mul hlin hq_pow (abs_nonneg _) hKline_nonneg
        have hprod2 : |(t + r * (r * t + h r)) * (f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) *
            (t + deriv h r)| ≤ (Kline * Bq ^ (n - 1)) * (1 + C) := by
          simpa [abs_mul] using mul_le_mul hprod1 hderiv_le (abs_nonneg _) (by positivity)
        simpa [mul_assoc] using hprod2
      have hsecond : |(f t ^ 2 - (r * t + h r) ^ 2) ^ n / (2 * (n : ℝ))| ≤ Bq ^ n / (2 * (n : ℝ)) := by
        have hden_nonneg : 0 ≤ 2 * (n : ℝ) := by positivity
        rw [abs_div, abs_of_nonneg hden_nonneg]
        exact div_le_div_of_nonneg_right hq_pow_n hden_nonneg
      have hsum_le : |(t + r * (r * t + h r)) * (f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) *
          (t + deriv h r) -
        (f t ^ 2 - (r * t + h r) ^ 2) ^ n / (2 * (n : ℝ))| ≤ B := by
        have htri := abs_sub_le ((t + r * (r * t + h r)) *
            (f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) * (t + deriv h r)) 0
            ((f t ^ 2 - (r * t + h r) ^ 2) ^ n / (2 * (n : ℝ)))
        have htri' : |(t + r * (r * t + h r)) * (f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) *
            (t + deriv h r) -
          (f t ^ 2 - (r * t + h r) ^ 2) ^ n / (2 * (n : ℝ))| ≤
            |(t + r * (r * t + h r)) * (f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) *
              (t + deriv h r)| +
            |(f t ^ 2 - (r * t + h r) ^ 2) ^ n / (2 * (n : ℝ))| := by
          simpa [sub_zero, zero_sub] using htri
        nlinarith [htri', hfirst, hsecond]
      dsimp [F']
      rw [if_pos hcond]
      exact hsum_le
    · dsimp [F']
      rw [if_neg hcond, abs_zero]
      exact hB_nonneg
  have h_bound_int : IntervalIntegrable (fun _ : ℝ => B) volume (-1 : ℝ) 1 := by
    exact intervalIntegrable_const
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (-1 : ℝ) 1 → ∀ r ∈ S,
      HasDerivAt (fun r => F r t) (F' r t) r := by
    filter_upwards [] with t ht r hr
    have htIoc : t ∈ Set.Ioc (-1 : ℝ) 1 := by
      simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    have htcc : t ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioc_subset_Icc_self htIoc
    have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
    have hh_deriv : HasDerivAt h (deriv h r) r := by
      have hd : DifferentiableAt ℝ h r := by
        exact (hh_cont.contDiffAt (by simp)).differentiableAt (by simp)
      exact hd.hasDerivAt
    have hslice := cap_centroid_slice_hasDerivAt (n := n) (F := f t) (s := r) (t := t)
      (dh := deriv h r) (h := h) hn hft_nonneg hh_deriv
    simpa [F, F', U, W] using hslice
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (F := F) (F' := F') (x₀ := s) (s := S) (μ := volume) (a := (-1 : ℝ)) (b := 1)
    hS_mem hF_meas hF_int hF'_meas h_bound' h_bound_int h_diff).2



lemma cap_centroid_moment_hasDerivAt_smooth {n : ℕ} {f h : ℝ → ℝ}
    (hn : 2 ≤ n)
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t)
    (hf_meas : Measurable f)
    (hf_bdd : Bornology.IsBounded (f '' Set.Icc (-1 : ℝ) 1))
    (hh_cont : ContDiffOn ℝ (WithTop.some (⊤ : ℕ∞)) h Set.univ)
    (s : ℝ) :
    HasDerivAt
      (fun r : ℝ =>
        ∫ t in (-1 : ℝ)..1,
          ∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
            (t + r * z) * (f t ^ 2 - z ^ 2) ^ (n - 1))
      (∫ t in (-1 : ℝ)..1,
        if -f t < s * t + h s ∧ s * t + h s < f t then
          (t + s * (s * t + h s)) * (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
            (t + deriv h s) -
          (f t ^ 2 - (s * t + h s) ^ 2) ^ n / (2 * (n : ℝ))
        else 0) s := by
  exact cap_centroid_moment_hasDerivAt_aux hn hf_nonneg hf_meas hf_bdd hh_cont s

end Commons.Geometry.Ulam