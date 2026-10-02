import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip
import Submission.Commons.NumberTheory.DirichletCharacter.rootNumber_norm_eq_one
import Submission.Commons.NumberTheory.DirichletCharacter.diskZeroCount_two_half
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_window_cover
import Submission.Commons.NumberTheory.Linnik.completedL_ballZeroCount
import Submission.Commons.NumberTheory.Linnik.completedL_local_zeroCount

open Complex DirichletCharacter Metric
open scoped Real Topology BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

namespace Work.LinnikAreas.A5

/-!
**Uniform-in-`N` zero count of `L(s,\chi)` in a disc** — a clash-free re-derivation of
`Commons.NumberTheory.DirichletCharacter.exists_LFunction_disc_zeroCount`.

This file avoids the import closure of the modules that both declare
`Commons.NumberTheory.DirichletCharacter.finite_zeroHeights_window`
(`.../DirichletCharacter/finite_zeroHeights_window.lean` and
`.../DirichletCharacter/logDeriv_rightHalf_avg.lean`), so that it can be imported together with
the §5 smoothing estimate `logDeriv_rightHalf_avg`.

The three ingredients are:
1. `Commons.NumberTheory.DirichletCharacter.diskZeroCount_two_half` — the uniform zero count of
   `Lambda` in the disk of radius `5/2` around `2 + i t` (its one-line wrapper
   `completedL_diskZeroCount_explicit` is what the original chain used, and is the only reason the
   original chain reached the clashing module);
2. the copies `local_zeroCount_uniformL_A5` / `ball_zeroCount_uniformL_A5` below (verbatim from
   `Submission/Commons/NumberTheory/BombieriVinogradov/siegel_walfisz_chi.lean`, lines 2050–2268,
   with `completedL_diskZeroCount_explicit` replaced by `diskZeroCount_two_half`), giving the
   uniform zero count of `Lambda` in an arbitrary disk;
3. the file `Submission/Commons/NumberTheory/DirichletCharacter/exists_LFunction_disc_zeroCount.lean`
   (its private helpers plus its main theorem, lines 17–454), copied below with the one call to
   `Commons.NumberTheory.BombieriVinogradov.ball_zeroCount_uniformL` replaced by
   `ball_zeroCount_uniformL_A5`.
-/

/-! ## Part 1: uniform zero counts for the completed L-function in a disk -/


/-- **Uniform local zero count** (disk centred on `Re = 2`). -/
theorem local_zeroCount_uniformL_A5 :
    ∃ c : ℝ, 0 < c ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hχprim : χ.IsPrimitive), ∀ R : ℝ, 2 ≤ R → ∀ t : ℝ,
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (completedLFunction χ)
          (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) R)) u : ℤ) : ℝ)) ≤
        c * R * (Real.log (2 + |t| + R) + Real.log (N : ℝ) + 2) := by
  classical
  refine ⟨4 * (9 / 2) * (1 + Real.log 3 / 2), by positivity, ?_⟩
  intro N _ χ hχ hχprim R hR t
  let n : ℕ := Nat.ceil (2 * R + 2)
  let J : Finset ℕ := Finset.range (n + 1)
  let m : ℕ → ℝ := fun j => t - (R + 1) + (j : ℝ)
  let X : ℝ := Real.log (2 + |t| + R) + Real.log (N : ℝ) + 2
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
  have hN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hX2 : 2 ≤ X := by
    dsimp [X]
    have h1 : 0 ≤ Real.log (2 + |t| + R) := Real.log_nonneg (by linarith only [abs_nonneg t, hR])
    linarith only [hN0, h1]
  have hn_le : (n : ℝ) ≤ 2 * R + 3 := by
    dsimp [n]
    have hc : (Nat.ceil (2 * R + 2) : ℝ) < 2 * R + 2 + 1 :=
      Nat.ceil_lt_add_one (a := 2 * R + 2) (by positivity : 0 ≤ 2 * R + 2)
    linarith only [hc]
  have hcard : ((n + 1 : ℕ) : ℝ) ≤ 4 * R := by
    dsimp [n]
    exact Commons.NumberTheory.Linnik.window_count_bound hR
  have h25 : (2.5 : ℝ) = (5:ℝ)/2 := by norm_num
  have hwin' : ∀ j : ℕ, j ≤ n →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (completedLFunction χ)
          (Metric.closedBall ((2 : ℂ) + Complex.I * ((m j) : ℂ)) ((5:ℝ)/2))) u : ℤ) : ℝ)) ≤
        (9 / 2) * (Real.log (2 + |m j|) + Real.log (N : ℝ) + 2) := by
    intro j hj
    have h0 := Commons.NumberTheory.DirichletCharacter.diskZeroCount_two_half
      χ hχ hχprim (m j)
    have hX2' : 2 ≤ Real.log (2 + |m j|) + Real.log (N : ℝ) + 2 := by
      have h1 : 0 ≤ Real.log (2 + |m j|) := Real.log_nonneg (by linarith only [abs_nonneg (m j)])
      linarith only [hN0, h1]
    have hlog4 : Real.log (2 + |m j| + 2) ≤ Real.log (2 + |m j|) + 2 := by
      have h1 : 2 + |m j| + 2 ≤ 4 * (2 + |m j|) := by linarith only [abs_nonneg (m j)]
      have h2 := Real.log_le_log (by positivity : (0:ℝ) < 2 + |m j| + 2) h1
      rw [Real.log_mul (by norm_num) (by positivity : (2 + |m j|) ≠ 0)] at h2
      have h3 : Real.log 4 ≤ 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
        have h4 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith only [this]
        push_cast; linarith only [h4]
      linarith only [h2, h3]
    have h5 : (3/2) * (Real.log (N : ℝ) + Real.log (2 + |m j| + 2)) + 6
        ≤ (3/2) * (Real.log (N : ℝ) + (Real.log (2 + |m j|) + 2)) + 6 := by linarith only [hlog4]
    have h6 : (3/2) * (Real.log (N : ℝ) + (Real.log (2 + |m j|) + 2)) + 6
        ≤ (9/2) * (Real.log (2 + |m j|) + Real.log (N : ℝ) + 2) := by linarith only [hX2']
    exact le_trans (le_trans h0 h5) h6
  have hlogm : ∀ j : ℕ, j ≤ n → Real.log (2 + |m j|) ≤ Real.log (2 + |t| + R) + Real.log 3 := by
    intro j hj
    have hpos1 : 0 < 2 + |m j| := by positivity
    have hle : 2 + |m j| ≤ 3 * (2 + |t| + R) := by
      have hb := Commons.NumberTheory.Linnik.window_center_le (R := R) (t := t) (j := j) (n := n) hR hj hn_le
      simpa [m] using hb
    have h := Real.log_le_log hpos1 hle
    rw [show 3 * (2 + |t| + R) = (2 + |t| + R) * 3 by ring] at h
    rw [Real.log_mul (ne_of_gt (by positivity : 0 < 2 + |t| + R))
        (ne_of_gt (by norm_num : 0 < (3 : ℝ)))] at h
    exact h
  have hEj : ∀ j : ℕ, j ≤ n →
      (Real.log (2 + |m j|) + Real.log (N : ℝ) + 2) ≤ X + Real.log 3 := by
    intro j hj
    have h0 := hlogm j hj
    dsimp [X]
    linarith only [h0]
  have hsum1 : (∑ j ∈ J, (9 / 2 : ℝ) * (Real.log (2 + |m j|) + Real.log (N : ℝ) + 2)) ≤
      ((n + 1 : ℕ) : ℝ) * ((9 / 2 : ℝ) * (X + Real.log 3)) := by
    have h1 : ∀ j ∈ J, (9 / 2 : ℝ) * (Real.log (2 + |m j|) + Real.log (N : ℝ) + 2) ≤
        (9 / 2 : ℝ) * (X + Real.log 3) := by
      intro j hj
      exact mul_le_mul_of_nonneg_left (hEj j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))) (by norm_num)
    have h2 : (∑ j ∈ J, (9 / 2 : ℝ) * (X + Real.log 3))
        = ((n + 1 : ℕ) : ℝ) * ((9 / 2 : ℝ) * (X + Real.log 3)) := by
      rw [Finset.sum_const]
      simp [J, nsmul_eq_mul]
    exact le_trans (Finset.sum_le_sum h1) (le_of_eq h2)
  have hsum2 : ((n + 1 : ℕ) : ℝ) * ((9 / 2 : ℝ) * (X + Real.log 3)) ≤
      (4 * (9 / 2) * (1 + Real.log 3 / 2)) * R * X := by
    have h2 : 0 ≤ (9 / 2 : ℝ) * (X + Real.log 3) := by positivity
    have h3 : (9 / 2 : ℝ) * (X + Real.log 3) ≤ ((9 / 2 : ℝ) * (1 + Real.log 3 / 2)) * X := by
      have hX : 0 ≤ X := by linarith only [hX2]
      have hx1 : X + Real.log 3 ≤ (1 + Real.log 3 / 2) * X := by
        have hposlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
        nlinarith only [hX2, hposlog]
      linarith only [hx1]
    calc ((n + 1 : ℕ) : ℝ) * ((9 / 2 : ℝ) * (X + Real.log 3))
        ≤ (4 * R) * ((9 / 2 : ℝ) * (X + Real.log 3)) :=
          mul_le_mul_of_nonneg_right hcard h2
      _ ≤ (4 * R) * (((9 / 2 : ℝ) * (1 + Real.log 3 / 2)) * X) :=
          mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ 4 * R)
      _ = (4 * (9 / 2) * (1 + Real.log 3 / 2)) * R * X := by ring
  have hcover := Commons.NumberTheory.DirichletCharacter.completedL_window_cover χ hχ hχprim
    (R := R) (t := t) hR
  have hgoal : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (completedLFunction χ)
      (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) R)) u : ℤ) : ℝ)) ≤
      (4 * (9 / 2) * (1 + Real.log 3 / 2)) * R * X := by
    have hcvr : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (completedLFunction χ)
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) R)) u : ℤ) : ℝ)) ≤
        ∑ j ∈ Finset.range (Nat.ceil (2 * R + 2) + 1), (∑ᶠ u : ℂ,
          (((MeromorphicOn.divisor (completedLFunction χ)
            (Metric.closedBall ((2 : ℂ) + Complex.I * ((m j : ℝ) : ℂ)) ((5:ℝ)/2))) u : ℤ) : ℝ)) := by
      have h := hcover
      rw [h25] at h
      refine le_trans h ?_
      apply Finset.sum_le_sum
      intro j hj
      exact le_of_eq (Commons.NumberTheory.Linnik.sum_divisor_center_eq (f := completedLFunction χ)
        (ρ := (5:ℝ)/2) (by
          rw [show m j = t - (R + 1) + (j : ℝ) from rfl]
          push_cast
          ring))
    calc (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (completedLFunction χ)
            (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) R)) u : ℤ) : ℝ))
        ≤ ∑ j ∈ Finset.range (Nat.ceil (2 * R + 2) + 1), (∑ᶠ u : ℂ,
            (((MeromorphicOn.divisor (completedLFunction χ)
              (Metric.closedBall ((2 : ℂ) + Complex.I * ((m j : ℝ) : ℂ)) ((5:ℝ)/2))) u : ℤ) : ℝ)) := hcvr
      _ ≤ ∑ j ∈ Finset.range (Nat.ceil (2 * R + 2) + 1),
            (9 / 2 : ℝ) * (Real.log (2 + |m j|) + Real.log (N : ℝ) + 2) := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          exact hwin' j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      _ = ∑ j ∈ J, (9 / 2 : ℝ) * (Real.log (2 + |m j|) + Real.log (N : ℝ) + 2) := by rfl
      _ ≤ ((n + 1 : ℕ) : ℝ) * ((9 / 2 : ℝ) * (X + Real.log 3)) := hsum1
      _ ≤ (4 * (9 / 2) * (1 + Real.log 3 / 2)) * R * X := hsum2
  simpa [X] using hgoal

/-- **Uniform zero count in an arbitrary disk.** -/
theorem ball_zeroCount_uniformL_A5 :
    ∃ c : ℝ, 0 < c ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hχprim : χ.IsPrimitive), ∀ a : ℂ, ∀ ρ : ℝ, 1 ≤ ρ →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ) : ℝ)) ≤
        c * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
  obtain ⟨c0, hc0, hlocal⟩ := local_zeroCount_uniformL_A5
  refine ⟨4 * max c0 0 + 4, by positivity, ?_⟩
  intro N _ χ hχ hχprim a ρ hρ
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
  have hN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hnorm : 0 ≤ ‖a‖ := norm_nonneg a
  have hρ0 : 0 ≤ ρ := by linarith only [hρ]
  have h2 := hlocal χ hχ hχprim (ρ + 2) (by linarith only [hρ] : 2 ≤ ρ + 2) a.im
  have h2' : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (completedLFunction χ)
        (Metric.closedBall ((2 : ℂ) + Complex.I * (a.im : ℂ)) (ρ + 2))) u : ℤ) : ℝ)) ≤
      c0 * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) := by
    have harg : (2 + |a.im| + (ρ + 2)) = (4 + |a.im| + ρ) := by ring
    simpa [harg] using h2
  have h12 : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (completedLFunction χ)
        (Metric.closedBall a ρ)) u : ℤ) : ℝ)) ≤
      c0 * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) :=
    le_trans (Commons.NumberTheory.Linnik.divisor_sum_le_divisor_sum_big χ hχ hχprim a ρ) h2'
  have hIm : |a.im| ≤ ‖a‖ := Complex.abs_im_le_norm a
  have hposLog : 0 < 4 + |a.im| + ρ := by linarith only [abs_nonneg a.im, hρ]
  have hleSq : 4 + ‖a‖ + ρ ≤ (‖a‖ + ρ + 2) ^ 2 := by linarith only [sq_nonneg (‖a‖ + ρ), hnorm, hρ]
  have hlog1 : Real.log (4 + |a.im| + ρ) ≤ 2 * Real.log (‖a‖ + ρ + 2) := by
    have hmono : Real.log (4 + |a.im| + ρ) ≤ Real.log (4 + ‖a‖ + ρ) :=
      Real.log_le_log hposLog (by linarith only [hIm])
    have hpos2 : 0 < 4 + ‖a‖ + ρ := by linarith only [hρ, hnorm]
    have hlog2 : Real.log (4 + ‖a‖ + ρ) ≤ Real.log ((‖a‖ + ρ + 2) ^ 2) :=
      Real.log_le_log hpos2 hleSq
    have hsq : Real.log ((‖a‖ + ρ + 2) ^ 2) = 2 * Real.log (‖a‖ + ρ + 2) := by
      rw [Real.log_pow]; ring
    linarith only [hmono, hlog2, hsq]
  have hXlog : 0 ≤ Real.log (‖a‖ + ρ + 2) := Real.log_nonneg (by linarith only [hρ, hnorm])
  have hsmall : 2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2 ≤
      2 * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by linarith only [hN0, hXlog]
  have hposT : 0 ≤ Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2 := by linarith only [hN0, hXlog]
  have hposC : 0 ≤ max c0 0 := le_max_right c0 0
  have hRhoFact : (ρ + 2) * (2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) ≤
      4 * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
    have hρ2 : ρ + 2 ≤ 2 * (ρ + 1) := by linarith only [hρ]
    have hleft : 0 ≤ 2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2 := by linarith only [hN0, hXlog]
    calc (ρ + 2) * (2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)
        ≤ (2 * (ρ + 1)) * (2 * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)) :=
          mul_le_mul hρ2 hsmall hleft (by linarith only [hρ])
      _ = 4 * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by ring
  have hposArg : 0 ≤ Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2 := by
    have h1pos : 0 ≤ Real.log (4 + |a.im| + ρ) := Real.log_nonneg (by linarith only [abs_nonneg a.im, hρ, hposLog])
    linarith only [hN0, h1pos]
  have hstepA : c0 * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) ≤
      (max c0 0) * (ρ + 2) * (2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
    have hle0 : c0 ≤ max c0 0 := le_max_left c0 0
    have hprod1 : c0 * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) ≤
        (max c0 0) * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) := by
      have hfact : 0 ≤ (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) := by positivity
      calc c0 * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2)
          = c0 * ((ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2)) := by ring
        _ ≤ (max c0 0) * ((ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_right hle0 hfact
        _ = (max c0 0) * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) := by ring
    have hArg : Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2 ≤
        2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2 := by linarith only [hlog1]
    have hpos2 : 0 ≤ (max c0 0) * (ρ + 2) := by positivity
    exact le_trans hprod1 (mul_le_mul_of_nonneg_left hArg hpos2)
  have hstepB : (max c0 0) * (ρ + 2) * (2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) ≤
      (max c0 0) * (4 * (ρ + 1)) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
    calc (max c0 0) * (ρ + 2) * (2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)
        = (max c0 0) * ((ρ + 2) * (2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)) := by ring
      _ ≤ (max c0 0) * (4 * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left hRhoFact hposC
      _ = (max c0 0) * (4 * (ρ + 1)) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by ring
  have hfinal : (max c0 0) * (4 * (ρ + 1)) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) ≤
      (4 * max c0 0 + 4) * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
    have hleC : 4 * max c0 0 ≤ 4 * max c0 0 + 4 := by linarith only []
    have hposR : 0 ≤ (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by positivity
    calc (max c0 0) * (4 * (ρ + 1)) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)
        = (4 * max c0 0) * ((ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)) := by ring
      _ ≤ (4 * max c0 0 + 4) * ((ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_right hleC hposR
      _ = (4 * max c0 0 + 4) * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by ring
  exact le_trans h12 (le_trans hstepA (le_trans hstepB hfinal))


/-! ## Part 2: comparing the divisors of `L` and of the completed L-function -/

/-!
# Uniform zero count of `L(·, χ)` in a small disk on `Re s ≥ 1`

This file proves the requested lemma `exists_LFunction_disc_zeroCount`: the
(multiplicity-weighted) divisor sum of a primitive non-trivial Dirichlet L-function over a closed
ball of radius `ρ ≤ 1` centred at a point `a` with `1 ≤ Re a` is at most
`c · (log (‖a‖ + 3) + log N + 2)` for an absolute constant `c`.

The plan is to compare with the *completed* L-function `Λ = L · γ`, whose uniform zero counts are
already available in the commons (`completedL_ballZeroCount_uniform`): the zeros of `L` in the
region `Re s ≥ 0` are the zeros of `Λ` in the critical strip, and the only point at which the two
divisors can disagree is `s = 0`, where `L` has a simple zero for even `χ` while `Λ` is non-zero.
The auxiliary facts needed for this comparison are collected first.
-/

/-! ### The divisor of an analytic function and its analytic order -/

/-- For an analytic function on a set, the integer divisor coefficient at a point of the set is the
analytic vanishing order there. -/
private lemma divisor_eq_analyticOrderNatAt {f : ℂ → ℂ} {U : Set ℂ} {u : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hu : u ∈ U) :
    MeromorphicOn.divisor f U u = (analyticOrderNatAt f u : ℤ) := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hu, (hf u hu).meromorphicOrderAt_eq]
  rcases eq_or_ne (analyticOrderAt f u) ⊤ with h | h
  · rw [h]; simp [analyticOrderNatAt, h]
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
    have h2 : analyticOrderNatAt f u = n := by
      rw [analyticOrderNatAt, ← hn]
      simp
    rw [h2, ← hn]
    simp

/-- Real-valued version of `divisor_eq_analyticOrderNatAt`. -/
private lemma divisor_cast_eq_analyticOrderNatAt {f : ℂ → ℂ} {U : Set ℂ} {u : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hu : u ∈ U) :
    ((MeromorphicOn.divisor f U u : ℤ) : ℝ) = (analyticOrderNatAt f u : ℝ) := by
  rw [divisor_eq_analyticOrderNatAt hf hu]
  simp

/-- Divisor coefficients of an analytic function are nonnegative. -/
private lemma divisor_nonneg_of_analyticOnNhd {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f U) :
    (0 : ℤ) ≤ MeromorphicOn.divisor f U z := by
  by_cases hz : z ∈ U
  · rw [MeromorphicOn.divisor_apply hf.meromorphicOn hz]
    have hAn : AnalyticAt ℂ f z := hf z hz
    have hNF := hAn.meromorphicNFAt
    have hord : (0 : WithTop ℤ) ≤ meromorphicOrderAt f z :=
      (MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt hNF).2 hAn
    exact (WithTop.untop₀_nonneg (α := ℤ) (a := meromorphicOrderAt f z)).mpr hord
  · rw [MeromorphicOn.divisor_def]
    rw [if_neg]
    intro h
    exact hz h.2

/-! ### Non-vanishing of the archimedean factor and of `L` on the imaginary axis -/

/-- The archimedean Gamma factor of a Dirichlet character does not vanish at a point of the
imaginary axis other than the origin. -/
private lemma gammaFactor_ne_zero_of_re_eq_zero {N : ℕ} (χ : DirichletCharacter ℂ N) {u : ℂ}
    (hre : u.re = 0) (hu0 : u ≠ 0) : χ.gammaFactor u ≠ 0 := by
  rcases χ.even_or_odd with hE | hO
  · rw [Even.gammaFactor_def hE]
    intro h
    rw [Complex.Gammaℝ_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    apply hu0
    have h2 : u.re = -((2 * n : ℕ) : ℝ) := by
      conv_lhs => rw [hn]
      simp
    rw [hre] at h2
    have hn0 : n = 0 := by
      have h3 : ((2 * n : ℕ) : ℝ) = 0 := by linarith only [h2]
      have h4 : (2 * n : ℕ) = 0 := by exact_mod_cast h3
      omega
    rw [hn0] at hn
    simpa using hn
  · rw [Odd.gammaFactor_def hO]
    intro h
    rw [Complex.Gammaℝ_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    have h2 : (u + 1).re = 1 := by simp [Complex.add_re, hre]
    have h3 : (-((2 : ℂ) * (n : ℂ))).re = -(2 * (n : ℝ)) := by simp
    have h4 := congrArg Complex.re hn
    rw [h2, h3] at h4
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith only [h4]

/-- A primitive non-trivial Dirichlet L-function does not vanish on the imaginary axis away from
the origin (its zeros in the half-plane `Re s ≥ 0` are the non-trivial zeros, which lie in the open
critical strip). -/
private lemma LFunction_ne_zero_of_re_eq_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {u : ℂ} (hre : u.re = 0) (hu0 : u ≠ 0) :
    DirichletCharacter.LFunction χ u ≠ 0 := by
  intro hz
  have hγ : χ.gammaFactor u ≠ 0 := gammaFactor_ne_zero_of_re_eq_zero χ hre hu0
  have hid := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ u (Or.inl hu0)
  have hΛ : DirichletCharacter.completedLFunction χ u = 0 := by
    rw [hid] at hz
    rcases (div_eq_zero_iff.mp hz) with h | h
    · exact h
    · exact absurd h hγ
  have hstrip := Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim u hΛ
  rw [hre] at hstrip
  exact lt_irrefl 0 hstrip.1

/-! ### The vanishing order of `Γ_ℝ^{-1}` at the origin -/

/-- `Γ_ℝ^{-1}` has a simple zero at the origin. -/
private lemma analyticOrderAt_Gammaℝ_inv_zero :
    analyticOrderAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) 0 = (1 : ℕ∞) := by
  have hdiff : AnalyticAt ℂ (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) 0 :=
    Complex.differentiable_Gammaℝ_inv.analyticAt 0
  have hcomp : AnalyticAt ℂ (fun s : ℂ => (Complex.Gammaℝ (s + 2))⁻¹) 0 :=
    (Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 2)).analyticAt 0
  have hF : AnalyticAt ℂ (fun s : ℂ => ((2 : ℂ) * ↑Real.pi)⁻¹ * (Complex.Gammaℝ (s + 2))⁻¹) 0 :=
    analyticAt_const.mul hcomp
  have hGamma2 : Complex.Gammaℝ 2 = (↑Real.pi)⁻¹ := by
    rw [Complex.Gammaℝ_def,
      show (-(2 : ℂ) / 2) = -1 by norm_num, show ((2 : ℂ) / 2) = 1 by norm_num,
      cpow_neg_one, Complex.Gamma_one, mul_one]
  have hF0 : ((2 : ℂ) * ↑Real.pi)⁻¹ * (Complex.Gammaℝ (0 + 2))⁻¹ ≠ 0 := by
    have hpi : (↑Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have h2pi : ((2 : ℂ) * ↑Real.pi) ≠ 0 := mul_ne_zero (by norm_num) hpi
    rw [zero_add, hGamma2, inv_inv]
    exact mul_ne_zero (inv_ne_zero h2pi) hpi
  have hglob : (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) =
      fun s : ℂ => (s - 0) ^ 1 • (((2 : ℂ) * ↑Real.pi)⁻¹ * (Complex.Gammaℝ (s + 2))⁻¹) := by
    funext s
    by_cases hs : s = 0
    · subst hs
      have h0 : Complex.Gammaℝ 0 = 0 := Complex.Gammaℝ_eq_zero_iff.mpr ⟨0, by norm_num⟩
      rw [h0]; simp
    · rw [sub_zero, pow_one, smul_eq_mul, Complex.Gammaℝ_add_two hs]
      field_simp
  have heq : (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) =ᶠ[𝓝 0]
      fun s : ℂ => (s - 0) ^ 1 • (((2 : ℂ) * ↑Real.pi)⁻¹ * (Complex.Gammaℝ (s + 2))⁻¹) :=
    Filter.EventuallyEq.of_eq hglob
  exact (hdiff.analyticOrderAt_eq_natCast (n := 1)).mpr ⟨_, hF, hF0, heq⟩

/-- The vanishing order of `Γ_ℝ^{-1}` at the origin, as a natural number. -/
private lemma analyticOrderNatAt_Gammaℝ_inv_zero :
    analyticOrderNatAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) 0 = 1 := by
  rw [analyticOrderNatAt, analyticOrderAt_Gammaℝ_inv_zero]
  simp

/-- The vanishing order of the inverse archimedean factor `γ^{-1}` at the origin is `1` for even
characters and `0` for odd characters. -/
private lemma analyticOrderAt_gammaFactor_inv_zero {N : ℕ} (χ : DirichletCharacter ℂ N) :
    analyticOrderAt (fun s : ℂ => (χ.gammaFactor s)⁻¹) 0 = 1 ∨
      analyticOrderAt (fun s : ℂ => (χ.gammaFactor s)⁻¹) 0 = 0 := by
  rcases χ.even_or_odd with hE | hO
  · left
    have hfun : (fun s : ℂ => (χ.gammaFactor s)⁻¹) = fun s : ℂ => (Complex.Gammaℝ s)⁻¹ := by
      funext s
      rw [Even.gammaFactor_def hE]
    rw [hfun]
    exact analyticOrderAt_Gammaℝ_inv_zero
  · right
    have hfun : (fun s : ℂ => (χ.gammaFactor s)⁻¹) =
        fun s : ℂ => (Complex.Gammaℝ (s + 1))⁻¹ := by
      funext s
      rw [Odd.gammaFactor_def hO]
    rw [hfun]
    refine analyticOrderAt_eq_zero.mpr (Or.inr ?_)
    simp [Complex.Gammaℝ_one]

/-- `γ^{-1}` has vanishing order at most one at the origin. -/
private lemma analyticOrderNatAt_gammaFactor_inv_zero_le_one {N : ℕ} (χ : DirichletCharacter ℂ N) :
    analyticOrderNatAt (fun s : ℂ => (χ.gammaFactor s)⁻¹) 0 ≤ 1 := by
  rcases analyticOrderAt_gammaFactor_inv_zero χ with h | h
  · rw [analyticOrderNatAt, h]
    simp
  · rw [analyticOrderNatAt, h]
    simp

/-! ### Non-vanishing of `Λ` and the vanishing order of `L` at the origin -/

/-- The completed L-function of a primitive non-trivial character does not vanish at `s = 0`. -/
private lemma completedLFunction_zero_ne_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    DirichletCharacter.completedLFunction χ 0 ≠ 0 := by
  have hNne : N ≠ 1 := by
    intro h
    subst h
    exact hχ (Subsingleton.elim χ 1)
  have hχine : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    calc χ = (χ⁻¹)⁻¹ := by rw [inv_inv]
      _ = 1⁻¹ := by rw [h]
      _ = 1 := by simp
  -- `Λ(1, χ⁻¹) ≠ 0`
  have hΛ1 : DirichletCharacter.completedLFunction (χ⁻¹) 1 ≠ 0 := by
    have hL1 : DirichletCharacter.LFunction (χ⁻¹) 1 ≠ 0 :=
      DirichletCharacter.LFunction_apply_one_ne_zero hχine
    have hγ1 : (χ⁻¹).gammaFactor 1 ≠ 0 := by
      rcases (χ⁻¹).even_or_odd with hE | hO
      · rw [Even.gammaFactor_def hE, Complex.Gammaℝ_one]; norm_num
      · intro h
        rw [Odd.gammaFactor_def hO, show ((1 : ℂ) + 1) = 2 by norm_num,
          Complex.Gammaℝ_eq_zero_iff] at h
        obtain ⟨n, hn⟩ := h
        have h2 : (-((2 : ℂ) * (n : ℂ))).re = -(2 * (n : ℝ)) := by simp
        have h4 := congrArg Complex.re hn
        rw [h2] at h4
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        norm_num at h4
        linarith only [h4]
    have hid := DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ⁻¹) 1 (Or.inr hNne)
    intro h
    rw [hid, h] at hL1
    simp at hL1
  have hroot : χ.rootNumber ≠ 0 := by
    intro h
    have h1 := Commons.NumberTheory.DirichletCharacter.rootNumber_norm_eq_one χ hχprim
    rw [h] at h1
    norm_num at h1
  have hpow : (N : ℂ) ^ ((1 : ℂ) - 1 / 2) ≠ 0 := by
    rw [cpow_ne_zero_iff]
    exact Or.inl (by exact_mod_cast (NeZero.ne N))
  have hFE := DirichletCharacter.IsPrimitive.completedLFunction_one_sub hχprim 1
  rw [show (1 : ℂ) - 1 = 0 by ring] at hFE
  intro hz
  refine (mul_ne_zero (mul_ne_zero hpow hroot) hΛ1) ?_
  rw [← hFE, hz]

/-- The L-function of a primitive non-trivial character has vanishing order at most one at the
origin. -/
private lemma analyticOrderNatAt_LFunction_zero_le_one {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    analyticOrderNatAt (DirichletCharacter.LFunction χ) 0 ≤ 1 := by
  have hNne : N ≠ 1 := by
    intro h
    subst h
    exact hχ (Subsingleton.elim χ 1)
  have hfun : DirichletCharacter.LFunction χ =
      DirichletCharacter.completedLFunction χ * (fun s : ℂ => (χ.gammaFactor s)⁻¹) := by
    funext s
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hNne),
      div_eq_mul_inv]
    rfl
  rw [hfun]
  have hΛan : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) 0 :=
    (differentiable_completedLFunction hχ).analyticAt 0
  have hγan : AnalyticAt ℂ (fun s : ℂ => (χ.gammaFactor s)⁻¹) 0 := by
    rcases χ.even_or_odd with hE | hO
    · have hfun2 : (fun s : ℂ => (χ.gammaFactor s)⁻¹) = fun s : ℂ => (Complex.Gammaℝ s)⁻¹ := by
        funext s
        rw [Even.gammaFactor_def hE]
      rw [hfun2]
      exact Complex.differentiable_Gammaℝ_inv.analyticAt 0
    · have hfun2 : (fun s : ℂ => (χ.gammaFactor s)⁻¹) =
          fun s : ℂ => (Complex.Gammaℝ (s + 1))⁻¹ := by
        funext s
        rw [Odd.gammaFactor_def hO]
      rw [hfun2]
      exact (Complex.differentiable_Gammaℝ_inv.comp (by fun_prop)).analyticAt 0
  have hΛord : analyticOrderAt (DirichletCharacter.completedLFunction χ) 0 = 0 :=
    (hΛan.analyticOrderAt_eq_zero).mpr (completedLFunction_zero_ne_zero χ hχ hχprim)
  have hγord_ne : analyticOrderAt (fun s : ℂ => (χ.gammaFactor s)⁻¹) 0 ≠ ⊤ := by
    rcases analyticOrderAt_gammaFactor_inv_zero χ with h | h
    · rw [h]; exact ENat.natCast_ne_top 1
    · rw [h]; exact ENat.natCast_ne_top 0
  have hmul := analyticOrderNatAt_mul hΛan hγan (by rw [hΛord]; exact ENat.natCast_ne_top 0) hγord_ne
  have hΛnat : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) 0 = 0 := by
    rw [analyticOrderNatAt, hΛord]
    simp
  rw [hmul, hΛnat, zero_add]
  exact analyticOrderNatAt_gammaFactor_inv_zero_le_one χ


/-! ### The divisor sum of `L` over a small ball -/

/-- Comparing the divisor sum of `L(·, χ)` over `closedBall a ρ` (`0 < ρ ≤ 1`, `1 ≤ Re a`) with
that of the completed L-function over `closedBall a 1`: every zero of `L` in the small ball other
than the origin is a non-trivial zero, hence a zero of `Λ` of the same multiplicity, while at the
origin `L` has vanishing order at most `1` and `Λ` does not vanish. -/
private lemma L_divisor_sum_le_completedL_divisor_sum_add {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    (a : ℂ) (ρ : ℝ) (_hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (ha : 1 ≤ a.re) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
        (Metric.closedBall a ρ)) u : ℤ) : ℝ)) ≤
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall a 1)) u : ℤ) : ℝ)) + 1 := by
  classical
  have hLdiff : Differentiable ℂ (DirichletCharacter.LFunction χ) := differentiable_LFunction hχ
  have hΛdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    differentiable_completedLFunction hχ
  have hLanBρ : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall a ρ) :=
    fun z _ => hLdiff.analyticAt z
  have hΛanB : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall a 1) :=
    fun z _ => hΛdiff.analyticAt z
  have hsub : Metric.closedBall a ρ ⊆ Metric.closedBall a 1 :=
    Metric.closedBall_subset_closedBall hρ1
  have hfinL : Function.HasFiniteSupport
      (fun u : ℂ => (((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
        (Metric.closedBall a ρ)) u : ℤ) : ℝ)) := by
    have h1 : (Function.support (fun u : ℂ => ((MeromorphicOn.divisor
        (DirichletCharacter.LFunction χ) (Metric.closedBall a ρ)) u : ℤ))).Finite := by
      simpa [Function.HasFiniteSupport] using
        ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
          (Metric.closedBall a ρ)).finiteSupport (isCompact_closedBall a ρ))
    exact h1.subset (fun u hu => by
      simp only [Function.mem_support] at hu ⊢
      exact fun hz => hu (by exact_mod_cast hz))
  have hfinΛ : Function.HasFiniteSupport
      (fun u : ℂ => (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall a 1)) u : ℤ) : ℝ)) := by
    have h1 : (Function.support (fun u : ℂ => ((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ) (Metric.closedBall a 1)) u : ℤ))).Finite := by
      simpa [Function.HasFiniteSupport] using
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a 1)).finiteSupport (isCompact_closedBall a 1))
    exact h1.subset (fun u hu => by
      simp only [Function.mem_support] at hu ⊢
      exact fun hz => hu (by exact_mod_cast hz))
  have hfinC : Function.HasFiniteSupport (fun u : ℂ => if u = 0 then (1 : ℝ) else 0) := by
    refine (Set.finite_singleton (0 : ℂ)).subset ?_
    intro u hu
    simp only [Function.mem_support] at hu
    simp only [Set.mem_singleton_iff]
    by_contra h
    exact hu (by simp [h])
  have hpt : ∀ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
        (Metric.closedBall a ρ)) u : ℤ) : ℝ) ≤
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall a 1)) u : ℤ) : ℝ) + (if u = 0 then (1 : ℝ) else 0) := by
    intro u
    by_cases huBρ : u ∈ Metric.closedBall a ρ
    · have huB : u ∈ Metric.closedBall a 1 := hsub huBρ
      rw [divisor_cast_eq_analyticOrderNatAt hLanBρ huBρ,
        divisor_cast_eq_analyticOrderNatAt hΛanB huB]
      by_cases hu0 : u = 0
      · subst hu0
        rw [if_pos rfl]
        have hL0 : analyticOrderNatAt (DirichletCharacter.LFunction χ) 0 ≤ 1 :=
          analyticOrderNatAt_LFunction_zero_le_one χ hχ hχprim
        have hΛ0 : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) 0 = 0 := by
          rw [analyticOrderNatAt,
            (hΛanB 0 huB).analyticOrderAt_eq_zero.mpr
              (completedLFunction_zero_ne_zero χ hχ hχprim)]
          simp
        rw [hΛ0, Nat.cast_zero, zero_add]
        exact_mod_cast hL0
      · rw [if_neg hu0, add_zero]
        by_cases hz : analyticOrderNatAt (DirichletCharacter.LFunction χ) u = 0
        · rw [hz, Nat.cast_zero]
          exact Nat.cast_nonneg _
        · have hLzero : DirichletCharacter.LFunction χ u = 0 :=
            apply_eq_zero_of_analyticOrderNatAt_ne_zero hz
          have hdist : ‖u - a‖ ≤ ρ := by
            have h := huBρ
            rwa [Metric.mem_closedBall, dist_eq_norm] at h
          have hre_ge : 0 ≤ u.re := by
            have h1 : |u.re - a.re| ≤ ‖u - a‖ := by
              have h := Complex.abs_re_le_norm (u - a)
              rwa [Complex.sub_re] at h
            have h2 : |u.re - a.re| ≤ ρ := le_trans h1 hdist
            have h3 := abs_le.mp h2
            linarith only [h3.1, ha, hρ1, h3]
          have hre0 : 0 < u.re := by
            rcases lt_or_eq_of_le hre_ge with h | h
            · exact h
            · exact absurd hLzero (LFunction_ne_zero_of_re_eq_zero χ hχ hχprim h.symm hu0)
          have hre1 : u.re < 1 := by
            by_contra hcon
            exact absurd hLzero (LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (le_of_not_gt hcon))
          rw [Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip
            χ hχ hre0 hre1]
    · have hzero : MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
          (Metric.closedBall a ρ) u = 0 :=
        (MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
          (Metric.closedBall a ρ)).apply_eq_zero_of_notMem huBρ
      rw [hzero, Int.cast_zero]
      by_cases hu0 : u = 0
      · subst hu0
        rw [if_pos rfl]
        by_cases h0B : (0 : ℂ) ∈ Metric.closedBall a 1
        · rw [divisor_cast_eq_analyticOrderNatAt hΛanB h0B]
          have : (0 : ℝ) ≤
            (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) 0 : ℝ) := Nat.cast_nonneg _
          linarith
        · rw [(MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall a 1)).apply_eq_zero_of_notMem h0B, Int.cast_zero]
          norm_num
      · rw [if_neg hu0, add_zero]
        by_cases huB : u ∈ Metric.closedBall a 1
        · rw [divisor_cast_eq_analyticOrderNatAt hΛanB huB]
          exact Nat.cast_nonneg _
        · rw [(MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall a 1)).apply_eq_zero_of_notMem huB, Int.cast_zero]
  calc
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
        (Metric.closedBall a ρ)) u : ℤ) : ℝ))
        ≤ ∑ᶠ u : ℂ, ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall a 1)) u : ℤ) : ℝ) + (if u = 0 then (1 : ℝ) else 0)) :=
          finsum_le_finsum' hfinL (hfinΛ.add hfinC) hpt
    _ = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall a 1)) u : ℤ) : ℝ))
          + (∑ᶠ u : ℂ, (if u = 0 then (1 : ℝ) else 0)) :=
          finsum_add_distrib hfinΛ hfinC
    _ = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall a 1)) u : ℤ) : ℝ)) + 1 := by
          rw [finsum_eq_single (fun u : ℂ => if u = 0 then (1 : ℝ) else 0) 0
            (fun x hx => by simp [hx])]
          norm_num

/-! ### The main theorem -/

/-! ## Part 3: the main theorem -/

/-
The requested lemma: the multiplicity-weighted divisor sum of a primitive non-trivial Dirichlet
L-function over a closed ball of radius `rho <= 1` centred at a point `a` with `1 <= Re a` is at
most `c * (log (||a|| + 3) + log N + 2)` for an absolute constant `c`.
-/
theorem LFunction_disc_zeroCount :
    ∃ c : ℝ, 0 < c ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ.IsPrimitive →
      ∀ (a : ℂ) (ρ : ℝ), 0 < ρ → ρ ≤ 1 → 1 ≤ a.re →
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
            (Metric.closedBall a ρ)) u : ℤ) : ℝ))
          ≤ c * (Real.log (‖a‖ + 3) + Real.log (N : ℝ) + 2) := by
  obtain ⟨c₀, hc₀, hball⟩ := ball_zeroCount_uniformL_A5
  refine ⟨max (2 * c₀ + 1) 1, lt_max_of_lt_left (by linarith only [hc₀]), ?_⟩
  intro N _ χ hχ hχprim a ρ hρ0 hρ1 ha
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hlogA : 0 ≤ Real.log (‖a‖ + 3) := Real.log_nonneg (by have := norm_nonneg a; linarith only [this])
  set X : ℝ := Real.log (‖a‖ + 3) + Real.log (N : ℝ) + 2 with hX
  have hX1 : 1 ≤ X := by simp only [hX]; linarith only [hlogN, hlogA]
  have hXpos : 0 ≤ X := le_trans zero_le_one hX1
  have hcomp := L_divisor_sum_le_completedL_divisor_sum_add χ hχ hχprim a ρ hρ0 hρ1 ha
  have hb := hball χ hχ hχprim a 1 le_rfl
  have hb' : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall a 1)) u : ℤ) : ℝ)) ≤ c₀ * 2 * X := by
    have h := hb
    rw [show (1 : ℝ) + 1 = 2 by norm_num,
      show ‖a‖ + 1 + 2 = ‖a‖ + 3 by ring] at h
    rw [hX]
    exact h
  calc
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
        (Metric.closedBall a ρ)) u : ℤ) : ℝ))
        ≤ (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall a 1)) u : ℤ) : ℝ)) + 1 := hcomp
    _ ≤ c₀ * 2 * X + 1 := by linarith [hb']
    _ ≤ (2 * c₀ + 1) * X := by linarith only [hX1, hc₀, hlogN, hlogA]
    _ ≤ max (2 * c₀ + 1) 1 * X := mul_le_mul_of_nonneg_right (le_max_left _ _) hXpos

end Work.LinnikAreas.A5
