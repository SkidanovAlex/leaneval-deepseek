import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Core.pd_window_helpers
import Submission.Work.TMC16Core.Main.theta_refold
import Submission.Work.TMC16Core.Main.theta_residue_bound
import Submission.Work.TMC16Core.Main.theta_shift_bound

/-!
# The theta-charge lemma for the C16 uniformity estimate

`Main.theta_charge_nr`: for a phase `θ` whose `fracDist (2θ + kα)` is bounded below by `csm`
for `|k| < K₀` and by `1/k²` for `K₀ ≤ |k|` (the two conclusions of `θ ∉ Theta α`), and whose
range bound `Bz` is controlled by `B0` as in the C16 hypotheses, there is a charge `c > 0`
with `c ≤ 1/2`, `c ≤ fracDist (2θ + jα)` for all `|j| ≤ Bz`, and `log (1/c) = O(log (q n))`.

Two regimes: under `(4 q_n)^9 ≤ q_{n+1}` the phase index is refolded mod `q_n`
(`Main.theta_refold`), which lets the large range `|j| ≤ B0 + 8 q_n + 4` be reached from the
short-range bound `4/q_n²` (`Main.theta_residue_bound`), the shift cost being controlled by
`Main.theta_shift_bound`; otherwise `B0` itself is already `O(q_n^{10})` and the crude bound
`1/j²` gives `log (1/c) = O(log q_n)` through `Core.theta_bound_of_setup`.

`log_case2` is the elementary numeric comparison used in the second regime.
-/

namespace Work.TMC16Core.Main

open Work.TMC16Core

theorem log_case2 {x M : ℝ} (hx : 0 ≤ x) (hM1 : 1 ≤ M)
    (hM : M ≤ 3 * 10 ^ 6 * (x + 1) ^ 10) :
    Real.log 2 + 2 * Real.log M ≤ 100 + 20 * Real.log (x + 2) := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hx1pos : 0 < x + 1 := by linarith
  have hx2pos : 0 < x + 2 := by linarith
  have hKpos : (0 : ℝ) < 3 * 10 ^ 6 := by norm_num
  have hlogM : Real.log M ≤ Real.log (3 * 10 ^ 6 * (x + 1) ^ 10) :=
    Real.log_le_log hMpos hM
  have hsplit : Real.log (3 * 10 ^ 6 * (x + 1) ^ 10)
      = Real.log (3 * 10 ^ 6) + 10 * Real.log (x + 1) := by
    rw [Real.log_mul (ne_of_gt hKpos) (pow_ne_zero 10 (ne_of_gt hx1pos)), Real.log_pow]
    push_cast
    ring
  have hlog3e6 : Real.log (3 * 10 ^ 6) ≤ 28 := by
    have hle : (3 * 10 ^ 6 : ℝ) ≤ 3 ^ 14 := by norm_num
    have h1 : Real.log (3 * 10 ^ 6) ≤ Real.log ((3 : ℝ) ^ 14) :=
      Real.log_le_log (by norm_num) hle
    rw [Real.log_pow] at h1
    have h3 : Real.log (3 : ℝ) ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
    push_cast at h1
    linarith
  have hlogm : Real.log M ≤ 28 + 10 * Real.log (x + 1) := by linarith [hlogM, hsplit, hlog3e6]
  have hxle : Real.log (x + 1) ≤ Real.log (x + 2) := Real.log_le_log hx1pos (by linarith)
  have h2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hlog2nn : 0 ≤ Real.log (x + 2) := Real.log_nonneg (by linarith)
  linarith [hlogm, hxle, h2le, hlog2nn]

theorem theta_charge_nr {α θ : ℝ} {K₀ : ℤ} {csm : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    {n : ℕ} {Bz : ℤ} {B0 : ℝ}
    (hK₀1 : 1 ≤ K₀) (hcsm : 0 < csm) (hcsm1 : csm ≤ 1 / 2)
    (h1 : ∀ k : ℤ, |k| < K₀ → csm ≤ Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α))
    (h2 : ∀ k : ℤ, K₀ ≤ |k| → ((((k.natAbs : ℕ) : ℝ))⁻¹)^2 ≤
      Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α))
    (hqpos : ∀ i, 0 < q i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hn : 1 ≤ n)
    (hbig : 10 ^ 6 ≤ csm * (q n : ℝ) ^ 2)
    (hB0nn : 0 ≤ B0)
    (hBz : (Bz : ℝ) ≤ B0 + 8 * (q n : ℝ) + 4)
    (hcase : ((4 * (q n : ℝ)) ^ 9 ≤ (q (n + 1) : ℝ) ∧
        B0 ≤ (q (n + 1) : ℝ) / (q n : ℝ)) ∨
      (B0 ≤ 10 ^ 6 * ((q n : ℝ) + 1) ^ 10)) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
      (∀ j : ℤ, |j| ≤ Bz → c ≤ Work.TMC16Core.fracDist (2 * θ + (j : ℝ) * α)) ∧
      Real.log (1 / c) ≤ Real.log (1 / csm) + 100 + 20 * Real.log ((q n : ℝ) + 2) := by
  have hqnR : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hqpos n
  have hqnsq : 2 * 10 ^ 6 ≤ (q n : ℝ) ^ 2 := by
    nlinarith [hbig, hcsm1, hqnR, sq_nonneg (q n : ℝ)]
  have hA2 : (2 : ℝ) ≤ (q n : ℝ) := by nlinarith [hqnsq]
  have hcsm_le : 0 ≤ Real.log (1 / csm) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hcsm, one_mul]
    linarith [hcsm1]
  rcases hcase with ⟨h4q, hB0le⟩ | hB0le
  · -- ============ CASE 1 ============
    have hAshift := theta_shift_bound (α := α) (q := q) (Δ := Δ) (n := n) (B0 := B0)
      hqpos hΔeq hΔup ⟨h4q, hB0le⟩
    have hres : ∀ r : ℤ, |r| ≤ (q n : ℝ) / 2 →
        4 / (q n : ℝ) ^ 2 ≤ Work.TMC16Core.fracDist (2 * θ + (r : ℝ) * α) :=
      theta_residue_bound (α := α) (θ := θ) (K₀ := K₀) (csm := csm) (q := q) (n := n)
        hK₀1 hcsm h1 h2 (hqpos n) hbig
    have hshift2 : ((B0 + 8 * (q n : ℝ) + 4) / (q n : ℝ) + 1 / 2) * Δ n
        ≤ (4 / (q n : ℝ) ^ 2) / 2 := by
      rw [show (4 / (q n : ℝ) ^ 2) / 2 = 2 / (q n : ℝ) ^ 2 by ring]
      exact hAshift
    have hrefold := theta_refold (α := α) (θ := θ) (Q := q n) (Δ := Δ n)
      (c := 4 / (q n : ℝ) ^ 2) (Y := B0 + 8 * (q n : ℝ) + 4)
      (hqpos n) (by positivity) (hΔeq n) hres hshift2
    refine ⟨2 / (q n : ℝ) ^ 2, by positivity, ?_, ?_, ?_⟩
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [hqnsq]
    · intro j hj
      have hjR : |((j : ℝ))| ≤ B0 + 8 * (q n : ℝ) + 4 := by
        have hcast : ((|j| : ℤ) : ℝ) ≤ (Bz : ℝ) := by exact_mod_cast hj
        rw [← Int.cast_abs]
        linarith [hBz]
      have hthis := hrefold j hjR
      rwa [show (4 / (q n : ℝ) ^ 2) / 2 = 2 / (q n : ℝ) ^ 2 by ring] at hthis
    · have hstep1 : Real.log ((q n : ℝ) ^ 2 / 2) ≤ 2 * Real.log (q n : ℝ) := by
        rw [Real.log_div (pow_ne_zero 2 (ne_of_gt hqnR)) (by norm_num), Real.log_pow]
        push_cast
        have h2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        linarith
      have hstep2 : 2 * Real.log ((q n : ℝ)) ≤ 2 * Real.log ((q n : ℝ) + 2) := by
        have h : Real.log (q n : ℝ) ≤ Real.log ((q n : ℝ) + 2) :=
          Real.log_le_log hqnR (le_add_of_nonneg_right (by norm_num))
        linarith
      have hstep3 : 2 * Real.log ((q n : ℝ) + 2) ≤ 20 * Real.log ((q n : ℝ) + 2) := by
        have hnn : 0 ≤ Real.log ((q n : ℝ) + 2) := Real.log_nonneg (by linarith)
        linarith
      have hgoal1 : 1 / (2 / (q n : ℝ) ^ 2) = (q n : ℝ) ^ 2 / 2 := by
        field_simp
      rw [hgoal1]
      linarith [hstep1, hstep2, hstep3, hcsm_le]
  · -- ============ CASE 2 ============
    have hBzbound : (Bz : ℝ) ≤ 2 * 10 ^ 6 * ((q n : ℝ) + 1) ^ 10 := by
      have hp : (q n : ℝ) + 1 ≤ ((q n : ℝ) + 1) ^ 10 := by
        have := pow_le_pow_right₀ (by linarith [hqnR] : (1 : ℝ) ≤ (q n : ℝ) + 1)
          (by norm_num : 1 ≤ 10)
        simpa using this
      have h8 : 8 * (q n : ℝ) + 4 ≤ 10 ^ 6 * ((q n : ℝ) + 1) ^ 10 := by linarith [hp, hqnR]
      linarith [hBz, hB0le, h8]
    set Bz' : ℤ := max Bz 1 with hBz'def
    have hBz'ge : Bz ≤ Bz' := by rw [hBz'def]; exact le_max_left _ _
    have hBz'1 : 1 ≤ Bz' := by rw [hBz'def]; exact le_max_right _ _
    have hBz'bound : (Bz' : ℝ) ≤ 2 * 10 ^ 6 * ((q n : ℝ) + 1) ^ 10 := by
      rw [hBz'def, Int.cast_max]
      refine max_le hBzbound ?_
      have hpow : ((1 : ℤ) : ℝ) ≤ ((q n : ℝ) + 1) ^ 10 := by
        rw [Int.cast_one]
        exact one_le_pow₀ (by linarith [hqnR])
      exact le_trans hpow (le_mul_of_one_le_left (by positivity) (by norm_num))
    obtain ⟨c0, hc0pos, hc0all, hc0log⟩ :=
      Work.TMC16Core.Core.theta_bound_of_setup (α := α) (θ := θ) (K₀ := K₀) (csm := csm) (Bz := Bz')
        hK₀1 hcsm (by linarith : csm ≤ 1) h1 h2 hBz'1
    refine ⟨min c0 (1 / 2), lt_min hc0pos (by norm_num), min_le_right _ _, ?_, ?_⟩
    · intro j hj
      exact le_trans (min_le_left _ _) (hc0all j (le_trans hj hBz'ge))
    · rcases le_or_gt c0 (1 / 2) with hle | hgt
      · rw [min_eq_left hle]
        have hKpos : (0 : ℝ) < 3 * 10 ^ 6 := by norm_num
        have hM1 : (1 : ℝ) ≤ (Bz' : ℝ) + 1 := by
          have : (1 : ℝ) ≤ (Bz' : ℝ) := by exact_mod_cast hBz'1
          linarith
        have hMbig : (Bz' : ℝ) + 1 ≤ 3 * 10 ^ 6 * ((q n : ℝ) + 1) ^ 10 := by
          have h1' : (1 : ℝ) ≤ 10 ^ 6 * ((q n : ℝ) + 1) ^ 10 := by
            have hp : (1 : ℝ) ≤ ((q n : ℝ) + 1) ^ 10 := by
              have h2' := pow_le_pow_right₀ (by linarith [hqnR] : (1 : ℝ) ≤ (q n : ℝ) + 1)
                (by norm_num : 1 ≤ 10)
              nlinarith [h2', hqnR]
            nlinarith [hp]
          linarith [hBz'bound, h1']
        have hnum := log_case2 (show (0 : ℝ) ≤ (q n : ℝ) by linarith) hM1 hMbig
        linarith [hc0log, hnum]
      · rw [min_eq_right (le_of_lt hgt)]
        rw [show (1 : ℝ) / (1 / 2) = 2 by norm_num]
        have h2le : Real.log 2 ≤ 100 := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
        have hnn : 0 ≤ 20 * Real.log ((q n : ℝ) + 2) := by
          apply mul_nonneg (by norm_num)
          exact Real.log_nonneg (by linarith [hA2])
        linarith [h2le, hcsm_le, hnn]

end Work.TMC16Core.Main

