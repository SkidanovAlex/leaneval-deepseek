import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs
import Submission.Work.Escape.Basic
import Submission.Work.Bottcher.Green.green_comm
import Submission.Work.Bottcher.Green.green_nonneg
import Submission.Work.Escape.green_le_log
import Submission.Work.ParamRaysCrit.GreenBound
import Submission.Work.Bottcher.Contraction.green_eq_greenFun
import Submission.Work.Bottcher.ContractionAux.isPreconnected_preimage_sq
import Submission.Work.Bottcher.Contraction.isPreconnected_iInter_of_antitone_isCompact
import Submission.Work.Bottcher.Contraction.exists_goodRadius_of_mem_mandelbar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The sublevel set `{G_c ≤ G_c(0)}` of the tricorn Green function is preconnected

For every parameter `c` the set of points whose Green function does not exceed the critical
level `greenParam c = G_c(0)` is preconnected.

The proof writes `{G_c ≤ G_c(0)}` as the intersection of a *decreasing* sequence of compact
preconnected "level balls"

  `A n = {z | ‖T_c^[n] z‖ ≤ radParam c n}`,   `radParam c n = exp (2^n * G_c(0) + δ)`,

and then applies `isPreconnected_iInter_of_antitone_isCompact`.  Two ingredients are used:

* the two-sided bound `|G_c w - log ‖w‖| ≤ log 2` above the escape radius
  (`Work.ParamRays.greenFun_le_log_add`, `Work.ParamRays.log_sub_le_greenFun`), transported to
  `Work.Bottcher.green` by `green_eq_greenFun`; this makes `⋂ A n = {G_c ≤ G_c(0)}` exactly;
* the branching of `T_c` at its unique critical point `0` (whose critical value is `c`): the
  preimage of a preconnected set containing the critical value `c` is preconnected
  (`isPreconnected_preimage_sq` through the evenness `T_c = conj ∘ sq + c`).

Every `A n` is preconnected by a downward induction, because the intermediate sets
`{z | ‖T_c^[k] z‖ ≤ radParam c n}` all contain the critical value `c` for `k ≤ n-1`.
-/

namespace Work.Bottcher.Contraction

open Metric Set Filter
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

/-! ## Elementary Green-function facts -/

theorem continuous_Tantibar (c : ℂ) : Continuous (Tantibar c) := by
  rw [← Work.Escape.Td_two_eq]
  exact Work.Escape.continuous_Td 2 c

/-- The Green function commutes with the iterates of `T_c` up to the factor `2 ^ n`. -/
theorem green_comm_iterate (c z : ℂ) (n : ℕ) :
    Work.Bottcher.green c ((Tantibar c)^[n] z) = (2 : ℝ) ^ n * Work.Bottcher.green c z := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Work.Bottcher.Green.green_comm, ih, pow_succ]
      ring

theorem greenParam_nonneg' (c : ℂ) : 0 ≤ Work.Bottcher.greenParam c := by
  rw [Work.Bottcher.greenParam_def]
  exact Work.Bottcher.Green.green_nonneg c 0

/-- The threshold `max 2 ‖c‖` lies below the escape radius `2 (1 + ‖c‖)`. -/
theorem max_two_norm_le_escapeRadius (c : ℂ) :
    max 2 ‖c‖ ≤ Work.Bottcher.escapeRadius c := by
  rw [Work.Bottcher.escapeRadius, max_le_iff]
  exact ⟨by have := norm_nonneg c; linarith, by have := norm_nonneg c; linarith⟩

/-- Above the threshold `max 2 ‖c‖` the tricorn Green function is `log ‖·‖` up to `log 2`. -/
theorem green_le_log_add' (c w : ℂ) (h : max 2 ‖c‖ < ‖w‖) :
    Work.Bottcher.green c w ≤ Real.log ‖w‖ + Real.log 2 := by
  rw [green_eq_greenFun]
  exact Work.ParamRays.greenFun_le_log_add c w h

theorem log_sub_le_green' (c w : ℂ) (h : max 2 ‖c‖ < ‖w‖) :
    Real.log ‖w‖ - Real.log 2 ≤ Work.Bottcher.green c w := by
  rw [green_eq_greenFun]
  exact Work.ParamRays.log_sub_le_greenFun c w h

/-- Above the threshold `max 2 ‖c‖` the map `T_c` strictly increases the modulus. -/
theorem lt_norm_Tantibar (c w : ℂ) (h : max 2 ‖c‖ < ‖w‖) :
    ‖w‖ < ‖Tantibar c w‖ := by
  have hge : ‖w‖ ^ 2 - ‖c‖ ≤ ‖Tantibar c w‖ := by
    have hh := Work.Escape.norm_Td_ge 2 c w
    rw [Work.Escape.Td_two_eq] at hh
    exact hh
  have hw2 : (2 : ℝ) < ‖w‖ := lt_of_le_of_lt (le_max_left _ _) h
  have hwc : ‖c‖ < ‖w‖ := lt_of_le_of_lt (le_max_right _ _) h
  have hnn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  nlinarith [hge, hw2, hwc, hnn, sq_nonneg (‖w‖ - 2)]

/-! ## The approximating radii -/

/-- A fixed additive constant, large enough so that `exp (greenDelta c)` dominates the escape
radius and `greenDelta c ≥ 3 log 2`. -/
noncomputable def greenDelta (c : ℂ) : ℝ :=
  Real.log (Work.Bottcher.escapeRadius c + 1) + 3 * Real.log 2 + 1

theorem three_log_two_le_greenDelta (c : ℂ) : 3 * Real.log 2 ≤ greenDelta c := by
  rw [greenDelta]
  have h : 0 ≤ Real.log (Work.Bottcher.escapeRadius c + 1) := by
    apply Real.log_nonneg
    rw [Work.Bottcher.escapeRadius]
    have := norm_nonneg c
    linarith
  linarith

theorem greenDelta_pos (c : ℂ) : 0 < greenDelta c :=
  lt_of_lt_of_le (by have h := Real.log_pos (show (1 : ℝ) < 2 by norm_num); linarith)
    (three_log_two_le_greenDelta c)

theorem escapeRadius_lt_exp_greenDelta (c : ℂ) :
    Work.Bottcher.escapeRadius c < Real.exp (greenDelta c) := by
  have hR : (0 : ℝ) < Work.Bottcher.escapeRadius c + 1 := by
    rw [Work.Bottcher.escapeRadius]; positivity
  have hle : Real.log (Work.Bottcher.escapeRadius c + 1) ≤ greenDelta c := by
    rw [greenDelta]
    have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  have hexp := Real.exp_le_exp.mpr hle
  rw [Real.exp_log hR] at hexp
  linarith

/-- The radius of the `n`-th level ball: `exp (2^n * G_c(0) + δ)`. -/
noncomputable def radParam (c : ℂ) (n : ℕ) : ℝ :=
  Real.exp (((2 : ℝ) ^ n) * Work.Bottcher.greenParam c + greenDelta c)

theorem radParam_pos (c : ℂ) (n : ℕ) : 0 < radParam c n := Real.exp_pos _

theorem exp_greenDelta_le_radParam (c : ℂ) (n : ℕ) :
    Real.exp (greenDelta c) ≤ radParam c n := by
  rw [radParam]
  apply Real.exp_le_exp.mpr
  have h : (0 : ℝ) ≤ (2 : ℝ) ^ n * Work.Bottcher.greenParam c :=
    mul_nonneg (by positivity) (greenParam_nonneg' c)
  linarith

theorem escapeRadius_lt_radParam (c : ℂ) (n : ℕ) :
    Work.Bottcher.escapeRadius c < radParam c n :=
  lt_of_lt_of_le (escapeRadius_lt_exp_greenDelta c) (exp_greenDelta_le_radParam c n)

theorem max_two_norm_lt_radParam (c : ℂ) (n : ℕ) : max 2 ‖c‖ < radParam c n :=
  lt_of_le_of_lt (max_two_norm_le_escapeRadius c) (escapeRadius_lt_radParam c n)

theorem log_radParam (c : ℂ) (n : ℕ) :
    Real.log (radParam c n) = (2 : ℝ) ^ n * Work.Bottcher.greenParam c + greenDelta c :=
  Real.log_exp _

/-! ## A uniform bound on the Green function in the ball of radius `max 2 ‖c‖` -/

noncomputable def greenBoundBall (c : ℂ) : ℝ :=
  2 * Real.log (max 2 (max (‖c‖ + 1) (max 2 ‖c‖)))

theorem greenBoundBall_nonneg (c : ℂ) : 0 ≤ greenBoundBall c := by
  rw [greenBoundBall]
  refine mul_nonneg (by norm_num) (Real.log_nonneg ?_)
  exact le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_max_left _ _)

theorem green_le_greenBoundBall (c w : ℂ) (h : ‖w‖ ≤ max 2 ‖c‖) :
    Work.Bottcher.green c w ≤ greenBoundBall c := by
  rw [greenBoundBall, Work.Bottcher.green_def]
  have hb := Work.Escape.green_le_log (Tantibar c) 2 ‖c‖
    (Work.Escape.monicGrowth_Tantibar c) le_rfl w
  have hmono : Real.log (max 2 (max (‖c‖ + 1) ‖w‖)) ≤
      Real.log (max 2 (max (‖c‖ + 1) (max 2 ‖c‖))) := by
    apply Real.log_le_log
    · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)
    · refine max_le (le_max_left _ _) (max_le ?_ ?_)
      · exact le_trans (le_max_left _ _) (le_max_right _ _)
      · exact le_trans h (le_trans (le_max_right _ _) (le_max_right _ _))
  calc Work.Escape.green (Tantibar c) 2 w
        ≤ 2 * Real.log (max 2 (max (‖c‖ + 1) ‖w‖)) := hb
    _ ≤ 2 * Real.log (max 2 (max (‖c‖ + 1) (max 2 ‖c‖))) :=
        mul_le_mul_of_nonneg_left hmono (by norm_num)

/-! ## Elementary real facts about logarithms and exponentials -/

theorem real_self_le_exp_log (x : ℝ) (hx : 0 ≤ x) : x ≤ Real.exp (Real.log x) := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h, Real.log_zero, Real.exp_zero]; norm_num
  · rw [Real.exp_log h]

theorem log_norm_le_log_radParam (c : ℂ) (n : ℕ) {w : ℂ} (h : ‖w‖ ≤ radParam c n) :
    Real.log ‖w‖ ≤ Real.log (radParam c n) := by
  rcases eq_or_lt_of_le (norm_nonneg w) with h0 | hpos
  · rw [← h0, Real.log_zero]
    apply Real.log_nonneg
    exact le_of_lt (lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (greenDelta_pos c))
      (exp_greenDelta_le_radParam c n))
  · exact Real.log_le_log hpos h

/-! ## The critical orbit stays inside the level balls -/

theorem crit_orbit_le_radParam (c : ℂ) {k n : ℕ} (hkn : k + 1 ≤ n) :
    ‖(Tantibar c)^[k] c‖ ≤ radParam c n := by
  set w : ℂ := (Tantibar c)^[k + 1] 0 with hw
  have hcw : (Tantibar c)^[k] c = w := by
    rw [hw, Function.iterate_succ_apply, Work.Bottcher.Tantibar_zero]
  have hG : Work.Bottcher.green c w = (2 : ℝ) ^ (k + 1) * Work.Bottcher.greenParam c := by
    rw [hw, green_comm_iterate, ← Work.Bottcher.greenParam_def]
  rw [hcw]
  by_cases hle : ‖w‖ ≤ max 2 ‖c‖
  · exact le_trans hle (le_of_lt (max_two_norm_lt_radParam c n))
  · have hlt : max 2 ‖c‖ < ‖w‖ := not_le.mp hle
    have h1 := log_sub_le_green' c w hlt
    rw [hG] at h1
    have hlam := greenParam_nonneg' c
    have hpow : (2 : ℝ) ^ (k + 1) * Work.Bottcher.greenParam c
        ≤ (2 : ℝ) ^ n * Work.Bottcher.greenParam c :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hkn) hlam
    have hdel := three_log_two_le_greenDelta c
    have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog : Real.log ‖w‖ ≤ (2 : ℝ) ^ n * Work.Bottcher.greenParam c + greenDelta c := by
      linarith [h1, hpow, hdel, hlog2]
    calc ‖w‖ ≤ Real.exp (Real.log ‖w‖) := real_self_le_exp_log _ (norm_nonneg w)
      _ ≤ Real.exp ((2 : ℝ) ^ n * Work.Bottcher.greenParam c + greenDelta c) :=
          Real.exp_le_exp.mpr hlog
      _ = radParam c n := by rw [radParam]

/-! ## The preimage of a preconnected set containing the critical value is preconnected -/

theorem isPreconnected_preimage_Tantibar {c : ℂ} {S : Set ℂ} (hS : IsPreconnected S)
    (hc : c ∈ S) : IsPreconnected ((Tantibar c) ⁻¹' S) := by
  have hSc : IsPreconnected ((fun s : ℂ => s - c) '' S) :=
    hS.image _ (continuous_id.sub continuous_const).continuousOn
  have h0c : (0 : ℂ) ∈ (fun s : ℂ => s - c) '' S := ⟨c, hc, by ring⟩
  have hpre : IsPreconnected ((fun w : ℂ => w ^ 2) ⁻¹' ((fun s : ℂ => s - c) '' S)) :=
    Work.Bottcher.ContractionAux.isPreconnected_preimage_sq hSc h0c
  have himg : (Tantibar c) ⁻¹' S =
      (starRingEnd ℂ) '' ((fun w : ℂ => w ^ 2) ⁻¹' ((fun s : ℂ => s - c) '' S)) := by
    ext z
    constructor
    · intro hz
      refine ⟨starRingEnd ℂ z, ?_, by simp⟩
      rw [Set.mem_preimage]
      refine ⟨(starRingEnd ℂ z) ^ 2 + c, ?_, by ring⟩
      simpa only [Set.mem_preimage, LeanEval.ComplexAnalysis.Tantibar] using hz
    · rintro ⟨w, hw, rfl⟩
      rw [Set.mem_preimage] at hw
      obtain ⟨s, hsS, hs⟩ := hw
      show LeanEval.ComplexAnalysis.Tantibar c (starRingEnd ℂ w) ∈ S
      simp only [LeanEval.ComplexAnalysis.Tantibar]
      rw [show starRingEnd ℂ (starRingEnd ℂ w) = w by simp]
      rw [show w ^ 2 + c = s by rw [← hs]; ring]
      exact hsS
  rw [himg]
  exact hpre.image _ continuous_star.continuousOn

/-! ## The level balls -/

def levelBall (c : ℂ) (n : ℕ) : Set ℂ := {z : ℂ | ‖(Tantibar c)^[n] z‖ ≤ radParam c n}

theorem isPreconnected_levelBall (c : ℂ) (n : ℕ) : IsPreconnected (levelBall c n) := by
  have key : ∀ k, k ≤ n → IsPreconnected {z : ℂ | ‖(Tantibar c)^[k] z‖ ≤ radParam c n} := by
    intro k
    induction k with
    | zero =>
        intro _
        have hset : {z : ℂ | ‖(Tantibar c)^[0] z‖ ≤ radParam c n}
            = closedBall 0 (radParam c n) := by
          ext z; simp [mem_closedBall, dist_eq_norm]
        rw [hset]
        exact (convex_closedBall (0 : ℂ) (radParam c n)).isPreconnected
    | succ k ih =>
        intro hk
        have hkn : k ≤ n := Nat.le_of_succ_le hk
        have hpre : IsPreconnected {z : ℂ | ‖(Tantibar c)^[k] z‖ ≤ radParam c n} := ih hkn
        have hcmem : c ∈ {z : ℂ | ‖(Tantibar c)^[k] z‖ ≤ radParam c n} :=
          crit_orbit_le_radParam c hk
        have hset : {z : ℂ | ‖(Tantibar c)^[k + 1] z‖ ≤ radParam c n}
            = (Tantibar c) ⁻¹' {z : ℂ | ‖(Tantibar c)^[k] z‖ ≤ radParam c n} := by
          ext z
          simp [Function.iterate_succ_apply]
        rw [hset]
        exact isPreconnected_preimage_Tantibar hpre hcmem
  exact key n le_rfl

theorem norm_le_of_mem_levelBall (c : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ levelBall c n) :
    ‖z‖ ≤ max (Work.Bottcher.escapeRadius c) (radParam c n) := by
  by_contra h
  rw [not_le] at h
  have hz_esc : Work.Bottcher.escapeRadius c < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) h
  have hz_rad : radParam c n < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) h
  have key : ∀ k ≤ n, ‖z‖ ≤ ‖(Tantibar c)^[k] z‖ := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        have hk' : k ≤ n := Nat.le_of_succ_le hk
        have hle := ih hk'
        have hesc : Work.Bottcher.escapeRadius c ≤ ‖(Tantibar c)^[k] z‖ :=
          le_trans hz_esc.le hle
        have hstep := le_norm_Tantibar_of_escapeRadius_le c ((Tantibar c)^[k] z) hesc
        rw [Function.iterate_succ_apply']
        linarith
  have hzle : ‖(Tantibar c)^[n] z‖ ≤ radParam c n := hz
  have hfin := key n le_rfl
  linarith

theorem isCompact_levelBall (c : ℂ) (n : ℕ) : IsCompact (levelBall c n) := by
  have hclosed : IsClosed (levelBall c n) := by
    have hcont : Continuous fun z : ℂ => (Tantibar c)^[n] z := (continuous_Tantibar c).iterate n
    exact isClosed_le hcont.norm continuous_const
  refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, ?_⟩
  exact (Metric.isBounded_closedBall (x := 0)
    (r := max (Work.Bottcher.escapeRadius c) (radParam c n))).subset (fun z hz => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact norm_le_of_mem_levelBall c n hz)

theorem levelBall_antitone (c : ℂ) (n : ℕ) : levelBall c (n + 1) ⊆ levelBall c n := by
  intro z hz
  by_cases hle : ‖(Tantibar c)^[n] z‖ ≤ max 2 ‖c‖
  · exact le_trans hle (le_of_lt (max_two_norm_lt_radParam c n))
  · have hlt : max 2 ‖c‖ < ‖(Tantibar c)^[n] z‖ := not_le.mp hle
    have hlt' : max 2 ‖c‖ < ‖Tantibar c ((Tantibar c)^[n] z)‖ :=
      lt_trans hlt (lt_norm_Tantibar c _ hlt)
    have hz' : ‖Tantibar c ((Tantibar c)^[n] z)‖ ≤ radParam c (n + 1) := by
      rw [← Function.iterate_succ_apply' (Tantibar c) n z]; exact hz
    have h1 := green_le_log_add' c (Tantibar c ((Tantibar c)^[n] z)) hlt'
    have hcomm := Work.Bottcher.Green.green_comm c ((Tantibar c)^[n] z)
    rw [hcomm] at h1
    have h2 := log_sub_le_green' c ((Tantibar c)^[n] z) hlt
    have hlog2 : Real.log ‖Tantibar c ((Tantibar c)^[n] z)‖ ≤ Real.log (radParam c (n + 1)) :=
      log_norm_le_log_radParam c (n + 1) hz'
    rw [log_radParam] at hlog2
    have hdel := three_log_two_le_greenDelta c
    have hgw : Work.Bottcher.green c ((Tantibar c)^[n] z) ≤
        ((2 : ℝ) ^ (n + 1) * Work.Bottcher.greenParam c + greenDelta c + Real.log 2) / 2 := by
      linarith
    have hpow : (2 : ℝ) ^ (n + 1) * Work.Bottcher.greenParam c
        = 2 * ((2 : ℝ) ^ n * Work.Bottcher.greenParam c) := by rw [pow_succ]; ring
    have hlog2b : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlw : Real.log ‖(Tantibar c)^[n] z‖ ≤
        (2 : ℝ) ^ n * Work.Bottcher.greenParam c + greenDelta c := by
      linarith [h2, hgw, hpow, hdel, hlog2b]
    calc ‖(Tantibar c)^[n] z‖ ≤ Real.exp (Real.log ‖(Tantibar c)^[n] z‖) :=
          real_self_le_exp_log _ (norm_nonneg _)
      _ ≤ Real.exp ((2 : ℝ) ^ n * Work.Bottcher.greenParam c + greenDelta c) :=
          Real.exp_le_exp.mpr hlw
      _ = radParam c n := by rw [radParam]

/-! ## The intersection is exactly the sublevel set -/

theorem iInter_levelBall_eq (c : ℂ) :
    (⋂ n, levelBall c n) = {z : ℂ | Work.Bottcher.green c z ≤ Work.Bottcher.greenParam c} := by
  ext z
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, levelBall]
  constructor
  · intro hz
    set C : ℝ := max (greenBoundBall c) (greenDelta c + Real.log 2) with hC
    have hCnn : 0 ≤ C := by
      rw [hC]
      exact le_trans (greenBoundBall_nonneg c) (le_max_left _ _)
    have hmain : ∀ n, Work.Bottcher.green c z ≤ Work.Bottcher.greenParam c + C / (2 : ℝ) ^ n := by
      intro n
      have hGn := green_comm_iterate c z n
      have hb : Work.Bottcher.green c ((Tantibar c)^[n] z) ≤
          max (greenBoundBall c)
            ((2 : ℝ) ^ n * Work.Bottcher.greenParam c + greenDelta c + Real.log 2) := by
        by_cases hle : ‖(Tantibar c)^[n] z‖ ≤ max 2 ‖c‖
        · exact le_trans (green_le_greenBoundBall c _ hle) (le_max_left _ _)
        · have hlt : max 2 ‖c‖ < ‖(Tantibar c)^[n] z‖ := not_le.mp hle
          have h1 := green_le_log_add' c ((Tantibar c)^[n] z) hlt
          have h2 : Real.log ‖(Tantibar c)^[n] z‖ ≤ Real.log (radParam c n) :=
            log_norm_le_log_radParam c n (hz n)
          rw [log_radParam] at h2
          exact le_trans (by linarith) (le_max_right _ _)
      have hp : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
      have hdiv : Work.Bottcher.green c z ≤
          max (greenBoundBall c)
            ((2 : ℝ) ^ n * Work.Bottcher.greenParam c + greenDelta c + Real.log 2)
            / (2 : ℝ) ^ n := by
        rw [le_div_iff₀ hp]
        rw [hGn] at hb
        linarith [hb]
      have hmax : max (greenBoundBall c)
            ((2 : ℝ) ^ n * Work.Bottcher.greenParam c + greenDelta c + Real.log 2)
            / (2 : ℝ) ^ n
          ≤ Work.Bottcher.greenParam c + C / (2 : ℝ) ^ n := by
        rw [div_le_iff₀ hp]
        have hX : (Work.Bottcher.greenParam c + C / (2 : ℝ) ^ n) * (2 : ℝ) ^ n
            = Work.Bottcher.greenParam c * (2 : ℝ) ^ n + C := by
          rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hp)]
        rw [hX]
        apply max_le
        · have hAC : greenBoundBall c ≤ C := by rw [hC]; exact le_max_left _ _
          have hlam := greenParam_nonneg' c
          nlinarith [hAC, hlam, hp]
        · have hBC : greenDelta c + Real.log 2 ≤ C := by rw [hC]; exact le_max_right _ _
          nlinarith [hBC]
      linarith
    have htend : Filter.Tendsto (fun n : ℕ => Work.Bottcher.greenParam c + C / (2 : ℝ) ^ n)
        Filter.atTop (nhds (Work.Bottcher.greenParam c)) := by
      have h0 : Filter.Tendsto (fun n : ℕ => C / (2 : ℝ) ^ n) Filter.atTop (nhds 0) := by
        have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
          (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
        have heq : (fun n : ℕ => C / (2 : ℝ) ^ n) = fun n : ℕ => C * (1 / 2 : ℝ) ^ n := by
          funext n; rw [div_eq_mul_inv, one_div, inv_pow]
        rw [heq]
        simpa using hp.const_mul C
      simpa using tendsto_const_nhds.add h0
    exact ge_of_tendsto htend (Filter.Eventually.of_forall hmain)
  · intro hz n
    have hGn := green_comm_iterate c z n
    by_cases hle : ‖(Tantibar c)^[n] z‖ ≤ max 2 ‖c‖
    · exact le_trans hle (le_of_lt (max_two_norm_lt_radParam c n))
    · have hlt : max 2 ‖c‖ < ‖(Tantibar c)^[n] z‖ := not_le.mp hle
      have h2 := log_sub_le_green' c ((Tantibar c)^[n] z) hlt
      rw [hGn] at h2
      have h3 : (2 : ℝ) ^ n * Work.Bottcher.green c z
          ≤ (2 : ℝ) ^ n * Work.Bottcher.greenParam c :=
        mul_le_mul_of_nonneg_left hz (by positivity)
      have hdel := three_log_two_le_greenDelta c
      have hlog2c : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hlog : Real.log ‖(Tantibar c)^[n] z‖
          ≤ (2 : ℝ) ^ n * Work.Bottcher.greenParam c + greenDelta c := by
        linarith [h2, h3, hdel, hlog2c]
      calc ‖(Tantibar c)^[n] z‖ ≤ Real.exp (Real.log ‖(Tantibar c)^[n] z‖) :=
            real_self_le_exp_log _ (norm_nonneg _)
        _ ≤ Real.exp ((2 : ℝ) ^ n * Work.Bottcher.greenParam c + greenDelta c) :=
            Real.exp_le_exp.mpr hlog
        _ = radParam c n := by rw [radParam]

theorem isPreconnected_green_le_greenParam (c : ℂ) :
    IsPreconnected {z : ℂ | Work.Bottcher.green c z ≤ Work.Bottcher.greenParam c} := by
  rw [← iInter_levelBall_eq c]
  exact isPreconnected_iInter_of_antitone_isCompact (isCompact_levelBall c)
    (isPreconnected_levelBall c) (levelBall_antitone c)

end

end Work.Bottcher.Contraction
