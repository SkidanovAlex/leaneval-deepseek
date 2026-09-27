import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.FanTri.BranchCompDefs
import Submission.Work.EQ.FanTri.branchComp_axis
import Submission.Work.EQ.FanTri.wtAux_uniform_bound
import Submission.Work.EQ.FanTri.Phi_bdd
import Submission.Work.EQ.FanSep.axis_walk
import Submission.Work.EQ.walk_bounds
import Submission.Work.EQ.charVal_main
import Submission.Work.EQ.FanTri.invBranch_axis_differentiableOn_ball
import Submission.Work.EQ.FanTri.branchComp_radius

namespace Work.EQ.FanTri

open Work.EQ
open Set

noncomputable section

/-! ## Self-contained bookkeeping for the two-point scaled Lipschitz bound

`branchComp a w` reads the word from the head (the head letter is applied last), so the walk on
the real axis that governs the composition reads `w.reverse`.  Everything in this section is a
local copy of the walk bookkeeping (the shared file `branchComp_radius` is being rewritten, so
the definitions used here are kept self-contained). -/

/-- The walk state of the word `w`: the state reached by reading `w.reverse` from state `0`. -/
def walkSt (w : List Bool) : ℕ := stAux w.reverse 0

/-- The walk weight of the word `w`: the product of the step weights along the walk of
`w.reverse` from state `0`. -/
def walkWt (a : ℝ) (w : List Bool) : ℝ := wtAux a w.reverse 0

@[simp] lemma walkSt_nil : walkSt ([] : List Bool) = 0 := rfl

@[simp] lemma walkWt_nil (a : ℝ) : walkWt a ([] : List Bool) = 1 := rfl

lemma walkSt_cons (c : Bool) (w : List Bool) : walkSt (c :: w) = stp c (walkSt w) := by
  simp only [walkSt, List.reverse_cons, stAux_append, stAux_nil]
  rfl

lemma walkWt_cons (a : ℝ) (c : Bool) (w : List Bool) :
    walkWt a (c :: w) = stW a c (walkSt w) * walkWt a w := by
  simp only [walkWt, List.reverse_cons, wtAux_append, wtAux_nil, wtAux_cons, walkSt]
  ring

/-- **The walk weight splits at any suffix.**  Reading `w.reverse` is the same as first walking
along the reverse of the last `k` letters and then continuing with the reverse of the remaining
prefix, so the weight is a product. -/
lemma walkWt_eq_mul_drop (a : ℝ) (w : List Bool) (k : ℕ) :
    walkWt a w = walkWt a (w.drop k) *
      wtAux a (w.take k).reverse (walkSt (w.drop k)) := by
  have hsplit : w.reverse = (w.drop k).reverse ++ (w.take k).reverse := by
    rw [← List.reverse_append, List.take_append_drop]
  rw [walkWt, hsplit, wtAux_append]
  rfl

/-- The step weight is `λ` times the modulus of the one-step factor `-1 + sgnB c / q`. -/
lemma stW_eq' {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (c : Bool) (n : ℕ) :
    stW a c n = eqLam a * |(-1 + sgnB c / stQ a n)| := by
  have hq : 0 < stQ a n := wb_stQ_pos ha0 ha1 n
  have hlam : 0 < eqLam a := eqLam_pos' ha0 ha1
  cases c with
  | true =>
      have h1 : stW a true n = |dnW a n| := by simp [stW]
      rw [h1, dnW, abs_mul, abs_of_pos hlam, sgnB_true]
      congr 1
      rw [show (-1 + 1 / stQ a n) = -(1 - 1 / stQ a n) by ring, abs_neg]
  | false =>
      have h1 : stW a false n = upW a n := by simp [stW]
      rw [h1, upW, sgnB_false]
      congr 1
      rw [show (-1 + -1 / stQ a n) = -(1 + 1 / stQ a n) by ring, abs_neg,
        abs_of_pos (by positivity)]

/-- **The centre of a finite composition of inverse branches is a walk centre.** -/
lemma branchComp_walkSt {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (w : List Bool) :
    Work.EQ.FanTri.branchComp a w (((-1 / 2 : ℝ) : ℂ), (0 : ℂ)) =
      (((stCtr (walkSt w) : ℝ) : ℂ), (0 : ℂ)) := by
  obtain ⟨hstp, -, hne, -⟩ := walk_bounds (a := a) ha0 ha1
  induction w with
  | nil => simp [walkSt, stCtr_zero, stCtr, stIdx]
  | cons c w ih =>
      rw [branchComp_cons, ih, walkSt_cons]
      rw [FanSep.invBranch_axis (a := a) c (hne (walkSt w))]
      rw [hstp]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst]
        congr 1
        rw [axStep]
        have h1 : sgnB c = (if c = true then (1 : ℝ) else -1) := by cases c <;> rfl
        have h2 : sgnR (stCtr (walkSt w) + a / 2)
            = (stCtr (walkSt w) + a / 2) / |stCtr (walkSt w) + a / 2| :=
          (div_abs_self (hne (walkSt w))).symm
        rw [h1, h2, ← mul_div_assoc]
      · simp

/-- **Holomorphy of a finite composition of inverse branches at the scaled radius.**

If the one-point scaled estimate `λ^|v| ‖F_v z - F_v A₁‖ ≤ D ‖z - A₁‖` holds on the ball of
radius `ρ λ^|v|` for every word `v`, and `Dρλ < (1-a)/8` (so that every intermediate composition
lands in the disc of radius `(1-a)/8` about an axis point, on which `invBranch` is holomorphic),
then `branchComp a w` is holomorphic on the ball of radius `ρ λ^|w|` about `A₁`. -/
lemma branchComp_differentiableOn_scaled {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {ρ D : ℝ} (hρ : 0 < ρ) (hD : 0 < D)
    (hbnd : ∀ (v : List Bool) (z : ℂ × ℂ),
      ‖z - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ ≤ ρ * (eqLam a) ^ v.length →
      (eqLam a) ^ v.length *
        ‖branchComp a v z - branchComp a v (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖
        ≤ D * ‖z - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖)
    (hsmall : D * ρ * eqLam a < (1 - a) / 8) :
    ∀ w : List Bool, DifferentiableOn ℂ (branchComp a w)
      (Metric.ball (((-1 / 2 : ℝ) : ℂ), (0 : ℂ)) (ρ * (eqLam a) ^ w.length)) := by
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1le : eqLam a ≤ 1 := (eqLam_lt_one' ha0 ha1).le
  intro w
  induction w with
  | nil =>
      rw [branchComp_nil]
      simpa using differentiableOn_id
  | cons c w' ih =>
      have hax : ∃ k : ℤ, stCtr (walkSt w') = -1 / 2 + 2 * (k : ℝ) :=
        ⟨stIdx (walkSt w'), rfl⟩
      have houter : DifferentiableOn ℂ (invBranch a c)
          (Metric.ball (((stCtr (walkSt w') : ℝ) : ℂ), (0 : ℂ)) ((1 - a) / 8)) :=
        invBranch_axis_differentiableOn_ball (a := a) ha0 ha1 hax c
      have hinner : DifferentiableOn ℂ (branchComp a w')
          (Metric.ball (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))
            (ρ * (eqLam a) ^ (c :: w').length)) :=
        ih.mono (Metric.ball_subset_ball (by
          rw [List.length_cons, pow_succ]
          exact mul_le_mul_of_nonneg_left
            (mul_le_of_le_one_right (pow_nonneg hlam0.le _) hlam1le) hρ.le))
      have hmap : MapsTo (branchComp a w')
          (Metric.ball (((-1 / 2 : ℝ) : ℂ), (0 : ℂ)) (ρ * (eqLam a) ^ (c :: w').length))
          (Metric.ball (((stCtr (walkSt w') : ℝ) : ℂ), (0 : ℂ)) ((1 - a) / 8)) := by
        intro z hz
        rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
        have hz' : ‖z - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖
            ≤ ρ * ((eqLam a) ^ w'.length * eqLam a) := by
          have h := hz.le
          rw [List.length_cons, pow_succ] at h
          exact h
        have hp : ‖z - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖
            ≤ ρ * (eqLam a) ^ w'.length :=
          le_trans hz' (mul_le_mul_of_nonneg_left
            (mul_le_of_le_one_right (pow_nonneg hlam0.le _) hlam1le) hρ.le)
        have hb := hbnd w' z hp
        rw [branchComp_walkSt (a := a) ha0 ha1 w'] at hb
        have hlamm : 0 < (eqLam a) ^ w'.length := pow_pos hlam0 _
        have h1 : ‖branchComp a w' z
            - (((stCtr (walkSt w') : ℝ) : ℂ), (0 : ℂ))‖
            ≤ D * ‖z - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ / (eqLam a) ^ w'.length := by
          refine (le_div_iff₀ hlamm).mpr ?_
          rw [mul_comm]
          exact hb
        have h2 : D * ‖z - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ / (eqLam a) ^ w'.length
            ≤ D * ρ * eqLam a := by
          calc D * ‖z - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ / (eqLam a) ^ w'.length
              ≤ D * (ρ * ((eqLam a) ^ w'.length * eqLam a)) / (eqLam a) ^ w'.length := by
                gcongr
            _ = D * ρ * eqLam a := by field_simp
        linarith [h1, h2, hsmall]
      have hcomp : DifferentiableOn ℂ (fun z => invBranch a c (branchComp a w' z))
          (Metric.ball (((-1 / 2 : ℝ) : ℂ), (0 : ℂ)) (ρ * (eqLam a) ^ (c :: w').length)) :=
        DifferentiableOn.comp (s := Metric.ball (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))
            (ρ * (eqLam a) ^ (c :: w').length))
          (t := Metric.ball (((stCtr (walkSt w') : ℝ) : ℂ), (0 : ℂ)) ((1 - a) / 8))
          houter hinner hmap
      exact hcomp

/-- **Two-point scaled Lipschitz bound for a finite composition of inverse branches near `A₁`.**
There are `ρ D > 0` such that for every word `w` and all `x, y` in the ball of radius
`ρ * λ ^ |w|` about `A₁ = (-1/2,0)`,
`λ ^ |w| * ‖branchComp a w x - branchComp a w y‖ ≤ D * ‖x - y‖`.

This is the sharper form needed for the prefix reduction of `fan_gap_unif`: the composition is
analytic on the ball of radius `ρ * λ ^ |w|` (each inverse branch is analytic on a ball of uniform
radius about every axis point, and the first step from `A₁` shrinks only through the stationary
factor `1/λ`), and its derivative there is bounded by `D * λ ^ (-|w|)`.

Route of the proof below.  The one-point scaled estimate
`λ^|w| ‖F_w z - F_w A₁‖ ≤ D₀ ‖z - A₁‖` on the ball of radius `ρ₀ λ^|w|` is
`Work.EQ.FanTri.branchComp_radius`.  Scaling `ρ` down so that `D₀ ρ λ < (1-a)/8` makes `F_w`
holomorphic on the ball of radius `ρ λ^|w|` about `A₁` (`branchComp_differentiableOn_scaled`:
every intermediate composition lands in the disc of radius `(1-a)/8` about an axis point, where
`invBranch` is holomorphic — `Work.EQ.FanTri.invBranch_axis_differentiableOn_ball`).  The Schwarz
lemma (`Complex.dist_le_div_mul_dist_of_mapsTo_ball`) applied at an interior centre `x` — the
image of the ball of radius `ρλ^n/2` about `x` is contained in the closed ball of radius `2D₀ρ`
about `F_w x`, because both `F_w x` and `F_w z` are within `D₀ρ` of `F_w A₁` — then gives the
two-point bound with constant `4D₀`. -/
theorem branchComp_lipschitz_scaled {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ ρ D : ℝ, 0 < ρ ∧ 0 < D ∧ ∀ (w : List Bool) (x y : ℂ × ℂ),
      ‖x - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ ≤ ρ * (Work.EQ.eqLam a) ^ w.length →
      ‖y - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ ≤ ρ * (Work.EQ.eqLam a) ^ w.length →
      (Work.EQ.eqLam a) ^ w.length *
        ‖Work.EQ.FanTri.branchComp a w x - Work.EQ.FanTri.branchComp a w y‖
        ≤ D * ‖x - y‖ := by
  obtain ⟨ρ₀, D₀, hρ₀, hD₀, hbnd₀⟩ := branchComp_radius ha0 ha1
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hlam1le : eqLam a ≤ 1 := hlam1.le
  have h1a : 0 < 1 - a := by linarith
  set ρ₂ : ℝ := min (ρ₀ / 8) ((1 - a) / (64 * D₀)) with hρ₂def
  have hρ₂0 : 0 < ρ₂ := lt_min (by linarith) (div_pos h1a (by positivity))
  have hρ₂ρ₀ : ρ₂ ≤ ρ₀ := le_trans (min_le_left _ _) (by linarith)
  have hρ₂D : D₀ * ρ₂ * eqLam a < (1 - a) / 8 := by
    have hle : ρ₂ ≤ (1 - a) / (64 * D₀) := min_le_right _ _
    have h1 : D₀ * ρ₂ ≤ (1 - a) / 64 := by
      have h2 := mul_le_mul_of_nonneg_left hle hD₀.le
      have h3 : D₀ * ((1 - a) / (64 * D₀)) = (1 - a) / 64 := by
        field_simp
      rwa [h3] at h2
    calc D₀ * ρ₂ * eqLam a ≤ D₀ * ρ₂ * 1 :=
          mul_le_mul_of_nonneg_left hlam1le (mul_nonneg hD₀.le hρ₂0.le)
      _ ≤ (1 - a) / 64 := by linarith
      _ < (1 - a) / 8 := by linarith
  have hbnd₂ : ∀ (v : List Bool) (z : ℂ × ℂ),
      ‖z - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ ≤ ρ₂ * (eqLam a) ^ v.length →
      (eqLam a) ^ v.length *
        ‖branchComp a v z - branchComp a v (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖
        ≤ D₀ * ‖z - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ := by
    intro v z hz
    exact hbnd₀ v z (le_trans hz (mul_le_mul_of_nonneg_right hρ₂ρ₀ (pow_nonneg hlam0.le _)))
  have hdiff := branchComp_differentiableOn_scaled (a := a) ha0 ha1 hρ₂0 hD₀ hbnd₂ hρ₂D
  refine ⟨ρ₂ / 8, 4 * D₀, by linarith, by linarith, ?_⟩
  intro w x y hx hy
  have hR0 : 0 < ρ₂ * (eqLam a) ^ w.length := mul_pos hρ₂0 (pow_pos hlam0 _)
  have hxhalf : ‖x - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖
      ≤ ρ₂ * (eqLam a) ^ w.length / 2 := by
    have h1 : (ρ₂ / 8) * (eqLam a) ^ w.length ≤ ρ₂ * (eqLam a) ^ w.length / 2 := by
      nlinarith [pow_pos hlam0 w.length, hρ₂0.le]
    linarith [hx, h1]
  -- every point of the ball of radius `ρ λ ^ n` is within `D₀ ρ₂` of the image of `A₁`
  have hdev : ∀ u : ℂ × ℂ, ‖u - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ ≤ ρ₂ * (eqLam a) ^ w.length →
      ‖branchComp a w u - branchComp a w (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ ≤ D₀ * ρ₂ := by
    intro u hu
    have hb := hbnd₂ w u hu
    have hlamn : 0 < (eqLam a) ^ w.length := pow_pos hlam0 _
    have h1 : ‖branchComp a w u - branchComp a w (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖
        ≤ D₀ * ‖u - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ / (eqLam a) ^ w.length := by
      refine (le_div_iff₀ hlamn).mpr ?_
      rw [mul_comm]
      exact hb
    have h2 : D₀ * ‖u - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ / (eqLam a) ^ w.length
        ≤ D₀ * ρ₂ := by
      calc D₀ * ‖u - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ / (eqLam a) ^ w.length
          ≤ D₀ * (ρ₂ * (eqLam a) ^ w.length) / (eqLam a) ^ w.length := by
            gcongr
        _ = D₀ * ρ₂ := by field_simp
    linarith [h1, h2]
  -- the composition is holomorphic on the ball used in the Schwarz lemma
  have hsubset : Metric.ball x (ρ₂ * (eqLam a) ^ w.length / 2)
      ⊆ Metric.ball (((-1 / 2 : ℝ) : ℂ), (0 : ℂ)) (ρ₂ * (eqLam a) ^ w.length) := by
    refine Metric.ball_subset_ball' ?_
    rw [dist_eq_norm]
    linarith [hxhalf]
  have hd : DifferentiableOn ℂ (branchComp a w)
      (Metric.ball x (ρ₂ * (eqLam a) ^ w.length / 2)) :=
    (hdiff w).mono hsubset
  -- the image of that ball stays in the closed ball of radius `2 D₀ ρ₂` about `F_w x`
  have hmaps : MapsTo (branchComp a w) (Metric.ball x (ρ₂ * (eqLam a) ^ w.length / 2))
      (Metric.closedBall (branchComp a w x) (2 * D₀ * ρ₂)) := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hzA : ‖z - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ ≤ ρ₂ * (eqLam a) ^ w.length := by
      have h1 : ‖z - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖
          ≤ ‖z - x‖ + ‖x - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ := by
        have h := norm_add_le (z - x) (x - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ)))
        rwa [sub_add_sub_cancel] at h
      linarith [hxhalf]
    have e1 := hdev z hzA
    have e2 := hdev x (by
      have h1 : ‖x - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ ≤ ρ₂ * (eqLam a) ^ w.length := by
        linarith [hxhalf]
      exact h1)
    calc ‖branchComp a w z - branchComp a w x‖
        ≤ ‖branchComp a w z - branchComp a w (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖
          + ‖branchComp a w x - branchComp a w (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ := by
          have h := norm_add_le
            (branchComp a w z - branchComp a w (((-1 / 2 : ℝ) : ℂ), (0 : ℂ)))
            (-(branchComp a w x - branchComp a w (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))))
          rw [norm_neg] at h
          convert h using 2 <;> ring
      _ ≤ 2 * D₀ * ρ₂ := by linarith [e1, e2]
  -- the Schwarz lemma at the centre `x`
  have hy' : y ∈ Metric.ball x (ρ₂ * (eqLam a) ^ w.length / 2) := by
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : ‖y - x‖ ≤ ‖y - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖
        + ‖x - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ := by
      have h := norm_add_le (y - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ)))
        ((((-1 / 2 : ℝ) : ℂ), (0 : ℂ)) - x)
      rw [show y - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))
            + ((((-1 / 2 : ℝ) : ℂ), (0 : ℂ)) - x) = y - x by abel,
        norm_sub_rev (((-1 / 2 : ℝ) : ℂ), (0 : ℂ)) x] at h
      exact h
    have h2 : (ρ₂ / 8) * (eqLam a) ^ w.length * 2 ≤ ρ₂ * (eqLam a) ^ w.length / 2 := by
      nlinarith [pow_pos hlam0 w.length, hρ₂0.le]
    linarith [h1, hx, hy, h2]
  have hSch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps hy'
  have hratio : 2 * D₀ * ρ₂ / (ρ₂ * (eqLam a) ^ w.length / 2)
      = 4 * D₀ / (eqLam a) ^ w.length := by
    field_simp
    ring
  have hdists : dist (branchComp a w y) (branchComp a w x)
      = ‖branchComp a w x - branchComp a w y‖ := by
    rw [dist_eq_norm, norm_sub_rev]
  calc (eqLam a) ^ w.length * ‖branchComp a w x - branchComp a w y‖
      = (eqLam a) ^ w.length * dist (branchComp a w y) (branchComp a w x) := by rw [hdists]
    _ ≤ (eqLam a) ^ w.length
          * (2 * D₀ * ρ₂ / (ρ₂ * (eqLam a) ^ w.length / 2) * dist y x) :=
        mul_le_mul_of_nonneg_left hSch (pow_nonneg hlam0.le _)
    _ = (eqLam a) ^ w.length * (4 * D₀ / (eqLam a) ^ w.length * ‖x - y‖) := by
        rw [hratio, dist_eq_norm, norm_sub_rev]
    _ = 4 * D₀ * ‖x - y‖ := by
        field_simp

end

end Work.EQ.FanTri
