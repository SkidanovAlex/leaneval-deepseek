import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B5.lagData_start
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.collar_q1
import Submission.Work.RPB.B5.AcZero_surj
import Submission.Work.RPB.B5.chordPhase_zero_surj
import Submission.Work.RPB.B5.rho_zero_surj
import Submission.Work.RPB.B5.chart_coords_zero

/-!
# B5: the `τ = 0` slice of the assembled family covers the whole zero section

The assembled family `ℓ τ (x,t) = lagPt W Γc Ac ρ τ x t` of `Defs.lean` is, on the left half
`x ≤ 0`, the collar `levelPt (Γc τ (sig x) t) (sig x) (Ac τ (sig x) t)` for `x ≤ -√2` and the
chord chart `W τ t (rho τ x t)` for `-√2 ≤ x ≤ 0`; the right half `x > 0` is `τ_π` of the
reflected left half, `tau π (basePt τ (-x) (t-π))`.

This module proves the `start_surj` field of `LagFamily` for `ℓ`: at `τ = 0` the parametrisation
`(x,t) ↦ ℓ 0 (x,t)` is onto the whole zero section `Zsec = {p = 0}`.

## The cover

Write a target `z ∈ Zsec` as `((q₁,q₂),(0,0))`.  We cover the left half `q₁ ≤ 0` by `basePt` and
the right half `q₁ > 0` by `tau π ∘ basePt` (using `tau π ∘ tau (-π) = id`):

* **collar** (`q₁ ≤ -√2`): take `x = q₁`, so `σ = sig x = q₁²/2 - 1 ≥ 0` and
  `√(2+2σ) = -q₁`.  By `collar_q1` the collar point has `q₁`-coordinate `-√(2+2σ) = q₁` and by
  `hτ0` it has `p = 0`; the `q₂`-coordinate `Ac 0 σ t` is surjective (`AcZero_surj`), giving `t`.

* **chart** (`-√2 < q₁ ≤ 0`): take `r = arccos(-q₁/√2) ∈ (0, π/2]`, so `-√2 cos r = q₁`.  Pick
  `t` with `a 0 t r = q₂` (`chordPhase_zero_surj`), then `x ∈ (-√2,0]` with `rho 0 x t = r²`
  (`rho_zero_surj`).  By `chart_coords_zero` the chart point has `q₁ = -√2 cos r = q₁`, `q₂ =
  a 0 t r = q₂` and `p = 0`.

* **right half** (`q₁ > 0`): apply the left-half cover to the point `tau (-π) z = ((-q₁, q₂-π),
  (0,0)) ∈ Zsec` (whose first coordinate is `< 0`), obtaining `y < 0`, `s` with
  `basePt 0 y s = tau (-π) z`; then `x = -y > 0` and `t = s + π` give
  `lagPt 0 x t = tau π (basePt 0 y s) = tau π (tau (-π) z) = z`.
  (`y = 0` is impossible because `basePt 0 0 s` has `q₁ = 0` while `tau (-π) z` has `q₁ = -q₁ < 0`.)
-/

open RectangularPegProblem
open Manifold Complex Real

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- For `x ≤ -√2` the collar level `sig x = x²/2 - 1` is nonnegative. -/
private lemma sig_nonneg_of_le (x : ℝ) (hx : x ≤ -Real.sqrt 2) : 0 ≤ sig x := by
  have h2 : (2 : ℝ) ≤ x ^ 2 := by
    have h : Real.sqrt 2 ≤ -x := by linarith
    calc (2 : ℝ) = (Real.sqrt 2) ^ 2 := (Real.sq_sqrt (by norm_num)).symm
      _ ≤ (-x) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg 2) h 2
      _ = x ^ 2 := by ring
  simp only [sig]; linarith

/-- For `x ≤ -√2` we have `√(2 + 2 sig x) = -x` (because `2 + 2 sig x = x²`). -/
private lemma sqrt_two_add_two_sig (x : ℝ) (hx : x ≤ -Real.sqrt 2) :
    Real.sqrt (2 + 2 * sig x) = -x := by
  have hx0 : x ≤ 0 := by linarith [hx, Real.sqrt_nonneg 2]
  rw [show (2 + 2 * sig x) = x ^ 2 by simp only [sig]; ring, Real.sqrt_sq_eq_abs,
    abs_of_nonpos hx0]

theorem lagData_start_surj (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    ∀ z ∈ Work.RPV.Zsec, ∃ x t : ℝ,
      lagPt D.W D.Γc D.Ac D.rho 0 x t = z := by
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have hsq2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  -- the point `basePt 0 0 s` (the middle chord, `rho = π²/4`, radius `π/2`) has `q₁ = 0`
  have hbase0 : ∀ s : ℝ, (basePt D.W D.Γc D.Ac D.rho 0 0 s).1.1 = 0 := by
    intro s
    have h0not : ¬ ((0 : ℝ) ≤ -Real.sqrt 2) := by linarith
    rw [basePt, ite_eq_right h0not]
    obtain ⟨h1, -, -⟩ := chart_coords_zero CI a ha D 0 (by linarith) (le_refl 0) s
    rw [h1, D.hrho0 0 hmem0 s]
    have hpi : Real.sqrt (Real.pi ^ 2 / 4) = Real.pi / 2 := by
      rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    rw [hpi, Real.cos_pi_div_two, mul_zero]
  -- ## the left half `w.1.1 ≤ 0` is covered by `basePt`
  have hcover : ∀ w : Work.RPV.PS, w ∈ Work.RPV.Zsec → w.1.1 ≤ 0 →
      ∃ y s : ℝ, y ≤ 0 ∧ basePt D.W D.Γc D.Ac D.rho 0 y s = w := by
    intro w hw hw1
    have hw2 : w.2 = 0 := hw
    by_cases hc : w.1.1 ≤ -Real.sqrt 2
    · -- ### collar branch
      obtain ⟨t, ht⟩ := AcZero_surj CI a D (sig w.1.1) (sig_nonneg_of_le w.1.1 hc) w.1.2
      refine ⟨w.1.1, t, hw1, ?_⟩
      rw [basePt, ite_eq_left hc, collarPt]
      have hq1 := collar_q1 CI a D (sig w.1.1) (sig_nonneg_of_le w.1.1 hc) t
      have hsq := sqrt_two_add_two_sig w.1.1 hc
      have hp := D.hτ0 (sig w.1.1) (sig_nonneg_of_le w.1.1 hc) t
      refine Prod.ext (Prod.ext ?_ ?_) ?_
      · rw [hq1, hsq]; ring
      · exact ht
      · rw [hp, hw2]
    · -- ### chart branch (`-√2 < w.1.1 ≤ 0`)
      have hw1' : -Real.sqrt 2 < w.1.1 := not_le.mp hc
      set q : ℝ := -(w.1.1) / Real.sqrt 2 with hqdef
      have hq_lt1 : q < 1 := by
        rw [hqdef, div_lt_one hsq2]; linarith
      have hq_ge0 : 0 ≤ q := by
        rw [hqdef]; exact div_nonneg (by linarith) hsq2.le
      set r : ℝ := Real.arccos q with hrdef
      have hrpos : 0 < r := by rw [hrdef]; exact Real.arccos_pos.mpr hq_lt1
      have hrle : r ≤ Real.pi / 2 := by
        rw [hrdef]; exact Real.arccos_le_pi_div_two.mpr hq_ge0
      have hcosr : Real.cos r = q := by
        rw [hrdef]; exact Real.cos_arccos (by linarith) hq_lt1.le
      obtain ⟨t, ht⟩ := chordPhase_zero_surj CI a ha r hrpos hrle w.1.2
      have hr2pos : 0 < r ^ 2 := by positivity
      have hr2le : r ^ 2 ≤ Real.pi ^ 2 / 4 := by
        calc r ^ 2 ≤ (Real.pi / 2) ^ 2 := pow_le_pow_left₀ hrpos.le hrle 2
          _ = Real.pi ^ 2 / 4 := by ring
      obtain ⟨x, hx1, hx0, hxrho⟩ := rho_zero_surj CI a D t (r ^ 2) hr2pos hr2le
      refine ⟨x, t, hx0, ?_⟩
      rw [basePt, ite_eq_right (not_le.mpr hx1)]
      obtain ⟨hq1c, hq2c, hpc⟩ := chart_coords_zero CI a ha D x hx1 hx0 t
      have hsqrt_r : Real.sqrt (D.rho 0 x t) = r := by rw [hxrho, Real.sqrt_sq hrpos.le]
      refine Prod.ext (Prod.ext ?_ ?_) ?_
      · rw [hq1c, hsqrt_r, hcosr, hqdef]
        field_simp
      · rw [hq2c, hsqrt_r]; exact ht
      · rw [hpc, hw2]
  -- ## assembly
  intro z hz
  have hz2 : z.2 = 0 := hz
  by_cases h : z.1.1 ≤ 0
  · -- left half: `lagPt = basePt`
    obtain ⟨y, s, hy, hys⟩ := hcover z hz h
    exact ⟨y, s, by rw [lagPt, ite_eq_left hy]; exact hys⟩
  · -- right half: cover `tau (-π) z` and apply `tau π`
    have hpos : 0 < z.1.1 := not_le.mp h
    have hz21 : z.2.1 = 0 := by simpa using congrArg Prod.fst hz2
    have hz22 : z.2.2 = 0 := by simpa using congrArg Prod.snd hz2
    have hz'1 : (Work.RPV.tau (-Real.pi) z).1.1 = -z.1.1 := by
      simp only [Work.RPV.tau, Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi]
      ring
    have hz'amem : Work.RPV.tau (-Real.pi) z ∈ Work.RPV.Zsec := by
      show (Work.RPV.tau (-Real.pi) z).2 = 0
      simp [Work.RPV.tau, hz21, hz22]
    have hz'le : (Work.RPV.tau (-Real.pi) z).1.1 ≤ 0 := by rw [hz'1]; linarith
    obtain ⟨y, s, hy, hys⟩ := hcover (Work.RPV.tau (-Real.pi) z) hz'amem hz'le
    have hyne : y ≠ 0 := by
      intro hy0
      have h1 : (basePt D.W D.Γc D.Ac D.rho 0 0 s).1.1 =
          (Work.RPV.tau (-Real.pi) z).1.1 := by rw [hy0] at hys; rw [hys]
      rw [hbase0 s, hz'1] at h1
      linarith
    have hyneg : y < 0 := by
      rcases lt_or_eq_of_le hy with hlt | heq
      · exact hlt
      · exact absurd heq hyne
    refine ⟨-y, s + Real.pi, ?_⟩
    have hxpos : 0 < -y := by linarith
    rw [lagPt, ite_eq_right (not_le.mpr hxpos)]
    simp only [neg_neg, add_sub_cancel_right]
    rw [hys, Work.RPV.tau_add]
    rw [show Real.pi + -Real.pi = 0 by ring, Work.RPV.tau_zero]

end Work.RPB.B5
