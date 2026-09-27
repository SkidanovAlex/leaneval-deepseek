import Mathlib
import Submission.Work.Geo.Radial.RadialDefs
import Submission.Work.Geo.Radial.radRho_continuous
import Submission.Work.Geo.Radial.radRho_facts

/-!
# Continuity of the sup-norm radial push `radPush`

`radPush ε R S s x = (radStretch ε R S s (radRho x) / radRho x) • x` is continuous
on `unitInterval × ℝⁿ`.

Away from the origin `radRho x ≠ 0`, so `radPush` is a composite of continuous maps:
`(s, x) ↦ radStretch ε R S s (radRho x) / radRho x` (continuous by `ContinuousAt.div`,
since the denominator `radRho x` does not vanish) followed by the continuous scalar
multiplication.  At the origin the quotient `radStretch ε R S s (radRho x) / radRho x`
is bounded (it lies in `[1, R / ε]`), so `‖radPush ε R S s x‖ ≤ (R / ε) ‖x‖` and
continuity follows from a squeeze.
-/

open Set Metric
open scoped Topology

namespace Work.Geo.Radial

/-- The sup-norm radius of a nonzero point is positive. -/
theorem radRho_pos_of_ne_zero {n : ℕ} [NeZero n] {x : PL.E n} (hx : x ≠ 0) :
    0 < radRho x :=
  lt_of_le_of_ne ((radRho_facts (n := n)).1 x)
    (Ne.symm fun h => hx (((radRho_facts (n := n)).2.2.1 x).mp h))

/-- The radial push shrinks distances at most by the factor `R / ε`: for `s ∈ [0,1]`,
`‖radPush ε R S s x‖ ≤ (R / ε) ‖x‖`.  (The scaling factor of `x` is
`radStretch ε R S s (radRho x) / radRho x`, which lies in `[1, R / ε]`.) -/
theorem norm_radPush_le {n : ℕ} [NeZero n] {ε R S s : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hεS : ε < S) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (x : PL.E n) :
    ‖radPush ε R S s x‖ ≤ (R / ε) * ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [radPush]
  · have hr : 0 < radRho x := radRho_pos_of_ne_zero hx
    set c := radStretch ε R S s (radRho x) / radRho x with hc
    have hkey : radPush ε R S s x = c • x := rfl
    rw [hkey, norm_smul, Real.norm_eq_abs]
    have hc1 : 1 ≤ c := by
      rw [hc, one_le_div hr]
      exact radStretch_ge_self hs0 hεR.le
    have hc2 : c ≤ R / ε := by
      rw [hc, div_le_iff₀ hr]
      exact radStretch_le_mul hε hεR.le hεS hs0 hs1 hr.le
    have habs : |c| ≤ R / ε := by
      rw [abs_of_nonneg (by linarith)]
      exact hc2
    exact mul_le_mul_of_nonneg_right habs (norm_nonneg x)

theorem radPush_continuous {n : ℕ} [NeZero n] {ε R S : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hRS : R < S) :
    Continuous fun p : unitInterval × PL.E n => radPush ε R S (p.1 : ℝ) p.2 := by
  have hεS : ε < S := by linarith
  have hρz : ∀ x : PL.E n, radRho x = 0 ↔ x = 0 := (radRho_facts (n := n)).2.2.1
  rw [continuous_iff_continuousAt]
  rintro ⟨s0, x0⟩
  by_cases hx : x0 = 0
  · -- At the origin `radPush ε R S s 0 = 0`; a global norm bound gives the squeeze.
    rw [hx, ContinuousAt]
    have hval : radPush ε R S (s0 : ℝ) (0 : PL.E n) = 0 := by simp [radPush]
    rw [hval, tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (g := fun p : unitInterval × PL.E n => (R / ε) * ‖p.2‖)
      (fun p => norm_nonneg _) ?_ ?_
    · intro p
      exact norm_radPush_le hε hεR hεS p.1.2.1 p.1.2.2 p.2
    · have hcont : Continuous fun p : unitInterval × PL.E n => (R / ε) * ‖p.2‖ :=
        continuous_const.mul continuous_snd.norm
      have := hcont.tendsto (s0, (0 : PL.E n))
      simpa using this
  · -- Away from the origin `radPush` is literally a quotient of continuous functions.
    have hρ : radRho x0 ≠ 0 := fun h => hx ((hρz x0).mp h)
    have hnum : ContinuousAt (fun p : unitInterval × PL.E n =>
        radStretch ε R S (p.1 : ℝ) (radRho p.2) / radRho p.2) (s0, x0) := by
      refine ContinuousAt.div ?_ ?_ hρ
      · have hg : ContinuousAt (fun p : unitInterval × PL.E n =>
            ((p.1 : ℝ), radRho p.2)) (s0, x0) :=
          (continuous_subtype_val.comp continuous_fst).continuousAt |>.prodMk
            ((radRho_continuous (n := n)).comp continuous_snd).continuousAt
        exact (radStretch_continuous ε R S).continuousAt.comp hg
      · exact ((radRho_continuous (n := n)).comp continuous_snd).continuousAt
    have hmain := hnum.smul (continuous_snd.continuousAt (x := (s0, x0)))
    have hfun : ((fun p : unitInterval × PL.E n =>
        radStretch ε R S (p.1 : ℝ) (radRho p.2) / radRho p.2) •
        (Prod.snd : unitInterval × PL.E n → PL.E n)) =
        (fun p : unitInterval × PL.E n => radPush ε R S (p.1 : ℝ) p.2) := rfl
    rw [hfun] at hmain
    exact hmain

end Work.Geo.Radial
