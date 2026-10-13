/-
Copyright: work module for the Elgindi finite-time singularity project.

# The radial Hardy inequality in the interior class (`C¹` on `(0,∞)`)

`Work.Spaces.HardyZ` proves, for a function `g` that is *real analytic* on a neighbourhood
of the closed quadrant `[0,∞) × [0,π/2]` (`Spaces.SmoothNbhd g`), the radial Hardy
inequality

  `(g z θ)² ≤ ∫_{Iz} (D_z g s θ)² w(s)² ds`,   `w(s) = (1+s)²/s²`,  `Iz = [0,∞)`,

for every `z ∈ Iz`.  The analyticity hypothesis is false for the cut-off `χ` and for the
stream functions of the bootstrap, so the `H2`-layer needs the same inequality under the
*interior* regularity that those functions do satisfy.

This file proves the one-dimensional form: `v : ℝ → ℝ` of class `C¹` on `(0,∞)`, tending to
`0` at `+∞`, with the weighted integral of `D_z v = s·v'(s)` integrable on `Iz`.  Then

  `(v z)² ≤ ∫_{Iz} (s · deriv v s)² · w(s)² ds`   for every `z > 0`.

(The endpoint `z = 0` is excluded: without continuity of `v` at `0` there is nothing to
prove there, and no consumer needs it.)

The proof is the classical one, and is the same as in `Work.Spaces.HardyZ`:

* `v z = v B - ∫_z^B v'(s) ds` for `z ≤ B` (FTC; `v` is `C¹` on the open half-line, and
  `deriv v` agrees with `derivWithin v (0,∞)` there);
* write `v'(s) = (s v'(s) w(s)) · (s/(1+s)²)` — the identity `s·w(s)·s/(1+s)² = 1`;
* Cauchy–Schwarz on `[z,B]` against `∫_z^B (s/(1+s)²)² ds ≤ 1`
  (`Spaces.hardyZ_integral_psi_sq_le_one`) and `∫_z^B (s v'(s) w(s))² ds ≤ P`
  (`Spaces.hardyZ_integral_Ioc_le_integral_Iz`);
* let `B → ∞` and use `v B → 0`.

The three auxiliary lemmas quoted above are the ones already proved in
`Submission/Work/Spaces/HardyZ.lean`; only the FTC and the continuity of `deriv v` are redone
here in the weaker interior class.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.HardyZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.HQ

theorem HardyZQ (v : ℝ → ℝ) (hcd : ContDiffOn ℝ 1 v (Set.Ioi (0 : ℝ)))
    (hdec : Filter.Tendsto v Filter.atTop (nhds 0))
    (hint : MeasureTheory.IntegrableOn
      (fun s => (s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz) :
    ∀ z ∈ Set.Ioi (0 : ℝ), (v z) ^ 2 ≤ MeasureTheory.integral
      (MeasureTheory.volume.restrict Work.Spaces.Iz)
      (fun s => (s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2) := by
  intro z hz
  have hzpos : (0 : ℝ) < z := hz
  have hz0 : 0 ≤ z := le_of_lt hzpos
  -- `v` is continuous on `(0,∞)` and `deriv v` is continuous there
  have hvcont : ContinuousOn v (Set.Ioi (0 : ℝ)) := hcd.continuousOn
  have hdvcontU : ContinuousOn (derivWithin v (Set.Ioi (0 : ℝ))) (Set.Ioi (0 : ℝ)) :=
    hcd.continuousOn_derivWithin isOpen_Ioi.uniqueDiffOn le_rfl
  have hdvcont : ContinuousOn (deriv v) (Set.Ioi (0 : ℝ)) :=
    hdvcontU.congr (fun x hx => (derivWithin_of_isOpen isOpen_Ioi hx).symm)
  have hdiff : DifferentiableOn ℝ v (Set.Ioi (0 : ℝ)) := hcd.differentiableOn one_ne_zero
  set P : ℝ := ∫ s in Work.Spaces.Iz, (s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2 with hPdef
  have hPnn : 0 ≤ P := by
    rw [hPdef]; exact integral_nonneg fun s => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- the fundamental theorem of calculus for `v` on `[z,B]`
  have hFTC : ∀ B, z ≤ B → ∫ s in z..B, deriv v s = v B - v z := by
    intro B hzB
    have hderiv : ∀ x ∈ Set.Ioo z B, HasDerivAt v (deriv v x) x := by
      intro x hx
      have hxmem : x ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith [hx.1])
      exact (hdiff.differentiableAt (isOpen_Ioi.mem_nhds hxmem)).hasDerivAt
    have hcont : ContinuousOn v (Set.Icc z B) :=
      hvcont.mono (fun x hx => Set.mem_Ioi.mpr (by linarith [hx.1]))
    have hintv : IntervalIntegrable (deriv v) volume z B := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hzB]
      exact hdvcont.mono (fun x hx => Set.mem_Ioi.mpr (by linarith [hx.1]))
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hzB hcont hderiv hintv
  -- continuity of the two Cauchy–Schwarz factors on `uIcc z B`
  have hAc : ∀ {B}, z ≤ B → ContinuousOn (fun s => s * deriv v s * Work.Spaces.w s)
      (Set.uIcc z B) := by
    intro B hzB
    rw [Set.uIcc_of_le hzB]
    refine (continuousOn_id.mul ?_).mul ?_
    · exact hdvcont.mono (fun x hx => Set.mem_Ioi.mpr (by linarith [hx.1]))
    · unfold Work.Spaces.w
      apply ContinuousOn.div
      · exact (continuousOn_const.add continuousOn_id).pow 2
      · exact continuousOn_id.pow 2
      · intro x hx
        have : 0 < x := by linarith [hx.1]
        positivity
  have hψc : ∀ {B}, z ≤ B → ContinuousOn (fun s => s / (1 + s) ^ 2) (Set.uIcc z B) := by
    intro B hzB
    rw [Set.uIcc_of_le hzB]
    apply ContinuousOn.div
    · exact continuousOn_id
    · exact (continuousOn_const.add continuousOn_id).pow 2
    · intro x hx
      have : 0 < x := by linarith [hx.1]
      positivity
  -- the key bound, for every `B ≥ z`
  have hkey : ∀ B, z ≤ B → |v z| ≤ |v B| + Real.sqrt P := by
    intro B hzB
    have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt z B hzB (hAc hzB) (hψc hzB)
    have hcongr : ∫ x in z..B, (x * deriv v x * Work.Spaces.w x) * (x / (1 + x) ^ 2)
        = ∫ x in z..B, deriv v x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hzB] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      simp only [Work.Spaces.w]
      field_simp
    have hA2le : ∫ x in z..B, (x * deriv v x * Work.Spaces.w x) ^ 2 ≤ P := by
      have h1 : ∫ x in z..B, (x * deriv v x * Work.Spaces.w x) ^ 2
          = ∫ x in z..B, (x * deriv v x) ^ 2 * (Work.Spaces.w x) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x _; ring
      rw [h1, hPdef]
      exact Work.Spaces.hardyZ_integral_Ioc_le_integral_Iz hz0 hzB hint
        (fun s _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have hψle : ∫ x in z..B, (x / (1 + x) ^ 2) ^ 2 ≤ 1 :=
      Work.Spaces.hardyZ_integral_psi_sq_le_one hz0 hzB
    have hchain : |∫ x in z..B, deriv v x| ≤ Real.sqrt P := by
      rw [← hcongr]
      calc |∫ x in z..B, (x * deriv v x * Work.Spaces.w x) * (x / (1 + x) ^ 2)|
          ≤ Real.sqrt (∫ x in z..B, (x * deriv v x * Work.Spaces.w x) ^ 2) *
              Real.sqrt (∫ x in z..B, (x / (1 + x) ^ 2) ^ 2) := hcs
        _ ≤ Real.sqrt P * Real.sqrt 1 := by
            exact mul_le_mul (Real.sqrt_le_sqrt hA2le) (Real.sqrt_le_sqrt hψle)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = Real.sqrt P := by rw [Real.sqrt_one, mul_one]
    have hchain' : |v B - v z| ≤ Real.sqrt P := by
      rw [← hFTC B hzB]; exact hchain
    have hsplit : v z = v B - (v B - v z) := by ring
    calc |v z| = |v B - (v B - v z)| := congrArg abs hsplit
      _ ≤ |v B| + |v B - v z| := abs_sub _ _
      _ ≤ |v B| + Real.sqrt P := by linarith [hchain']
  have hlim : Tendsto (fun B => |v B| + Real.sqrt P) atTop (nhds (Real.sqrt P)) := by
    have habs : Tendsto (fun B => |v B|) atTop (nhds 0) := by simpa using hdec.abs
    simpa using habs.add_const (Real.sqrt P)
  have hev : ∀ᶠ B in atTop, |v z| ≤ |v B| + Real.sqrt P :=
    (eventually_ge_atTop z).mono fun B hB => hkey B hB
  have hle : |v z| ≤ Real.sqrt P := ge_of_tendsto hlim hev
  calc (v z) ^ 2 = |v z| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt P) ^ 2 := by nlinarith [hle, abs_nonneg (v z), Real.sqrt_nonneg P]
    _ = P := Real.sq_sqrt hPnn

end Work.FTS.H2.HQ
