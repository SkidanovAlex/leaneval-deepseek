import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.PhiStar.phiAj_smooth2
import Submission.Work.FTS.EllExist.Honesty.Pieces.primitive_contDiffOn
import Submission.Work.FTS.EllExist.Honesty.Pieces.tailIntegral_contDiffOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

open MeasureTheory Set Filter
open scoped Real Topology ContDiff

set_option autoImplicit false

/-!
# `ModeRescaledSmooth`

`radGreen α m c` is the explicit mode-`m` radial Green function

`radGreen α m c z = 1/(α(4m+5))·( z^{s⁻}∫₀^z c t t^{s⁺-1} dt + z^{s⁺}∫_{Ioi z} c t t^{-s⁺-1} dt )`

with `s⁺ = 2m/α`, `s⁻ = -(2m+5)/α`.  For the source `c = φ_α = phiA α` (a rational function,
smooth on `(0,∞)` away from `-1`) we show that `(z+1)/z · radGreen α m φ_α` is `C^n` on `(0,∞)`
for **every** `n` and **every** real `α` — no positivity of `α` is needed, because the two pieces
are smooth in all regimes:

* the `0..z` piece is a primitive of the `C^n` function `t ↦ c t · t^{s⁺-1}` on `(0,∞)`
  (`EllExist.Honesty.Pieces.primitive_contDiffOn`, which handles the case where that function is
  not integrable near `0`: then Lean's interval integral is the junk constant `0`);
* the `Ioi z` piece is the tail integral of the `C^n` function `t ↦ c t · t^{-s⁺-1}`; the same
  dichotomy occurs at `∞` and is handled by `tailIntegral_contDiffOn_all` below
  (integrability on one tail is equivalent to integrability on every tail, by continuity of the
  integrand on `(0,∞)` and compactness of the difference of two tails);
* the prefactors `z^{s^±}` and the outer factor `(z+1)/z` are `C^∞` on `(0,∞)`.

Nothing about the analytic content of `radGreen` (that it solves the mode equation) is used here.
-/

/-- **Dichotomy for tails.**  For a function continuous on `(0,∞)`, either every tail `Ioi z`
(`z > 0`) carries an integrable function, or none does.  (Two tails differ by a compact set on
which the function is bounded.) -/
theorem integrableOn_Ioi_dichotomy_of_continuousOn {k : ℝ → ℝ}
    (hk : ContinuousOn k (Set.Ioi 0)) :
    (∀ z : ℝ, 0 < z → IntegrableOn k (Set.Ioi z)) ∨
      (∀ z : ℝ, 0 < z → ¬ IntegrableOn k (Set.Ioi z)) := by
  by_cases h1 : IntegrableOn k (Set.Ioi (1 : ℝ))
  · left
    intro z hz
    rcases le_or_gt 1 z with hle | hlt
    · exact h1.mono_set (Ioi_subset_Ioi hle)
    · rw [← Ioc_union_Ioi_eq_Ioi (le_of_lt hlt)]
      refine (IntegrableOn.mono_set ?_ Ioc_subset_Icc_self).union h1
      exact ContinuousOn.integrableOn_Icc (hk.mono fun x hx => lt_of_lt_of_le hz hx.1)
  · right
    intro z hz hzint
    refine h1 ?_
    rcases le_or_gt z 1 with hle | hlt
    · exact hzint.mono_set (Ioi_subset_Ioi hle)
    · rw [← Ioc_union_Ioi_eq_Ioi (le_of_lt hlt)]
      refine (IntegrableOn.mono_set ?_ Ioc_subset_Icc_self).union hzint
      exact ContinuousOn.integrableOn_Icc (hk.mono fun x hx => lt_of_lt_of_le zero_lt_one hx.1)

/-- **Smoothness of a tail integral, junk case included.**  The tail integral
`z ↦ ∫ t in Ioi z, f t` of a function of class `C^n` on `(0,∞)` is again of class `C^n` on
`(0,∞)`; if `f` is integrable on no tail then each integral is the junk constant `0`. -/
theorem tailIntegral_contDiffOn_all (n : ℕ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ n f (Set.Ioi 0)) :
    ContDiffOn ℝ n (fun z => ∫ t in Set.Ioi z, f t) (Set.Ioi 0) := by
  rcases integrableOn_Ioi_dichotomy_of_continuousOn hf.continuousOn with hall | hnone
  · exact Work.FTS.EllExist.Honesty.Pieces.tailIntegral_contDiffOn n hf (hall 1 zero_lt_one)
  · refine (contDiffOn_const (c := (0 : ℝ)) (s := Set.Ioi 0)).congr (fun z hz => ?_)
    exact MeasureTheory.integral_undef (hnone z hz)

/-- **Smoothness of the radial Green function.**  For every real `α`, every `m : ℕ` and every
`n : ℕ`, `radGreen α m c` is `C^n` on `(0,∞)` as soon as `c` is. -/
theorem contDiffOn_radGreen (α : ℝ) (m : ℕ) (n : ℕ) {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ n c (Set.Ioi 0)) :
    ContDiffOn ℝ n (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z) (Set.Ioi 0) := by
  have hf1 : ContDiffOn ℝ n (fun t : ℝ => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioi 0) :=
    hc.mul (contDiffOn_id.rpow_const_of_ne (p := (2 * (m : ℝ) + 5) / α - 1)
      (fun x hx => ne_of_gt hx))
  have hf2 : ContDiffOn ℝ n (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 0) :=
    hc.mul (contDiffOn_id.rpow_const_of_ne (p := -(2 * (m : ℝ) / α) - 1)
      (fun x hx => ne_of_gt hx))
  have hA : ContDiffOn ℝ n
      (fun z => ∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioi 0) := Work.FTS.EllExist.Honesty.Pieces.primitive_contDiffOn n hf1
  have hB : ContDiffOn ℝ n
      (fun z => ∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 0) :=
    tailIntegral_contDiffOn_all n hf2
  have hza : ContDiffOn ℝ n (fun z : ℝ => z ^ (-(2 * (m : ℝ) + 5) / α)) (Set.Ioi 0) :=
    contDiffOn_id.rpow_const_of_ne (p := -(2 * (m : ℝ) + 5) / α) (fun x hx => ne_of_gt hx)
  have hzb : ContDiffOn ℝ n (fun z : ℝ => z ^ (2 * (m : ℝ) / α)) (Set.Ioi 0) :=
    contDiffOn_id.rpow_const_of_ne (p := 2 * (m : ℝ) / α) (fun x hx => ne_of_gt hx)
  have hmain : ContDiffOn ℝ n (fun z : ℝ => 1 / (α * (4 * (m : ℝ) + 5)) *
      (z ^ (-(2 * (m : ℝ) + 5) / α)
          * (∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
        + z ^ (2 * (m : ℝ) / α)
          * (∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1)))) (Set.Ioi 0) :=
    contDiffOn_const.mul ((hza.mul hA).add (hzb.mul hB))
  exact hmain.congr (fun z _ => rfl)

theorem ModeRescaledSmooth (α : ℝ) (m : ℕ) (n : ℕ) :
    ContDiffOn ℝ n (fun z => (z + 1) / z
      * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z) (Set.Ioi 0) := by
  have hc : ContDiffOn ℝ n (Work.FTS.VocabO.phiA α) (Set.Ioi 0) :=
    fun z hz => (Work.FTS.PhiStar.contDiffAt_phiA_of α (n : ℕ∞ω) hz).contDiffWithinAt
  have hG : ContDiffOn ℝ n
      (fun z => Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z)
      (Set.Ioi 0) :=
    contDiffOn_radGreen α m n hc
  have hfac : ContDiffOn ℝ n (fun z : ℝ => (z + 1) / z) (Set.Ioi 0) :=
    (contDiffOn_id.add contDiffOn_const).div contDiffOn_id (fun z hz => ne_of_gt hz)
  exact hfac.mul hG

end Work.FTS.PhiStar.FlatWAux
