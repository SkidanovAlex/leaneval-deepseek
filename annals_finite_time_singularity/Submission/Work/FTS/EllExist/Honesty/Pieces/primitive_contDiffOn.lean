import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.PhiStar.Radial.intervalIntegrable_of_Ioi_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty.Pieces

/-- If `f` is integrable on `Ioc 0 z` with `z > 0` and continuous on `(0,∞)`, then it is
integrable on `Ioo 0 1`.  (This is the contradiction step of the `¬ P` branch: the compact
piece `Icc z 1` is harmless.) -/
theorem integrableOn_Ioo_zero_one_of_Ioc {f : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hcont : ContinuousOn f (Set.Ioi 0)) (hIoc : MeasureTheory.IntegrableOn f (Set.Ioc 0 z)) :
    MeasureTheory.IntegrableOn f (Set.Ioo 0 1) := by
  rcases lt_or_ge z 1 with hz1 | hz1
  · -- `z < 1`: `Ioo 0 1 ⊆ Ioc 0 z ∪ Ioo z 1`, and `f` is continuous on the compact `Icc z 1`.
    have hB : MeasureTheory.IntegrableOn f (Set.Ioo z 1) :=
      ((hcont.mono (fun x hx => lt_of_lt_of_le hz hx.1)).integrableOn_Icc).mono_set
        Set.Ioo_subset_Icc_self
    refine (hIoc.union hB).mono_set ?_
    intro x hx
    rcases le_or_gt x z with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨h, hx.2⟩
  · -- `1 ≤ z`: `Ioo 0 1 ⊆ Ioc 0 z`.
    exact hIoc.mono_set (fun x hx => ⟨hx.1, le_trans (le_of_lt hx.2) hz1⟩)

/-- **Primitive of a `C^n` function on `(0,∞)` is `C^n` there** (Lean's junk-value convention for the interval integral included).  This is the `0..z` half of the case-split needed by `Work.FTS.EllExist.Honesty.radGreen_contDiffOn`.

ROUTE.  Put `F z = ∫ t in (0:ℝ)..z, f t` and `P := MeasureTheory.IntegrableOn f (Set.Ioo 0 1)`.

* **Case `P`.**  For every `z > 0`, `IntervalIntegrable f volume 0 z`: `f` is continuous on `(0,∞)` and `Ioc 0 z ⊆ Ioo 0 1 ∪ Icc (min z 1) z`, the second piece compact (this is exactly
  `Work.FTS.PhiStar.Radial.intervalIntegrable_of_Ioi_Ioo`, import it).  Then
  `intervalIntegral.integral_hasDerivAt_right` gives `HasDerivAt F (f z) z` for every `z ∈ Ioi 0`,
  so `deriv F = f` pointwise there.  With `ContDiffOn.congr` this gives
  `ContDiffOn ℝ n (deriv F) (Ioi 0)`, and `contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi` plus
  `DifferentiableOn` gives `ContDiffOn ℝ (n+1) F (Ioi 0)` (the conjunct
  `↑n = ⊤ → AnalyticOn …` is vacuous since `↑n ≠ ⊤ : ℕ∞ω`); downgrade with `ContDiffOn.of_le`
  (`Nat.le_succ n`).

* **Case `¬ P`.**  Show `¬ MeasureTheory.IntegrableOn f (Set.Ioc 0 z)` for every `z > 0`: if
  `Ioc 0 z` were integrable then so would be `Ioo 0 (min z 1)` (subset) and `Ioo (min z 1) 1`
  (subset of the compact `Icc (min z 1) 1`, on which `f` is continuous since `min z 1 > 0`), and
  `Ioo 0 1 = Ioo 0 (min z 1) ∪ Ioo (min z 1) 1`, so
  `IntegrableOn.union` would give `P`.  Hence `F z = ∫ t in Ioc 0 z, f t = 0` by
  `intervalIntegral.integral_of_le` and `MeasureTheory.integral_undef`, i.e. `F = 0` on `Ioi 0`,
  and `contDiffOn_congr` with the constant `0` finishes.

Do NOT attempt to derive `P` from `hf`: it is false (`f t = t ^ (-30)`). -/
theorem primitive_contDiffOn (n : ℕ) {f : ℝ → ℝ} (hf : ContDiffOn ℝ n f (Set.Ioi 0)) :
    ContDiffOn ℝ n (fun z => ∫ t in (0 : ℝ)..z, f t) (Set.Ioi 0) := by
  by_cases hP : MeasureTheory.IntegrableOn f (Set.Ioo 0 1)
  · -- Case `P`: `F` is a genuine primitive of the continuous `f` on `(0,∞)`.
    have hcont : ContinuousOn f (Set.Ioi 0) := hf.continuousOn
    have hii : ∀ z ∈ Set.Ioi 0, IntervalIntegrable f MeasureTheory.volume 0 z :=
      fun z hz => Work.FTS.PhiStar.Radial.intervalIntegrable_of_Ioi_Ioo hz hcont hP
    have hderiv : ∀ z ∈ Set.Ioi 0, HasDerivAt (fun z => ∫ t in (0 : ℝ)..z, f t) (f z) z := by
      intro z hz
      refine intervalIntegral.integral_hasDerivAt_right (hii z hz) ?_
        (hcont.continuousAt (isOpen_Ioi.mem_nhds hz))
      exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hcont z hz
    have hderiv_eq : ∀ z ∈ Set.Ioi 0, deriv (fun z => ∫ t in (0 : ℝ)..z, f t) z = f z :=
      fun z hz => (hderiv z hz).deriv
    have hcd : ContDiffOn ℝ n (deriv (fun z => ∫ t in (0 : ℝ)..z, f t)) (Set.Ioi 0) :=
      hf.congr hderiv_eq
    have hdiff : DifferentiableOn ℝ (fun z => ∫ t in (0 : ℝ)..z, f t) (Set.Ioi 0) :=
      fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt
    have htop : ¬ ((n : WithTop ℕ∞) = ⊤) := ne_of_lt (WithTop.coe_lt_top (n : ℕ∞))
    have hsucc : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) (fun z => ∫ t in (0 : ℝ)..z, f t)
        (Set.Ioi 0) :=
      (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ)
        (f := fun z => ∫ t in (0 : ℝ)..z, f t) (s := Set.Ioi 0) (n := (n : WithTop ℕ∞))
        isOpen_Ioi).mpr ⟨hdiff, fun h => absurd h htop, hcd⟩
    exact ContDiffOn.of_le hsucc (le_add_of_nonneg_right zero_le_one)
  · -- Case `¬ P`: the interval integral is the junk constant `0` on `(0,∞)`.
    have hnoIoc : ∀ z ∈ Set.Ioi 0, ¬ MeasureTheory.IntegrableOn f (Set.Ioc 0 z) :=
      fun z hz hIoc => hP (integrableOn_Ioo_zero_one_of_Ioc hz hf.continuousOn hIoc)
    have hF0 : ∀ z ∈ Set.Ioi 0, (∫ t in (0 : ℝ)..z, f t) = 0 := by
      intro z hz
      have hni : ¬ MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Set.Ioc 0 z)) := by
        simpa only [MeasureTheory.IntegrableOn] using hnoIoc z hz
      rw [intervalIntegral.integral_of_le hz.le, MeasureTheory.integral_undef hni]
    exact (contDiffOn_const (c := (0 : ℝ))).congr hF0

end Work.FTS.EllExist.Honesty.Pieces
