import ChallengeDeps
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Submission.ScatKernelChosen
import Submission.ScatProfileExterior
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Concavity of the canonical scattering profile on `[0,R]`

`U(r) := canonicalProfile v w R r` satisfies, a.e. on `(0,R)`, the Carathéodory
equation `U'' = (v/2)·(U − id)` (`Submission.BoseGases.canonicalProfile_reg`).
Since `v ≥ 0` and the maximum principle gives `U r ≤ r` for `0 < r < R`
(`Submission.BoseGases.canonicalProfile_le_r`), the second derivative is `≤ 0`
a.e. on `(0,R)`; with `deriv U` absolutely continuous on compact subintervals of
`(0,R)` (`Submission.BoseGases.antitoneOn_deriv_of_ae_second_nonpos`) this makes
`deriv U` antitone on `(0,R)`, hence `U` concave on `[0,R]` by
`AntitoneOn.concaveOn_of_deriv` (continuity on the closed interval is
`canonicalProfile_reg`).

This is the concavity of the classical scattering profile used downstream:
`r ↦ r·ω(r) = U(r)` is concave, equivalently the secant slope `U(r)/r = ω(r)`
is non-increasing (with the right convexity conclusion, unlike mere
antitonicity of `r ↦ U(r)/r`, which allows a jump-type counterexample).
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Work.BoseFixB1B

open Filter Metric MeasureTheory Set
open scoped ContDiff Topology Real Interval

theorem canonicalProfile_concaveOn_Icc {v w : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hrad : _root_.BoseGases.IsRadial w) (hw : _root_.BoseGases.IsScatteringSolution w v) :
    ConcaveOn ℝ (Set.Icc 0 R) (Submission.BoseGases.canonicalProfile v w R) := by
  let U : ℝ → ℝ := Submission.BoseGases.canonicalProfile v w R
  let q : ℝ → ℝ := fun x => (Submission.BoseGases.radialProfile v x / 2) * (U x - x)
  obtain ⟨hU0, hcont0, hdiff0, hac0, hsec0⟩ :=
    Submission.BoseGases.canonicalProfile_reg (v := v) (w := w) (R := R)
      hR hvrad hv_supp hrad hw
  have hcont : ContinuousOn U (Set.Icc (0 : ℝ) R) := by simpa [U] using hcont0
  have hdiff : DifferentiableOn ℝ U (interior (Set.Icc (0 : ℝ) R)) := by
    rw [interior_Icc]
    intro x hx
    exact (hdiff0 x hx.1 hx.2).differentiableWithinAt
  have hanti : AntitoneOn (deriv U) (interior (Set.Icc (0 : ℝ) R)) := by
    rw [interior_Icc]
    intro x hx y hy hxy
    have hx0 : 0 < x := hx.1
    have hyR : y < R := hy.2
    have hac : AbsolutelyContinuousOnInterval (deriv U) x y := by
      simpa [U] using hac0 (a := x) (b := y) hx0 hxy hyR.le
    have hsec : ∀ᵐ t : ℝ, t ∈ Set.uIcc x y → HasDerivAt (deriv U) (q t) t := by
      filter_upwards [hsec0 (a := x) (b := y) hx0 hxy hyR.le] with t ht
      intro hmem
      simpa [q, U] using ht hmem
    have hq : ∀ᵐ t : ℝ, t ∈ Set.uIcc x y → q t ≤ 0 := by
      apply Eventually.of_forall
      intro t ht
      have htI : t ∈ Set.Icc x y := by rwa [Set.uIcc_of_le hxy] at ht
      have ht0 : 0 < t := lt_of_lt_of_le hx0 htI.1
      have htR : t < R := lt_of_le_of_lt htI.2 hyR
      have hle : U t ≤ t := by
        simpa [U] using Submission.BoseGases.canonicalProfile_le_r (v := v) (w := w) (R := R)
          hR hv_nonneg hvrad hv_supp hrad hw t ht0 htR
      have hrp : 0 ≤ Submission.BoseGases.radialProfile v t := by
        dsimp [Submission.BoseGases.radialProfile]
        exact hv_nonneg (t • Submission.BoseGases.radU0)
      dsimp [q]
      exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg hrp (by norm_num)) (sub_nonpos.mpr hle)
    have hres := Submission.BoseGases.antitoneOn_deriv_of_ae_second_nonpos hac hsec hq
    have hxmem : x ∈ Set.uIcc x y := by rw [Set.uIcc_of_le hxy]; exact ⟨le_rfl, hxy⟩
    have hymem : y ∈ Set.uIcc x y := by rw [Set.uIcc_of_le hxy]; exact ⟨hxy, le_rfl⟩
    exact hres hxmem hymem hxy
  have hmain : ConcaveOn ℝ (Set.Icc (0 : ℝ) R) U :=
    AntitoneOn.concaveOn_of_deriv (D := Set.Icc (0 : ℝ) R) (convex_Icc 0 R) hcont hdiff hanti
  simpa [U] using hmain

end Work.BoseFixB1B
