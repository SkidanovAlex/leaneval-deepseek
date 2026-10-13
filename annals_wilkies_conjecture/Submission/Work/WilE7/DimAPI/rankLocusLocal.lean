import Mathlib
import Submission.Work.WilE7.DimAPI.rankLocusAux
import Submission.Work.WilE9G.Sard.sardOnLevelSet

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7.DimAPI

/-- Local Sard input for the rank-deficient locus of an absolute stratum, at a point `z₀` where
the equation family `h = (a ↦ eaEval S.X.c (S.h a) ·)` is submersive: near `z₀`, the points of
`S.X.set` whose restricted projection rank is at most `r` are mapped by the `r+1`-coordinate
projection `coordMap` onto a Lebesgue-null set.

The classical argument is the local Morse–Sard theorem for the analytic (= subanalytic) map
`F := coordMap` restricted to the analytic level set `{h = h z₀}`.  `Work.WilE9G.Sard.sardOnLevelSet`
provides exactly this: it exhibits a null set `N` and a neighbourhood `U` of `z₀` such that every
level-set point at which `F` is not submersive (onto `ker (fderiv ℝ h z)`) has `F`-value in `N`.
A point `z` with `projRank S z ≤ r` has the restricted linear map
`coordLin = (· ∘ e) ∘ basePrLin` on the tangent space `ker (jac S z)` of image of dimension `≤ r`,
so it cannot surject onto `ℝ^{r+1}` (`not_surj_restrict_of_finrank_le`), i.e. it is critical; and
on `S.X.set` the equations vanish, so `h z = h z₀ = 0` and the Sard hypothesis applies. -/
theorem rankLocusLocal {n m : ℕ} (S : WilkiesDesign.E.Stratum 0 (n + m))
    (hS : WilkiesDesign.E.Stratum.Good S) (r : ℕ)
    (e : Fin (r + 1) ↪ Fin n) {z₀ : Fin (0 + (n + m)) → ℝ}
    (hz₀ : z₀ ∈ WilkiesDesign.E.SemiPf.set S.X)
    (hsurj : Function.Surjective (fderiv ℝ (fun w : Fin (0 + (n + m)) → ℝ =>
      fun a : Fin S.j => WilkiesDesign.E.eaEval S.X.c (S.h a) w) z₀)) :
    ∃ V : Set (Fin (0 + (n + m)) → ℝ), V ∈ nhds z₀ ∧ MeasureTheory.volume
      (Work.WilE7.DimAPI.coordMap n m (r + 1) e ''
        ({z ∈ WilkiesDesign.E.SemiPf.set S.X | Work.WilE7.MainDesign.projRank S z ≤ r} ∩ V)) = 0 := by
  obtain ⟨N, U, hvolN, hU, hcond⟩ :=
    Work.WilE9G.Sard.sardOnLevelSet
      (fun w : Fin (0 + (n + m)) → ℝ => fun a : Fin S.j => WilkiesDesign.E.eaEval S.X.c (S.h a) w)
      (Work.WilE7.DimAPI.coordMap n m (r + 1) e)
      (fun x => Work.WilE7.DimAPI.eaFamily_analyticAt S.X.c S.h x)
      (fun x => Work.WilE7.DimAPI.coordMap_analyticAt n m (r + 1) e x)
      z₀ hsurj
  refine ⟨U, hU, ?_⟩
  refine MeasureTheory.measure_mono_null ?_ hvolN
  rintro y ⟨z, ⟨⟨hzS, hpr⟩, hzU⟩, rfl⟩
  refine hcond z hzU ?_ ?_
  · funext a
    rw [(hS z hzS).1 a, (hS z₀ hz₀).1 a]
  · intro hbad
    apply Work.WilE7.DimAPI.not_surj_restrict_of_finrank_le
      (LinearMap.ker (Work.WilE7.MainDesign.jac S z)) (Work.WilE7.MainDesign.basePrLin n m)
      (LinearMap.funLeft ℝ ℝ e) hpr
    intro w
    obtain ⟨v, hv1, hv2⟩ := hbad w
    refine ⟨v, ?_, ?_⟩
    · rw [LinearMap.mem_ker, ← Work.WilE7.DimAPI.fderiv_eaFamily_apply_jac S z v]
      exact hv1
    · rw [Work.WilE7.DimAPI.fderiv_coordMap_apply] at hv2
      exact hv2

end Work.WilE7.DimAPI
