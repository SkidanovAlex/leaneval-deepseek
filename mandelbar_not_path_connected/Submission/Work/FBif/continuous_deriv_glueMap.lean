import Mathlib
import Submission.Work.FBif.Glue
import Submission.Work.FBif.glue_derivs
import Submission.Work.FBif.antipoly_wirtinger

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Continuity of the glued map and of its Wirtinger derivatives

For a `C¹` map `F : ℂ → ℂ` the Wirtinger derivatives

```
∂F  = ½ (D F 1 - i D F i),      ∂̄F = ½ (D F 1 + i D F i)
```

are computed from the real Fréchet derivative `D F = fderiv ℝ F`; since `C¹` means that the
Fréchet derivative depends continuously on the base point, `∂F` and `∂̄F` are again continuous.
Combined with `Work.FBif.glue_derivs`, which shows that the glued map
`glueMap c q ε χ = T_c + ε · χ · q` is `C¹`, this gives
`Work.FBif.continuous_deriv_glueMap`.
-/

open scoped Topology

noncomputable section

namespace Work.FBif

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- The `∂`-Wirtinger derivative of a `C¹` map is continuous. -/
theorem continuous_dz_of_contDiff {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) :
    Continuous (fun z : ℂ => Work.MRMT.dz F z) := by
  have hd : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have h1 : Continuous (fun L : ℂ →L[ℝ] ℂ => L 1) :=
    (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous
  have hI : Continuous (fun L : ℂ →L[ℝ] ℂ => L Complex.I) :=
    (ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous
  have hc : Continuous
      (fun z : ℂ => (fderiv ℝ F z 1 - Complex.I * fderiv ℝ F z Complex.I) / 2) :=
    ((h1.comp hd).sub (continuous_const.mul (hI.comp hd))).div_const 2
  simpa [Work.MRMT.dz] using hc

/-- The `∂̄`-Wirtinger derivative of a `C¹` map is continuous. -/
theorem continuous_dzbar_of_contDiff {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) :
    Continuous (fun z : ℂ => Work.MRMT.dzbar F z) := by
  have hd : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have h1 : Continuous (fun L : ℂ →L[ℝ] ℂ => L 1) :=
    (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous
  have hI : Continuous (fun L : ℂ →L[ℝ] ℂ => L Complex.I) :=
    (ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous
  have hc : Continuous
      (fun z : ℂ => (fderiv ℝ F z 1 + Complex.I * fderiv ℝ F z Complex.I) / 2) :=
    ((h1.comp hd).add (continuous_const.mul (hI.comp hd))).div_const 2
  simpa [Work.MRMT.dzbar] using hc

theorem continuous_deriv_glueMap (c : ℂ) {q : ℂ → ℂ} (hq : Work.FBif.Antipoly q) {ε : ℝ}
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ 1 χ) :
    Continuous (Work.FBif.glueMap c q ε χ) ∧
      Continuous (fun z : ℂ => Work.MRMT.dz (Work.FBif.glueMap c q ε χ) z) ∧
      Continuous (fun z : ℂ => Work.MRMT.dzbar (Work.FBif.glueMap c q ε χ) z) := by
  obtain ⟨P, hP⟩ := hq
  obtain ⟨hdiff, -, -⟩ := glue_derivs c hP ε hχ
  exact ⟨hdiff.continuous, continuous_dz_of_contDiff hdiff, continuous_dzbar_of_contDiff hdiff⟩

end Work.FBif

end
