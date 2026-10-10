import Mathlib
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.ASLink
import Submission.Work.MotK.TGen.ChartMaps
import Submission.Work.MotK.TGen.ChartIso
import Submission.Work.MotK.AwayAlgEquivOfComp
import Submission.Work.MotV5.ASChart.Stereo
import Submission.Work.MotV5.ASChart.kleinPAS_stereoPt
import Submission.Work.MotV5.ASChart.kleinSecAS_stereoPt
import Submission.Work.MotV5.ASChart.ASCore
import Submission.Work.MotV5.ASChart.ASChartLocalDefs
import Submission.Work.MotV5.ASChart.PsiL_bwVecAS2L
import Submission.Work.MotV5.ASChart.PhiL_fwVecAS2L
import Submission.Work.MotV5.ASChart.PsiL_sdualAS2L
import Submission.Work.MotV5.ASChart.PhiL_sAS2L_sq
import Submission.Work.MotV5.ASChart.ASChartIsoL
import Submission.Work.MotV5.ASChart.ASChartIsoL2

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotV5.ASChart.chartIsoAS2` — the chart isomorphism of the corrected AS chart

The two chart maps of the corrected AS (characteristic-`5`) affine chart of the Crauder–Katz link
(`Submission/Work/MotAS/GUIDE_CENSUSAS2.md`),

* `PhiL = χ^*` with `χ = π_{pAS0} ∘ R^AS` and
* `PsiL = f^*` with `f = P^AS ∘ y^AS(pAS0, ·)`,

are mutually inverse up to units of the two chart localisations, so

  `A[1/FdivAS2] ≃ₐ[K] A[1/GdivAS2]`   (`A = K[X₀,X₁,X₂]`),

which is the `Φ`-component of the census `Work.MotAS.CensusAS2`.

The proof is assembled in the sibling files: `ASChartLocalDefs` (the chart data and the two chart
rings, with the definitions repeated locally so that they are definitionally equal to the
`Work.MotAS` ones), `ASCore` (the AS link identities, root-free), the four value lemmas
(`PhiL_fwVecAS2L`, `PsiL_bwVecAS2L`, `PhiL_sAS2L_sq`, `PsiL_sdualAS2L`), `ASChartIsoL` (the unit
conditions, the two descent maps and the two composites on the generators) and `ASChartIsoL2`
(`chartIsoL`).  Here `chartIsoL` is instantiated at the Klein data `D`, transported along the
definitional equalities `FdivAS2L = Work.MotAS.FdivAS2`, `GdivAS2L = Work.MotAS.GdivAS2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.MotV5.ASChart

/-- The characteristic hypothesis, pushed to `RatFunc 𝕜` and then to the chart ring. -/
theorem chartIsoAS2_charFive (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] :
    (5 : MvPolynomial (Fin 3) (RatFunc 𝕜)) = 0 := by
  have h5K : (5 : RatFunc 𝕜) = 0 := by
    have h : ((5 : ℕ) : RatFunc 𝕜) = 0 := by
      rw [← map_natCast (algebraMap 𝕜 (RatFunc 𝕜)) 5, CharP.cast_eq_zero 𝕜 5, map_zero]
    simpa using h
  have h : ((5 : ℕ) : MvPolynomial (Fin 3) (RatFunc 𝕜)) = 0 := by
    rw [← map_natCast (algebraMap (RatFunc 𝕜) (MvPolynomial (Fin 3) (RatFunc 𝕜))) 5,
      show ((5 : ℕ) : RatFunc 𝕜) = 0 from h5K, map_zero]
  simpa using h

/-- `linAS2L (aK D) (bK D)` is a unit under `ASGood D`. -/
theorem chartIsoAS2_linUnit (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) :
    IsUnit (linAS2L (Work.MotAS.aK D) (Work.MotAS.bK D)) := by
  have h5 : (5 : MvPolynomial (Fin 3) (RatFunc 𝕜)) = 0 := chartIsoAS2_charFive 𝕜
  have hΛ : Work.MotAS.aK D ^ 2 - Work.MotAS.aK D * Work.MotAS.bK D - Work.MotAS.bK D ^ 2
      ≠ 0 := Work.MotAS.aK_sq_sub_ne D hD
  have hfac : (MvPolynomial.C (Work.MotAS.aK D) ^ 2 - MvPolynomial.C (Work.MotAS.aK D)
        * MvPolynomial.C (Work.MotAS.bK D) - MvPolynomial.C (Work.MotAS.bK D) ^ 2 :
        MvPolynomial (Fin 3) (RatFunc 𝕜))
      = MvPolynomial.C (Work.MotAS.aK D ^ 2 - Work.MotAS.aK D * Work.MotAS.bK D
          - Work.MotAS.bK D ^ 2) := by
    rw [map_sub, map_sub, map_mul, map_pow, map_pow]
  have h6 : ((6 : ℕ) : MvPolynomial (Fin 3) (RatFunc 𝕜)) = 1 := by
    have h : ((5 : ℕ) : MvPolynomial (Fin 3) (RatFunc 𝕜)) + 1 = 1 := by
      rw [show ((5 : ℕ) : MvPolynomial (Fin 3) (RatFunc 𝕜)) = 0 from h5, zero_add]
    rw [show (6 : ℕ) = 5 + 1 from rfl, Nat.cast_add, Nat.cast_one]
    exact h
  have h2 : IsUnit (-(2 : MvPolynomial (Fin 3) (RatFunc 𝕜))) := by
    refine ⟨⟨-(2), -(3), ?_, ?_⟩, rfl⟩
    · rw [show -(2 : MvPolynomial (Fin 3) (RatFunc 𝕜)) * -(3) = ((6 : ℕ) : MvPolynomial (Fin 3) (RatFunc 𝕜))
        from by norm_num, h6]
    · rw [show -(3 : MvPolynomial (Fin 3) (RatFunc 𝕜)) * -(2) = ((6 : ℕ) : MvPolynomial (Fin 3) (RatFunc 𝕜))
        from by norm_num, h6]
  rw [linAS2L_eq_const, hfac]
  exact h2.mul (Work.MotAS.isUnit_C hΛ)

theorem chartIsoAS2 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) :
    Nonempty (Localization.Away
        (Work.MotAS.FdivAS2 (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜)) ≃ₐ[RatFunc 𝕜]
      Localization.Away
        (Work.MotAS.GdivAS2 (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜))) := by
  have h5 : (5 : MvPolynomial (Fin 3) (RatFunc 𝕜)) = 0 := chartIsoAS2_charFive 𝕜
  have hlin : IsUnit (linAS2L (Work.MotAS.aK D) (Work.MotAS.bK D)) := chartIsoAS2_linUnit 𝕜 D hD
  exact chartIsoL h5 (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜) hlin

end Work.MotV5.ASChart
