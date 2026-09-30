import Mathlib
import Submission.Work.Pi6.EFACTS.Basic
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The Wang data over the sphere model for the cover `E = S³⟨3⟩`

This is a direct instantiation of the library's corrected `E4` over a sphere
(`Work.StemsB.wangSphereE4`) for the transported projection `proj g3 : E → SphModel 3` and the two
fibrewise trivialities of `Work.Pi6.EFACTS.Basic`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.Pi6.EFACTS

noncomputable section

/-- **The Wang data of the cover.**  For a Postnikov section `g3 : S³ → P₃` there are
identifications `γ` (of the cohomology of the outer piece with that of the fibre) and `τS` of the
relative cohomology with the fibre, such that the resulting transgression

`θ_n = γ⁻¹ ≫ pairδ ≫ τS_n : H^{n+3}(fib g3) → H^{n+1}(fib g3)`

fits the two exactness spots of the Wang sequence **and** is a derivation of degree `-2` (in the
shifted form of `Work.StemsB.WangCohShiftDerivation`). -/
theorem wangData {P3 : Type} [TopologicalSpace P3] (g3 : C(S3, P3)) :
    ∃ (γ : ∀ k : ℕ,
        Work.Cohomology.singularCohomology ℤ k
            (TopCat.of ((proj g3) ⁻¹' Work.StemsB.sphLoopOuter 3)) ≅
          Work.Cohomology.singularCohomology ℤ k (Work.StemsB.wangCohFsp 3 (proj g3)))
      (τS : ∀ n : ℕ,
        (Work.Cohomology.relComplex ℤ (TopCat.of (Ecov g3))
            ((proj g3) ⁻¹' Work.StemsB.sphLoopOuter 3)).homology (n + 3 + 1) ≅
          Work.Cohomology.singularCohomology ℤ (n + 1) (Work.StemsB.wangCohFsp 3 (proj g3))),
      (∀ n : ℕ, Function.Exact
        (Work.StemsB.wangCohShiftα (TopCat.of (Ecov g3))
          ((proj g3) ⁻¹' Work.StemsB.sphLoopOuter 3) (Work.StemsB.wangCohFsp 3 (proj g3)) 3 γ
          (n + 3))
        (Work.StemsB.wangCohShiftθ (TopCat.of (Ecov g3))
          ((proj g3) ⁻¹' Work.StemsB.sphLoopOuter 3) (Work.StemsB.wangCohFsp 3 (proj g3)) 3 γ τS
          n)) ∧
      (∀ n : ℕ, Function.Exact
        (Work.StemsB.wangCohShiftθ (TopCat.of (Ecov g3))
          ((proj g3) ⁻¹' Work.StemsB.sphLoopOuter 3) (Work.StemsB.wangCohFsp 3 (proj g3)) 3 γ τS
          n)
        (Work.StemsB.wangCohShiftβS (TopCat.of (Ecov g3))
          ((proj g3) ⁻¹' Work.StemsB.sphLoopOuter 3) (Work.StemsB.wangCohFsp 3 (proj g3)) 3 τS
          n)) ∧
      Work.StemsB.WangCohShiftDerivation (TopCat.of (Ecov g3))
        ((proj g3) ⁻¹' Work.StemsB.sphLoopOuter 3) (Work.StemsB.wangCohFsp 3 (proj g3)) 3 γ τS :=
  Work.StemsB.wangSphereE4 3 (by norm_num) (Ecov g3) (proj g3) (isHurewiczFibration_proj g3)
    (fibrewiseTrivial_proj_outer g3) shellPt (fibrewiseTrivial_proj_big g3)

end

end Work.Pi6.EFACTS
