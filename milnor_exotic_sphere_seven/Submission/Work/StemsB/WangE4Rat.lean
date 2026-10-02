import Submission.Work.StemsB.WangSequenceShiftedR
import Submission.Work.StemsB.WangDerivationR
import Submission.Work.StemsB.wangSphereDerivation_existsRat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# E4 over a sphere, over `ℚ`: exactness **and** the derivation property

This is the `ℚ`-coefficient form of `Work.StemsB.wangSphereE4` (`WangE4.lean`): for a Hurewicz
fibration `p : E → SphModel b` (`b ≥ 2`) which is fibrewise trivial over the outer piece
`sphLoopOuter b` and over the inner cube `sphLoopBig b`, there are identifications `γ` of
`H^*(E|_O) ≅ H^*(F)` and `τS` of `H^{n+b+1}(E,E|_O) ≅ H^{n+1}(F)` such that the transgression
`θ = γ⁻¹ ≫ pairδ ≫ τS` is

* exact in the two Wang spots, in every degree (`wangCohShiftExact₂R`, `wangCohShiftExact₃R`,
  which are stated for an **arbitrary** pair `γ, τS`), and
* a derivation of degree `-(b-1)`
  (`θ_{n+n'+b}(a ⌣ b) = θ_n(a) ⌣ b + (-1)^{(b-1)(n+b)} · a ⌣ θ_{n'}(b)`).

The derivation half is `Work.StemsB.wangSphereDerivation_existsRat`, the rational counterpart of
the `ℤ` chapter `wangSphereDerivation_exists.lean` (collar Thom class + collar suspension class +
the collar transgression algebra).  This is what subproject SERRE's C2 odd step consumes.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false

namespace Work.StemsB

noncomputable section

/-- **E4 over a sphere, over `ℚ`.** -/
theorem wangSphereE4Rat (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : ContinuousMap E (Work.StemsB.SphModel b)) (hp : Work.StemsB.IsHurewiczFibration p)
    (hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b) (Work.StemsB.dOuter b))
    (d_G : ↥(Work.StemsB.sphLoopBig b))
    (hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig b) d_G) :
    ∃ (γ : ∀ k : ℕ,
        Work.Cohomology.singularCohomology ℚ k (TopCat.of (p ⁻¹' Work.StemsB.sphLoopOuter b)) ≅
        Work.Cohomology.singularCohomology ℚ k (Work.StemsB.wangCohFsp b p))
      (τS : ∀ n : ℕ,
        (Work.Cohomology.relComplex ℚ (TopCat.of E)
            (p ⁻¹' Work.StemsB.sphLoopOuter b)).homology (n + b + 1) ≅
        Work.Cohomology.singularCohomology ℚ (n + 1) (Work.StemsB.wangCohFsp b p)),
      (∀ n : ℕ, Function.Exact
          (wangCohShiftαR ℚ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter b)
            (Work.StemsB.wangCohFsp b p) b γ (n + b))
          (wangCohShiftθR ℚ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter b)
            (Work.StemsB.wangCohFsp b p) b γ τS n)) ∧
        (∀ n : ℕ, Function.Exact
          (wangCohShiftθR ℚ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter b)
            (Work.StemsB.wangCohFsp b p) b γ τS n)
          (wangCohShiftβSR ℚ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter b)
            (Work.StemsB.wangCohFsp b p) b τS n)) ∧
        Work.StemsB.WangCohShiftDerivationR ℚ (TopCat.of E)
          (p ⁻¹' Work.StemsB.sphLoopOuter b) (Work.StemsB.wangCohFsp b p) b γ τS := by
  obtain ⟨γ, τS, hder⟩ := wangSphereDerivation_existsRat b hb E p hp hT_O d_G hT_G
  exact ⟨γ, τS, fun n => wangCohShiftExact₂R ℚ _ _ _ _ _ _ n,
    fun n => wangCohShiftExact₃R ℚ _ _ _ _ _ _ n, hder⟩

end

end Work.StemsB
