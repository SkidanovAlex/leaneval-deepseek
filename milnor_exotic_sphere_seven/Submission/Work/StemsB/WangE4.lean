import Submission.Work.StemsB.wangSphereDerivation_exists

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# E4 over a sphere, corrected: exactness **and** the derivation property, with one `θ`

`Work.Serre.SerreE4` (`Submission/Work/Serre/Engine.lean`) asks for a transgression of degree
`+(m-1)` fitting two exactness spots; that statement is **false** (the Hopf fibration refutes it at
`q = 1`, see `E4_CORRECTION.md`).  In the classical indexing — the blueprint's own E4 — the
transgression has degree `-(m-1)` and the two exactness spots are

* `H^n(F) --θ_n--> H^{n+1}(F) --βS_n--> H^{n+m+1}(E)`  (`im θ_n = ker βS_n`),
* `H^{n+m}(E) --α_(n+m)--> H^{n+m}(F) --θ_n--> H^{n+1}(F)`  (`im α_(n+m) = ker θ_n`),

where `θ_n = wangCohShiftθ … n`, `α = wangCohShiftα … γ` and `βS = wangCohShiftβS … τS`.

This file proves the **complete corrected E4 over a sphere**: for a Hurewicz fibration
`p : E → SphModel b` (`b ≥ 2`) with the two fibrewise trivialities, there are identifications
`γ, τS` for which the transgression `θ` is simultaneously exact (both spots, all degrees) and a
derivation of degree `-(b-1)`:

  `θ_{n+n'+b}(a ⌣ b) = θ_n(a) ⌣ b + (-1)^{(b-1)(n+b)} · (a ⌣ θ_{n'}(b))`.

The exactness is `wangCohShiftExact₂/₃` (valid for *arbitrary* families `γ, τS`), and the derivation
is `Work.StemsB.wangSphereDerivation_exists` (the clutching-map argument of
`wangSphereDerivation_exists.lean`, built on the collar suspension class
`Work.StemsB.collarSuspensionStrong` and the collar Thom class `Work.StemsB.collar_thomClass`).
Over `ℚ` (as in `Work.Serre.ratCoh`) the same statement holds by scalar extension.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false

namespace Work.StemsB

noncomputable section

/-- **E4 over a sphere, corrected.**  For `b ≥ 2` and a Hurewicz fibration `p : E → SphModel b`
with the two fibrewise trivialities there are `γ, τS` such that the transgression
`θ = γ⁻¹ ≫ pairδ ≫ τS` is exact in the two Wang spots (in every degree) **and** is a derivation of
degree `-(b-1)`. -/
theorem wangSphereE4 (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : ContinuousMap E (Work.StemsB.SphModel b)) (hp : Work.StemsB.IsHurewiczFibration p)
    (hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b) (Work.StemsB.dOuter b))
    (d_G : ↥(Work.StemsB.sphLoopBig b))
    (hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig b) d_G) :
    ∃ (γ : ∀ k : ℕ,
        Work.Cohomology.singularCohomology ℤ k (TopCat.of (p ⁻¹' Work.StemsB.sphLoopOuter b)) ≅
        Work.Cohomology.singularCohomology ℤ k (Work.StemsB.wangCohFsp b p))
      (τS : ∀ n : ℕ,
        (Work.Cohomology.relComplex ℤ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter b)).homology
            (n + b + 1) ≅
        Work.Cohomology.singularCohomology ℤ (n + 1) (Work.StemsB.wangCohFsp b p)),
      (∀ n : ℕ, Function.Exact
          (wangCohShiftα (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter b)
            (Work.StemsB.wangCohFsp b p) b γ (n + b))
          (wangCohShiftθ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter b)
            (Work.StemsB.wangCohFsp b p) b γ τS n)) ∧
        (∀ n : ℕ, Function.Exact
          (wangCohShiftθ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter b)
            (Work.StemsB.wangCohFsp b p) b γ τS n)
          (wangCohShiftβS (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter b)
            (Work.StemsB.wangCohFsp b p) b τS n)) ∧
        Work.StemsB.WangCohShiftDerivation (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter b)
          (Work.StemsB.wangCohFsp b p) b γ τS := by
  obtain ⟨γ, τS, hder⟩ := wangSphereDerivation_exists b hb E p hp hT_O d_G hT_G
  exact ⟨γ, τS, fun n => wangCohShiftExact₂ _ _ _ _ _ _ n,
    fun n => wangCohShiftExact₃ _ _ _ _ _ _ n, hder⟩

end

end Work.StemsB
