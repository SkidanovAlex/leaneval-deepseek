import Mathlib
import Submission.Work.StemsB.WangSphere
import Submission.Work.StemsB.WangE4Rat
import Submission.Work.StemsB.WangE4

/-!
# E4 — the Wang sequence over a sphere, with the derivation property (corrected indexing)

**The statement in `Submission/Work/Serre/Engine.lean` (degrees `q ↦ q + (m-1)`) is FALSE**; see
`Submission/Work/StemsB/E4_CORRECTION.md` for the Hopf-fibration counterexample.  The corrected
statement is the one recorded here, with the transgression indexed by its *source* degree
(`θ_n : H^{n+m}(F) → H^{n+1}(F)`, i.e. degree `-(m-1)`), which is the classical Wang sequence

`… → H^q(E) --α--> H^q(F) --θ--> H^{q-m+1}(F) --β--> H^{q+1}(E) --α--> …   (q = n + m)`.

## What this file provides

* `Work.Serre.SerreE4` — the corrected statement, as a `Prop` (the same shape as the proved
  theorem `Work.StemsB.wangSphereE4Rat` of area STEMSB, which owns route B: the two-disc/excision
  part, `Work.StemsB.wangSphereE4` (integral) and `Work.StemsB.wangSphereE4Rat` (rational));
* **`Work.Serre.serreE4 : Work.Serre.SerreE4`** — the proved statement, obtained by importing
  `Work.StemsB.wangSphereE4Rat`.

The two hypotheses `hT_O`/`hT_G` (fibrewise triviality of the fibration over the outer piece
`sphLoopOuter b` of the sphere model and over the inner cube `sphLoopBig b`) are the *local
triviality inputs* of the two-disc argument: they are what lets the collar/Thom machinery of
`Work.StemsB.SerreSphereCollar` be applied.  They are part of the standard sphere model
`Work.StemsB.SphModel` and are available for every fibration in the applications (the path–loop
fibration over a sphere is trivial over each of the two discs by `Work.StemsB.SphModel`'s
construction).

## The conclusion, unwound

Given the data, there are identifications

* `γ : H^k(E|_O) ≅ H^k(F_sp)` (`F_sp = Work.StemsB.wangCohFsp b p`, a model fibre), and
* `τS : H^{n+b+1}(E, E|_O) ≅ H^{n+1}(F_sp)`;

the transgression `θ_n := γ⁻¹ ≫ δ ≫ τS` (`δ` the connecting map of the pair `(E, E|_O)`,
`Work.StemsB.wangCohShiftθR`) then makes the Wang sequence exact in the two spots
(`Work.StemsB.wangCohShiftExact₂R/₃R`, which hold for arbitrary `γ, τS`), and it is a derivation of
degree `-(b-1)`:

`θ_{n+n'+b}(a ⌣ b) = θ_n(a) ⌣ b + (-1)^{(b-1)(n+b)} · a ⌣ θ_{n'}(b)`

(`Work.StemsB.WangCohShiftDerivationR`, supplied here by
`Work.StemsB.wangSphereDerivation_existsRat`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false

namespace Work.Serre

noncomputable section

/-- **The conclusion of E4** (corrected indexing): the Wang sequence of a Hurewicz fibration over
`S^b` (`b ≥ 2`) is exact in its two spots and its transgression is a derivation of degree
`-(b-1)`.  The hypotheses are the local triviality inputs of the two-disc argument. -/
def SerreE4Conclusion (b : ℕ) (E : Type) [TopologicalSpace E]
    (p : C(E, Work.StemsB.SphModel b))
    (hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b) (Work.StemsB.dOuter b))
    (d_G : ↥(Work.StemsB.sphLoopBig b))
    (hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig b) d_G) : Prop :=
  ∃ (γ : ∀ k : ℕ,
      Work.Cohomology.singularCohomology ℚ k (TopCat.of (p ⁻¹' Work.StemsB.sphLoopOuter b)) ≅
      Work.Cohomology.singularCohomology ℚ k (Work.StemsB.wangCohFsp b p))
    (τS : ∀ n : ℕ,
      (Work.Cohomology.relComplex ℚ (TopCat.of E)
          (p ⁻¹' Work.StemsB.sphLoopOuter b)).homology (n + b + 1) ≅
      Work.Cohomology.singularCohomology ℚ (n + 1) (Work.StemsB.wangCohFsp b p)),
    (∀ n : ℕ, Function.Exact
        (Work.StemsB.wangCohShiftαR ℚ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter b)
          (Work.StemsB.wangCohFsp b p) b γ (n + b))
        (Work.StemsB.wangCohShiftθR ℚ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter b)
          (Work.StemsB.wangCohFsp b p) b γ τS n)) ∧
      (∀ n : ℕ, Function.Exact
        (Work.StemsB.wangCohShiftθR ℚ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter b)
          (Work.StemsB.wangCohFsp b p) b γ τS n)
        (Work.StemsB.wangCohShiftβSR ℚ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter b)
          (Work.StemsB.wangCohFsp b p) b τS n)) ∧
      Work.StemsB.WangCohShiftDerivationR ℚ (TopCat.of E)
        (p ⁻¹' Work.StemsB.sphLoopOuter b) (Work.StemsB.wangCohFsp b p) b γ τS

/-- **E4 (blueprint §1, corrected — `Submission/Work/StemsB/E4_CORRECTION.md`).**  *The Wang sequence
over a sphere, with the derivation property.*  For a Hurewicz fibration `p : E → Sᵇ` (`b ≥ 2`),
there are identifications of the cohomology of the outer piece with that of the fibre and of the
relative cohomology of the pair `(E, E|_O)` with a shift of the fibre cohomology, such that the
transgression `θ = γ⁻¹ ≻ δ ≻ τS` is exact in the two Wang spots and is a derivation of degree
`-(b-1)`.  See `SerreE4Conclusion` for the conclusion and the module docstring for the indexing.

**Do not state this with `θ` of degree `+(m-1)`: that version is refuted by the Hopf fibration**
(`H⁰(S¹) = ℚ`, `H¹(S¹) = ℚ`, `H^*(S³) = ℚ` in degrees `0,3` — the exactness spots are incompatible).
-/
def SerreE4 : Prop :=
  ∀ (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, Work.StemsB.SphModel b)) (hp : Work.StemsB.IsHurewiczFibration p)
    (hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b) (Work.StemsB.dOuter b))
    (d_G : ↥(Work.StemsB.sphLoopBig b))
    (hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig b) d_G),
    SerreE4Conclusion b E p hT_O d_G hT_G

/-- **E4 is proved** — by area STEMSB's route B (`Work.StemsB.wangSphereE4`,
`Work.StemsB.wangSphereE4Rat`, `Work.StemsB.wangSphereDerivation_existsRat`), re-exported here. -/
theorem serreE4 : SerreE4 :=
  fun b hb E hE p hp hT_O d_G hT_G =>
    @Work.StemsB.wangSphereE4Rat b hb E hE p hp hT_O d_G hT_G

end

end Work.Serre
