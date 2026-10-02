import Mathlib
import Submission.Work.Stems.wangOddStep
import Submission.Work.StemsB.WangE4Rat
import Submission.Work.Serre.gysinCupIsoReduction
import Submission.Work.Stems.Engine.DualVanishing
import Submission.Work.StemsB.serreExactSphereProp
import Submission.Work.StemsB.SerreSphereStep

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The odd step of the `C2` layer, geometric form

`Work.Stems.isZero_wangTotal` (`Submission/Work/Stems/wangOddStep.lean`) turns the exactness of the
Wang sequence into the vanishing of the total space, from the vanishing of the fibre.  This file
supplies the geometric data: for a Hurewicz fibration `p : E → Sᵇ` which is fibrewise trivial over
the two pieces of the standard cover of `Sᵇ` (`b ≥ 2`), the pair `(E, p⁻¹(sphLoopOuter b))` and the
two identifications `γ`, `τS` exist by `Work.StemsB.wangSphereE4Rat` (the corrected E4, which is
where the proof of the Wang sequence lives).  The result is

> if the fibre `F = p ⁻¹{∞}` has vanishing rational cohomology in degrees `0 < t ≤ T`, `t ≠ b-1`,
> then `H^t(E;ℚ) = 0` for `b+1 ≤ t ≤ min T (2b-2)`.

For the odd step of `C2` one applies this to the projection `Eₙ → Sᵇ` of the homotopy fibre of the
bottom cell `Sᵇ → K(ℤ,b)` (`b` odd), whose fibre is `ΩK(ℤ,b) ≅ K(ℤ,b-1)`, a rational sphere below
degree `2b-2` by the even step of `C2`; then `Eₙ` is rationally acyclic in the range and
`Work.Serre.SerreE3a` makes `K(ℤ,b)` a rational sphere.  See `Submission/Work/Stems/C2ODD_PLAN.md`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Stems

noncomputable section

/-- **The Wang odd step over a sphere.**  For a Hurewicz fibration `p : E → Sᵇ` (`b ≥ 2`) which is
fibrewise trivial over the outer piece and over the inner cube of `Work.StemsB.SphModel b`, if the
fibre over `∞` has vanishing rational cohomology in degrees `0 < t ≤ T`, `t ≠ b-1`, then the total
space has vanishing rational cohomology in degrees `b+1 ≤ t ≤ min T (2b-2)`. -/
theorem isZero_ratCoh_sphereFibration (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, Work.StemsB.SphModel b)) (hp : Work.StemsB.IsHurewiczFibration p)
    (hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b) (Work.StemsB.dOuter b))
    (d_G : ↥(Work.StemsB.sphLoopBig b))
    (hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig b) d_G) (T : ℕ)
    (hfib : ∀ t : ℕ, 0 < t → t ≤ T → t ≠ b - 1 →
      Subsingleton (Work.Cohomology.singularCohomology ℚ t (Work.StemsB.wangCohFsp b p))) :
    ∀ t : ℕ, b + 1 ≤ t → t ≤ T → t ≤ 2 * b - 2 →
      Subsingleton (Work.Cohomology.singularCohomology ℚ t (TopCat.of E)) := by
  obtain ⟨γ, τS, _hE₂, _hE₃, _hder⟩ := Work.StemsB.wangSphereE4Rat b hb E p hp hT_O d_G hT_G
  exact isZero_wangTotal (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter b)
    (Work.StemsB.wangCohFsp b p) b T hb γ τS hfib

/-- **The homological form of the Wang odd step over a sphere.**  `Work.Serre.ratH` (the homology
of the singular chains) is the coefficient system in which the `C2` layer is stated
(`Work.Stems.CoverAcyclic`), so the odd step is recorded in both forms: the vanishing of the
fibre's rational *homology* in degrees `0 < t ≤ T`, `t ≠ b-1` gives the vanishing of the total
space's rational homology in degrees `b+1 ≤ t ≤ min T (2b-2)`.

The two transfers are the field universal coefficient theorem over `ℚ`
(`Work.Stems.isZero_ratH_of_isZero_ratCoh`, `Work.Serre.isZero_ratCoh_of_isZero_ratH_dup`). -/
theorem isZero_ratH_sphereFibration (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, Work.StemsB.SphModel b)) (hp : Work.StemsB.IsHurewiczFibration p)
    (hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b) (Work.StemsB.dOuter b))
    (d_G : ↥(Work.StemsB.sphLoopBig b))
    (hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig b) d_G) (T : ℕ)
    (hfib : ∀ t : ℕ, 0 < t → t ≤ T → t ≠ b - 1 →
      IsZero (Work.Serre.ratH (Work.StemsB.wangCohFsp b p) t)) :
    ∀ t : ℕ, b + 1 ≤ t → t ≤ T → t ≤ 2 * b - 2 →
      IsZero (Work.Serre.ratH (TopCat.of E) t) := by
  have hfib' : ∀ t : ℕ, 0 < t → t ≤ T → t ≠ b - 1 →
      Subsingleton (Work.Cohomology.singularCohomology ℚ t (Work.StemsB.wangCohFsp b p)) :=
    fun t h1 h2 h3 =>
      show Subsingleton (Work.Serre.ratCoh (Work.StemsB.wangCohFsp b p) t) from
        ModuleCat.isZero_iff_subsingleton.mp (Work.Serre.isZero_ratCoh_of_isZero_ratH_dup (hfib t h1 h2 h3))
  intro t ht1 htT ht2
  have hc := isZero_ratCoh_sphereFibration b hb E p hp hT_O d_G hT_G T hfib' t ht1 htT ht2
  exact Work.Stems.isZero_ratH_of_isZero_ratCoh (X := TopCat.of E) (k := t)
    (show IsZero (Work.Serre.ratCoh (TopCat.of E) t) from
      ModuleCat.isZero_iff_subsingleton.mpr hc)

/-! ## The two fibrewise trivialities are automatic for a Hurewicz fibration

`Work.StemsB.wangSphereE4Rat` (the corrected E4) asks for the fibration to be fibrewise trivial over
the two pieces of the standard cover of `Work.StemsB.SphModel b`.  For a Hurewicz fibration those
two hypotheses are *theorems*: both pieces are contractible, and a fibration over a contractible set
is fibrewise trivial (`Work.StemsB.fibrewiseTrivial_of_contraction`), with the explicit contractions
`Work.StemsB.sphLoopOuterContr` and `Work.StemsB.serreSphere_contract_big`.  This removes the two
hypotheses from the statements below. -/

/-- **The outer piece is fibrewise trivial** for a Hurewicz fibration over `SphModel b`. -/
theorem fibrewiseTrivial_sphLoopOuter {b : ℕ} (E : Type) [TopologicalSpace E]
    (p : C(E, Work.StemsB.SphModel b)) (hp : Work.StemsB.IsHurewiczFibration p) :
    Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b) (Work.StemsB.dOuter b) :=
  Work.StemsB.fibrewiseTrivial_of_contraction p hp (Work.StemsB.sphLoopOuter b)
    (Work.StemsB.dOuter b) (Work.StemsB.sphLoopOuterContr b)
    (fun w => Work.StemsB.sphLoopOuterContr_zero b w)
    (fun w => by
      rw [show Work.StemsB.dOuter b
          = (⟨OnePoint.infty, Or.inl rfl⟩ : ↥(Work.StemsB.sphLoopOuter b)) from Subtype.ext rfl]
      exact Work.StemsB.sphLoopOuterContr_one b w)
    (fun t => by
      rw [show Work.StemsB.dOuter b
          = (⟨OnePoint.infty, Or.inl rfl⟩ : ↥(Work.StemsB.sphLoopOuter b)) from Subtype.ext rfl]
      exact Work.StemsB.sphLoopOuterContr_fixes b t)

/-- **The inner cube is fibrewise trivial** for a Hurewicz fibration over `SphModel b`, `b ≥ 1`. -/
theorem fibrewiseTrivial_sphLoopBig {b : ℕ} (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, Work.StemsB.SphModel b)) (hp : Work.StemsB.IsHurewiczFibration p) :
    ∃ d_G : ↥(Work.StemsB.sphLoopBig b), Work.StemsB.FibrewiseTrivial p
      (Work.StemsB.sphLoopBig b) d_G := by
  have hshell : Work.StemsB.sphShellPt b ∈ Work.StemsB.sphLoopBig b :=
    (Work.StemsB.serreSphere_sets b hb).2.2.2.2
  obtain ⟨c, hc0, hc1, hcb⟩ := Work.StemsB.serreSphere_contract_big b hb hshell
  exact ⟨⟨Work.StemsB.sphShellPt b, hshell⟩,
    Work.StemsB.fibrewiseTrivial_of_contraction p hp (Work.StemsB.sphLoopBig b)
      ⟨Work.StemsB.sphShellPt b, hshell⟩ c hc0 hc1 hcb⟩

/-- **The Wang odd step over a sphere, with the fibrewise trivialities discharged.**  For a
Hurewicz fibration `p : E → Sᵇ` (`b ≥ 2`), if the fibre over `∞` has vanishing rational cohomology
in degrees `0 < t ≤ T`, `t ≠ b-1`, then the total space has vanishing rational cohomology in degrees
`b+1 ≤ t ≤ min T (2b-2)`. -/
theorem isZero_ratCoh_sphereFibration' (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, Work.StemsB.SphModel b)) (hp : Work.StemsB.IsHurewiczFibration p) (T : ℕ)
    (hfib : ∀ t : ℕ, 0 < t → t ≤ T → t ≠ b - 1 →
      Subsingleton (Work.Cohomology.singularCohomology ℚ t (Work.StemsB.wangCohFsp b p))) :
    ∀ t : ℕ, b + 1 ≤ t → t ≤ T → t ≤ 2 * b - 2 →
      Subsingleton (Work.Cohomology.singularCohomology ℚ t (TopCat.of E)) := by
  obtain ⟨d_G, hT_G⟩ := fibrewiseTrivial_sphLoopBig (by omega : 1 ≤ b) E p hp
  exact isZero_ratCoh_sphereFibration b hb E p hp (fibrewiseTrivial_sphLoopOuter E p hp) d_G hT_G
    T hfib

/-- **The same in rational homology.** -/
theorem isZero_ratH_sphereFibration' (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, Work.StemsB.SphModel b)) (hp : Work.StemsB.IsHurewiczFibration p) (T : ℕ)
    (hfib : ∀ t : ℕ, 0 < t → t ≤ T → t ≠ b - 1 →
      Subsingleton ↥(Work.Serre.ratH (Work.StemsB.wangCohFsp b p) t)) :
    ∀ t : ℕ, b + 1 ≤ t → t ≤ T → t ≤ 2 * b - 2 →
      Subsingleton ↥(Work.Serre.ratH (TopCat.of E) t) := by
  intro t ht1 htT ht2
  have hfib' : ∀ t : ℕ, 0 < t → t ≤ T → t ≠ b - 1 →
      Subsingleton (Work.Cohomology.singularCohomology ℚ t (Work.StemsB.wangCohFsp b p)) :=
    fun t h1 h2 h3 =>
      show Subsingleton (Work.Serre.ratCoh (Work.StemsB.wangCohFsp b p) t) from
        ModuleCat.isZero_iff_subsingleton.mp
          (Work.Serre.isZero_ratCoh_of_isZero_ratH_dup
            (ModuleCat.isZero_iff_subsingleton.mpr (hfib t h1 h2 h3)))
  have hc := isZero_ratCoh_sphereFibration' b hb E p hp T hfib' t ht1 htT ht2
  exact ModuleCat.isZero_iff_subsingleton.mp (Work.Stems.isZero_ratH_of_isZero_ratCoh
    (X := TopCat.of E) (k := t)
    (show IsZero (Work.Serre.ratCoh (TopCat.of E) t) from
      ModuleCat.isZero_iff_subsingleton.mpr hc))

end

end Work.Stems

