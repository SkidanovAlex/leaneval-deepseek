import Mathlib
import Submission.Work.StemsB.collarSigmaDefs
import Submission.Work.Cohomology.PairSequence
import Submission.Work.StemsB.collarSuspensionClass

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The splitting of the collar cohomology along the suspension class

For the collar pair `Q = ↥(sphLoopBig b) × Y`, `C = sphLoopCollarProd b Y` (`b ≥ 1`, `Y` an
arbitrary space), the long exact sequence of the pair degenerates
(`Work.StemsB.collarRestr_injective`, `Work.StemsB.serreSphere_collar_delta_surjective`): in every
degree

  `0 → H^n(Q) --i^*--> H^n(C) --δ--> H^{n+1}(Q,C) → 0`

is short exact.  With the suspension class `s ∈ H^{b-1}(C)` of
`Work.StemsB.collarSuspensionClass` (transgressing to a Thom class `τ`) this file records the
**splitting**:

  `x - π^*(Σ x) ⌣ s ∈ im i^*                                                       (collarSplit)`

where `Σ = collarSigma` is the transgression coefficient map, i.e. every class of `H^{m+b}(C)` is
the sum of a class coming from `Q` and a multiple `π^*(Σ x) ⌣ s` of the suspension class.  This is
the object called "the splitting" in `D2_PLAN.md` §2 item 3.

The file contains the two steps of the *assembly*:

* `collarDelta_ker` — the exactness of the pair at `H^{m+b}(C)` (`ker δ = im i^*`), a direct
  consequence of `Work.Cohomology.pair_exact₃`;
* `collarSplit_of_delta` — the splitting follows from the single **`δ`-computation**
  `δ (π^*(Σ x) ⌣ s) = δ x` (equivalently `= collarRelEq (δ x)`), which is where the one-sided
  derivation `Work.Sph3Disc.pairDelta_mixedCup_general` and the multiplicativity of the projection
  enter.  That computation is the hand-off; everything else is here.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.StemsB

noncomputable section

variable {Y : Type} [TopologicalSpace Y]

/-- **The exactness of the collar pair at `H^{m+b}(C)`**: the kernel of the connecting
homomorphism `collarDelta` is the range of the restriction `collarRestr`. -/
theorem collarDelta_ker (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y] (m : ℕ) :
    LinearMap.ker (collarDelta (Y := Y) b m)
      = LinearMap.range (collarRestr (Y := Y) b (m + b)) := by
  have h := ShortComplex.Exact.moduleCat_range_eq_ker
    (Work.Cohomology.pair_exact₃ ℤ (TopCat.of (↥(sphLoopBig b) × Y))
      (sphLoopCollarProd b Y) (m + b))
  rw [show collarDelta (Y := Y) b m
        = (Work.Cohomology.pairδ ℤ (TopCat.of (↥(sphLoopBig b) × Y))
            (sphLoopCollarProd b Y) (m + b)).hom from rfl]
  rw [show collarRestr (Y := Y) b (m + b)
        = (HomologicalComplex.homologyMap (Work.Cohomology.restr ℤ
            (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)) (m + b)).hom from rfl]
  exact h.symm

/-- **The splitting follows from the `δ`-computation.**  If `δ (π^*(Σ x) ⌣ s) = δ x`, then
`x - π^*(Σ x) ⌣ s` lies in the image of the restriction, i.e. `collarSplit` holds. -/
theorem collarSplit_of_delta (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℤ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ)
    (s : Work.Cohomology.singularCohomology ℤ (b - 1) (TopCat.of ↥(sphLoopCollarProd b Y)))
    (m : ℕ)
    (x : (Work.Cohomology.singularCochainComplex ℤ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (m + b))
    (h : collarDelta (Y := Y) b m (collarSPart b hb (Y := Y) τ hτ s m x)
      = collarDelta (Y := Y) b m x) :
    ∃ a : (Work.Cohomology.singularCochainComplex ℤ
        (TopCat.of (↥(sphLoopBig b) × Y))).homology (m + b),
      x - collarSPart b hb (Y := Y) τ hτ s m x = collarRestr (Y := Y) b (m + b) a := by
  have hmem : x - collarSPart b hb (Y := Y) τ hτ s m x
      ∈ LinearMap.ker (collarDelta (Y := Y) b m) := by
    show collarDelta (Y := Y) b m
      ((x - collarSPart b hb (Y := Y) τ hτ s m x) :
        (Work.Cohomology.singularCochainComplex ℤ
          (TopCat.of ↥(sphLoopCollarProd b Y))).homology (m + b)) = 0
    rw [map_sub, h, sub_self]
  rw [collarDelta_ker b hb Y m] at hmem
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a, ha.symm⟩


/-- **The transgression condition** of the suspension class: the connecting homomorphism of the
collar pair sends `s` to the Thom class `τ`. -/
def CollarTransgresses (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (s : (Work.Cohomology.singularCochainComplex ℤ
        (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1))
    (τ : Work.Thom.RelCoh ℤ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) : Prop :=
  (Work.Cohomology.pairδ ℤ (TopCat.of (↥(sphLoopBig b) × Y))
      (sphLoopCollarProd b Y) (b - 1)).hom s
    = (eqToHom (congrArg (fun t => (Work.Cohomology.relComplex ℤ
        (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)).homology t)
        (by omega : b - 1 + 1 = b)).symm) τ

/-- `Work.StemsB.collarSuspensionClass`, phrased with `CollarTransgresses`. -/
theorem collarSuspensionClass' (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y] :
    ∃ (s : (Work.Cohomology.singularCochainComplex ℤ
          (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1))
      (τ : Work.Thom.RelCoh ℤ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)),
      CollarThom (Y := Y) b τ ∧ CollarTransgresses (Y := Y) b hb s τ := by
  obtain ⟨s, τ, hτ, hs⟩ := collarSuspensionClass b hb Y
  exact ⟨s, τ, hτ, hs⟩

end

end Work.StemsB
