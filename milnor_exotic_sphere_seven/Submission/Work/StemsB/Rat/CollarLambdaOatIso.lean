import Mathlib
import Submission.Work.StemsB.collarLambda_homotopy
import Submission.Work.Cohomology.homotopyEquiv
import Submission.Work.StemsB.SerreSphereStep

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The two clutching maps at the shell point are homotopy equivalences

`Work.StemsB.collarLambda_homotopy` shows that the two clutching maps at the shell point,
`collarLambdaPat : F_G → F_O` and `collarLambdaOat : F_O → F_G` (`F_G = p ⁻¹'{d_G.1}`,
`F_O = p ⁻¹'{(dOuter b).1}`), are inverse up to homotopy.  Here we draw the cohomological
consequences, which are the transport isomorphisms of the derivation argument
(`D2_PLAN_SESSION_NEXT.md` §1 Step 4):

* `rhoCoh  = collarLambdaOat^* : H^k(F_G) → H^k(F_O)` (the `ρ` of the plan);
* `lamPtCoh = collarLambdaPat^* : H^k(F_O) → H^k(F_G)` (the `λ_pt^*` of the plan);

* `collarLambdaOat_isIso`  — `ρ` is an isomorphism;
* `collarLambdaPat_comp_rho` — `ρ ∘ λ_pt^* = id` and `λ_pt^* ∘ ρ = id`.

These two identities are what turn the collar computation `collarSigma_cup` into the derivation
property of the Wang transgression: they allow the "base parts" produced by `λ_pt^*` to be removed
again by `ρ`.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.StemsB.Rat

noncomputable section

variable {E : Type} [TopologicalSpace E]

/-- The fibre over the outer point `(dOuter b).1` (the `F_O` of the derivation argument, i.e. the
`wangCohFsp` of the Wang sequence). -/
abbrev WangFO (b : ℕ) (p : C(E, SphModel b)) : TopCat :=
  TopCat.of ↥(p ⁻¹' {(dOuter b).1})

/-- The fibre over the inner point `d_G.1` (the `F_G` of the derivation argument). -/
abbrev WangFG (b : ℕ) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b)) : TopCat :=
  TopCat.of ↥(p ⁻¹' {d_G.1})

/-- The pullback `ρ = λ_O-pt^* : H^k(F_G) → H^k(F_O)`. -/
def rhoCoh (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (k : ℕ) :
    Work.Cohomology.singularCohomology ℚ k (WangFG b p d_G) ⟶
      Work.Cohomology.singularCohomology ℚ k (WangFO b p) :=
  Work.Cohomology.singularCohomologyMap ℚ (WangFO b p) (WangFG b p d_G)
    (TopCat.ofHom (collarLambdaOat b hb p d_G hT_G hT_O)) k

/-- The pullback `λ_pt^* : H^k(F_O) → H^k(F_G)`. -/
def lamPtCoh (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (k : ℕ) :
    Work.Cohomology.singularCohomology ℚ k (WangFO b p) ⟶
      Work.Cohomology.singularCohomology ℚ k (WangFG b p d_G) :=
  Work.Cohomology.singularCohomologyMap ℚ (WangFG b p d_G) (WangFO b p)
    (TopCat.ofHom (collarLambdaPat b hb p d_G hT_G hT_O)) k

/-- The two homotopies of `collarLambda_homotopy`, in the orientation of `TopCat.Homotopy`. -/
def collarLambda_homotopy' (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b))
    (d_G : ↥(sphLoopBig b)) (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) :
    (TopCat.Homotopy (TopCat.ofHom (collarLambdaOat b hb p d_G hT_G hT_O) ≫
        TopCat.ofHom (collarLambdaPat b hb p d_G hT_G hT_O)) (𝟙 (WangFO b p))) ×
    (TopCat.Homotopy (TopCat.ofHom (collarLambdaPat b hb p d_G hT_G hT_O) ≫
        TopCat.ofHom (collarLambdaOat b hb p d_G hT_G hT_O)) (𝟙 (WangFG b p d_G))) := by
  classical
  have h := collarLambda_homotopy b hb p d_G hT_G hT_O
  refine ⟨?_, ?_⟩
  · exact topCatHomotopyOf (X := WangFO b p) (Y := WangFG b p d_G)
      (f := TopCat.ofHom (collarLambdaOat b hb p d_G hT_G hT_O))
      (g := TopCat.ofHom (collarLambdaPat b hb p d_G hT_G hT_O))
      (Classical.choose h.1) (Classical.choose_spec h.1).1 (Classical.choose_spec h.1).2
  · exact topCatHomotopyOf (X := WangFG b p d_G) (Y := WangFO b p)
      (f := TopCat.ofHom (collarLambdaPat b hb p d_G hT_G hT_O))
      (g := TopCat.ofHom (collarLambdaOat b hb p d_G hT_G hT_O))
      (Classical.choose h.2) (Classical.choose_spec h.2).1 (Classical.choose_spec h.2).2

/-- **`ρ` is an isomorphism** (it is a homotopy equivalence, with inverse `λ_pt^*`). -/
theorem collarLambdaOat_isIso (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b))
    (d_G : ↥(sphLoopBig b)) (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (k : ℕ) :
    IsIso (rhoCoh b hb p d_G hT_G hT_O k) := by
  obtain ⟨h1, h2⟩ := collarLambda_homotopy' b hb p d_G hT_G hT_O
  have h := Work.Cohomology.homotopyEquiv ℚ (WangFO b p) (WangFG b p d_G)
    (TopCat.ofHom (collarLambdaOat b hb p d_G hT_G hT_O))
    (TopCat.ofHom (collarLambdaPat b hb p d_G hT_G hT_O)) h1 h2 k
  exact h

/-- **The round trips** `ρ ∘ λ_pt^* = id` and `λ_pt^* ∘ ρ = id`. -/
theorem collarLambdaPat_comp_rho (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b))
    (d_G : ↥(sphLoopBig b)) (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (k : ℕ) :
    (∀ x : Work.Cohomology.singularCohomology ℚ k (WangFO b p),
        (rhoCoh b hb p d_G hT_G hT_O k).hom ((lamPtCoh b hb p d_G hT_G hT_O k).hom x) = x)
      ∧ (∀ y : Work.Cohomology.singularCohomology ℚ k (WangFG b p d_G),
        (lamPtCoh b hb p d_G hT_G hT_O k).hom ((rhoCoh b hb p d_G hT_G hT_O k).hom y) = y) := by
  obtain ⟨h1, h2⟩ := collarLambda_homotopy' b hb p d_G hT_G hT_O
  constructor
  · have key : lamPtCoh b hb p d_G hT_G hT_O k ≫ rhoCoh b hb p d_G hT_G hT_O k =
        𝟙 (Work.Cohomology.singularCohomology ℚ k (WangFO b p)) := by
      rw [show lamPtCoh b hb p d_G hT_G hT_O k ≫ rhoCoh b hb p d_G hT_G hT_O k
          = Work.Cohomology.singularCohomologyMap ℚ (WangFO b p) (WangFO b p)
              (TopCat.ofHom (collarLambdaOat b hb p d_G hT_G hT_O) ≫
                TopCat.ofHom (collarLambdaPat b hb p d_G hT_G hT_O)) k from
        (Work.Cohomology.singularCohomologyMap_comp ℚ
          (TopCat.ofHom (collarLambdaOat b hb p d_G hT_G hT_O))
          (TopCat.ofHom (collarLambdaPat b hb p d_G hT_G hT_O)) k).symm]
      rw [Work.Cohomology.homotopyInvariance ℚ (WangFO b p) (WangFO b p) h1 k,
        Work.Cohomology.singularCohomologyMap_id]
    intro x
    have hx := congrArg (fun φ => φ.hom x) key
    simpa using hx
  · have key : rhoCoh b hb p d_G hT_G hT_O k ≫ lamPtCoh b hb p d_G hT_G hT_O k =
        𝟙 (Work.Cohomology.singularCohomology ℚ k (WangFG b p d_G)) := by
      rw [show rhoCoh b hb p d_G hT_G hT_O k ≫ lamPtCoh b hb p d_G hT_G hT_O k
          = Work.Cohomology.singularCohomologyMap ℚ (WangFG b p d_G) (WangFG b p d_G)
              (TopCat.ofHom (collarLambdaPat b hb p d_G hT_G hT_O) ≫
                TopCat.ofHom (collarLambdaOat b hb p d_G hT_G hT_O)) k from
        (Work.Cohomology.singularCohomologyMap_comp ℚ
          (TopCat.ofHom (collarLambdaPat b hb p d_G hT_G hT_O))
          (TopCat.ofHom (collarLambdaOat b hb p d_G hT_G hT_O)) k).symm]
      rw [Work.Cohomology.homotopyInvariance ℚ (WangFG b p d_G) (WangFG b p d_G) h2 k,
        Work.Cohomology.singularCohomologyMap_id]
    intro y
    have hy := congrArg (fun φ => φ.hom y) key
    simpa using hy

end

end Work.StemsB.Rat
