import Mathlib
import Submission.Work.LerayHirsch.FibreZetaPow
import Submission.Work.LerayHirsch.LH
import Submission.Work.LerayHirsch.FibreRestrict

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The Leray–Hirsch map of the trivial bundle pulled back to a fibre

Let `Z : VectorBundleCore ℂ B (ℂ^m) ι` and let `ψ : ProjFibre Z b ⟶ P(ε^m)` be the composite

`ψ = projUniv m ∘ projClassFibre Z b`,

the identification of the fibre of `P(Z) → B` over `b` with `P(ε^m) = P(ℂ^m × PUnit)`
(`Work.LerayHirsch.projUniv` is the canonical homeomorphism of
`Work.LerayHirsch.nonempty_homeo_projSpace_trivial`, `Work.LerayHirsch.projClassFibre` the
"class of the fibre coordinate" of `Work.LerayHirsch.fibreMap_bijective`).

The theorem of this module is that the composite of the Leray–Hirsch decomposition map of the
*trivial* bundle `ε^m` over the point base `PUnit` (which is a bijection by hypothesis,
`LerayHirschFull (trivCore m)` — this is `KunnethCP` at a point) with the pullback `ψ^*` is again a
bijection:

`∏_i H^{2(k-i)}(pt;ℤ) ≅ H^{2k}(P(ε^m);ℤ) ≅ H^{2k}(ℂP^{m-1};ℤ)`.

Mathematically the content is exactly "the restrictions `1, ζ, …, ζ^{m-1}` of the Leray–Hirsch
basis of `H^*(P(ε^m))` form a basis of the fibre `H^*(ℂP^{m-1})`" (`Submission/Work/LerayHirsch/
README.md` §0.5): `ψ` is a homeomorphism, so it induces an isomorphism on cohomology, and the
hypothesis says that the left-hand map is an isomorphism.

The proof formalises this: `ψ` is the composite of the two homeomorphisms

* `Work.LerayHirsch.fibreHomeo` — `ProjFibre Z b ≃ₜ ℂP^{m-1}`, whose underlying map is
  `projClassFibre Z b` (`projClass_fibreMap` / `fibreMap_projClass` are the two round trips, and
  `continuous_projClass_subtype` / `continuous_fibreMap` their continuity);
* `Work.LerayHirsch.projUnivHomeo` — `ℂP^{m-1} ≃ₜ P(ε^m)`, whose underlying map is `projUniv m`,
  with inverse `projClass (trivCore m)` (`projClass_fibreMap` / `fibreMap_projClass` for the trivial
  bundle over the point base, and `continuous_projClass_trivCore` for the continuity of the
  inverse);

so that `CohMap ψ` is a composite of bijections
(`Work.LerayHirsch.bijective_CohMap_of_homeomorph`), and a composite of bijections is a bijection.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open CategoryTheory

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-! ## Continuity of `projClass` for the trivial bundle over a point -/

/-- The map `projClass (ε^m) : P(ε^m) → ℂP^{m-1}` ("the class of the fibre coordinate") is
continuous.

The fibre of `P(ε^m) → PUnit` over the unique point is all of `P(ε^m)`, so this is the restriction
to a fibre of `projClass`, whose continuity is `Work.LerayHirsch.continuous_projClass_subtype`,
composed with the (bijective) inclusion of the fibre. -/
theorem continuous_projClass_trivCore (m : ℕ) : Continuous (projClass (trivCore m)) := by
  have h : projClass (trivCore m) =
      (fun x : ProjFibre (trivCore m) PUnit.unit => projClass (trivCore m) x.1) ∘
        (fun y : ProjSpace (trivCore m) =>
          (⟨y, Subsingleton.elim ((projMap (trivCore m)) y) PUnit.unit⟩ :
            ProjFibre (trivCore m) PUnit.unit)) := rfl
  rw [h]
  exact (continuous_projClass_subtype (trivCore m) PUnit.unit).comp
    (Continuous.subtype_mk continuous_id _)

/-! ## The two homeomorphisms whose composite is `ψ` -/

/-- **`ℂP^{m-1} ≃ₜ P(ε^m)`**, with underlying map the canonical identification
`Work.LerayHirsch.projUniv m` and inverse `projClass (trivCore m)`: the two round trips are
`Work.LerayHirsch.projClass_fibreMap` and `Work.LerayHirsch.fibreMap_projClass` for the trivial
bundle over the point base (where the fibre condition is vacuous), the continuity of the inverse is
`Work.LerayHirsch.continuous_projClass_trivCore`. -/
def projUnivHomeo (m : ℕ) : ℙ ℂ (EuclideanSpace ℂ (Fin m)) ≃ₜ ProjSpace (trivCore m) where
  toFun := projUniv m
  invFun := projClass (trivCore m)
  left_inv := fun x => projClass_fibreMap (trivCore m) PUnit.unit x
  right_inv := fun y => by
    have h := fibreMap_projClass (trivCore m) PUnit.unit y (Subsingleton.elim _ _)
    exact congrArg Subtype.val h
  continuous_toFun := (projUniv m).continuous
  continuous_invFun := continuous_projClass_trivCore m

/-- **The fibre `ProjFibre Z b ≃ₜ ℂP^{m-1}`**, with underlying map
`Work.LerayHirsch.projClassFibre Z b` and inverse `fibreMap Z b`.  The two round trips are
`Work.LerayHirsch.projClass_fibreMap` and `Work.LerayHirsch.fibreMap_projClass`, and the continuity
of the two maps is `Work.LerayHirsch.continuous_projClass_subtype` (unfolded definition of
`projClassFibre`) and `Work.LerayHirsch.continuous_fibreMap`. -/
def fibreHomeo (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    ProjFibre Z b ≃ₜ ℙ ℂ (EuclideanSpace ℂ (Fin m)) where
  toFun := projClassFibre Z b
  invFun := fibreMap Z b
  left_inv := fun x => by
    have h := fibreMap_projClass Z b x.1 x.2
    simpa using h
  right_inv := fun y => projClass_fibreMap Z b y
  continuous_toFun := (projClassFibre Z b).continuous
  continuous_invFun := continuous_fibreMap Z b

/-! ## The statement -/

theorem bijective_lhMap_fibre_of_trivCore {m : ℕ}
    (h : Work.LerayHirsch.LerayHirschFull (Work.LerayHirsch.trivCore m))
    {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) (k : ℕ) :
    Function.Bijective
      (fun xf : (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * (k - (i : ℕ))) PUnit =>
        (CohMap ((Work.LerayHirsch.projUniv m).comp (Work.LerayHirsch.projClassFibre Z b))
            ℤ (2 * k)).hom
          (Work.LerayHirsch.lhMap (Work.LerayHirsch.trivCore m) k xf)) := by
  -- the pullback along `ψ = projUniv ∘ projClassFibre` is bijective, being the pullback along a
  -- composite of homeomorphisms
  have hψ : Function.Bijective
      (CohMap ((projUniv m).comp (projClassFibre Z b)) ℤ (2 * k)).hom := by
    rw [Work.Thom.CohMap_comp (projClassFibre Z b) (projUniv m) ℤ (2 * k)]
    rw [ModuleCat.hom_comp]
    have hcoe : (↑(fibreHomeo Z b) : C(ProjFibre Z b, ℙ ℂ (EuclideanSpace ℂ (Fin m))))
        = projClassFibre Z b := ContinuousMap.ext (fun x => rfl)
    have huniv : (↑(projUnivHomeo m) : C(ℙ ℂ (EuclideanSpace ℂ (Fin m)), ProjSpace (trivCore m)))
        = projUniv m := ContinuousMap.ext (fun x => rfl)
    rw [← hcoe, ← huniv]
    exact (bijective_CohMap_of_homeomorph (fibreHomeo Z b) (2 * k)).comp
      (bijective_CohMap_of_homeomorph (projUnivHomeo m) (2 * k))
  -- and `lhMap (ε^m) k` is bijective by the Leray–Hirsch hypothesis
  exact hψ.comp (h.1 k)

end

end Work.LerayHirsch
