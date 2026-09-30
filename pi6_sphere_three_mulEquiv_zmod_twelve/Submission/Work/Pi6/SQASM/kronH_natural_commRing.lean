import Mathlib
import Submission.Work.Cohomology.kronH_natural
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.kronH_bijective_field
import Submission.Work.Cohomology.Pullback
import Submission.Work.Cohomology.Singular
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Naturality of the Kronecker pairing, coefficients in an arbitrary commutative ring

`Submission/Work/Cohomology/kronH_natural.lean` proves the naturality of the Kronecker pairing
`⟨α, f_* c⟩ = ⟨f^* α, c⟩` for integral coefficients.  That proof only ever uses the *computation
rule* `kronH_apply` of the pairing (evaluation of a cocycle on a cycle), which is available for an
arbitrary coefficient ring: everything in `kronecker_descent.lean` is stated for `[CommRing R]`.
The two auxiliary lemmas that were stated over `ℤ` are restated here over a general `CommRing R`,
and the naturality proof is reproduced verbatim.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQASM

noncomputable section

open Work.Cohomology

/-- **The computation rule for the Kronecker pairing on cycles**, coefficients in `CommRing R`. -/
lemma kronH_cyc_apply_commRing (R : Type) [CommRing R] (X : SSet) (n : ℕ)
    (w : (cochainC R X).cycles n) (v : (chainC R X).cycles n) :
    kronH R X n ((cochainC R X).homologyπ n w) ((chainC R X).homologyπ n v) =
      cochainOfCycle R X n w ((chainC R X).iCycles n v) := by
  rw [← cohomologyClassOf_eq_homologyπ R X n w]
  exact kronH_apply R X ((cochainC R X).iCycles n w) (cochainDiff_iCycles R X n w) v

/-- The transpose of the chain map sends the underlying cochain of a cycle to the underlying
cochain of the image cycle, coefficients in `CommRing R`. -/
lemma cochainOfCycle_cyclesMapS_commRing (R : Type) [CommRing R] (X Y : TopCat) (f : X ⟶ Y)
    (n : ℕ) (w : (cochainC R (TopCat.toSSet.obj Y)).cycles n) :
    cochainOfCycle R (TopCat.toSSet.obj X) n
        ((HomologicalComplex.cyclesMap (dualChainMapS R X Y f) n).hom w)
      = (cochainPullbackHomS R X Y f n).hom
          (cochainOfCycle R (TopCat.toSSet.obj Y) n w) := by
  exact congrArg (fun (g : (cochainC R (TopCat.toSSet.obj Y)).cycles n ⟶
      (cochainC R (TopCat.toSSet.obj X)).X n) => g.hom w)
    (HomologicalComplex.cyclesMap_i (dualChainMapS R X Y f) n)

/-- The pointwise form of `cochainOfCycle_cyclesMapS_commRing`, in the form needed for the
naturality of the Kronecker pairing. -/
lemma cochainOfCycle_cyclesMapS_apply_commRing (R : Type) [CommRing R] (X Y : TopCat)
    (f : X ⟶ Y) (n : ℕ) (w : (cochainC R (TopCat.toSSet.obj Y)).cycles n)
    (x : (chainC R (TopCat.toSSet.obj X)).X n) :
    cochainOfCycle R (TopCat.toSSet.obj X) n
        ((HomologicalComplex.cyclesMap (dualChainMapS R X Y f) n).hom w) x
      = cochainOfCycle R (TopCat.toSSet.obj Y) n w (((chainMapS R X Y f).f n).hom x) := by
  have h := LinearMap.congr_fun (cochainOfCycle_cyclesMapS_commRing R X Y f n w) x
  exact h.trans (cochainPullbackHomS_apply R X Y f n
    (cochainOfCycle R (TopCat.toSSet.obj Y) n w) x)

/-- **Naturality of the Kronecker pairing over a commutative ring**: for a continuous map
`f : X ⟶ Y`, a cohomology class `α ∈ Hⁿ(Y;R)` and a homology class `c ∈ Hₙ(X;R)`,

  `⟨α, f_* c⟩ = ⟨f^* α, c⟩`. -/
theorem kronH_natural_commRing (R : Type) [CommRing R] (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (α : (Work.Cohomology.singularCochainComplex R Y).homology n)
    (c : (Work.Cohomology.singularChains R X).homology n) :
    Work.Cohomology.kronH R (TopCat.toSSet.obj Y) n α
        ((HomologicalComplex.homologyMap (Work.Cohomology.chainMap R X Y f) n) c)
      = Work.Cohomology.kronH R (TopCat.toSSet.obj X) n
          ((Work.Cohomology.singularCohomologyMap R X Y f n) α) c := by
  change kronH R (TopCat.toSSet.obj Y) n α
      (HomologicalComplex.homologyMap (chainMapS R X Y f) n c)
    = kronH R (TopCat.toSSet.obj X) n
      (HomologicalComplex.homologyMap (dualChainMapS R X Y f) n α) c
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((cochainC R (TopCat.toSSet.obj Y)).homologyπ n)).mp inferInstance α
  obtain ⟨v, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((chainC R (TopCat.toSSet.obj X)).homologyπ n)).mp inferInstance c
  have hA : (HomologicalComplex.homologyMap (chainMapS R X Y f) n)
      ((chainC R (TopCat.toSSet.obj X)).homologyπ n v)
      = (chainC R (TopCat.toSSet.obj Y)).homologyπ n
          ((HomologicalComplex.cyclesMap (chainMapS R X Y f) n).hom v) :=
    homologyMap_homologyπ_apply (chainMapS R X Y f) n v
  have hB : (HomologicalComplex.homologyMap (dualChainMapS R X Y f) n)
      ((cochainC R (TopCat.toSSet.obj Y)).homologyπ n w)
      = (cochainC R (TopCat.toSSet.obj X)).homologyπ n
          ((HomologicalComplex.cyclesMap (dualChainMapS R X Y f) n).hom w) :=
    homologyMap_homologyπ_apply (dualChainMapS R X Y f) n w
  have hcA : ((chainC R (TopCat.toSSet.obj Y)).iCycles n).hom
        ((HomologicalComplex.cyclesMap (chainMapS R X Y f) n).hom v)
      = ((chainMapS R X Y f).f n).hom
        (((chainC R (TopCat.toSSet.obj X)).iCycles n).hom v) :=
    congrArg (fun (g : (chainC R (TopCat.toSSet.obj X)).cycles n ⟶
        (chainC R (TopCat.toSSet.obj Y)).X n) => g.hom v)
      (HomologicalComplex.cyclesMap_i (chainMapS R X Y f) n)
  rw [hA, hB]
  rw [kronH_cyc_apply_commRing R (TopCat.toSSet.obj Y) n w
        ((HomologicalComplex.cyclesMap (chainMapS R X Y f) n).hom v),
      kronH_cyc_apply_commRing R (TopCat.toSSet.obj X) n
        ((HomologicalComplex.cyclesMap (dualChainMapS R X Y f) n).hom w) v]
  rw [hcA, cochainOfCycle_cyclesMapS_apply_commRing R X Y f n w
        (((chainC R (TopCat.toSSet.obj X)).iCycles n).hom v)]

end

end Work.Pi6.SQASM
