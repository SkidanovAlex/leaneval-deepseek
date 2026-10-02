import Mathlib
import Submission.Work.Bordism.Basic
import Submission.Work.SignatureBordism.Intersection
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Cohomology.kronH_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Multiplicativity of the intersection form under disjoint union

For closed oriented `(k+k)`-manifolds `M`, `N` in the model of
`Submission/Work/Bordism/Basic.lean` (a space together with a fundamental class) the middle
intersection form of the disjoint union `M ⊔ N` splits as the orthogonal sum of the two forms:

`Q_{M ⊔ N}(y, z) = Q_M(i_M^* y, i_M^* z) + Q_N(i_N^* y, i_N^* z)`,

where `i_M : M ⟶ M ⊔ N` and `i_N : N ⟶ M ⊔ N` are the coproduct inclusions and `y, z` are
cohomology classes on `M ⊔ N`.

The proof unfolds `interForm` into the Kronecker pairing of the cup product against the fundamental
class (`Work.SignatureBordism.interForm_apply`), uses that the fundamental class of `M ⊔ N` is
`(i_M)_*[M] + (i_N)_*[N]` (`Work.Bordism.ClosedOriented.disj`), that the Kronecker pairing is
additive in the homology class, and then applies the two naturalities
`Work.Cohomology.kronH_natural` (naturality of the Kronecker pairing) and
`Work.Cohomology.cupNaturalH` (naturality of the cup product) to each summand.

## Formalisation remark

The workspace identifies the singular chains of a topological space with the chains of its singular
simplicial set *by definition*, but the equality is not visible at the transparency level used by
`rw`; the additions are therefore combined with `congrArg` and `Eq.trans` rather than with `rw`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology

namespace Work.Bordism

open Work.Cohomology Work.SignatureBordism

noncomputable section

theorem interForm_coprod {k : ℕ} (M N : Work.Bordism.ClosedOriented (k + k))
    (y z : (Work.Cohomology.cochainC ℤ
      (TopCat.toSSet.obj (CategoryTheory.Limits.coprod M.X N.X))).homology k) :
    Work.SignatureBordism.interForm ℤ (TopCat.toSSet.obj (CategoryTheory.Limits.coprod M.X N.X))
        k k (Work.Bordism.ClosedOriented.disj M N).c y z
      = Work.SignatureBordism.interForm ℤ (TopCat.toSSet.obj M.X) k k M.c
          (Work.Cohomology.singularCohomologyMap ℤ M.X (CategoryTheory.Limits.coprod M.X N.X)
            (CategoryTheory.Limits.coprod.inl) k y)
          (Work.Cohomology.singularCohomologyMap ℤ M.X (CategoryTheory.Limits.coprod M.X N.X)
            (CategoryTheory.Limits.coprod.inl) k z)
        + Work.SignatureBordism.interForm ℤ (TopCat.toSSet.obj N.X) k k N.c
          (Work.Cohomology.singularCohomologyMap ℤ N.X (CategoryTheory.Limits.coprod M.X N.X)
            (CategoryTheory.Limits.coprod.inr) k y)
          (Work.Cohomology.singularCohomologyMap ℤ N.X (CategoryTheory.Limits.coprod M.X N.X)
            (CategoryTheory.Limits.coprod.inr) k z) := by
  have h1 := interForm_apply ℤ (TopCat.toSSet.obj (CategoryTheory.Limits.coprod M.X N.X)) k k
      (ClosedOriented.disj M N).c y z
  have hc : (ClosedOriented.disj M N).c
      = HomologicalComplex.homologyMap (chainMap ℤ M.X (CategoryTheory.Limits.coprod M.X N.X)
          CategoryTheory.Limits.coprod.inl) (k+k) M.c
        + HomologicalComplex.homologyMap (chainMap ℤ N.X (CategoryTheory.Limits.coprod M.X N.X)
          CategoryTheory.Limits.coprod.inr) (k+k) N.c := rfl
  have hnatM := kronH_natural M.X (CategoryTheory.Limits.coprod M.X N.X)
      CategoryTheory.Limits.coprod.inl (k+k)
      (cupH' ℤ (TopCat.toSSet.obj (CategoryTheory.Limits.coprod M.X N.X)) k k y z) M.c
  have hnatN := kronH_natural N.X (CategoryTheory.Limits.coprod M.X N.X)
      CategoryTheory.Limits.coprod.inr (k+k)
      (cupH' ℤ (TopCat.toSSet.obj (CategoryTheory.Limits.coprod M.X N.X)) k k y z) N.c
  have hcupM := cupNaturalH ℤ CategoryTheory.Limits.coprod.inl k k y z
  have hcupN := cupNaturalH ℤ CategoryTheory.Limits.coprod.inr k k y z
  have hM := interForm_apply ℤ (TopCat.toSSet.obj M.X) k k M.c
      (singularCohomologyMap ℤ M.X (CategoryTheory.Limits.coprod M.X N.X)
        CategoryTheory.Limits.coprod.inl k y)
      (singularCohomologyMap ℤ M.X (CategoryTheory.Limits.coprod M.X N.X)
        CategoryTheory.Limits.coprod.inl k z)
  have hN := interForm_apply ℤ (TopCat.toSSet.obj N.X) k k N.c
      (singularCohomologyMap ℤ N.X (CategoryTheory.Limits.coprod M.X N.X)
        CategoryTheory.Limits.coprod.inr k y)
      (singularCohomologyMap ℤ N.X (CategoryTheory.Limits.coprod M.X N.X)
        CategoryTheory.Limits.coprod.inr k z)
  have hAM := congrArg (fun t => (kronH ℤ (TopCat.toSSet.obj M.X) (k+k) t) M.c) hcupM
  have hAN := congrArg (fun t => (kronH ℤ (TopCat.toSSet.obj N.X) (k+k) t) N.c) hcupN
  have hR : ((interForm ℤ (TopCat.toSSet.obj M.X) k k M.c)
          (singularCohomologyMap ℤ M.X (CategoryTheory.Limits.coprod M.X N.X)
            CategoryTheory.Limits.coprod.inl k y))
          (singularCohomologyMap ℤ M.X (CategoryTheory.Limits.coprod M.X N.X)
            CategoryTheory.Limits.coprod.inl k z)
        + ((interForm ℤ (TopCat.toSSet.obj N.X) k k N.c)
          (singularCohomologyMap ℤ N.X (CategoryTheory.Limits.coprod M.X N.X)
            CategoryTheory.Limits.coprod.inr k y))
          (singularCohomologyMap ℤ N.X (CategoryTheory.Limits.coprod M.X N.X)
            CategoryTheory.Limits.coprod.inr k z)
      = (kronH ℤ (TopCat.toSSet.obj M.X) (k+k)
            (cupH' ℤ (TopCat.toSSet.obj M.X) k k
              ((singularCohomologyMap ℤ M.X (CategoryTheory.Limits.coprod M.X N.X)
                CategoryTheory.Limits.coprod.inl k) y)
              ((singularCohomologyMap ℤ M.X (CategoryTheory.Limits.coprod M.X N.X)
                CategoryTheory.Limits.coprod.inl k) z))) M.c
        + (kronH ℤ (TopCat.toSSet.obj N.X) (k+k)
            (cupH' ℤ (TopCat.toSSet.obj N.X) k k
              ((singularCohomologyMap ℤ N.X (CategoryTheory.Limits.coprod M.X N.X)
                CategoryTheory.Limits.coprod.inr k) y)
              ((singularCohomologyMap ℤ N.X (CategoryTheory.Limits.coprod M.X N.X)
                CategoryTheory.Limits.coprod.inr k) z))) N.c :=
    Eq.trans (congrArg (fun t => t + _) hM) (congrArg (fun t => _ + t) hN)
  exact Eq.trans (Eq.trans h1 (Eq.trans
      (congrArg (kronH ℤ (TopCat.toSSet.obj (CategoryTheory.Limits.coprod M.X N.X)) (k+k)
        (cupH' ℤ (TopCat.toSSet.obj (CategoryTheory.Limits.coprod M.X N.X)) k k y z)) hc)
      (Eq.trans (map_add _ _ _) (Eq.trans
        (congrArg (fun t => t + _) hnatM)
        (Eq.trans (congrArg (fun t => _ + t) hnatN) (Eq.trans
          (congrArg (fun t => t + _) hAM)
          (congrArg (fun t => _ + t) hAN))))))) hR.symm

end

end Work.Bordism
