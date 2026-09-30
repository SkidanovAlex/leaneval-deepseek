import Mathlib
import Submission.Work.ThomBordism.nondegenerateCompLinearEquiv
import Submission.Work.ThomBordism.nondegenerateSumProd
import Submission.Work.ThomBordism.sigmaInterForm
import Submission.Work.ThomBordism.sigmaCohomology

/-!
# Non-degeneracy of the middle intersection form of a disjoint union

For a finite family of spaces `α : ι → TopCat` and homology classes `c i ∈ H_{k+k}(α i)`, if the
middle intersection form of every piece against `c i` is non-degenerate, then so is the middle
intersection form of the disjoint union `Σ i, α i` against the sum `∑ i (incl i)_* c i`:

`Work.ThomBordism.nondegenerateSigmaSum`.

This is the non-degeneracy companion of the additivity of the signature over a finite disjoint union
(`Work.ThomBordism.sigma_sigmaTypeSum_aux`), and the second half of the reduction of
`Work.ThomBordism.bdryMidFormNondegenerate`.

The proof combines three ingredients:

* `Work.ThomBordism.ratInterForm_sigmaSum` — the intersection form of the disjoint union is the
  orthogonal sum of the forms of the pieces, precomposed with the pullbacks along the inclusions;
* `Work.ThomBordism.pullbackRat_sigma_bijective` — the product of the pullbacks along the inclusions
  is a `ℚ`-linear *equivalence* `Hᵏ(Σ i, α i;ℚ) ≃ ∏ i, Hᵏ(α i;ℚ)`;
* `Work.ThomBordism.nondegenerate_sum_prod` (non-degeneracy of an orthogonal sum) together with
  `Work.ThomBordism.nondegenerate_comp_linearEquiv` (invariance under a linear equivalence).

No finite-dimensionality hypothesis is needed.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open CategoryTheory Limits Topology
open scoped TensorProduct

namespace Work.ThomBordism

noncomputable section

/-- **Non-degeneracy of the middle intersection form over a finite disjoint union.** -/
theorem nondegenerateSigmaSum {ι : Type} [Fintype ι] (α : ι → TopCat.{0}) {k : ℕ}
    (c : ∀ i, (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (α i))).homology (k + k))
    (h : ∀ i, Work.Bordism.Nondegenerate (Work.SignatureBordism.quadOfBilin
      (Work.SignatureBordism.ratInterForm k (TopCat.toSSet.obj (α i)) (c i)))) :
    Work.Bordism.Nondegenerate (Work.SignatureBordism.quadOfBilin
      (Work.SignatureBordism.ratInterForm k (TopCat.toSSet.obj (TopCat.of (Σ i, α i)))
        (∑ i, HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i))
          (k + k) (c i)))) := by
  classical
  -- the cohomological splitting of the disjoint union
  let Φ : Work.SignatureBordism.ratCohomology k
        (TopCat.toSSet.obj (TopCat.of (Σ i, α i))) ≃ₗ[ℚ]
        (∀ i, Work.SignatureBordism.ratCohomology k (TopCat.toSSet.obj (α i))) :=
    LinearEquiv.ofBijective
      (LinearMap.pi (fun i => Work.Bordism.pullbackRat k (TopCat.sigmaι α i)))
      (pullbackRat_sigma_bijective α k)
  -- the orthogonal sum of the forms of the pieces
  let Qprod : QuadraticForm ℚ
      (∀ i, Work.SignatureBordism.ratCohomology k (TopCat.toSSet.obj (α i))) :=
    ∑ i, (Work.SignatureBordism.quadOfBilin
        (Work.SignatureBordism.ratInterForm k (TopCat.toSSet.obj (α i)) (c i))).comp
      (LinearMap.proj i : (∀ i, Work.SignatureBordism.ratCohomology k
        (TopCat.toSSet.obj (α i))) →ₗ[ℚ]
          Work.SignatureBordism.ratCohomology k (TopCat.toSSet.obj (α i)))
  have hQ : Work.SignatureBordism.ratInterForm k
        (TopCat.toSSet.obj (TopCat.of (Σ i, α i)))
        (∑ i, HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i))
          (k + k) (c i))
      = ∑ i, (Work.SignatureBordism.ratInterForm k (TopCat.toSSet.obj (α i)) (c i)).compl₁₂
          (Work.Bordism.pullbackRat k (TopCat.sigmaι α i))
          (Work.Bordism.pullbackRat k (TopCat.sigmaι α i)) :=
    ratInterForm_sigmaSum α c
  have hΦ_apply : ∀ (x : Work.SignatureBordism.ratCohomology k
      (TopCat.toSSet.obj (TopCat.of (Σ i, α i)))) (i : ι),
      Φ x i = Work.Bordism.pullbackRat k (TopCat.sigmaι α i) x := by
    intro x i
    show (LinearMap.pi (fun i => Work.Bordism.pullbackRat k (TopCat.sigmaι α i))) x i = _
    rw [LinearMap.pi_apply]
  have hquad : Work.SignatureBordism.quadOfBilin
        (Work.SignatureBordism.ratInterForm k (TopCat.toSSet.obj (TopCat.of (Σ i, α i)))
          (∑ i, HomologicalComplex.homologyMap
            (Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i))
            (k + k) (c i)))
      = Qprod.comp (Φ : Work.SignatureBordism.ratCohomology k
          (TopCat.toSSet.obj (TopCat.of (Σ i, α i))) →ₗ[ℚ]
          (∀ i, Work.SignatureBordism.ratCohomology k (TopCat.toSSet.obj (α i)))) := by
    rw [hQ]
    refine QuadraticMap.ext fun x => ?_
    rw [Work.SignatureBordism.quadOfBilin_apply, QuadraticMap.comp_apply]
    have hQprod : Qprod ((Φ : Work.SignatureBordism.ratCohomology k
            (TopCat.toSSet.obj (TopCat.of (Σ i, α i))) →ₗ[ℚ]
            (∀ i, Work.SignatureBordism.ratCohomology k (TopCat.toSSet.obj (α i)))) x)
        = ∑ i, Work.SignatureBordism.quadOfBilin
            (Work.SignatureBordism.ratInterForm k (TopCat.toSSet.obj (α i)) (c i))
            (Work.Bordism.pullbackRat k (TopCat.sigmaι α i) x) := by
      change (∑ i, (Work.SignatureBordism.quadOfBilin
          (Work.SignatureBordism.ratInterForm k (TopCat.toSSet.obj (α i)) (c i))).comp
        (LinearMap.proj i : (∀ i, Work.SignatureBordism.ratCohomology k
          (TopCat.toSSet.obj (α i))) →ₗ[ℚ]
            Work.SignatureBordism.ratCohomology k (TopCat.toSSet.obj (α i)))) (Φ x) = _
      rw [sum_apply]
      exact Finset.sum_congr rfl fun i _ => by
        rw [QuadraticMap.comp_apply, LinearMap.proj_apply, hΦ_apply]
    rw [hQprod, sum_apply₂]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.compl₁₂_apply, Work.SignatureBordism.quadOfBilin_apply]
  rw [hquad]
  refine (nondegenerate_comp_linearEquiv Qprod Φ).mpr ?_
  exact nondegenerate_sum_prod (fun i => Work.SignatureBordism.quadOfBilin
      (Work.SignatureBordism.ratInterForm k (TopCat.toSSet.obj (α i)) (c i))) (fun i => h i)

end

end Work.ThomBordism
