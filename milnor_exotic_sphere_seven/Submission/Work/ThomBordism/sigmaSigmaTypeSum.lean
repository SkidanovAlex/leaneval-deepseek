import Mathlib
import Submission.Work.ThomBordism.sigmaCohomology
import Submission.Work.ThomBordism.sigmaInterForm
import Submission.Work.ThomBordism.signatureSumProd
import Submission.Work.Bordism.sigma_disj

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Additivity of the signature over a finite disjoint union

For a finite family of spaces `Y i` and homology classes `c i ∈ H_{2k}(Y i ; ℤ)`, the signature of
the disjoint union `Σ i, Y i` against the class `∑ i (incl i)_* (c i)` is the sum of the signatures
of the pieces:

`Work.ThomBordism.sigmaSigmaTypeSum`.

The proof combines the cohomological splitting of a finite disjoint union
(`Work.ThomBordism.pullbackRat_sigma_bijective`), the computation of the intersection form of a
finite disjoint union as the orthogonal sum of the forms of the pieces
(`Work.ThomBordism.ratInterForm_sigmaSum`) and the additivity of the signature over a finite
orthogonal sum (`Work.ThomBordism.signature_sum_prod`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory Limits Topology
open scoped TensorProduct

namespace Work.ThomBordism

noncomputable section

variable {ι : Type} [Fintype ι] (α : ι → TopCat.{0})

/-- The class on the disjoint union which is the sum of the pushforwards of the classes of the
pieces. -/
noncomputable def sigmaSumClass {k : ℕ}
    (c : ∀ i, (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (α i))).homology (k + k)) :
    (Work.Cohomology.chainC ℤ
      (TopCat.toSSet.obj (TopCat.of (Σ i, α i)))).homology (k + k) :=
  ∑ i, HomologicalComplex.homologyMap
    (Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i)) (k + k) (c i)

/-- **Additivity of the signature over a finite disjoint union**, in the form in which the spaces
are displayed as a `σ`-type of topological spaces. -/
theorem sigma_sigmaTypeSum_aux {k : ℕ}
    (c : ∀ i, (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (α i))).homology (k + k))
    [∀ i, FiniteDimensional ℚ
      (Work.SignatureBordism.ratCohomology k (TopCat.toSSet.obj (α i)))]
    [FiniteDimensional ℚ (Work.SignatureBordism.ratCohomology k
      (TopCat.toSSet.obj (TopCat.of (Σ i, α i))))] :
    Work.SignatureBordism.sigma k (TopCat.toSSet.obj (TopCat.of (Σ i, α i)))
        (sigmaSumClass α c)
      = ∑ i, Work.SignatureBordism.sigma k (TopCat.toSSet.obj (α i)) (c i) := by
  classical
  -- the cohomological splitting
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
      (LinearMap.proj i)
  have hQ : Work.SignatureBordism.ratInterForm k
        (TopCat.toSSet.obj (TopCat.of (Σ i, α i))) (sigmaSumClass α c)
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
          (sigmaSumClass α c))
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
        (LinearMap.proj i)) (Φ x) = _
      rw [sum_apply]
      exact Finset.sum_congr rfl fun i _ => by
        rw [QuadraticMap.comp_apply, LinearMap.proj_apply, hΦ_apply]
    rw [hQprod, sum_apply₂]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.compl₁₂_apply, Work.SignatureBordism.quadOfBilin_apply]
  calc Work.SignatureBordism.sigma k (TopCat.toSSet.obj (TopCat.of (Σ i, α i)))
        (sigmaSumClass α c)
      = Work.SignatureBordism.signature (Work.SignatureBordism.quadOfBilin
          (Work.SignatureBordism.ratInterForm k (TopCat.toSSet.obj (TopCat.of (Σ i, α i)))
            (sigmaSumClass α c))) := rfl
    _ = Work.SignatureBordism.signature (Qprod.comp
          (Φ : Work.SignatureBordism.ratCohomology k
            (TopCat.toSSet.obj (TopCat.of (Σ i, α i))) →ₗ[ℚ]
            (∀ i, Work.SignatureBordism.ratCohomology k (TopCat.toSSet.obj (α i))))) := by
        rw [hquad]
    _ = Work.SignatureBordism.signature Qprod :=
        Work.SignatureBordism.signature_comp_linearEquiv _ Φ
    _ = ∑ i, Work.SignatureBordism.signature (Work.SignatureBordism.quadOfBilin
          (Work.SignatureBordism.ratInterForm k (TopCat.toSSet.obj (α i)) (c i))) :=
        signature_sum_prod (fun i => Work.SignatureBordism.quadOfBilin
          (Work.SignatureBordism.ratInterForm k (TopCat.toSSet.obj (α i)) (c i)))
    _ = ∑ i, Work.SignatureBordism.sigma k (TopCat.toSSet.obj (α i)) (c i) := rfl


/-- **Additivity of the signature under a finite disjoint union.**  The signature of `Σ i, Y i`
against the class obtained by pushing the classes `c i` forward along the inclusions is the sum of
the signatures of the pieces. -/
theorem sigmaSigmaTypeSum {k : ℕ} (ι : Type) [Fintype ι] (Y : ι → Type)
    [∀ i, TopologicalSpace (Y i)]
    (c : ∀ i, (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (TopCat.of (Y i)))).homology (k + k))
    [∀ i, FiniteDimensional ℚ (Work.SignatureBordism.ratCohomology k (TopCat.toSSet.obj (TopCat.of (Y i))))]
    [FiniteDimensional ℚ (Work.SignatureBordism.ratCohomology k (TopCat.toSSet.obj (TopCat.of (Σ i, Y i))))] :
    Work.SignatureBordism.sigma k (TopCat.toSSet.obj (TopCat.of (Σ i, Y i)))
        (∑ i, HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (TopCat.of (Y i)) (TopCat.of (Σ i, Y i))
            (TopCat.ofHom ⟨fun y => (⟨i, y⟩ : Sigma Y), by continuity⟩)) (k + k) (c i))
      = ∑ i, Work.SignatureBordism.sigma k (TopCat.toSSet.obj (TopCat.of (Y i))) (c i) := by
  exact sigma_sigmaTypeSum_aux (fun i => TopCat.of (Y i)) c

end

end Work.ThomBordism
