import Mathlib
import Submission.Work.SignatureBordism.Rationalisation
import Submission.Work.Bordism.Middle
import Submission.Work.Cohomology.kronH_natural
import Submission.Work.Cohomology.cupNaturalH

/-!
# The intersection form of a `σ`-type of spaces

For a finite family of spaces `α : ι → TopCat` and homology classes `c i ∈ H_{2k}(α i)`, the
intersection pairing of the disjoint union `Σ i, α i` against the class `∑ i (incl i)_* (c i)` is
the sum of the intersection pairings of the pieces against the pulled back classes:

`Work.ThomBordism.interForm_sigmaSum`,

and the rationalised form `Work.ThomBordism.ratInterForm_sigmaSum` is the orthogonal sum of the
rationalised forms of the pieces.  This is the finite-family generalisation of
`Work.Bordism.interForm_coprod`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open CategoryTheory Limits Topology
open scoped TensorProduct

namespace Work.ThomBordism

noncomputable section

variable {ι : Type} [Fintype ι] (α : ι → TopCat.{0})

/-- Evaluating a finite sum of `ℚ`-linear maps. -/
lemma sum_apply_lin {κ : Type} [Fintype κ] {M N : Type} [AddCommMonoid M] [Module ℚ M]
    [AddCommMonoid N] [Module ℚ N] (h : κ → (M →ₗ[ℚ] N)) (x : M) :
    (∑ j, h j) x = ∑ j, h j x :=
  map_sum (G := (M →ₗ[ℚ] N) →+ N)
    { toFun := fun f => f x, map_zero' := rfl, map_add' := fun _ _ => rfl } h Finset.univ

/-- Evaluating a finite sum of `ℚ`-bilinear maps. -/
lemma sum_apply₂ {κ : Type} [Fintype κ] {M N P : Type} [AddCommMonoid M] [Module ℚ M]
    [AddCommMonoid N] [Module ℚ N] [AddCommMonoid P] [Module ℚ P]
    (F : κ → (M →ₗ[ℚ] N →ₗ[ℚ] P)) (x : M) (y : N) :
    (∑ i, F i) x y = ∑ i, F i x y := by
  rw [sum_apply_lin F x, sum_apply_lin (fun i => F i x) y]

/-- **The intersection pairing of a `σ`-type of spaces is the sum of the pairings of the pieces.**
The class on the disjoint union is the sum of the pushforwards of the classes of the pieces. -/
theorem interForm_sigmaSum {k : ℕ}
    (c : ∀ i, (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (α i))).homology (k + k))
    (y z : (Work.Cohomology.cochainC ℤ
      (TopCat.toSSet.obj (TopCat.of (Σ i, α i)))).homology k) :
    Work.SignatureBordism.interForm ℤ (TopCat.toSSet.obj (TopCat.of (Σ i, α i))) k k
        (∑ i, HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i))
          (k + k) (c i)) y z
      = ∑ i, Work.SignatureBordism.interForm ℤ (TopCat.toSSet.obj (α i)) k k (c i)
          ((Work.Cohomology.singularCohomologyMap ℤ (α i) (TopCat.of (Σ i, α i))
            (TopCat.sigmaι α i) k).hom y)
          ((Work.Cohomology.singularCohomologyMap ℤ (α i) (TopCat.of (Σ i, α i))
            (TopCat.sigmaι α i) k).hom z) := by
  rw [Work.SignatureBordism.interForm_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Work.Cohomology.kronH_natural (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i) (k + k)
    (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of (Σ i, α i))) k k y z) (c i),
    Work.Cohomology.cupNaturalH ℤ (TopCat.sigmaι α i) k k y z,
    Work.SignatureBordism.interForm_apply]

/-- **The rationalised intersection form of a `σ`-type is the orthogonal sum of the rationalised
forms of the pieces.** -/
theorem ratInterForm_sigmaSum {k : ℕ}
    (c : ∀ i, (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (α i))).homology (k + k)) :
    Work.SignatureBordism.ratInterForm k (TopCat.toSSet.obj (TopCat.of (Σ i, α i)))
        (∑ i, HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i))
          (k + k) (c i))
      = ∑ i, (Work.SignatureBordism.ratInterForm k (TopCat.toSSet.obj (α i)) (c i)).compl₁₂
          (Work.Bordism.pullbackRat k (TopCat.sigmaι α i))
          (Work.Bordism.pullbackRat k (TopCat.sigmaι α i)) := by
  refine Work.SignatureBordism.tensor_bilin_ext fun a b y z => ?_
  have hL : (Work.SignatureBordism.ratInterForm k (TopCat.toSSet.obj (TopCat.of (Σ i, α i)))
        (∑ i, HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i))
          (k + k) (c i))) (a ⊗ₜ[ℤ] y) (b ⊗ₜ[ℤ] z)
      = (a * b) * ((Work.SignatureBordism.interForm ℤ
          (TopCat.toSSet.obj (TopCat.of (Σ i, α i))) k k
          (∑ i, HomologicalComplex.homologyMap
            (Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i))
            (k + k) (c i)) y z) : ℚ) :=
    Work.SignatureBordism.ratInterForm_tmul k _ _ a b y z
  rw [hL]
  rw [sum_apply₂]
  have hterm : ∀ i, ((Work.SignatureBordism.ratInterForm k (TopCat.toSSet.obj (α i)) (c i)).compl₁₂
        (Work.Bordism.pullbackRat k (TopCat.sigmaι α i))
        (Work.Bordism.pullbackRat k (TopCat.sigmaι α i))) (a ⊗ₜ[ℤ] y) (b ⊗ₜ[ℤ] z)
      = (a * b) * ((Work.SignatureBordism.interForm ℤ (TopCat.toSSet.obj (α i)) k k (c i)
          ((Work.Cohomology.singularCohomologyMap ℤ (α i) (TopCat.of (Σ i, α i))
            (TopCat.sigmaι α i) k).hom y)
          ((Work.Cohomology.singularCohomologyMap ℤ (α i) (TopCat.of (Σ i, α i))
            (TopCat.sigmaι α i) k).hom z)) : ℚ) := by
    intro i
    rw [LinearMap.compl₁₂_apply, Work.Bordism.pullbackRat_tmul, Work.Bordism.pullbackRat_tmul,
      Work.SignatureBordism.ratInterForm_tmul]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rw [interForm_sigmaSum α c y z, Int.cast_sum, Finset.mul_sum]

end

end Work.ThomBordism
