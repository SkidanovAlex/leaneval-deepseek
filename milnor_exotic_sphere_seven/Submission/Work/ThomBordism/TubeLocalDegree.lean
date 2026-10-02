import Submission.Work.ThomBordism.gaussTubeData

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The local-degree predicate of a tube

`Work.ThomBordism.IsLocalDegreeClass` is the predicate "the relative class `U` implements the local
degree of the member's fundamental class `V.c` w.r.t. the tube collapse class": the Kronecker form
of the identity of `Work.Tubular.exists_localDegree_at_collapseRelK8` /
`Work.ThomBordism.localDegreeSpan`:

  `⟨x ⌣ U, collapseRelK8 C g hg hR hbox⟩ = ⟨z^*x, V.c⟩`  for all `x ∈ H⁸(ν)`.

It is recorded here (in a file that has no `sorry`) so that lemmas about it can be stated without
importing the (still unproved) target of `univLocalDegreeClass.lean`.
-/

open CategoryTheory

namespace Work.ThomBordism

noncomputable section

/-- **The local-degree predicate**: `U ∈ H^k(ν, ν∖0)` implements the local degree of the member's
fundamental class `V.c` with respect to the collapse class of the tube data. -/
def IsLocalDegreeClass {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y.ofLp j| < R)
    (U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E)) : Prop :=
  ∀ x : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)),
    Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E) (k + 8)
      ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup
        (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k x U))
      (Work.Tubular.collapseRelK8 C g hg hR hbox)
    = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
        ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom x) V.c

/-- The local-degree predicate for the pullback of the universal Thom class along a lifted
Gauss/classifying bundle map `G` of the normal bundle (this is the class appearing in the target
`Work.ThomBordism.univLocalDegreeClass`). -/
def IsLocalDegreeClassGtdU {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y.ofLp j| < R) : Prop :=
  IsLocalDegreeClass C g hg hR hbox (Work.ThomBordism.gtdU E ND G hgm)

end

end Work.ThomBordism
