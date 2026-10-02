import Submission.Work.Tubular.OnePointLocalDegree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

/-!
# Wiring the local degree to the Hurewicz pairing

The assembly of item 3, in the form in which it is available **now**: the sole geometric gap of the
chapter (`Work.Tubular.TubeLocalDegreeOnePoint`, the local degree of the collapse, stated in the
pair `(ν⁺, A)`), together with the description of the class `u` of the universal Thom space
(Grassmann's obligation, §17), gives the ν-side Hurewicz pairing identity

  `⟨u, c'⟩_{ν⁺} = ⟨(zero section)^* x, [V]⟩`

for the class `u` whose relativisation is the mixed cup `x ⌣ U`.  This is the identity that
`Work.Tubular.kronH_alphaV_pairings` (§16.2) reduces the two fields of `Work.Tubular.TubeThomRep`
to, so the consumer can wire the assembly today and instantiate the hypothesis when the fibre
computation lands.

> **VACUITY WARNING (README §35.2).**  The class `x` ranges over
> `H⁸(OnePoint (NormalTotal E)) = H⁸(Th ν)`, and the Thom space of the rank-`k` normal bundle is
> `(k-1)`-connected, so for `8 < k` — in particular for the project's `k = 11` — this group is
> **zero**, both sides of the identity vanish, and the statement holds for *every* pair `(U, c')`.
> The non-vacuous form of the local degree is `Work.Tubular.TubeLocalDegree` /
> `Work.Tubular.TubeLocalDegreePairing` (`LocalStep.lean`), stated on `Z.TotalSpace` (where
> `H⁸ ≅ H⁸(V) ≅ ℤ`); its wiring to the Hurewicz pairing is
> `Work.Tubular.kronH_relKronH_eq_fundClass` together with the `8 + k ↔ k + 8` transport
> `Work.Tubular.hurewiczClassOf_add_comm`.


* `Work.Tubular.relCoh_of_abs` — the relativisation `H^{k+8}(ν⁺) → H^{k+8}(ν⁺,A)` (the inverse of
  the forgetful map, an isomorphism because `A` is contractible);
* `Work.Tubular.kronH_eq_relKronH_onePoint'` — the pairing transfer in the `relCoh_of_abs` spelling;
* `Work.Tubular.kronH_onePoint_of_localDegree` — the wiring.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial Topology

open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular

noncomputable section

open Work.Cohomology

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The relativisation of a degree-`k+8` class on `ν⁺`**: the inverse of the forgetful map
`H^{k+8}(ν⁺,A) → H^{k+8}(ν⁺)`, which is an isomorphism because `A` is contractible
(`Work.Tubular.bijective_relToAbs_onePoint`). -/
noncomputable def relCoh_of_abs (E : EmbeddingData V (8 + k)) :
    Work.Thom.Coh ℤ (k + 8) (OnePoint (NormalTotal E)) →ₗ[ℤ]
      Work.Thom.RelCoh ℤ (k + 8) (OnePoint (NormalTotal E)) (onePointNonzero E) :=
  (LinearEquiv.ofBijective ((Work.Thom.relToAbs ℤ (onePointNonzero E) (k + 8)).hom)
    (bijective_relToAbs_onePoint E (k + 6))).symm

/-- The defining property of `relCoh_of_abs`: forgetting it returns the original class. -/
theorem relToAbs_relCoh_of_abs (E : EmbeddingData V (8 + k))
    (u : Work.Thom.Coh ℤ (k + 8) (OnePoint (NormalTotal E))) :
    (Work.Thom.relToAbs ℤ (onePointNonzero E) (k + 8)).hom (relCoh_of_abs E u) = u := by
  rw [relCoh_of_abs]
  rw [← LinearEquiv.ofBijective_apply (f := (Work.Thom.relToAbs ℤ (onePointNonzero E) (k + 8)).hom)
    (hf := bijective_relToAbs_onePoint E (k + 6))]
  exact LinearEquiv.apply_symm_apply _ u

/-- **The consumer's Hurewicz pairing in the relative world**, in the `relCoh_of_abs` spelling. -/
theorem kronH_eq_relKronH_onePoint' (E : EmbeddingData V (8 + k))
    (u : Work.Thom.Coh ℤ (k + 8) (OnePoint (NormalTotal E)))
    (c' : (singularChains ℤ (TopCat.of (OnePoint (NormalTotal E)))).homology (k + 8)) :
    Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of (OnePoint (NormalTotal E))))
        (k + 8) u c'
      = relKronH (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E) (k + 8)
          (relCoh_of_abs E u)
          ((HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
            (inclChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E))) (k + 8)) c') := by
  rw [relCoh_of_abs]
  exact kronH_eq_relKronH_onePoint E u c'

/-- **The wiring lemma: the local degree gives the ν-side Hurewicz pairing.**  If the relativisation
of the class `u` of the universal Thom space is the mixed cup `x ⌣ U` (the description of the
universal classes, Grassmann's obligation) and the local degree holds for `U` and `c'`, then the
pairing of `u` with `c'` is the pairing of `(zero section)^* x` with `[V]`. -/
theorem kronH_onePoint_of_localDegree (E : EmbeddingData V (8 + k))
    (U : Work.Thom.RelCoh ℤ k (OnePoint (NormalTotal E)) (onePointNonzero E))
    (c' : (singularChains ℤ (TopCat.of (OnePoint (NormalTotal E)))).homology (k + 8))
    (hdeg : TubeLocalDegreeOnePoint E U c')
    (u : Work.Thom.Coh ℤ (k + 8) (OnePoint (NormalTotal E)))
    (x : Work.Thom.Coh ℤ 8 (OnePoint (NormalTotal E)))
    (hx : relCoh_of_abs E u
      = (Nat.add_comm 8 k) ▸ (mixedCup (TopCat.of (OnePoint (NormalTotal E)))
          (onePointNonzero E) 8 k x U)) :
    Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of (OnePoint (NormalTotal E))))
        (k + 8) u c'
      = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
          ((Work.Thom.CohMap (zeroSectionOnePoint E) ℤ 8).hom x) V.c :=
  calc Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of (OnePoint (NormalTotal E))))
        (k + 8) u c'
      = relKronH (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E) (k + 8)
          (relCoh_of_abs E u)
          ((HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
            (inclChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E))) (k + 8)) c') :=
        kronH_eq_relKronH_onePoint' E u c'
    _ = relKronH (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E) (k + 8)
          ((Nat.add_comm 8 k) ▸ (mixedCup (TopCat.of (OnePoint (NormalTotal E)))
            (onePointNonzero E) 8 k x U))
          ((HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
            (inclChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E))) (k + 8)) c') := by
        rw [hx]
    _ = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
          ((Work.Thom.CohMap (zeroSectionOnePoint E) ℤ 8).hom x) V.c := hdeg x

end

end Work.Tubular
