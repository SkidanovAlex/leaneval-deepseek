import Submission.Work.Tubular.onePoint_compl_zero
import Submission.Work.Tubular.onePoint_homology_relChains
import Submission.Work.Tubular.relKronH_relToAbs
import Submission.Work.Cohomology.contractible
import Submission.Work.Cohomology.PairSequence

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

/-!
# The consumer's Hurewicz pairing, in the relative world of the pair `(ν⁺, A)`

The Pontryagin–Thom chapter consumes (through `Work.Tubular.TubeThomRep` /
`Work.Tubular.kronH_alphaV_pairings`) the **absolute** Hurewicz pairing

  `⟨u, h(collapse)⟩_{ν⁺}`,      `u ∈ H^{k+8}(ν⁺)`,  `h(collapse) ∈ H_{k+8}(ν⁺)`.

This module rewrites it in the **relative** world of the pair `(ν⁺, A)`, where both sides are
computed by explicit maps:

* `Work.Tubular.bijective_relToAbs_onePoint` — the forgetful map
  `relToAbs : H^n(ν⁺,A) → H^n(ν⁺)` is bijective for `n ≥ 1`, because `A` is contractible and hence
  `H^{n-1}(A) = H^n(A) = 0` (the long exact sequence of the pair);
* `Work.Tubular.kronH_eq_relKronH_onePoint` — consequently

  `⟨u, c'⟩_{ν⁺} = relKronH (ν⁺,A) (Ψ u) (π_* c')`

  for `Ψ = relToAbs⁻¹ : H^{k+8}(ν⁺) → H^{k+8}(ν⁺,A)` and `π_*` the map of the pair.  This is
  `Work.Tubular.relKronH_relToAbs_apply` (the non-vacuous transfer, README §26.7) with
  `relToAbs (Ψ u) = u`.

So the remaining geometric input of item 3 can be stated *in the pair `(ν⁺,A)`*, where the collapse
class `π_*(h(collapse))` and the relativised universal class `Ψ(D.p1sqU)` are both explicit; the
statement is `Work.Tubular.TubeLocalDegreeOnePoint` below.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial Topology

open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular

noncomputable section

open Work.Cohomology

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **`relToAbs : H^{n+1}(ν⁺,A) → H^{n+1}(ν⁺)` is bijective.**  `A = (ν∖0) ∪ {∞}` is contractible,
so `H^n(A) = H^{n+1}(A) = 0`, and the long exact sequence of the pair
(`Work.Cohomology.pair_exact₁`, `pair_exact₂`) makes the middle map an isomorphism. -/
theorem bijective_relToAbs_onePoint (E : EmbeddingData V (8 + k)) (n : ℕ) :
    Function.Bijective ((Work.Thom.relToAbs ℤ (onePointNonzero E) (n + 2)).hom) := by
  have hc : ContractibleSpace ↥(onePointNonzero E) := contractibleSpace_onePointNonzero E
  haveI := hc
  have hvan : ∀ m : ℕ, 1 ≤ m → IsZero
      (singularCohomology ℤ m (TopCat.of (onePointNonzero E))) := by
    intro m hm
    have hm' : m = (m - 1) + 1 := by omega
    rw [hm']
    exact Work.Cohomology.contractible ℤ (TopCat.of (onePointNonzero E)) (m - 1)
  haveI H1 : IsZero (singularCohomology ℤ (n + 1) (TopCat.of (onePointNonzero E))) :=
    hvan (n + 1) (by omega)
  haveI H2 : IsZero (singularCohomology ℤ (n + 2) (TopCat.of (onePointNonzero E))) :=
    hvan (n + 2) (by omega)
  have hmono : Mono (HomologicalComplex.homologyMap
      (relIncl ℤ (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E)) (n + 2)) := by
    have hδ : pairδ ℤ (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E) (n + 1)
        = 0 := H1.eq_of_src (pairδ ℤ (TopCat.of (OnePoint (NormalTotal E)))
          (onePointNonzero E) (n + 1)) 0
    exact (ShortComplex.exact_iff_mono _ hδ).mp
      (pair_exact₁ ℤ (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E) (n + 1))
  have hrestr : HomologicalComplex.homologyMap
      (restr ℤ (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E)) (n + 2) = 0 :=
    H2.eq_of_tgt (HomologicalComplex.homologyMap
      (restr ℤ (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E)) (n + 2)) 0
  have hepi : Epi (HomologicalComplex.homologyMap
      (relIncl ℤ (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E)) (n + 2)) :=
    (ShortComplex.exact_iff_epi _ hrestr).mp
      (pair_exact₂ ℤ (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E) (n + 2))
  have hinj : Function.Injective (HomologicalComplex.homologyMap
      (relIncl ℤ (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E)) (n + 2)).hom :=
    (ModuleCat.mono_iff_injective _).mp hmono
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap
      (relIncl ℤ (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E)) (n + 2)).hom :=
    (ModuleCat.epi_iff_surjective _).mp hepi
  have hrel : Work.Thom.relToAbs ℤ (onePointNonzero E) (n + 2)
      = HomologicalComplex.homologyMap (relIncl ℤ (TopCat.of (OnePoint (NormalTotal E)))
          (onePointNonzero E)) (n + 2) := rfl
  rw [hrel]
  exact ⟨hinj, hsurj⟩

/-- **The consumer's Hurewicz pairing, rewritten in the relative world of the pair `(ν⁺,A)`.** -/
theorem kronH_eq_relKronH_onePoint (E : EmbeddingData V (8 + k))
    (u : Work.Thom.Coh ℤ (k + 8) (OnePoint (NormalTotal E)))
    (c' : (singularChains ℤ (TopCat.of (OnePoint (NormalTotal E)))).homology (k + 8)) :
    Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of (OnePoint (NormalTotal E))))
        (k + 8) u c'
      = relKronH (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E) (k + 8)
          ((LinearEquiv.ofBijective
            ((Work.Thom.relToAbs ℤ (onePointNonzero E) (k + 8)).hom)
            (bijective_relToAbs_onePoint E (k + 6))).symm u)
          ((HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
            (inclChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E))) (k + 8)) c') := by
  have h := relKronH_relToAbs_apply (B := OnePoint (NormalTotal E)) (onePointNonzero E) (k + 8)
    ((LinearEquiv.ofBijective ((Work.Thom.relToAbs ℤ (onePointNonzero E) (k + 8)).hom)
      (bijective_relToAbs_onePoint E (k + 6))).symm u) c'
  have h2 : ((Work.Thom.relToAbs ℤ (onePointNonzero E) (k + 8)).hom)
      ((LinearEquiv.ofBijective ((Work.Thom.relToAbs ℤ (onePointNonzero E) (k + 8)).hom)
        (bijective_relToAbs_onePoint E (k + 6))).symm u) = u := by
    rw [← LinearEquiv.ofBijective_apply (f := (Work.Thom.relToAbs ℤ (onePointNonzero E) (k + 8)).hom)
      (hf := bijective_relToAbs_onePoint E (k + 6))]
    exact LinearEquiv.apply_symm_apply _ u
  rw [h2] at h
  exact h.symm

end

end Work.Tubular
