import Mathlib
import Submission.Work.RatHurewicz.Cofibre.AssemblyDefs
import Submission.Work.RatHurewicz.Cofibre.isIso_beta_of_contractible_subspace
import Submission.Work.RatHurewicz.Cofibre.isIso_beta_cofibreV
import Submission.Work.Serre.Assembly.serreK2IntSharp

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The pair map `(C,V) → (B,{b})` is a homology isomorphism in the stable range

For `c : C(cofibre ι, B)` constant on the punctured cone `V = cofibreV ι`, the induced map of pairs
`(cofibre ι, V) → (B, {b})` is an isomorphism on integral homology in degrees `0 < j < N` whenever
`c` is a `π`-isomorphism up to `N` (`serreK2IntSharp`) and `B` is path connected.

The proof is the naturality square of the pair sequence
`β_V ≫ ψ_* = c_* ≫ β_B` (`Work.Cohomology.cokernel_π_cokernelMap`), in which `β_V` is an isomorphism
for `j > 0` (the punctured cone is contractible, `isIso_beta_cofibreV`), `c_*` is an isomorphism by
`serreK2IntSharp`, and `β_B` is an isomorphism for `j > 0` because `{b}` is a contractible subspace
(`isIso_beta_of_contractible_subspace`).
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.RatHurewicz.Cofibre

noncomputable section

variable {E F B : Type} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]

/-- **The pair map `(cofibre ι, V) → (B,{b})` is a homology isomorphism in the stable range.** -/
theorem isIso_homologyMap_psiMap (ι : C(F, E)) (c : C(cofibre ι, B)) (b : B)
    (hc : ∀ z : cofibre ι, z ∈ cofibreV ι → c z = b)
    (hC : Nonempty (cofibre ι)) (hB : PathConnectedSpace B) (N : ℕ)
    (hπ : ∀ j : ℕ, j < N → ∀ y : cofibre ι, Function.Bijective (Work.Serre.piMapN c j y))
    (j : ℕ) (hj0 : 0 < j) (hjN : j < N) :
    IsIso (HomologicalComplex.homologyMap (psiMap ι c b hc) j) := by
  haveI : Nonempty (cofibre ι) := hC
  -- the naturality square of the pair sequence, at the level of homology
  have h0 : cokernel.π (Work.Cohomology.inclChains (TopCat.of (cofibre ι)) (cofibreV ι))
        ≫ psiMap ι c b hc
      = Work.Cohomology.chainMap ℤ (TopCat.of (cofibre ι)) (TopCat.of B) (TopCat.ofHom c)
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of B) ({b} : Set B)) := by
    unfold psiMap Work.Cohomology.relChainsMapOf
    exact Work.Cohomology.cokernel_π_cokernelMap _ _ _ _ _
  have e1 : HomologicalComplex.homologyMap
        (cokernel.π (Work.Cohomology.inclChains (TopCat.of (cofibre ι)) (cofibreV ι))) j
        ≫ HomologicalComplex.homologyMap (psiMap ι c b hc) j
      = HomologicalComplex.homologyMap
          (cokernel.π (Work.Cohomology.inclChains (TopCat.of (cofibre ι)) (cofibreV ι))
            ≫ psiMap ι c b hc) j :=
    (HomologicalComplex.homologyMap_comp _ _ j).symm
  have e2 : HomologicalComplex.homologyMap
        (cokernel.π (Work.Cohomology.inclChains (TopCat.of (cofibre ι)) (cofibreV ι))
          ≫ psiMap ι c b hc) j
      = HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (TopCat.of (cofibre ι)) (TopCat.of B) (TopCat.ofHom c)
            ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of B) ({b} : Set B))) j :=
    congrArg (fun m => HomologicalComplex.homologyMap m j) h0
  have e3 : HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of (cofibre ι)) (TopCat.of B) (TopCat.ofHom c)
          ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of B) ({b} : Set B))) j
      = HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (TopCat.of (cofibre ι)) (TopCat.of B) (TopCat.ofHom c)) j
        ≫ HomologicalComplex.homologyMap
          (cokernel.π (Work.Cohomology.inclChains (TopCat.of B) ({b} : Set B))) j :=
    HomologicalComplex.homologyMap_comp _ _ j
  have hsq : HomologicalComplex.homologyMap
        (cokernel.π (Work.Cohomology.inclChains (TopCat.of (cofibre ι)) (cofibreV ι))) j
        ≫ HomologicalComplex.homologyMap (psiMap ι c b hc) j
      = HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (TopCat.of (cofibre ι)) (TopCat.of B) (TopCat.ofHom c)) j
        ≫ HomologicalComplex.homologyMap
          (cokernel.π (Work.Cohomology.inclChains (TopCat.of B) ({b} : Set B))) j :=
    e1.trans (e2.trans e3)
  -- the three factors are isomorphisms
  have hV : IsIso (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains (TopCat.of (cofibre ι)) (cofibreV ι))) j) :=
    isIso_beta_cofibreV ι j hj0
  haveI hVi : IsIso (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains (TopCat.of (cofibre ι)) (cofibreV ι))) j) := hV
  haveI hB' : PathConnectedSpace ↥(TopCat.of B) := hB
  have hb : IsIso (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains (TopCat.of B) ({b} : Set B))) j) :=
    isIso_beta_of_contractible_subspace (TopCat.of B) ({b} : Set B) j (by omega)
  have hc_ : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (cofibre ι)) (TopCat.of B) (TopCat.ofHom c)) j) :=
    Work.Serre.Assembly.serreK2IntSharp c N hπ j hj0 hjN
  have hprod : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (cofibre ι)) (TopCat.of B) (TopCat.ofHom c)) j
      ≫ HomologicalComplex.homologyMap
        (cokernel.π (Work.Cohomology.inclChains (TopCat.of B) ({b} : Set B))) j) :=
    IsIso.comp_isIso' hc_ hb
  have hfg : IsIso (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains (TopCat.of (cofibre ι)) (cofibreV ι))) j
      ≫ HomologicalComplex.homologyMap (psiMap ι c b hc) j) := hsq ▸ hprod
  haveI : IsIso (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains (TopCat.of (cofibre ι)) (cofibreV ι))) j
      ≫ HomologicalComplex.homologyMap (psiMap ι c b hc) j) := hfg
  exact IsIso.of_isIso_comp_left
    (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains (TopCat.of (cofibre ι)) (cofibreV ι))) j)
    (HomologicalComplex.homologyMap (psiMap ι c b hc) j)

end

end Work.RatHurewicz.Cofibre
