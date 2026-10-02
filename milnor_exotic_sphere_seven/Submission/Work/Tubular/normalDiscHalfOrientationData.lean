import Mathlib
import Submission.Work.Tubular.chartedSpace_normalDisc_add
import Submission.Work.Orient.Boundary
import Submission.Work.Tubular.tubeHalfOrientation
import Submission.Work.Tubular.mem_boundary_normalDiscSub_add
import Submission.Work.Tubular.exists_halfOrientationFamily_euclidean
import Submission.Work.Tubular.tubeExcisionNat
import Submission.Work.Tubular.tubeTransferChain

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

/-!
# The transferred family of local generators of the normal disc bundle

This file assembles the data of the half-orientation family of the normal disc bundle
`D_ε(ν)` (`Work.Tubular.exists_halfOrientationFamily_normalDiscSub`) from the Euclidean family
`Work.Tubular.exists_halfOrientationFamily_euclidean`:

* `pieceClass C K hK hKc a'` — the class over a compact piece `K` of the disc bundle obtained by
  excising the Euclidean class `a'` and pushing it forward along the inverse tubular map;
* `transferredClass C γ₀ x hx` — the local generator at an interior point `x`, the image of the
  Euclidean generator `γ₀` at the corresponding point of the open tube;
* `span_transferredClass` — the transferred class is a generator.
-/

open scoped Manifold Topology
open CategoryTheory CategoryTheory.Limits
open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k] {ε : ℝ}

/-- The transferred generator: the ambient local class at the tube point, pushed forward along the
inverse tubular map. -/
noncomputable def transferredClass {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (γ₀ : ∀ y : Euc (8 + k), Work.Orient.LocH (TopCat.of (Euc (8 + k))) (8 + k) y)
    (x : NormalDiscSub E ε) (hx : normalNorm E (x : NormalTotal E) < ε) :
    (Work.Cohomology.relChains (TopCat.of (NormalDiscSub E ε))
      (discRelSub (E := E) ({x} : Set (NormalDiscSub E ε)))).homology (8 + k) :=
  letI : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (excisionMap (E := E) ({x} : Set (NormalDiscSub E ε))) (8 + k)) :=
    isIso_excisionMap_homologyMap C
      (fun q hq => by rw [Set.mem_singleton_iff] at hq; exact hq ▸ hx) isCompact_singleton
  (HomologicalComplex.homologyMap (invChainMap C ({x} : Set (NormalDiscSub E ε))) (8 + k)).hom
    ((CategoryTheory.inv (HomologicalComplex.homologyMap
        (excisionMap (E := E) ({x} : Set (NormalDiscSub E ε))) (8 + k))).hom
      (tubePtClass C γ₀ x hx))

theorem span_transferredClass {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (γ₀ : ∀ y : Euc (8 + k), Work.Orient.LocH (TopCat.of (Euc (8 + k))) (8 + k) y)
    (hgen : ∀ y, Submodule.span ℤ ({γ₀ y} : Set
      (Work.Orient.LocH (TopCat.of (Euc (8 + k))) (8 + k) y)) = ⊤)
    (x : NormalDiscSub E ε) (hx : normalNorm E (x : NormalTotal E) < ε) :
    Submodule.span ℤ ({transferredClass C γ₀ x hx} : Set
      ((Work.Cohomology.relChains (TopCat.of (NormalDiscSub E ε))
        (discRelSub (E := E) ({x} : Set (NormalDiscSub E ε)))).homology (8 + k))) = ⊤ := by
  haveI : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (excisionMap (E := E) ({x} : Set (NormalDiscSub E ε))) (8 + k)) :=
    isIso_excisionMap_homologyMap C
      (fun q hq => by rw [Set.mem_singleton_iff] at hq; exact hq ▸ hx) isCompact_singleton
  rw [transferredClass]
  refine span_top_homologyMap_invChainMap C ({x} : Set (NormalDiscSub E ε))
    (fun q hq => by rw [Set.mem_singleton_iff] at hq; exact hq ▸ hx) isCompact_singleton _ ?_
  exact span_of_surjective_eq_top _
    (((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).2)
    (span_tubePtClass C γ₀ hgen x hx)

/-- The class over a piece `K`, obtained by transferring the ambient class `a'`. -/
noncomputable def pieceClass {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (K : Set (NormalDiscSub E ε)) (hK : ∀ q ∈ K, normalNorm E (q : NormalTotal E) < ε)
    (hKc : IsCompact K)
    (a' : (Work.Cohomology.relChains (TopCat.of (Euc (8 + k)))
      ((tubeImage (E := E) K)ᶜ)).homology (8 + k)) :
    (Work.Cohomology.relChains (TopCat.of (NormalDiscSub E ε))
      (discRelSub (E := E) K)).homology (8 + k) :=
  letI : CategoryTheory.IsIso (HomologicalComplex.homologyMap (excisionMap (E := E) K) (8 + k)) :=
    isIso_excisionMap_homologyMap C hK hKc
  (HomologicalComplex.homologyMap (invChainMap C K) (8 + k)).hom
    ((CategoryTheory.inv (HomologicalComplex.homologyMap (excisionMap (E := E) K) (8 + k))).hom a')


end

end Work.Tubular
