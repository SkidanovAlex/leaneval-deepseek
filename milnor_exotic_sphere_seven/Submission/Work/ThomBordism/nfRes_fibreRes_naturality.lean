import Mathlib
import Submission.Work.ThomBordism.orientedFibreGen
import Submission.Work.ThomBordism.fibreRes_relCohMap
import Submission.Work.Tubular.exists_euclidean_normalBundle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.ThomBordism

noncomputable section

/-!
# Naturality of the fibre restriction of the normal Thom class

This is the normal-bundle instance of `Work.ThomBordism.fibreRes_relCohMap`, but stated for the
*concrete* fibre pairs appearing in the last mile of `Work.ThomBordism.thomRational`: the fibre
`nfSet E x` of the normal total space `Work.Tubular.NormalTotal E` over `x` (with punctured part
`nfPunct E x`, inclusion `nfIncl E x`) and the abstract fibre `fibre Z x` of the bundle `Z` over
`V.pt` (with punctured part `fibrePunctSub Z x`, inclusion `fibreIncl Z x`).

Both sides of the identity are obtained by pulling a class of the Thom pair back along a map of
pairs into `(Z.TotalSpace, zeroComplement Z) → (NormalTotal E, normalNonzero E)`; the two composites
`nfIncl ∘ e` and `φ ∘ fibreIncl` agree by `he`, so the statement is pure functoriality of
`Work.Thom.relCohMap` (`relCohMap_compA` + `relCohMap_congrA`).  The general form is abstracted in
`Work.ThomBordism.relCohMap_fibreRes_naturality_gen` below, so that the target follows by
instantiation.
-/

/-- **Abstract naturality of a fibre restriction.**  For a map of pairs `F : (X,A) → (Y,B)`, a
"fibre" `P ⊆ S` of `X` with inclusion `inc : S → X` and a "fibre" `Q ⊆ T` of `Y` with inclusion
`incn : T → Y`, together with a map `ee : S → T` of the two fibre pairs over which `F` and `incn`
agree, the pullback of a relative class `σ` and the restriction to the fibre commute. -/
theorem relCohMap_fibreRes_naturality_gen {X Y S T : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace S] [TopologicalSpace T]
    (A : Set X) (B : Set Y) (P : Set S) (Q : Set T)
    (inc : C(S, X)) (hinc : ∀ p ∈ P, inc p ∈ A)
    (incn : C(T, Y)) (hincn : ∀ p ∈ Q, incn p ∈ B)
    (F : C(X, Y)) (hF : ∀ p ∈ A, F p ∈ B)
    (ee : C(S, T)) (he : ∀ p, incn (ee p) = F (inc p))
    (hpe : ∀ p, p ∈ P ↔ ee p ∈ Q)
    (n : ℕ) (σ : Work.Thom.RelCoh ℤ n Y B) :
    (ModuleCat.Hom.hom (Work.Thom.relCohMap ee P Q (fun p hp => (hpe p).mp hp) ℤ n))
        ((ModuleCat.Hom.hom (Work.Thom.relCohMap incn Q B hincn ℤ n)) σ)
      = (ModuleCat.Hom.hom (Work.Thom.relCohMap inc P A hinc ℤ n))
        ((ModuleCat.Hom.hom (Work.Thom.relCohMap F A B hF ℤ n)) σ) := by
  have he' : ∀ p ∈ P, ee p ∈ Q := fun p hp => (hpe p).mp hp
  have h1 : ∀ p ∈ P, incn (ee p) ∈ B := fun p hp => hincn (ee p) (he' p hp)
  have h2 : ∀ p ∈ P, F (inc p) ∈ B := fun p hp => hF (inc p) (hinc p hp)
  have hL : (ModuleCat.Hom.hom (Work.Thom.relCohMap ee P Q he' ℤ n))
      ((ModuleCat.Hom.hom (Work.Thom.relCohMap incn Q B hincn ℤ n)) σ)
      = (ModuleCat.Hom.hom (Work.Thom.relCohMap (incn.comp ee) P B h1 ℤ n)) σ := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp (Work.Thom.relCohMap incn Q B hincn ℤ n)
      (Work.Thom.relCohMap ee P Q he' ℤ n),
      Work.Thom.relCohMap_compA P Q B ee incn he' hincn h1 ℤ n]
  have hR : (ModuleCat.Hom.hom (Work.Thom.relCohMap inc P A hinc ℤ n))
      ((ModuleCat.Hom.hom (Work.Thom.relCohMap F A B hF ℤ n)) σ)
      = (ModuleCat.Hom.hom (Work.Thom.relCohMap (F.comp inc) P B h2 ℤ n)) σ := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp (Work.Thom.relCohMap F A B hF ℤ n)
      (Work.Thom.relCohMap inc P A hinc ℤ n),
      Work.Thom.relCohMap_compA P A B inc F hinc hF h2 ℤ n]
  rw [hL, hR]
  have hmap : incn.comp ee = F.comp inc := by
    apply ContinuousMap.ext
    intro p
    exact he p
  exact congrArg (fun m => (ModuleCat.Hom.hom m) σ)
    (Work.Thom.relCohMap_congrA (f := incn.comp ee) (f' := F.comp inc) P B hmap h1 h2 ℤ n)

end

theorem nfRes_fibreRes_naturality {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ι : Type}
    (Z : Work.TangentClasses.RealBundle V.pt (Work.Tubular.Euc k) ι)
    (φ : Z.TotalSpace ≃ₜ Work.Tubular.NormalTotal E)
    (hproj : ∀ p : Z.TotalSpace, Work.Tubular.NormalTotal.proj (φ p) = p.1)
    (hmem : ∀ p ∈ Work.Thom.zeroComplement Z, φ p ∈ Work.Tubular.normalNonzero E)
    (x : V.pt)
    (e : ↥(Work.ThomBordism.fibre Z x) ≃ₜ ↥(Work.ThomBordism.nfSet E x))
    (he : ∀ p : ↥(Work.ThomBordism.fibre Z x),
      ((e p : ↥(Work.ThomBordism.nfSet E x)) : Work.Tubular.NormalTotal E)
        = φ (p : Z.TotalSpace))
    (hpe : ∀ p : ↥(Work.ThomBordism.fibre Z x),
      p ∈ Work.ThomBordism.fibrePunctSub Z x ↔ e p ∈ Work.ThomBordism.nfPunct E x)
    (W : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E)) :
    (ModuleCat.Hom.hom (Work.Thom.relCohMap (e : C(↥(Work.ThomBordism.fibre Z x),
        ↥(Work.ThomBordism.nfSet E x))) (Work.ThomBordism.fibrePunctSub Z x)
        (Work.ThomBordism.nfPunct E x) (fun p hp => (hpe p).mp hp) ℤ k))
      (Work.ThomBordism.nfRes E x k W)
    = Work.ThomBordism.fibreRes Z x k
        ((ModuleCat.Hom.hom (Work.Thom.relCohMap (φ : C(Z.TotalSpace, Work.Tubular.NormalTotal E))
          (Work.Thom.zeroComplement Z) (Work.Tubular.normalNonzero E) hmem ℤ k)) W) := by
  exact relCohMap_fibreRes_naturality_gen (Work.Thom.zeroComplement Z)
    (Work.Tubular.normalNonzero E) (Work.ThomBordism.fibrePunctSub Z x)
    (Work.ThomBordism.nfPunct E x) (Work.ThomBordism.fibreIncl Z x)
    (Work.ThomBordism.fibreIncl_mem Z x) (Work.ThomBordism.nfIncl E x)
    (Work.ThomBordism.nfIncl_mem E x) (φ : C(Z.TotalSpace, Work.Tubular.NormalTotal E)) hmem
    (e : C(↥(Work.ThomBordism.fibre Z x), ↥(Work.ThomBordism.nfSet E x)))
    (fun p => he p) hpe k W

end Work.ThomBordism
