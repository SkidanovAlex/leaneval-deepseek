import Submission.Work.ThomBordism.absThomCompareUniversal
import Submission.Work.ThomBordism.existsComparisonNatural
import Submission.Work.Tubular.ThomComparison
import Submission.Work.ThomBordism.absThomCompareIso
import Submission.Work.ThomBordism.absExcisionHomeoIso
import Submission.Work.ThomBordism.absContractible
import Submission.Work.ThomBordism.absNZRelToAbsBijective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The concrete-vs-generic bridge of the comparison, in the *chain-A* spelling

The assembly of `Work.ThomBordism.NuPairing` (the pairing half of obligation 2) has to combine three
things that the tree states in two mutually incompatible spellings of the canonical comparison
`H^n(Z⁺) ≃ H^n(Z, Z∖0)`:

* the **class description** `Work.ThomBordism.universalClassPullbackPair`
  (`Submission/Work/ThomBordism/absThomCompareUniversal.lean`), stated with the comparison `PhiZ` and
  the *chain-A* definition of the comparison in `Submission/Work/ThomBordism/absThomComparePhiZ.lean` /
  `absThomComparePhi.lean`;
* the **concrete-vs-generic bridge** between TUBULAR's `Work.Tubular.compPull` and the generic
  `compPullZ`, which is proved in `Submission/Work/ThomBordism/tubeBridge.lean` — but that file
  *redefines* `relCohOfAbsZ`/`ThetaZ`, so it cannot be imported together with the chain-A files
  (`Work.ThomBordism.ThetaZ` would be declared twice);
* the **naturality** `Work.ThomBordism.ThetaZ_natural` (chain A) and the local degree.

This file removes the obstruction by re-stating the three bridge facts here, in the spelling of chain
A: they mention only `Work.Tubular.compPull`, `Work.ThomBordism.compPullZ`, `Work.Thom.relCohMap` and
the incidence data `absNZ` / `excSubZ` / `someZ` / `homeoV` / `infComplIncl`, i.e. nothing that depends
on which `ThetaZ` is in scope.  The proofs are those of `tubeBridge.lean`
(`compPull_eq_relCohMap`, `compPullZ_eq_relCohMap`, `compPull_compPullZ_absNZ`), which is the file to
consult for their documentation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory Limits
open Work.TangentClasses
open scoped Topology

namespace Work.ThomBordism

noncomputable section

section ConcreteGeneric

open Work.Tubular

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The concrete comparison, as a single pullback along the map `ν → ν⁺`. -/
theorem compPull_eq_relCohMap {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} (n : ℕ) :
    compPull E n
      = (Work.Thom.relCohMap ((infComplIncl E).comp (homeoV E : C(NormalTotal E, infCompl E)))
          (normalNonzero E) (onePointNonzero E) (fun x hx => (homeoV_mem E x).mp hx) ℤ n).hom := by
  ext γ
  show (Work.Thom.relCohMap (homeoV E : C(NormalTotal E, infCompl E)) (normalNonzero E) (excSub E)
      (fun x hx => (homeoV_mem E x).mp hx) ℤ n).hom
      ((Work.Thom.relCohMap (infComplIncl E) (excSub E) (onePointNonzero E)
        (fun y hy => hy) ℤ n).hom γ)
    = (Work.Thom.relCohMap ((infComplIncl E).comp (homeoV E : C(NormalTotal E, infCompl E)))
      (normalNonzero E) (onePointNonzero E) (fun x hx => (homeoV_mem E x).mp hx) ℤ n).hom γ
  change (ModuleCat.Hom.hom ((Work.Thom.relCohMap (infComplIncl E) (excSub E) (onePointNonzero E)
        (fun y hy => hy) ℤ n) ≫
      (Work.Thom.relCohMap (homeoV E : C(NormalTotal E, infCompl E)) (normalNonzero E) (excSub E)
        (fun x hx => (homeoV_mem E x).mp hx) ℤ n))) γ = _
  rw [Work.Thom.relCohMap_compA (normalNonzero E) (excSub E) (onePointNonzero E)
    (homeoV E) (infComplIncl E) (fun x hx => (homeoV_mem E x).mp hx)
    (fun y hy => hy) (fun x hx => (homeoV_mem E x).mp hx) ℤ n]

/-- The generic comparison, as a single pullback along the map `Z → Z⁺`. -/
theorem compPullZ_eq_relCohMap {ι : Type} (Z : RealBundle V.pt (Work.Tubular.Euc k) ι)
    (N : NormLike Z) (n : ℕ) :
    compPullZ Z N n
      = (Work.Thom.relCohMap (someZ Z) (Work.Thom.zeroComplement Z) (absNZ Z)
          (fun x hx => (some_mem_absNZ Z x).mpr hx) ℤ n).hom := by
  ext γ
  show (Work.Thom.relCohMap (someHomeoZ Z) (Work.Thom.zeroComplement Z) (excSubZ Z)
      (fun x hx => (some_mem_excSubZ Z x).mp hx) ℤ n).hom
      ((Work.Thom.relCohMap (infZIncl Z) (excSubZ Z) (absNZ Z) (fun y hy => hy) ℤ n).hom γ)
    = (Work.Thom.relCohMap (someZ Z) (Work.Thom.zeroComplement Z) (absNZ Z)
      (fun x hx => (some_mem_absNZ Z x).mpr hx) ℤ n).hom γ
  change (ModuleCat.Hom.hom ((Work.Thom.relCohMap (infZIncl Z) (excSubZ Z) (absNZ Z)
        (fun y hy => hy) ℤ n) ≫
      (Work.Thom.relCohMap (someHomeoZ Z) (Work.Thom.zeroComplement Z) (excSubZ Z)
        (fun x hx => (some_mem_excSubZ Z x).mp hx) ℤ n))) γ = _
  rw [Work.Thom.relCohMap_compA (Work.Thom.zeroComplement Z) (excSubZ Z) (absNZ Z)
    (someHomeoZ Z) (infZIncl Z) (fun x hx => (some_mem_excSubZ Z x).mp hx)
    (fun y hy => hy) (fun x hx => (some_mem_absNZ Z x).mpr hx) ℤ n]
  rfl

/-- **The concrete comparison is the generic one** (see the section comment). -/
theorem compPull_compPullZ_absNZ {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    {ι : Type} (Z : RealBundle V.pt (Work.Tubular.Euc k) ι) (N : NormLike Z)
    (ψ : Z.TotalSpace ≃ₜ NormalTotal E)
    (hmemψ : ∀ p ∈ normalNonzero E, ψ.symm p ∈ Work.Thom.zeroComplement Z)
    (Ψ₁ : OnePoint Z.TotalSpace ≃ₜ OnePoint (NormalTotal E))
    (hΨ₁ : ∀ p : Z.TotalSpace, Ψ₁ (OnePoint.some p) = OnePoint.some (ψ p))
    (hmemΨ : ∀ x ∈ onePointNonzero E, Ψ₁.symm x ∈ absNZ Z)
    (n : ℕ) (β : Work.Thom.RelCoh ℤ n (OnePoint Z.TotalSpace) (absNZ Z)) :
    compPull E n
        ((Work.Thom.relCohMap Ψ₁.symm (onePointNonzero E) (absNZ Z) hmemΨ ℤ n).hom β)
      = (Work.Thom.relCohMap ψ.symm (normalNonzero E) (Work.Thom.zeroComplement Z)
          hmemψ ℤ n).hom (compPullZ Z N n β) := by
  rw [compPull_eq_relCohMap (V := V) (k := k) (E := E) n]
  -- the two `relCohMap`s compose
  have hstep : (Work.Thom.relCohMap ((infComplIncl E).comp (homeoV E : C(NormalTotal E, infCompl E)))
        (normalNonzero E) (onePointNonzero E) (fun x hx => (homeoV_mem E x).mp hx) ℤ n).hom
        ((Work.Thom.relCohMap Ψ₁.symm (onePointNonzero E) (absNZ Z) hmemΨ ℤ n).hom β)
      = (Work.Thom.relCohMap
          (((Ψ₁.symm : C(OnePoint (NormalTotal E), OnePoint Z.TotalSpace)).comp
            ((infComplIncl E).comp (homeoV E : C(NormalTotal E, infCompl E)))))
          (normalNonzero E) (absNZ Z)
          (fun x hx => hmemΨ _ (by simpa using (homeoV_mem E x).mp hx)) ℤ n).hom β := by
    change (ModuleCat.Hom.hom ((Work.Thom.relCohMap Ψ₁.symm (onePointNonzero E) (absNZ Z) hmemΨ ℤ n) ≫
      (Work.Thom.relCohMap ((infComplIncl E).comp (homeoV E : C(NormalTotal E, infCompl E)))
        (normalNonzero E) (onePointNonzero E)
        (fun x hx => (homeoV_mem E x).mp hx) ℤ n))) β = _
    rw [Work.Thom.relCohMap_compA (normalNonzero E) (onePointNonzero E) (absNZ Z)
      ((infComplIncl E).comp (homeoV E : C(NormalTotal E, infCompl E)))
      (Ψ₁.symm : C(OnePoint (NormalTotal E), OnePoint Z.TotalSpace))
      (fun x hx => (homeoV_mem E x).mp hx) hmemΨ
      (fun x hx => hmemΨ _ (by simpa using (homeoV_mem E x).mp hx)) ℤ n]
  rw [hstep]
  -- the generic side, as a single `relCohMap`
  rw [compPullZ_eq_relCohMap (Z := Z) N n]
  have hstep2 : (Work.Thom.relCohMap ψ.symm (normalNonzero E) (Work.Thom.zeroComplement Z)
        hmemψ ℤ n).hom
        ((Work.Thom.relCohMap (someZ Z) (Work.Thom.zeroComplement Z) (absNZ Z)
          (fun x hx => (some_mem_absNZ Z x).mpr hx) ℤ n).hom β)
      = (Work.Thom.relCohMap ((someZ Z).comp (ψ.symm : C(NormalTotal E, Z.TotalSpace)))
          (normalNonzero E) (absNZ Z)
          (fun x hx => (some_mem_absNZ Z _).mpr (hmemψ x hx)) ℤ n).hom β := by
    change (ModuleCat.Hom.hom ((Work.Thom.relCohMap (someZ Z) (Work.Thom.zeroComplement Z) (absNZ Z)
        (fun x hx => (some_mem_absNZ Z x).mpr hx) ℤ n) ≫
      (Work.Thom.relCohMap ψ.symm (normalNonzero E) (Work.Thom.zeroComplement Z) hmemψ ℤ n))) β = _
    rw [Work.Thom.relCohMap_compA (normalNonzero E) (Work.Thom.zeroComplement Z) (absNZ Z)
      (ψ.symm : C(NormalTotal E, Z.TotalSpace)) (someZ Z) hmemψ
      (fun x hx => (some_mem_absNZ Z x).mpr hx)
      (fun x hx => (some_mem_absNZ Z _).mpr (hmemψ x hx)) ℤ n]
  rw [hstep2]
  -- the two maps agree
  have hfun : ((Ψ₁.symm : C(OnePoint (NormalTotal E), OnePoint Z.TotalSpace)).comp
        ((infComplIncl E).comp (homeoV E : C(NormalTotal E, infCompl E))))
      = (someZ Z).comp (ψ.symm : C(NormalTotal E, Z.TotalSpace)) := by
    ext p
    have h2 : Ψ₁ (OnePoint.some (ψ.symm p)) = OnePoint.some p := by
      rw [hΨ₁ (ψ.symm p), ψ.apply_symm_apply]
    simp only [ContinuousMap.comp_apply, someZ_apply, infComplIncl_apply]
    change Ψ₁.symm (OnePoint.some p) = OnePoint.some (ψ.symm p)
    apply Ψ₁.injective
    rw [Ψ₁.apply_symm_apply]
    exact h2.symm
  exact congrArg (fun (φ : Work.Thom.RelCoh ℤ n (OnePoint Z.TotalSpace) (absNZ Z) ⟶
      Work.Thom.RelCoh ℤ n (NormalTotal E) (normalNonzero E)) => ModuleCat.Hom.hom φ β)
    (Work.Thom.relCohMap_congrA (normalNonzero E) (absNZ Z) hfun _ _ ℤ n)

end ConcreteGeneric

end

end Work.ThomBordism
