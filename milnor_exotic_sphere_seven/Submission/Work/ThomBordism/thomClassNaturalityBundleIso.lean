import Mathlib
import Submission.Work.Tubular.nonempty_thomClass_of_bundleIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# The Thom class transports along a bundle isomorphism — with its class named

`Work.Tubular.nonempty_thomClass_of_bundleIso` proves that a Thom class of `Z` transports to *some*
Thom class of `Z'` along a bundle isomorphism `e : Z ≅ Z'`; its proof *exhibits* the witness
`(e⁻¹)^*(T.τ)`, but the statement only records existence, so a consumer that has to *compute* with
the transported class (e.g. the pairing computation of the Pontryagin–Thom chapter) cannot use it.

This file states and proves the *named* form:

  `T'.τ = (relCohMap e⁻¹ (Z'∖0) (Z∖0) hf ℤ n).hom T.τ`,

with the membership side condition `hf` of `relCohMap` taken as a *named hypothesis* rather than a
term of the argument list — this is the workaround for the elaborator blow-up recorded in
`Submission/Work/Tubular/PairingNotes.md` §6 (naming the membership argument together with
`Work.Thom.cupMap_transfer_fwdA` reaches a deterministic `isDefEq` timeout at 16M heartbeats; taking
it as a variable keeps the statement small, and it is *always* satisfiable, `e.symm.hom_ne_zero`).
-/

namespace Work.ThomBordism

open Work.TangentClasses

/-- **Thom-class naturality under a bundle isomorphism, with the transported class named.**

For an isomorphism `e : Z ≅ Z'` of real bundles over a common base (arbitrary model fibres and
covers) and a Thom class `T` of `Z`, the class `(e⁻¹)^*(T.τ)` — the pullback of `T.τ` along the
homeomorphism of pairs induced by `e⁻¹` — is a Thom class of `Z'`.  This is the *named* refinement of
`Work.Tubular.nonempty_thomClass_of_bundleIso`, needed whenever the transported class has to be
computed with.

The membership hypothesis `hf` is the side condition of `Work.Thom.relCohMap`; it is always
available (`Work.Thom.BundleIso.symm` and `hom_ne_zero`), and taking it as a variable avoids the
elaborator blow-up of `PairingNotes.md` §6. -/
theorem thomClassNaturalityBundleIso {B : Type} [TopologicalSpace B] {F F' : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {ι ι' : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (Z' : Work.TangentClasses.RealBundle B F' ι')
    (e : Work.Thom.BundleIso Z Z') (T : Work.Thom.ThomClass Z n)
    (hf : ∀ x ∈ Work.Thom.zeroComplementCore Z', e.invTotalSpace x ∈ Work.Thom.zeroComplementCore Z) :
    ∃ T' : Work.Thom.ThomClass Z' n,
      T'.τ = (Work.Thom.relCohMap (e.toHomeomorph.symm : C(Z'.TotalSpace, Z.TotalSpace))
        (Work.Thom.zeroComplementCore Z') (Work.Thom.zeroComplementCore Z) hf ℤ n).hom T.τ := by
  classical
  -- The homeomorphism of pairs, in the direction used by `relCohMap`.
  have hiff : ∀ x : Z'.TotalSpace, x ∈ Work.Thom.zeroComplement Z' ↔
      (e.toHomeomorph.symm x) ∈ Work.Thom.zeroComplement Z := by
    intro x
    constructor
    · intro hx
      exact e.symm.hom_ne_zero hx
    · intro hx
      have h2 : e.toHomeomorph (e.toHomeomorph.symm x) ∈ Work.Thom.zeroComplement Z' :=
        e.hom_ne_zero hx
      rwa [e.toHomeomorph.apply_symm_apply] at h2
  have hbij : ∀ m, Function.Bijective (Work.Thom.relCohMap
      (e.toHomeomorph.symm : C(Z'.TotalSpace, Z.TotalSpace)) (Work.Thom.zeroComplement Z')
      (Work.Thom.zeroComplement Z) hf ℤ m).hom :=
    fun m => Work.Thom.bijective_relCohMap_of_homeomorphA (Work.Thom.zeroComplement Z')
      (Work.Thom.zeroComplement Z) e.toHomeomorph.symm hiff ℤ m
  -- A bundle isomorphism lies over the base: `π ∘ e⁻¹ = π'`.
  have hπ : (Work.Thom.bundleProj Z).comp (e.toHomeomorph.symm : C(Z'.TotalSpace, Z.TotalSpace))
      = Work.Thom.bundleProj Z' := by
    ext p; rfl
  exact ⟨⟨(Work.Thom.relCohMap (e.toHomeomorph.symm : C(Z'.TotalSpace, Z.TotalSpace))
      (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement Z) hf ℤ n).hom T.τ,
      Work.Thom.cupMap_transfer_fwdA (e.toHomeomorph.symm : C(Z'.TotalSpace, Z.TotalSpace))
        (Work.Thom.zeroComplement Z) (Work.Thom.zeroComplement Z') hf hbij
        (Work.Thom.bundleProj Z) (Work.Thom.bundleProj Z') hπ n T.τ T.isThom⟩, rfl⟩

end Work.ThomBordism
