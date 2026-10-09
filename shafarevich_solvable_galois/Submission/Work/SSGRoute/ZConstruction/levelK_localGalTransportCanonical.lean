import Mathlib
import Submission.Work.SSGRoute.ZDataMup.LT_localGaloisTransport
import Submission.Work.SSGRoute.lcHoms_congr
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The canonical transport of the level-`K` local characters to the completion

`Work.SSGRoute.ZDataMup.LT_lcHoms_levelK_localGalois` supplies, for a finite place `A` and the
canonical homeomorphism `mupLocalGalEquiv A hAK : ↥(decomp (k := ↥K) A) ≃* Gal(κ̄_A/κ_A)`, a
*`Nonempty`* statement: there exists a multiplicative equivalence between the locally constant
characters of the level-`K` local group and those of the absolute Galois group of the completion.
It is obtained from `lcHoms_congr`, whose witness is the explicit map
`χ ↦ χ.comp e.symm.toMonoidHom`.

For the place-transport of the canonical pairing the *chosen* witness matters, so this file writes
that map out as an explicit `def` `levelKLocalGalTransport` with the computation rule
`levelKLocalGalTransport_apply` (a `rfl`), instead of a `Classical.choice` of the `Nonempty`.  This
is the same move as `levelK_modelIsoCanonical.lean` performed for the model identification. -/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  {A : ValuationSubring Ω}

/-- **The canonical transport of the level-`K` local characters to the completion**, as an explicit
multiplicative equivalence `χ ↦ χ.comp (mupLocalGalEquiv A hAK).symm.toMonoidHom` (the witness
constructed by `lcHoms_congr`), rather than a `Classical.choice` of the `Nonempty` supplied by
`LT_lcHoms_levelK_localGalois`. -/
noncomputable def levelKLocalGalTransport (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) :
    ↥(Work.SSGRoute.lcHoms p ↥(_root_.SSGRoute.decomp (k := ↥K) A)) ≃*
      ↥(Work.SSGRoute.lcHoms p
        ((SeparableClosure (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)) ≃ₐ[
          Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK]
          (SeparableClosure (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)))) where
  toFun χ :=
    ⟨χ.1.comp (Work.SSGRoute.ZDataMup.mupLocalGalEquiv (p := p) (k := k) (Ω := Ω) (K := K)
        A hAK).symm.toMonoidHom,
      χ.2.comp_continuous
        ((Work.SSGRoute.ZDataMup.mupLocalGalEquiv (p := p) (k := k) (Ω := Ω) (K := K) A hAK).toEquiv
          |>.continuous_symm_iff.mpr
          (Work.SSGRoute.ZDataMup.isHomeomorph_mupLocalGalEquiv (p := p) (k := k) (Ω := Ω)
            (K := K) A hAK).isOpenMap)⟩
  invFun ξ :=
    ⟨ξ.1.comp (Work.SSGRoute.ZDataMup.mupLocalGalEquiv (p := p) (k := k) (Ω := Ω) (K := K)
        A hAK).toMonoidHom,
      ξ.2.comp_continuous
        (Work.SSGRoute.ZDataMup.isHomeomorph_mupLocalGalEquiv (p := p) (k := k) (Ω := Ω)
          (K := K) A hAK).continuous⟩
  left_inv χ := by ext g; simp
  right_inv ξ := by ext g; simp
  map_mul' χ ψ := by ext g; simp

/-- **The computation rule of the canonical transport**: it is the map
`χ ↦ χ.comp (mupLocalGalEquiv A hAK).symm.toMonoidHom` (definitional). -/
theorem levelKLocalGalTransport_apply (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (χ : ↥(Work.SSGRoute.lcHoms p ↥(_root_.SSGRoute.decomp (k := ↥K) A))) :
    (levelKLocalGalTransport (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hAK χ).1 =
      χ.1.comp (Work.SSGRoute.ZDataMup.mupLocalGalEquiv (p := p) (k := k) (Ω := Ω) (K := K)
        A hAK).symm.toMonoidHom := rfl

/-- The canonical transport is the witness of the `Nonempty` statement of
`LT_lcHoms_levelK_localGalois`. -/
theorem levelKLocalGalTransport_mem (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) :
    Nonempty
      (↥(Work.SSGRoute.lcHoms p ↥(_root_.SSGRoute.decomp (k := ↥K) A)) ≃*
        ↥(Work.SSGRoute.lcHoms p
          ((SeparableClosure (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)) ≃ₐ[
            Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK]
            (SeparableClosure (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK))))) :=
  ⟨levelKLocalGalTransport (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hAK⟩

end

end Work.SSGRoute.ZConstruction
