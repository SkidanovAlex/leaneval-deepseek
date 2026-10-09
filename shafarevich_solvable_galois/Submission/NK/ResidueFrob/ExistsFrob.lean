import Submission.NK.ResidueFrob.Setup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The existence of a local Frobenius lift at a place

The second field of `NK.FrobeniusBridge.PlaceLevelBridgeCore` is the existence of an element of
the decomposition group which is a local Frobenius lift.  This file shows that it is exactly the
named classical input `NK.LocalAnabelian.ResidueCardInput` (the canonical Frobenius of
`Gal(κ̄/κ)`, together with the Teichmüller normalisation of its action on the roots of unity):
once that element is available, transporting it along the identification `D_A ≃* Gal(κ̄/κ)` is
formal.

Note that this input is *not* derivable from `NK.LocalTame.TameData` alone: the latter contains
`TameStructureInput.exists_frobeniusLift` (an element outside `I_κ`), but says nothing about the
action of that element on the tame inertia, so it does not produce an element acting on the
prime-to-`p` roots of unity by `ζ ↦ ζ ^ q`.  The input `ResidueCardInput` is what the local
structure theory of `Submission/Work/LocalStructure/` provides
(`NK.LocalStructure.TameFrobeniusCore.exists_frob`).
-/

namespace NK.ResidueFrob

open scoped Pointwise Classical

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]
variable {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The existence of a local Frobenius lift at the place `A`**, from the classical input
`NK.LocalAnabelian.ResidueCardInput` (the Frobenius of the local field, normalised through
`κ^ur = κ(μ_{p'})`). -/
theorem exists_frob_of_residueCardInput (A : NK.FrobeniusBridge.FinitePlaceOf K K') {p q : ℕ}
    (h : NK.LocalAnabelian.ResidueCardInput p q (NK.FrobeniusBridge.localField A)
      (NK.FrobeniusBridge.localClosure A)) :
    ∃ (u : Gal(K'/K))
      (hu : u ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1),
      NK.LocalAnabelian.IsFrobeniusFor p q
        (NK.FrobeniusBridge.localGaloisEquiv A ⟨u, hu⟩) := by
  set u₀ : Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1 :=
    (NK.FrobeniusBridge.localGaloisEquiv A).symm h.frob with hu₀
  refine ⟨(u₀ : Gal(K'/K)), u₀.2, ?_⟩
  have hcoe : (⟨(u₀ : Gal(K'/K)), u₀.2⟩ :
      Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1) = u₀ :=
    Subtype.ext rfl
  rw [hcoe, hu₀, MulEquiv.apply_symm_apply]
  exact ⟨h.frob_notMem_inertia, h.actsAsFrobenius⟩

end NK.ResidueFrob
