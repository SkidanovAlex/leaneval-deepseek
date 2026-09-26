import Submission.Work.Item3.SymFallTwo

open Submission.FreeGroupAut
set_option autoImplicit false

/-!
# Nielsen's generation theorem for `Aut(F_n)`

This module proves `aut_nielsen` — the elementary Nielsen moves generate the
whole automorphism group of the free group — by assembling the machinery of
the reduction (all of it kernel-checked, `[propext, Classical.choice,
Quot.sound]`):

    symFallTwoEnergyStep (n)              (Item3/SymFallTwo.lean)
      ⤳ SymFallTwoEnergyStep n
      ⤳ SymEnergyStepMacro n              (SymEnergy.symEnergyStepMacro_of_symFallTwoEnergyStep)
      ⤳ ∃ γ ∈ AutClosure n, IsSignedPermutation (α * γ) for all α
                                          (SymEnergy.reachable_signed_of_symEnergyStep,
                                           well-founded descent in the
                                           lexicographic measure (N, eEnergySym))
      ⤳ Subgroup.closure (AutGen n) = ⊤   (AssemblyBridge.aut_nielsen_of_reachable_signed,
                                           SignedClosure.signedPermutation_mem_closure).

The statement used to sit (with a `sorry`) in `Submission/Work/Nielsen.lean`;
it is moved here because its proof needs the descent modules, which import
`Nielsen.lean` itself.
-/

namespace Submission.Nielsen

/-- **Nielsen's theorem**: the concrete symmetric generating set `AutGen n`
(single-generator inversions and the right/left transvections with exponent
`±1`) generates the full automorphism group of the free group `F_n`:

    closure(AutGen n) = ⊤. -/
theorem aut_nielsen (n : ℕ) :
    Subgroup.closure (AutGen n : Set (MulAut (FreeGroup (Fin n)))) = ⊤ :=
  aut_nielsen_of_symFallTwoEnergyStep (symFallTwoEnergyStep n)

end Submission.Nielsen
