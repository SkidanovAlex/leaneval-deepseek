import Mathlib.Order.CompletePartialOrder
import Mathlib.RepresentationTheory.Invariants
import Mathlib.NumberTheory.NumberField.Basic
import Submission.NK.CFTLib.Existence.arl_invariants_via_core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
namespace NK.CFTLib.Existence

/-
# The `H⁰`-form of the arithmetic input of Route B

This is the statement `A^G ≤ range(N_N)` of
`Submission/Work/CFTLib/Existence/notes_rep_invariants.lean`: the `Gal(Ω/K)`-invariants of the
idèle class group `C_Ω` are norms for the restriction of the representation to the subgroup
`Nsub`.

The proof is the transfer (Verlagerung) computation `C_K ⊆ N_{Ω/L'}C_Ω` for the cyclic complement
`L' = Ω^{Nsub}` of the fixed field `M' = Ω^{Msub}` of `Msub`, reduced to the Artin-symbol
computation via the idèlic Artin map built from `h : NK.CFTLib.ArtinReciprocityIdeal`; it lives in

* `NK.CFTLib.Existence.arl_normClass_inclusion_core` — the core transfer statement;
* `NK.CFTLib.Existence.arl_invariants_via_core` — this statement, obtained from the core.

The variant proofs `NK.CFTLib.Existence.arl_invariants` and
`...repInvariants_le_range_norm_of_arl` (which exist and are sorry-free) cannot be imported here:
they transitively import `NK.CFTLib.Existence.res_inf_le_ker_res_of_auxiliary`, which imports
*this* file (this lemma is the arithmetic input `harith` of that reduction), so that import would
create a build cycle.  See the docstring of
`Submission/Work/CFTLib/Existence/arl_invariants_via_core.lean` for the cycle-free route.
-/

theorem rep_invariants_le_range_norm_of_auxiliary (h : NK.CFTLib.ArtinReciprocityIdeal)
    {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Field Ω] [NumberField Ω] [Algebra K Ω]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal] [Nsub.Normal] [Fintype Nsub]
    (hN : Nat.card (Gal(Ω/K) ⧸ Nsub) = Nat.card Gal(L/K))
    (hM : Nat.card (Gal(Ω/K) ⧸ Msub) = Nat.card Gal(L/K))
    (hcyc : IsCyclic (Gal(Ω/K) ⧸ Msub))
    (hdisj : IntermediateField.fixedField Msub ⊓ IntermediateField.fixedField Nsub = ⊥)
    (hsup : IntermediateField.fixedField Msub ⊔ IntermediateField.fixedField Nsub = ⊤) :
    (NK.GlobalCFT.IdeleClassGroup.rep K Ω).ρ.invariants ≤
      LinearMap.range ((Rep.res Nsub.subtype (NK.GlobalCFT.IdeleClassGroup.rep K Ω)).ρ.norm) :=
  NK.CFTLib.Existence.arl_invariants_via_core h Msub Nsub hN hM hcyc hdisj hsup

end NK.CFTLib.Existence
