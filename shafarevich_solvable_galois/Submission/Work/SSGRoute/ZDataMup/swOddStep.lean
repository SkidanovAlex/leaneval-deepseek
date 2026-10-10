import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZSplit.SWClauses
import Submission.Work.SSGRoute.ZSplit.SWFourOddKummer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shared step of the odd-`p` §4 construction: additivity of the Kummer cochain in the element

This module `Submission.Work.SSGRoute.ZDataMup.swOddStep` holds the single lemma which *both* the
node `Submission.Work.SSGRoute.z_data_mup_odd_of_grunwald` and the arithmetic core
`Submission.Work.SSGRoute.ZDataMup.sw_odd_kummer_core` (and its scaffolding
`Submission.Work.SSGRoute.ZDataMup.swCoreDefs`) need from each other's files: the element-wise
additivity of the level-`K` Kummer cochain.

`χ_{a b} = χ_a + χ_b` for `a, b ∈ Kˣ`: the Kummer index of a product is the sum of the Kummer
indices (`Work.SSGRoute.kummerIdx_mul`) once the chosen `p`-th roots are multiplied.  This is the
identity by which the construction of Schmidt–Wingberg §4 — whose final class is the *sum*
`z = z_i + z_N`, i.e. the product of the two Kummer elements — is computed at the places at which
the one-sided vanishing has to be verified.

It lives in its own module (rather than in either of the two files that use it) so that the import
graph stays acyclic: `swCoreDefs` → this module, and the node's file → `sw_odd_kummer_core` →
`swCoreDefs` → this module.
-/

namespace Work.SSGRoute

/-- **The level-`K` Kummer cochain is additive in its argument**: `χ_{a b} = χ_a + χ_b`. -/
theorem nodeKummerCocharZMod_mul {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω] {p : ℕ} [Fact p.Prime]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (a b : (↥K)ˣ) :
    ZSplit.nodeKummerCocharZMod K ζ hζK hζ (a * b) =
      ZSplit.nodeKummerCocharZMod K ζ hζK hζ a +
        ZSplit.nodeKummerCocharZMod K ζ hζK hζ b := by
  have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) p :=
    ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  funext σ
  by_cases hσ : σ ∈ K.fixingSubgroup
  · rw [Pi.add_apply, ZSplit.nodeKummerCocharZMod_apply hσ,
      ZSplit.nodeKummerCocharZMod_apply hσ, ZSplit.nodeKummerCocharZMod_apply hσ,
      kummerCharZMod_apply, kummerCharZMod_apply, kummerCharZMod_apply]
    have hcd : (kummerSqrtUnitZMod (Ω := Ω) p a * kummerSqrtUnitZMod (Ω := Ω) p b) ^ p =
        Units.map (algebraMap ↥K Ω) (a * b) := by
      rw [mul_pow, kummerSqrtUnitZMod_pow, kummerSqrtUnitZMod_pow, map_mul]
    have hstep : kummerIdx p hζ' (a * b) (kummerSqrtUnitZMod (Ω := Ω) p (a * b))
        (kummerSqrtUnitZMod_pow (Ω := Ω) p (a * b))
        (IntermediateField.fixingSubgroupEquiv K ⟨σ, hσ⟩)
        = kummerIdx p hζ' (a * b)
          (kummerSqrtUnitZMod (Ω := Ω) p a * kummerSqrtUnitZMod (Ω := Ω) p b) hcd
          (IntermediateField.fixingSubgroupEquiv K ⟨σ, hσ⟩) :=
      kummerIdx_congr p hζ' (a * b) (kummerSqrtUnitZMod_pow (Ω := Ω) p (a * b)) hcd _
    rw [hstep, kummerIdx_mul p hζ' a b (kummerSqrtUnitZMod (Ω := Ω) p a)
      (kummerSqrtUnitZMod (Ω := Ω) p b) (kummerSqrtUnitZMod_pow (Ω := Ω) p a)
      (kummerSqrtUnitZMod_pow (Ω := Ω) p b) hcd]
  · rw [ZSplit.nodeKummerCocharZMod_of_notMem hσ, Pi.add_apply,
      ZSplit.nodeKummerCocharZMod_of_notMem hσ, ZSplit.nodeKummerCocharZMod_of_notMem hσ,
      add_zero]

end Work.SSGRoute
