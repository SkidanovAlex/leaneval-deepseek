import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZDataMup.oPairAtDef
import Submission.Work.SSGRoute.ZSplit.FrobeniusValue
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `Σ`-dichotomy, trivial half: a class killing the local group is annihilated by the pairing

`Work.SSGRoute.ZDataMup.OddForm.oPairAt A a b = oPairForm (toClass a) (toClass b)` is
`ZMod p`-bilinear in its two variables (`ZDataMup/mupOddPairLin.lean`).  Hence, if the cochain `b`
is the **zero function on the local group** `decomp k A ⊓ K.fixingSubgroup`, then its class in
`H¹` is `0` (`toClass` is the class of the cochain, and `0` is a coboundary), so
`oPairAt A a b = 0`.

This is the "trivial half" of the `Σ`-dichotomy of the p. 16 computation
(Schmidt–Wingberg, p. 16): at a place `P ∈ Σ` that is *inert* under the involution, the invariant
element `a` is a **local square**, i.e. its Kummer cochain `χ_a` kills the whole local group of `P`
(the residue-field argument of the paper, since `K_P/L_𝔭` is unramified quadratic), and this file
delivers the conclusion `oPairAt P (χ_X) (χ_a) = 0` without any further arithmetic.

The same statement in the `oPairGlob` language is *not* immediate, which is why the `oPairAt`
(descent to `H¹`) form is the useful one here.
-/

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod 2)] [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) (ZMod 2)]

/-- **The class in `H¹` of a cochain vanishing on the local group is zero.** -/
theorem toClass_eq_zero_of_eq_zero_on {A : ValuationSubring Ω}
    (b : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hb : ∀ u ∈ (SSGRoute.decomp k A ⊓ K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)), b u = 0) :
    Work.SSGRoute.toClass 2 k Ω K (ZMod 2)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b = 0 := by
  have hcl : b ∈ Work.SSGRoute.lcCocycles 2 k Ω K (ZMod 2)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) := by
    refine ⟨?_, ?_⟩
    · intro g hg h hh
      rw [hb (g * h) (mul_mem hg hh), hb g hg, hb h hh]
      simp
    · refine ⟨⊤, ?_, ?_⟩
      · show IsOpen ((⊤ : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω))
        rw [Subgroup.coe_top]
        exact isOpen_univ
      · intro g hg u hu huH
        rw [hb (g * u) (mul_mem hg huH), hb g hg]
  rw [Work.SSGRoute.toClass_eq_zero_iff _ _ _ _ _ _ hcl, Work.SSGRoute.mem_coboundaries]
  refine ⟨0, fun g hg => ?_⟩
  rw [hb g hg]
  simp

/-- **The trivial half of the `Σ`-dichotomy.**  If the Kummer cochain of `b ∈ (↥K)ˣ` kills the whole
local group of the finite place `A`, then the local pairing of any cochain `a` against it vanishes. -/
theorem oPairAt_eq_zero_of_kills_localGroup (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (α : (Ω ≃ₐ[k] Ω) → ZMod 2) (b : (↥K)ˣ)
    (hb : ∀ u ∈ (SSGRoute.decomp k A ⊓ K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)),
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b u = 0) :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
      (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
      α (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b) = 0 := by
  have hzero : Work.SSGRoute.toClass 2 k Ω K (ZMod 2)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b) = 0 :=
    toClass_eq_zero_of_eq_zero_on (A := A) _ (fun u hu => hb u hu)
  show Work.SSGRoute.ZDataMup.OddForm.oPairForm (K := K) (p := 2) (k := k) (Ω := Ω)
      (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) hA
      (Work.SSGRoute.toClass 2 k Ω K (ZMod 2) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) α)
      (Work.SSGRoute.toClass 2 k Ω K (ZMod 2) (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b)) = 0
  rw [hzero, map_zero]

end Work.SSGRoute.ZConstruction
