import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZConstruction.levelK_kummerCharHom_dictionary
import Submission.Work.SSGRoute.ZDataTwo.SignAdjustment
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p = 2` first element of the escape, made totally positive

`Work.SSGRoute.GrunwaldEscapeCore.kummerFirstElement_noImag` (proved, `p = 2`-ready) produces an
element `a ∈ (↥K)ˣ` realising the datum `g + h A` on the local groups `decomp k A ⊓ G_K` of the
finite place set `T`.  `Work.SSGRoute.ZDataTwo.signAdjustment_mu2` (proved) produces, for an
*arbitrary* `a`, an `s ∈ (↥K)ˣ` whose Kummer character vanishes on those same local groups and such
that `a · s` is *totally positive* (its Kummer character kills every involution of `G_K`).

Composing the two gives the precise input the `p = 2` escape correction needs -- and the input that
`Work.SSGRoute.ZDataTwo.orthogonality_L2K_two` consumes as `ha` + `hapos`:

* `a` realises the datum on the local groups of `T` (`ha`), and
* `a` is totally positive (`hapos`), i.e. `kummerCharZMod a c = 0` for every involution `c` of
  `G_K` -- equivalently, by `ZDataTwo.realPlace_involution_kummerChar_iff`, `a` is positive at every
  real place of `↥K`.

The composition goes through the multiplicativity of the Kummer character in the element,
`Work.SSGRoute.ZConstruction.kummerCharZMod_add`.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataTwo

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **The `p = 2` first element of the escape, totally positive.**  There is `a ∈ (↥K)ˣ` which
realises the datum `g + h A` on the local groups of `T` and whose Kummer character vanishes at every
involution of `G_K` (i.e. `a` is a square at every real place of `↥K`).

This is the `p = 2` strengthening of `GrunwaldEscapeCore.kummerFirstElement_noImag` obtained from
the sign adjustment `ZDataTwo.signAdjustment_mu2`; it is the hypothesis pair `ha` + `hapos` of the
`p = 2` escape orthogonality. -/
theorem firstElement_totallyPositive (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0) :
    ∃ a : (↥K)ˣ,
      (∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a
            (Work.SSGRoute.gesLocalToGalK K σ)) ∧
      (∀ (c : Ω ≃ₐ[k] Ω) (hc : c ∈ K.fixingSubgroup), c ^ 2 = 1 →
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a
          (Work.SSGRoute.gesGalKOfFixing K c hc) = 0) := by
  obtain ⟨a, ha⟩ := Work.SSGRoute.GrunwaldEscapeCore.kummerFirstElement_noImag 2 k Ω K ζ hζ T
    hTfin hTdisj g hg hgc h hh hhc
  obtain ⟨s, hs, hspos⟩ := signAdjustment_mu2 k Ω K ζ hζ T hTfin a
  refine ⟨a * s, ?_, fun c hc hc2 => hspos c hc hc2⟩
  intro A hA σ
  have hadd := Work.SSGRoute.ZConstruction.kummerCharZMod_add (p := 2) (K := K) (Ω := Ω)
    (ζ := ζ) (hζ := hζ) a s (Work.SSGRoute.gesLocalToGalK K σ)
  rw [hadd, hs A hA σ, add_zero]
  exact ha A hA σ

end Work.SSGRoute.ZDataTwo
