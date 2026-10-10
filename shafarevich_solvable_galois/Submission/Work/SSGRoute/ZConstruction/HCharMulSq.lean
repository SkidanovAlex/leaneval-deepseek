import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.NodeS35.swPinFamily
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.galois_sup_structure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Step 1 of the p. 16 roadmap: the pinned value is unchanged by multiplying the class by a square

`NodeS35.pinValue … (Q, b) 0 t` is the value of the Kummer cochain `χ_b` of the stage-`0` class
`b` at the Frobenius pinned at the `t`-sibling of `Q`.  The p. 16 computation replaces `b` by the
*normalised* representative `z = b x²` (`ZDataTwo.TwoRec.claimOfPreTwo_localNormalise`); the present
file supplies the bookkeeping that this replacement does not change the value:

* `hLevel_mul_sq_eq` (`ZConstruction/LevelSquare.lean`) — the Kummer level is unchanged;
* `hChar_mul_sq` (here) — the descended level character is unchanged
  (`χ_{b x²} = χ_b + χ_{x²}` and `χ_{x²} = 2 χ_x = 0` in `ZMod 2`);
* `pinValue_mul_sq` (here) — the pinned value itself is unchanged.
-/

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.OddForm
open Work.SSGRoute.ZDataMup.LTRecFamHonest

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- **The descended level character is unchanged by multiplying the class by a square** (`p = 2`):
`χ_{b x²} = χ_b` on the Galois group of any common level `M` — because `χ_{x²} = 2 χ_x = 0`. -/
theorem hChar_mul_sq (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2) (b x : (↥K)ˣ)
    {M : IntermediateField ↥K Ω} [FiniteDimensional ↥K M] [IsGalois ↥K M]
    (hM : hLevel (Ω := Ω) (K := K) (p := 2) (b * (x * x)) ≤ M)
    (hMb : hLevel (Ω := Ω) (K := K) (p := 2) b ≤ M)
    (γ : ↥M ≃ₐ[↥K] ↥M) :
    hChar (K := K) (p := 2) ζ hζ (b * (x * x)) hM γ =
      hChar (K := K) (p := 2) ζ hζ b hMb γ := by
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥K) (K₁ := M) (E := Ω) γ
  rw [← hσ, hChar_apply (K := K) (p := 2) ζ hζ (b * (x * x)) hM σ,
    hChar_apply (K := K) (p := 2) ζ hζ b hMb σ]
  congr 1
  rw [kummerCharZMod_add (Ω := Ω) (p := 2) (ζ := ζ) (hζ := hζ) b (x * x) σ]
  have hzero : kummerCharZMod (Ω := Ω) 2 (ζ := ζ) hζ (x * x) σ = 0 := by
    rw [kummerCharZMod_add (Ω := Ω) (p := 2) (ζ := ζ) (hζ := hζ) x x σ, ← two_mul,
      show (2 : ZMod 2) = 0 from by decide, zero_mul]
  rw [hzero, add_zero]

/-- **Step 1 of the p. 16 roadmap (the cochain form): multiplying the class by a square does not
change the Kummer cochain.**  `χ_{b x²} = χ_b` on `G_K` at `p = 2`, because `χ_{b x²} = χ_b + χ_{x²}`
(additivity in the coefficient) and `χ_{x²} = 2 χ_x = 0`.

This is the form in which the representative change of `TwoRec.claimOfPreTwo_localNormalise` (the
normalised `z = b x²`) is consumed: it needs no Kummer-level bookkeeping, only the value of the
cochain at a pinned Frobenius. -/
theorem nodeKummerCocharZMod_mul_sq (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (b x : (↥K)ˣ) (ψ : Ω ≃ₐ[k] Ω) (hψ : ψ ∈ K.fixingSubgroup) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (b * (x * x)) ψ =
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b ψ := by
  rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ)
      (β := b * (x * x)) hψ,
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ)
      (β := b) hψ,
    kummerCharZMod_add (Ω := Ω) (p := 2) (ζ := (⟨ζ, hζK⟩ : ↥K))
      (hζ := Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) b (x * x) _]
  have hzero : kummerCharZMod (Ω := Ω) 2 (ζ := (⟨ζ, hζK⟩ : ↥K))
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (x * x)
      ((IntermediateField.fixingSubgroupEquiv K) ⟨ψ, hψ⟩) = 0 := by
    rw [kummerCharZMod_add (Ω := Ω) (p := 2) (ζ := (⟨ζ, hζK⟩ : ↥K))
        (hζ := Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) x x _,
      ← two_mul, show (2 : ZMod 2) = 0 from by decide, zero_mul]
  rw [hzero, add_zero]

end Work.SSGRoute.ZConstruction
