import Mathlib
import Submission.Work.SSGRoute.H9.swPairingValueFrob
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H9

theorem swKummerCochar_kills_levelKernel {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (b : (↥K)ˣ)
    (L : IntermediateField k Ω) [Normal k L]
    (hroot : (Work.SSGRoute.kummerSqrtZMod (K := ↥K) (Ω := Ω) p b : Ω) ∈ L)
    (u : Ω ≃ₐ[k] Ω) (huK : u ∈ K.fixingSubgroup) (_huL : SSGRoute.res k L u = 1) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b u = 0 := by
  rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK)
    (hζ := hζ) (β := b) huK, Work.SSGRoute.kummerCharZMod_apply]
  -- `u` restricts to `1` on `L`, hence fixes `L` pointwise, in particular the chosen root.
  have hfixL : ∀ x ∈ L, u x = x := (AlgEquiv.restrictNormal_eq_one_iff L u).mp _huL
  have hγL : (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p b : Ω) ∈ L := by
    rw [Work.SSGRoute.kummerSqrtUnitZMod_coe]; exact hroot
  -- the Kummer index vanishes because the automorphism fixes the chosen `p`-th root of `b`.
  refine Work.SSGRoute.kummerIdx_eq_zero_of_apply_eq p
    (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) b
    (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p b)
    (Work.SSGRoute.kummerSqrtUnitZMod_pow (Ω := Ω) p b) _ ?_
  show u (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p b : Ω) = _
  exact hfixL _ hγL

end Work.SSGRoute.H9
