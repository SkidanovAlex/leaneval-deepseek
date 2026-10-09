import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.RealPlaceInvolution
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Total positivity from positivity at all real places (`p = 2`)

The archimedean half of the *sign adjustment* of the `p = 2` escape construction.  A class
`b ∈ (↥K)ˣ` whose images at every real place of `↥K` are positive kills *every* involution of
`G_K = Gal(Ω/K)`: by the Artin--Schreier dictionary at the intermediate level
(`Work.SSGRoute.ZDataTwo.realPlace_involution_kummerChar_iff`, proved in
`ZDataTwo/RealPlaceInvolution.lean`) each non-trivial involution of `Gal(Ω/K)` is the conjugation at
one of those real places, and the Kummer character of `b` vanishes there exactly when `b` is not
negative.

This is the reduction of the second conjunct of `Work.SSGRoute.ZDataTwo.signAdjustment_mu2` (and of
the total-positivity conjunct of `Work.SSGRoute.ZDataTwo.Mu2EscapeCorrection`) to the
*element-level* statement "`b` is positive at every real place", which is what the sign-adjustment
tools (`NK.CFTLib.Arl.exists_integral_sign_adjust` and the modulus version in
`NK/NUV2/RouteB/RayModulus`) produce.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataTwo

open _root_.SSGRoute

/-- **Positivity at every real place makes the Kummer character vanish at every involution.** -/
theorem kummerCharZMod_eq_zero_of_forall_not_isNegAt (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2) (b : (↥K)ˣ)
    (hb : ∀ w : NumberField.InfinitePlace ↥K, w.IsReal → ¬ IsNegAt w b) :
    ∀ (c : Ω ≃ₐ[k] Ω) (hc : c ∈ K.fixingSubgroup), c ^ 2 = 1 →
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ b
        (Work.SSGRoute.gesGalKOfFixing K c hc) = 0 := by
  classical
  haveI : NumberField ↥K := NumberField.of_module_finite k ↥K
  intro c hc hc2
  by_cases hc1 : c = 1
  · -- the identity involution: every Kummer character vanishes there
    subst hc1
    have hone : Work.SSGRoute.gesGalKOfFixing K (1 : Ω ≃ₐ[k] Ω) hc = 1 :=
      map_one (IntermediateField.fixingSubgroupEquiv K)
    rw [hone, Work.SSGRoute.kummerCharZMod_apply]
    exact Work.SSGRoute.kummerIdx_one 2 hζ b _ _
  · -- a non-trivial involution is the conjugation at a real place
    obtain ⟨w, hwreal, hw⟩ :=
      realPlace_involution_kummerChar_iff k Ω K ζ hζ c hc hc2 hc1
    have hto : Work.SSGRoute.gesGalKOfFixing K c hc =
        (IntermediateField.fixingSubgroupEquiv K) ⟨c, hc⟩ := rfl
    rw [hto, hw b]
    exact hb w hwreal

end Work.SSGRoute.ZDataTwo
