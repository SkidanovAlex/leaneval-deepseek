import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Submission.Work.SSGRoute.ZDataTwo.kummerCochar_conjElem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup.LocalUnramified

theorem kummerCharZMod_eq_zero_iff_apply_sqrt
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p) (a : Kˣ) (σ : Ω ≃ₐ[K] Ω) :
    Work.SSGRoute.kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ a σ = 0 ↔
      σ (Work.SSGRoute.kummerSqrtZMod (Ω := Ω) p a) =
        Work.SSGRoute.kummerSqrtZMod (Ω := Ω) p a := by
  rw [Work.SSGRoute.kummerCharZMod_apply]
  exact Work.SSGRoute.kummerIdx_eq_zero_iff_apply_eq p hζ a
    (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p a)
    (Work.SSGRoute.kummerSqrtUnitZMod_pow (Ω := Ω) p a) σ

end Work.SSGRoute.ZDataMup.LocalUnramified
