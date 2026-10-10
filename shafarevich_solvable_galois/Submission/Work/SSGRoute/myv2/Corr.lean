import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.GrunwaldEscapeCore.Vocab
import Submission.Work.SSGRoute.ZConstruction.kummerCharZModAdd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The antisymmetry of the local Kummer pairing, corrected by a "correction element"

`GrunwaldEscapeCore.kummerCharZMod_antisymm` derives the antisymmetry
`χ_y τ + χ_x σ = 0` from the *vanishing* of the diagonal `χ_c τ = 0` for `τ` a lift of the local
factor of `c`.

For `p = 2` the diagonal is **not** zero: the norm of the `p`-th root `α` of `c` is `-c`, so the
local factor of `c` is that of `-c` inverted, i.e. the local factor of `-1`.  The correct general
hypothesis is therefore that *there is a fixed element* `σ₀` with

  `χ_c τ = χ_c σ₀`   for every `c` whose Kummer field lies in the level `E` and every lift `τ` of
  the local factor of `c`

(odd `p`: `σ₀ = 1`, since the diagonal vanishes; `p = 2`: `σ₀` a lift of the local factor of `-1`).
The algebraic shuffle below shows that the antisymmetry `χ_y τ + χ_x σ = 0` still holds: the
corrections at `x`, `y` and `x y` cancel because `χ_{xy} = χ_x + χ_y` everywhere.
-/

namespace Work.SSGRoute.N2v2

open _root_.SSGRoute

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

/-- **Antisymmetry of the local Kummer pairing, with a correction element.**  If there is `σ₀` such
that `χ_c` is constant on the lifts of the local factor `θ c` (with value `χ_c σ₀`) for every `c`
whose Kummer field lies in `E`, then the pairing `β(x,y) = χ_y(τ)` (`τ` a lift of `θ x`) is
antisymmetric: `χ_y τ + χ_x σ = 0`. -/
theorem kummerCharZMod_pairing_antisymm
    (p : ℕ) [Fact p.Prime] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] [IsSepClosure ↥K Ω]
    [DistribMulAction (↥K ≃ₐ[k] ↥K) (ZMod p)]
    [SMulCommClass (↥K ≃ₐ[k] ↥K) (ZMod p) (ZMod p)]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (E : IntermediateField ↥K Ω) [FiniteDimensional ↥K E] [Normal ↥K E]
    (θ : (↥K)ˣ →* (↥E ≃ₐ[↥K] ↥E)) (σ₀ : Ω ≃ₐ[↥K] Ω)
    (hdiag : ∀ c : (↥K)ˣ, NK.LocalAnabelian.kummerField (K' := Ω) p c ≤ E →
      ∀ τ : Ω ≃ₐ[↥K] Ω,
        AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E τ = θ c →
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c τ =
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ₀)
    (x y : (↥K)ˣ)
    (hx : NK.LocalAnabelian.kummerField (K' := Ω) p x ≤ E)
    (hy : NK.LocalAnabelian.kummerField (K' := Ω) p y ≤ E)
    (hxy : NK.LocalAnabelian.kummerField (K' := Ω) p (x * y) ≤ E)
    (τ σ : Ω ≃ₐ[↥K] Ω)
    (hτ : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E τ = θ x)
    (hσ : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ = θ y) :
    Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ y τ +
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ x σ = 0 := by
  have hxyτσ : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E (τ * σ) = θ (x * y) := by
    rw [map_mul, map_mul, hτ, hσ]
  have h0 := hdiag (x * y) hxy (τ * σ) hxyτσ
  have h2 := hdiag x hx τ hτ
  have h3 := hdiag y hy σ hσ
  rw [Work.SSGRoute.ZConstruction.kummerCharZMod_apply_mul (ζ := ζ) (hζ := hζ) (x * y) τ σ,
    Work.SSGRoute.ZConstruction.kummerCharZMod_add (ζ := ζ) (hζ := hζ) x y τ,
    Work.SSGRoute.ZConstruction.kummerCharZMod_add (ζ := ζ) (hζ := hζ) x y σ,
    Work.SSGRoute.ZConstruction.kummerCharZMod_add (ζ := ζ) (hζ := hζ) x y σ₀,
    h3, h2] at h0
  linear_combination h0

end Work.SSGRoute.N2v2
