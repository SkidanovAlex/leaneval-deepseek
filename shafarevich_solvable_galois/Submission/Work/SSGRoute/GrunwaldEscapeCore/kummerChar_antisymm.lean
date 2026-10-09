import Mathlib
import Submission.Work.SSGRoute.GrunwaldEscapeCore.Vocab
import Submission.Work.SSGRoute.ZConstruction.kummerCharZModAdd
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
import Submission.NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Antisymmetry of the local Kummer pairing

`NOTE_orthogonality_route.md` §3/§6.2.  At a place `𝔭` of `↥K` and for a level `E/↥K` (abelian,
containing the Kummer fields involved), the local Kummer pairing is

  `β(x, y) := χ_y (θ_𝔭 x)`      (`x, y ∈ (↥K)ˣ`),

where `θ_𝔭 : (↥K)ˣ →* Gal(E/K)` is the local Artin factor (a homomorphism, so `β` is additive in
`x` *for free*) and `χ_c` is the global Kummer character of `c` (additive in `c`, so `β` is additive
in `y` *for free*).

The *whole* arithmetic content of the orthogonality of the Grünwald escape is the **diagonal**
`β(c, c) = 0`, i.e. `θ_𝔭 c` acting trivially on the Kummer field `K(c^{1/p})` of `c` — which is
`mem_localNormSubgroup_of_kummerRoot` (`norm_kummerRoot.lean`) together with the kernel clause
`ker θ_𝔭 = localNormSubgroup` of the local Artin factor.

Given the diagonal, the pairing is **antisymmetric** by the algebraic shuffle

  `0 = β(xy, xy) = β(x,x) + β(y,y) + β(x,y) + β(y,x)`,

i.e. `β(x,y) + β(y,x) = 0`.  Antisymmetry — *not* symmetry — is what the orthogonality needs: at a
place `A ∈ T` with `h A ≡ 0` one has `χ_a = g = χ_{b_g}` on `D_A`, i.e. `β(z, a_𝔭) = β(z, (b_g)_𝔭)`
for all `z`, and antisymmetry converts this into `β(a_𝔭, c_𝔭) = β((b_g)_𝔭, c_𝔭)`, which is the
form in which the product formula for the pair `(F_{b_g}, c)` applies.
-/

namespace Work.SSGRoute.GrunwaldEscapeCore

open _root_.SSGRoute

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

/-- **Antisymmetry of the local Kummer pairing at a level.**  If the diagonal `β(c,c) = 0` holds at
the level `E` for `c = x`, `c = y` and `c = x * y`, then the pairing is antisymmetric at `x`, `y`.

The hypothesis `hdiag` is exactly what `mem_localNormSubgroup_of_kummerRoot` supplies (through the
kernel clause of the local Artin factor and the compatibility of the factors across levels); the
content of this lemma is the algebraic shuffle, i.e. that the *alternating* property forces
antisymmetry. -/
theorem kummerCharZMod_antisymm
    (p : ℕ) [Fact p.Prime] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] [IsSepClosure ↥K Ω]
    [DistribMulAction (↥K ≃ₐ[k] ↥K) (ZMod p)]
    [SMulCommClass (↥K ≃ₐ[k] ↥K) (ZMod p) (ZMod p)]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (E : IntermediateField ↥K Ω) [FiniteDimensional ↥K E] [Normal ↥K E]
    (θ : (↥K)ˣ →* (↥E ≃ₐ[↥K] ↥E))
    (hdiag : ∀ c : (↥K)ˣ, NK.LocalAnabelian.kummerField (K' := Ω) p c ≤ E →
      ∀ τ : Ω ≃ₐ[↥K] Ω,
        AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E τ = θ c →
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c τ = 0)
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
  rw [Work.SSGRoute.ZConstruction.kummerCharZMod_apply_mul (ζ := ζ) (hζ := hζ) (x * y) τ σ,
    Work.SSGRoute.ZConstruction.kummerCharZMod_add (ζ := ζ) (hζ := hζ) x y τ,
    Work.SSGRoute.ZConstruction.kummerCharZMod_add (ζ := ζ) (hζ := hζ) x y σ,
    hdiag x hx τ hτ, hdiag y hy σ hσ, add_zero, zero_add] at h0
  linear_combination h0

end Work.SSGRoute.GrunwaldEscapeCore
