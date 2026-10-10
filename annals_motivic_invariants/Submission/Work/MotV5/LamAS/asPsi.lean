import Mathlib
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.LamAS.asML
import Submission.Work.MotV5.LamAS.Setup
import Submission.Work.MotV5.LamAS.shift_of_pow_five_sub_self
import Submission.Work.MotV5.LamAS.asRootField_galois_basic
import Submission.Work.MotV5.coeffAut
import Submission.Work.MotV5.LamAS.asIota_range
import Submission.Work.MotV5.RigAS.twistFieldTrue_sup_asRoot

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# The twisted Galois action of the Artin–Schreier LAM node, on the model `M = L(E)`

With `K = RatFunc 𝕜`, `L = asL2 f₁ f₂ ⊆ Kb 𝕜` the two-root Artin–Schreier field and
`M = asML D f₁ f₂ = L(E)`, this file sets up

* `asCoeff` — the coefficient action of `γ ∈ Gal(L/K)` on `M` (the base change of
  `Work.MotV5.coeffAction`), acting on the constants `L` by `γ` and fixing `x, y`;
* `asShift` — the Galois shift `χ(γ)` of an Artin–Schreier root `W ∈ L` of `X⁵ - X - g`;
* `asPsi` — the twisted Galois action `ψ_γ = σS ^ (χ γ) ∘ γ̃` of the class of `g`;
* `asF` — the twist field `asTwistFieldTrue D g τ σS`, pulled back to `M` along the base-change
  map `asIota`.

and it collects the structural facts about them (`asPsi_fixes_asF`, `asF_sup`, `asF_inf`,
`asF_linearDisjoint`) that the LAM node uses.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace Work.MotV5.LamAS

open WeierstrassCurve WeierstrassCurve.Affine

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- **The coefficient action of `γ ∈ Gal(L/K)` on `M = L(E)`**: the `K`-algebra automorphism
acting on the constants `L` by `γ` and fixing the two coordinates `x, y`. -/
noncomputable def asCoeff (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜)
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) :
    asML D f₁ f₂ ≃ₐ[RatFunc 𝕜] asML D f₁ f₂ :=
  Work.MotV5.coeffAction (R := 𝕜) (K := RatFunc 𝕜)
    (L := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) D.E γ

theorem asCoeff_algebraMap (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜)
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    (l : ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) :
    asCoeff D f₁ f₂ γ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l) =
      algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) (γ l) :=
  Work.MotV5.coeffAction_algebraMap (R := 𝕜) (K := RatFunc 𝕜)
    (L := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) D.E γ l

theorem asCoeff_genX (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜)
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) :
    asCoeff D f₁ f₂ γ (Work.MotV.genX (asE2 D f₁ f₂)) = Work.MotV.genX (asE2 D f₁ f₂) :=
  Work.MotV5.coeffAction_genX (R := 𝕜) (K := RatFunc 𝕜)
    (L := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) D.E γ

theorem asCoeff_genY (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜)
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) :
    asCoeff D f₁ f₂ γ (Work.MotV.genY (asE2 D f₁ f₂)) = Work.MotV.genY (asE2 D f₁ f₂) :=
  Work.MotV5.coeffAction_genY (R := 𝕜) (K := RatFunc 𝕜)
    (L := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) D.E γ

/-- **The Galois shift `χ(γ)` of an Artin–Schreier root.**  If `W ∈ L` satisfies
`W⁵ - W = g` with `g ∈ K`, then every `K`-automorphism `γ` of `L` moves `W` by an element of the
prime field: `γ (W) = W + χ(γ)`. -/
noncomputable def asShift (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) (g : RatFunc 𝕜)
    (W : ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    (hW : W ^ 5 - W = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) g)
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) : Fin 5 :=
  Classical.choose (shift_of_pow_five_sub_self (F := RatFunc 𝕜) hW γ)

theorem asShift_spec (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) (g : RatFunc 𝕜)
    (W : ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    (hW : W ^ 5 - W = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) g)
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) :
    γ W = W + algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (((asShift D f₁ f₂ g W hW γ : Fin 5) : ℤ)) :=
  Classical.choose_spec (shift_of_pow_five_sub_self (F := RatFunc 𝕜) hW γ)

/-- **The twisted Galois action of the class of `g` on `M`**: `ψ_γ = σS ^ (χ γ) ∘ γ̃`, where
`σS` is (a lift to `M` of) the projective fifth-torsion shift and `γ̃` the coefficient action. -/
noncomputable def asPsi (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) (g : RatFunc 𝕜)
    (σS : asML D f₁ f₂ ≃ₐ[↥(asL2 (𝕜 := 𝕜) f₁ f₂)] asML D f₁ f₂)
    (W : ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    (hW : W ^ 5 - W = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) g)
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) :
    asML D f₁ f₂ ≃ₐ[RatFunc 𝕜] asML D f₁ f₂ :=
  (σS ^ ((asShift D f₁ f₂ g W hW γ : Fin 5) : ℕ)).restrictScalars (RatFunc 𝕜) *
    asCoeff D f₁ f₂ γ

/-- The twist field `asTwistFieldTrue D g τ σS`, pulled back to `M = L(E)` along the base-change
map `asIota` (i.e. the `K`-subfield of `M` whose image in `Om D` is the twist field). -/
noncomputable def asF (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) (g : RatFunc 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D) :
    IntermediateField (RatFunc 𝕜) (asML D f₁ f₂) :=
  (asTwistFieldTrue D g τ σS).comap (asIota D f₁ f₂)

end Work.MotV5.LamAS
