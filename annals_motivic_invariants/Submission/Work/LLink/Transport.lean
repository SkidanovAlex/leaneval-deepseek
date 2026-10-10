import Mathlib
import Submission.Work.Motivic.cInv_add
import Submission.Work.Motivic.cInv_eq_zero_of_pseudoReg
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.LLink.Transport` — transport of a link to affine space

The Cremona group of the challenge is `Cr 𝕜 3 = Bir(𝔸³/𝕜)` (`ChallengeDeps.lean`), while the
constructions of the paper produce birational maps between projective threefolds (`Q³ ⤏ ℙ³`).
The bridge is *transport along birational identifications with affine space*:

`φ = ε ∘ ψ ∘ δ`, where `ε : 𝔸³ ⤏ S` and `δ : T ⤏ 𝔸³` are birational maps over `𝕜`.

This file defines that transport and proves that it lies in `Cr 𝕜 3` and that its invariant is
additive: `cInv 𝕜 z (ε ∘ ψ ∘ δ) = cInv 𝕜 z ε + cInv 𝕜 z ψ + cInv 𝕜 z δ`, so that the transport
identifications contribute nothing whenever `cInv 𝕜 z ε = cInv 𝕜 z δ = 0` (the paper's *strong
birationality* of `Q³` and `ℙ³` with `ℙ³`/`𝔸³`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.LLink

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

variable {𝕜 : Type} [Field 𝕜]
variable {S T : Scheme.{0}} [IrreducibleSpace S] [IrreducibleSpace T]

/-- Affine `3`-space over `𝕜`, the ambient scheme of the Cremona group `Cr 𝕜 3`. -/
noncomputable abbrev Affine3 (𝕜 : Type) [Field 𝕜] : Scheme.{0} := 𝔸(Fin 3; Spec (.of 𝕜))

/-- The **affine transport** of a birational map `ψ : S ⤏ T` along birational identifications
`ε : 𝔸³ ⤏ S` and `δ : T ⤏ 𝔸³`: the birational self-map `ε ∘ ψ ∘ δ` of `𝔸³`. -/
noncomputable def transport (ε : (Affine3 𝕜).BirationalMap S) (ψ : S.BirationalMap T)
    (δ : T.BirationalMap (Affine3 𝕜)) : (Affine3 𝕜).BirationalMap (Affine3 𝕜) :=
  ε.trans (ψ.trans δ)

@[simp]
theorem transport_def (ε : (Affine3 𝕜).BirationalMap S) (ψ : S.BirationalMap T)
    (δ : T.BirationalMap (Affine3 𝕜)) :
    transport ε ψ δ = ε.trans (ψ.trans δ) := rfl

/-- The affine transport of maps over `𝕜` is over `𝕜`. -/
theorem transport_isOver [S.Over (Spec (.of 𝕜))] [T.Over (Spec (.of 𝕜))]
    (ε : (Affine3 𝕜).BirationalMap S) (ψ : S.BirationalMap T) (δ : T.BirationalMap (Affine3 𝕜))
    [ε.IsOver (Spec (.of 𝕜))] [ψ.IsOver (Spec (.of 𝕜))] [δ.IsOver (Spec (.of 𝕜))] :
    (transport ε ψ δ).IsOver (Spec (.of 𝕜)) := by
  haveI hmid : (ψ.trans δ).IsOver (Spec (.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans ψ δ
  rw [transport_def]
  exact Work.Motivic.pseudoReg_isOver_trans ε (ψ.trans δ)

/-- The **transported Cremona map**: the affine transport, regarded as an element of the Cremona
group `Cr 𝕜 3 = Bir(𝔸³/𝕜)` of the challenge. -/
noncomputable def transportCr [S.Over (Spec (.of 𝕜))] [T.Over (Spec (.of 𝕜))]
    (ε : (Affine3 𝕜).BirationalMap S) (ψ : S.BirationalMap T) (δ : T.BirationalMap (Affine3 𝕜))
    [ε.IsOver (Spec (.of 𝕜))] [ψ.IsOver (Spec (.of 𝕜))] [δ.IsOver (Spec (.of 𝕜))] : Cr 𝕜 3 :=
  ⟨transport ε ψ δ, transport_isOver ε ψ δ⟩

@[simp]
theorem transportCr_coe [S.Over (Spec (.of 𝕜))] [T.Over (Spec (.of 𝕜))]
    (ε : (Affine3 𝕜).BirationalMap S) (ψ : S.BirationalMap T) (δ : T.BirationalMap (Affine3 𝕜))
    [ε.IsOver (Spec (.of 𝕜))] [ψ.IsOver (Spec (.of 𝕜))] [δ.IsOver (Spec (.of 𝕜))] :
    ((transportCr ε ψ δ : Cr 𝕜 3) : (Affine3 𝕜).BirationalMap (Affine3 𝕜)) =
      transport ε ψ δ := rfl

/-- **Additivity of the invariant along the transport**: the coefficient of the transported map
splits into the three coefficients of its factors. -/
theorem cInv_transport_eq [Variety 𝕜 S] [Variety 𝕜 T]
    (ε : (Affine3 𝕜).BirationalMap S) (ψ : S.BirationalMap T) (δ : T.BirationalMap (Affine3 𝕜))
    [ε.IsOver (Spec (.of 𝕜))] [ψ.IsOver (Spec (.of 𝕜))] [δ.IsOver (Spec (.of 𝕜))]
    {Z : Scheme.{0}} [Z.Over (Spec (.of 𝕜))] (z : Z) :
    cInv 𝕜 z (transport ε ψ δ) = cInv 𝕜 z ε + cInv 𝕜 z ψ + cInv 𝕜 z δ := by
  haveI hmid : (ψ.trans δ).IsOver (Spec (.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans ψ δ
  have h2 := Work.Motivic.cInv_add (𝕜 := 𝕜) (X := S) (Y := T) (Z := Affine3 𝕜) z ψ δ
  have h1 := Work.Motivic.cInv_add (𝕜 := 𝕜) (X := Affine3 𝕜) (Y := S) (Z := Affine3 𝕜) z ε
    (ψ.trans δ)
  rw [transport_def, h1, h2]
  first | refl_ring1 | ring

/-- The transport of a map whose two identifications have vanishing invariant has the same
invariant as the original map: the paper's `c(φ) = c(ψ)` for an L-link, transported to `𝔸³`. -/
theorem cInv_transport_eq_of_eq_zero [Variety 𝕜 S] [Variety 𝕜 T]
    (ε : (Affine3 𝕜).BirationalMap S) (ψ : S.BirationalMap T) (δ : T.BirationalMap (Affine3 𝕜))
    [ε.IsOver (Spec (.of 𝕜))] [ψ.IsOver (Spec (.of 𝕜))] [δ.IsOver (Spec (.of 𝕜))]
    {Z : Scheme.{0}} [Z.Over (Spec (.of 𝕜))] (z : Z)
    (hε : cInv 𝕜 z ε = 0) (hδ : cInv 𝕜 z δ = 0) :
    cInv 𝕜 z (transport ε ψ δ) = cInv 𝕜 z ψ := by
  rw [cInv_transport_eq ε ψ δ z, hε, hδ]
  first | refl_ring1 | ring

end Work.LLink
