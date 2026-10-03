/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# `ℂ[G] ↪ U(G)`: the group algebra inside the algebra of affiliated operators

For a model `D : GroupVonNeumannAlgebra G` of the group von Neumann algebra, the algebra of
affiliated operators is `U(G) = D.affiliated = N(G)[(N(G) ∖ {0})⁻¹]`
(`Submission.Work.ORVonNeumann.VonNeumannAlgebra`).  This module constructs the composite

  `ℂ[G] →+* N(G) →+* U(G)`

(the first map is the linearisation of the regular representation `ρ`, the second is the
Ore localisation's `numeratorRingHom`) and proves that it is injective and `ℂ`-linear: the
fields `ι`, `ι_injective`, `ι_algebraMap` of `StarRegularEnvelope`.

## Main results

* `Work.ORVonNeumann.VonNeumannAlgebra.liftHom` — `ℂ[G] →+* N(G)`, the algebra lift of `ρ`;
* `Work.ORVonNeumann.VonNeumannAlgebra.toU` — `ℂ[G] →+* U(G)`;
* `Work.ORVonNeumann.VonNeumannAlgebra.toU_injective`;
* `Work.ORVonNeumann.VonNeumannAlgebra.toU_algebraMap` — `ℂ`-linearity.
-/
import Mathlib
import Submission.Work.ORVonNeumann.VonNeumannAlgebra
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.lift_mul
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.lift_injective

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORVonNeumann.VonNeumannAlgebra

open Work.ORVonNeumann

variable {G : Type u} [Group G] (D : GroupVonNeumannAlgebra G)

/-- The ring homomorphism `ℂ[G] →+* N(G)` linearising the regular representation `ρ`. -/
noncomputable def liftHom : MonoidAlgebra ℂ G →+* D.N :=
  (MonoidAlgebra.lift ℂ D.N G D.ρ).toRingHom

/-- `liftHom` is `D.lift` on elements. -/
theorem liftHom_apply (f : MonoidAlgebra ℂ G) : liftHom D f = D.lift f := by
  show (MonoidAlgebra.lift ℂ D.N G D.ρ) f = D.lift f
  rw [Work.ORVonNeumann.GroupVonNeumannAlgebra.lift, MonoidAlgebra.lift_apply]

/-- **`ℂ[G]` inside `U(G)`**: the composite of the lift `ℂ[G] →+* N(G)` with the Ore
localisation map `N(G) →+* U(G)`. -/
noncomputable def toU : MonoidAlgebra ℂ G →+* D.affiliated :=
  (OreLocalization.numeratorRingHom (S := nonZeroDivisors D.N)).comp (liftHom D)

/-- `toU` sends `f` to the fraction `D.lift f / 1`. -/
theorem toU_apply (f : MonoidAlgebra ℂ G) :
    toU D f = (OreLocalization.numeratorRingHom (S := nonZeroDivisors D.N)) (D.lift f) := by
  show OreLocalization.numeratorRingHom (S := nonZeroDivisors D.N) (liftHom D f) = _
  rw [liftHom_apply]

/-- **`ℂ[G]` embeds in `U(G)`.** -/
theorem toU_injective : Function.Injective (toU D) := by
  have h1 : Function.Injective (OreLocalization.numeratorRingHom (S := nonZeroDivisors D.N)) :=
    OreLocalization.numeratorHom_inj (S := nonZeroDivisors D.N) inf_le_left
  intro f g hfg
  have h2 : liftHom D f = liftHom D g := h1 hfg
  rw [liftHom_apply, liftHom_apply] at h2
  exact lift_injective D h2

/-- **`ℂ`-linearity** of `ℂ[G] →+* U(G)`. -/
theorem toU_algebraMap (c : ℂ) :
    toU D (algebraMap ℂ (MonoidAlgebra ℂ G) c) = algebraMap ℂ D.affiliated c := by
  have h : liftHom D (algebraMap ℂ (MonoidAlgebra ℂ G) c) = algebraMap ℂ D.N c :=
    (MonoidAlgebra.lift ℂ D.N G D.ρ).commutes c
  show OreLocalization.numeratorHom (S := nonZeroDivisors D.N)
      (liftHom D (algebraMap ℂ (MonoidAlgebra ℂ G) c)) = _
  rw [h]
  rfl

end Work.ORVonNeumann.VonNeumannAlgebra
